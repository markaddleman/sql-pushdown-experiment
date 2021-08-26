(ns sql-rewrite
  (:require [meander.epsilon :as m]
            [meander.strategy.epsilon :as m*]
            [bq :as bq]
            [weavejester.dependency :as dep]
            [clojure.test :refer [deftest is]]
            [honeysql.core :as h])
  (:import [honeysql.types SqlCall]))

; support windowing clause

(def simplify
  (m*/bottom-up
    (m*/until =
      (m*/rewrite
        {:from [] & ?rest}
        {& ?rest}

        {:where true & ?rest}
        {& ?rest}

        {:group-by [] & ?rest}
        {& ?rest}

        {:having [] & ?rest}
        {& ?rest}

        {:order-by [] & ?rest}
        {& ?rest}

        {:limit nil :offset nil :as ?query}
        (m/app #(dissoc % :limit :offset) ?query)

        {:offset nil :as ?query}
        (m/app #(dissoc % :offset) ?query)))))

(declare normalize-honey)
(defn normalize-expr [expr alias]
  (-> expr
      (m/rewrite
        {(m/some :select) _ :as ?honey}
        (m/app #(normalize-honey % alias) ?honey)

        (m/and (m/pred (partial instance? SqlCall))
               {:name ?name :args (m/seqable !arg ...)})
        (m/app (partial apply h/call) ?name [(m/app #(normalize-expr % alias) !arg) ...])

        ?? ??)))

(defn normalize-order-by-expr [expr alias]
  (-> expr
      (m/rewrite
        [_ _ :as ?full-order-by-expr]
        ?full-order-by-expr

        ?expr
        [?expr :asc])
      (m/rewrite
        [?expr (m/and (m/or :asc :desc) ?order)]
        [(m/cata ?expr) ?order]

        ?expr
        (m/app #(normalize-expr % alias) ?expr))))

(defn normalize-honey [honey alias]
  (-> honey
      (m/rewrite
        {(m/and (m/or ::bq/with :with) ?with) (m/some (m/seqable (m/seqable !query !query-alias) ...))
         &                                    ?rest}
        {?with [[(m/app #(normalize-expr % alias) !query) (m/app alias !query-alias)] ...]
         &     (m/cata ?rest)}

        {:select   (m/and (m/gather (m/seqable !col-expr-with-alias !col-expr-alias))
                          (m/gather (m/and (m/not (m/seqable _ _))
                                           (m/and !col-expr-no-alias-1
                                                  !col-expr-no-alias-2))))
         :from     (m/and (m/gather (m/seqable !table-expr-with-alias !table-expr-alias))
                          (m/gather (m/and (m/not (m/seqable _ _))
                                           (m/and !table-expr-no-alias-1
                                                  !table-expr-no-alias-2))))
         :where    (m/or (m/some ?where-expr)
                         (m/let [?where-expr true]))
         :group-by (m/seqable !group-by-expr ...)
         :having   (m/seqable !having-expr ...)
         :order-by (m/seqable !order-by-expr ...)
         :limit    ?limit
         :offset   ?offset}
        {:select   [[(m/app #(normalize-expr % alias) !col-expr-with-alias) !col-expr-alias] ...
                    [(m/app #(normalize-expr % alias) !col-expr-no-alias-1) (m/app alias !col-expr-no-alias-2)] ...]
         :from     [[(m/app #(normalize-expr % alias) !table-expr-with-alias) !table-expr-alias] ...
                    [(m/app #(normalize-expr % alias) !table-expr-no-alias-1) (m/app alias !table-expr-no-alias-2)] ...]
         :where    (m/app #(normalize-expr % alias) ?where-expr)
         :group-by [(m/app #(normalize-expr % alias) !group-by-expr) ...]
         :having   [(m/app #(normalize-expr % alias) !having-expr) ...]
         :order-by [(m/app #(normalize-order-by-expr % alias) !order-by-expr) ...]
         :limit    ?limit
         :offset   ?offset})))

(comment
  (-> {:select [:a
                [(h/call "and" (h/call "=" :a :c) :b) :alias]
                [{:select [:inner] :from [:s]} :select-alias]] :from [:t]}
      (normalize-honey identity)
      (simplify)))

(def constants (comp #{Boolean Long String} (partial class)))

(declare optimize-honey)
(defn optimize-expr [expr]
  (-> expr
      (m/rewrite
        {(m/some :select) _ :as ?honey}
        (m/app optimize-honey ?honey)

        ?? ??)))

(defn optimize-honey [normalized-honey]
  (-> normalized-honey
      (m/rewrite
        {(m/and (m/or ::bq/with :with) ?with) [[!query !query-alias] ...]
         &                                    ?rest}
        {?with (m/map-of !query-alias (m/cata !query))
         &     (m/cata ?rest)}

        {:select   [[!col-expr !col-expr-alias] ...]
         :from     [[!from-expr !from-alias] ...]
         :where    ?where-expr
         :group-by [!group-by-expr ...]
         :having   [!having-expr ...]
         :order-by [[!order-by-expr !order] ...]}
        {:select   (m/map-of !col-expr-alias (m/app optimize-expr !col-expr))
         :from     [[(m/app optimize-expr !from-expr) !from-alias] ...]
         :where    (m/app optimize-expr ?where-expr)
         :group-by [(m/app optimize-expr !group-by-expr) ...]
         :having   [(m/app optimize-expr !having-expr) ...]
         :order-by [[(m/app optimize-expr !order-by-expr) !order] ...]})))

(defn cols-to-push-down [optimized-honey]
  (->> (m/rewrite optimized-honey
         {(m/some (m/or ::bq/with :with)) (m/map-of !view-name !view)
          &                               ?query}
         [(m/cata !view) ... (m/cata ?query)]

         {(m/some :select) (m/map-of _ !expr)
          :from            (m/and [[_ ?table-alias]]
                                  (m/gather [(m/and {(m/some :select) _}
                                                    !query) _]))
          :where           ?where-expr
          :group-by        [!group-by-expr ...]
          :having          [!having-expr ...]
          :order-by        [[!order-by-expr _] ...]}
         [(m/cata [?where-expr ?table-alias])
          [(m/cata [!expr ?table-alias]) ...
           (m/cata !query) ...
           (m/cata [!group-by-expr ?table-alias]) ...
           (m/cata [!having-expr ?table-alias]) ...
           (m/cata [!order-by-expr ?table-alias]) ...]]

         [(m/pred (partial instance? SqlCall) {:args (m/seqable !arg ...)}) ?table-alias]
         [(m/cata [!arg ?table-alias]) ...]

         [{(m/some :select) _ :as ?query} _]
         (m/cata ?query)

         [{:args (m/seqable !expr ...)} ?table-alias]
         [(m/cata [!expr ?table-alias]) ...]

         [(m/pred keyword? ?col) ?table-alias]
         [?col ?table-alias]

         [(m/pred constants ?expr) ?table-alias]
         [])
       (flatten)
       (partition 2)
       (set)))

(comment
  (-> {:where    true,
       :group-by [],
       :having   [],
       :select   {:a :a},
       :from     [[:x :x]],
       :with     {:y {:where true, :group-by [], :having [], :select {}, :from [[:z :z]]},
                  :x {:where true, :group-by [], :having [], :from [[:y :y]], :select {:a :a}}}}
      (cols-to-push-down)))

(defn incorporate-col [col select-expr]
  (merge {col col} select-expr))

(defn incorporate-cols [optimized-honey cols]
  (reduce (fn [optimized-honey [col table-alias]]
            (m/rewrite optimized-honey
              {(m/and (m/or ::bq/with :with) ?with) {~table-alias {:select ?select-expr
                                                                   &       ?rest-view}
                                                     &            ?rest-with}
               &                                    ?rest-query}
              {?with {~table-alias {:select (m/app (partial incorporate-col col) ?select-expr)
                                    &       ?rest-view}
                      &            ?rest-with}
               &     ?rest-query}

              ?? ??))
          optimized-honey
          cols))

(defn topo-sort [optimized-honey]
  (into [] (filter (complement nil?))
        (-> (reduce (fn [graph [source dep]]
                      (dep/depend graph dep source))
                    (dep/graph)
                    (-> optimized-honey
                        (m/search
                          {(m/or ::bq/with :with) {?view-alias  (m/$ {:from (m/scan [?table-alias _])})
                                                   ?table-alias _}}
                          [?view-alias ?table-alias]

                          {(m/or ::bq/with :with) {?table-alias _}
                           :from                  [[?table-alias _]]}
                          [nil ?table-alias])))
            (dep/topo-sort))))

(defn reverse-optimize-honey [optimized-honey]
  (let [view-order (zipmap (topo-sort optimized-honey)
                           (map (partial * -1) (range)))]
    (-> optimized-honey
        (m/rewrite
          {(m/and (m/or ::bq/with :with) ?with) (m/map-of !view-name !view)
           &                                    ?rest}
          {?with (m/app (comp
                          vec
                          (partial sort-by (comp view-order second))
                          (partial filter (comp (partial contains? view-order)
                                                second)))
                        [[(m/cata !view) !view-name] ...])
           &     (m/cata ?rest)}

          {(m/some :select) ?select-expr
           :from            ?from-expr
           &                ?rest}
          {:select (m/app (partial into []) ?select-expr)
           :from   (m/app (partial into []) ?from-expr)
           &       ?rest}))))

(comment
  (-> {:with   [[{:select [:a] :from [:x]} :v]
                [{:select [:a] :from [:y]} :x]]
       :select [:a] :from [:v]}
      (normalize-honey identity)
      (optimize-honey)
      (reverse-optimize-honey)
      (simplify)
      (h/format)))

(defn push-down [normalized-honey]
  (loop [optimized-honey (optimize-honey normalized-honey)
         prev nil]
    (if (= prev optimized-honey)
      (reverse-optimize-honey optimized-honey)
      (recur (incorporate-cols
               optimized-honey
               (cols-to-push-down optimized-honey))
             optimized-honey))))

(deftest optimized-honey
  (is (= {:select {:a :a, :b :b}, :from [[:t :t]]}
         (-> {:select [:a :b] :from [:t]}
             (normalize-honey identity)
             (optimize-honey)
             (simplify))))

  (is (= {:select {:a-alias :a, :b-alias :b}, :from [[:t :t-alias]]}
         (-> {:select [[:a :a-alias] [:b :b-alias]] :from [[:t :t-alias]]}
             (normalize-honey identity)
             (optimize-honey)
             (simplify)))))

(deftest normalize-select-exprs
  (is (= {:select [[1 :alias]]})
      (-> {:select [1]}
          (normalize-honey (constantly :alias))
          (simplify)))

  (is (= {:select [[:a :a]]}
         (-> {:select [[:a :a]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[:a :a]]}
         (-> {:select [:a]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[:a :a] [:b :b]]}
         (-> {:select [:a :b]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[:b :c] [:a :a]]}
         (-> {:select [:a [:b :c]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[:a :b] [:b :c]]}
         (-> {:select [[:a :b] [:b :c]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[:a :a]], :from [[:t :t]], :where {:select [[:b :b]], :from [[:s :s]]}}
         (-> {:select [:a]
              :from   [:t]
              :where  {:select [:b] :from [:s]}}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[:a :a]], :from [[:t :t]], :where (h/call "exists" {:select [[:b :b]], :from [[:s :s]]})}
         (-> {:select [:a] :from [:t]
              :where  (h/call "exists" {:select [:b] :from [:s]})}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[(h/call "and" (h/call "=" :a :c) :b) :alias]
                   [{:select [[:inner :inner]], :from [[:s :s]]} :select-alias]
                   [:a :a]],
          :from   [[:t :t]]}
         (-> {:select [:a
                       [(h/call "and" (h/call "=" :a :c) :b) :alias]
                       [{:select [:inner] :from [:s]} :select-alias]] :from [:t]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[:a :a]] :from [[:t :t]] :limit 10 :offset 10}
         (-> {:select [:a] :from [:t] :limit 10 :offset 10}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[:a :a]] :from [[:t :t]] :limit 10}
         (-> {:select [:a] :from [:t] :limit 10}
             (normalize-honey identity)
             (simplify)))))

(deftest normalize-from-exprs
  (is (= {:select []
          :from   [[:a :a]]}
         (-> {:from [[:a :a]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select []
          :from   [[:a :a]]}
         (-> {:from [:a]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select []
          :from   [[:a :a] [:b :b]]}
         (-> {:from [:a :b]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select []
          :from   [[:b :c] [:a :a]]}
         (-> {:from [:a [:b :c]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select []
          :from   [[:a :b] [:b :c]]}
         (-> {:from [[:a :b] [:b :c]]}
             (normalize-honey identity)
             (simplify)))))

(deftest sub-selects
  (is (= {:select {:alias {:select {:a :a, :b :b}, :from [[{:select {:a :a}, :from [[:t :t]]} :t]]}}}
         (-> {:select [[{:select [:a :b] :from [[{:select [:a] :from [:t]} :t]]} :alias]]}
             (normalize-honey identity)
             (optimize-honey)
             (simplify)))))

(deftest with-clause
  (is (= {:select {:a 1}, :from [[:v :v]], :with {:v {:select {:a :a}, :from [[:t :t]]}}}
         (-> {:with   [[{:select [:a] :from [:t]} :v]]
              :select [[1 :a]]
              :from   [:v]}
             (normalize-honey identity)
             (optimize-honey)
             (simplify)))))

(deftest push-downs
  (is (= #{[:a :t] [:c :t] [:b :t] [:inner :s]}
         (-> {:select [:a
                       [(h/call "and" (h/call "=" :a :c) :b) :alias]
                       [{:select [:inner] :from [:s]} :select-alias]] :from [:t]}
             (normalize-honey identity)
             (optimize-honey)
             (cols-to-push-down))))

  (is (= #{[:a :t] [:a :s]}
         (-> {:select [:a] :from [[{:select [:a] :from [:s]} :t]]}
             (normalize-honey identity)
             (optimize-honey)
             (cols-to-push-down))))

  (is (= #{[:b :t] [:a :v]}
         (-> {:with   [[{:select [:b] :from [:t]} :v]]
              :select [:a] :from [:v]}
             (normalize-honey identity)
             (optimize-honey)
             (cols-to-push-down)))))

(deftest push-downs
  (is (= {:select [[:a :a]]}
         (-> {:select [:a]}
             (normalize-honey identity)
             (push-down)
             (simplify))))

  (is (= {:select [[:a :a]] :from [[:t :t]]}
         (-> {:select [:a] :from [:t]}
             (normalize-honey identity)
             (push-down)
             (simplify))))

  (is (= '{:select [(:a :a)],
           :from   [[:x :x]],
           :with   [[{:select [(:a :a)], :from [[:z :z]]} :y]
                    [{:select [(:a :a)], :from [[:y :y]]} :x]]}
         (-> {:with   [[{:select [] :from [:y]} :x]
                       [{:select [] :from [:z]} :y]]
              :select [:a] :from [:x]}
             (normalize-honey identity)
             (push-down)
             (simplify)))))

(deftest topo-sorts
  (is (= [] (-> {:select [] :from [:v]}
                (normalize-honey identity)
                (optimize-honey)
                (topo-sort))))

  (is (= [:v] (-> {:with   [[{:select [] :from []} :v]]
                   :select [] :from [:v]}
                  (normalize-honey identity)
                  (optimize-honey)
                  (topo-sort))))

  (is (= [:v :x] (-> {:with   [[{:select [] :from [:x]} :v]
                               [{:select [] :from []} :x]]
                      :select [] :from [:v]}
                     (normalize-honey identity)
                     (optimize-honey)
                     (topo-sort))))

  (is (= [:v :x] (-> {:with   [[{:select [] :from [:x]} :v]
                               [{:select [] :from []} :x]]
                      :select [[{:select [:a] :from [:x]} :b]]}
                     (normalize-honey identity)
                     (optimize-honey)
                     (topo-sort)))))