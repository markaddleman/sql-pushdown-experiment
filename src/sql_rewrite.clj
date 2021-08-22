(ns sql-rewrite
  (:require [meander.epsilon :as m]
            [meander.strategy.epsilon :as m*]
            [clojure.test :refer [deftest is]]
            [honeysql.core :as h])
  (:import [honeysql.types SqlCall]))

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
        {& ?rest}))))

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

(defn normalize-honey [honey alias]
  (-> honey
      (m/rewrite
        {:with (m/some (m/seqable (m/seqable !query !query-alias) ...))
         &     ?rest}
        {:with [[(m/app #(normalize-expr % alias) !query) (m/app alias !query-alias)] ...]
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
         :having   (m/seqable !having-expr ...)}
        {:select   [[(m/app #(normalize-expr % alias) !col-expr-with-alias) !col-expr-alias] ...
                    [(m/app #(normalize-expr % alias) !col-expr-no-alias-1) (m/app alias !col-expr-no-alias-2)] ...]
         :from     [[(m/app #(normalize-expr % alias) !table-expr-with-alias) !table-expr-alias] ...
                    [(m/app #(normalize-expr % alias) !table-expr-no-alias-1) (m/app alias !table-expr-no-alias-2)] ...]
         :where    (m/app #(normalize-expr % alias) ?where-expr)
         :group-by [(m/app #(normalize-expr % alias) !group-by-expr) ...]
         :having   [(m/app #(normalize-expr % alias) !having-expr) ...]})))

(comment
  )

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
        {:with [[!query !query-alias] ...]
         &     ?rest}
        {:with (m/map-of !query-alias (m/cata !query))
         &     (m/cata ?rest)}

        {:select [[!col-expr !col-expr-alias] ...]
         :from   [[!table-expr !table-expr-alias] ...]
         &       ?rest}
        {:select (m/map-of !col-expr-alias (m/app optimize-expr !col-expr))
         :from   (m/map-of !table-expr-alias (m/app optimize-expr !table-expr))
         &       ?rest})))

(defn cols-to-push-down [normalized-honey]
  (->> (m/rewrite normalized-honey
         {:with [[!view !view-name] ...]
          &     ?query}
         [(m/cata !view) ... (m/cata ?query)]

         {:select   [[!expr _] ...]
          :from     (m/and [[_ ?table-alias]]
                           (m/gather [(m/and {(m/some :select) _}
                                             !query) _]))
          :where    ?where-expr
          :group-by [!group-by-expr ...]
          :having   [!having-expr ...]}
         [(m/cata [?where-expr ?table-alias])
          [(m/cata [!expr ?table-alias]) ...
           (m/cata !query) ...
           (m/cata [!group-by-expr ?table-alias]) ...
           (m/cata [!having-expr ?table-alias]) ...]]

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

(defn incorporate-col [col select-expr]
  (merge {col col} select-expr))

(defn incorporate-cols [optimized-honey cols]
  (reduce (fn [optimized-honey [col table-alias]]
            (m/rewrite optimized-honey
              {:with {~table-alias {:select ?select-expr
                                    &       ?rest-view}
                      &            ?rest-with}
               &     ?rest-query}
              {:with {~table-alias {:select (m/app (partial incorporate-col col) ?select-expr)
                                    &       ?rest-view}
                      &            ?rest-with}
               &     ?rest-query}))
          optimized-honey
          cols))

(defn reverse-optimize-honey [optimized-honey]
  (-> optimized-honey
      (m/rewrite
        {:with (m/map-of !view-name !view)
         &     ?rest}
        {:with [[(m/cata !view) !view-name] ...]
         &     (m/cata ?rest)}

        {(m/some :select) ?select-expr
         :from            ?from-expr
         &                ?rest}
        {:select (m/app (partial into []) ?select-expr)
         :from   (m/app (partial into []) ?from-expr)
         &       ?rest})))

(comment
  (let [honey {:with   [[{:select [] :from [:t]} :v]]
               :select [:a] :from [:v]}
        normalized-honey (normalize-honey honey identity)
        cols-to-push-down (cols-to-push-down normalized-honey)]
    (reverse-optimize-honey
      (incorporate-cols (optimize-honey normalized-honey)
                        cols-to-push-down))))

(comment
  (-> {:where    true,
       :group-by [],
       :having   [],
       :select   [[:a :a]],
       :from     [[:v :v]],
       :with     [[{:where true, :group-by [], :having [], :select [[:a :a]], :from [[:t :t]]} :v]]}
      (simplify)
      (h/format)))

(deftest optimized-honey
  (is (= {:select {:a :a, :b :b}, :from {:t :t}}
         (-> {:select [:a :b] :from [:t]}
             (normalize-honey identity)
             (simplify)
             (optimize-honey))))

  (is (= {:select {:a-alias :a, :b-alias :b}, :from {:t-alias :t}}
         (-> {:select [[:a :a-alias] [:b :b-alias]] :from [[:t :t-alias]]}
             (normalize-honey identity)
             (simplify)
             (optimize-honey)))))

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
  (is (= {:where    true,
          :group-by [],
          :having   [],
          :select   {:alias {:where    true,
                             :group-by [],
                             :having   [],
                             :select   {:a :a, :b :b},
                             :from     {:t {:where true, :group-by [], :having [], :select {:a :a}, :from {:t :t}}}}},
          :from     {}}
         (-> {:select [[{:select [:a :b] :from [[{:select [:a] :from [:t]} :t]]} :alias]]}
             (normalize-honey identity)
             (optimize-honey)))))

(deftest with-clause
  (is (= {:with   {:v {:select {:a :a},
                       :from   {:t :t}}}
          :select {:a 1}, :from {:v :v}}
         (-> {:with   [[{:select [:a] :from [:t]} :v]]
              :select [[1 :a]]
              :from   [:v]}
             (normalize-honey identity)
             (simplify)
             (optimize-honey)))))

(deftest push-downs
  (is (= #{[:a :t] [:c :t] [:b :t] [:inner :s]}
         (-> {:select [:a
                       [(h/call "and" (h/call "=" :a :c) :b) :alias]
                       [{:select [:inner] :from [:s]} :select-alias]] :from [:t]}
             (normalize-honey identity)
             (cols-to-push-down))))

  (is (= #{[:a :t] [:a :s]}
         (-> {:select [:a] :from [[{:select [:a] :from [:s]} :t]]}
             (normalize-honey identity)
             (cols-to-push-down))))

  (is (= #{[:b :t] [:a :v]}
         (-> {:with   [[{:select [:b] :from [:t]} :v]]
              :select [:a] :from [:v]}
             (normalize-honey identity)
             (cols-to-push-down)))))