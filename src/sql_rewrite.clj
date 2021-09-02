(ns sql-rewrite
  (:require [meander.epsilon :as m]
            [net.cgrand.xforms :as x]
            [bq :as bq]
            [weavejester.dependency :as dep]
            [clojure.test :refer [deftest is]]
            [honeysql.core :as sql])
  (:import [honeysql.types SqlCall]))

; push down already fully qualified columns

(defn unqualified-col? [v]
  (and (keyword? v) (not (namespace v))))

(defn qualified-col? [v]
  (and (keyword? v) (namespace v)))

(def table-name? keyword?)

(defn remove-unused-clauses [normalized-honey]
  (into {} (filter (complement #{[:select []]
                                 [:from []]
                                 [:where true]
                                 [:group-by []]
                                 [:having []]
                                 [:order-by []]
                                 [:limit nil]
                                 [:offset nil]
                                 [::bq/rows-between []]
                                 [::bq/partition-by []]}))
        normalized-honey))

(defn simplify [normalized-honey]
  (-> normalized-honey
      (m/rewrite
        {(m/and (m/or ::bq/with :with) ?with) [[!table-expr !table-alias] ...]
         &                                    ?rest}
        {?with [[(m/cata !table-expr) !table-alias] ...]
         &     (m/cata ?rest)}

        {:select           [[!col-expr !col-alias] ...]
         :from             [[!table-expr !table-alias] ...]
         :where            ?where-expr
         :group-by         [!group-by-expr ...]
         :having           [!having-expr ...]
         :order-by         [[!order-by-expr !ordering] ...]
         :limit            ?limit-expr
         :offset           ?offset-expr
         ::bq/rows-between [!rows-between-expr ...]
         ::bq/partition-by [!partition-by-expr ...]}

        (m/app remove-unused-clauses
               {:select           [[(m/cata !col-expr) !col-alias] ...]
                :from             [[(m/cata !table-expr) !table-alias] ...]
                :where            (m/cata ?where-expr)
                :group-by         [(m/cata !group-by-expr) ...]
                :having           [(m/cata !having-expr) ...]
                :order-by         [[(m/cata !order-by-expr) !ordering] ...]
                :limit            (m/cata ?limit-expr)
                :offset           (m/cata ?offset-expr)
                ::bq/rows-between [(m/cata !rows-between-expr) ...]
                ::bq/partition-by [(m/cata !partition-by-expr) ...]})

        (m/and (m/pred (partial instance? SqlCall) ?call)
               {:args (m/seqable !arg ...)})
        (m/app assoc ?call :args (m/seqable (m/cata !arg) ...))

        ?? ??)))

(declare normalize-honey)
(defn normalize-expr [expr alias]
  (-> expr
      (m/rewrite
        {(m/some :select) _ :as ?honey}
        (m/app #(normalize-honey % alias) ?honey)

        {(m/or :order-by ::bq/partition-by ::bq/rows-between) _ :as ?windowing-clause}
        (m/app #(normalize-honey % alias) ?windowing-clause)

        (m/and (m/pred (partial instance? SqlCall))
               {:name ?name :args (m/seqable !arg ...)})
        (m/app (partial apply sql/call) ?name [(m/app #(normalize-expr % alias) !arg) ...])

        [(m/pred keyword? ?op) & ?args]
        (m/cata (m/app (fn [op args] (apply sql/call (name op) args)) ?op ?args))

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

        {:select           (m/and (m/gather (m/seqable !col-expr-with-alias !col-expr-alias))
                                  (m/gather (m/and (m/not (m/seqable _ _))
                                                   (m/and !col-expr-no-alias-1
                                                          !col-expr-no-alias-2))))
         :from             (m/and (m/gather (m/seqable !table-expr-with-alias !table-expr-alias))
                                  (m/gather (m/and (m/not (m/seqable _ _))
                                                   (m/and !table-expr-no-alias-1
                                                          !table-expr-no-alias-2))))
         :where            (m/or (m/some ?where-expr)
                                 (m/let [?where-expr true]))
         :group-by         (m/seqable !group-by-expr ...)
         :having           (m/seqable !having-expr ...)
         :order-by         (m/seqable !order-by-expr ...)
         :limit            ?limit
         :offset           ?offset

         ; windowing clause entries
         ::bq/partition-by (m/seqable !partition-expr ...)
         ::bq/rows-between (m/seqable !rows-between-expr ...)}
        {:select           [[(m/app #(normalize-expr % alias) !col-expr-with-alias) !col-expr-alias] ...
                            [(m/app #(normalize-expr % alias) !col-expr-no-alias-1) (m/app alias !col-expr-no-alias-2)] ...]
         :from             [[(m/app #(normalize-expr % alias) !table-expr-with-alias) !table-expr-alias] ...
                            [(m/app #(normalize-expr % alias) !table-expr-no-alias-1) (m/app alias !table-expr-no-alias-2)] ...]
         :where            (m/app #(normalize-expr % alias) ?where-expr)
         :group-by         [(m/app #(normalize-expr % alias) !group-by-expr) ...]
         :having           [(m/app #(normalize-expr % alias) !having-expr) ...]
         :order-by         [(m/app #(normalize-order-by-expr % alias) !order-by-expr) ...]
         :limit            ?limit
         :offset           ?offset

         ; windowing clause entries
         ::bq/partition-by [(m/app #(normalize-expr % alias) !partition-expr) ...]
         ::bq/rows-between [!rows-between-expr ...]})))

(comment
  (-> {:select [[{:select [[:a :a]] :from []} :a]]
       :from   []}
      (normalize-honey identity)
      (simplify)))

(def constant? (comp (some-fn #{Boolean Long String} nil?) (partial class)))

(declare optimize-honey)
(defn optimize-expr [expr]
  (-> expr
      (m/rewrite
        (m/and (m/pred (partial instance? SqlCall) ?call)
               {:args (m/seqable !expr ...)})
        (m/app assoc ?call :args (m/seqable (m/cata !expr) ...))

        (m/and {(m/or (m/some :select)
                      (m/some :order-by)) _
                :as                       ?honey})
        (m/app optimize-honey ?honey)

        ?? ??)))

(defn optimize-honey [normalized-honey]
  (-> normalized-honey
      (m/rewrite
        {(m/and (m/or ::bq/with :with) ?with) [[!query !query-alias] ...]
         &                                    ?rest}
        {?with (m/map-of !query-alias (m/cata !query))
         &     (m/cata ?rest)}

        {:select           [[!col-expr !col-alias] ...]
         :from             [[!from-expr !from-alias] ...]
         :where            ?where-expr
         :group-by         [!group-by-expr ...]
         :having           [!having-expr ...]
         :order-by         [[!order-by-expr !order] ...]
         :limit            ?limit-expr
         :offset           ?offset-expr
         ::bq/partition-by [!partition-by-expr ...]
         ::bq/rows-between [!rows-between-expr ...]}
        {:select           (m/map-of !col-alias (m/app optimize-expr !col-expr))
         :from             [[(m/app optimize-expr !from-expr) !from-alias] ...]
         :where            (m/app optimize-expr ?where-expr)
         :group-by         [(m/app optimize-expr !group-by-expr) ...]
         :having           [(m/app optimize-expr !having-expr) ...]
         :order-by         [[(m/app optimize-expr !order-by-expr) !order] ...]
         :limit            (m/app optimize-expr ?limit-expr)
         :offset           (m/app optimize-expr ?offset-expr)
         ::bq/rows-between [(m/app optimize-expr !rows-between-expr) ...]
         ::bq/partition-by [(m/app optimize-expr !partition-by-expr) ...]})))

(defn my-group-by [kfn vals-fn coll]
  (into {} (x/by-key kfn vals-fn (x/into []))
        coll))

(defn cols-to-push [optimized-honey qualified-col? unqualified-col? col-table-ref unqualified-col]
  (my-group-by second
               first
               (-> [optimized-honey [::query] {} []]
                   (m/rewrite
                     [{(m/or ::bq/with :with) [[!query !query-alias] ...]} ?location ?alias->location ?cols-to-push]
                     [(m/cata [!query [!query-alias & ?location] ?alias->location ?cols-to-push]) ...]

                     [{:select           (m/map-of _ !expr)
                       :from             (m/and [[?table-expr ?table-alias] & _]
                                                (m/gather [{(m/some :select) _ :as !table-expr} !table-alias]))
                       :where            (m/or (m/pred (complement true?) !expr)
                                               (m/let [[!expr ...] []]))
                       :group-by         [!expr ...]
                       :having           [!expr ...]
                       :order-by         [[!expr _] ...]
                       :limit            (m/or (m/pred (complement nil?) !expr)
                                               (m/let [[!expr ...] []]))
                       :offset           (m/or (m/pred (complement nil?) !expr)
                                               (m/let [[!expr ...] []]))
                       ::bq/partition-by [!expr ...]
                       ::bq/rows-between [!expr ...]}
                      ?location {& ?alias->location} ?cols-to-push]
                     [(m/cata [!expr [?table-expr & ?location]
                               {&            ?alias->location
                                ?table-alias [?table-expr & ?location]}
                               ?cols-to-push]) ...
                      (m/cata [!table-expr [?table-expr & ?location]
                               {&            ?alias->location
                                ?table-alias [?table-expr & ?location]}
                               ?cols-to-push]) ...]

                     [(m/and (m/pred (partial instance? SqlCall) ?call)
                             {:args (m/seqable !arg ...)})
                      ?location ?alias->location ?cols-to-push]
                     [(m/cata [!arg ?location ?alias->location ?cols-to-push]) ...]

                     [(m/and (m/pred qualified-col? ?qualified-col)
                             (m/let [?table-alias (col-table-ref ?qualified-col)
                                     ?col (unqualified-col ?qualified-col)]))
                      ?location ?alias->location ?cols-to-push]
                     [[?col (m/app get ?alias->location ?table-alias)] & ?cols-to-push]

                     [(m/pred constant? _) _ _ _]
                     []

                     [?col ?location ?alias->location ?cols-to-push]
                     [[?col ?location] & ?cols-to-push])
                   (m/rewrite
                     [(m/pred unqualified-col? ?col) ?location]
                     [[?col ?location]]

                     [[[] & ?rest]]
                     (m/cata ?rest)

                     [!element ...]
                     (m/app (partial apply concat) [(m/cata !element) ...])))))

(comment
  (let [optimized-honey (-> {:select [:a]
                             :from   [[:t :outer]]
                             :where  (sql/call "exists" {:select [1]
                                                         :from   [[:t :inner]]
                                                         :where  [:= :outer/k :inner/k]})}
                            (normalize-honey identity)
                            (optimize-honey))]
    (time (dotimes [_ 10000]
            (cols-to-push optimized-honey qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name)))))

  #_{:select [:a] :from [[:t :v]]}
  #_{:select [:a] :from [[{:select [] :from [:t]} :v]]}
  #_{:select [:v/a] :from [[:t :v]]}
  #_{:select [[(sql/call "count" :a) :count-a]] :from [[{:select [] :from [:t]} :v]]}
  #_{:select [:a]
     :from   [[:t :outer]]
     :where  (sql/call "exists" {:select [1]
                                 :from   [[:t :inner]]
                                 :where  [:= :outer/k :inner/k]})}
  #_{:select [:a]
     :from   [[:t :outer]]
     :where  [:= :k {:select [[(sql/call "MAX" :b) :max-b]]
                     :from   [[:t :inner]]}]}
  #_{:with   [[{:select [] :from [:physical]} :t]]
     :select [:a]
     :from   [[:t :outer]]
     :where  [:= :k {:select [[(sql/call "MAX" :b) :max-b]]
                     :from   [[:t :inner]]
                     :where  [:= :inner/k :outer/k]}]})

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

(defn table-deps [optimized-honey table-name?]
  (partition 2 (-> optimized-honey
                   (m/rewrite
                     [?table-name {(m/some :args) (m/gather (m/pred map? !expr))}]
                     [(m/cata [?table-name !expr]) ...]

                     [?table-name {:select           (m/gather [_ (m/pred map? !expr)])
                                   :from             (m/and (m/gather [(m/pred table-name? !dep-table-name) _])
                                                            (m/gather [(m/pred map? !expr) _]))
                                   :where            !expr
                                   :group-by         (m/gather [(m/pred map? !expr)])
                                   :having           (m/gather [(m/pred map? !expr)])
                                   :order-by         (m/gather [(m/pred map? !expr) _])
                                   ::bq/partition-by (m/gather (m/pred map? !expr))}]
                     [[?table-name !dep-table-name] ... (m/cata [?table-name !expr]) ...]

                     {(m/or :with ::bq/with) (m/map-of !cte-name !cte-expr)
                      (m/some :from)         _ :as ?query}
                     [(m/cata [!cte-name !cte-expr]) ... & (m/cata [::query ?query])]

                     _ [])
                   (flatten))))

(defn topo-sort [optimized-honey table-name?]
  (into [] (filter (complement nil?))
        (-> (reduce (fn [graph [source dep]]
                      (dep/depend graph dep source))
                    (dep/graph)
                    (table-deps optimized-honey table-name?))
            (dep/topo-sort))))

(defn reverse-optimize-honey [optimized-honey table-name?]
  (let [view-order (zipmap (topo-sort optimized-honey table-name?)
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

          {:select           (m/map-of !col-alias !col-expr)
           :from             [[!table-expr !table-alias] ...]
           :where            ?where-expr
           :group-by         [!group-by-expr ...]
           :having           [!having-expr ...]
           :order-by         [[!order-by-expr !ordering] ...]
           :limit            ?limit-expr
           :offset           ?offset-expr
           ::bq/partition-by [!partition-by-expr ...]
           ::bq/rows-between [!rows-between-expr ...]}
          {:select           [[(m/cata !col-expr) !col-alias] ...]
           :from             [[(m/cata !table-expr) !table-alias] ...]
           :where            (m/cata ?where-expr)
           :group-by         [(m/cata !group-by-expr) ...]
           :having           [!having-expr ...]
           :order-by         [[(m/cata !order-by-expr) !ordering] ...]
           :limit            (m/cata ?limit-expr)
           :offset           ?offset-expr
           ::bq/partition-by [(m/cata !partition-by-expr) ...]
           ::bq/rows-between [(m/cata !rows-between-expr) ...]}

          (m/and (m/pred (partial instance? SqlCall) ?call)
                 {:args (m/seqable !arg ...)})
          (m/app assoc ?call :args (m/seqable (m/cata !arg) ...))

          ?? ??))))

(defn push-down [normalized-honey table-name? qualified-col? unqualified-col? col-table-ref unqualified-col]
  (loop [optimized-honey (optimize-honey normalized-honey)
         prev nil]
    (if (= prev optimized-honey)
      (reverse-optimize-honey optimized-honey table-name?)
      (recur (incorporate-cols
               optimized-honey
               (cols-to-push optimized-honey qualified-col? unqualified-col? col-table-ref unqualified-col))
             optimized-honey))))

(comment
  (-> {:with   [[{:select [] :from [:y]} :x]
                [{:select [] :from [:z]} :y]]
       :select [:a [(sql/call "FIRST_VALUE" {:select [:b] :from [:x]}) :c]] :from [:x]}
      (normalize-honey identity)
      (push-down table-name? qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name))
      (simplify)))

(deftest optimized-honey
  (is (= {:from [[:t :t]], :select [[:a :a] [:b :b]]}
         (-> {:select [:a :b] :from [:t]}
             (normalize-honey identity)
             (optimize-honey)
             (reverse-optimize-honey table-name?)
             (simplify))))

  (is (= {:from [[:t :t-alias]], :select [[:a :a-alias] [:b :b-alias]]}
         (-> {:select [[:a :a-alias] [:b :b-alias]] :from [[:t :t-alias]]}
             (normalize-honey identity)
             (optimize-honey)
             (reverse-optimize-honey table-name?)
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

  (is (= {:select [[:a :a]], :from [[:t :t]], :where (sql/call "exists" {:select [[:b :b]], :from [[:s :s]]})}
         (-> {:select [:a] :from [:t]
              :where  (sql/call "exists" {:select [:b] :from [:s]})}
             (normalize-honey identity)
             (simplify))))

  (is (= {:select [[(sql/call "and" (sql/call "=" :a :c) :b) :alias]
                   [{:select [[:inner :inner]], :from [[:s :s]]} :select-alias]
                   [:a :a]],
          :from   [[:t :t]]}
         (-> {:select [:a
                       [(sql/call "and" (sql/call "=" :a :c) :b) :alias]
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
             (simplify))))

  (is (= {:select [[(sql/call "WINDOW"
                              (sql/call "LAST_VALUE" :col)
                              {:bq/rows-between [(sql/inline "UNBOUNDED PRECEDING") (sql/inline "CURRENT ROW")],
                               :order-by        [[:timestamp :asc]],
                               :bq/partition-by [:caseId]})
                    :alias]]
          :from   [[:t :t]]}
         (-> {:select [[(sql/call "WINDOW" (sql/call "LAST_VALUE" :col)
                                  {::bq/partition-by [:caseId]
                                   :order-by         [:timestamp]
                                   ::bq/rows-between [(sql/inline "UNBOUNDED PRECEDING")
                                                      (sql/inline "CURRENT ROW")]}) :alias]]
              :from   [:t]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:where (sql/call "=" :inner/a :outer/a), :from [[:t :inner]], :select [[(sql/call "MAX" :b) :max-b]]}
         (-> {:select [[(sql/call "MAX" :b) :max-b]]
              :from   [[:t :inner]]
              :where  [:= :inner/a :outer/a]}
             (normalize-honey identity)
             (simplify)))))

(deftest normalize-from-exprs
  (is (= {:from [[:a :a]]}
         (-> {:from [[:a :a]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:from [[:a :a]]}
         (-> {:from [:a]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:from [[:a :a] [:b :b]]}
         (-> {:from [:a :b]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:from [[:b :c] [:a :a]]}
         (-> {:from [:a [:b :c]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:from [[:a :b] [:b :c]]}
         (-> {:from [[:a :b] [:b :c]]}
             (normalize-honey identity)
             (simplify)))))

(deftest sub-selects
  (is (= {:select [[{:from [[{:from [[:t :t]], :select [[:a :a]]} :t]], :select [[:a :a] [:b :b]]} :alias]]}
         (-> {:select [[{:select [:a :b] :from [[{:select [:a] :from [:t]} :t]]} :alias]]}
             (normalize-honey identity)
             (optimize-honey)
             (reverse-optimize-honey table-name?)
             (simplify)))))

(deftest with-clause
  (is (= {:from [[:v :v]], :select [[1 :a]], :with [[{:from [[:t :t]], :select [[:a :a]]} :v]]}
         (-> {:with   [[{:select [:a] :from [:t]} :v]]
              :select [[1 :a]]
              :from   [:v]}
             (normalize-honey identity)
             (optimize-honey)
             (reverse-optimize-honey table-name?)
             (simplify)))))

(deftest push-downs
  (is (= {:select [[:a :a]]}
         (-> {:select [:a]}
             (normalize-honey identity)
             (push-down table-name? qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:select [[:a :a]] :from [[:t :t]]}
         (-> {:select [:a] :from [:t]}
             (normalize-honey identity)
             (push-down table-name? qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= '{:select [(:a :a)],
           :from   [[:x :x]],
           :with   [[{:select [(:a :a)], :from [[:z :z]]} :y]
                    [{:select [(:a :a)], :from [[:y :y]]} :x]]}
         (-> {:with   [[{:select [] :from [:y]} :x]
                       [{:select [] :from [:z]} :y]]
              :select [:a] :from [:x]}
             (normalize-honey identity)
             (push-down table-name? qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:select [[(sql/call "WINDOW"
                              (sql/call "LAST_VALUE" :col)
                              {:bq/rows-between [(sql/inline "UNBOUNDED PRECEDING") (sql/inline "CURRENT ROW")],
                               :order-by        [[:timestamp :asc]],
                               :bq/partition-by [:caseId]})
                    :alias]],
          :from   [[:v :v]],
          :with   [[{:select [[:col :col] [:timestamp :timestamp] [:caseId :caseId]], :from [[:t :t]]} :v]]}
         (-> {:with   [[{:select [] :from [:t]} :v]]
              :select [[(sql/call "WINDOW" (sql/call "LAST_VALUE" :col)
                                  {::bq/partition-by [:caseId]
                                   :order-by         [:timestamp]
                                   ::bq/rows-between [(sql/inline "UNBOUNDED PRECEDING")
                                                      (sql/inline "CURRENT ROW")]}) :alias]]
              :from   [:v]}
             (normalize-honey identity)
             (push-down table-name? qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:with [[{:from [[:z :z]], :select [[:a :a] [:b :b]]} :y]
                 [{:from [[:y :y]], :select [[:a :a] [:b :b]]} :x]],
          :from [[:x :x]],
          :select [[(sql/call "FIRST_VALUE" {:from [[:x :x]], :select [[:b :b]]}) :c] [:a :a]]}
         (-> {:with   [[{:select [] :from [:y]} :x]
                       [{:select [] :from [:z]} :y]]
              :select [:a [(sql/call "FIRST_VALUE" {:select [:b] :from [:x]}) :c]] :from [:x]}
             (normalize-honey identity)
             (push-down table-name? qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= #{[:a :t] [:c :t] [:b :t] [:inner :s]}
         (-> {:select [:a
                       [(sql/call "and" (sql/call "=" :a :c) :b) :alias]
                       [{:select [:inner] :from [:s]} :select-alias]] :from [:t]}
             (normalize-honey identity)
             (optimize-honey)
             (cols-to-push qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name)))))

  (is (= #{[:a :t] [:a :s]}
         (-> {:select [:a] :from [[{:select [:a] :from [:s]} :t]]}
             (normalize-honey identity)
             (optimize-honey)
             (cols-to-push qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name)))))

  (is (= #{[:b :t] [:a :v]}
         (-> {:with   [[{:select [:b] :from [:t]} :v]]
              :select [:a] :from [:v]}
             (normalize-honey identity)
             (optimize-honey)
             (cols-to-push qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name))))))

(deftest topo-sorts
  (is (= [] (-> {:select [] :from [:v]}
                (normalize-honey identity)
                (optimize-honey)
                (topo-sort table-name?))))

  (is (= [::query :v] (-> {:with   [[{:select [] :from []} :v]]
                           :select [] :from [:v]}
                          (normalize-honey identity)
                          (optimize-honey)
                          (topo-sort table-name?))))

  (is (= [::query :v :x] (-> {:with   [[{:select [] :from [:x]} :v]
                                       [{:select [] :from []} :x]]
                              :select [] :from [:v]}
                             (normalize-honey identity)
                             (optimize-honey)
                             (topo-sort table-name?))))

  (is (= [::query :v :x] (-> {:with   [[{:select [] :from [:x]} :v]
                                       [{:select [] :from []} :x]]
                              :select [[{:select [:a] :from [:x]} :b]]}
                             (normalize-honey identity)
                             (optimize-honey)
                             (topo-sort table-name?)))))

(comment
  {::bq/with [[{:select [:e :o]
                :from   [[(sql/call "UNNEST" (sql/call "ARRAY"
                                                       (sql/call "STRUCT" ["Stage" :e] [0 :o])
                                                       (sql/call "STRUCT" ["Flow" :e] [1 :o])
                                                       (sql/call "STRUCT" ["Flow Name" :e] [2 :o])
                                                       (sql/call "STRUCT" ["Child Count" :e] [3 :o])))
                          :ordering]]}
               :event-ordering]
              [{:select [] :from [:t]} :v]]
   :select   [[(sql/call "WINDOW" (sql/call "IGNORE_NULLS" (sql/call "LAST_VALUE" :attributes/stageName))
                         {::bq/partition-by [:attributes/caseId]
                          :order-by         [:timestamp {:select [:o]
                                                         :from   [:event-ordering]
                                                         :where  [:= :entity-projected-data/event :e]}]
                          ::bq/rows-between [(sql/inline "UNBOUNDED PRECEDING")
                                             (sql/inline "CURRENT ROW")]})
               :event]]
   :where    [:and
              [:= "Stage" :event]                           ; important to preserve :event push down
              [:<> nil :attributes/caseId]
              [:<> "" :attributes/caseId]]
   :from     [:v]})

(comment
  (time (dotimes [_ 10000]
          (-> {:with   [[{:select [] :from [:physical]} :t]
                        [{:select [] :from [:t]} :v]
                        [{:select [] :from [:v]} :u]]
               :select [:a [(sql/call "FIRST_VALUE" {:select [:b] :from [:u]}) :c]]}
              (normalize-honey identity)
              (push-down table-name? qualified-col? unqualified-col? (comp keyword namespace) (comp keyword name))
              (simplify)))))