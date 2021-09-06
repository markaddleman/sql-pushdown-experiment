(ns sql-rewrite
  (:require [meander.epsilon :as m]
            [net.cgrand.xforms :as x]
            [bq :as bq]
            [weavejester.dependency :as dep]
            [honeysql.core :as sql]
            [clojure.string :as str])
  (:import [honeysql.types SqlCall]))

; joins
; unions
; intersection
; push down already fully qualified columns

(defn remove-unused-clauses [normalized-honey]
  (into {} (filter (complement #{[:select []]
                                 [:from []]
                                 [:join []]
                                 [:left-join []]
                                 [:right-join []]
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
         :join             [[!join-expr !join-alias] !join-condition ...]
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
                :join             [[(m/cata !join-expr) !join-alias] (m/cata !join-condition) ...]
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
  (letfn [(vectorize [x] (if-not (vector? x)
                           [x x]
                           x))]
    (-> honey
        (m/rewrite
          [?expr ?alias]
          [(m/app #(normalize-expr % alias) ?expr) ?alias]

          {(m/and (m/or ::bq/with :with) ?with) (m/some (m/seqable (m/seqable !query !query-alias) ...))
           &                                    ?rest}
          {?with [[(m/cata !query) (m/app alias !query-alias)] ...]
           &     (m/cata ?rest)}

          {:select           (m/and (m/gather (m/seqable !col-expr-with-alias !col-expr-alias))
                                    (m/gather (m/and (m/not (m/seqable _ _))
                                                     (m/and !col-expr-no-alias-1
                                                            !col-expr-no-alias-2))))
           :from             (m/seqable !from ...)
           :join             (m/seqable !join !join-condition ...)
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
           :from             [(m/cata (m/app vectorize !from)) ...]
           :join             [(m/cata (m/app vectorize !join)) (m/app #(normalize-expr % alias) !join-condition) ...]
           :where            (m/app #(normalize-expr % alias) ?where-expr)
           :group-by         [(m/app #(normalize-expr % alias) !group-by-expr) ...]
           :having           [(m/app #(normalize-expr % alias) !having-expr) ...]
           :order-by         [(m/app #(normalize-order-by-expr % alias) !order-by-expr) ...]
           :limit            ?limit
           :offset           ?offset

           ; windowing clause entries
           ::bq/partition-by [(m/app #(normalize-expr % alias) !partition-expr) ...]
           ::bq/rows-between [!rows-between-expr ...]}))))

(comment
  (-> {:with   [[{:from [[:z :z]]} :y]
                [{:from [[:y :y]]} :x]]
       :select [[:a :a]]
       :from   [[:x :x]]}
      (normalize-honey identity)))

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
         :from             (m/and (m/or [[?default-from-expr ?default-from-alias] & _]
                                        (m/let [?default-from-expr nil
                                                ?default-from-alias nil]))
                                  [[!from-expr !from-alias] ...])
         :join             [[!join-expr !join-alias] !join-condition ...]
         :where            ?where-expr
         :group-by         [!group-by-expr ...]
         :having           [!having-expr ...]
         :order-by         [[!order-by-expr !order] ...]
         :limit            ?limit-expr
         :offset           ?offset-expr
         ::bq/partition-by [!partition-by-expr ...]
         ::bq/rows-between [!rows-between-expr ...]}
        {:select           (m/map-of !col-alias (m/app optimize-expr !col-expr))
         :from             (m/map-of !from-alias (m/app optimize-expr !from-expr))
         :from-default     {?default-from-alias (m/app optimize-expr ?default-from-expr)}
         :join             [[(m/app optimize-expr !join-expr) !join-alias] (m/app optimize-expr !join-condition) ...]
         :where            (m/app optimize-expr ?where-expr)
         :group-by         [(m/app optimize-expr !group-by-expr) ...]
         :having           [(m/app optimize-expr !having-expr) ...]
         :order-by         [[(m/app optimize-expr !order-by-expr) !order] ...]
         :limit            (m/app optimize-expr ?limit-expr)
         :offset           (m/app optimize-expr ?offset-expr)
         ::bq/rows-between [(m/app optimize-expr !rows-between-expr) ...]
         ::bq/partition-by [(m/app optimize-expr !partition-by-expr) ...]})))


(defn table-deps [optimized-honey]
  (partition 2 (-> optimized-honey
                   (m/rewrite
                     [?table-name {(m/some :args) (m/gather (m/pred map? !expr))}]
                     [(m/cata [?table-name !expr]) ...]

                     [?table-name {:select           (m/gather [_ (m/pred map? !expr)])
                                   :from             (m/and (m/gather [(m/and (m/not {(m/some :select) _})
                                                                              !dep-table-name) _])
                                                            (m/gather [(m/and {(m/some :select) _}
                                                                              !expr) _]))
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

(defn topo-sort [optimized-honey]
  (into [] (filter (complement nil?))
        (-> (reduce (fn [graph [source dep]]
                      (dep/depend graph dep source))
                    (dep/graph)
                    (table-deps optimized-honey))
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

          {:select           (m/map-of !col-alias !col-expr)
           :from             (m/map-of !table-alias !table-expr)
           :join             [[!join-expr !join-alias] !join-condition ...]
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
           :join             [[(m/cata !join-expr) !join-alias] (m/cata !join-condition) ...]
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

(defn my-group-by [kfn vals-fn coll]
  (into [] (x/by-key kfn vals-fn (x/into #{}))
        coll))

(defn push-path [table-alias ctx]
  (m/rewrite ctx
    {?cte-name    _
     ~table-alias {?table-alias ?cte-name}}
    [:with ?cte-name :select]

    {?cte-name _
     nil       {?table-alias ?cte-name}}
    [:with ?cte-name :select]

    {nil {?table-alias {(m/some :select) _}}}
    [:from ?table-alias :select]))

(defn cols-to-push [optimized-honey col-table-ref unqualified-col]
  (my-group-by second first
               (-> [optimized-honey (merge {nil (dissoc optimized-honey :with ::bq/with)}
                                           (:with optimized-honey)
                                           (::bq/with optimized-honey)
                                           (:from optimize-honey))
                    []]
                   (m/rewrite
                     [{(m/or ::bq/with :with) (m/and (m/map-of !query-alias (m/and !query-1 !query-2))
                                                     ?ctes)
                       &                      ?rest}
                      ?ctx ?cols-to-push]
                     [(m/cata [!query-1 {&   ?ctes
                                         nil !query-2} ?cols-to-push]) ...
                      (m/cata [?rest ?ctx ?cols-to-push])]

                     [(m/pred (partial instance? SqlCall)
                              {:name (m/and (m/pred (complement nil?))
                                            (m/pred (comp (partial = "window") str/lower-case name)))
                               :args (m/seqable ?fn {:order-by         [[!expr _] ...]
                                                     ::bq/partition-by [!expr ...]})})
                      ?ctx ?cols-to-push]
                     [(m/cata [?fn ?ctx ?cols-to-push])
                      (m/cata [!expr ?ctx ?cols-to-push]) ...]

                     [(m/pred (partial instance? SqlCall)
                              {:args (m/seqable !arg ...)})
                      ?ctx ?cols-to-push]
                     [(m/cata [!arg ?ctx ?cols-to-push]) ...]

                     [{:from (m/pred empty?)} _ ?cols-to-push]
                     ?cols-to-push

                     [{:select       (m/map-of _ !expr)
                       :from         (m/gather [_ (m/and {(m/some :select) _} !table-expr-1 !table-expr-2)])
                       :from-default ?from-default
                       :where        !expr
                       :group-by     [!expr ...]
                       :having       [!expr ...]
                       :order-by     [[!expr _] ...] :as ?new-ctx}
                      ?ctx ?cols-to-push]
                     [(m/cata [!expr {& ?ctx nil ?from-default} ?cols-to-push]) ...
                      (m/cata [!table-expr-1 ?ctx ?cols-to-push]) ...]

                     [(m/pred constant? _) ?ctx ?cols-to-push]
                     ?cols-to-push

                     [?col ?ctx ?cols-to-push]
                     [{:column  (m/app unqualified-col ?col)
                       :push-to (m/app (fn [col query] (push-path (col-table-ref col) query))
                                       ?col ?ctx)}
                      & ?cols-to-push])
                   (m/rewrite
                     [{(m/some :push-to) nil}]
                     []

                     [{(m/some :column)  ?col
                       (m/some :push-to) ?location}]
                     [[?col ?location]]

                     [[[] & ?rest]]
                     (m/cata ?rest)

                     [!element ...]
                     (m/app (partial apply concat) [(m/cata !element) ...])))))

(comment
  #_{:select [:a] :from [[:t :v]]}
  #_{:select [:a] :from [[{:select [] :from [:t]} :v]]}
  #_{:select [:a] :from [[{:select [:a] :from [:t]} :v]]}
  #_{:select [:v/a] :from [[:t :v]]}
  #_{:select [:v/a] :from [[{:select [] :from [:t]} :v]]}
  #_{:with   [[{:select [] :from [:y]} :x]
              [{:select [] :from [:x]} :t]]
     :select [:a] :from [[{:select [] :from [:t]} :v]]}
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

(defn incorporate-cols [optimized-honey cols-to-push]
  (reduce (fn [optimized-honey [path cols]]
            (try (update-in optimized-honey path (partial apply conj) (sequence (map (fn [c] [c c]))
                                                                                cols))
                 (catch Throwable t
                   (throw (ex-info "Exception incorporating columns"
                                   {:optimized-honey optimized-honey
                                    :path            path
                                    :at-location     (get-in optimized-honey path)
                                    :cols            cols}
                                   t)))))
          optimized-honey
          cols-to-push))

(defn push-down-once [optimized-honey col-table-ref unqualified-col]
  (incorporate-cols optimized-honey (cols-to-push optimized-honey col-table-ref unqualified-col)))

(comment

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

(defn push-down [normalized-honey col-table-ref unqualified-col]
  (loop [i 10
         optimized-honey (optimize-honey normalized-honey)
         prev nil]
    (when (zero? i)
      (throw (ex-info "Too many push down loops"
                      {:optimized-honey optimized-honey})))
    (if (= prev optimized-honey)
      (reverse-optimize-honey optimized-honey)
      (recur (dec i)
             (push-down-once optimized-honey col-table-ref unqualified-col)
             optimized-honey))))


