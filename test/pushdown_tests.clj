(ns pushdown-tests
  (:require [clojure.test :refer :all]
            [sql-rewrite :refer :all]
            [bq :as bq]
            [honeysql.core :as sql]
            [criterium.core :refer [bench quick-bench]]))
(comment
  (quick-bench
    (-> {:with   [[{:select [] :from [:physical]} :t]
                  [{:select [] :from [:t]} :v]
                  [{:select [] :from [:v]} :u]]
         :select [:a [(sql/call "FIRST_VALUE" {:select [:b] :from [:u]}) :c]]}
        (normalize-honey identity)
        (push-down (comp keyword namespace) (comp keyword name))
        (simplify))))

(deftest optimize
  (is (= {:from [[:t :t]], :select [[:a :a] [:b :b]]}
         (-> {:select [:a :b] :from [:t]}
             (normalize-honey identity)
             (optimize-honey)
             (reverse-optimize-honey)
             (simplify))))

  (is (= {:from [[:t :t-alias]], :select [[:a :a-alias] [:b :b-alias]]}
         (-> {:select [[:a :a-alias] [:b :b-alias]] :from [[:t :t-alias]]}
             (normalize-honey identity)
             (optimize-honey)
             (reverse-optimize-honey)
             (simplify)))))

(deftest normalize
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
             (simplify))))

  (is (= {:from [[:x :x]], :select [[:a :a]], :with [[{:from [[:z :z]]} :y] [{:from [[:y :y]]} :x]]}
         (-> {:with   [[{:from [[:z :z]]} :y]
                       [{:from [[:y :y]]} :x]]
              :select [[:a :a]]
              :from   [[:x :x]]}
             (normalize-honey identity)
             (simplify))))

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

  (is (= {:from [[:a :a] [:b :c]]}
         (-> {:from [:a [:b :c]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:from [[:a :b] [:b :c]]}
         (-> {:from [[:a :b] [:b :c]]}
             (normalize-honey identity)
             (simplify))))

  (is (= {:from [[{:union-all [{:from [[:t1 :t1]]} {:from [[:t2 :t2]]}]} :t]], :select [[:a :a]]}
         (-> {:select [:a]
              :from   [[{:union-all [{:select [] :from [:t1]}
                                     {:select [] :from [:t2]}]} :t]]}
             (normalize-honey identity)
             (simplify)))))

(deftest push-downs
  (is (= {:select [[:a :a]]}
         (-> {:select [:a]}
             (normalize-honey identity)
             (push-down (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:select [[:a :a]] :from [[:t :t]]}
         (-> {:select [:a] :from [:t]}
             (normalize-honey identity)
             (push-down (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= '{:select [[:a :a]],
           :from   [[:x :x]],
           :with   [[{:select [[:a :a]], :from [[:z :z]]} :y]
                    [{:select [[:a :a]], :from [[:y :y]]} :x]]}
         (-> {:with   [[{:select [] :from [:y]} :x]
                       [{:select [] :from [:z]} :y]]
              :select [:a] :from [:x]}
             (normalize-honey identity)
             (push-down (comp keyword namespace) (comp keyword name))
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
             (push-down (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:with   [[{:from [[:z :z]], :select [[:b :b] [:a :a]]} :y]
                   [{:from [[:y :y]], :select [[:b :b] [:a :a]]} :x]],
          :from   [[:x :x]],
          :select [[(sql/call "FIRST_VALUE" {:from [[:x :x]], :select [[:b :b]]}) :c] [:a :a]]}
         (-> {:with   [[{:select [] :from [:y]} :x]
                       [{:select [] :from [:z]} :y]]
              :select [:a [(sql/call "FIRST_VALUE" {:select [:b] :from [:x]}) :c]] :from [:x]}
             (normalize-honey identity)
             (push-down (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:from   [[:t :t]],
          :select [[(sql/call "and" (sql/call "=" :a :c) :b) :alias]
                   [{:from [[:s :s]], :select [[:inner :inner]]} :select-alias]
                   [:a :a]]}
         (-> {:select [:a
                       [(sql/call "and" (sql/call "=" :a :c) :b) :alias]
                       [{:select [:inner] :from [:s]} :select-alias]] :from [:t]}
             (normalize-honey identity)
             (push-down (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:from [[{:from [[:s :s]], :select [[:a :a]]} :t]], :select [[:a :a]]}
         (-> {:select [:a] :from [[{:select [:a] :from [:s]} :t]]}
             (normalize-honey identity)
             (push-down (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:from [[:v :v]], :select [[:a :a]], :with [[{:from [[:t :t]], :select [[:b :b] [:a :a]]} :v]]}
         (-> {:with   [[{:select [:b] :from [:t]} :v]]
              :select [:a] :from [:v]}
             (normalize-honey identity)
             (push-down (comp keyword namespace) (comp keyword name))
             (simplify))))

  (is (= {:select [[{:from [[{:from [[:t :t]], :select [[:a :a]]} :t]], :select [[:a :a] [:b :b]]} :alias]]}
         (-> {:select [[{:select [:a :b] :from [[{:select [:a] :from [:t]} :t]]} :alias]]}
             (normalize-honey identity)
             (optimize-honey)
             (reverse-optimize-honey)
             (simplify))))

  (is (= {:from [[:v :v]], :select [[1 :a]], :with [[{:from [[:t :t]], :select [[:a :a]]} :v]]}
         (-> {:with   [[{:select [:a] :from [:t]} :v]]
              :select [[1 :a]]
              :from   [:v]}
             (normalize-honey identity)
             (optimize-honey)
             (reverse-optimize-honey)
             (simplify))))

  (is (= {}
         (-> {:with   [[{:union-all [{:select [] :from [:y]}
                                     {:select [] :from [:x]}]} :v]]
              :select [:a]
              :from   [:v]}
             (normalize-honey identity)
             (push-down (comp keyword namespace) (comp keyword name))
             (simplify)))))

(deftest topo-sorts
  (is (= [] (-> {:select [] :from [:v]}
                (normalize-honey identity)
                (optimize-honey)
                (topo-sort))))

  (is (= [:sql-rewrite/query :v]
         (-> {:with   [[{:select [] :from []} :v]]
              :select [] :from [:v]}
             (normalize-honey identity)
             (optimize-honey)
             (topo-sort))))

  (is (= [:sql-rewrite/query :v :x]
         (-> {:with   [[{:select [] :from [:x]} :v]
                       [{:select [] :from []} :x]]
              :select [] :from [:v]}
             (normalize-honey identity)
             (optimize-honey)
             (topo-sort))))

  (is (= [:sql-rewrite/query :v :x]
         (-> {:with   [[{:select [] :from [:x]} :v]
                       [{:select [] :from []} :x]]
              :select [[{:select [:a] :from [:x]} :b]]}
             (normalize-honey identity)
             (optimize-honey)
             (topo-sort)))))
