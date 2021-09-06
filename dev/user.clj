(ns user)

(comment
  (require '[vlaaad.reveal :as reveal])
  (add-tap (reveal/ui)))

(defn echo [x]
  (tap> x)
  x)