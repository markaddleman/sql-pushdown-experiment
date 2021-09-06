(ns user)

(comment
  (add-tap ((requiring-resolve 'vlaaad.reveal/ui))))

(defn echo [x]
  (tap> x)
  x)