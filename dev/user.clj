(ns user
  (:require [portal.api :as inspect]))

;; Start Portal inspector on REPL start

;; Open a portal inspector window
(inspect/open)

;; Add portal as a tap> target
(inspect/tap)


(comment
  ;; Clear all values in the portal inspector window
  (inspect/clear)

  ;; Close the inspector
  (inspect/close)

  ) ;; End of rich comment block