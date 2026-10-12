#lang info

(define scribblings '(("scribblings/liquid-shplait.scrbl" (multi-page) (language))))
;; The tests and examples are checked with Z3 when they compile, so
;; `raco setup` leaves them alone (a package build server may not have
;; Z3); `raco test` compiles and runs them.
(define compile-omit-paths '("tests" "examples"))
