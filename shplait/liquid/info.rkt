#lang info

(define scribblings '(("scribblings/liquid-shplait.scrbl" (multi-page) (language))))
;; The tests and examples are checked with Z3 when they compile, so
;; `raco setup` leaves them alone (a package build server may not have
;; Z3); `raco test` compiles and runs them.
(define compile-omit-paths '("tests" "examples"))

;; The tests run Z3, which the package build service does not have; it
;; sets PLT_PKG_BUILD_SERVICE, so they are skipped there (and run
;; everywhere else, failing if Z3 is missing).
(define test-omit-paths (if (getenv "PLT_PKG_BUILD_SERVICE") 'all '()))
