#lang info

;; A multi-collection package: it adds `shplait/liquid` to the `shplait`
;; collection, so the language is `#lang shplait/liquid`.
(define collection 'multi)
(define version "0.3")
(define deps '(("base" #:version "9.3") "rhombus-lib" "shrubbery-lib" "shplait"))
(define build-deps '("scribble-lib" "rhombus-scribble-lib" "rackunit-lib"))
(define pkg-desc "Refinement (liquid) types for Shplait, checked at compile time with Z3")
(define language-families '("Rhombus"))
(define license 'MIT)
