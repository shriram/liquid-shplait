#lang racket/base

;; Compile-time state shared between the language module (main.rkt)
;; and the checker's finish hook: the module body as `#%module-begin`
;; received it, so that the top-level check works on the text being
;; compiled and not on a file that may be out of date (DrRacket runs
;; the buffer, saved or not); and the form typed at the prompt, so that
;; the hook, which is only told "an interaction finished", can check
;; the calls in it.

(provide set-module-body! take-module-body
         set-interaction-form! take-interaction-form)

(define body (box #f))
(define form (box #f))

(define (set-module-body! stx) (set-box! body stx))
(define (take-module-body)
  (define b (unbox body))
  (set-box! body #f)
  b)

(define (set-interaction-form! stx) (set-box! form stx))
(define (take-interaction-form)
  (define f (unbox form))
  (set-box! form #f)
  f)
