#lang racket/base

;; `#lang shplait/liquid` = shplait + the refinement-type extension.
;;
;; The reader injects
;;
;;     import: open: lib("shplait/liquid/refinements.rhm")
;;
;; ahead of the user's body, which puts the refinement-aware `fun`
;; and `def` wrappers (and the refinement-brace type form) in scope
;; before shplait's type checker sees anything.  Everything else is
;; plain shplait, plus the built-in functions of builtins.rhm
;; (`unreachable`, `assert`).  Those are provided here, by the module
;; language, rather than by the prelude: a program may define its own
;; function of the same name, which shadows a module-language binding
;; but would collide with an `open:` import.

(require shplait
         (only-in shplait
                  [#%top-interaction shplait-top-interaction]
                  [#%module-begin shplait-module-begin])
         (for-syntax racket/base "liquid/interaction.rkt")
         "liquid/builtins.rhm"
         ;; not used here: user programs import it through the reader's
         ;; prelude, and requiring it makes `raco make liquid.rkt` (and
         ;; `raco setup`) compile it, which matters: uncompiled, it is
         ;; re-expanded on every run, about two seconds each time
         (only-in "liquid/refinements.rhm"))
(provide (except-out (all-from-out shplait) #%top-interaction #%module-begin)
         (all-from-out "liquid/builtins.rhm")
         (rename-out [liquid-top-interaction #%top-interaction]
                     [liquid-module-begin #%module-begin]))

;; The module body, handed to the checker's finish hook (see
;; interaction.rkt): the top-level check must see the text being
;; compiled, which in DrRacket is the buffer, saved or not.
(define-syntax (liquid-module-begin stx)
  (syntax-case stx ()
    [(_ . body)
     (begin
       (set-module-body! #'body)
       #'(shplait-module-begin . body))]))

;; The interactions window: remember the form typed at the prompt, so
;; that the refinement layer's finish hook (which shplait calls with
;; `'interaction` once the form is expanded) can check the calls in
;; it; then hand the form to shplait as usual.
(define-syntax (liquid-top-interaction stx)
  (syntax-case stx ()
    [(_ . form)
     (begin
       (set-interaction-form! #'form)
       #'(shplait-top-interaction . form))]))

(module reader syntax/module-reader
  #:language '(lib "shplait/liquid.rkt")
  #:info (lambda (key default make-default)
           ;; DrRacket asks here for the colour lexer, indentation and
           ;; the rest; delegate to Rhombus's shrubbery support, with
           ;; Shplait's operator variant and keyword classification.
           (define get-info-proc (dynamic-require '(submod rhombus reader) 'get-info-proc))
           (case key
             [(documentation-language-family) "Shplait"]
             [else (get-info-proc key default make-default
                                  #:variant shplait-variant
                                  #:semantic-type-guess shplait-type-guess)]))
  #:read read-liquid
  #:read-syntax read-liquid-syntax
  #:whole-body-readers? #t

  (require shrubbery/parse
           shrubbery/variant
           racket/promise
           racket/port)

  ;; Shplait's reader variant, copied from shplait/main.rkt: operators
  ;; may not start with `|` (except `||`), so `| ~else:` is never read
  ;; as one operator, and `$`/`...` do not continue a line.
  (define shplait-variant
    (make-variant #:allow-operator? (lambda (str)
                                      (cond
                                        [(equal? (string-ref str 0) #\|) (equal? str "||")]
                                        [else #t]))
                  #:indented-operator-continue? (lambda (str)
                                                  (not (or (equal? str "$") (equal? str "..."))))))
  (define shplait-type-guess
    (let ([classify (delay (dynamic-require '(lib "shplait/private/syntax_color.rhm") 'classify))])
      (lambda (str default) ((force classify) str))))


  (define prelude-text
    "import:\n  open: lib(\"shplait/liquid/refinements.rhm\")\n\n")

  ;; Placed last: persists the module's records for the interactions
  ;; window (see refinements.rhm).
  (define trailer-text "\nliquid_module_end()\n")

  ;; Splice two parse-all results — each shaped `(multi <group> ...)`
  ;; — into one combined `(multi <prelude-groups> ... <body-groups> ...)`,
  ;; using the body's syntax for source-location inheritance.
  (define (splice-multis prelude-stx body-stx)
    (define prelude-parts (syntax->list prelude-stx))
    (define body-parts (syntax->list body-stx))
    (datum->syntax body-stx
                   (cons (car body-parts)
                         (append (cdr prelude-parts) (cdr body-parts)))
                   body-stx))

  (define (read-liquid-syntax src in)
    (define prelude-stx
      (parse-all (open-input-string prelude-text)
                 #:source 'shplait-liquid-prelude))
    (define trailer-stx
      (parse-all (open-input-string trailer-text)
                 #:source 'shplait-liquid-trailer))
    (define body-stx (parse-all in #:source src #:variant shplait-variant))
    (list (splice-multis prelude-stx (splice-multis body-stx trailer-stx))))

  (define (read-liquid in)
    (define prelude-stx (parse-all (open-input-string prelude-text)))
    (define trailer-stx (parse-all (open-input-string trailer-text)))
    (define body-stx (parse-all in #:variant shplait-variant))
    (list (syntax->datum (splice-multis prelude-stx (splice-multis body-stx trailer-stx))))))
