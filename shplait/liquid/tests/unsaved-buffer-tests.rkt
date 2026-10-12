#lang racket/base

;; DrRacket compiles the definitions window whether or not it is
;; saved.  This runs a module's text plus an extra, "unsaved" line under
;; the file's name, the way DrRacket does, and checks that the extra
;; line is checked.

(require racket/file racket/port racket/string racket/runtime-path rackunit)

(define-runtime-path here ".")

(define (run-unsaved file extra)
  (define text (string-append (file->string file) "\n" extra "\n"))
  (define out (open-output-string))
  (define ok?
    (parameterize ([current-output-port out] [current-error-port out])
      (with-handlers ([exn:fail? (lambda (e) (display (exn-message e) out) #f)])
        (define stx (parameterize ([read-accept-reader #t])
                      (read-syntax file (open-input-string text))))
        (parameterize ([current-namespace (make-base-namespace)]
                       [current-module-declare-name (make-resolved-module-path file)])
          (eval stx)
          (dynamic-require file #f))
        #t)))
  (values ok? (get-output-string out)))

(define module-file (path->complete-path (build-path here "verify" "pass" "measure_ordered_list.rhm")))

(define cases
  ;; (extra line, must compile?, text expected in the output)
  (list (list "insert(1, ocons(0, onil()))" #t "")
        (list "ocons(2, ocons(1, onil()))" #f "the claim `is_onil(t) || ohd(t) >= hd` is violated")
        (list "def bad = ocons(2, ocons(1, onil()))" #f "the claim `is_onil(t) || ohd(t) >= hd` is violated")
        ;; the reachability built-ins, unsaved
        (list "unreachable()" #f "call to `unreachable()`: it is reached")
        (list "assert(ohd(insert(1, onil())) == 1)" #t "")
        (list "assert(ohd(insert(1, onil())) == 2)" #f "is violated")
        ;; polymorphic instantiation, unsaved
        (list "fun idd(x :: ?a) :: ?a: x\nfun keep_ne({l :: OList | !is_onil(l)}) :: {r :: OList | !is_onil(r)}: idd(l)"
              #f "is violated when idd(...) = onil()")
        ;; refinements below the top level, unsaved
        (list "fun outer(n :: Int) :: Int:\n  fun g({y :: Int | y > 0}) :: Int: y\n  g(1)"
              #f "function `g` is defined inside another definition")
        (list "fun outer2(n :: Int) :: Int:\n  def m :: {k :: Int | k > 0} = n * n + 1\n  m"
              #f "`def m` is defined inside another definition")
        (list "def k2 = (let y = 2: y * 2)" #t "")))

(for ([c cases])
  (define-values (ok? out) (run-unsaved module-file (car c)))
  (with-check-info (['extra-line (car c)] ['output (string-trim out)])
    (check-equal? ok? (cadr c) "compiles")
    (check-true (string-contains? out (caddr c))
                (format "output should contain ~s" (caddr c)))))
