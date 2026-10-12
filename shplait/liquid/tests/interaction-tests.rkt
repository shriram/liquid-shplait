#lang racket/base

;; The interactions window is checked like the module.  Runs a module's
;; REPL the way DrRacket does (the module's namespace, the Rhombus
;; interaction reader) and checks what each line produces.

(require racket/system racket/port racket/string racket/runtime-path rackunit)

(define-runtime-path here ".")

(define racket-exe
  (let ([p (find-system-path 'exec-file)])
    (cond [(complete-path? p) p]
          [(find-executable-path p) => values]
          [else (path->complete-path p (find-system-path 'orig-dir))])))

;; Feed the lines (blank-line separated, one interaction each) to the
;; module's REPL; return the combined output.
(define (repl module-path lines)
  ;; stderr merged into stdout at the OS level, so that an error's
  ;; lines and the prompts come out in order
  (define-values (proc out in err)
    (parameterize ([current-directory here])
      (subprocess #f #f 'stdout racket-exe "-e"
                  (format "(require racket/enter rhombus/runtime-config) (enter! (file ~s))"
                          (path->string module-path))
                  "-i")))
  (display (string-join lines "\n\n") in)
  (close-output-port in)
  (define text (port->string out))
  (subprocess-wait proc)
  (close-input-port out)
  text)

;; (module, cases); a case is (interaction, text that must appear in
;; the output for it)
(define sessions
  (list
   (list (build-path here "verify" "pass" "measure_ordered_list.rhm")
         (list (list "insert(1, onil())" "- OList")
               (list "insert(1, ocons(0, onil()))" "- OList")
               (list "ocons(2, ocons(1, onil()))" "the claim `is_onil(t) || ohd(t) >= hd` is violated")
               (list "fun twice({n :: Int | n > 0}) :: {m :: Int | m > n}: n * 2" "")
               (list "twice(0)" "the claim `0 > 0` is violated")
               (list "twice(3)" "6")
               ;; a `let` at the prompt binds its variable for the calls in it
               (list "let k = 3: twice(k)" "6")
               (list "let k = 0: twice(k)" "the claim `k > 0` is violated")
               (list "def k2 = (let y = 2: y * 2)" "")
               ;; refinements below the top level are rejected at the prompt too
               (list "let {k :: Int | k > 0} = 3: k" "a `let` binding cannot carry a refinement")
               (list "fun outer(n :: Int) :: Int:\n  fun g({y :: Int | y > 0}) :: Int: y\n  g(1)"
                     "function `g` is defined inside another definition")
               (list "fun bad({n :: Int | n > 0}) :: {m :: Int | m > n}: n" "the claim `m > n` is violated")
               ;; the reachability built-ins at the prompt
               (list "unreachable()" "call to `unreachable()`: it is reached")
               (list "assert(ohd(insert(1, onil())) == 1)" "")
               (list "assert(2 < 1)" "the claim `2 < 1` is violated")
               ;; a polymorphic function defined at the prompt
               (list "fun idd(x :: ?a) :: ?a: x" "")
               (list "fun keep_ne({l :: OList | !is_onil(l)}) :: {r :: OList | !is_onil(r)}: idd(l)"
                     "is violated when idd(...) = onil()")))
   ;; a polymorphic signature persisted from the module
   (list (build-path here "verify" "pass" "poly_instantiation.rhm")
         (list (list "pos_int(id(4))" "4")
               (list "pos_int(id(0 - 1))" "is violated")
               (list "keep(id(file(3, #true)))" "- File")))))

(for ([s (in-list sessions)])
  (define cases (cadr s))
  (define output (repl (car s) (map car cases)))
  ;; one chunk per prompt; the prompt is the module path, either quoted
  ;; ("/dir/x.rhm"> ) or collection-relative (<pkgs>/.../x.rhm> )
  (define chunks (cdr (regexp-split #px"(?:\"[^\"]*|<[^> \n]*>[^ \n\"]*)[.]rhm\"?> " output)))
  (for ([c cases] [i (in-naturals)])
    ;; the REPL wraps long messages over continuation lines starting `;`
    (define chunk
      (regexp-replace* #px"\\s*\n;\\s*" (if (< i (length chunks)) (list-ref chunks i) "") " "))
    (with-check-info (['interaction (car c)] ['output (string-trim chunk)])
      (check-true (string-contains? chunk (cadr c))
                  (format "output should contain ~s" (cadr c))))))
