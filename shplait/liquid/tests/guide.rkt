#lang racket/base

;; The guide's examples work as the guide says.  The code blocks are
;; read from scribblings/liquid-shplait.scrbl itself, so an edited or
;; added example is tested without changing this file:
;;
;;   - each `@rhombusblock(...)` must compile as a program, without its
;;     lines marked `// rejected`, and each such line, added alone, must
;;     be rejected by the refinement checker;
;;   - the few blocks that are not whole programs are listed below;
;;   - each error message the guide quotes is produced by the program it
;;     describes, and appears in the guide as quoted.

(require racket/file racket/string racket/list racket/runtime-path rackunit)

(define-runtime-path guide-file "../scribblings/liquid-shplait.scrbl")

(define guide (file->string guide-file))

;; Declare the module read from `text` in a fresh namespace.  Returns
;; #f if it compiles, else the error message.
(define (compile-error text)
  (define name (build-path (find-system-path 'temp-dir) "liquid-guide-example.rhm"))
  (with-handlers ([exn:fail? exn-message])
    (define stx (parameterize ([read-accept-reader #t])
                  (read-syntax name (open-input-string text))))
    (parameterize ([current-namespace (make-base-namespace)]
                   [current-module-declare-name (make-resolved-module-path name)])
      (eval stx))
    #f))

(define (program . chunks)
  (string-append "#lang shplait/liquid\n" (string-join chunks "\n") "\n"))

(define (rejected? msg)
  (and msg (string-contains? msg "refinement checking failed") #t))

(define (squash s) (string-normalize-spaces s))

;; ----------------------------------------------------------------------
;; The code blocks

;; The text of each `@rhombusblock( ... )`, its common indentation and
;; any `#,(...)` line (the `#lang` line) removed.
(define (code-blocks text)
  (let loop ([start 0] [acc '()])
    (define m (regexp-match-positions #rx"@rhombusblock[(]" text start))
    (cond
      [(not m) (reverse acc)]
      [else
       (define open (sub1 (cdar m)))
       (define close
         (let scan ([i (add1 open)] [depth 1])
           (case (string-ref text i)
             [(#\() (scan (add1 i) (add1 depth))]
             [(#\)) (if (= depth 1) i (scan (add1 i) (sub1 depth)))]
             [else (scan (add1 i) depth)])))
       (define lines
         (for/list ([l (in-list (string-split (substring text (add1 open) close) "\n" #:trim? #f))]
                    #:unless (regexp-match? #px"^\\s*#," l))
           l))
       (define indent
         (apply min 1000 (for/list ([l (in-list lines)] #:when (regexp-match? #px"\\S" l))
                           (string-length (car (regexp-match #px"^ *" l))))))
       (define body
         (for/list ([l (in-list lines)])
           (if (>= (string-length l) indent) (substring l indent) "")))
       (loop (add1 close) (cons (string-trim (string-join body "\n") "\n" #:repeat? #t) acc))])))

(define blocks (code-blocks guide))

(define (block-starting prefix)
  (or (for/first ([b (in-list blocks)] #:when (string-prefix? b prefix)) b)
      (error 'guide "no code block starts with ~s" prefix)))

;; Definitions the turnstile fragment in "Checks at the Boundary" leaves out.
(define turnstile-prelude #<<EOF
type Turnstile
| locked(credit :: Int)
| unlocked()

measure fun is_locked(t :: Turnstile) :: Boolean:
  match t
  | locked(c): #true
  | unlocked(): #false

type Response
| succeeded(after :: Turnstile)
| refused()
EOF
  )

;; Blocks that are not whole programs, by how they start: #f to skip
;; one, or what to put before it.
(define (context-for b)
  (cond
    [(regexp-match? #px"^\\{[^}]*\\}$" b) 'skip]                      ; notation only
    [(string-prefix? b "fun push(") turnstile-prelude]
    [(string-prefix? b "fun insert(") (block-starting "type OList")]
    [else ""]))

;; Blocks the guide shows being rejected as a whole.
(define (rejected-block? b)
  (and (string-prefix? b "fun id(x :: ?a) :: ?a:") (string-contains? b "pos_int")))

(test-case "the guide has code blocks"
  (check-true (> (length blocks) 15)))

(for ([b (in-list blocks)] [k (in-naturals 1)])
  (define context (context-for b))
  (unless (eq? context 'skip)
    (with-check-info (['block-number k] ['block b])
      (define lines (string-split b "\n" #:trim? #f))
      (define (rejected-line? l) (regexp-match? #px"//\\s*rejected" l))
      (define kept (string-join (filter (lambda (l) (not (rejected-line? l))) lines) "\n"))
      (cond
        [(rejected-block? b)
         (define msg (compile-error (program context kept)))
         (check-true (rejected? msg) (format "rejected, as the guide says; got: ~a" (or msg "no error")))]
        [else
         (define msg (compile-error (program context kept)))
         (check-false msg "compiles")
         (for ([l (in-list lines)] #:when (rejected-line? l))
           (with-check-info (['rejected-line l])
             (define msg (compile-error (program context kept l)))
             (check-true (rejected? msg)
                         (format "added alone, rejected; got: ~a" (or msg "no error")))))]))))

;; ----------------------------------------------------------------------
;; The quoted messages: the text as the guide quotes it (a trailing
;; "..." means the guide shortens it) and the program that produces it.

(define quoted
  (list
   (list "`double`, return: the claim `y > 0` is violated when n = 1"
         (program "fun double({n :: Int | n > 0}) :: {y :: Int | y > 0}:" "  n / 2"))
   (list "`h`, call to `safe_div`, argument 2: the claim `(a + 1) != 0` is violated when a = -1"
         (program "fun safe_div(n :: Int, {d :: Int | d != 0}) :: Int:" "  n / d"
                  "fun h({a :: Int | a > -2}) :: Int:" "  safe_div(10, a + 1)"))
   (list "fun `f`: cannot check the return obligation: call to `string_append`, which is neither a function defined in this module nor one of the builtins the checker models (`max`, `min`, ..."
         (program "fun f(s :: String) :: {n :: Int | n >= 0}:"
                  "  string_length(string_append(s, s))"))
   (list "`midpoint`, assert: the claim `half > 0` is violated when half = 0"
         (program "fun midpoint({lo :: Int | lo >= 0}, {hi :: Int | hi >= lo})"
                  "  :: {m :: Int | m >= lo && m <= hi}:"
                  "  def half = (hi - lo) / 2"
                  "  assert(half > 0)"
                  "  lo + half"))
   (list "`sign`, call to `unreachable()`: it is reached when n = 0"
         (program "fun sign(n :: Int) :: {s :: Int | s == 1 || s == -1}:"
                  "  cond" "  | n > 0: 1" "  | n < 0: -1" "  | ~else: unreachable()"))
   (list "`press`, call to `push`, argument 1: the claim `! is_locked(t)` is violated when t = locked(0)"
         (program turnstile-prelude
                  "fun push({t :: Turnstile | !is_locked(t)}) :: Turnstile:" "  locked(0)"
                  "fun press(t :: Turnstile) :: Response:" "  succeeded(push(t))"))))

(for ([q (in-list quoted)])
  (define text (car q))
  (define shown (squash (if (string-suffix? text "...") (substring text 0 (- (string-length text) 3)) text)))
  (with-check-info (['message text])
    (check-true (string-contains? (squash guide) shown) "the guide quotes it")
    (define msg (compile-error (cadr q)))
    (check-true (and msg (string-contains? (squash msg) shown) #t)
                (format "the program produces it; got: ~a" (or msg "no error")))))
