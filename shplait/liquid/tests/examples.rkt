#lang racket/base

;; The failing code in the examples is rejected.  Each example in
;; examples/ marks a piece of failing code with a `// error: ...` line,
;; followed by the code: one commented-out `// <code>` line or a
;; `/* ... */` block.  For each such piece, this compiles the example
;; with that piece (alone) uncommented and checks that the refinement
;; checker rejects it.  The examples as written must compile.

(require racket/file racket/path racket/string racket/vector racket/runtime-path rackunit)

(define-runtime-path examples-dir "../examples")

;; Commented lines that are an alternative to the line above the
;; `// error:` line rather than an addition: the case comments out that
;; line and uncomments this one, keeping its indentation.
(define alternatives
  '(("div-1.rhm" . "//      | nz(nb): nz(na + nb)")))

;; Declare the module read from `text` as if it were `file`, in a fresh
;; namespace.  Returns #f if it compiles, else the error message.
(define (compile-error file text)
  (with-handlers ([exn:fail? exn-message])
    (define stx (parameterize ([read-accept-reader #t])
                  (read-syntax file (open-input-string text))))
    (parameterize ([current-namespace (make-base-namespace)]
                   [current-module-declare-name (make-resolved-module-path file)])
      (eval stx))
    #f))

(struct example-case (line text) #:transparent)

;; The cases of one example: the line number of its `// error:` line and
;; the program text with that case uncommented.  Lines are blanked
;; rather than removed, so that line numbers stay the file's.
(define (example-cases file lines)
  (define v (list->vector lines))
  (define n (vector-length v))
  (define (text-with edits)
    (define w (vector-copy v))
    (for ([e (in-list edits)]) (vector-set! w (car e) (cdr e)))
    (string-join (vector->list w) "\n"))
  (for/list ([i (in-range n)]
             #:when (string-prefix? (vector-ref v i) "// error:"))
    (define next (and (< (add1 i) n) (vector-ref v (add1 i))))
    (define text
      (cond
        [(not next) (fail (format "line ~a: `// error:` at the end of the file" (add1 i)))]
        [(equal? next "/*")
         (define close
           (for/first ([k (in-range (+ i 2) n)] #:when (equal? (vector-ref v k) "*/")) k))
         (unless close (fail (format "line ~a: unclosed `/*`" (add1 i))))
         (text-with (list (cons (add1 i) "") (cons close "")))]
        [(member (cons (path->string (file-name-from-path file)) next) alternatives)
         (text-with (list (cons (sub1 i) (string-append "//" (vector-ref v (sub1 i))))
                          (cons (add1 i) (substring next 2))))]
        [(string-prefix? next "// ")
         (text-with (list (cons (add1 i) (substring next 3))))]
        [else (fail (format "line ~a: `// error:` not followed by commented-out code" (add1 i)))]))
    (example-case (add1 i) text)))

(for ([file (in-list (sort (directory-list examples-dir #:build? #t) path<?))]
      #:when (regexp-match? #rx"[.]rhm$" (path->string file)))
  (define path (simplify-path (path->complete-path file)))
  (define source (file->string path))
  (with-check-info (['example path])
    (check-false (compile-error path source) "the example as written compiles")
    (for ([c (in-list (example-cases path (string-split source "\n" #:trim? #f)))])
      (with-check-info (['error-line (example-case-line c)])
        (define msg (compile-error path (example-case-text c)))
        (check-true (and msg (string-contains? msg "refinement checking failed") #t)
                    (format "uncommented, rejected by the refinement checker; got: ~a"
                            (or msg "no error")))))))
