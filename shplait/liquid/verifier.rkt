#lang racket

;; Refinement-type verifier for shplait/liquid — the checking core.
;;
;; Entry point: `verify_module`, called at compile time from the
;; finish_frame_hook callback in refinements.rhm.  Input is the
;; STRUCTURED stash captured by the `fun`/`def` wrapper macros — not
;; a re-parse of the source — so discovery of definitions is exact.
;; (One bounded re-parse remains: scanning top-level expression
;; groups for calls to refined functions and for `def x = box(...)`;
;; see `top-level-obligations`.)
;;
;; The checker FAILS CLOSED.  Every obligation either
;;   - is discharged by Z3 (unsat),
;;   - produces a counterexample (reported), or
;;   - cannot be expressed (reported as an error naming the construct).
;; There are no silent skips.  Z3 being missing, timing out, or
;; returning anything but sat/unsat is an error, not a pass.
;;
;; Obligations generated:
;;   RETURN     for each fun with a refined return type, one VC per
;;              if/cond/match branch: preconditions + path condition
;;              entail the return predicate of the branch's body.
;;   CALL-SITE  for each call to a fun with refined parameters, from
;;              fun bodies, def right-hand sides, and top-level
;;              expressions: preconditions + path conditions entail
;;              the callee's parameter predicate on the actual.
;;   SET_BOX    for set_box(b, v) where b is a Boxof-refined
;;              parameter: v satisfies the element predicate.
;;   BOX-ARG    for a `box(e)` (or a top-level `def n = box(e)`)
;;              reaching a Boxof-refined parameter: e satisfies the
;;              element predicate.
;;   DEF        for each refined def: the right-hand side satisfies
;;              the predicate.
;;   REACH      for each call to the built-in `unreachable()`: the
;;              assumptions at the call are contradictory.
;;   ASSERT     for each call to the built-in `assert(P)`: P follows
;;              from the assumptions at the call.
;;
;; PARTIAL CORRECTNESS.  `error(...)` and `unreachable()` never return,
;; so a claim about a result holds vacuously on a path that reaches
;; one; the checker excludes exactly those paths, tracking the
;; condition under which a subterm is evaluated through `if` arms and
;; the right operands of `&&`/`||` (see `note-divergence!`).
;;
;; POLYMORPHISM.  Inside a function a type variable `?a` is an
;; uninterpreted sort (only `==`/`!=` mean anything).  At a call, each
;; type variable that is a parameter's whole type is instantiated from
;; the argument, and a result of type `?a` is a fresh value of the
;; instantiated sort; when no argument determines it, the result's
;; sort is fixed by its use (a FLEXIBLE term, as for `error(...)`).
;;
;; Expression sub-language for predicates and checked bodies:
;;   integer and boolean literals; identifiers (parameters, local
;;   `def` bindings, `match` pattern variables); prefix `-` and `!`;
;;   + - * / and infix `mod` (`/` is shplait's TRUNCATING division and
;;   `mod` is shplait's sign-of-divisor modulo, both encoded
;;   explicitly — SMT-LIB's `div`/`mod` are Euclidean and disagree on
;;   negative operands); comparisons < <= > >= == !=; && and ||;
;;   parens; if/cond/match; calls to module functions (result modeled
;;   as a fresh constant carrying the callee's return refinement, if
;;   any — which is also what makes a recursive specification work,
;;   by assumption at the recursive call); a fixed table of shplait
;;   builtins (`max`, `min`, `add1`, `sub1`, `is_even`, `is_odd`,
;;   `length`, `string_length`, `is_empty`, `is_cons`, `cons`);
;;   `error`, and the shplait/liquid built-ins `unreachable` and
;;   `assert` (lang/builtins.rhm); `unbox` on a Boxof parameter.
;;   Anything else is an unsupported-construct ERROR when it appears
;;   where a translation is required.
;;
;; Every translated expression carries a SORT (`int`, `bool`, `sym`, a
;; datatype, a type variable, a flexible sort fixed by first use, or
;; `opaque` for a value the checker does not model, such as a list or
;; a string).  Sort mismatches are reported here rather than shipped
;; to Z3 as malformed scripts.  An opaque value may be used only as
;; the argument of a measure (`length`, `string_length`, `is_empty`,
;; `is_cons`), which is what makes refinements such as
;; `{xs :: Listof(Int) | length(xs) > 0}` checkable.
;;
;; MUTABLE STATE.  Refinements over the heap are unsound without
;; aliasing control, so the surface is RESTRICTED rather than modeled
;; (see `check-box-usage!` and `classify-box-defs`):
;;   - a `Boxof` parameter may appear only as the target of
;;     `unbox`/`set_box`, or as a whole argument in another `Boxof`
;;     parameter position carrying the SAME element refinement;
;;   - an argument in a `Boxof` parameter position must be a literal
;;     `box(e)` (then `e` is checked against the element predicate),
;;     a `Boxof` parameter with the same element refinement, or a
;;     top-level `def name = box(e)` all of whose uses in the module
;;     agree on one element refinement (then `e` is checked);
;;   - the unbox cache is invalidated by every statement that can
;;     write to a box.
;; Together these make the element refinement a real invariant: it is
;; established wherever a box enters a refined position and
;; re-established by every write.  Without them a box could be
;; viewed through two different refinements and the checker would
;; accept programs that violate their own specification at run time
;; (the box_* cases in tests/verify_fail.rhm).
;;
;; Known limitation: calls are not allowed inside refinement
;; predicates, except the builtins and measures listed above.

(require shrubbery/parse
         racket/treelist)

(provide verify_module verify_interaction)

;; ======================================================================
;; Unsupported-construct signalling
;; ======================================================================

(struct unsupported (why) #:transparent)
(define (unsup why . args) (raise (unsupported (apply format why args))))

;; ======================================================================
;; Rhombus-value normalization
;; ======================================================================

(define (tl->list x)
  (cond [(treelist? x) (treelist->list x)]
        [(list? x) x]
        [else (error 'verify_module "expected a list, got ~e" x)]))

(define (stx-datum x)
  (if (syntax? x) (syntax->datum x) x))

;; A group-context syntax (a body, a predicate, a rhs) normalizes to a
;; list of token-lists, one per group.
(define (stx->groups stx)
  (match (stx-datum stx)
    [(cons 'multi gs)
     (for/list ([g (in-list gs)])
       (match g
         [(cons 'group ts) ts]
         [_ (unsup "unrecognized program shape")]))]
    [(list 'group (cons 'block gs))
     (for/list ([g (in-list gs)])
       (match g [(cons 'group ts) ts] [_ (unsup "unrecognized program shape")]))]
    [(cons 'block gs)
     (for/list ([g (in-list gs)])
       (match g [(cons 'group ts) ts] [_ (unsup "unrecognized program shape")]))]
    [(cons 'group ts) (list ts)]
    [(? symbol? s) (list (list s))]
    [(? number? n) (list (list n))]
    [d (list (list d))]))

(define (id-sym x)
  (define d (stx-datum x))
  (if (symbol? d) d (error 'verify_module "expected identifier, got ~e" d)))

;; ======================================================================
;; Rendering tokens back to surface-ish text (for error messages)
;; ======================================================================

(define (render-toks ts)
  (let loop ([ts ts] [acc '()] [prev '()])
    (cond
      [(null? ts) (apply string-append (reverse acc))]
      [else
       (define t (car ts))
       (define s (render-tok t))
       (define glue?
         (or (null? acc)
             (and (pair? t) (memq (car t) '(parens brackets braces))
                  (pair? prev) (symbol? (car prev)))
             ;; a type variable `?a` is the operator `?` and a name
             (and (symbol? t) (pair? prev) (equal? (car prev) '(op ?)))))
       (loop (cdr ts) (cons (if glue? s (string-append " " s)) acc) (list t))])))

(define (render-tok t)
  (match t
    [(list 'splice ts) (render-toks ts)]
    [(? symbol? s) (symbol->string s)]
    [(? number? n) (number->string n)]
    [(? string? s) (format "~s" s)]
    [(? boolean? b) (if b "#true" "#false")]
    [(list 'op o) (symbol->string o)]
    [(cons 'parens gs) (format "(~a)" (render-groups gs))]
    [(cons 'brackets gs) (format "[~a]" (render-groups gs))]
    [(cons 'braces gs) (format "{~a}" (render-groups gs))]
    [(cons 'block _) ": ..."]
    [(cons 'alts _) "| ..."]
    [_ "..."]))

(define (render-groups gs)
  (string-join (for/list ([g (in-list gs)])
                 (match g [(cons 'group ts) (render-toks ts)] [_ "..."]))
               ", "))

;; ======================================================================
;; Records
;; ======================================================================

;; param: (param name-sym base-toks refinement-or-#f kind)
;;   refinement: (refinement bound-sym pred-toks)
;;   kind: 'plain | 'boxof   ('boxof = Boxof({el :: T | P}) parameter,
;;                            in which case base-toks is the ELEMENT type)
(struct param (name base refinement kind) #:transparent)
(struct refinement (bound pred-toks) #:transparent)
;; fn: (fn name-sym params ret-refinement-or-#f ret-base-toks body-groups)
(struct fn (name params ret ret-base body-groups) #:transparent)
;; refined def: (rdef name-sym refinement base-toks rhs-toks)
(struct rdef (name refinement base rhs-toks) #:transparent)
;; measure: (measure name-sym params scrut-sym ret-sort clauses)
;;   params: (listof (cons param-sym sort)), scrut: the datatype
;;   parameter the body matches on
;;   clauses: (listof (list ctor-sym (listof var-sym) body-toks))
(struct measure (name params scrut ret-sort clauses) #:transparent)

(define (measure-scrut-sort m)
  (cdr (assq (measure-scrut m) (measure-params m))))

(define (parse-measure-record rec)
  (match (tl->list rec)
    [(list name params-tl rt body)
     (define params
       (for/list ([pr (in-list (tl->list params-tl))])
         (match (tl->list pr)
           [(list x pt)
            (define srt (base-sort (base->toks (stx-datum pt))))
            (unless (and (sort-smt srt) (not (tvar-sort? srt)))
              (unsup "a measure's parameter `~a` has type ~a, which the checker does not model"
                     (id-sym x) (base-name (base->toks (stx-datum pt)))))
            (cons (id-sym x) srt)])))
     (define rsort (base-sort (base->toks (stx-datum rt))))
     (unless (and (sort-smt rsort) (not (tvar-sort? rsort)))
       (unsup "a measure must return `Int`, `Boolean`, `Symbol` or a datatype declared in this module"))
     (define groups (stx->groups body))
     (unless (= (length groups) 1)
       (unsup "a measure's body must be a single `match` on a datatype parameter"))
     (match (car groups)
       [(cons 'match scrut-and-alts)
        (define-values (scrut-toks alts-tail) (split-at-alts scrut-and-alts))
        (define pname
          (match scrut-toks
            [(list (? symbol? x)) #:when (and (assq x params) (data-sort? (cdr (assq x params)))) x]
            [_ (unsup "a measure must `match` on one of its parameters, of a datatype declared in this module")]))
        (define clauses
          (match alts-tail
            [(list (cons 'alts cs)) cs]
            [_ (unsup "a measure's `match` needs `|` clauses")]))
        (measure (id-sym name) params pname rsort
                 (for/list ([cl (in-list clauses)])
                   (match cl
                     [`(block (group . ,clause-toks))
                      (define-values (pat-toks body-block) (split-at-trailing-block clause-toks))
                      (define body-toks
                        (match body-block
                          [(list 'block (list 'group ts ...)) ts]
                          [_ (unsup "unrecognized `match` clause shape in a measure")]))
                      (match pat-toks
                        [(list (? symbol? ctor) (cons 'parens gs))
                         (list ctor
                               (for/list ([g (in-list gs)])
                                 (match g
                                   [(list 'group (? symbol? v)) v]
                                   [_ (unsup "a measure's patterns may bind only plain variables")]))
                               body-toks)]
                        [_ (unsup "each clause of a measure must be a constructor pattern `ctor(v, ...)`")])]
                     [_ (unsup "unrecognized `match` clause shape in a measure")])))]
       [_ (unsup "a measure's body must be a single `match` on a datatype parameter")])]))
;; datatype field: (dfield name-sym base-toks refinement-or-#f)
(struct dfield (name base refinement) #:transparent)

(define (base->toks base-datum)
  (match base-datum
    [(list 'multi (cons 'group ts)) ts]
    [(cons 'group ts) ts]
    [(? symbol? s) (list s)]
    [_ '()]))

(define (parse-refinement-field r)
  (define (mk bound pred)
    (refinement (id-sym bound)
                (match (stx->groups pred)
                  [(list ts) ts]
                  [_ (unsup "multi-group refinement predicate")])))
  (cond
    [(or (eq? r #f) (and (syntax? r) (eq? (syntax->datum r) #f))) #f]
    [else
     (match (tl->list r)
       [(list bound pred) (mk bound pred)]
       [(list bound _base pred) (mk bound pred)])]))

;; The refinement field of a return type is #false or [bound, base,
;; pred]; recover the base tokens, falling back to the separately
;; stashed unrefined return type.
(define (ret-base-of ret-field fallback)
  (define from-field
    (and (not (eq? ret-field #f))
         (not (and (syntax? ret-field) (eq? (syntax->datum ret-field) #f)))
         (match (tl->list ret-field)
           [(list _bound base _pred) (base->toks (stx-datum base))]
           [_ #f])))
  (or from-field (base->toks (stx-datum fallback))))

(define (parse-fun-record rec)
  (match (tl->list rec)
    [(list name params-tl ret ret-base body)
     (fn (id-sym name)
         (for/list ([p (in-list (tl->list params-tl))])
           (match (tl->list p)
             [(list pname base refinement-field kind)
              (param (id-sym pname)
                     (base->toks (stx-datum base))
                     (parse-refinement-field refinement-field)
                     (stx-datum kind))]))
         (parse-refinement-field ret)
         (ret-base-of ret ret-base)
         (stx->groups body))]))

(define (parse-ctor-record rec)
  (match (tl->list rec)
    [(list ctor tname fields-tl)
     (list (id-sym ctor) (id-sym tname)
           (for/list ([f (in-list (tl->list fields-tl))])
             (match (tl->list f)
               [(list fname base refinement-field)
                (dfield (id-sym fname)
                        (base->toks (stx-datum base))
                        (parse-refinement-field refinement-field))])))]))

(define (parse-def-record rec)
  (match (tl->list rec)
    [(list name refinement-field base rhs)
     (rdef (id-sym name)
           (parse-refinement-field refinement-field)
           (base->toks (stx-datum base))
           (match (stx->groups rhs)
             [(list ts) ts]
             [_ (unsup "multi-group def right-hand side")]))]))

;; ======================================================================
;; Base types -> sorts
;; ======================================================================

;; 'int, 'bool, 'sym, (list 'data T) for a datatype of this module,
;; (list 'tvar a) for a type variable `?a`, or 'opaque (a value the
;; checker does not model).
;;
;; A type variable is an uninterpreted SMT sort inside the function
;; that declares it: values of it can only be compared with `==` and
;; `!=`, which is all shplait lets a polymorphic function do with them,
;; so a proof at the uninterpreted sort holds at every instantiation.
;; At a call, the callee's type variables are instantiated from the
;; actual arguments instead (see `parse-call`).
(define (base-sort ts)
  (match ts
    [(list 'Int) 'int]
    [(list 'Boolean) 'bool]
    [(list 'Symbol) 'sym]
    [(list (? symbol? n)) #:when (hash-ref (current-type-table) n #f) (list 'data n)]
    [(list (list 'op '?) (? symbol? a)) (list 'tvar a)]
    [_ 'opaque]))

;; The type variable a base type consists of (`?a` -> 'a), else #f.
(define (type-var-of ts)
  (match ts
    [(list (list 'op '?) (? symbol? a)) a]
    [_ #f]))

(define (data-sort? s) (and (pair? s) (eq? (car s) 'data)))
(define (tvar-sort? s) (and (pair? s) (eq? (car s) 'tvar)))
(define (t-of smt sort [src #f]) (T smt sort (hash) src))

;; The sort of a datatype field.  A field whose type is a type variable
;; belongs to a polymorphic datatype, which is declared to the solver
;; with its fields unmodelled.
(define (field-sort f)
  (define s (base-sort (dfield-base f)))
  (if (tvar-sort? s) 'opaque s))

(define (base-name ts)
  (if (null? ts) "an inferred type" (format "`~a`" (render-toks ts))))

(define (sort-smt s)
  (cond [(eq? s 'int) "Int"]
        [(eq? s 'bool) "Bool"]
        [(eq? s 'sym) "Int"]                     ; symbols: distinct integer codes
        [(data-sort? s) (symbol->string (cadr s))]
        [(tvar-sort? s) (format "%tv_~a" (cadr s))]
        [else #f]))

;; Boxof(T) -> the tokens of T, else #f.
(define (box-element-base ts)
  (match ts
    [(list 'Boxof (list 'parens (cons 'group inner))) inner]
    [_ #f]))

;; ======================================================================
;; Terms: an SMT string plus a sort, plus measures for opaque values
;; ======================================================================

;; smt      : string, or #f for an opaque value with no SMT encoding
;; sort     : 'int | 'bool | 'opaque
;; measures : hash of measure-name -> SMT string
;; src      : symbol naming the value (so measures can be cached), or #f
(struct T (smt sort measures src) #:transparent)

;; In the environment a callee's predicate is read in at a call site,
;; a name whose actual argument the checker cannot translate: using it
;; reports why that argument failed, in the caller's terms.
;; position : the argument's 1-based position, or a field name
;; toks     : the argument as written
(struct untranslated (position toks why) #:transparent)

;; In an environment, a `let`-bound name whose right-hand side the
;; checker cannot translate: using it reports why.
(struct failed-local (why) #:transparent)

;; `let x = rhs: ...`: the environment for the body.  `x` stands for a
;; constant equal to `rhs`, named after `x` for counterexamples.  The
;; constant goes where the rhs's own lines go (the current extras), so
;; it is declared wherever the terms it is equal to are.  An rhs the
;; checker cannot translate is not an error by itself; a use of `x`
;; that matters is, and says why.
;;
;; A `let` may shadow: its scope is its body, and everything the
;; checker reads in a scope comes from the environment passed down to
;; it.  (A local `def` may not, because the function's return claim is
;; read in the scope after its `def`s, where a shadowed parameter would
;; be the wrong one.)  The exception is a `Boxof` parameter, whose uses
;; are policed by name.
(define (bind-let x rhs env)
  (when (hash-ref (current-box-params) x #f)
    (unsup "`let ~a` shadows a `Boxof` parameter; rename it" x))
  (define t (with-handlers ([unsupported? (lambda (e) (failed-local (unsupported-why e)))])
              (expr->term rhs env)))
  (cond
    [(failed-local? t) (hash-set env x t)]
    [(sort-smt (T-sort t))
     (define const (fresh-name (format "~a_local" x)))
     (push-extra! (format "(declare-const ~a ~a)" const (sort-smt (T-sort t))))
     (push-extra! (format "(assert (= ~a ~a))" const (T-smt t)))
     (note-const-sort! const (T-sort t))
     (assume-invariant! t push-extra!)
     (hash-set env x (T const (T-sort t) (T-measures t) (string->symbol const)))]
    ;; unmodelled or flexible: the term itself (measures, identity kept)
    [else (hash-set env x t)]))

;; In an environment, a function defined inside the one being checked.
;; It carries no specification (refinements are checked only on
;; top-level definitions), so a claim cannot depend on a call to it.
(struct local-function () #:transparent)

(define (local-function-message name)
  (format "`~a` is a function defined inside another definition (or a function value); the checker does not follow calls to it, so nothing is known about its result (refinements are checked only on functions defined at the top level of the module)"
          name))

;; A function definition among the tokens: `fun NAME(params) ...: body`
;; or an anonymous `fun (params) ...: body`.
;; -> (list name-or-#f param-groups body-block), or #f
(define (fun-def-parts toks)
  (define (block? x) (and (pair? x) (eq? (car x) 'block)))
  (match toks
    [(list-rest 'fun (? symbol? name) (cons 'parens gs) rest)
     #:when (and (pair? rest) (block? (last rest)))
     (list name gs (last rest))]
    [(list-rest 'fun (cons 'parens gs) rest)
     #:when (and (pair? rest) (block? (last rest)))
     (list #f gs (last rest))]
    [_ #f]))

;; The environment for the body of a function defined inside the one
;; being checked: its parameters are arbitrary values (it may be called
;; with anything, and it cannot carry refinements), while the names it
;; uses from the enclosing scope keep what is known about them — their
;; values do not change, so that knowledge holds whenever it is called.
(define (bind-local-params name param-groups env)
  (define env0 (if name (hash-set env name (local-function)) env))
  (for/fold ([e env0]) ([g (in-list param-groups)])
    (match g
      [(list 'group (? symbol? p)) (hash-set e p (flex-term (fresh-value-maker (format "~a_arg" p))))]
      [(list-rest 'group (? symbol? p) '(op ::) type-toks)
       (define s (base-sort type-toks))
       (hash-set e p
                 (cond
                   [(tvar-sort? s) (flex-term (fresh-value-maker (format "~a_arg" p)))]
                   [(sort-smt s) ((fresh-value-maker (format "~a_arg" p)) s)]
                   [else (T #f 'opaque (hash '%type type-toks)
                            (string->symbol (fresh-name (format "~a_arg" p))))]))]
      [_ e])))

;; `let x = rhs: body` -> (values x rhs-toks body-block), or #f
(define (split-let toks)
  (match toks
    [(list-rest 'let (? symbol? x) '(op =) more)
     #:when (and (pair? more) (let ([l (last more)]) (and (pair? l) (eq? (car l) 'block))))
     (values x (drop-right more 1) (last more))]
    [_ (values #f #f #f)]))

(define (t-int s) (T s 'int (hash) #f))
(define (t-bool s) (T s 'bool (hash) #f))
(define (t-opaque measures src) (T #f 'opaque measures src))

;; An opaque term that remembers its declared type, for messages.  The
;; type is kept among the measures under a key no measure can have.
(define (t-opaque-typed type-toks src)
  (T #f 'opaque (if (null? type-toks) (hash) (hash '%type type-toks)) src))

(define (sort-word s)
  (cond
    [(eq? s 'int) "an integer"]
    [(eq? s 'bool) "a boolean"]
    [(eq? s 'sym) "a symbol"]
    [(data-sort? s) (format "a value of type `~a`" (cadr s))]
    [(tvar-sort? s) (format "a value of the type variable `?~a`" (cadr s))]
    [(flexible? s) "a value of a type not yet known"]
    [else "a value of a type the checker does not model (such as a list or a string)"]))

;; Like `sort-word`, naming the declared type of an unmodelled value
;; when the term knows it.
(define (term-word t)
  (cond
    [(and (eq? (T-sort t) 'opaque) (hash-ref (T-measures t) '%type #f))
     => (lambda (ts) (format "a value of type ~a, which the checker does not model" (base-name ts)))]
    [else (sort-word (T-sort t))]))

(define (need-sort t0 want who)
  (define t (at-sort t0 want))
  (unless (equal? (T-sort t) want)
    (unsup "~a needs ~a but got ~a" who (sort-word want) (term-word t)))
  (T-smt t))

;; ----------------------------------------------------------------------
;; Terms of a sort not known when they are made
;;
;; `error(...)` and `unreachable()` have whatever type their context
;; needs, and so does the result of a call whose return type is a type
;; variable the arguments leave unbound (`fun impossible(...) :: ?a`).
;; Such a term is FLEXIBLE: its sort is fixed by its first use, when
;; `make` builds the term at that sort; every later use sees the same
;; term, so a flexible value bound to a name keeps one identity.
(struct flexible ([term #:mutable] make))

(define (flex-term make) (T #f (flexible #f make) (hash) #f))
(define (flex? t) (flexible? (T-sort t)))

;; `t` at sort `want`: a flexible term is resolved to `want` on first
;; use; any other term is returned as it is.
(define (at-sort t want)
  (cond
    [(not (flex? t)) t]
    [else
     (define fl (T-sort t))
     (or (flexible-term fl)
         (let ([r ((flexible-make fl) want)])
           (set-flexible-term! fl r)
           r))]))

;; A maker for a fresh value named after `base`.  Its declaration (and
;; `assume!`'s facts about it) go to the function-level prefix: the
;; term may be used by obligations other than the one that resolved it.
(define ((fresh-value-maker base [assume! void]) want)
  (define const (fresh-name base))
  (cond
    [(sort-smt want)
     (parameterize ([current-extras (current-prefix)])
       (push-prefix! (format "(declare-const ~a ~a)" const (sort-smt want)))
       (note-const-sort! const want)
       (define t (t-of const want (string->symbol const)))
       (assume-invariant! t push-prefix!)
       (assume! t)
       t)]
    [else (T #f 'opaque (hash) (string->symbol const))]))

;; Two terms that must have one sort (the arms of an `if`, the sides of
;; `==`): a flexible one takes the other's sort.
(define (unify-pair a b)
  (cond
    [(and (flex? a) (not (flex? b))) (values (at-sort a (T-sort b)) b)]
    [(and (flex? b) (not (flex? a))) (values a (at-sort b (T-sort a)))]
    [else (values a b)]))

;; ----------------------------------------------------------------------
;; Reachability: `error(...)` and `unreachable()` never return
;;
;; Partial correctness: a claim about a result holds vacuously on any
;; path where evaluation raises an error.  While an expression is
;; translated, `current-reach-guard` is the condition under which the
;; subterm being translated is evaluated, relative to the obligation
;; being built: the arm of an `if` is reached only under its test, the
;; right operand of `&&` only when the left one is true, that of `||`
;; only when it is false.  A never-returning call records that guard;
;; the obligation then excludes it, i.e. assumes the call is not
;; reached.  Where the guard goes depends on the context:
;;   - with `current-divergence` set (the branches of a body), into
;;     that box, to be excluded from the branch's path condition;
;;   - otherwise, as an assumption on the current extras, which is the
;;     obligation being built, or — while statements are walked — the
;;     function-level prefix, so the code after a statement assumes the
;;     statement returned.
(define current-reach-guard (make-parameter "true"))
(define current-divergence (make-parameter #f))

(define (note-divergence!)
  (define g (current-reach-guard))
  (define b (current-divergence))
  (if b
      (set-box! b (cons g (unbox b)))
      (push-extra! (format "(assert ~a)" (negate g)))))

(define (with-guard g thunk)
  (parameterize ([current-reach-guard (conj (current-reach-guard) g)])
    (thunk)))

;; Run `thunk` collecting divergence; -> (values result condition),
;; where condition is what must hold for the evaluation to return.
(define (with-divergence thunk)
  (define b (box '()))
  (define r (parameterize ([current-divergence b]
                           [current-reach-guard "true"])
              (thunk)))
  (values r (for/fold ([p "true"]) ([g (in-list (unbox b))]) (conj p (negate g)))))

;; Divergence that must not leak into the prefix: a best-effort scan
;; (call discovery) translates guards it may then drop, so whatever
;; they record is discarded.
(define (discarding-divergence thunk)
  (parameterize ([current-divergence (box '())])
    (thunk)))

(define (int-of t who) (need-sort t 'int who))
(define (bool-of t who) (need-sort t 'bool who))

;; ======================================================================
;; Operators
;; ======================================================================

;; name -> (prec arg-sort result-sort smt-op)
(define op-info
  (hash
   '*    (list 60 'int 'int "*")
   '/    (list 60 'int 'int "tdiv")
   'mod  (list 60 'int 'int "tmod")
   '+    (list 50 'int 'int "+")
   '-    (list 50 'int 'int "-")
   '<    (list 40 'int 'bool "<")
   '<=   (list 40 'int 'bool "<=")
   '>    (list 40 'int 'bool ">")
   '>=   (list 40 'int 'bool ">=")
   '==   (list 40 'any 'bool "=")
   '!=   (list 40 'any 'bool "distinct")
   '&&   (list 30 'bool 'bool "and")
   (string->symbol "||") (list 20 'bool 'bool "or")))

(define (op-prec op) (cond [(hash-ref op-info op #f) => first] [else #f]))

(define (apply-op op a0 b0)
  (match-define (list _prec arg-sort _res-sort smt) (hash-ref op-info op))
  (define-values (a b)
    (if (eq? arg-sort 'any)
        (let-values ([(a b) (unify-pair a0 b0)])
          ;; both flexible (two never-returning calls compared): any sort
          (values (at-sort a 'int) (at-sort b 'int)))
        (values a0 b0)))
  (cond
    [(eq? arg-sort 'any)
     (unless (equal? (T-sort a) (T-sort b))
       (unsup "`~a` compares ~a with ~a" op (term-word a) (term-word b)))
     (when (eq? (T-sort a) 'opaque)
       (unsup "`~a` is not checked on this type; compare integers or booleans, or use `is_empty`/`length` for lists"
              op))
     (t-bool (format "(~a ~a ~a)" smt (T-smt a) (T-smt b)))]
    [else
     (define who (format "operator `~a`" op))
     (define x (need-sort a arg-sort who))
     (define y (need-sort b arg-sort who))
     (define s (format "(~a ~a ~a)" smt x y))
     (if (eq? (third (hash-ref op-info op)) 'int) (t-int s) (t-bool s))]))

;; Truncating division and sign-of-divisor modulo, matching shplait.
;; SMT-LIB `div`/`mod` are Euclidean; shplait's `/` truncates toward
;; zero and its `mod` follows Racket's `modulo` (sign of the divisor).
(define preamble
  (string-join
   (list
    "(declare-sort Opaque 0)"
    "(define-fun tdiv ((a Int) (b Int)) Int (ite (>= a 0) (div a b) (- (div (- a) b))))"
    "(define-fun tmod ((a Int) (b Int)) Int (ite (or (> b 0) (= (mod a b) 0)) (mod a b) (+ (mod a b) b)))")
   "\n"))

;; ======================================================================
;; Per-translation context
;; ======================================================================

(define current-sig-table (make-parameter (hash)))     ; name -> fn
(define current-ctor-table (make-parameter (hash)))   ; ctor -> (listof dfield)
(define current-ctor-type (make-parameter (hash)))    ; ctor -> type-sym
(define current-type-table (make-parameter (hash)))   ; type-sym -> (listof (cons ctor fields))
(define current-measure-table (make-parameter (hash))) ; name -> measure
(define current-decls (make-parameter ""))            ; SMT datatype + measure declarations
(define current-in-measure (make-parameter #f))       ; translating a measure body
(define current-symbol-codes (make-parameter #f))      ; symbol -> integer code (module-wide)
(define current-const-sorts (make-parameter #f))       ; smt constant name -> sort (module-wide)
(define (note-const-sort! name sort)
  (define h (current-const-sorts))
  (when h (hash-set! h (if (symbol? name) (symbol->string name) name) sort)))
(define (symbol-of-code n)
  (define h (current-symbol-codes))
  (or (and h (for/first ([(sym code) (in-hash h)] #:when (equal? code n)) (format "#'~a" sym)))
      (format "#'symbol~a" n)))
(define (symbol-code sym)
  (define h (current-symbol-codes))
  (unless h (unsup "symbol literal `#'~a` outside a module" sym))
  (hash-ref! h sym (lambda () (hash-count h))))
(define current-box-params (make-parameter (hash)))    ; name -> param
(define current-extras (make-parameter #f))            ; box of per-obligation lines
(define current-prefix (make-parameter #f))            ; box of function-level lines
(define current-unbox-cache (make-parameter #f))       ; box-name -> T
(define current-measure-cache (make-parameter #f))     ; (src . measure) -> smt
(define current-failed-locals (make-parameter (hash))) ; name -> why
(define current-allow-calls (make-parameter #t))       ; #f inside predicates
(define current-top-def-names (make-parameter (set)))  ; names of the module's top-level `def`s
;; The module's top-level `def`s as functions see them: name ->
;; top-const (a term and the SMT lines declaring it), or a string
;; saying why the checker cannot use that def.  See compute-top-consts.
(struct top-const (term lines) #:transparent)
(define current-top-consts (make-parameter (hash)))
(define current-param-env (make-parameter (hash)))     ; params visible to predicates

(define fresh-counter 0)
(define (fresh-name prefix)
  (set! fresh-counter (+ fresh-counter 1))
  (format "~a_~a" prefix fresh-counter))

(define (push-into! b line)
  (when (and b (not (member line (unbox b))))
    (set-box! b (append (unbox b) (list line)))))

(define (push-extra! line) (push-into! (current-extras) line))
(define (push-prefix! line) (push-into! (current-prefix) line))

(define (extra-lines) (let ([b (current-extras)]) (if b (unbox b) '())))

;; ======================================================================
;; Builtins
;; ======================================================================

(define builtin-arity
  (hash 'max 2 'min 2 'add1 1 'sub1 1 'is_even 1 'is_odd 1
        'length 1 'string_length 1 'is_empty 1 'is_cons 1 'cons 2))

(define builtin-names-text
  "`max`, `min`, `add1`, `sub1`, `is_even`, `is_odd`, `length`, `string_length`, `is_empty`, `is_cons`, `cons`, `error`, `unreachable`, `assert`")

(define (builtin? name) (hash-ref builtin-arity name #f))

;; Exactly-encodable integer/boolean builtins.
(define (builtin-exact name args)
  (define (i k who) (int-of (list-ref args k) who))
  (case name
    [(max) (let ([a (i 0 "`max`")] [b (i 1 "`max`")])
             (t-int (format "(ite (>= ~a ~a) ~a ~a)" a b a b)))]
    [(min) (let ([a (i 0 "`min`")] [b (i 1 "`min`")])
             (t-int (format "(ite (<= ~a ~a) ~a ~a)" a b a b)))]
    [(add1) (t-int (format "(+ ~a 1)" (i 0 "`add1`")))]
    [(sub1) (t-int (format "(- ~a 1)" (i 0 "`sub1`")))]
    [(is_even) (t-bool (format "(= (mod ~a 2) 0)" (i 0 "`is_even`")))]
    [(is_odd) (t-bool (format "(not (= (mod ~a 2) 0))" (i 0 "`is_odd`")))]
    [else #f]))

;; The measure of a value: an explicit measure when the term carries
;; one, otherwise a non-negative constant cached per source name.
(define (measure-of t0 mname)
  ;; a flexible value measured is a list or a string: unmodelled
  (define t (at-sort t0 'opaque))
  (when (current-in-measure)
    (unsup "`~a` cannot be used inside a measure; a measure may only use its constructor's fields, arithmetic, and other measures" mname))
  (cond
    [(hash-ref (T-measures t) mname #f) => values]
    [(T-src t)
     => (lambda (src)
          (define cache (current-measure-cache))
          (define key (cons src mname))
          (or (and cache (hash-ref cache key #f))
              (let ([const (fresh-name (format "~a_of_~a" mname src))])
                (when cache (hash-set! cache key const))
                (push-prefix! (format "(declare-const ~a Int)" const))
                (push-prefix! (format "(assert (>= ~a 0))" const))
                const)))]
    [else
     (unsup "cannot determine `~a` of this expression; apply it to a variable or a literal"
            mname)]))

(define (builtin-call name arg-terms)
  (define arity (hash-ref builtin-arity name))
  (unless (= (length arg-terms) arity)
    (unsup "`~a` takes ~a argument(s), got ~a" name arity (length arg-terms)))
  (or (builtin-exact name arg-terms)
      (case name
        [(length) (t-int (measure-of (first arg-terms) 'length))]
        [(string_length) (t-int (measure-of (first arg-terms) 'string_length))]
        [(is_empty) (t-bool (format "(= ~a 0)" (measure-of (first arg-terms) 'length)))]
        [(is_cons) (t-bool (format "(> ~a 0)" (measure-of (first arg-terms) 'length)))]
        [(cons)
         (define tail (second arg-terms))
         (define tail-len
           (with-handlers ([unsupported? (lambda (e) #f)]) (measure-of tail 'length)))
         (t-opaque (hash 'length (if tail-len (format "(+ 1 ~a)" tail-len) "1")) #f)]
        [else (unsup "`~a` is not one of the builtins the checker models" name)])))

;; ======================================================================
;; Expression translation
;; ======================================================================

(define (expr->term toks env)
  (define-values (result rest) (parse-expr toks 0 env))
  (unless (null? rest)
    (unsup "cannot analyze expression near `~a`" (render-toks rest)))
  result)

(define (parse-expr toks min-prec env)
  (define-values (lhs rest1) (parse-atom toks env))
  (let loop ([lhs lhs] [rest rest1])
    (define op
      (match rest
        [(cons (list 'op o) _) o]
        [(cons 'mod _) 'mod]                      ; shplait's infix `mod`
        [_ #f]))
    (cond
      [(not op) (values lhs rest)]
      [else
       (define prec (op-prec op))
       (cond
         [(not prec) (unsup "operator `~a` is not supported in checked code" op)]
         [(>= prec min-prec)
          ;; The right operand of `&&` is evaluated only when the left
          ;; is true, that of `||` only when it is false; a call that
          ;; never returns there is reached only then.
          (define (rhs-guard)
            (define l (and (memq op (list '&& (string->symbol "||")))
                           (let ([l* (at-sort lhs 'bool)])
                             (and (eq? (T-sort l*) 'bool) (T-smt l*)))))
            (cond [(not l) "true"]
                  [(eq? op '&&) l]
                  [else (negate l)]))
          (define-values (rhs rest2)
            (with-guard (rhs-guard)
                        (lambda () (parse-expr (cdr rest) (add1 prec) env))))
          (loop (apply-op op lhs rhs) rest2)]
         [else (values lhs rest)])])))

(define (parens-groups form)
  (match form
    [(cons 'parens gs)
     (for/list ([g (in-list gs)])
       (match g [(cons 'group ts) ts] [_ (unsup "unrecognized argument shape")]))]
    [_ #f]))

(define (parse-atom toks env)
  (match toks
    [(cons head rest)
     (define next-parens (and (pair? rest) (pair? (car rest))
                              (eq? (caar rest) 'parens)
                              (car rest)))
     (cond
       ;; ---- literals
       [(number? head)
        (unless (exact-integer? head)
          (unsup "`~a` is not an integer; shplait has no fractional numbers, so refinements are over integers (model money as cents)"
                 head))
        (values (t-int (if (negative? head)
                           (format "(- ~a)" (- head))
                           (number->string head)))
                rest)]
       [(string? head)
        (values (t-opaque (hash 'string_length (number->string (string-length head))) #f)
                rest)]
       [(memq head '(#t #true true)) (values (t-bool "true") rest)]
       ;; ---- symbol literal #'name
       [(and (equal? head (list 'op '|#'|)) (pair? rest) (symbol? (car rest)))
        (values (t-of (number->string (symbol-code (car rest))) 'sym) (cdr rest))]
       [(memq head '(#f #false false)) (values (t-bool "false") rest)]
       ;; ---- list literal
       [(and (pair? head) (eq? (car head) 'brackets))
        (values (t-opaque (hash 'length (number->string (length (cdr head)))) #f) rest)]
       ;; ---- prefix operators
       [(equal? head '(op -))
        (define-values (v r) (parse-expr rest 55 env))
        (values (t-int (format "(- ~a)" (int-of v "prefix `-`"))) r)]
       [(equal? head '(op !))
        (define-values (v r) (parse-expr rest 35 env))
        (values (t-bool (format "(not ~a)" (bool-of v "prefix `!`"))) r)]
       ;; ---- unbox(b)
       [(and (eq? head 'unbox) next-parens)
        (match (parens-groups next-parens)
          [(list (list (? symbol? box-name)))
           (values (unbox-term box-name) (cdr rest))]
          [_ (unsup "`unbox` is checked only on a `Boxof` parameter named directly")])]
       ;; ---- box(e) / set_box are not expressions the checker uses
       [(and (eq? head 'box) next-parens)
        (unsup "a `box(...)` expression is checked only as an argument in a `Boxof` parameter position")]
       [(and (eq? head 'set_box) next-parens)
        (unsup "`set_box` is a statement; the checker cannot use its result as a value")]
       ;; ---- `if c | a | b` as an expression: an ite term.  This is
       ;; what lets a predicate say `y == (if a > b | a | b)`.
       [(eq? head 'if)
        (define-values (cond-toks alts-tail) (split-at-alts rest))
        (match alts-tail
          [(cons (list 'alts
                       (list 'block (list 'group then-toks ...))
                       (list 'block (list 'group else-toks ...)))
                 after)
           (define c (bool-of (expr->term cond-toks env) "an `if` condition"))
           (define-values (a b)
             (unify-pair (with-guard c (lambda () (expr->term then-toks env)))
                         (with-guard (negate c) (lambda () (expr->term else-toks env)))))
           (define (ite-at a b)
             (define sort (T-sort a))
             (unless (and (sort-smt sort) (equal? sort (T-sort b)))
               (unsup "the two arms of this `if` must have the same modelled type (integer, boolean, or a datatype) for the checker to model it"))
             (T (format "(ite ~a ~a ~a)" c (T-smt a) (T-smt b)) sort (hash) #f))
           (values (if (and (flex? a) (flex? b))
                       ;; neither arm returns, or both are of a type only
                       ;; the context determines
                       (flex-term (lambda (want) (ite-at (at-sort a want) (at-sort b want))))
                       (ite-at a b))
                   after)]
          [_ (unsup "`if` without exactly two `|` alternatives")])]
       ;; ---- `let x = rhs: body` as an expression; its block ends the
       ;; token list
       [(and (eq? head 'let) (let-values ([(x r b) (split-let toks)]) x))
        (define-values (x rhs blk) (split-let toks))
        (values (expr->term (block-result-toks blk) (bind-let x rhs env)) '())]
       ;; ---- an anonymous function as a value
       [(and (eq? head 'fun) next-parens)
        (unsup "a function value (an anonymous `fun`) is not something the checker models, so a claim cannot depend on one")]
       ;; ---- calls
       [(and (symbol? head) next-parens)
        (parse-call head (parens-groups next-parens) (cdr rest) env)]
       ;; ---- identifiers
       [(symbol? head)
        (cond
          [(hash-ref env head #f)
           => (lambda (v)
                (when (local-function? v)
                  (unsup "~a" (local-function-message head)))
                (when (failed-local? v)
                  (unsup "`let`-bound `~a` cannot be checked: ~a" head (failed-local-why v)))
                (when (untranslated? v)
                  (unsup "this refinement depends on ~a (`~a`), which the checker cannot analyze: ~a"
                         (let ([pos (untranslated-position v)])
                           (if (symbol? pos) (format "field `~a`" pos) (format "argument ~a" pos)))
                         (render-toks (untranslated-toks v))
                         (untranslated-why v)))
                (values v rest))]
          [(hash-ref (current-box-params) head #f)
           (unsup "`Boxof` parameter `~a` may be used only in `unbox(~a)`, `set_box(~a, ...)`, or as a whole argument to a `Boxof` parameter with the same element refinement"
                  head head head)]
          [(hash-ref (current-failed-locals) head #f)
           => (lambda (why)
                (unsup "local definition `~a` cannot be checked: ~a" head why))]
          [(hash-ref (current-top-consts) head #f)
           => (lambda (c)
                (cond
                  [(not (top-const? c))
                   (unsup "top-level `~a` cannot be checked: ~a" head c)]
                  [(not (current-prefix))
                   (unsup "top-level `~a` cannot be used here" head)]
                  [else
                   (for-each push-prefix! (top-const-lines c))
                   (values (top-const-term c) rest)]))]
          [(set-member? (current-top-def-names) head)
           (unsup "top-level `~a` cannot be checked: it is not a `def` the checker can analyze" head)]
          [else
           (unsup "identifier `~a` is not a parameter, a local `def`, or a pattern variable of this function"
                  head)])]
       ;; ---- grouping and rejects
       [(and (pair? head) (eq? (car head) 'parens))
        (match head
          [(list 'parens (list 'group inner ...))
           (values (expr->term inner env) rest)]
          [_ (unsup "unrecognized parenthesized form")])]
       [(and (pair? head) (eq? (car head) 'block))
        (unsup "block forms are not supported in checked code")]
       [(and (pair? head) (eq? (car head) 'alts))
        (unsup "misplaced `|` alternatives in checked code")]
       [(pair? head)
        (unsup "`~a` forms are not supported in checked code" (car head))]
       [else (unsup "cannot analyze `~a`" head)])]
    [_ (unsup "expected an expression")]))

(define (unbox-term box-name)
  (define p (hash-ref (current-box-params) box-name #f))
  (unless p
    (unsup "`unbox` target `~a` is not a `Boxof` parameter of this function" box-name))
  (define cache (current-unbox-cache))
  (cond
    [(and cache (hash-ref cache box-name #f)) => values]
    [else
     (define elem-sort (base-sort (param-base p)))
     (unless (sort-smt elem-sort)
       (unsup "`unbox(~a)` has type ~a, which the checker does not model"
              box-name (base-name (param-base p))))
     (define const (fresh-name (format "~a_content" box-name)))
     (push-prefix! (format "(declare-const ~a ~a)" const (sort-smt elem-sort)))
     (define t (t-of const elem-sort (string->symbol const)))
     (when (and (param-refinement p) (not (trivially-true? (param-refinement p))))
       (match-define (refinement bound pred) (param-refinement p))
       (push-prefix! (format "(assert ~a)"
                             (bool-of (parameterize ([current-allow-calls #f])
                                        (expr->term pred (hash-set (current-param-env) bound t)))
                                      "a Boxof element refinement"))))
     (when cache (hash-set! cache box-name t))
     t]))

(define predicate-callables '(max min add1 sub1 is_even is_odd length string_length is_empty is_cons))

;; A constructor application.  When every field's argument has an SMT
;; term the value is the constructor term itself; otherwise it is a
;; fresh constant known to be built by this constructor, with the
;; fields that do translate fixed through their selectors.
(define (ctor-term ctor fields arg-groups env)
  (unless (= (length arg-groups) (length fields))
    (unsup "`~a` takes ~a field(s), got ~a" ctor (length fields) (length arg-groups)))
  (define tname (hash-ref (current-ctor-type) ctor))
  (define sort (list 'data tname))
  (define args
    (for/list ([g (in-list arg-groups)] [f (in-list fields)])
      (define t (with-handlers ([unsupported? (lambda (e) #f)])
                  (at-sort (expr->term g env) (field-sort f))))
      (and t (T-smt t) (equal? (T-sort t) (field-sort f)) (T-smt t))))
  (cond
    [(andmap values args)
     (t-of (if (null? args)
               (symbol->string ctor)
               (format "(~a ~a)" ctor (string-join args " ")))
           sort)]
    [else
     (when (current-in-measure)
       (unsup "in a measure, every field of `~a(...)` must be an expression the checker models" ctor))
     (define const (fresh-name (format "~a_value" ctor)))
     (push-extra! (format "(declare-const ~a ~a)" const tname))
     (push-extra! (format "(assert ((_ is ~a) ~a))" ctor const))
     (for ([a (in-list args)] [f (in-list fields)] #:when a)
       (push-extra! (format "(assert (= (~a_~a ~a) ~a))" ctor (dfield-name f) const a)))
     (t-of const sort (string->symbol const))]))

;; The term for an actual argument, or, when the checker cannot
;; translate it, an `untranslated` record of why.
(define (actual-or-untranslated a position env)
  (with-handlers ([unsupported?
                   (lambda (e) (untranslated position a (unsupported-why e)))])
    (expr->term a env)))

;; The other fields of a constructor, bound to the actual arguments, so
;; a field predicate can mention them.
(define (sibling-env fields actuals j env)
  (for/fold ([e (hash)]) ([a (in-list actuals)] [f (in-list fields)] [k (in-naturals 1)]
                          #:unless (= k j))
    (hash-set e (dfield-name f) (actual-or-untranslated a (dfield-name f) env))))

(define (parse-call head arg-groups rest env)
  ;; A name bound locally (a parameter, a `let`, a function defined
  ;; inside this one) is not the top-level function it may share its
  ;; name with: lexically it is the local binding, a function value the
  ;; checker does not follow.
  (when (hash-ref env head #f)
    (unsup "~a" (local-function-message head)))
  (define callee (hash-ref (current-sig-table) head #f))
  (define msr (hash-ref (current-measure-table) head #f))
  ;; Inside a predicate only the modelled builtins and this module's
  ;; measures may be called; a module function of the same name as a
  ;; builtin shadows it, so it is refused too rather than silently
  ;; read as the builtin.
  (unless (current-allow-calls)
    (unless (or msr
                (hash-ref (current-ctor-table) head #f)
                (and (memq head predicate-callables) (not callee)))
      (unsup "a refinement predicate may not call `~a`: the only calls allowed in a predicate are the builtins `max`, `min`, `add1`, `sub1`, `is_even`, `is_odd`, the measures `length`, `string_length`, `is_empty`, `is_cons`, and this module's `measure fun`s"
             head)))
  (cond
    [msr
     (unless (= (length arg-groups) (length (measure-params msr)))
       (unsup "measure `~a` takes ~a argument(s), got ~a" head (length (measure-params msr)) (length arg-groups)))
     (define args
       (for/list ([g (in-list arg-groups)] [pr (in-list (measure-params msr))])
         (define arg (at-sort (expr->term g env) (cdr pr)))
         (unless (equal? (T-sort arg) (cdr pr))
           (unsup "measure `~a`'s parameter `~a` is ~a but was given ~a"
                  head (car pr) (sort-word (cdr pr)) (term-word arg)))
         (T-smt arg)))
     (values (t-of (format "(~a ~a)" head (string-join args " ")) (measure-ret-sort msr)) rest)]
    [callee
     (unless (= (length arg-groups) (length (fn-params callee)))
       (unsup "call to `~a` with ~a argument(s); its definition has ~a"
              head (length arg-groups) (length (fn-params callee))))
     ;; Translate the arguments the checker is responsible for (box
     ;; positions are handled by check-box-usage!).  The resulting
     ;; environment is what a dependent return refinement — one that
     ;; mentions the callee's own parameters — is interpreted in.
     (define callee-env
       (for/fold ([e (hash)]) ([ts (in-list arg-groups)]
                               [cp (in-list (fn-params callee))])
         (if (param-box-class cp)
             e
             (hash-set e (param-name cp) (expr->term ts env)))))
     ;; Instantiate the callee's type variables: a parameter whose
     ;; whole type is `?a` binds `a` to the sort of its argument.  (The
     ;; callee's own `?a`, an uninterpreted sort, means nothing here.)
     (define inst
       (for/fold ([h (hash)]) ([cp (in-list (fn-params callee))])
         (define a (type-var-of (param-base cp)))
         (define actual (and a (hash-ref callee-env (param-name cp) #f)))
         (if (and actual (not (flex? actual)) (not (hash-has-key? h a)))
             (hash-set h a (T-sort actual))
             h)))
     (define ret-type (fn-ret-base callee))
     (define ret-tv (type-var-of ret-type))
     ;; The callee's return refinement, assumed of the result.  Over a
     ;; result the checker does not model it is best-effort: a predicate
     ;; that only a measure could state is dropped, which assumes less.
     (define (assume-ret! t)
       (when (and (fn-ret callee) (not (trivially-true? (fn-ret callee))))
         (match-define (refinement bound pred) (fn-ret callee))
         (define (assume!)
           (push-extra! (format "(assert ~a)"
                                (bool-of (parameterize ([current-allow-calls #f])
                                           (expr->term pred (hash-set callee-env bound t)))
                                         "a return refinement"))))
         (if (sort-smt (T-sort t))
             (assume!)
             (with-handlers ([unsupported? void]) (assume!)))))
     (define t
       (cond
         ;; The arguments leave the result's type variable unbound, so
         ;; the result has whatever type its use needs.
         [(and ret-tv (not (hash-ref inst ret-tv #f)))
          (flex-term (fresh-value-maker (format "~a_result" head) assume-ret!))]
         [else
          (define ret-sort (if ret-tv (hash-ref inst ret-tv) (base-sort ret-type)))
          (define const (fresh-name (format "~a_result" head)))
          (cond
            [(sort-smt ret-sort)
             (push-extra! (format "(declare-const ~a ~a)" const (sort-smt ret-sort)))
             (note-const-sort! const ret-sort)
             (define rt (t-of const ret-sort (string->symbol const)))
             (assume-invariant! rt push-extra!)
             (assume-ret! rt)
             rt]
            ;; Result type is not modelled: an opaque value, usable only
            ;; through a measure (which its return refinement may fix).
            [else
             (push-extra! (format "(declare-const ~a Opaque)" const))
             (define rt (T const 'opaque
                           (if (or ret-tv (null? ret-type)) (hash) (hash '%type ret-type))
                           (string->symbol const)))
             (assume-ret! rt)
             rt])]))
     (values t rest)]
    ;; `cons` needs only its tail's length, so its head is not
    ;; translated: an element the checker does not model (a `Char` from
    ;; `string_get`) does not stop the list from being checked.  Calls
    ;; inside the head are still found and checked by the call scan.
    [(and (eq? head 'cons) (= (length arg-groups) 2))
     (values (builtin-call head (list #f (expr->term (second arg-groups) env))) rest)]
    [(builtin? head)
     (define arg-terms (for/list ([ts (in-list arg-groups)]) (expr->term ts env)))
     (values (builtin-call head arg-terms) rest)]
    [(hash-ref (current-ctor-table) head #f)
     ;; A datatype value: an algebraic-datatype term.  Its field
     ;; obligations are generated by the call scan, not here.
     => (lambda (fields) (values (ctor-term head fields arg-groups env) rest))]
    ;; `error(...)` and the built-in `unreachable()` never return: the
    ;; path that reaches them is excluded (partial correctness), and
    ;; their result has whatever type its context needs.  `error`'s
    ;; arguments are not analyzed; calls inside them are still found and
    ;; checked by the call scan.  (`unreachable`'s own obligation is
    ;; made by the call scan too.)
    [(memq head '(error unreachable))
     (note-divergence!)
     (values (flex-term (fresh-value-maker "never!")) rest)]
    ;; The built-in `assert(P)` returns nothing; its obligation is made by
    ;; the call scan.
    [(eq? head 'assert)
     (values (t-opaque-typed '(Void) #f) rest)]
    [else
     (unsup "call to `~a`, which is neither a function defined in this module nor one of the builtins the checker models (~a)"
            head builtin-names-text)]))

;; ======================================================================
;; Bodies: branches with path conditions
;; ======================================================================

;; -> (listof (list path-cond-smt-or-"true" term))
;;
;; A path condition includes the conditions under which the branch's
;; evaluation RETURNS: a call to `error` or `unreachable` in a test, a
;; scrutinee or the result excludes the paths that reach it (partial
;; correctness).  A branch that never returns has the path "false";
;; the return obligation skips it.
(define (body->branches toks env)
  (match toks
    [(cons 'if rest)
     (define-values (cond-toks alts-tail) (split-at-alts rest))
     (match alts-tail
       [(list (list 'alts then-blk else-blk))
        (define then-toks (block-result-toks then-blk))
        (define else-toks (block-result-toks else-blk))
        (define-values (cond-smt returns)
          (with-divergence
           (lambda () (bool-of (expr->term cond-toks env) "an `if` condition"))))
        (append
         (for/list ([b (in-list (body->branches then-toks env))])
           (list (conj returns (conj cond-smt (first b))) (second b)))
         (for/list ([b (in-list (body->branches else-toks env))])
           (list (conj returns (conj (negate cond-smt) (first b))) (second b))))]
       [_ (unsup "`if` without exactly two `|` alternatives")])]
    [(list 'cond (list 'alts clauses ...))
     (cond-clauses->branches clauses env)]
    [(cons 'match scrut-and-alts)
     (match-branches scrut-and-alts env)]
    ;; `let x = rhs: body`: the body's branches, with `x` bound; a
    ;; never-returning call in `rhs` excludes them all
    [(list-rest 'let (? symbol?) '(op =) _)
     #:when (let-values ([(x r b) (split-let toks)]) x)
     (define-values (x rhs blk) (split-let toks))
     (define-values (env* returns) (with-divergence (lambda () (bind-let x rhs env))))
     (for/list ([b (in-list (body->branches (block-result-toks blk) env*))])
       (list (conj returns (first b)) (second b)))]
    [(cons (? symbol? kw) _)
     #:when (memq kw '(letrec let_cc begin block try time trace))
     (unsup "`~a` is not supported inside a checked function body; use a local `def` or a `let` for a binding, or move the code into its own `fun`"
            kw)]
    [_
     (define-values (t returns) (with-divergence (lambda () (expr->term toks env))))
     (list (list returns t))]))

;; A block's groups, and the group that is its value (the last one).
;; Earlier groups are statements: their calls are scanned for
;; obligations, but they cannot bind names the result uses.
(define (block-groups blk)
  (match blk
    [(cons 'block gs) (for/list ([g (in-list gs)]) (match g [(cons 'group ts) ts] [_ (unsup "unrecognized block shape")]))]
    [_ (unsup "expected a block")]))
(define (block-result-toks blk)
  (define gs (block-groups blk))
  (when (null? gs) (unsup "empty block"))
  (for ([g (in-list (reverse (cdr (reverse gs))))])
    (when (match g [(cons 'def _) #t] [_ #f])
      (unsup "a local `def` inside a `match` clause, an `if` arm or a `let` body is not supported; move it to the top of the function body, use a `let`, or move the code into its own `fun`")))
  (last gs))
(define (block-groups/safe blk)
  (with-handlers ([unsupported? (lambda (e) '())]) (block-groups blk)))

(define (conj a b)
  (cond [(equal? a "true") b]
        [(equal? b "true") a]
        [(or (equal? a "false") (equal? b "false")) "false"]
        [else (format "(and ~a ~a)" a b)]))

(define (negate g)
  (cond [(equal? g "true") "false"]
        [(equal? g "false") "true"]
        [else (format "(not ~a)" g)]))

(define (split-at-alts toks)
  (let loop ([acc '()] [rest toks])
    (cond
      [(null? rest) (values (reverse acc) '())]
      [(and (pair? (car rest)) (eq? (caar rest) 'alts))
       (values (reverse acc) rest)]
      [else (loop (cons (car rest) acc) (cdr rest))])))

(define (cond-clauses->branches clauses env)
  (let loop ([clauses clauses] [neg-prev "true"] [acc '()])
    (cond
      [(null? clauses) (reverse acc)]
      [else
       (match (car clauses)
         [`(block (group #:else ,else-blk))
          (define body-toks (block-result-toks else-blk))
          (loop (cdr clauses) neg-prev
                (append (reverse
                         (for/list ([b (in-list (body->branches body-toks env))])
                           (list (conj neg-prev (first b)) (second b))))
                        acc))]
         [`(block (group . ,clause-toks))
          (define-values (guard-toks body-block) (split-at-trailing-block clause-toks))
          (define body-toks (block-result-toks body-block))
          ;; a guard that never returns cuts off this clause and the
          ;; ones after it
          (define-values (guard-smt returns)
            (with-divergence
             (lambda () (bool-of (expr->term guard-toks env) "a `cond` guard"))))
          (define path (conj neg-prev (conj returns guard-smt)))
          (loop (cdr clauses)
                (conj neg-prev (conj returns (negate guard-smt)))
                (append (reverse
                         (for/list ([b (in-list (body->branches body-toks env))])
                           (list (conj path (first b)) (second b))))
                        acc))]
         [_ (unsup "unrecognized `cond` clause shape")])])))

(define (split-at-trailing-block toks)
  (let loop ([acc '()] [rest toks])
    (cond
      [(null? rest) (unsup "clause without a body block")]
      [(null? (cdr rest))
       (define tail (car rest))
       (unless (and (pair? tail) (eq? (car tail) 'block))
         (unsup "clause without a trailing body block"))
       (values (reverse acc) tail)]
      [else (loop (cons (car rest) acc) (cdr rest))])))

;; ---- match ------------------------------------------------------------
;;
;; Each clause is checked independently with its pattern variables
;; bound to fresh, UNCONSTRAINED constants: the checker does not
;; relate the scrutinee to the pattern, so a datatype field's
;; invariant has to be re-established by a guard.  That is the sound
;; direction (nothing is assumed about a field).

(define (match-branches scrut-and-alts env)
  (define-values (scrut-toks alts-tail) (split-at-alts scrut-and-alts))
  (when (null? scrut-toks)
    (unsup "`match` without a scrutinee"))
  (define clauses
    (match alts-tail
      [(list (cons 'alts cs)) cs]
      [_ (unsup "`match` without `|` clauses")]))
  (define-values (scrut returns)
    (with-handlers ([unsupported? (lambda (e) (values #f "true"))])
      (with-divergence (lambda () (expr->term scrut-toks env)))))
  (append*
   (for/list ([cl (in-list clauses)])
     (match cl
       [`(block (group . ,clause-toks))
        (define-values (pat-toks body-block) (split-at-trailing-block clause-toks))
        (define body-toks (block-result-toks body-block))
        (define-values (env* pc) (bind-pattern pat-toks env scrut))
        (for/list ([b (in-list (body->branches body-toks env*))])
          (list (conj returns (if pc (conj pc (first b)) (first b))) (second b)))]
       [_ (unsup "unrecognized `match` clause shape")]))))

;; Bind a match pattern's variables.  Supported shapes:
;;   CTOR(v, ...)   [] / [v, ...]   ~else   _   v
;; Nested patterns are rejected.
;;
;; When the constructor is one this module declared, each variable is
;; bound at its field's sort and the field's refinement is ASSUMED
;; here — that is the payoff of declaring it.  Without a declared
;; refinement a field is an arbitrary value of its type.
(define (bind-pattern pat-toks env scrut0)
  ;; A scrutinee whose type its context determines (the result of a
  ;; polymorphic call) takes it from the pattern.
  (define scrut
    (cond
      [(not (and scrut0 (flex? scrut0))) scrut0]
      [else
       (match pat-toks
         [(list (? symbol? c) (cons 'parens _))
          #:when (hash-ref (current-ctor-type) c #f)
          (at-sort scrut0 (list 'data (hash-ref (current-ctor-type) c)))]
         [(or (list 'cons (cons 'parens _)) (list (cons 'brackets _)))
          (at-sort scrut0 'opaque)]
         [_ scrut0])]))
  (define (bind-var env name fld field-env sort-hint)
    (cond
      [else
       (when (and (not (regexp-match? #rx"^_" (symbol->string name)))
                  (or (hash-ref env name #f) (hash-ref (current-box-params) name #f)))
         (unsup "`match` pattern variable `~a` shadows an existing binding; rename it"
                name))
       (define const (fresh-name (format "~a_field" name)))
       (define sort (cond [fld (field-sort fld)] [(eq? sort-hint 'opaque) 'opaque] [else 'int]))
       (push-prefix! (format "(declare-const ~a ~a)" const (or (sort-smt sort) "Opaque")))
       (note-const-sort! const sort)
       (define t (T const sort (hash) (string->symbol const)))
       (assume-invariant! t push-prefix!)
       (values (if (regexp-match? #rx"^_" (symbol->string name)) env (hash-set env name t))
               t)]))
  ;; -> (values env (listof term)) ; one term per pattern position.
  ;; Every variable is bound first; then each field's refinement is
  ;; assumed with all the other fields in scope.
  (define (bind-args env gs fields [hints '()])
    (define-values (env* terms)
      (for/fold ([env env] [terms '()] #:result (values env (reverse terms)))
                ([g (in-list gs)] [i (in-naturals)])
        (match g
          [(list 'group (? symbol? v))
           (define fld (and fields (< i (length fields)) (list-ref fields i)))
           (define-values (env* t)
             (bind-var env v fld (hash) (and (< i (length hints)) (list-ref hints i))))
           (values env* (cons t terms))]
          [_ (unsup "`match` patterns may bind only plain variables (no nested patterns)")])))
    (when (and fields (= (length terms) (length fields)))
      (define field-env
        (for/hash ([f (in-list fields)] [t (in-list terms)]) (values (dfield-name f) t)))
      (for ([f (in-list fields)] [t (in-list terms)]
            #:when (and (dfield-refinement f) (not (trivially-true? (dfield-refinement f)))))
        (match-define (refinement bound pred) (dfield-refinement f))
        (push-prefix! (format "(assert ~a)"
                              (bool-of (parameterize ([current-allow-calls #f])
                                         (expr->term pred (hash-set field-env bound t)))
                                       "a datatype field refinement")))))
    (values env* terms))
  (define (scrut-data?) (and scrut (data-sort? (T-sort scrut)) (T-smt scrut)))
  (define (scrut-length)
    (and scrut (eq? (T-sort scrut) 'opaque)
         (with-handlers ([unsupported? (lambda (e) #f)]) (measure-of scrut 'length))))
  (match pat-toks
    [(list '~else) (values env #f)]
    [(list '#:else) (values env #f)]
    [(list (? symbol? v))
     (define-values (env* t) (bind-var env v #f (hash) #f))
     (values env* #f)]
    [(list (? symbol? ctor) (cons 'parens gs))
     (define fields (hash-ref (current-ctor-table) ctor #f))
     (cond
       [fields
        (define-values (env* terms) (bind-args env gs fields))
        (values env*
                (and (scrut-data?)
                     (= (length terms) (length fields))
                     (andmap T-smt terms)
                     (format "(= ~a ~a)" (T-smt scrut)
                             (if (null? terms)
                                 (symbol->string ctor)
                                 (format "(~a ~a)" ctor (string-join (map T-smt terms) " "))))))]
       [(and (eq? ctor 'cons) (= (length gs) 2))
        (define-values (env* terms) (bind-args env gs #f '(int opaque)))
        (define len (scrut-length))
        (values env*
                (and len
                     (let ([tail-len (with-handlers ([unsupported? (lambda (e) #f)])
                                       (measure-of (second terms) 'length))])
                       (and tail-len (format "(= ~a (+ 1 ~a))" len tail-len)))))]
       [else
        (define-values (env* terms) (bind-args env gs #f))
        (values env* #f)])]
    [(list (cons 'brackets gs))
     (define-values (env* terms) (bind-args env gs #f))
     (define len (scrut-length))
     (values env* (and len (format "(= ~a ~a)" len (length gs))))]
    [_ (unsup "unsupported `match` pattern `~a`" (render-toks pat-toks))]))

;; ======================================================================
;; Call discovery: a TOTAL deep scan (never errors), used to find
;; call sites and set_box sites in any tree.  Path conditions are
;; collected best-effort; an untranslatable guard contributes no path
;; condition, which makes the eventual obligation STRONGER (checked
;; unconditionally) — the conservative, sound direction.
;; ======================================================================

;; -> (listof (list callee-sym actual-token-lists path-conds env))
;; The environment travels with each call, so an argument that mentions
;; a `match` pattern variable can be translated at the call's own scope.
;; The guards and scrutinees translated here only sharpen path
;; conditions; whatever a never-returning call among them would record
;; is discarded, since the scan cannot place it on the right path
;; (dropping it only makes the obligations stronger).
(define (find-calls stx env)
  (discarding-divergence (lambda () (find-calls-rec stx '() env))))

(define (try-guard-smt toks env)
  (with-handlers ([unsupported? (lambda (e) #f)])
    (define t (at-sort (expr->term toks env) 'bool))
    (and (eq? (T-sort t) 'bool) (T-smt t))))

(define (find-calls-rec stx path-conds env)
  (cond
    [(not (pair? stx)) '()]
    [else
     (match stx
       ;; a function defined here (named or anonymous): the calls in its
       ;; body are checked in this scope, with its parameters arbitrary;
       ;; its header is not a call
       [(cons 'fun _)
        #:when (fun-def-parts stx)
        (match-define (list name params blk) (fun-def-parts stx))
        (define env* (bind-local-params name params env))
        (append-map (lambda (ts) (find-calls-rec ts path-conds env*))
                    (block-groups/safe blk))]
       ;; `let x = rhs: body`: calls in the body see `x` (bound to the
       ;; reason, if it cannot be, so an argument that needs it says why)
       [(list-rest 'let (? symbol?) '(op =) _)
        #:when (let-values ([(x r b) (split-let stx)]) x)
        (define-values (x rhs blk) (split-let stx))
        (define env*
          (with-handlers ([unsupported?
                           (lambda (e) (hash-set env x (failed-local (unsupported-why e))))])
            (bind-let x rhs env)))
        (append (find-calls-rec rhs path-conds env)
                (append-map (lambda (ts) (find-calls-rec ts path-conds env*))
                            (block-groups/safe blk)))]
       [(cons 'if rest)
        (define-values (cond-toks alts-tail) (split-at-alts rest))
        (match alts-tail
          [(list (list 'alts then-blk else-blk))
           (define g (try-guard-smt cond-toks env))
           (define (scan blk pcs)
             (append-map (lambda (ts) (find-calls-rec ts pcs env)) (block-groups/safe blk)))
           (append
            (find-calls-rec cond-toks path-conds env)
            (scan then-blk (if g (cons g path-conds) path-conds))
            (scan else-blk (if g (cons (format "(not ~a)" g) path-conds) path-conds)))]
          [_ (find-calls-children stx path-conds env)])]
       [(list 'cond (list 'alts clauses ...))
        (let loop ([cs clauses] [pcs path-conds] [acc '()])
          (cond
            [(null? cs) acc]
            [else
             (match (car cs)
               [`(block (group #:else ,else-blk))
                (loop (cdr cs) pcs
                      (append acc
                              (append-map (lambda (ts) (find-calls-rec ts pcs env))
                                          (block-groups/safe else-blk))))]
               [`(block (group . ,clause-toks))
                (define parts
                  (with-handlers ([unsupported? (lambda (e) #f)])
                    (call-with-values (lambda () (split-at-trailing-block clause-toks)) list)))
                (cond
                  [(not parts) (loop (cdr cs) pcs (append acc (find-calls-children (car cs) pcs env)))]
                  [else
                   (define g (try-guard-smt (first parts) env))
                   (loop (cdr cs)
                         (if g (cons (format "(not ~a)" g) pcs) pcs)
                         (append acc
                                 (find-calls-rec (first parts) pcs env)
                                 (append-map (lambda (ts)
                                               (find-calls-rec ts (if g (cons g pcs) pcs) env))
                                             (block-groups/safe (second parts)))))])]
               [_ (loop (cdr cs) pcs (append acc (find-calls-children (car cs) pcs env)))])]))]
       [(cons 'match rest)
        (define-values (scrut-toks alts-tail) (split-at-alts rest))
        (match alts-tail
          [(list (cons 'alts clauses))
           (define scrut (with-handlers ([unsupported? (lambda (e) #f)]) (expr->term scrut-toks env)))
           (append
            (find-calls-rec scrut-toks path-conds env)
            (append*
             (for/list ([cl (in-list clauses)])
               (match cl
                 [`(block (group . ,clause-toks))
                  (define parts
                    (with-handlers ([unsupported? (lambda (e) #f)])
                      (call-with-values (lambda () (split-at-trailing-block clause-toks))
                                        list)))
                  (cond
                    [(not parts) '()]
                    [else
                     (define-values (env* pc)
                       (with-handlers ([unsupported? (lambda (e) (values env #f))])
                         (bind-pattern (first parts) env scrut)))
                     (append-map (lambda (ts)
                                   (find-calls-rec ts (if pc (cons pc path-conds) path-conds) env*))
                                 (block-groups/safe (second parts)))])]
                 [_ '()]))))]
          [_ (find-calls-children stx path-conds env)])]
       [(list-rest (? symbol? name)
                   (list 'parens groups ...)
                   rest)
        (define actuals
          (for/list ([g (in-list groups)])
            (match g [`(group . ,ts) ts] [_ '()])))
        (append (list (list name actuals path-conds env))
                (append-map (lambda (a) (find-calls-rec a path-conds env)) actuals)
                (find-calls-rec rest path-conds env))]
       [_ (find-calls-children stx path-conds env)])]))

(define (find-calls-children stx path-conds env)
  (append
   (if (pair? (car stx)) (find-calls-rec (car stx) path-conds env) '())
   (find-calls-rec (cdr stx) path-conds env)))

;; ======================================================================
;; Z3
;; ======================================================================

(define z3-candidates
  '("/opt/homebrew/bin/z3" "/usr/local/bin/z3" "/opt/local/bin/z3" "/usr/bin/z3"))

;; DrRacket started from the Finder or the Dock does not inherit the
;; shell's PATH, so `find-executable-path` fails there even when the
;; command line works; hence the fixed candidates.
(define z3-path
  (delay
    (or (let ([env-z3 (getenv "Z3")])
          (and env-z3 (if (absolute-path? env-z3)
                          env-z3
                          (let ([p (find-executable-path env-z3)])
                            (and p (path->string p))))))
        (let ([p (find-executable-path "z3")])
          (and p (path->string p)))
        (for/first ([c (in-list z3-candidates)] #:when (file-exists? c)) c)
        (let ([home (find-system-path 'home-dir)])
          (for/first ([rel (in-list '(".local/bin/z3" "bin/z3"))]
                      #:when (file-exists? (build-path home rel)))
            (path->string (build-path home rel))))
        (error 'shplait/liquid
               "z3 not found; refinement checking requires z3. Put it on PATH, or set the Z3 environment variable to its location (DrRacket started from the Finder does not see the shell's PATH, so start it from a terminal or set Z3)"))))

(define z3-timeout-seconds 10)
(define small-value-bound 3)

;; Re-run a satisfiable script with |x| <= small-value-bound asserted
;; for every declared Int constant; the model, or #f.
(define (small-model smt label)
  (define ints (regexp-match* #px"\\(declare-const (\\S+) Int\\)" smt #:match-select cadr))
  ;; integer fields of datatype-typed constants, one level down
  (define data-consts
    (regexp-match* #px"\\(declare-const (\\S+) ([A-Za-z_][A-Za-z0-9_]*)\\)" smt #:match-select cdr))
  (define field-terms
    (for*/list ([m (in-list data-consts)]
                #:when (hash-ref (current-type-table) (string->symbol (cadr m)) #f)
                [c (in-list (hash-ref (current-type-table) (string->symbol (cadr m))))]
                [f (in-list (cdr c))]
                #:when (eq? (field-sort f) 'int))
      (cons (format "((_ is ~a) ~a)" (car c) (car m))
            (format "(~a_~a ~a)" (car c) (dfield-name f) (car m)))))
  (cond
    [(and (null? ints) (null? field-terms)) #f]
    [else
     (define bounds
       (string-join (append
                     (for/list ([c (in-list ints)])
                       (format "(assert (<= (- ~a) ~a ~a))" small-value-bound c small-value-bound))
                     (for/list ([ft (in-list field-terms)])
                       (format "(assert (=> ~a (<= (- ~a) ~a ~a)))" (car ft) small-value-bound (cdr ft) small-value-bound)))
                    "\n"))
     (define smt2 (regexp-replace #rx"[(]check-sat[)]" smt (string-append bounds "\n(check-sat)")))
     (with-handlers ([(lambda (e) #t) (lambda (e) #f)])
       (define-values (verdict model) (run-z3/once smt2 label))
       (and (eq? verdict 'sat) model))]))

;; Raised when the current security guard forbids running z3 at all
;; (DrRacket's background expansion).  verify_module then skips the
;; check: the program is checked when it is actually run.
(struct no-subprocess ())

;; -> (values 'unsat "") | (values 'sat model-text) ; anything else raises
;; The script goes to z3 on its standard input: nothing is written to
;; disk, which matters under a security guard that forbids writes.
(define (run-z3 smt label)
  (define-values (verdict model) (run-z3/once smt label))
  (if (eq? verdict 'sat)
      (values 'sat (or (small-model smt label) model))
      (values verdict model)))

;; Identifiers may contain any character shplait allows (emoji, say),
;; but an SMT-LIB simple symbol is ASCII; one that is not is sent as a
;; quoted symbol, |...|.  Racket's reader reads |...| back as the bare
;; symbol, so models need no translation.
(define (smt-quote-non-ascii smt)
  (regexp-replace* #px"[^\\s()|\"]*[\u0080-\U10FFFF][^\\s()|\"]*" smt "|&|"))

(define (run-z3/once smt label)
  (define-values (proc out in err)
    (with-handlers ([exn:fail?
                     (lambda (e)
                       (if (regexp-match? #rx"forbidden|access denied|not allowed" (exn-message e))
                           (raise (no-subprocess))
                           (raise e)))])
      (subprocess #f #f #f (force z3-path) (format "-T:~a" z3-timeout-seconds) "-in")))
  (define out-str
    (dynamic-wind
     void
     (lambda ()
       (display (smt-quote-non-ascii smt) in)
       (close-output-port in)
       (define stdout (port->string out))
       (define stderr (port->string err))
       (subprocess-wait proc)
       (string-append stdout stderr))
     (lambda ()
       (close-input-port out)
       (close-input-port err))))
  (define trimmed (string-trim out-str))
  (cond
    [(regexp-match? #rx"^unsat" trimmed) (values 'unsat "")]
    [(regexp-match? #rx"^sat" trimmed)
     (define nl (regexp-match-positions #rx"\n" trimmed))
     (values 'sat (if nl (substring trimmed (cdar nl)) ""))]
    [(regexp-match? #rx"timeout|unknown" trimmed)
     (unsup "z3 gave up on obligation `~a` after ~a seconds (~a). The claim may still be true: the checker proves a claim by unfolding measures a step at a time and it cannot reason by induction, so a fact about every value of a recursive datatype (that a smaller scope implies a larger one, say) is out of its reach unless a precondition states exactly what the call needs"
            label z3-timeout-seconds (string-trim trimmed))]
    [else
     (unsup "z3 could not decide obligation `~a` (output: ~a)"
            label
            (if (> (string-length trimmed) 200)
                (string-append (substring trimmed 0 200) "...")
                trimmed))]))

;; The text of a claim for a message: the predicate as the user wrote it,
;; with the internal `%v` (a box's element) shown in words.  With
;; `subst`, a hash from the callee's names to the actual argument tokens,
;; the claim is shown in the caller's terms: `i < rows(m)` at a call
;; `set(t, j, i, v)` reads `j < rows(t)`.
(define (render-claim pred-toks [subst #f])
  (with-handlers ([(lambda (e) #t) (lambda (e) #f)])
    (define toks (if subst (subst-toks pred-toks subst) pred-toks))
    (regexp-replace* #rx"%v" (render-toks toks) "the contents")))

(define (subst-toks toks subst)
  (define (one t)
    (cond
      [(and (symbol? t) (hash-ref subst t #f))
       => (lambda (actual)
            ;; an atom or a call needs no parentheses; anything with an
            ;; operator at top level does
            (define compound?
              (for/or ([x (in-list actual)]) (and (pair? x) (eq? (car x) 'op))))
            (cond
              [(= (length actual) 1) (car actual)]
              [compound? (list 'parens (cons 'group actual))]
              [else (list 'splice actual)]))]
      [(and (pair? t) (memq (car t) '(parens brackets braces)))
       (cons (car t) (for/list ([g (in-list (cdr t))])
                       (match g [(cons 'group ts) (cons 'group (map one ts))] [_ g])))]
      [else t]))
  (map one toks))

;; The substitution for a call: each callee parameter (and the bound
;; name of the checked one) to the caller's argument tokens.
(define (call-subst callee actuals bound j)
  (for/fold ([h (hash bound (list-ref actuals (sub1 j)))])
            ([cp (in-list (fn-params callee))] [a (in-list actuals)])
    (hash-set h (param-name cp) a)))

;; The checker names its SMT constants after the source: `h_field_3` is
;; the pattern variable `h`, `to_minutes_result_5` the result of a call to
;; `to_minutes`, `clock_content_1` the contents of the box `clock`,
;; `length_of_l_2` the measure `length(l)`.  Undo that for the reader.
(define (source-name n)
  (define base (regexp-replace #px"_[0-9]+$" n ""))
  (cond
    [(regexp-match #px"^(.*)_(?:field|local|def|arg)$" base) => (lambda (m) (second m))]
    [(regexp-match #px"^(.*)_result$" base) => (lambda (m) (format "~a(...)" (second m)))]
    [(regexp-match #px"^(.*)_content$" base) => (lambda (m) (format "unbox(~a)" (second m)))]
    [(regexp-match #px"^(length|string_length)_of_(.*)$" base)
     => (lambda (m) (format "~a(~a)" (second m) (source-name (third m))))]
    [else base]))

;; Pretty-print a Z3 model: (define-fun n () Int 1) / (- 1) -> "n = 1",
;; in source names, without repeating a binding that says the same thing.
(define (pretty-model model-text [script #f])
  (define relevant
    (and script
         (let ([m (regexp-match-positions (regexp-quote obligation-marker) script)])
           (and m (substring script (cdar m))))))
  (define (mentioned? name)
    (or (not relevant)
        (regexp-match? (pregexp (string-append "(?<![A-Za-z0-9_!])" (regexp-quote name) "(?![A-Za-z0-9_!])"))
                       relevant)))
  (define sexp
    (with-handlers ([exn:fail? (lambda (e) #f)])
      (read (open-input-string model-text))))
  (define (render-value v [sort #f])
    (match v
      [(? number?) (if (eq? sort 'sym) (symbol-of-code v) (number->string v))]
      [(list '- (? number? n)) (format "-~a" n)]
      ['true "#true"]
      ['false "#false"]
      [(? symbol?)
       (cond
         [(hash-ref (current-ctor-table) v #f) (format "~a()" v)]
         ;; a value of a type variable: z3 names the elements of an
         ;; uninterpreted sort `%tv_a!val!0`, `%tv_a!val!1`, ...
         [(regexp-match #px"^%tv_(.+)!val!([0-9]+)$" (symbol->string v))
          => (lambda (m) (format "?~a#~a" (second m) (third m)))]
         [(regexp-match? #rx"!" (symbol->string v)) "_"]   ; a value the checker does not model
         [else (symbol->string v)])]
      [(cons (? symbol? c) args)
       #:when (hash-ref (current-ctor-table) c #f)
       (define fields (hash-ref (current-ctor-table) c))
       (format "~a(~a)" c
               (string-join (for/list ([a (in-list args)] [i (in-naturals)])
                              (render-value a (and (< i (length fields))
                                                   (field-sort (list-ref fields i)))))
                            ", "))]
      [_ (format "~s" v)]))
  (define bindings
    (if (list? sexp)
        (for/list ([d (in-list sexp)]
                   #:when (match d
                            [(list 'define-fun (? symbol? n) '() srt _)
                             (and (not (eq? srt 'Opaque))
                                  (not (regexp-match? #rx"!" (symbol->string n)))
                                  (mentioned? (symbol->string n)))]
                            [_ #f]))
          (match-define (list _ name _ _ val) d)
          (define sort (let ([h (current-const-sorts)]) (and h (hash-ref h (symbol->string name) #f))))
          (format "~a = ~a" (source-name (symbol->string name)) (render-value val sort)))
        '()))
  ;; #f when there is nothing to show: the obligation has no free
  ;; variables, so the claim is false for the call as written.
  (define unique (sort (remove-duplicates bindings) string<?))
  (and (pair? unique) (string-join unique ", ")))

;; "the claim `c` is violated when x = 1, y = 2", or just "the claim
;; `c` is violated" when no value is involved.  The obligation of an
;; `unreachable()` claims that its call is never reached; a
;; counterexample is a way of reaching it.
(define (violated-text claim values)
  (cond
    [(eq? claim 'unreachable)
     (string-append "it is reached" (if values (format " when ~a" values) ""))]
    [else
     (string-append (if claim (format "the claim `~a` is violated" claim) "refinement violated")
                    (if values (format " when ~a" values) ""))]))

;; The obligation that a call to the built-in `unreachable()` is not
;; reached, and that the built-in `assert(P)` holds: `path-conds` and
;; the prefix are the assumptions at the call.  -> obligation, or #f
;; when `name` is not one of these two built-ins (a module function of
;; the same name is an ordinary function).
(define (reachability-obligation owner name actuals path-conds env)
  (cond
    [(hash-ref (current-sig-table) name #f) #f]
    [(hash-ref env name #f) #f]           ; a local binding of that name
    [(and (eq? name 'unreachable) (null? actuals))
     (parameterize ([current-extras (box '())])
       (obligation owner "call to `unreachable()`"
                   (assemble path-conds "(assert true)") 'unreachable))]
    [(and (eq? name 'assert) (= (length actuals) 1))
     (parameterize ([current-extras (box '())])
       (define goal (bool-of (expr->term (first actuals) env) "`assert`"))
       (obligation owner "assert"
                   (assemble path-conds (format "(assert (not ~a))" goal))
                   (render-claim (first actuals))))]
    [else #f]))

;; ======================================================================
;; Obligations
;; ======================================================================

(struct obligation (owner label program claim [anchor #:auto]) #:transparent #:mutable)
(define (with-anchor o stx) (set-obligation-anchor! o stx) o)

;; A predicate that is literally `true` claims nothing.
(define (trivially-true? r)
  (and (refinement? r)
       (match (refinement-pred-toks r)
         [(list (or 'true #t)) #t]
         [_ #f])))

;; An obligation's script is the preamble, the function-level prefix
;; AS OF NOW (declarations, preconditions, unbox constants, local
;; bindings), then the lines this obligation itself needed.  Call
;; `assemble` only after the goal has been built, so that constants
;; created while building it are already in the prefix.
(define (assemble path-conds negated-goal)
  (define body
    (append (let ([b (current-prefix)]) (if b (unbox b) '()))
            ;; While walking the body, extras and prefix are the same
            ;; box (constants created there must outlive the statement);
            ;; only an obligation-local extras box adds lines here.
            (list obligation-marker)
            (if (eq? (current-extras) (current-prefix)) '() (extra-lines))
            (for/list ([p (in-list (reverse path-conds))])
              (format "(assert ~a)" p))
            (list negated-goal "(check-sat)" "(get-model)")))
  ;; the uninterpreted sorts standing for the type variables used
  (define tvar-sorts
    (remove-duplicates
     (append* (for/list ([line (in-list body)])
                (regexp-match* #px"%tv_[A-Za-z0-9_]+" line)))))
  (string-join
   (append (list preamble)
           (for/list ([s (in-list tvar-sorts)]) (format "(declare-sort ~a 0)" s))
           (list (current-decls))
           body)
   "\n"))

;; Everything after this line in a script belongs to one obligation;
;; a counterexample shows only the values that part mentions.
(define obligation-marker "; --- obligation ---")

;; The term standing for a parameter inside its own function.
(define (param-term p)
  (define s (base-sort (param-base p)))
  (if (sort-smt s)
      (t-of (symbol->string (param-name p)) s (param-name p))
      (T (symbol->string (param-name p)) 'opaque (hash) (param-name p))))

;; Eager declaration check: every declared predicate must be
;; translatable, whether or not any obligation ends up using it.
;; -> #t if the predicate translates (or claims nothing), #f if it was
;; reported.  Callers skip the obligations that would only repeat it.
(define (validate-refinement! who r base env add-err!)
  (cond
    [(not (and r (not (trivially-true? r)))) #t]
    [else
     (with-handlers ([unsupported?
                      (lambda (e)
                        (add-err! (format "the refinement on ~a" who)
                                  (unsupported-why e))
                        #f)])
      (define bound-term
        (let ([s (base-sort base)])
          (if (sort-smt s)
              (t-of "declared_value" s 'declared_value)
              (t-opaque (hash) 'declared_value))))
      (parameterize ([current-allow-calls #f]
                     [current-extras (box '())]
                     [current-prefix (box '())]
                     [current-measure-cache (make-hash)]
                     [current-unbox-cache (make-hash)])
        (bool-of (expr->term (refinement-pred-toks r)
                             (hash-set env (refinement-bound r) bound-term))
                 (format "the refinement on ~a" who))
        #t))]))

;; ======================================================================
;; Box usage discipline
;; ======================================================================

;; A box "class" identifies the invariant a box is viewed through:
;; (list 'box #f) for no claim, (list 'box normalized-pred) otherwise.
(define (normalize-pred r)
  (and r
       (not (trivially-true? r))
       (subst-sym (refinement-pred-toks r) (refinement-bound r) '%v)))

(define (subst-sym x from to)
  (cond [(eq? x from) to]
        [(pair? x) (cons (subst-sym (car x) from to) (subst-sym (cdr x) from to))]
        [else x]))

(define (param-box-class p)
  (cond
    [(eq? (param-kind p) 'boxof) (list 'box (normalize-pred (param-refinement p)))]
    [(box-element-base (param-base p)) (list 'box #f)]
    [else #f]))

(define (class-desc cls)
  (match cls
    [(list 'box #f) "a `Boxof` with no element refinement"]
    [(list 'box pred) (format "a `Boxof` whose element satisfies `~a`"
                              (render-toks (subst-sym pred '%v 'v)))]
    [_ "a non-box position"]))

;; A constructor with a refined field may be used only as the head of
;; a direct call.  Used as a value (`map(circle, xs)`) it would build
;; values whose field refinement nothing proved, and the assumption
;; made when a `match` pattern binds that field would be unsound.
(define (check-ctor-escape! stx err)
  (define (refined-ctor? name)
    (define fields (hash-ref (current-ctor-table) name #f))
    (and fields
         (for/or ([f (in-list fields)])
           (and (dfield-refinement f) (not (trivially-true? (dfield-refinement f)))))))
  (let walk ([x stx])
    (cond
      [(not (pair? x)) (void)]
      [else
       (match x
         [(list-rest (? symbol? name) (cons 'parens groups) rest)
          (for ([g (in-list groups)]) (walk g))
          (walk rest)]
         [(cons (? symbol? name) rest)
          #:when (refined-ctor? name)
          (err "constructor `~a` has a refined field, so it may be used only as a direct call `~a(...)`; passing it as a value would build values nothing checked"
               name name)
          (walk rest)]
         [_ (when (pair? (car x)) (walk (car x)))
            (walk (cdr x))])])))

;; The single identifier an argument consists of, if it is one.
(define (box-arg-name toks)
  (match toks [(list (? symbol? s)) s] [_ #f]))

;; The `box(e)` an argument consists of, if it is one.
(define (box-arg-literal toks)
  (match toks
    [(list 'box (list 'parens (cons 'group inner))) inner]
    [_ #f]))

;; Module-level box defs: name -> (cons init-toks class-or-#f).
(define current-box-defs (make-parameter (hash)))

;; Walk a token tree enforcing the box rules.  `box-param` maps a
;; symbol to a param or #f; `on-box-arg` is called for each argument
;; landing in a box position; `err` reports a disallowed occurrence.
(define (walk-box-tree stx box-param on-box-arg err)
  (define (allowed-target? a) (and (box-arg-name a) (box-param (box-arg-name a))))
  ;; the `Boxof` parameters a token tree mentions
  (define (box-names-in x)
    (cond
      [(and (symbol? x) (box-param x)) (list x)]
      [(pair? x) (remove-duplicates (append (box-names-in (car x)) (box-names-in (cdr x))))]
      [else '()]))
  (define (walk x)
    (cond
      [(not (pair? x)) (void)]
      [else
       (match x
         ;; A function defined inside this one may be called after the
         ;; enclosing function has read a box, when the box may have
         ;; changed; the checker tracks a box's contents only within
         ;; the function that receives it, so such a function may not
         ;; use the box at all.
         [(cons 'fun _)
          #:when (fun-def-parts x)
          (for ([b (in-list (box-names-in x))])
            (err "a function defined inside another may not use that function's `Boxof` parameter `~a` (the checker tracks a box only in the function that receives it); pass the box to a top-level function instead"
                 b))]
         [(list-rest (? symbol? name) (cons 'parens groups) rest)
          (define actuals
            (for/list ([g (in-list groups)])
              (match g [`(group . ,ts) ts] [_ '()])))
          (cond
            [(memq name '(unbox set_box))
             (for ([a (in-list actuals)] [j (in-naturals 1)])
               (unless (and (= j 1) (allowed-target? a)) (walk a)))]
            [else
             (define callee (hash-ref (current-sig-table) name #f))
             (for ([a (in-list actuals)] [j (in-naturals 1)])
               (define cp (and callee
                               (<= j (length (fn-params callee)))
                               (list-ref (fn-params callee) (sub1 j))))
               (define cls (and cp (param-box-class cp)))
               (cond
                 [cls (on-box-arg name j a cls)]
                 [else (walk a)]))])
          (walk rest)]
         [(cons (? symbol? name) rest)
          #:when (box-param name)
          (err "`Boxof` parameter `~a` may be used only in `unbox(~a)`, `set_box(~a, ...)`, or as a whole argument to a `Boxof` parameter with the same element refinement"
               name name name)
          (walk rest)]
         [_ (when (pair? (car x)) (walk (car x)))
            (walk (cdr x))])]))
  (walk stx))

;; Check one argument that lands in a Boxof parameter position.
(define (check-box-argument owner callee-name j actual cls add-err! add-obl!)
  (define name (box-arg-name actual))
  (define lit (box-arg-literal actual))
  (define p (and name (hash-ref (current-box-params) name #f)))
  (define def-entry (and name (hash-ref (current-box-defs) name #f)))
  (define (reject why)
    (add-err! (format "argument ~a of the call to `~a`" j callee-name)
              (format "~a, but that position needs ~a; pass `box(<expression>)` directly, forward a `Boxof` parameter declared with the same element refinement, or use a top-level `def name = box(...)` that is only ever used at this refinement"
                      why (class-desc cls))))
  (define (check-contents! init what)
    (match cls
      [(list 'box #f) (void)]
      [(list 'box pred)
       (with-handlers ([unsupported?
                        (lambda (e)
                          (add-err! (format "argument ~a of the call to `~a`" j callee-name)
                                    (unsupported-why e)))])
         (define t (expr->term init (hash)))
         (define goal (bool-of (parameterize ([current-allow-calls #f])
                                 (expr->term pred (hash '%v t)))
                               "a Boxof element refinement"))
         (add-obl! (obligation owner
                               (format "call to `~a`, argument ~a (~a)" callee-name j what)
                               (assemble '() (format "(assert (not ~a))" goal)) (render-claim pred))))]))
  (cond
    [p
     (define actual-cls (param-box-class p))
     (unless (equal? actual-cls cls)
       (reject (format "`~a` is ~a" name (class-desc actual-cls))))]
    [lit (check-contents! lit "box contents")]
    [def-entry
     (cond
       [(equal? (cdr def-entry) cls) (void)]
       [else
        (reject (format "the top-level box `~a` is used elsewhere as ~a"
                        name (class-desc (cdr def-entry))))])]
    [else
     (reject (if name
                 (format "`~a` is neither a `Boxof` parameter of this function nor a top-level `def ~a = box(...)`"
                         name name)
                 "the argument is not a `box(...)` expression"))]))

;; ======================================================================
;; Per-function checking
;; ======================================================================

;; Does this statement hand a box to a module function, which could
;; write to it?  (`set_box` itself updates the cache where it is
;; checked, so it does not need to be caught here.)
(define (passes-box-to-call? stx box-names)
  (let loop ([x stx])
    (cond
      [(not (pair? x)) #f]
      [else
       (match x
         [(list-rest (? symbol? name) (cons 'parens groups) rest)
          (or (and (hash-ref (current-sig-table) name #f)
                   (for/or ([g (in-list groups)])
                     (match g
                       [(list 'group (? symbol? v)) (and (memq v box-names) #t)]
                       [_ #f])))
              (for/or ([g (in-list groups)]) (loop g))
              (loop rest))]
         [_ (or (loop (car x)) (loop (cdr x)))])])))

;; Statement classification for a multi-statement body.
;; -> (values 'def name rhs-toks) | (values 'expr #f toks)
(define (classify-statement toks)
  (match toks
    [(list-rest 'def (? symbol? name) rest)
     (define eq-pos
       (for/first ([t (in-list rest)] [i (in-naturals)] #:when (equal? t '(op =))) i))
     (unless eq-pos
       (unsup "local `def ~a` without a `=` right-hand side" name))
     (values 'def name (list-tail rest (add1 eq-pos)))]
    [(cons (? symbol? kw) _)
     #:when (memq kw '(letrec let_cc begin block try time trace macro module type import))
     (unsup "`~a` is not supported inside a checked function body; use a local `def` or a `let` for a binding, or move the code into its own `fun`"
            kw)]
    [_ (values 'expr #f toks)]))

(define (fn-obligations f)
  (define obls '())
  (define errs '())
  (define (add-obl! o) (set! obls (cons o obls)))
  (define (add-err! label why)
    (set! errs (cons (list (fn-name f)
                           (format "fun `~a`: cannot check ~a: ~a"
                                   (fn-name f) label why))
                     errs)))
  (define prefix (box '()))
  (define failed-locals (make-hash))
  ;; The environment in which this function's own refinements are read:
  ;; every parameter the checker models, under its own name.
  (define base-env
    (for/fold ([env (hash)]) ([p (in-list (fn-params f))])
      (if (param-box-class p) env (hash-set env (param-name p) (param-term p)))))
  (parameterize ([current-box-params
                  (for/hash ([p (in-list (fn-params f))]
                             #:when (param-box-class p))
                    (values (param-name p) p))]
                 [current-unbox-cache (make-hash)]
                 [current-measure-cache (make-hash)]
                 [current-prefix prefix]
                 [current-extras prefix]
                 [current-failed-locals failed-locals]
                 [current-param-env base-env])
    (define box-names (hash-keys (current-box-params)))

    ;; ---- declarations for the parameters the checker models
    (for ([p (in-list (fn-params f))] #:unless (param-box-class p))
      (define t (param-term p))
      (push-prefix! (format "(declare-const ~a ~a)"
                            (param-name p) (or (sort-smt (T-sort t)) "Opaque")))
      (note-const-sort! (param-name p) (T-sort t))
      (assume-invariant! t push-prefix!))

    ;; ---- eager validation of declared refinements: a predicate that
    ;; cannot be translated is an error even if no obligation uses it.
    ;; An obligation that would only repeat the same message is skipped.
    (define bad-params
      (for/set ([p (in-list (fn-params f))]
                #:unless (validate-refinement! (format "parameter `~a`" (param-name p))
                                               (param-refinement p) (param-base p)
                                               base-env add-err!))
        (param-name p)))
    (define ret-ok?
      (validate-refinement! "the return type" (fn-ret f) (fn-ret-base f)
                            base-env add-err!))

    ;; ---- preconditions, once per function
    (with-handlers ([unsupported?
                     (lambda (e) (add-err! "this function's preconditions"
                                           (unsupported-why e)))])
      (parameterize ([current-allow-calls #f])
        (for ([p (in-list (fn-params f))]
              #:when (and (not (param-box-class p))
                          (not (set-member? bad-params (param-name p)))
                          (param-refinement p)
                          (not (trivially-true? (param-refinement p)))))
          (match-define (refinement bound pred) (param-refinement p))
          (push-prefix!
           (format "(assert ~a)"
                   (bool-of (expr->term pred (hash-set base-env bound
                                                       (hash-ref base-env (param-name p))))
                            "a parameter refinement"))))))

    ;; ---- constructor and box usage discipline (total scans)
    (check-ctor-escape! (cons 'body (fn-body-groups f))
                        (lambda (fmt . args)
                          (add-err! "the use of a constructor" (apply format fmt args))))
    (walk-box-tree (cons 'body (fn-body-groups f))
                   (lambda (n) (hash-ref (current-box-params) n #f))
                   (lambda (callee-name j actual cls)
                     (parameterize ([current-extras (box '())])
                       (check-box-argument (fn-name f) callee-name j actual cls
                                           add-err! add-obl!)))
                   (lambda (fmt . args)
                     (add-err! "the use of a `Boxof` value" (apply format fmt args))))

    ;; ---- walk the body statement by statement
    (define groups (fn-body-groups f))
    (define stmts (if (null? groups) '() (reverse (cdr (reverse groups)))))
    (define result (if (null? groups) '() (last groups)))
    (define env
      (for/fold ([env base-env]) ([st (in-list stmts)])
        (with-handlers ([unsupported?
                         (lambda (e)
                           (add-err! "a statement of the body" (unsupported-why e))
                           env)])
          (define-values (kind name rhs) (classify-statement st))
          (emit-call-obligations! f st env add-obl! add-err! prefix)
          (define env*
            (cond
              [(eq? kind 'def)
               (when (or (hash-ref env name #f)
                         (hash-ref (current-box-params) name #f))
                 (unsup "local `def ~a` shadows a parameter or an earlier local definition; rename it"
                        name))
               (define t
                 (with-handlers ([unsupported?
                                  (lambda (e)
                                    (hash-set! failed-locals name (unsupported-why e))
                                    #f)])
                   (expr->term rhs env)))
               (cond
                 [(not t) env]
                 [(sort-smt (T-sort t))
                  (define const (fresh-name (format "~a_local" name)))
                  (push-prefix! (format "(declare-const ~a ~a)" const (sort-smt (T-sort t))))
                  (push-prefix! (format "(assert (= ~a ~a))" const (T-smt t)))
                  (note-const-sort! const (T-sort t))
                  (assume-invariant! t push-prefix!)
                  (hash-set env name
                            (T const (T-sort t) (T-measures t) (string->symbol const)))]
                 [else (hash-set env name t)])]
              ;; a function defined here: its name is a local function
              ;; for the rest of the body (its calls are not checked
              ;; against any top-level function of the same name)
              [(match (fun-def-parts st) [(list (? symbol? n) _ _) n] [_ #f])
               => (lambda (n) (hash-set env n (local-function)))]
              [else
               (statement-assumption! st env)
               env]))
          (when (passes-box-to-call? st box-names)
            (hash-clear! (current-unbox-cache)))
          env*)))

    ;; ---- obligations from the result expression
    (emit-call-obligations! f result env add-obl! add-err! prefix)

    ;; ---- RETURN obligation.  Skipped when a parameter predicate could
    ;; not be translated: proving the result without that assumption
    ;; would report a violation that is only the missing precondition.
    (when (and ret-ok? (set-empty? bad-params) (fn-ret f) (not (trivially-true? (fn-ret f))))
      (match-define (refinement ret-bound ret-pred) (fn-ret f))
      (with-handlers ([unsupported?
                       (lambda (e) (add-err! "the return obligation" (unsupported-why e)))])
        (define branches (body->branches result env))
        (for ([b (in-list branches)]
              [i (in-naturals 1)]
              ;; a branch that never returns claims nothing
              #:unless (equal? (first b) "false"))
          (parameterize ([current-extras (box '())])
            (define goal
              (bool-of (parameterize ([current-allow-calls #f])
                         (expr->term ret-pred (hash-set env ret-bound (second b))))
                       "the return refinement"))
            (define label
              (if (= (length branches) 1) "return" (format "return [branch ~a]" i)))
            (add-obl!
             (obligation (fn-name f) label
                         (assemble (if (equal? (first b) "true") '() (list (first b)))
                                   (format "(assert (not ~a))" goal)) (render-claim ret-pred))))))))
  (values (reverse obls) (reverse errs)))

;; What a statement that is not a `def` tells the rest of the body.  The
;; rest runs only if the statement returned: after `error(...)` or
;; `unreachable()` it does not run at all, and after `assert(P)` (whose
;; obligation is checked where the call is found) `P` holds.  Other
;; statements tell it nothing.
(define (statement-assumption! st env)
  (define (builtin-named? name) (not (hash-ref (current-sig-table) name #f)))
  (match st
    [(list (? symbol? head) (cons 'parens _))
     #:when (and (memq head '(error unreachable)) (builtin-named? head))
     (push-prefix! "(assert false)")]
    [(list 'assert (list 'parens (cons 'group p-toks)))
     #:when (builtin-named? 'assert)
     (with-handlers ([unsupported? void])     ; reported by the assert's own obligation
       (parameterize ([current-extras (current-prefix)])
         (push-prefix! (format "(assert ~a)" (bool-of (expr->term p-toks env) "`assert`")))))]
    [_ (void)]))

;; Call-site and set_box obligations discovered in one statement.
(define (emit-call-obligations! f toks outer-env add-obl! add-err! prefix)
  (for ([c (in-list (find-calls toks outer-env))])
    (match-define (list callee-name actuals path-conds env) c)
    (cond
      ;; a call through a local binding (a function defined inside this
      ;; one, a function-valued parameter or `let`) is not a call to the
      ;; top-level function of that name, and has nothing to check
      [(hash-ref env callee-name #f) (void)]
      ;; the built-ins `unreachable()` and `assert(P)`
      [(with-handlers ([unsupported?
                        (lambda (e)
                          (add-err! (format "the `~a`" callee-name) (unsupported-why e))
                          #t)])
         (reachability-obligation (fn-name f) callee-name actuals path-conds env))
       => (lambda (o) (when (obligation? o) (add-obl! o)))]
      [(eq? callee-name 'set_box)
       (match actuals
         [(list (list (? symbol? box-name)) value-toks)
          (define p (hash-ref (current-box-params) box-name #f))
          (cond
            [(and (not p) (hash-ref (current-box-defs) box-name #f))
             => (lambda (entry)
                  (match (cdr entry)
                    [(list 'box (? list?))
                     (add-err! (format "the `set_box` on `~a`" box-name)
                               "a top-level box viewed through an element refinement cannot be written inside a function; pass it as a `Boxof` parameter instead")]
                    [_ (void)]))]
            [(not p)
             (add-err! (format "the `set_box` on `~a`" box-name)
                       "the target of `set_box` must be a `Boxof` parameter of this function")]
            [(and (param-refinement p) (not (trivially-true? (param-refinement p))))
             (match-define (refinement bound pred) (param-refinement p))
             (with-handlers ([unsupported?
                              (lambda (e)
                                (add-err! (format "the `set_box` obligation on `~a`" box-name)
                                          (unsupported-why e)))])
               ;; the value's constants stay function-level (the cache
               ;; below reuses them), but a never-returning call in it
               ;; excuses only this obligation
               (define-values (value-t returns)
                 (with-divergence (lambda () (expr->term value-toks env))))
               ;; the element predicate speaks about the parameters, as at
               ;; `unbox`, not about whatever a `let` binds at the call
               (define goal
                 (bool-of (parameterize ([current-allow-calls #f])
                            (expr->term pred (hash-set (current-param-env) bound value-t)))
                          "a Boxof element refinement"))
               (add-obl!
                (obligation (fn-name f)
                            (format "set_box on `~a`" box-name)
                            (assemble (cons returns path-conds) (format "(assert (not ~a))" goal))
                            (render-claim pred)))
               ;; After the write this box holds exactly this value, and
               ;; any OTHER box may be an alias of it, so its cached
               ;; contents are no longer known.
               (when (current-unbox-cache)
                 (hash-clear! (current-unbox-cache))
                 (hash-set! (current-unbox-cache) box-name value-t)))]
            [else (void)])]
         [_ (add-err! "a `set_box`"
                      "the target of `set_box` must be a `Boxof` parameter named directly")])]
      ;; constructing a datatype value: each refined field is an obligation
      [(hash-ref (current-ctor-table) callee-name #f)
       => (lambda (fields)
            (when (= (length actuals) (length fields))
              (for ([actual (in-list actuals)]
                    [fld (in-list fields)]
                    [j (in-naturals 1)]
                    #:when (and (dfield-refinement fld)
                                (not (trivially-true? (dfield-refinement fld)))))
                (match-define (refinement bound pred) (dfield-refinement fld))
                (with-handlers ([unsupported?
                                 (lambda (e)
                                   (add-err! (format "field `~a` of `~a`"
                                                     (dfield-name fld) callee-name)
                                             (unsupported-why e)))])
                  (parameterize ([current-extras (box '())])
                    (define actual-t (expr->term actual env))
                    (define siblings (sibling-env fields actuals j env))
                    (define goal
                      (bool-of (parameterize ([current-allow-calls #f])
                                 (expr->term pred (hash-set siblings bound actual-t)))
                               "a datatype field refinement"))
                    (add-obl!
                     (obligation (fn-name f)
                                 (format "~a, field `~a`" callee-name (dfield-name fld))
                                 (assemble path-conds
                                           (format "(assert (not ~a))" goal)) (render-claim pred))))))))]
      [else
       (define callee (hash-ref (current-sig-table) callee-name #f))
       (when callee
         (cond
           [(not (= (length actuals) (length (fn-params callee))))
            (add-err! (format "the call to `~a`" callee-name)
                      "argument count does not match the definition")]
           [else
            (for ([actual (in-list actuals)]
                  [cp (in-list (fn-params callee))]
                  [j (in-naturals 1)]
                  #:when (and (not (param-box-class cp))
                              (param-refinement cp)
                              (not (trivially-true? (param-refinement cp)))))
              (match-define (refinement bound pred) (param-refinement cp))
              (with-handlers ([unsupported?
                               (lambda (e)
                                 (add-err! (format "the call to `~a` (argument ~a)" callee-name j)
                                           (unsupported-why e)))])
                (parameterize ([current-extras (box '())])
                  (define actual-t (expr->term actual env))
                  (define arg-env (callee-arg-env callee actuals env))
                  (define goal
                    (bool-of (parameterize ([current-allow-calls #f])
                               (expr->term pred (hash-set arg-env bound actual-t)))
                             "a parameter refinement"))
                  (add-obl!
                   (obligation (fn-name f)
                               (format "call to `~a`, argument ~a" callee-name j)
                               (assemble path-conds (format "(assert (not ~a))" goal))
                               (render-claim pred (call-subst callee actuals bound j)))))))]))])))

;; A callee's refinement may mention the callee's other parameters
;; (`{r :: Int | r <= c}`).  At a call site those names stand for the
;; corresponding actuals.  An argument that cannot be translated is
;; bound to an `untranslated` record, so a predicate that needs it
;; reports why that argument failed, rather than naming the callee's
;; parameter as if it were in the caller's scope.
(define (callee-arg-env callee actuals env)
  (for/fold ([e (hash)]) ([a (in-list actuals)] [cp (in-list (fn-params callee))]
                          [j (in-naturals 1)])
    (cond
      [(param-box-class cp) e]
      [else (hash-set e (param-name cp) (actual-or-untranslated a j env))])))

;; ======================================================================
;; DEF obligations
;; ======================================================================

(define (def-obligations d)
  (define obls '())
  (define errs '())
  (match-define (rdef name r base rhs-toks) d)
  (define prefix (box '()))
  (parameterize ([current-box-params (hash)]
                 [current-unbox-cache (make-hash)]
                 [current-measure-cache (make-hash)]
                 [current-prefix prefix]
                 [current-extras prefix])
    (define ok?
      (validate-refinement! (format "def `~a`" name) r base (hash)
                            (lambda (label why)
                              (set! errs (cons (list name (format "def `~a`: cannot check ~a: ~a"
                                                                 name label why))
                                               errs)))))
    (when (and ok? r (not (trivially-true? r)))
      (match-define (refinement bound pred) r)
      (with-handlers ([unsupported?
                       (lambda (e)
                         (set! errs (cons (list name
                                                (format "def `~a`: cannot check its refinement: ~a"
                                                        name (unsupported-why e)))
                                          errs)))])
        (define rhs-t (expr->term rhs-toks (hash)))
        (define goal
          (bool-of (parameterize ([current-allow-calls #f])
                     (expr->term pred (hash bound rhs-t)))
                   "the def refinement"))
        (set! obls
              (cons (obligation name "definition refinement"
                                (assemble '() (format "(assert (not ~a))" goal)) (render-claim pred))
                    obls)))))
  (values (reverse obls) (reverse errs)))

;; ======================================================================
;; Top level
;; ======================================================================

(define (source-groups path)
  (cond
    [(not (and path (file-exists? path))) '()]
    [else
     (define src-text (file->string path))
     ;; Blank out the `#lang` line rather than dropping it, so that the
     ;; positions and line numbers of what follows are the file's.
     (define body-text
       (cond
         [(regexp-match #px"^#lang [^\n]*\n" src-text)
          => (lambda (m)
               (define lang-line (car m))
               (string-append (make-string (sub1 (string-length lang-line)) #\space)
                              "\n"
                              (substring src-text (string-length lang-line))))]
         [else src-text]))
     (define stx
       (with-handlers ([exn:fail? (lambda (e) #f)])
         (call-with-input-string body-text
           (lambda (in)
             (port-count-lines! in)
             (parse-all in #:source path)))))
     ;; syntax objects, so that a problem can be anchored at its group
     (if stx (cdr (syntax->list stx)) '())]))

(define (group-datum g) (if (syntax? g) (syntax->datum g) g))

(define (skip-group? g0)
  (define g (group-datum g0))
  (match g
    ;; `check:` bodies are scanned like any other expression: they can
    ;; call refined functions and build datatype values.
    [`(group ,(? symbol? head) . ,_) (memq head '(fun import type module measure))]
    [_ #f]))

;; Find `def NAME = box(e)` at the top level.
(define (collect-box-defs groups)
  (for/fold ([h (hash)]) ([g0 (in-list groups)])
    (define g (group-datum g0))
    (match g
      [`(group def ,(? symbol? name) (op =) box (parens (group . ,init)))
       (hash-set h name init)]
      [`(group def ,(? symbol? name) (op ::) ,_ ... (op =) box (parens (group . ,init)))
       (hash-set h name init)]
      [_ h])))

;; Determine the single element class each top-level box is used at.
;; -> (values name -> (cons init class-or-#f), errors)
(define (classify-box-defs groups box-defs)
  (define seen (make-hash))
  (define errs '())
  (for ([g0 (in-list groups)] #:unless (skip-group? g0))
    (define g (group-datum g0))
    (match g
      [`(group . ,toks)
       (walk-box-tree toks
                      (lambda (n) #f)
                      (lambda (callee-name j actual cls)
                        (define n (box-arg-name actual))
                        (when (and n (hash-ref box-defs n #f))
                          (define prev (hash-ref seen n 'none))
                          (cond
                            [(eq? prev 'none) (hash-set! seen n cls)]
                            [(not (equal? prev cls))
                             (set! errs
                                   (cons (format "box `~a` is passed both to ~a and to ~a; a box may be viewed through only one element refinement"
                                                 n (class-desc prev) (class-desc cls))
                                         errs))]
                            [else (void)])))
                      (lambda (fmt . as) (void)))]
      [_ (void)]))
  (values (for/hash ([(n init) (in-hash box-defs)])
            (values n (cons init (let ([c (hash-ref seen n 'none)])
                                   (if (eq? c 'none) #f c)))))
          (reverse errs)))

;; Top-level obligations: calls to checked functions from top-level
;; expression groups (including def right-hand sides), the box
;; discipline at top level, and the contents check for every
;; top-level `def name = box(e)` used at a refined box position.
;; Top-level `def`s are immutable, so wherever a function's refinement
;; or checked body names one, it may assume what the def says: a
;; refined def its refinement (proved by def-obligations), a plain one
;; its right-hand side.  Computed once per module, in order, each def
;; in terms of the earlier ones; a right-hand side the checker cannot
;; analyze (including any call) makes that def unusable, and a use of
;; it fails closed with the reason.
(define (compute-top-consts groups rdefs)
  (define rdef-table (for/hash ([d (in-list rdefs)]) (values (rdef-name d) d)))
  (for/fold ([table (hash)]) ([g0 (in-list groups)] #:unless (skip-group? g0))
    (match (group-datum g0)
      [`(group def ,(? symbol? name) . ,rest)
       (define eq-pos
         (for/first ([t (in-list rest)] [i (in-naturals)] #:when (equal? t '(op =))) i))
       (define rhs (and eq-pos (list-tail rest (add1 eq-pos))))
       (define d (hash-ref rdef-table name #f))
       (define lines (box '()))
       (hash-set
        table name
        (with-handlers ([unsupported?
                         (lambda (e)
                           (define why (unsupported-why e))
                           (cond
                             [(regexp-match #px"^a refinement predicate may not call `([^`]+)`" why)
                              => (lambda (m)
                                   (format "its right-hand side calls `~a`, and a top-level `def` is modelled only when its right-hand side makes no calls"
                                           (second m)))]
                             [else why]))])
          (parameterize ([current-prefix lines]
                         [current-extras lines]
                         [current-allow-calls #f]
                         [current-top-consts table]
                         [current-box-params (hash)]
                         [current-unbox-cache (make-hash)]
                         [current-measure-cache (make-hash)])
            (cond
              [(and d (rdef-refinement d) (not (trivially-true? (rdef-refinement d))))
               (match-define (refinement bound pred) (rdef-refinement d))
               (define sort (base-sort (rdef-base d)))
               (define const (fresh-name (format "~a_def" name)))
               (define t
                 (cond
                   [(sort-smt sort)
                    (push-prefix! (format "(declare-const ~a ~a)" const (sort-smt sort)))
                    (note-const-sort! const sort)
                    (t-of const sort (string->symbol const))]
                   [else (t-opaque (hash) (string->symbol const))]))
               (push-prefix! (format "(assert ~a)"
                                     (bool-of (expr->term pred (hash bound t)) "a def refinement")))
               (top-const t (unbox lines))]
              [rhs
               (define t (expr->term rhs (hash)))
               (cond
                 [(sort-smt (T-sort t))
                  (define const (fresh-name (format "~a_def" name)))
                  (push-prefix! (format "(declare-const ~a ~a)" const (sort-smt (T-sort t))))
                  (push-prefix! (format "(assert (= ~a ~a))" const (T-smt t)))
                  (note-const-sort! const (T-sort t))
                  (assume-invariant! t push-prefix!)
                  (top-const (T const (T-sort t) (T-measures t) (string->symbol const))
                             (unbox lines))]
                 [else
                  (top-const (T #f (T-sort t) (T-measures t)
                                (or (T-src t) (string->symbol (fresh-name (format "~a_def" name)))))
                             (unbox lines))])]
              [else (unsup "its right-hand side was not found")]))))]
      [_ table])))

(define (top-level-obligations groups anchor-name rdefs)
  (define obls '())
  (define errs '())
  (define prefix (box '()))
  (define (add-err0! label why [anchor #f])
    (set! errs (cons (list anchor-name (format "~a: ~a" label why) anchor) errs)))
  (define (add-obl0! o) (set! obls (cons o obls)))
  (define add-err! add-err0!)
  (define add-obl! add-obl0!)
  (parameterize ([current-box-params (hash)]
                 [current-unbox-cache (make-hash)]
                 [current-measure-cache (make-hash)]
                 [current-prefix prefix]
                 [current-extras prefix])
    ;; contents of each classified box def
    (for ([(name entry) (in-hash (current-box-defs))])
      (match-define (cons init cls) entry)
      (match cls
        [(list 'box (? list? pred))
         (with-handlers ([unsupported?
                          (lambda (e)
                            (add-err! (format "top-level box `~a`" name) (unsupported-why e)))])
           (parameterize ([current-extras (box '())])
             (define t (expr->term init (hash)))
             (define goal (bool-of (parameterize ([current-allow-calls #f])
                                     (expr->term pred (hash '%v t)))
                                   "a Boxof element refinement"))
             (add-obl! (obligation anchor-name
                                   (format "initial contents of box `~a`" name)
                                   (assemble '() (format "(assert (not ~a))" goal)) (render-claim pred)))))]
        [_ (void)]))
    ;; A top-level `def` is in scope for the groups after it: a refined
    ;; one contributes its predicate (already proved by def-obligations),
    ;; a plain one its right-hand side when that translates.  A value
    ;; the checker does not model (a `String`, a list) is bound as an
    ;; opaque term, known through its measures.
    (define rdef-table (for/hash ([d (in-list rdefs)]) (values (rdef-name d) d)))
    (define env (hash))
    (define (bind-refined-def! name d)
      (match-define (refinement bound pred) (rdef-refinement d))
      (define sort (base-sort (rdef-base d)))
      (define const (fresh-name (format "~a_def" name)))
      (define t
        (cond
          [(sort-smt sort)
           (push-prefix! (format "(declare-const ~a ~a)" const (sort-smt sort)))
           (t-of const sort (string->symbol const))]
          [else (t-opaque (hash) (string->symbol const))]))
      ;; translate first, so a predicate that fails leaves nothing behind
      (define assumption
        (with-handlers ([unsupported? (lambda (e) #f)])
          (parameterize ([current-extras (box '())])
            (define goal (bool-of (parameterize ([current-allow-calls #f])
                                    (expr->term pred (hash bound t)))
                                  "a def refinement"))
            (append (extra-lines) (list (format "(assert ~a)" goal))))))
      (when assumption
        (for-each push-prefix! assumption)
        (set! env (hash-set env name t))))
    (define (bind-top-def! name rhs)
      (define d (hash-ref rdef-table name #f))
      (cond
        [(and d (rdef-refinement d) (not (trivially-true? (rdef-refinement d))))
         (bind-refined-def! name d)]
        [else
         (define t (with-handlers ([unsupported? (lambda (e) #f)])
                     (expr->term rhs env)))
         (cond
           [(not t) (void)]
           [(sort-smt (T-sort t))
            (define const (fresh-name (format "~a_def" name)))
            (push-prefix! (format "(declare-const ~a ~a)" const (sort-smt (T-sort t))))
            (push-prefix! (format "(assert (= ~a ~a))" const (T-smt t)))
            (assume-invariant! t push-prefix!)
            (set! env (hash-set env name
                                (T const (T-sort t) (T-measures t)
                                   (string->symbol const))))]
           ;; opaque: keep the measures it carries and the name its other
           ;; measures are cached under (a call result's, so the facts
           ;; its return refinement asserted still apply)
           [else
            (set! env (hash-set env name
                                (T #f (T-sort t) (T-measures t)
                                   (or (T-src t)
                                       (string->symbol (fresh-name (format "~a_def" name)))))))])]))
    (for ([g0 (in-list groups)] #:unless (skip-group? g0))
      (define g (group-datum g0))
      ;; anchor at the group's first term (the callee, usually), which
      ;; is what DrRacket highlights and names
      (define anchor
        (and (syntax? g0)
             (match (syntax->list g0)
               [(list _ first-term _ ...) first-term]
               [_ g0])))
      (define (add-obl! o) (add-obl0! (with-anchor o anchor)))
      (define (add-err! label why) (add-err0! label why anchor))
      (match g
        [`(group . ,toks)
         (check-ctor-escape! toks
                             (lambda (fmt . args)
                               (add-err! "a top-level use of a constructor"
                                         (apply format fmt args))))
         (walk-box-tree toks
                        (lambda (n) #f)
                        (lambda (callee-name j actual cls)
                          (parameterize ([current-extras (box '())])
                            (check-box-argument anchor-name callee-name j actual cls
                                                add-err! add-obl!)))
                        (lambda (fmt . as) (void)))
         (for ([c (in-list (find-calls toks env))])
           (match-define (list callee-name actuals path-conds call-env) c)
           ;; the built-ins `unreachable()` and `assert(P)`
           (let ([o (with-handlers ([unsupported?
                                     (lambda (e)
                                       (add-err! (format "top-level `~a`" callee-name)
                                                 (unsupported-why e))
                                       #f)])
                      (reachability-obligation anchor-name callee-name actuals path-conds call-env))])
             (when o (add-obl! o)))
           ;; constructing a datatype value at top level (a locally
           ;; bound name is not the constructor or function it may shadow)
           (let ([fields (and (not (hash-ref call-env callee-name #f))
                              (hash-ref (current-ctor-table) callee-name #f))])
             (when (and fields (= (length actuals) (length fields)))
               (for ([actual (in-list actuals)]
                     [fld (in-list fields)]
                     [j (in-naturals 1)]
                     #:when (and (dfield-refinement fld)
                                 (not (trivially-true? (dfield-refinement fld)))))
                 (match-define (refinement bound pred) (dfield-refinement fld))
                 (with-handlers ([unsupported?
                                  (lambda (e)
                                    (add-err! (format "top-level `~a`, field `~a`"
                                                      callee-name (dfield-name fld))
                                              (unsupported-why e)))])
                   (parameterize ([current-extras (box '())])
                     (define actual-t (expr->term actual call-env))
                     (define siblings (sibling-env fields actuals j call-env))
                     (define goal
                       (bool-of (parameterize ([current-allow-calls #f])
                                  (expr->term pred (hash-set siblings bound actual-t)))
                                "a datatype field refinement"))
                     (add-obl!
                      (obligation anchor-name
                                  (format "top-level ~a, field `~a`"
                                          callee-name (dfield-name fld))
                                  (assemble path-conds
                                            (format "(assert (not ~a))" goal)) (render-claim pred))))))))
           (define callee (and (not (hash-ref call-env callee-name #f))
                               (hash-ref (current-sig-table) callee-name #f)))
           (when (and callee (= (length actuals) (length (fn-params callee))))
             (for ([actual (in-list actuals)]
                   [cp (in-list (fn-params callee))]
                   [j (in-naturals 1)]
                   #:when (and (not (param-box-class cp))
                               (param-refinement cp)
                               (not (trivially-true? (param-refinement cp)))))
               (match-define (refinement bound pred) (param-refinement cp))
               (with-handlers ([unsupported?
                                (lambda (e)
                                  (add-err! (format "top-level call to `~a` (argument ~a)"
                                                    callee-name j)
                                            (unsupported-why e)))])
                 (parameterize ([current-extras (box '())])
                   (define actual-t (expr->term actual call-env))
                   (define arg-env (callee-arg-env callee actuals call-env))
                   (define goal
                     (bool-of (parameterize ([current-allow-calls #f])
                                (expr->term pred (hash-set arg-env bound actual-t)))
                              "a parameter refinement"))
                   (add-obl!
                    (obligation anchor-name
                                (format "top-level call to `~a`, argument ~a" callee-name j)
                                (assemble path-conds (format "(assert (not ~a))" goal))
                                (render-claim pred (call-subst callee actuals bound j)))))))))
         ;; bind after checking, so a def cannot refer to itself
         (match toks
           [(list-rest 'def (? symbol? name) rest)
            (define eq-pos
              (for/first ([t (in-list rest)] [i (in-naturals)]
                          #:when (equal? t '(op =)))
                i))
            (when eq-pos (bind-top-def! name (list-tail rest (add1 eq-pos))))]
           [_ (statement-assumption! toks env)])]
        [_ (void)])))
  (values (reverse obls) (reverse errs)))

;; ======================================================================
;; Entry point
;; ======================================================================

;; verify_module : rhombus-list rhombus-list -> (listof (list name-sym message))
;; Returns ALL problems: counterexamples and unanalyzable constructs.
;; `body` is the module body as `#%module-begin` received it (a list
;; holding one `multi` syntax), which is what DrRacket compiles whether
;; or not the file is saved; the file is read only if no body was
;; handed over.
(define (verify_module funs-tl defs-tl ctors-tl measures-tl [body #f])
  (verify-with funs-tl defs-tl ctors-tl measures-tl #f #f (body-groups body)))

(define (body-groups body)
  (and body
       (let ([forms (syntax->list body)])
         (and (pair? forms)
              (match (syntax->list (car forms))
                [(cons _multi gs) gs]
                [_ #f])))))

;; verify_interaction : the module's records (persisted, plus any
;; definitions typed at the prompt so far), the records typed in THIS
;; interaction, and the interaction form itself.  Only the pending
;; definitions get their own obligations; the form's top-level calls
;; are checked against everything.
(define (verify_interaction funs-tl defs-tl ctors-tl measures-tl pending-funs-tl pending-defs-tl form)
  (define groups
    (cond
      [(not form) '()]
      [else
       (match (stx-datum form)
         [(cons 'multi gs) gs]
         [g (list g)])]))
  (verify-with funs-tl defs-tl ctors-tl measures-tl
               (tl->list pending-funs-tl) (tl->list pending-defs-tl) groups))

(define (verify-with funs-tl defs-tl ctors-tl measures-tl pending-funs pending-defs groups)
  (define fun-recs (tl->list funs-tl))
  (define def-recs (tl->list defs-tl))
  (define ctor-entries (map parse-ctor-record (tl->list ctors-tl)))
  (define ctor-table (for/hash ([e (in-list ctor-entries)]) (values (first e) (third e))))
  (define ctor-type (for/hash ([e (in-list ctor-entries)]) (values (first e) (second e))))
  (define type-table
    (for/fold ([h (hash)]) ([e (in-list ctor-entries)])
      (hash-update h (second e)
                   (lambda (l) (append l (list (cons (first e) (third e)))))
                   '())))
  (parameterize ([current-type-table type-table]
                 [current-ctor-type ctor-type]
                 [current-ctor-table ctor-table]
                 [current-symbol-codes (make-hash)]
                 [current-const-sorts (make-hash)])
    (verify-module* fun-recs def-recs ctors-tl (tl->list measures-tl)
                    pending-funs pending-defs groups)))

;; The SMT text declaring this module's datatypes.
(define (datatype-decls)
  (define types (sort (hash-keys (current-type-table)) symbol<?))
  (cond
    [(null? types) ""]
    [else
     (define (field-smt-sort f) (or (sort-smt (field-sort f)) "Opaque"))
     (string-append
      (format "(declare-datatypes (~a) (~a))"
              (string-join (for/list ([t (in-list types)]) (format "(~a 0)" t)) " ")
              (string-join
               (for/list ([t (in-list types)])
                 (format "(~a)"
                         (string-join
                          (for/list ([c (in-list (hash-ref (current-type-table) t))])
                            (match-define (cons ctor fields) c)
                            (if (null? fields)
                                (format "(~a)" ctor)
                                (format "(~a ~a)" ctor
                                        (string-join
                                         (for/list ([f (in-list fields)])
                                           (format "(~a_~a ~a)" ctor (dfield-name f) (field-smt-sort f)))
                                         " "))))
                          " ")))
               " ")))]))

;; A measure as a recursive SMT function: (values header body).
(define (measure-definition m)
  (define tname (cadr (measure-scrut-sort m)))
  (define ctors (hash-ref (current-type-table) tname))
  (for ([c (in-list ctors)])
    (define n (count (lambda (cl) (eq? (car cl) (car c))) (measure-clauses m)))
    (unless (= n 1)
      (unsup "measure `~a` must have exactly one clause for constructor `~a`" (measure-name m) (car c))))
  (define cases
    (for/list ([cl (in-list (measure-clauses m))])
      (match-define (list ctor vars body-toks) cl)
      (define fields
        (cond [(assq ctor ctors) => cdr]
              [else (unsup "`~a` is not a constructor of `~a`" ctor tname)]))
      (unless (= (length vars) (length fields))
        (unsup "in measure `~a`, `~a` takes ~a field(s), got ~a" (measure-name m) ctor (length fields) (length vars)))
      (define smt-vars (for/list ([i (in-range (length vars))]) (format "v~a" i)))
      (define param-env
        (for/hash ([pr (in-list (measure-params m))] #:unless (eq? (car pr) (measure-scrut m)))
          (values (car pr) (t-of (symbol->string (car pr)) (cdr pr) (car pr)))))
      (define env
        (for/fold ([e param-env]) ([v (in-list vars)] [f (in-list fields)] [sv (in-list smt-vars)]
                                   #:unless (regexp-match? #rx"^_" (symbol->string v)))
          (define srt (field-sort f))
          (when (hash-ref e v #f)
            (unsup "in measure `~a`, pattern variable `~a` shadows a parameter" (measure-name m) v))
          (hash-set e v (if (sort-smt srt) (t-of sv srt) (t-opaque (hash) (string->symbol sv))))))
      (define t
        (parameterize ([current-allow-calls #f]
                       [current-in-measure #t]
                       [current-extras (box '())]
                       [current-prefix (box '())]
                       [current-unbox-cache (make-hash)]
                       [current-measure-cache (make-hash)])
          (expr->term body-toks env)))
      (unless (equal? (T-sort t) (measure-ret-sort m))
        (unsup "in measure `~a`, the clause for `~a` computes ~a but the measure returns ~a"
               (measure-name m) ctor (sort-word (T-sort t)) (sort-word (measure-ret-sort m))))
      (format "(~a ~a)"
              (if (null? smt-vars)
                  (symbol->string ctor)
                  (format "(~a ~a)" ctor (string-join smt-vars " ")))
              (T-smt t))))
  (values (format "(~a (~a) ~a)" (measure-name m)
                  (string-join (for/list ([pr (in-list (measure-params m))])
                                 (format "(~a ~a)" (car pr) (sort-smt (cdr pr))))
                               " ")
                  (sort-smt (measure-ret-sort m)))
          (format "(match ~a (~a))" (measure-scrut m) (string-join cases " "))))

;; The invariant of a datatype as a recursive SMT predicate: every
;; field refinement of the value's constructor (those the predicate
;; language can express), and the invariants of its datatype-typed
;; fields.  Assumed for every value of the type the checker meets;
;; sound because every construction site proves the field refinements.
(define (invariant-definition tname)
  (define ctors (hash-ref (current-type-table) tname))
  (define cases
    (for/list ([c (in-list ctors)])
      (match-define (cons ctor fields) c)
      (define smt-vars (for/list ([i (in-range (length fields))]) (format "v~a" i)))
      (define terms
        (for/list ([f (in-list fields)] [sv (in-list smt-vars)])
          (define srt (field-sort f))
          (if (sort-smt srt) (t-of sv srt) (t-opaque (hash) (string->symbol sv)))))
      (define env (for/hash ([f (in-list fields)] [t (in-list terms)]) (values (dfield-name f) t)))
      (define conjuncts
        (append
         (for/list ([f (in-list fields)] [t (in-list terms)]
                    #:when (and (dfield-refinement f) (not (trivially-true? (dfield-refinement f)))))
           (match-define (refinement bound pred) (dfield-refinement f))
           (with-handlers ([unsupported? (lambda (e) #f)])
             (parameterize ([current-allow-calls #f]
                            [current-in-measure #t]
                            [current-extras (box '())]
                            [current-prefix (box '())]
                            [current-unbox-cache (make-hash)]
                            [current-measure-cache (make-hash)])
               (bool-of (expr->term pred (hash-set env bound t)) "a datatype field refinement"))))
         (for/list ([f (in-list fields)] [t (in-list terms)]
                    #:when (data-sort? (T-sort t)))
           (format "(inv_~a ~a)" (cadr (T-sort t)) (T-smt t)))))
      (define real (filter values conjuncts))
      (format "(~a ~a)"
              (if (null? smt-vars) (symbol->string ctor) (format "(~a ~a)" ctor (string-join smt-vars " ")))
              (cond [(null? real) "true"]
                    [(null? (cdr real)) (car real)]
                    [else (format "(and ~a)" (string-join real " "))]))))
  (cons (format "(inv_~a ((v ~a)) Bool)" tname tname)
        (format "(match v (~a))" (string-join cases " "))))

;; Assume the invariant of a datatype-typed term.
(define (assume-invariant! t push)
  (when (and (data-sort? (T-sort t)) (T-smt t))
    (push (format "(assert (inv_~a ~a))" (cadr (T-sort t)) (T-smt t)))))

(define (verify-module* fun-recs def-recs ctors-tl measure-recs pending-funs pending-defs interaction-groups)
  ;; Measures are parsed first, so that every predicate can call them.
  (define-values (measures measure-errs)
    (for/fold ([ms '()] [errs '()] #:result (values (reverse ms) (reverse errs)))
              ([rec (in-list measure-recs)])
      (with-handlers ([unsupported?
                       (lambda (e)
                         (define nm (match (tl->list rec) [(cons name _) (id-sym name)]))
                         (values ms (cons (list nm (format "measure `~a`: ~a" nm (unsupported-why e)))
                                          errs)))])
        (values (cons (parse-measure-record rec) ms) errs))))
  (parameterize ([current-measure-table (for/hash ([m (in-list measures)]) (values (measure-name m) m))])
    (define-values (defs0 def-errs)
      (for/fold ([ds '()] [errs '()] #:result (values (reverse ds) (reverse errs)))
                ([m (in-list measures)])
        (with-handlers ([unsupported?
                         (lambda (e)
                           (values ds (cons (list (measure-name m)
                                                  (format "measure `~a`: ~a" (measure-name m) (unsupported-why e)))
                                            errs)))])
          (define-values (header body) (measure-definition m))
          (values (cons (cons header body) ds) errs))))
    (define inv-defs
      (for/list ([t (in-list (sort (hash-keys (current-type-table)) symbol<?))])
        (invariant-definition t)))
    (define defs (append inv-defs (reverse (reverse defs0))))
    (define decls
      (string-append
       (datatype-decls)
       (if (null? defs)
           ""
           (format "\n(define-funs-rec (~a) (~a))"
                   (string-join (map car defs) " ")
                   (string-join (map cdr defs) " ")))))
    (parameterize ([current-decls decls])
      (define problems (verify-module** fun-recs def-recs ctors-tl
                                        pending-funs pending-defs interaction-groups))
      (append (append measure-errs def-errs) problems))))

(define (verify-module** fun-recs def-recs ctors-tl pending-funs pending-defs interaction-groups)
  (define source-path
    (for/or ([rec (in-list (append fun-recs def-recs (tl->list ctors-tl)))])
      (match (tl->list rec)
        [(cons name _) (and (syntax? name)
                            (let ([src (syntax-source name)])
                              (and (path-string? src) src)))]
        [_ #f])))
  (define-values (fns rec-errs)
    (for/fold ([fns '()] [errs '()] #:result (values (reverse fns) (reverse errs)))
              ([rec (in-list fun-recs)])
      (with-handlers ([unsupported?
                       (lambda (e)
                         (define nm (match (tl->list rec)
                                      [(cons name _) (id-sym name)]))
                         (values fns (cons (list nm (format "fun `~a`: ~a" nm (unsupported-why e)))
                                           errs)))])
        (values (cons (parse-fun-record rec) fns) errs))))
  (define-values (rdefs rdef-errs)
    (for/fold ([ds '()] [errs '()] #:result (values (reverse ds) (reverse errs)))
              ([rec (in-list def-recs)])
      (with-handlers ([unsupported?
                       (lambda (e)
                         (define nm (match (tl->list rec)
                                      [(cons name _) (id-sym name)]))
                         (values ds (cons (list nm (format "def `~a`: ~a" nm (unsupported-why e)))
                                          errs)))])
        (values (cons (parse-def-record rec) ds) errs))))
  ;; In an interaction the groups are the form typed at the prompt and
  ;; only the pending definitions are checked; in a module, the whole
  ;; source and every definition.
  (define interaction? (and pending-funs #t))
  (define groups
    (cond [interaction? interaction-groups]
          [interaction-groups interaction-groups]     ; the module body, from #%module-begin
          [else (source-groups source-path)]))
  (define pending-fn-names
    (and interaction?
         (for/list ([rec (in-list pending-funs)])
           (match (tl->list rec) [(cons name _) (id-sym name)]))))
  (define pending-def-names
    (and interaction?
         (for/list ([rec (in-list pending-defs)])
           (match (tl->list rec) [(cons name _) (id-sym name)]))))
  (define anchor-name
    (cond [(pair? fns) (fn-name (car fns))]
          [(pair? rdefs) (rdef-name (car rdefs))]
          [else 'module]))
  (parameterize ([current-sig-table
                  (for/hash ([f (in-list fns)])
                    (values (fn-name f) f))]
                 [current-ctor-table (current-ctor-table)]
                 [current-top-def-names
                  (set-union
                   (for/set ([d (in-list rdefs)]) (rdef-name d))
                   (for*/set ([g0 (in-list groups)]
                              [n (in-value (match (group-datum g0)
                                             [`(group def ,(? symbol? n) . ,_) n]
                                             [_ #f]))]
                              #:when n)
                     n))])
    (define-values (box-def-table box-def-errs)
      (classify-box-defs groups (collect-box-defs groups)))
    (parameterize ([current-box-defs box-def-table]
                   [current-top-consts (compute-top-consts groups rdefs)])
      (define all-obls '())
      (define all-errs (append rec-errs rdef-errs
                               (for/list ([m (in-list box-def-errs)])
                                 (list anchor-name m))))
      (for ([f (in-list fns)]
            #:when (or (not interaction?) (memq (fn-name f) pending-fn-names)))
        (define-values (obls errs) (fn-obligations f))
        (set! all-obls (append all-obls obls))
        (set! all-errs (append all-errs errs)))
      (for ([d (in-list rdefs)]
            #:when (or (not interaction?) (memq (rdef-name d) pending-def-names)))
        (define-values (obls errs) (def-obligations d))
        (set! all-obls (append all-obls obls))
        (set! all-errs (append all-errs errs)))
      (define-values (top-obls top-errs)
        (top-level-obligations groups 'module rdefs))
      (set! all-obls (append all-obls top-obls))
      (set! all-errs (append all-errs top-errs))
      (define failures
        (with-handlers ([no-subprocess? (lambda (e) 'skipped)])
        (for/fold ([acc '()] #:result (reverse acc))
                  ([o (in-list all-obls)])
          (with-handlers ([unsupported?
                           (lambda (e)
                             (cons (list (obligation-owner o)
                                         (format "~a: ~a" (obligation-owner o) (unsupported-why e))
                                         (obligation-anchor o))
                                   acc))])
            (define-values (verdict model) (run-z3 (obligation-program o) (obligation-label o)))
            (case verdict
              [(unsat) acc]
              [(sat)
               (define who (if (eq? (obligation-owner o) 'module)
                               ""
                               (format "`~a`, " (obligation-owner o))))
               (cons (list (obligation-owner o)
                           (format "~a~a: ~a"
                                   who
                                   (obligation-label o)
                                   (violated-text (obligation-claim o)
                                                  ;; how an `unreachable()` is reached
                                                  ;; involves every assumption, so no
                                                  ;; value is filtered out
                                                  (pretty-model model
                                                                (and (not (eq? (obligation-claim o) 'unreachable))
                                                                     (obligation-program o)))))
                           (obligation-anchor o))
                     acc)])))))
      (if (eq? failures 'skipped)
          '()
          (append failures all-errs)))))
