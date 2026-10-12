#lang rhombus/scribble/manual
@(import:
    meta_label:
      only_meta 0:
        shplait open)

@(def repo_url = "https://github.com/shriram/liquid-shplait")
@// An ordinary space after `#lang`, not the non-breaking one Scribble
@// puts between code tokens: a copied `#lang` line needs a real space.
@(def lang_line = @elem([hash_lang(), " ", @tt{shplait/liquid}]))
@(fun example(name):
    @hyperlink(repo_url ++ "/blob/main/shplait/liquid/examples/" ++ name){@filepath(name)})

@title(~category: #'language){Liquid Shplait}

Liquid Shplait implements ``liquid'' typing. Liquid types are a long
line of work by Ranjit Jhala and collaborators, starting with
@hyperlink("https://dl.acm.org/doi/10.1145/1375581.1375602"){this one}.
Liquid types are a form of refinement types, which were originally
added to modern programming languages
@hyperlink("https://dl.acm.org/doi/10.1145/113445.113468"){in this work}.
Here's a
@hyperlink("https://arxiv.org/abs/2010.07763"){more recent survey}
on the concept of refinement types. Liquid Shplait is
directly inspired by and based on these ideas.

Liquid Shplait is a liquid extension to
@hyperlink("https://docs.racket-lang.org/shplait/"){Shplait}.
A refinement attaches a predicate to a type. Thus, for instance,
this example says that @rhombus(double) takes only positive integers and
returns positive integers:
@rhombusblock(
  #,(lang_line)

  fun double({n :: Int | n > 0}) :: {y :: Int | y > 0}:
    n * 2
)

While the program compiles, the checker turns every such claim into
proof obligations and asks the @hyperlink("https://github.com/Z3Prover/z3"){Z3}
solver to discharge them. If the body were @rhombus(n / 2) or
@rhombus(n - 2), the program would not compile:

@verbatim(~indent: 2){
`double`, return: the claim `y > 0` is violated when n = 1
}

If, however, the function definition were changed to
@rhombusblock(
  #,(lang_line)

  fun double({n :: Int | n > 2}) :: {y :: Int | y > 0}:
    n - 2
)
then it would again type-check without any difficulty.

Checking refinements happens purely statically. The checker does not add
run-time checks: any refinement that cannot be checked is rejected, not turned
into a run-time check. Checking happens as part of type-checking, so if the
program compiles (e.g., in DrRacket you see the REPL prompt), that means all the
checks have passed.

@docmodule(~lang, shplait/liquid)

@table_of_contents()

@// ------------------------------------------------------------
@section(~tag: "installing"){Installing Liquid Shplait}

Liquid Shplait needs Racket 9.3 or later and the
@hyperlink("https://github.com/Z3Prover/z3"){Z3} solver. Install the
package from DrRacket's @onscreen{File} menu, with @onscreen{Install
Package...} and the name @tt{liquid-shplait}, or from the command line:

@verbatim(~indent: 2){
raco pkg install liquid-shplait
}

Install Z3 with a package manager (for instance, @exec{brew install z3}
on macOS or @exec{apt install z3} on Debian and Ubuntu), or download it
from the @hyperlink("https://github.com/Z3Prover/z3/releases"){Z3
releases}. The checker looks for @exec{z3} first in the @tt{Z3}
environment variable, which should hold the path of the executable;
then on the @tt{PATH}; then, on macOS and Linux, in
@filepath{/opt/homebrew/bin}, @filepath{/usr/local/bin},
@filepath{/opt/local/bin}, @filepath{~/.local/bin} and
@filepath{~/bin}. On Windows, put the directory containing
@filepath{z3.exe} on the @tt{PATH}, or set @tt{Z3} to the path of
@filepath{z3.exe}. DrRacket started from the macOS Finder or Dock does
not see a shell's @tt{PATH}, which matters only if @exec{z3} is
somewhere else.

@// ------------------------------------------------------------
@section(~tag: "running"){Running Programs}

Run a program from the command line, on any platform:

@verbatim(~indent: 2){
racket program.rhm
}

The program is checked as it compiles, and runs if every claim holds.
In DrRacket, checking happens when you click Run, and again for each
interaction typed at the prompt. DrRacket's background expansion does
not run Z3, so a refinement error appears on Run, not as you type.

@// ------------------------------------------------------------
@section(~tag: "refinements"){Refinements}

Refinements attach to names, adding a predicate: e.g.,

@rhombusblock(
  {n :: Int | n > 0}
)

This notation should remind you of set notation from math. Vocalize the above
as ``@rhombus(n) is an @rhombus(Int), where @rhombus(n) is greater than
@rhombus(0)''. Read the stick as ``where''.

Liquid Shplait is a limited language meant primarily for educational purposes,
so it supports only limited forms of writing refinements. They may appear in the
following positions:

@itemlist(
  @item{a @rhombus(fun) parameter: @rhombus(fun f({n :: Int | n > 0}) :: Int: n);}
  @item{a @rhombus(fun) result: @rhombus(fun f(n :: Int) :: {y :: Int | y >= 0}: n * n);}
  @item{a @rhombus(def): @rhombus(def limit :: {k :: Int | k > 0} = 5);}
  @item{a @rhombus(Boxof) element: @rhombus(b :: Boxof({v :: Int | v >= 0}));}
  @item{a datatype field: @rhombus(circle(radius :: {r :: Int | r > 0})).}
)

The @rhombus(fun) or @rhombus(def) must be at the top level of the
module. A refinement anywhere else is a compile-time error
(@secref("limitations")).

You might notice in the examples above that we associate names even with the
return value of a function (such as @rhombus(y) above), which we don't normally
do. This is so that we can explicitly refer to, and refine, the return value.
This name is only bound in that predicate.

Some predicates can refer to other names. A return's predicate can
refer to the function's parameters:

@rhombusblock(
  fun percent_of({total :: Int | total >= 0},
                 {pct :: Int | pct >= 0 && pct <= 100})
    :: {out :: Int | out >= 0 && out <= total}:
    (total * pct) / 100
)

A parameter's predicate may mention the other parameters, too. At a
call, each parameter in a predicate stands for the corresponding
argument:

@rhombusblock(
  fun safe_get(s :: String, {i :: Int | i >= 0 && i < string_length(s)}) :: Char:
    string_get(s, i)

  safe_get("hello", 1)     // accepted
  safe_get("hello", 7)     // rejected: 7 < string_length("hello") is false
)

The predicate @rhombus(true) is always true. It can be useful while debugging as
you're trying to figure out the exact claim. The predicate @rhombus(#false) is
@emph{never} true, so it identifies situations that can never occur (for
instance, unreachable code: see @secref("reachability")).

Top-level definitions are immutable, so a function may use them in
its refinements and its body. If you use a @rhombus(def) with a refinement, that
refinement applies to its use as well. You can also refer to top-level
constants, which is useful for eliminating ``magic constants'' inside
refinements:

@rhombusblock(
  def TICKET_COST = 2

  fun unlock({credit :: Int | credit >= TICKET_COST}) :: Int:
    credit - TICKET_COST
)

@// ------------------------------------------------------------
@section(~tag: "proved"){What Liquid Shplait Proves}

Checking is an extended form of assume-guarantee reasoning. A function's body
can assume the refinements on its parameters; it must guarantee the refinements
on the return value. At each call, the caller must guarantee the parameters and can
assume the refinements on what the function returns.

In the example below, @rhombus(safe_div) assumes (i.e., requires) that its
second parameter be non-zero. The function @rhombus(use) expects its parameter
to be greater than zero, which means it is non-zero. Thus, Liquid Shplait will
establish that there are no (refinement) type errors in this program:

@rhombusblock(
  fun safe_div(n :: Int, {d :: Int | d != 0}) :: Int:
    n / d

  fun use({x :: Int | x > 0}) :: Int:
    safe_div(100, x)        // x > 0 gives x != 0
)

Suppose we weaken @rhombus(use)'s parameter to @rhombus({x :: Int | true}). At that
point, the call to @rhombus(safe_div) is rejected, because @rhombus(use) can no
longer guarantee what @rhombus(safe_div) assumes.

The branches of a conditional add information based on what predicates passed to
arrive at that branch. In the first arm of an @rhombus(if),
the test is known to be true, and in the second, false; each arm of an
@rhombus(if) or @rhombus(cond) is checked separately. A
@rhombus(match) clause knows that the value matched is that
constructor applied to the pattern variables.

A recursive call assumes the function's own result refinement, so a
specification by induction needs no extra annotation:

@rhombusblock(
  fun count(xs :: Listof(Int)) :: {y :: Int | y >= 0}:
    match xs
    | []: 0
    | cons(h, t): 1 + count(t)
)

This is partial correctness: if a function does not terminate, we do not know
anything about the result. Thus, every guarantee from Liquid Shplait comes with
an implicit expectation that the function terminates.

Division and @rhombus(mod) are modelled exactly as Shplait computes
them: @rhombus(/) truncates, and @rhombus(mod) takes the sign of the
divisor. That is why @rhombus(n / 2) fails for @rhombus(double) above:
when @rhombus(n) is @rhombus(1), the result is @rhombus(0).

@// ------------------------------------------------------------
@section(~tag: "rejection"){Rejections}

When a refinement claim fails, Liquid Shplait reports this and presents a
counter-example:

@verbatim(~indent: 2){
`h`, call to `safe_div`, argument 2: the claim `(a + 1) != 0` is violated when a = -1
}

Only the values the failing claim depends on are shown. When every
argument is a literal, there is nothing to show, and the message ends
with ``is violated'': the claim is false for the call as written.

Sometimes a claim may mathematically be true, but the prover is not able to
discharge it. In such cases, Liquid Shplait will halt with an error. This is an
inherent weakness of using refinement types---their dependency on provers---in
return for superior ergonomics (not having to write proofs by hand).

A construct that Liquid Shplait cannot analyze is a compile-time error
naming the construct:

@verbatim(~indent: 2){
fun `f`: cannot check the return obligation: call to `string_append`,
which is neither a function defined in this module nor one of the
builtins the checker models (`max`, `min`, ...)
}

@// ------------------------------------------------------------
@section(~tag: "datatypes"){Datatypes}

A datatype field may carry a refinement. This is proved at every
constructor application, and assumed wherever a @rhombus(match)
pattern binds the field:

@rhombusblock(
  type Shape
  | circle(radius :: {r :: Int | r > 0})
  | square(side :: {s :: Int | s > 0})

  fun area(sh :: Shape) :: {a :: Int | a > 0}:
    match sh
    | circle(r): 3 * r * r
    | square(s): s * s

  area(circle(2))          // accepted
  area(circle(0))          // rejected: 0 > 0 is false
)

A field's predicate may mention the constructor's other fields:

@rhombusblock(
  type Span
  | span(lo :: Int, hi :: {h :: Int | h >= lo})
)

A limitation of Liquid Shplait is that it can only establish the refinement
check at direct constructors. In the example above, a call like
@rhombus(map(circle, xs)) would result in an error.

@// ------------------------------------------------------------
@section(~tag: "measures"){Measure Functions}

Sometimes a predicate needs to depend on something more complicated than
a constant. For this, Liquid Shplait provides @emph{measures}.
A @rhombus(measure fun) is a function that predicates may call. Its body
is a single @rhombus(match) on a datatype parameter, with one clause
per constructor, each written in the predicate language
(@secref("predicates")). In the following example, @rhombus(OList) reflects an
ordered list (in ascending order):

@rhombusblock(
  type OList
  | onil()
  | ocons(hd :: Int, tl :: {t :: OList | is_onil(t) || ohd(t) >= hd})

  measure fun is_onil(l :: OList) :: Boolean:
    match l
    | onil(): #true
    | ocons(h, t): #false

  measure fun ohd(l :: OList) :: Int:
    match l
    | onil(): 0
    | ocons(h, t): h
)

The second field of @rhombus(ocons) says the list is sorted. A measure function
is available as an ordinary function that can be used in the program. However,
it is also available to the checker as a
recursive function that the solver interprets exactly. A refinement can,
for instance, therefore
say what inserting into an ordered list does to its head, and the
checker proves it for this key function in insertion sort:

@rhombusblock(
  fun insert(x :: Int, xs :: OList)
    :: {r :: OList | !is_onil(r)
                     && ohd(r) == (if is_onil(xs) | x | min(x, ohd(xs)))}:
    match xs
    | onil(): ocons(x, onil())
    | ocons(y, ys):
        if x <= y
        | ocons(x, ocons(y, ys))
        | ocons(y, insert(x, ys))
)

The result is never empty; its head is @rhombus(x) if @rhombus(xs)
was empty; otherwise, the head is the smaller of @rhombus(x) and the old head.

An important limitation of measure functions is that they must be total. That
means they must provide a value even when no meaningful one exists: e.g., the
@rhombus(0) above in the @rhombus(onil) case. When using measure functions,
either make this value meaningless, or guard against it ever being used (e.g.,
only caring about the value of @rhombus(ohd) in the @rhombus(ocons) case).

Lists and strings are not modelled themselves, but a predicate may
refer to them through the measures @rhombus(length),
@rhombus(string_length), @rhombus(is_empty) and @rhombus(is_cons).

@// ------------------------------------------------------------
@section(~tag: "bodies"){Checked Bodies}

The bodies of functions with refinements can use many but not all
features of Shplait.
A body is a sequence of (zero or more) local @rhombus(def)s followed by one
result expression, and it may contain:

@itemlist(
  @item{integer, boolean and symbol literals, and identifiers;}
  @item{@rhombus(+), @rhombus(-), @rhombus(*), @rhombus(/), @rhombus(mod),
    comparisons, @rhombus(&&), @rhombus(||) and @rhombus(!);}
  @item{@rhombus(if), @rhombus(cond), @rhombus(match) and @rhombus(let);}
  @item{calls to this module's functions and constructors;}
  @item{the builtins @rhombus(max), @rhombus(min), @rhombus(add1),
    @rhombus(sub1), @rhombus(is_even), @rhombus(is_odd), the list and
    string measures, and @rhombus(cons);}
  @item{@rhombus(error), @rhombus(unreachable) and @rhombus(assert) (@secref("reachability")).}
)

For instance, there is
no @rhombus(abs); write @rhombus(max(n, -n)). A local @rhombus(def) may
not shadow a parameter or an earlier local.


@// ------------------------------------------------------------
@section(~tag: "reachability"){@rhombus(error), @rhombus(unreachable) and @rhombus(assert)}

A call to @rhombus(error) never returns. Therefore, every claim about the result
holds on every path that reaches one. This makes @rhombus(error) useful
for cases not yet written and for run-time failures:

@rhombusblock(
  fun big({n :: Int | n > 0}) :: {r :: Int | r > 5}:
    if n > 5
    | n
    | error(#'big, "too small")
)

The non-@rhombus(error) paths are still checked.

However, sometimes we want to make a stronger claim: that some piece of code can
never be reached. For instance, we may match across a datatype, but a refinement
may tell us that some of those cases can never occur. For this, we can use
@rhombus(unreachable()). This is a strong claim: that this body of code will
never be called. If Liquid Shplait cannot prove that, it signals a static
error. Therefore, use
@rhombus(unreachable) instead of @rhombus(error) when that's what you mean to
signal.

@rhombusblock(
  fun sign({n :: Int | n != 0}) :: {s :: Int | s == 1 || s == -1}:
    cond
    | n > 0: 1
    | n < 0: -1
    | ~else: unreachable()
)

Without the precondition, @rhombus(sign) is rejected:

@verbatim(~indent: 2){
`sign`, call to `unreachable()`: it is reached when n = 0
}

Sometimes we want to make a claim about a particular predicate at some point in
a program. @rhombus(assert(P)) claims that @rhombus(P) holds where it is
written. @rhombus(P) must follow from the assumptions there, and
the rest of the body may then assume it:

@rhombusblock(
  fun midpoint({lo :: Int | lo >= 0}, {hi :: Int | hi >= lo})
    :: {m :: Int | m >= lo && m <= hi}:
    def half = (hi - lo) / 2
    assert(half >= 0 && half <= hi - lo)
    lo + half
)

The @rhombus(assert) states, and the checker proves, the key fact that the result
depends on. If we change the assertion to
@rhombus(assert(half > 0)), this produces an error:

@verbatim(~indent: 2){
`midpoint`, assert: the claim `half > 0` is violated when half = 0
}

Both @rhombus(unreachable) and @rhombus(assert) will signal an error at run time
(the latter only if the predicate fails). Code inside the module, which has been
checked by Liquid Shplait, can never trigger these run-time errors barring an
error in the language. However,
code in other modules is not checked (@secref("limitations")); it may violate
refinement assertions, and hence can trigger these errors.

@// ------------------------------------------------------------
@section(~tag: "polymorphism"){Polymorphic Functions}

Combining polymorphic functions with refinements needs some care. Consider the
polymorphic identity function, @rhombus(fun id(x :: ?a) :: ?a). It does not say
anything about how the return relates to its parameter except that they will be
the same type. Therefore, if we try to use it with a function that consumes and
promises to return a positive integer, it will fail:
@rhombusblock(
  fun id(x :: ?a) :: ?a:
    x

  fun pos_int({n :: Int | n > 0}) :: {r :: Int | r > 0}:
    id(n)
)

To pass, @rhombus(id) must relate its result to its argument:

@rhombusblock(
  fun id(x :: ?a) :: {r :: ?a | r == x}:
    x
)

Inside @rhombus(id), the type variable stands for any type, so the only
thing a predicate can say about a value of type @rhombus(?a) is whether or not
it is definitely equal to another.

@// ------------------------------------------------------------
@section(~tag: "boxes"){Mutable State}

Liquid Shplait allows a small amount of mutable state to be combined with
refinements. It permits writing a refinement on a @rhombus(Boxof) element.
Every write must re-establish it, so every read may assume it:

@rhombusblock(
  fun bump(b :: Boxof({v :: Int | v >= 0})) :: Void:
    set_box(b, unbox(b) + 1)

  def counter = box(0)

  bump(counter)
)

Liquid Shplait has not been proven sound, and state interacts with the other
features of the language in odd ways. Therefore, use it with caution.
Nevertheless, to try to ensure soundness, there are various restrictions on
boxes. A @rhombus(Boxof) parameter
may appear only in @rhombus(unbox(b)) and @rhombus(set_box(b, e)), or
as a whole argument to another @rhombus(Boxof) parameter with the same
element refinement. The argument for a @rhombus(Boxof) parameter must
be a literal @rhombus(box(e)), such a parameter, or a top-level
@rhombus(def) of a @rhombus(box(e)) used at only one refinement.
Without these rules, a box could be written through one view and read
through a stronger one.

@// ------------------------------------------------------------
@section(~tag: "boundary"){Checks at the Boundary}

Examples with literal arguments can make checking look entirely
static. In a real program, however, values arrive from outside the program, and
we cannot know anything about them for certain. For instance, suppose we need
the user to specify a payment amount. If they type it into a Web interface, the
program cannot know what they entered; they may even have entered a negative
``payment''.

Therefore, we cannot supply unknown values directly to functions with
refinements. We instead need run-time checks to establish what the functions
expect:

@rhombusblock(
  fun push({t :: Turnstile | !is_locked(t)}) :: Turnstile:
    locked(0)

  fun press(t :: Turnstile) :: Response:
    if is_locked(t)
    | refused()
    | succeeded(push(t))
)

The good news is that if we 
leave out the test, or test the wrong thing, Liquid Shplait will report an
error: e.g.,

@verbatim(~indent: 2){
`press`, call to `push`, argument 1: the claim `! is_locked(t)` is
violated when t = locked(0)
}

Thus, refinements do not remove run-time checks from a program's entry
points. Rather, they ensure that each check exists, is in the right place,
and is strong enough. All code past the entry points never needs to
repeat the dynamic checks, and is checked entirely statically.
The example @example("turnstile.rhm") is a complete program in this
style.

@// ------------------------------------------------------------
@section(~tag: "predicates"){The Predicate Language}

A predicate is written in a much smaller language than all of Liquid Shplait,
consistent with what the solver can handle:

@verbatim(~indent: 2){
predicate ::= integer | #true | #false | true | false
            | identifier                  a parameter, the binder, or a top-level def
            | - predicate | ! predicate
            | predicate op predicate       + - * / mod
            | predicate cmp predicate      < <= > >= == !=
            | predicate && predicate | predicate || predicate
            | ( predicate )
            | if predicate | predicate | predicate
            | builtin(predicate, ...)       max min add1 sub1 is_even is_odd
            | measure(identifier)           length string_length is_empty is_cons
            | name(predicate, ...)          a measure fun of this module
            | ctor(predicate, ...)          a constructor of this module
            | unbox(identifier)             a Boxof parameter
            | #'identifier                  a symbol, with == and != only
}

A predicate may not call an ordinary function. The only exception is
@rhombus(measure fun)s, which in turn are heavily restricted in what they can
express [@secref("measures")].

There is no one way to write a specification. Sometimes it is convenient to
write it to look more like an equation:
@rhombus({y :: Int | y == max(a, b)}). In other cases it may make more sense to
write it as a property with one
solution: @rhombus(y >= a && y >= b && (y == a || y == b)). The checker
treats them alike.

@// ------------------------------------------------------------
@section(~tag: "timeout"){Timeout}

Each obligation goes to Z3 with a ten-second limit. If Z3 times out or
answers @litchar{unknown}, the obligation fails, and the message says
the claim may still be true. The usual cause is a claim that needs
induction. The checker unfolds measures a step at a time on
constructors, and does not reason about every value of a
recursive datatype. A precondition should therefore try to use the callee's
claim with the arguments substituted in, rather than a stronger-seeming
fact that implies it only by induction. Nonlinear arithmetic can also
time out.

@// ------------------------------------------------------------
@section(~tag: "limitations"){Limitations}

@itemlist(
  @item{Only integers: Shplait has no other numbers, so amounts of money,
    for instance, must be integers (e.g., represented as cents).}
  @item{No refinements on @rhombus(Listof) or @rhombus(Mapof) elements. You can,
    however, write a custom datatype with refined fields, as in @rhombus(OList)
    above.}
  @item{No refinements on a definition inside another definition, on an
    anonymous @rhombus(fun) (a lambda), on a @rhombus(let), or in a function
    type.}
  @item{No calls to functions outside the module, beyond the modelled
    builtins.}
  @item{No measures that look inside a list: e.g., ``the result has the same
    elements as the input'' cannot be stated.}
  @item{No refinements that are themselves parameters (abstract
    refinements), and no quantified refinements.}
  @item{No measures over a polymorphic datatype.}
  @item{No nested @rhombus(match) patterns.}
  @item{No checks at module boundaries. Refinements are proved for the
    code in a module, but values that come from code the checker did not
    see (another module, or another language) are not checked. A
    constructor with a refined field can be called from such code with
    any arguments, and a function's refinements are not checked when it
    is called from there. So the guarantees hold only when a module's
    functions and constructors are used from checked code. (Shplait does
    not check values at module boundaries either.)}
)

A value whose refinement was
proved when it was made keeps that refinement, even after an operation
has produced a newer value from it. So a refinement cannot stop a
program from using an old value, such as a turnstile that has already
let someone through: @example("turnstile.rhm"). Preventing that requires
additional type system features to deal with aliasing, such as linearity or
separation logic.

@// ------------------------------------------------------------
@section(~tag: "examples"){Examples}

The repository's @hyperlink(repo_url ++ "/tree/main/shplait/liquid/examples"){examples}
directory has short programs. In each, a commented-out definition or
call marked @litchar{error:} is one the checker rejects; uncomment it to
see the message.

@itemlist(
  @item{@example("div-0.rhm") to @example("div-4.rhm"): integers with a
    distinguished zero, from plain Shplait to a division whose divisor
    cannot be zero.}
  @item{@example("str-0.rhm") to @example("str-2.rhm"): indexing into a
    string, with the index's range depending on the string, and through
    a concatenation.}
  @item{@example("turnstile.rhm"): a coin-operated turnstile, with
    operations that require a state and an interface that checks it.}
)
