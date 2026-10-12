# Notes for developing Liquid Shplait

For people and agents working on the implementation. Users should read the
guide (`shplait/liquid/scribblings/liquid-shplait.scrbl`).

## Layout

The package `liquid-shplait` is a multi-collection package that adds
`shplait/liquid` to the `shplait` collection.

- `shplait/liquid.rkt`: the language (`#lang shplait/liquid`) and its reader.
- `shplait/liquid.rhm`: re-exports it, so Rhombus code can
  `import: shplait/liquid`.
- `shplait/liquid/refinements.rhm`: the surface syntax.
- `shplait/liquid/verifier.rkt`: the checker.
- `shplait/liquid/builtins.rhm`: `unreachable` and `assert`.
- `shplait/liquid/interaction.rkt`: the module body and REPL forms the
  checker needs (DrRacket checks unsaved buffers and each interaction).
- `shplait/liquid/tests/`, `shplait/liquid/examples/`,
  `shplait/liquid/scribblings/`.

## How it works

1. The reader parses a module with Shplait's reader variant and puts
   `import: open: lib("shplait/liquid/refinements.rhm")` before the body
   and `liquid_module_end()` after it.
2. `refinements.rhm` defines `fun`, `def`, `type`, `measure fun` and `let`.
   Each strips the refinement braces, so Shplait's type checker sees only
   base types, records the refinements, parameters, body and fields for the
   checker, and hands the stripped form to Shplait.
3. When Shplait finishes expanding the module, its `finish_frame_hook` calls
   the verifier with the records. The hook is chained onto any hook already
   installed, so other extensions keep theirs.
4. `verifier.rkt` translates the claims into SMT-LIB obligations and runs
   `z3` on each, with a 10-second limit. A satisfiable obligation is a
   failed claim; its model becomes the counterexample, shown in the
   program's own names. All failures in a module are reported together, as
   one compile-time error.

Every translated expression carries a sort (integer, boolean, a module
datatype, or opaque for values the checker does not model), so sort errors
are reported by the checker rather than sent to Z3.

## Rules the implementation keeps

- **Fail closed.** A construct the checker cannot analyze, in a position
  that carries a claim, is a compile-time error naming the construct. So is
  a missing `z3`, a timeout, or an `unknown`. Never accept a claim that was
  not proved.
- Messages use the names in the program (`f(...)`, `length(l)`, the
  constructor's own name), not internal SMT names. Internal constants get a
  suffix (`_def`, `_local`, ...) that `source-name` strips.
- Names are passed to Z3 as written; a name with a non-ASCII character is
  sent as a quoted symbol (`smt-quote-non-ascii`).
- The checker adds no run-time checks.

## Tests

Run everything with `raco test -p liquid-shplait` (needs `z3`; several
minutes). `raco setup` does not compile `tests/` and `examples/` (see
`shplait/liquid/info.rkt`), because compiling them runs Z3.

- Programs that must be accepted are ordinary files, run by `raco test`:
  `tests/positive/`, `tests/datastructures/`, `tests/compat/` (plain
  Shplait is unaffected), `tests/verify/pass/`, `tests/readme/pass/`.
- Programs that must be rejected are `check_rejects: <program> ~throws
  "<message>"` cases (from `tests/eval.rhm`, after Shplait's own
  `tests/eval.rhm`) in `tests/verify_fail.rhm`, `tests/unsupported.rhm`
  (constructs outside the checked subset), `tests/negative.rhm` (rejected
  by Shplait itself) and `tests/readme_fail.rhm`.
- `tests/examples.rkt`: every `// error:` case in `examples/` is rejected,
  and the examples compile as written.
- `tests/guide.rkt`: every code block in the guide behaves as the guide
  says, and every error message the guide quotes is produced and quoted
  exactly.
- `tests/interaction-tests.rkt`, `tests/unsaved-buffer-tests.rkt`: the REPL
  and DrRacket's unsaved buffers.

Add a passing and a rejected test with each feature, and a regression test
with each fix. Comments in tests say what the test checks, not its history.

## Examples

Each file in `examples/` is a short program. Code the checker rejects is
commented out after a `// error: <what goes wrong>` line, either as one
`// ` line or as a `/* ... */` block. `tests/examples.rkt` finds these
cases.

## The guide

`scribblings/liquid-shplait.scrbl`. Its code is typeset, not evaluated, so
building the docs does not need Z3; `tests/guide.rkt` checks it instead. A
new quoted error message needs an entry in that test's `quoted` list.

Quick build, for checking edits:

```
scribble --html --dest doc-build shplait/liquid/scribblings/liquid-shplait.scrbl
```

Scribble renders spaces in code as non-breaking spaces. A copied `#lang`
line then fails to read, so the guide writes its `#lang` lines with the
`lang_line` helper, which uses an ordinary space.

## Known weaknesses

- **No checks at module boundaries.** Values from code the checker did not
  see (another module, another language) are not checked: a constructor
  with a refined field can be called with any arguments, and a function's
  parameter refinements are not checked when it is called from there.
  Shplait itself does not check values at its boundary, and exports every
  definition with no way to withhold one, so a proper boundary (checked
  only for importers) needs a change in Shplait first.
- `examples/str-0.rhm`: the error for `get("hello", -1)` is Rhombus's
  "value does not satisfy annotation", except when some other modules have
  run first in the same process, when it is Racket's `string-ref`
  contract violation. The test expecting the first can therefore fail in
  a full `raco test` run.
