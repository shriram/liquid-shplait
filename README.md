# Liquid Shplait

Refinement types for [Shplait](https://docs.racket-lang.org/shplait/),
checked at compile time by the [Z3](https://github.com/Z3Prover/z3) solver.

```
#lang shplait/liquid

fun double({n :: Int | n > 0}) :: {y :: Int | y > 0}:
  n * 2
```

## Installing

Liquid Shplait needs Racket 9.3 or later and Z3.

Install the package from DrRacket's File menu (Install Package..., with the
name `liquid-shplait`), or from the command line:

```
raco pkg install liquid-shplait
```

Install Z3 with a package manager (for instance, `brew install z3` on macOS
or `apt install z3` on Debian and Ubuntu), or from the
[Z3 releases](https://github.com/Z3Prover/z3/releases). The checker finds
`z3` through the `Z3` environment variable, the `PATH`, or the usual install
locations.

## Documentation

Installing the package installs its documentation as well. Read it using one of:

- opening documentation from DrRacket's `Help | Racket Documentation` menu and
  searching for the language, or
- visiting <https://docs.racket-lang.org/liquid-shplait/>.

Short example programs are in [`shplait/liquid/examples`](shplait/liquid/examples).

## Tests

```
raco test -p liquid-shplait
```

## License

MIT.
