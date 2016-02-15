# Vellvm-Legacy

This is a "sanitized" copy of the original Vellvm repo, not including
publication sources, experiment results, and code, test cases, and benchmarks
that we don't have the right to redistribute. Sources for the required modified
third-party libraries have been removed from the history instead provided via
patches.

The modified OCaml bindings used for the Parser, Interpreter, and
verified instrumentation/optimization passes have diverged significantly from
what is availble with newer versions of LLVM and will not compile. Neither the
bindings, SoftBound or Vmem2reg passes are currently included in the
repository. It is possible to extract the interpreter, but there is currently no
way to parse LLVM bitcode into a Vellvm AST.

## Dependencies

- [OPAM](https://opam.ocaml.org/)

## Build

```
opam switch 4.02.3
opam install ott coq.8.5.0~camlp4

make init
make
```

## Interactive Theorem Proving

It is recommended to use the following tools:

- [Emacs](https://www.gnu.org/software/emacs/),
- [ProofGeneral](http://proofgeneral.inf.ed.ac.uk/) and [Company-Coq](https://github.com/cpitclaudel/company-coq).  Here is a [installation manual](https://github.com/cpitclaudel/company-coq).
- See `.dir-locals.el` for `coq-load-path` variable.
