# feec

A Lean 4 formalization, built on Mathlib, of finite element exterior calculus (FEEC) for
constrained wave equations: Galerkin approximation of Hilbert complexes, the finite element de
Rham and Bernstein–Gelfand–Gelfand complexes, time stepping, and the linearized Einstein–Bianchi
equations with their constraints. It adapts the framework of the thesis
[*A New Approach to Finite Element Simulations of General Relativity*](http://hdl.handle.net/11299/175309)
(V. Quenneville-Bélair, University of Minnesota, 2015) and the results the thesis builds on. The
library `Feec` has no `sorry`, and every constant it defines depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The results are prepared as nine entries for the [Palomar registry](https://palomar-registry.org),
one directory each under `palomar/`: a challenge stated over Mathlib alone (`Challenge.lean`),
its proof from the library (`Solution.lean`), the compared theorems (`comparator.json`) and a
description (`formalization.yaml`).

| Entry | Subject |
|---|---|
| [`feec`](palomar/feec) | Galerkin approximation of Hilbert complexes: bounded cochain projections, the static theory, the Hodge wave and heat equations |
| [`crimes`](palomar/crimes) | Variational crimes for Hilbert complexes, and mass lumping |
| [`fem`](palomar/fem) | Uniformly bounded commuting projections for the finite element de Rham complexes |
| [`shapes`](palomar/shapes) | Affinely invariant polynomial differential forms and their degrees of freedom |
| [`waves`](palomar/waves) | Finite element methods for the Hodge wave and Maxwell equations |
| [`timestepping`](palomar/timestepping) | A-stable rational time stepping for C₀-semigroups, and the heat equation in the maximum norm |
| [`bgg`](palomar/bgg) | Bernstein–Gelfand–Gelfand complexes and their cohomology |
| [`einsteinbianchi`](palomar/einsteinbianchi) | The weak-symmetry finite element method for the linearized Einstein–Bianchi equations |
| [`constraints`](palomar/constraints) | Which boundary conditions keep the constraints of the linearized Einstein–Bianchi equations |

## Build

```bash
lake exe cache get                    # prebuilt Mathlib
lake build
lake exe feec-gate                    # citations, import layering, axioms, naming, Palomar packages
cd palomar/feec && lake build && lake comparator   # one entry against its challenge
```

On hosts whose C library is older than the toolchain's `clang` needs (glibc < 2.29), run the
executables with `LEAN_CC=$(which clang) LIBRARY_PATH="$(lean --print-prefix)/lib"`.

## Citing

```bibtex
@software{QuennevilleBelair_feec,
  author  = {Quenneville-B{\'e}lair, Vincent},
  title   = {feec: A Lean formalization of finite element exterior calculus for the Einstein--Bianchi system},
  year    = {2026},
  url     = {https://github.com/vincentqb/feec}
}
```

## License

Apache License 2.0; see [LICENSE](LICENSE).
