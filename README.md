# feec

A Lean 4 / Mathlib formalization of the abstract framework from the thesis
*A New Approach to Finite Element Simulations of General Relativity*
(Quenneville-Bélair, 2015): Hilbert complexes, the abstract Hodge wave equation, Brezzi-type
stability, and the BGG construction with weakly imposed symmetries that underlies the
finite element discretization of the linearized Einstein–Bianchi system.

The thesis argues informally in places; here every step is checked by Lean's kernel.
Where the thesis leaves a gap or states a result imprecisely, the formal statement says
exactly what is proved and under which hypotheses. The development contains no `sorry`,
`admit` or `axiom`; every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

## Contents

The library is organized by mathematics, not by thesis chapter
([`docs/OVERVIEW.md`](docs/OVERVIEW.md#module-map)):

- `Feec.ForMathlib`, `Feec.Operator`, `Feec.Semigroup`, `Feec.Evolution`: unbounded operators,
  `C₀`-groups and semigroups, Stone's theorem, evolution equations, over `ℝ` and `ℂ`.
- `Feec.Variational`, `Feec.TimeStepping`: inf-sup theory, Galerkin methods, Crank–Nicolson.
- `Feec.HilbertComplex`: Hilbert complexes of any length, Hodge theory, the Hodge wave equation,
  constraint propagation, approximation, BGG complexes.
- `Feec.Fourier`, `Feec.Domain`, `Feec.Algebra`, `Feec.Geometry`: symbol complexes, `L²` fields
  on domains, polynomial forms, curvature tensors.
- `Feec.Models`, `Feec.Physics`, `Feec.Counterexamples`: the concrete complexes (torus, `ℝⁿ`,
  bounded domains, cubes), linearized gravity, the linearized and nonlinear Einstein–Bianchi
  systems, and the refutations.
- `Feec.Mesh`, `Feec.FiniteElement`: simplicial and Freudenthal meshes, `P_rΛᵏ` and `P_r⁻Λᵏ`
  elements, Whitney complexes, Stokes on simplices, interpolation error, smoothed projections.
- `Feec.Examples`, `Feec.Numerics`: non-vacuity witnesses, the Crank–Nicolson table and the
  plane-wave runs of Ch. 7.

`docs/THESIS_MAP.md` maps every thesis result to its Lean declarations.

## Highlights

- Stone's theorem over `ℝ` and `ℂ` (`LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup`): the Hodge wave equation of every Hilbert complex is well posed, with the thesis's full forcing class (Thms 4.3, 4.6–4.7).
- Constraint propagation (Props 4.16–4.19) for every Hilbert complex: a constraint propagates iff it is a reducing subcomplex. Props 4.17/4.19 hold on 𝕋³ and ℝ³; on every bounded domain their hypotheses and conclusions fail, and on cubes with the thesis's boundary conditions only stationary data propagate. With tensorial mirror boundary conditions, characterized by Green's formulas (weak trace conditions), they hold on every open cube. The Ch. 6 method inherits the bounded-domain failure.
- Brezzi theory and Babuška–Nečas over `ℝ` and `ℂ`, the semi-discrete error estimate (Thm 4.14), and the BGG weak-symmetry construction (Ch. 5–6).
- FEEC beyond the thesis: Lumer–Phillips and the Hodge heat equation, the Hodge solution operator and the quasi-optimal error estimate of the mixed method (AFW 2010, Thm 3.9), unisolvent `P_rΛᵏ`/`P_r⁻Λᵏ` elements in any dimension, and Whitney complexes on Freudenthal meshes of cubes with the finite element method's stability and convergence proved from the smoothed-projection estimates, which remain an explicit hypothesis ([coverage table](docs/OVERVIEW.md#feec-book-coverage)).
- The nonlinear Einstein–Bianchi system (§3.4) in an orthonormal frame: every vacuum metric satisfies it, it linearizes to the system of Prop 3.4, and in the thesis' `K`/`a` form the printed signs of the `B`-constraint and the `B`-evolution equation are corrected. The second Bianchi identity and its contractions are proved for metrics of any signature.
- The Ch. 7 runs as implemented, with boundary data from the exact plane wave: well posed via a lifting, the plane wave stays TSD while a TSD perturbation of its data does not, and the fully discrete Crank–Nicolson scheme on Whitney spaces is well posed with its constraint monitors bounded by the consistency error.
- Twenty corrections to the thesis, each pinned to a Lean declaration (most in `Feec.Counterexamples`), e.g. Prop 2.4(b) is off by a factor ½, "Fredholm ⇒ closed" is false, Prop 6.2 needs compatibility conditions.
- Every correction comes with a proved repaired statement (the table in [`docs/OVERVIEW.md`](docs/OVERVIEW.md#repaired-statements)). For Props 4.17/4.19 and Ch. 6 the repair covers domains without boundary and cubes, not curved domains.

See [`docs/OVERVIEW.md`](docs/OVERVIEW.md) for the module map, the full list of corrections, the repaired statements and the
scope (what enters as hypotheses), and [`docs/references.bib`](docs/references.bib) for the
bibliography cited in the docstrings.

## Citing

```bibtex
@software{QuennevilleBelair_feec,
  author  = {Quenneville-B{\'e}lair, Vincent},
  title   = {feec: A Lean formalization of finite element exterior calculus for the Einstein--Bianchi system},
  year    = {2026},
  url     = {https://github.com/vincentqb/feec}
}
```

## References

```bibtex
@phdthesis{QuennevilleBelair2015,
  author  = {Quenneville-B{\'e}lair, Vincent},
  title   = {A New Approach to Finite Element Simulations of General Relativity},
  school  = {University of Minnesota},
  year    = {2015},
  month   = jun,
  url     = {http://hdl.handle.net/11299/175309}
}

@book{Arnold2018FEEC,
  author    = {Arnold, Douglas N.},
  title     = {Finite Element Exterior Calculus},
  series    = {CBMS-NSF Regional Conference Series in Applied Mathematics},
  volume    = {93},
  publisher = {Society for Industrial and Applied Mathematics},
  address   = {Philadelphia, PA},
  year      = {2018},
  doi       = {10.1137/1.9781611975543},
  isbn      = {978-1-611975-53-6}
}
```
