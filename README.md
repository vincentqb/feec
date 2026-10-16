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

## Highlights

- Stone's theorem on real Hilbert spaces (`Feec.stoneGroup`), which discharges the existence hypotheses of Ch. 4.
- The abstract Hodge wave equation (Thms 4.6–4.7), Brezzi theory, the semi-discrete error estimate (Thm 4.14), and the BGG weak-symmetry construction (Ch. 5–6).
- Props 4.17/4.19: proved on 𝕋³ and ℝ³; on every bounded domain their hypotheses and conclusions fail, and they hold on the largest invariant constraint space, which for Prop 4.17 on every cube contains only stationary data. The Ch. 6 method inherits the bounded-domain failure.
- Eighteen corrections to the thesis, each pinned to a Lean declaration, e.g. Prop 2.4(b) is off by a factor ½, "Fredholm ⇒ closed" is false, Prop 6.2 needs compatibility conditions.

See [`docs/OVERVIEW.md`](docs/OVERVIEW.md) for the module map, the full list of corrections and the
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
