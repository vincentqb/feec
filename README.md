# feec

A Lean 4 / Mathlib formalization of the abstract framework from the thesis
*A New Approach to Finite Element Simulations of General Relativity*
(Quenneville-Bélair, 2015): Hilbert complexes, the abstract Hodge wave equation, Brezzi-type
stability, and the BGG construction with weakly imposed symmetries that underlies the
finite element discretization of the linearized Einstein–Bianchi system.

The thesis argues informally in places; here every step is checked by Lean's kernel.
Where the thesis leaves a gap or states a result imprecisely, the formal statement says
exactly what is proved and under which hypotheses.

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

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
  url     = {https://www-users.cse.umn.edu/~arnold/papers/QuennevilleThesis.pdf}
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
