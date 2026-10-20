# feec

A Lean 4 / Mathlib formalization of finite element exterior calculus (FEEC) for constrained
wave equations, following the thesis *A New Approach to Finite Element Simulations of General
Relativity* (Quenneville-Bélair, 2015). There is no `sorry`, `admit` or `axiom`, and every
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## The constrained FEEC theorem

`Feec.HilbertComplex.constrainedFEEC` (in `Feec/HilbertComplex/Approximation/ConstrainedFEEC.lean`).

Take a Hilbert complex `W` (any finite window of any `ComplexShape`, over `ℝ` or `ℂ`), its
Hodge wave equation `ξ' = Lξ` with `L = d − d†`, a closed constraint subspace `K`, and a family
of finite-dimensional subcomplexes `Vₕ` with uniformly bounded commuting cochain projections that
approximate `W`. Then:

1. **Well-posedness.** For data in `D(L)` the solution `e^{tL}ξ₀` exists (Stone's theorem), is
   the only strong and the only weak solution, and conserves energy.
2. **Propagation.** Every solution starting in `K` stays in `K` for all `t ∈ ℝ` if and only if
   `K` reduces `L`.
3. **Convergence.** The semi-discrete solutions `ξₕ` converge to `ξ` uniformly on `[0, T]`, for
   data in `D(L)`, and for any data in `W` once `ξₕ(0) → ξ₀`. For data in a rate class (for
   example `D(L³)` or Sobolev data, when the instance supplies the approximation estimates):
   `‖ξ(t) − ξₕ(t)‖ ≤ (1 + C_P)(1 + t)² C hᵅ ‖ξ₀‖`.
4. **Constraint residual.** If `K` reduces `L`, then `dist(ξₕ(t), K) ≤ ‖ξ(t) − ξₕ(t)‖ → 0`,
   with the same rate. If `K` does not reduce `L`, then for every `T > 0` some data leave the
   constraint within time `T`, and so do the limits of the discrete solutions, whose residuals
   tend to a positive number. In general the data lie in `K` or in `K^⊥`. On graded complexes,
   with `K` invariant under the grading and `D(L) ∩ K` dense in `K`, they lie in `D(L) ∩ K`.
   Without a grading, if `D(L) ∩ K` is dense in `K`, some datum of `D(L) ∩ K` leaves `K` at some
   `t ∈ [−T, T]`; in that case the discrete residuals are not stated.

`constrainedFEEC_nonvacuous` shows that both branches of item 4 occur.

## Instances

The "Verdict" column says which branch of item 4 holds. `C_P(1+t)²` stands for the factor
`(1 + C_P)(1 + t)²` of item 3. Lean names are relative to `Feec.Instances.Maxwell` (M) and
`Feec.Instances.EinsteinBianchi` (EB).

| Model | Domain / BCs, discretization | Constraint | Verdict | Rate | Lean name |
|---|---|---|---|---|---|
| Maxwell | `𝕋ᵈ`, spectral Galerkin | Gauss laws | converges to the constrained solution | none stated | M `torus`, `torus_converges`, `torus_residual` |
| Maxwell | `𝕋ᵈ`, spectral Galerkin | `E = 0`, `B = 0` (not reducing) | solutions and discrete limits leave `K` | — | M `torus_potential_residual` |
| Maxwell | cube `(0,½)ⁿ`, PMC / PEC, Whitney forms | Gauss laws | converges to the constrained solution | `O(h)` for `C²` orbits | M `cubePMC_rate`, `cubePEC_rate` |
| Maxwell | parallelepipeds, PMC / PEC, Whitney forms | Gauss laws | converges to the constrained solution | `O(h)` for `C²` orbits | M `paraPMC_rate`, `paraPEC_rate` |
| Maxwell | star-shaped w.r.t. a ball, PMC / PEC, Whitney forms | Gauss laws | converges to the constrained solution | `O(h)` for `C²` orbits | M `starPMC_rate`, `starPEC_rate` |
| linearized Einstein–Bianchi | `𝕋³`, Fourier spectral | TSD | converges to the constrained solution | `C_P(1+t)² (N+1)^{-s}` for `H^{2+s}` | EB `einsteinBianchi_torus_constrainedFEEC_sobolev` |
| linearized Einstein–Bianchi | `ℝ³`, no discretization | TSD | propagates (items 1–2 only) | — | EB `einsteinBianchi_euclidean` |
| linearized Einstein–Bianchi | cube, mirror BCs, cosine–sine spectral | TSD | converges to the constrained solution | `C_P(1+t)² (N+1)^{-s}` for `H^{2+s}` | EB `einsteinBianchi_mirror_constrainedFEEC_sobolev` |
| linearized Einstein–Bianchi | cube, mirror BCs, scheme (6.5)* | TSD | converges to the constrained solution | `O(h)` for `D(L³)`, `O(hˢ)` for `H^{2+s}`, `s ≤ 1` | EB `mirrorFEMVerdict` |
| linearized Einstein–Bianchi | cube, thesis BCs, scheme (6.5)* | TSD (not reducing) | converges to wrong physics | — | EB `standardCubeVerdict` |

\* Scheme (6.5) of the thesis, with the elements of Tables 5.1/6.1. It discretizes the two rows of
the BGG construction rather than the complex by subcomplexes, so these rows come from the model
theorems and not from `constrainedFEEC`. `einsteinBianchi_constrainedFEEC_summary` bundles the
Einstein–Bianchi rows.

[`docs/OVERVIEW.md`](docs/OVERVIEW.md) has the module map, further results, the corrections to the
thesis with their repaired statements, and the scope. [`docs/THESIS_MAP.md`](docs/THESIS_MAP.md)
maps every thesis result to its Lean declarations.

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
