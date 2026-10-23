# feec

A Lean 4 / Mathlib formalization of finite element exterior calculus (FEEC) for constrained
wave equations, following the thesis *A New Approach to Finite Element Simulations of General
Relativity* (Quenneville-Bélair, 2015). There is no `sorry`, `admit` or `axiom`, and every
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## The approximating FEEC theorem

`Feec.HilbertComplex.approxFEEC` (in `Feec/HilbertComplex/Approximation/ApproxFEEC.lean`),
statement `ApproxFEEC.Verdict`: the verdict `DissipFEEC.Verdict` of the dissipative theorem
`dissipFEEC` for its forward-time reading, and the conclusions that use both time directions,
each a named predicate of the shared vocabulary `Feec.Evolution.Scheme` (convergence from a
datum, invariance, departures, residuals). The whole statement, in words, is
[docs/headline.md](docs/headline.md) (`Feec.HilbertComplex.headline`, typeset by leantex).

Take a Hilbert complex `W` (any finite window of any `ComplexShape`, over `ℝ` or `ℂ`), its
Hodge wave equation `ξ' = Lξ` with `L = d − d†`, and a closed constraint subspace `K`. A
discretization is a family of Hilbert spaces `Xₕ` with their own inner products, skew bounded
generators `Lₕ`, and uniformly bounded maps `ιₕ : Xₕ → W` with uniformly bounded left inverses
`πₕ`. Nothing else is assumed: `ιₕ` need not be an inclusion, an isometry or a cochain map, so
variational crimes in the sense of Holst–Stern are allowed. Consistency is tested along exact
orbits: a *core* is a subspace of data with discrete comparison trajectories `pₕ(t)` such that
`ιₕ pₕ(t) → e^{tL}ξ₀` and the consistency defect `pₕ' − Lₕ pₕ → 0`, uniformly on `[0, T]`. The
discrete solution is `ξₕ(t) = ιₕ e^{tLₕ} vₕ`. Then:

1. **Well-posedness.** For data in `D(L)` the solution `e^{tL}ξ₀` exists (Stone's theorem), is
   the only strong and the only weak solution, and conserves energy.
2. **Propagation.** Every solution starting in `K` stays in `K` for all `t ∈ ℝ` if and only if
   `K` reduces `L`.
3. **Convergence.** `ξₕ → ξ` uniformly on `[0, T]` for every datum in the closure of the core and
   every family with `ιₕ vₕ → ξ₀`; `vₕ = πₕ ξ₀` is one such family. For a rate class the error is
   best approximation plus consistency:
   `‖ξ(t) − ξₕ(t)‖ ≤ (C + ‖ιₕ‖ C' t) hᵅ ‖ξ₀‖ + ‖ιₕ‖ ‖pₕ(0) − vₕ‖`.
4. **Constraint residual**, measured as `dist(ξₕ(t), K)` in `W`. If `K` reduces `L`, the
   residual is at most the error and tends to `0`. If a solution leaves a closed set `Q`, the
   residuals tend to the positive number `dist(ξ(t), Q)`. A non-reducing `K` is left by some
   datum of `K` or of `K^⊥`. If `D(L) ∩ K` is dense in `K`, a datum of `D(L) ∩ K` leaves `K` at
   some `t ∈ [−T, T]`. On graded complexes with `K` invariant under the grading, it leaves `K`
   forward in time, so its residuals tend to a positive limit.

**The conforming case.** When `Xₕ` are finite-dimensional subcomplexes with uniformly bounded
commuting cochain projections and `ιₕ` is the inclusion, this is the constrained FEEC theorem
`Feec.HilbertComplex.constrainedFEEC`, with rate factor `(1 + C_P)(1 + t)²`.
`ConstrainedFEEC.constrainedFEEC_of_approxFEEC` derives its statement verbatim from
`approxFEEC`. The witnesses `ApproxFEEC.perturbed_nonvacuous` and
`ApproxFEEC.projPerturbed_nonvacuous` (in `ApproxFEECWitness.lean`) have non-isometric `ιₕ`,
a nonzero consistency defect and an inexact scheme, and exhibit both branches of item 4.

**Discrete complexes.** `ApproxFEEC.ofComplex` (in `ApproxComplex.lean`) builds such a
discretization from finite-dimensional Hilbert complexes `Vₕ` with their own inner products and
cochain maps `iₕ : Vₕ → W` (Holst–Stern): the generator is the Hodge wave operator of `Vₕ`, and the
consistency is derived from the inner-product defect `‖1 − iₕ*iₕ‖ → 0` and graph-norm
approximation. `approxFEEC_ofComplex` adds discrete constraints: reducing subcomplexes of `Vₕ`,
such as discrete Gauss laws, are preserved exactly. `ApproxFEEC.ofComplexCrime` (in
`ApproxComplexCrime.lean`) drops the cochain condition: a discrete differential `𝐝ₕ` with
`𝐝ₕ𝐝ₕ = 0` and reading maps with a cochain defect, measured weakly; `ofComplex` is its case with
zero cochain defect. `ApproxComplexCrime.rateClass` turns complex-level rates (best
approximation, inner-product and cochain defects) into rate classes; `rateClass_of_split` does it
at order `min(α, β, γ)` from the three orders separately.

## Instances

Every row but the last is an instance of `approxFEEC`: its headline is `F.Verdict Z`, proved by
`approxFEEC F Z`, and its rate theorem applies the rate clause `approxFEEC_rate`. The last row
(absorbing boundary conditions, a dissipative generator) is an instance of `dissipFEEC`, the
dissipative extension of `approxFEEC` (an approximating discretization is a dissipative one for the
skew-adjoint generator, `ApproxFEEC.toDissipFEEC`, and the verdict of `approxFEEC` contains the
verdict of `dissipFEEC` for it).
The "Verdict" column says which branch of item 4 holds. Lean names are relative to
`Feec.Instances.Maxwell` (M), `Feec.Instances.EuclideanBand` (B) and
`Feec.Instances.EinsteinBianchi` (EB).

| Model | Domain / BCs, discretization | Constraint | Verdict | Rate | Lean name |
|---|---|---|---|---|---|
| Maxwell | `𝕋ᵈ`, spectral Galerkin | Gauss laws | converges to the constrained solution | none stated | M `torus_approxFEEC` |
| Maxwell | `𝕋ᵈ`, spectral Galerkin | `E = 0`, `B = 0` (not reducing) | solutions and discrete limits leave `K` | — | M `torus_potential_residual_of_approxFEEC` |
| Maxwell | `ℝᵈ`, frequencies `\|ξ\| ≤ N` | Gauss laws | converges; residual exactly `0` | `(N+1)^{-s}` on `Hˢ` | B `maxwell_euclidean_band` |
| Maxwell | cube `(0,½)ⁿ`, PMC / PEC, Whitney forms | Gauss laws | converges to the constrained solution | `(1 + C_P)(1 + 2t) O(h)` for `C²` orbits | M `cubePMC_approxFEEC`, `cubePMC_approx_rate` (PEC alike), `cubePMC_ofComplex`, `cubePMC_ofComplex_rate` |
| Maxwell | parallelepipeds, PMC / PEC, Whitney forms | Gauss laws | converges to the constrained solution | `(1 + C_P)(1 + 2t) O(h)` for `C²` orbits | M `paraPMC_approxFEEC`, `paraPMC_approx_rate` (PEC alike) |
| Maxwell | star-shaped w.r.t. a ball, PMC / PEC, Whitney forms | Gauss laws | converges to the constrained solution | `(1 + C_P)(1 + 2t) O(h)` for `C²` orbits | M `starPMC_approxFEEC`, `starPMC_approx_rate` (PEC alike) |
| linearized Einstein–Bianchi | `𝕋³`, Fourier spectral | TSD | converges to the constrained solution | `(N+1)^{-s}` on `Hˢ`, all `t ≥ 0` | EB `einsteinBianchi_torus_approxFEEC`, `_sobolev` |
| linearized Einstein–Bianchi | `ℝ³`, frequencies `\|ξ\| ≤ N` | TSD | converges; residual exactly `0` | `(N+1)^{-s}` on `Hˢ`, exponent sharp | B `einsteinBianchi_euclidean_band` |
| linearized Einstein–Bianchi | cube, mirror BCs, cosine–sine spectral | TSD | converges to the constrained solution | `(N+1)^{-s}` on `Hˢ`, all `t ≥ 0` | EB `einsteinBianchi_mirror_approxFEEC`, `_sobolev` |
| linearized Einstein–Bianchi | cube, mirror BCs, scheme (6.5) | TSD | converges to the constrained solution | `(4K + 8Kt) h` for `D(L³)`, `(6K + 12Kt) hˢ` for `H^{2+s}`, `s ≤ 1` | EB `mirrorFEMApproxVerdict`; `FEM.einsteinBianchi_mirrorFEM_ofComplexCrime`, `_rate`, `_rate_sobolev`; `FEM.einsteinBianchi_mirrorFEM_ofCochainDefect` |
| linearized Einstein–Bianchi | cube, thesis BCs, scheme (6.5) | TSD (not reducing) | converges to a solution that leaves TSD; residuals tend to a positive limit | — | EB `standardCubeApproxVerdict`; `FEM.einsteinBianchi_standardCube_ofComplexCrime` |
| linearized Einstein–Bianchi | cube, absorbing BCs `n × Eᵢ + (Bᵢ)_τ = 0`, Galerkin with boundary term (dense-sequence spaces) | TSD (not invariant) | well posed, radiates; converges to a solution that leaves TSD; residuals tend to a positive limit | — | EB `absorbingVerdict` |

Scheme (6.5) uses the elements of Tables 5.1/6.1 and couples the two rows of the BGG construction
by `S₀,ₕ = π¹S⁰`, in general different from `S⁰`, so its discrete complex is not a subcomplex. Its
verdicts are instances of `approxFEEC`, with the elliptic projection (6.4) of the exact solution as
comparison trajectory. Its generator is `𝐝ₕ − 𝐝ₕ*` for a discrete differential `𝐝ₕ`, so it is also
formalized through `ofComplexCrime` (via `ofGalerkinCore`): this re-derives the same verdicts from the
(6.4) cores and adds an exactly preserved discrete Gauss constraint (`FEM.hiddenGauss`; that it
lies in TSD is not shown). The cochain defect of (6.5) is
the pair of consistency functionals `ℓ((I − π¹)S⁰·)`, `⟪M, (I − π²)S¹·⟫` of the Strang bound of (6.4)
(`FEM.cochainDefectForm_eq`); for mirror BCs it vanishes on TSD states, and the mirror convergence verdict
(without rates) also follows through `ofCochainDefect` from graph-norm approximation, independently of (6.4): its
family `FEM.mirrorFamily` is built directly from the discretization, and neither the elliptic core
nor the Strang theorem is in the dependency closure (`FEM.einsteinBianchi_mirrorFEM_ofCochainDefect`).
That the cochain defect is nonzero for some mesh and datum is not proved, and the split rate
`rateClass_of_split` is exercised only by an abstract witness (limits in `docs/OVERVIEW.md`).
On `ℝ³` and `ℝᵈ` the Sobolev classes are defined on the Fourier side, and the truncation is a semi-discretization in frequency.
`einsteinBianchi_summary` bundles the Einstein–Bianchi rows.

[`docs/OVERVIEW.md`](docs/OVERVIEW.md) has the module map, further results, the corrections to the
thesis with their repaired statements, and the scope. [`docs/THESIS_MAP.md`](docs/THESIS_MAP.md)
maps every thesis result to its Lean declarations.

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
lake exe feec-gate   # the verification gate
```

`lake exe feec-gate` runs every check of the verification gate (`docs/REFACTOR_PLAN.md` §5), all
written in Lean (`scripts/FeecCheck/`): the citation convention, the import layering (the partial
order of layers of `docs/REFACTOR_PLAN.md` §1), the axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), banned identifiers, `docs/THESIS_MAP.md` up to date, the
migration coverage of `docs/migration/map.tsv`, and the names of the documentation (every Lean name
in backticks in `README.md` and `docs/*.md` is a declaration, module or namespace; historical
regions may also name pre-refactor declarations, see `scripts/FeecCheck/DocNames.lean`). It exits
nonzero on any failure and prints each violation as `path:line: message`. Each check is also an
executable of its own (`feec-citations`, `feec-layering`, `feec-axioms`, `feec-naming`,
`feec-thesismap`, `feec-mapcheck`, `feec-docnames`); `lake exe feec-thesismap` regenerates
`docs/THESIS_MAP.md`.

`lake exe feec-deps [OUT_DIR]` (`scripts/FeecCheck/Deps.lean`, default `.lake/feec-deps`) is a
measurement tool for minimality, not a gate check: it writes TSV reports of the declarations that
nothing kept uses (`dead.tsv`, from the seeds of `map.tsv`, the docs, cited docstrings and
metaprograms), wrappers, duplicate statements, name twins and the largest proofs.
`lake exe feec-deps --strip FILE OUT [DIR]` writes `FILE` without the dead groups listed in
`DIR/dead.tsv`; check a deletion by building.

The checks are compiled executables. On hosts whose C library is too old for the toolchain's
bundled `clang` (glibc < 2.29, e.g. Amazon Linux 2), point Lake at a system `clang` and the
toolchain's libraries:

```bash
LEAN_CC=$(which clang) LIBRARY_PATH="$(lean --print-prefix)/lib" lake exe feec-gate
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
