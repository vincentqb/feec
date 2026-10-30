# feec

A Lean 4 / Mathlib formalization of finite element exterior calculus (FEEC) for constrained
wave equations, following the thesis *A New Approach to Finite Element Simulations of General
Relativity* (Quenneville-Bélair, 2015). There is no `sorry`, `admit` or `axiom`, and every
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## The FEEC theorem

`Feec.HilbertComplex.ConformingFamily.feec : F.Verdict` (`Approximation/Crown.lean`) collects the
approximation theory in one statement, for every conforming family `F` of a Hilbert complex on
`ℕ` or `ℤ`: the static FEEC theorem in every degree (Arnold–Falk–Winther 2010, Thms 3.4–3.9), and
on every window with every closed constraint the semidiscrete wave and heat FEEC theorems and
the fully discrete ones for every time scheme (θ-schemes, Crank–Nicolson, and every A-stable
rational scheme of order `p ≥ 1`, among them the Gauss–Legendre, Radau IIA and SDIRK Runge–Kutta
methods, contractive by von Neumann's inequality, `Feec.TimeStepping.RationalScheme.norm_step_le`)
and for leapfrog under the CFL condition, and the perturbed theorems for every bounded
dissipative perturbation `B` (damping, Ohmic loss), discretized by `Lₕ + Pₕ B ιₕ`; the fully
discrete verdicts include forced iterates (the discrete Duhamel formula; stability against every
comparison, no forced rate) and inhomogeneous boundary data by a lifting; the Crank–Nicolson runs
of thesis Ch. 7 have the same structure (`Feec.Instances.Lifting`; their identification with a
crown scheme is open). Each field is the verdict of the layer theorem below.
`Feec.HilbertComplex.ConformingFamily.feec_rated` adds the rates `O(hᵒʳᵈ)` of a Jackson
estimate, and for the fully discrete schemes `O(hᵒʳᵈ + τᵖ)` along a smooth comparison of order
`p + 1` (`DissipFEEC.Comparison.Smooth`; no such comparison is built here for the Jackson rate
classes) and `O(hᵒʳᵈ + τ^{p/(p+2)})` uniformly in `h` for every Jackson datum and every one-step
`TimeScheme` (smoothing by time averages; not leapfrog); `docs/crown.pdf` renders the module.

Closed range of `𝔅ᵏ` is necessary for the static clause at `j → k` (the uniform discrete
Poincaré inequality forces it, `ConformingFamily.StaticVerdict.closedRangeAt`; the periodic
complex has `ℌ = 0`, a conforming family and no static verdict).
`Feec.Counterexamples.crownSharpness` (`Counterexamples/Sharpness.lean`) collects this with the
counterexamples showing that the TSD constraint is not reducing on bounded domains (so only the
departure clause applies to it) and that `P_{r+1}Λ⁰ × P_r⁻Λ¹` is not a subcomplex.
`Feec.Counterexamples.crownCorrections` (same file) collects, by reference, the thesis
corrections bearing on the crown (the statements involve no crown object; the tie is documentary):
the weak-symmetry discretization, not a stacked BGG family, has no uniqueness without exactness at
`V_h¹` and no solution for some data (Props 5.3–5.4, 6.2); continuous second-order and mixed
(first-order) wave solutions agree exactly under a compatibility condition (§4.8); Lorentz-gauge
plane waves reach the TT waves of the Einstein–Bianchi instance by the corrected gauge of Prop 2.6,
and two printed identities of §2.8 are false; `G = 0 ⇔ Ric = 0` fails in dimension `2` (§2.4).
`Feec.Instances.crownNonVacuity` (`Instances/CrownNonVacuity.lean`) instantiates the rated crown
on the Whitney forms of the cube, with closed range and `ℌ⁰ ≠ 0`, a non-reducing constraint for
which the departure clause fires, and a nonzero heat datum, and collects the non-vacuity
witnesses of the layers.

The FEEC theorem for approximating families with variational crimes in the sense of Holst and
Stern (`Feec.HilbertComplex.ApproxComplexCrime.feec`: reading maps that need not be inclusions nor
cochain maps, an inner-product and a cochain defect) is on the crown's tree: the crown imports it
and consumes it on its zero-defect instance, every conforming window read as such a family (the
last field `crime` of `ConformingFamily.Verdict`; the identification is at the level of data, and
on conforming windows the field adds the Strang, residual and defect estimates). The weak-symmetry
scheme (6.5) of the thesis applies the crime theorem under both boundary conditions, with its rates
(`Feec.Instances.EinsteinBianchiFEMCrown`).

Every one of the 394 modules is on the crown's tree: each is imported, transitively, by
`Crown.lean` or by a module that applies it (`Feec.Instances`, the sharpness and non-vacuity
companions), and is used there. The last ones tied: the scheme (6.5) and its rates (above),
`TimeStepping.BlockMatrix` (the Hermitian signed Crank–Nicolson systems, the last field
`crankNicolson_signed` of the fully discrete verdict), `Variational.Fortin` (the uniform discrete
inf-sup condition `StaticVerdict.infSup`, by Fortin operators built from the cochain projections),
`Algebra.Proxy3` (Maxwell's equations in vector proxies, `Domain.VectorProxy`,
`Instances.Maxwell.vec_maxwellFEEC`), and the thesis corrections, by reference only
(`Counterexamples.{ConstrainedEvolution, DiscreteBGG, MixedWave, Curvature, LinearizedGravity}`
and `HilbertComplex.SecondOrder`, in `crownCorrections`).

## The approximating FEEC theorem

The master theorem is a tower of three, each a structure of named conclusions extending the one
below and each proved from the one below, with every conclusion stated at the most general layer
where it holds (all in `Feec/HilbertComplex/Approximation/`):

* `Feec.HilbertComplex.dissipFEEC : F.Verdict Z` (`DissipFEEC.lean`) for a discretization
  `F : DissipFEEC A κ` of a generator `A`, m-dissipative by the field `F.isMDissipative`, whose
  exact flow `F.S` is the Lumer–Phillips contraction semigroup: well-posedness and energy, the
  propagation criteria, convergence and rates, the constraint residual and the departures from
  sets that are not kept;
* `Feec.HilbertComplex.skewFEEC` (`SkewFEEC.lean`) for `F : SkewFEEC A κ`, a skew-adjoint `A`
  (field `F.isSkewAdjoint`) with skew discrete generators (a `DissipFEEC` whose m-dissipativity
  and discrete dissipativity are derived, so cores and rate classes are shared): adds Stone's
  isometric group `F.U` (equal to `F.S` for `t ≥ 0`), conservation of the norm, reducing iff
  invariant for all `t ∈ ℝ`, and the departure in both time directions;
* `Feec.HilbertComplex.approxFEEC` (`ApproxFEEC.lean`) for `F : ApproxFEEC H κ`
  (`:= SkewFEEC H.wave κ`), the skew case of the Hodge wave operator `L = 𝐝 − 𝐝†` of a Hilbert
  complex `H`: adds unique weak solutions and, on graded complexes, reducing iff kept forward in
  time.

The regression tests `scripts/FeecCheck/Verdicts.lean` derive from the verdicts the earlier,
longer conjunctions (with the semigroup and the wave group written out, convergence on the core,
the departures with their residual limits), so the structured statement loses nothing;
`scripts/FeecCheck/MaxwellInstances.lean` pins the verdicts of the concrete Maxwell
discretizations (torus, cube, parallelepipeds, star-shaped domains) and derives the per-instance
rates of earlier versions from the FEEC theorem.

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
   residual is at most the error and tends to `0`. If a solution from a datum in the closure of
   the core leaves a closed set `Q`, the residuals tend to the positive number `dist(ξ(t), Q)`.
   A non-reducing `K` is left by some datum of `K` or of `K^⊥`. If `D(L) ∩ K` is dense in `K`, a
   datum of `D(L) ∩ K` leaves `K` at some `t ∈ [−T, T]`. On graded complexes with `K` invariant
   under the grading, it leaves `K` forward in time, and when that datum lies in the closure of
   the core its residuals tend to a positive limit. The fields of the verdicts are the
   departures `DissipFEEC.Verdict.leaves` (a set that is not kept), `leaves_smooth` (with a dense
   smooth part) and `SkewFEEC.Verdict.leaves_smooth_symm` (both time directions), and the limit
   `tendsto_infDist`; derived, not fields, are `DissipFEEC.Verdict.detects` (a departure gives a
   positive residual limit, eventually above half of it) and `dissipFEEC_leaves_of_not_isReducing`
   (the `K`-or-`K^⊥` case of `leaves`).

**The conforming case.** A conforming family (`Feec.HilbertComplex.ConformingFamily`, the data
of Arnold–Falk–Winther 2010, §3.3, with bounds in `W` rather than `V`, on any Hilbert complex) is a family of finite-dimensional
subcomplexes `Vₕ` with commuting cochain projections `πₕ`, uniformly bounded in `W`, and the
approximation property `dist(w, Vₕⁱ) → 0`. With a closed constraint
(`ConformingFamily.withConstraint`) it is the case where `ιₕ` is the inclusion, and the
constrained FEEC theorem `Feec.HilbertComplex.constrainedFEEC` gives the verdict
`ConstrainedFEEC.Verdict`. It contains items 1–4, with rate factor `(1 + C_P)(1 + t)²`. It also
contains the discrete cohomology (field `cohomology`): wherever `H` has closed range and
finite-dimensional harmonic forms, `πₕ` eventually induces isomorphisms `Hⁱ(H) ≅ Hⁱ(Vₕ)`
(Arnold–Falk–Winther 2010, Thm 3.4). `ConstrainedFEEC.constrainedFEEC_of_approxFEEC` derives
items 1–4 of the same verdict from `approxFEEC`, and the cohomology field directly. The witnesses `ApproxFEEC.perturbed_nonvacuous` and
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
`approxFEEC F Z`, and its rate theorem applies the rate clause `dissipFEEC_rate` (the field
`rate` of the verdict). The last row (absorbing boundary conditions, a dissipative generator) is
an instance of `dissipFEEC`, the base of the tower.
The "Verdict" column says which branch of item 4 holds. Lean names are relative to
`Feec.Instances.Maxwell` (M), `Feec.Instances.EuclideanBand` (B) and
`Feec.Instances.EinsteinBianchi` (EB).

| Model | Domain / BCs, discretization | Constraint | Verdict | Rate | Lean name |
|---|---|---|---|---|---|
| Maxwell | `𝕋ᵈ`, spectral Galerkin | Gauss laws | converges to the constrained solution | none stated | M `torus`, `maxwellFEEC` |
| Maxwell | `𝕋ᵈ`, spectral Galerkin | `E = 0`, `B = 0` (not reducing) | solutions and discrete limits leave `K` | — | M `torus_potential_residual_of_approxFEEC` |
| Maxwell | `ℝᵈ`, frequencies `\|ξ\| ≤ N` | Gauss laws | converges; residual exactly `0` | `(N+1)^{-s}` on `Hˢ` | B `maxwell_euclidean_band` |
| Maxwell | cube `(0,½)ⁿ`, PMC / PEC, Whitney forms and every admissible sequence `P_rΛ`/`P_r⁻Λ`; PMC with the cubical `Q_b⁻Λ` (hexahedral Nédélec) | Gauss laws | converges to the constrained solution | `(1 + C_P)(1 + 2t) O(h)` for `C²` orbits; `O(h^{s+1})` for `C^{s+2}` orbits and sequences of order `s`; for `Q_b⁻Λ`, `O(h^{s+1})` for `IsCsForm s` orbits with `s + 1 ≤ min b` | M `cubePMC`, `cubePolyPMC` (PEC alike), `maxwellFEEC` with `ConformingFamily.feec_rated` (Jackson estimates `FEM.whitneyJackson`, `FEM.polyJackson`), `cubeQMinus_maxwellFEEC` (`FEM.qMinusJackson`), `cubePMC_ofComplex` |
| Maxwell | parallelepipeds, PMC / PEC, Whitney forms and every admissible sequence | Gauss laws | converges to the constrained solution | `(1 + C_P)(1 + 2t) O(h)` for `C²` orbits; `O(h^{s+1})` for `C^{s+2}` orbits | M `paraPMC`, `paraPolyPMC` (PEC alike), `maxwellFEEC` with `ConformingFamily.feec_rated` |
| Maxwell | star-shaped w.r.t. a ball, PMC / PEC, Whitney forms and every admissible sequence | Gauss laws | converges to the constrained solution | `(1 + C_P)(1 + 2t) O(h)` for `C²` orbits; `O(h^{s+1})` for `C^{s+2}` orbits | M `starPMC`, `starPolyPMC` (PEC alike), `maxwellFEEC` with `ConformingFamily.feec_rated` |
| Maxwell in linear media | cube, parallelepipeds, star-shaped; PMC / PEC; every admissible sequence; every medium `ε = e† e`, `μ = m† m` (isotropic fields `c ≤ ε(x), μ(x) ≤ C` on the cube, projections bounded by `max √(C/c) 1` times the unweighted ones) | weighted Gauss laws `d†(εE) = 0`, `d(μH) = 0` | converges to the constrained solution (reweighted complex) | `O(h^{s+1})` for data with `C^{s+2}` unweighted orbits | M `medium_maxwellFEEC`, `cube_medium_maxwellFEEC` (`para_`, `star_` alike), `cube_isotropic_maxwellFEEC`, `norm_mediumFamily_π_le`, `mem_windowGauss_medium_iff`; `ConformingFamily.conj` |
| linearized Einstein–Bianchi | `𝕋³`, Fourier spectral | TSD | converges to the constrained solution | `(N+1)^{-s}` on `Hˢ`, all `t ≥ 0` | EB `einsteinBianchi_torus_approxFEEC`, `_sobolev` |
| linearized Einstein–Bianchi | `ℝ³`, frequencies `\|ξ\| ≤ N` | TSD | converges; residual exactly `0` | `(N+1)^{-s}` on `Hˢ`, exponent sharp | B `einsteinBianchi_euclidean_band` |
| linearized Einstein–Bianchi | cube, mirror BCs, cosine–sine spectral | TSD | converges to the constrained solution | `(N+1)^{-s}` on `Hˢ`, all `t ≥ 0` | EB `einsteinBianchi_mirror_approxFEEC`, `_sobolev` |
| linearized Einstein–Bianchi | cube, mirror BCs, scheme (6.5) | TSD | converges to the constrained solution | `(4K + 8Kt) h` for `D(L³)`, `(6K + 12Kt) hˢ` for `H^{2+s}`, `s ≤ 1` | EB `mirrorFEMApprox_verdict` (`MirrorFEMApprox.Verdict`), `FEM.mirrorComplex` |
| linearized Einstein–Bianchi | cube, thesis BCs, scheme (6.5) | TSD (not reducing) | converges to a solution that leaves TSD; residuals tend to a positive limit | — | EB `standardCubeApprox_verdict` (`StandardCubeApprox.Verdict`), `FEM.standardCubeComplex` |
| linearized Einstein–Bianchi, grad–curl (4.14) and strong symmetry (4.16) | `𝕋³`, Fourier spectral; `ℝ³`, frequencies `\|ξ\| ≤ N`; cubes and boxes, mirror BCs, cosine–sine spectral | TSD | converges to the constrained solution; the TT gravitational plane waves are exact eigenmodes | — | `Feec.Instances.EinsteinBianchi.GradCurl`: `torus_verdict`, `euclidean_verdict`, `mirror_verdict`, `mirrorCube_verdict`, `mirrorBox_verdict`, `planeWave_verdict`; `SymCurl.torus_verdict`, `SymCurl.euclidean_verdict` |
| linearized Einstein–Bianchi, grad–curl (4.14) | bounded domains, thesis BCs, every constrained FEEC discretization (none constructed yet: conditional) | TSD (not reducing) | residuals tend to `0` at all times exactly for the data of `K*`: the stationary data on cubes and boxes | — | `Feec.Instances.EinsteinBianchi.Bounded`: `residual_tendsto_zero_iff_mem_coreSub`, `cube_residual_tendsto_zero_iff`, `box_residual_tendsto_zero_iff` |
| Maxwell, `k`-forms | open `Ω ⊆ ℝⁿ`, PEC, every constrained FEEC discretization (none constructed yet: conditional; `cubePEC` is not yet identified with it) | Gauss laws | converges to the constrained solution | — | `Feec.Instances.MaxwellForms.formsFEEC` |
| linearized Einstein–Bianchi | cube, absorbing BCs `n × Eᵢ + (Bᵢ)_τ = 0`, Galerkin with boundary term (dense-sequence spaces) | TSD (not invariant) | well posed, radiates; converges to a solution that leaves TSD; residuals tend to a positive limit | — | EB `absorbingVerdict` |

Scheme (6.5) uses the elements of Tables 5.1/6.1 and couples the two rows of the BGG construction
by `S₀,ₕ = π¹S⁰`, in general different from `S⁰`, so its discrete complex is not a subcomplex. Its
generator is `𝐝ₕ − 𝐝ₕ*` for a discrete differential `𝐝ₕ`, so it is one crime front: `ofComplexCrime`
(via `ofGalerkinCore`) of its elliptic core, the elliptic projection (6.4) of the exact solution as
comparison trajectory, with an exactly preserved discrete Gauss constraint (`FEM.hiddenGauss`; that
it lies in TSD is not shown). The cochain defect of (6.5) is
the pair of consistency functionals `ℓ((I − π¹)S⁰·)`, `⟪M, (I − π²)S¹·⟫` of the Strang bound of (6.4)
(`FEM.cochainDefectForm_eq`); it is `O(h)` for the thesis' BCs (`FEM.exists_standardCube_cochainDefect_le_mesh`,
regularity of `ℓ(t)` and `M(t)` assumed) and vanishes on TSD states for mirror BCs
(`FEM.mirrorComplex_cochainDefect_eq_zero`).
That the cochain defect is nonzero for some mesh and datum is not proved, and the split rate
`rateClass_of_split` is exercised only by an abstract witness (limits in `docs/OVERVIEW.md`).
On `ℝ³` and `ℝᵈ` the Sobolev classes are defined on the Fourier side, and the truncation is a semi-discretization in frequency.
`einsteinBianchi_summary` bundles the Einstein–Bianchi rows.

## Finite elements and complexes

| Topic | Statement | Lean name |
|---|---|---|
| Finite element front end | Every conforming family, on every window and with every closed constraint, falls under `constrainedFEEC`. Whitney forms and every admissible `P_rΛ`/`P_r⁻Λ` sequence are conforming families on the Freudenthal cube, on parallelepipeds and on domains star-shaped w.r.t. a ball, and the cubical `Q_b⁻Λ` (every multidegree `b ≥ 1`) on the cubical meshes of the cube, in `HΛ`. | `ConformingFamily.withConstraint`, `ConformingFamily.window`, `Feec.Models.ConformingFamilies`, `Feec.Models.Cube.FEM.qMinusFamily` |
| Static FEEC | For every conforming family of a complex with closed range, with constants independent of `h`: the discrete Poincaré inequality, well-posedness of the discrete mixed Hodge Laplacian, vanishing harmonic gap, eventually the cohomology of the complex, quasi-optimality and convergence (Arnold–Falk–Winther 2010, Thms 3.4–3.9). With a Jackson estimate the error is `O(hᵒʳᵈ)`; under rates of the elliptic-regularity quantities `η`, `δ`, `μ`, the `L²` error of `u` is one order better (Thm 3.11). | `Feec.HilbertComplex.ConformingFamily.staticFEEC`, `Feec.HilbertComplex.ConformingFamily.StaticVerdict.rate`, `Feec.HilbertComplex.ConformingFamily.rate_static_L2` |
| Periodic table (simplicial) | Each choice of `P_r` and `P_r⁻` kinds ending in `P_sΛⁿ` gives an admissible sequence, in any dimension (that these are all of them is not formalized). Whitney forms are the `P₁⁻Λ` complex on every mesh. Closed-form dimensions are given for Lagrange, both Nédélec kinds, Raviart–Thomas and BDM in `ℝ²` and `ℝ³`. | `Feec.FiniteElement.PolySeq.ofKinds`, `Feec.FiniteElement.whitneySubcomplex_eq_trimmed`, `Feec.FiniteElement.finrank_polyMinusSpace_three_one` |
| Discrete cohomology | A cochain projection with `‖q − πq‖ < ‖q‖` on nonzero harmonic forms induces `Hⁱ(H) ≅ Hⁱ(Vₕ)`. This holds eventually for every conforming family. For `N` large, `dim Hᵏ(Vₕ) = [k = 0]`, or `[k = n]` with vanishing traces, on the cube and on parallelepipeds; on star-shaped domains with closed range and finite-dimensional harmonic forms, `dim Hᵏ(Vₕ) = dim Hᵏ(Ω)`. | `Feec.HilbertComplex.Subcomplex.CochainProjection.cohomologyEquiv`, `Feec.HilbertComplex.ConformingFamily.eventually_bijective_cohomologyMap`, `Feec.Models.Parallelepiped.eventually_finrank_cohomology_poly` |
| BGG construction | Take two complexes linked by maps `S` with `d S = −S d̃`, of any length, on any shape and over any ring. Eliminating the pairs matched by `S` leaves a derived complex with the cohomology of the twisted complex. The Arnold–Hu BGG complex on `ℤ` is a special case. On smooth fields of `ℝ³` the Hessian, elasticity and div-div complexes are the BGG complexes of vector-valued de Rham rows, with their cohomology. For bounded data the derived complex is a Hilbert complex whose cohomology has dimension at most that of the rows, with closed range wherever the rows have finite-dimensional cohomology; on `L²(Ω)` this holds for the three complexes given the regular decompositions after `J`, which are not proved. Discrete rows linked by `S` with commuting projections (`S Ṽₕ ⊆ Vₕ`, `πₕ S = S π̃ₕ`) give a conforming family of the derived complex, so the FEEC theorem holds for such discrete BGG complexes, in the graph norms. No finite element family of this kind is constructed: the only instances are the full families of finite-dimensional data (`πₕ = id`), and the Hessian, elasticity and div-div corollaries also assume the regular decompositions and finite-dimensional de Rham cohomology, neither proved. | `Feec.BGG.Data.derivedHomologyIso`, `Feec.BGG.Data.bggHomologyIso`, `Feec.Domain.hessianBGGIso`, `Feec.Domain.elasticityBGGIso`, `Feec.Domain.divDivBGGIso`, `Feec.BGG.BoundedData.derivedComplex_closedRangeAt`, `Feec.BGG.HilbertData.bggVerdict`, `Feec.Domain.hessianMaximalData_derivedVerdict`, `Feec.BGG.BoundedData.StackedFamily.derived`, `Feec.BGG.HilbertData.StackedFamily.bggVerdict`, `Feec.Domain.hessianFEEC`, `Feec.BGG.BoundedData.idShift_toHilbertData_bggVerdict` |
| Perturbations | A dissipative FEEC discretization with a dense core has consistent discrete resolvents (Trotter–Kato, converse direction), and consistency survives every bounded perturbation `B` with `A + B` dissipative, discretized by `Lₕ + Bₕ`: the perturbed discretization has the dissipative and fully discrete verdicts, and its exact flow is the Dyson–Phillips perturbation. In the crown, every window of every conforming family carries it for every bounded dissipative `B` with `Bₕ = Pₕ B ιₕ` (damped waves, damped heat flow, Maxwell with Ohmic loss `E' = −d†H − σE`); impedance (absorbing) problems, among them the absorbing Einstein–Bianchi problem on the cube, carry it too. No rate is transferred from `A` to `A + B`. | `Feec.HilbertComplex.DissipFEEC.tendsto_incl_discreteRes`, `Feec.HilbertComplex.perturbFEEC`, `Feec.HilbertComplex.constrainedFEEC_perturbed`, `Feec.Instances.Perturbed.ohmic`, `Feec.ImpedanceTriple.GalerkinData.perturbed_verdict`, `Feec.Instances.Perturbed.absorbing_perturbed` |

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

## Palomar submission

`palomar/` is a nested Lake project packaging the headline for the
[Palomar registry](https://palomar-registry.org): `palomar/Challenge.lean` restates over Mathlib
alone (about 330 lines) a Hilbert complex on ℤ, conforming families and the conclusions of the
crown (static: cohomology, well-posedness and convergence of the mixed method; wave and heat on
every window: well-posedness, semidiscrete and θ-scheme convergence for every datum, propagation
of constraints iff reducing) as one theorem, FEEC.feec; `palomar/Solution.lean` proves it from the
crown through `palomar/Solution/Bridge.lean`, with the challenge's definitions copied verbatim in
`palomar/Solution/Defs.lean`. `palomar/comparator.json` and `palomar/formalization.yaml` are the
submission metadata. Build and judge it with

```bash
cd palomar && lake build && lake comparator
```

## Citing

```bibtex
@software{QuennevilleBelair_feec,
  author  = {Quenneville-B{\'e}lair, Vincent},
  title   = {feec: A Lean formalization of finite element exterior calculus for the Einstein--Bianchi system},
  year    = {2026},
  url     = {https://github.com/vincentqb/feec}
}

@phdthesis{QuennevilleBelair2015,
  author  = {Quenneville-B{\'e}lair, Vincent},
  title   = {A New Approach to Finite Element Simulations of General Relativity},
  school  = {University of Minnesota},
  year    = {2015},
  url     = {http://hdl.handle.net/11299/175309}
}
```

## Related work

Every work cited in the Lean docstrings, and those below, has an entry in
[`docs/references.bib`](docs/references.bib).

**Papers.**

* FEEC: Arnold–Falk–Winther, [*Acta Numerica* 2006](https://doi.org/10.1017/S0962492906210018)
  and [*Bull. AMS* 2010](https://doi.org/10.1090/S0273-0979-10-01278-4); Arnold,
  [*Finite Element Exterior Calculus*](https://doi.org/10.1137/1.9781611975543) (SIAM, 2018);
  variational crimes, Holst–Stern [2012](https://doi.org/10.1007/s10208-012-9119-7); evolution
  problems, Gillette–Holst–Zhu [2017](https://doi.org/10.4208/jcm.1610-m2015-0319).
* Finite element spaces: Arnold–Logg, [*Periodic table of the finite
  elements*](https://www-users.cse.umn.edu/~arnold/papers/periodic-table.pdf) (2014); cubical
  meshes, Arnold–Awanou [2014](https://doi.org/10.1090/S0025-5718-2013-02783-4),
  Arnold–Boffi–Bonizzoni [2015](https://doi.org/10.1007/s00211-014-0631-3) and
  Gillette–Kloefkorn [2019](https://doi.org/10.1090/mcom/3354).
* BGG construction: Arnold–Hu, [*Complexes from complexes*](https://doi.org/10.1007/s10208-021-09498-9)
  (2021); Čap–Hu [2024](https://doi.org/10.1007/s10208-023-09608-9).
* Time stepping: Pazy, [*Semigroups of Linear Operators*](https://doi.org/10.1007/978-1-4612-5561-1)
  (1983); Brenner–Thomée [1979](https://doi.org/10.1137/0716051) (rational approximation of
  semigroups); Thomée, [*Galerkin Finite Element Methods for Parabolic
  Problems*](https://doi.org/10.1007/3-540-33122-0) (2006).
* Formal proofs for numerical PDEs (Coq): a finite difference scheme for the wave equation down to
  its C program, Boldo et al. [2014](https://doi.org/10.1016/j.camwa.2014.06.004); the Lax–Milgram
  theorem, Boldo et al. [2017](https://doi.org/10.1145/3018610.3018625).

**Finite element software.**

* [fem4gr](https://github.com/vincentqb/fem4gr): the FEniCS implementation of the thesis'
  Crank–Nicolson experiments (Ch. 7), whose step is formalized in `Feec.TimeStepping.Cayley`.
* [FIAT](https://github.com/firedrakeproject/fiat) (Kirby, [2004](https://doi.org/10.1145/1039813.1039820)):
  finite element bases, among them the Lagrange, Raviart–Thomas, Nédélec and BDM elements of the
  periodic table and the trimmed serendipity forms on cubes.
* [FEniCS](https://fenicsproject.org) ([book, 2012](https://doi.org/10.1007/978-3-642-23099-8);
  [DOLFINx](https://github.com/FEniCS/dolfinx), [Basix](https://github.com/FEniCS/basix)) and
  [Firedrake](https://github.com/firedrakeproject/firedrake) (Rathgeber et al.,
  [2017](https://doi.org/10.1145/2998441)): finite element solvers generated from variational forms.
* [PyDEC](https://github.com/hirani/pydec) (Bell–Hirani, [2012](https://doi.org/10.1145/2382585.2382588)):
  discrete exterior calculus and lowest-order Whitney forms on simplicial and cubical complexes.

**Lean 4.**

* [Mathlib](https://github.com/leanprover-community/mathlib4)
  ([CPP 2020](https://doi.org/10.1145/3372885.3373824)): the library this project builds on
  (Hilbert spaces, unbounded operators, homological algebra, measure theory).
* [PhysLib](https://github.com/leanprover-community/physlib) (formerly PhysLean): physics in
  Lean, including electromagnetism and relativity.
* [SciLean](https://github.com/lecopivo/SciLean): scientific computing in Lean.
* [Carleson](https://github.com/fpvandoorn/carleson): a formalization of Carleson's theorem on
  Fourier series, a large harmonic analysis project on Mathlib.
