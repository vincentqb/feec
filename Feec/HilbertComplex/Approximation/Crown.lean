-- leantex: show = prose
module

public import Feec.HilbertComplex.Approximation.ApproxComplexCrime
public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.HilbertComplex.Approximation.HeatFEEC
public import Feec.HilbertComplex.Approximation.PerturbFEEC
public import Feec.HilbertComplex.Approximation.RationalScheme
public import Feec.HilbertComplex.Approximation.Reweight

/-!
# The FEEC theorem

One theorem collects the approximation theory of the library: static and time-dependent,
semidiscrete and fully discrete, for every conforming family of every Hilbert complex.

**The FEEC theorem** (`ConformingFamily.feec`, statement `ConformingFamily.Verdict`). Let `H` be a
Hilbert complex over `𝕜 = ℝ` or `ℂ` on `ℕ` or `ℤ` (the de Rham complex `HΛ(Ω)`, its versions
with boundary conditions, an elasticity or Hessian complex, …) and let `Vₕ` be a conforming family
of `H` along a filter `h → 0`: finite-dimensional subcomplexes with commuting cochain projections
`πₕ` bounded in `L²` uniformly in `h` and the approximation property `dist(w, Vₕ) → 0`
([AFW2010], §3.3, §5.5; [AFW2006]; [HolstStern2012], §3). Then:

1. (**static**, `static`) if `H` has closed range and `ℌʲ` is finite-dimensional, the discrete
   Poincaré inequality holds uniformly in `h`, the discrete mixed Hodge Laplacian is uniformly
   well-posed, the harmonic gap tends to `0`, `πₕ` eventually induces isomorphisms
   `Hʲ(H) ≅ Hʲ(Vₕ)`, the mixed method is quasi-optimal and converges ([AFW2010], Thms 3.4, 3.5,
   3.6, 3.8, 3.9);
2. (**wave**, `wave`, `constrained`) on every window `Wᵃ → ⋯ → W^{a+m-1}` and for every closed
   constraint `K`, the semidiscrete Hodge wave equation `ξₕ' = Lₕ ξₕ` is well-posed, conserves
   energy, converges uniformly on bounded time intervals for every convergent family of initial
   values, at the rate `(1 + C_P)(1 + t)² C hᵅ ‖ξ₀‖` on every rate class; `K` propagates iff it
   reduces `L`, the constraint residual then tends to `0`, and otherwise some datum leaves `K`
   with a positive residual in the limit ([QuennevilleBelair2015], Thms 4.6, 4.7, 4.14,
   Prop. 4.17); these are the conclusions of the skew-adjoint and dissipative FEEC theorems for
   the wave operator ([HolstStern2012], Thms 3.9, 3.10 for the elliptic analogues);
3. (**heat**, `heat`) on every window with closed range, the
   semidiscrete Hodge heat equation `uₕ' = -Δₕ uₕ` is well-posed, dissipates energy and converges
   for every datum, with the heat Ritz projection `Rₕ = Gₕ Qₕ Δ + P_ℌₕ Qₕ` built from the static
   mixed method ([AFW2010], Thm 3.9; [Wheeler1973]; [GilletteHolstZhu2017]);
4. (**fully discrete**, `full`) for every time scheme, power bounded and consistent of order `p`
   uniformly in `h` (the θ-schemes `θ ≥ ½`, implicit Euler and Crank–Nicolson are ones,
   `DissipFEEC.thetaScheme`, `DissipFEEC.crankNicolson`, and so is every A-stable rational scheme
   of order `p ≥ 1` by von Neumann's inequality, `DissipFEEC.rationalScheme`, among them the
   stability functions of A-stable implicit Runge–Kutta methods, `DissipFEEC.gaussLegendre2`,
   `DissipFEEC.radauIIA2`, `DissipFEEC.sdirk2`), the iterates of the wave and heat
   discretizations are stable and converge as `h, τ → 0`, with error at most the spatial rate
   plus the temporal error `τᵖ ‖Lₕ^{p+1} v‖`, which is `O(τᵖ)` uniformly in `h` along smooth
   comparisons for schemes consistent along trajectories ([BrennerThomee1979]; [Thomee2006],
   Ch. 7–9), and for every scheme (one-step `TimeScheme`s) and every datum of a rate class in
   `D(L)` the error from the comparison initial value is the spatial rate plus `O(τ^{p/(p+2)})`
   uniformly in `h` (the scheme is tested on data smoothed by time averages,
   `TimeScheme.norm_S_sub_sol_le_uniform`); the explicit leapfrog scheme for the wave equation
   converges under the CFL condition `τ ‖Lₕ‖ ≤ c < 1` ([Joly2003]); the time discretization of
   the exact wave and heat equations alone by every A-stable rational scheme of order `p` has
   the error `K nτ τᵖ ‖L^{p+1} x‖` on `D(L^{p+1})`, with the constant of the discrete schemes
   (Brenner–Thomée for the unbounded generators, `ConstrainedFEEC.FullVerdict.exact_wave`,
   `ConstrainedFEEC.FullVerdict.exact_heat`); the field carries
   **forcing and inhomogeneous boundary data**: the forced iterates `Wₙ₊₁ = Pₕ Wₙ + gₙ` have the
   comparison error plus the summed consistency defects (the discrete Duhamel formula,
   `DissipFEEC.TimeScheme.Verdict.forced_iterates`), and for an operator `L_max ≥ L` without
   boundary conditions and a lifting `G` of the boundary data the solution is `G` plus the mild
   solution with the forcing `f − G' + L_max G`, approximated by the lifted iterates
   `Gₕ,ₙ + ιₕ Wₙ` (`lifted_iterates`; the Crank–Nicolson runs of [QuennevilleBelair2015], Ch. 7,
   have the same structure, forced Crank–Nicolson of a compression, `Feec.Instances.Lifting`; their
   identification with a time scheme of the crown is open);
5. (**perturbed**, `perturbed`) for every bounded dissipative `B` on the window (damping, Ohmic
   loss `σ E`, absorption), the Galerkin discretizations `Lₕ + Pₕ B ιₕ` of `ξ' = (L + B) ξ` and
   `-Δₕ + Pₕ B ιₕ` of `u' = (-Δ + B) u` (`Pₕ` the orthogonal projection onto `Vₕ`) are dissipative
   FEEC discretizations whose exact flow is the Dyson–Phillips perturbation, the unique semigroup
   generated by `L + B`; their Trotter–Kato cores are dense, and the dissipative and fully
   discrete FEEC theorems hold for every datum and every time scheme ([Pazy1983], §3.1, §3.3,
   §3.4; `constrainedFEEC_perturbed`, from `perturbFEEC`: every dissipative FEEC discretization
   with a dense core has consistent resolvents, which survive bounded perturbations).

**With a Jackson estimate** (`ConformingFamily.feec_rated`, statement
`ConformingFamily.Verdict.Rated`: classes `Reg s` approximated in `Vₕ` at the order `hᵒʳᵈ⁽ˢ⁾` in the
graph norm, [AFW2010], §3.4; [Arnold2018], Ch. 7) all errors are `O(hᵒʳᵈ⁽ˢ⁾)` for regular data:
the mixed method (`rate_static`, [AFW2010], Thm 3.9), the semidiscrete wave equation
(`rate_wave`, `(1 + C_P)(1 + 2t) C L hᵒʳᵈ⁽ˢ⁾`, [QuennevilleBelair2015], Thm 4.14), the heat equation
(`rate_heat`, `(2 + 3t) K L hᵒʳᵈ⁽ˢ⁾` with `K` the constant of the static rate), and the fully
discrete schemes (`rate_full`, `O(hᵒʳᵈ⁽ˢ⁾ + τᵖ)` along smooth comparisons for schemes consistent
along trajectories, and `O(hᵒʳᵈ⁽ˢ⁾ + τ^{p/(p+2)})` for every datum of the Jackson classes and every
scheme, `FullRate.wave_uniform`, `FullRate.heat_uniform`).

**Approximating families with variational crimes** (`ApproxComplexCrime.feec`, statement
`ApproxComplexCrime.Verdict`; [HolstStern2012], §3). For discrete differential spaces `(Xₕ, 𝐝ₕ)`
with their own inner products and reading maps `iₕ` that need not be inclusions nor cochain maps,
with inner-product defect `‖1 - iₕ* iₕ‖ → 0` and consistent approximation on the admissible states
(the cochain defect `⟪𝐝ₕ* iₕ* y - iₕ* 𝐝* y, v⟫` enters the consistency residual): the approximating,
fully discrete (every time scheme, leapfrog) and perturbed (dense core) FEEC theorems on the
core, exact preservation of discrete constraints, and the Strang, residual-splitting and defect
estimates of the exact-load projection; the rates are those of its rate classes. The crown
consumes it on the zero-defect instance: every conforming window read as an approximating family
(`ConstrainedFEEC.toCrime`, `windowCrime`, with `Jₕ = 1`, zero cochain defect and the discrete
solutions of the window) satisfies it (`crime`). This identification is at the level of data;
on a conforming window the field `crime` adds to `wave`, `full` and `perturbed` (stated there on
the subcomplex front and its Ritz core) the Strang, residual and defect estimates. The
weak-symmetry scheme (6.5) of [QuennevilleBelair2015], Ch. 6 applies `ApproxComplexCrime.feec`
under both boundary conditions, with its rates (`Feec.Instances.EinsteinBianchiFEMCrown`).

The crown is assembled from the layer theorems: `ConformingFamily.staticFEEC`, `approxFEEC` and
`constrainedFEEC` for the conforming windows (`ConstrainedFEEC.toApprox` with the core of the wave
Ritz projection), `ConstrainedFEEC.heatFEEC`, and `dissipFEEC_fullyDiscrete` with
`SkewFEEC.norm_S_sub_leapfrog_le` and `SkewFEEC.crankNicolson_signed`
(`constrainedFEEC_fullyDiscrete`), `constrainedFEEC_perturbed`, and `ApproxComplexCrime.feec` (from
`approxFEEC_ofComplexCrime`, `dissipFEEC_fullyDiscrete` and `perturbFEEC`); each field is the layer
verdict itself. Every finite element family with bounded smoothed projections is a conforming family
(`Feec.Models.ConformingFamilies`: Whitney forms and every admissible sequence `P_rΛ`, `P_r⁻Λ` on
the cube, parallelepipeds and star-shaped domains, and the cubical `Q_b⁻Λ` on the cube,
`FEM.qMinusFamily`), so the crown holds for each. It also holds for every discrete BGG complex of
stacked conforming families (`S Ṽₕ ⊆ Vₕ`, `πₕ S = S π̃ₕ`): the discrete derived complexes are a
conforming family of the derived complex (`BGG.BoundedData.StackedFamily.derived`), which has closed
range under the hypotheses of the analytic BGG theorem (`BGG.HilbertData.StackedFamily.bggVerdict`;
the Hessian, elasticity and div-div complexes, `Feec.Domain.hessianFEEC`,
`Feec.Domain.elasticityFEEC`, `Feec.Domain.divDivFEEC`). Conforming families and their Jackson
estimates transfer to every reweighted complex `H.conj a` (weighted inner products, variable
coefficients: `ConformingFamily.conj`, `SubcomplexFamily.Jackson.conj`, for weights with uniformly
bounded condition numbers), so the crown holds for them as well, e.g. for Maxwell's equations in
every linear medium given by factors `ε = e† e`, `μ = m† m`, in particular isotropic media
(`Feec.Instances.MaxwellMedia`; anisotropic media once real factors are supplied). The physics
instances read through the crown: the Einstein–Bianchi systems (4.14), (4.16) on `𝕋³`, `ℝ³`, mirror
cubes and boxes, with the TT plane waves as exact modes (`Feec.Instances.EinsteinBianchiGradCurl`),
damped waves and Ohmic loss (`Feec.Instances.Perturbed`), and, for every discretization (none is
constructed yet), the TSD residuals on bounded domains and Maxwell's equations for forms
(`Feec.Instances.EinsteinBianchiBounded`, `Feec.Instances.MaxwellForms`), and Maxwell's
equations in vector proxies on `H¹ → H(curl) → H(div) → L²` (`Feec.Instances.Maxwell.vecFamily`,
`vec_maxwellFEEC`, through `Feec.Domain.deRhamVec_maximalComplex_eq_map`).

**Sharpness and non-vacuity.** Closed range of `𝔅ᵏ` is necessary for the static verdict at
`j → k` (`ConformingFamily.StaticVerdict.closedRangeAt`; the periodic complex has `ℌ = 0`, a
conforming family and no static verdict). `Feec.Counterexamples.Sharpness` (`crownSharpness`)
collects this with the counterexamples showing that the reducing hypothesis fails for the TSD
constraint (only `leaves` applies to it) and the subcomplex hypothesis for non-matching
polynomial pairs. `Feec.Instances.CrownNonVacuity` (`crownNonVacuity`) instantiates the rated
crown on the Whitney forms of the cube: closed range with `ℌ⁰ ≠ 0`, a non-reducing constraint for
which `leaves` fires, and a nonzero heat datum. `Feec.Counterexamples.Sharpness`
(`crownCorrections`) also collects, by reference, the thesis corrections bearing on the crown
(stacked BGG and (6.3), the second-order wave form, linearized gravity; no crown object occurs in
them).

**Outside the crown.**

* BGG discretizations: the BGG verdicts are in the graph norms of the domain complexes (the `L²`
  realization of the derived complex is not formalized); the regular decompositions and the
  finite-dimensional cohomology of the vector-valued de Rham complexes are hypotheses, no finite
  element family with `S Ṽₕ ⊆ Vₕ` is constructed (the only instances are the full families of
  finite-dimensional data, `πₕ = id`), and the weak-symmetry elements
  (`BGG.Discrete`, discrete connecting maps `Πₕ S`) are not stacked families: the scheme (6.5)
  of [QuennevilleBelair2015] enters through the crime crown, not through the BGG fields.
* The improved `L²` rate is conditional on rates of the elliptic quantities `η`, `δ`, `μ`
  (`ConformingFamily.rate_static_L2`, [AFW2010], Thm 3.11).
* Impedance (absorbing) boundary conditions: their discretizations are dissipative FEEC
  discretizations with their own Ritz projections, not conforming windows, and carry no rate;
  with a bounded dissipative perturbation they have the perturbed verdict
  (`ImpedanceTriple.GalerkinData.perturbed_verdict`).
* Perturbations and forcing: the perturbed verdict (`perturbed`) carries no rate of its own (the
  rate classes of `L` are not transferred to `L + B`), and forced (Duhamel) problems have no rate,
  semidiscrete or fully discrete (the fully discrete field bounds forced iterates against every
  comparison by stability; no consistency bound for a discretized load is proved).
* No-slip Stokes and conforming elastodynamics (no conforming family of their complexes).
* Explicit Runge–Kutta methods (polynomial stability functions, not bounded on the imaginary
  axis) and the sharp uniform-in-`h` order `τᵖ` along trajectories for general rational schemes
  (`TimeScheme.IsTrajConsistent` is proved for the θ-schemes only; the order `τ^{p/(p+2)}` holds
  for them as for every `TimeScheme`); the CFL condition of leapfrog is a hypothesis (no global
  inverse estimate `‖Lₕ‖ ≲ h⁻¹`).
* The sharp uniform temporal order `τᵖ` of `rate_full` holds along a smooth comparison of order
  `p + 1` (`DissipFEEC.Comparison.Smooth`, supplied by `DissipFEEC.Ritz.smooth` from a bound of
  the lifted orbit); the bound of the lifted wave and heat orbits is not packaged here, and for
  all Jackson data the uniform order is `τ^{p/(p+2)}`. The nonsmooth-data estimates of parabolic
  smoothing (heat: self-adjoint `Lₕ ≤ 0`, strongly A-stable schemes, `O(τᵖ/tᵖ)`) are not
  formalized.

## Main definitions

* `ConformingFamily.windowFEEC`: the conforming window with a constraint; `windowCrime`: the same,
  read as an approximating family with zero defects.
* `ConstrainedFEEC.FullVerdict`, `ConstrainedFEEC.FullRate`; `ConstrainedFEEC.jacksonWaveRateClass`.
* `ConformingFamily.Verdict`, `ConformingFamily.Verdict.Rated`; `ApproxComplexCrime.Verdict`.

## Main results

* **`ConformingFamily.feec`**, **`ConformingFamily.feec_rated`**, **`ApproxComplexCrime.feec`**;
  `constrainedFEEC_fullyDiscrete`, `constrainedFEEC_fullRate`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5, §5.5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5, Ch. 7, Ch. 8
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4, §4.6, §4.10, Ch. 6, Ch. 7
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7–9
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.1, §3.3, §3.4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric NormedSpace

@[expose] public noncomputable section

namespace Feec.HilbertComplex

/-! ### The fully discrete verdict of a constrained FEEC discretization -/

section Full

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  {κ : Type*}

/-- **The fully discrete verdict** of a constrained FEEC discretization `G`: the fully discrete
FEEC theorem (`dissipFEEC_fullyDiscrete`) for every time scheme of the wave discretization (with
the core of the wave Ritz projection) and of the heat discretization (with the heat core), and
the error of explicit leapfrog for the wave discretization under the CFL condition, the
Hermitian signed linear systems of its Crank–Nicolson steps, and the Brenner–Thomée error of
every A-stable rational scheme for the exact wave and heat equations (unbounded generators). -/
structure ConstrainedFEEC.FullVerdict (G : ConstrainedFEEC H κ) : Prop where
  /-- the fully discrete wave equation, for every time scheme -/
  wave (Θ : G.toApprox.TimeScheme) : Θ.Verdict G.toCore
  /-- the fully discrete heat equation, for every time scheme -/
  heat (hcr : ∀ i, H.ClosedRangeAt i) (hb : ∀ i, G.IsGraphBounded i)
    (Θ : G.toHeat.TimeScheme) : Θ.Verdict (G.heatCore hcr hb)
  /-- explicit leapfrog for the wave equation under the CFL condition `τ ‖Lₕ‖ ≤ c < 1`: the
  semidiscrete rate plus the error of the first step and a second-order temporal error -/
  leapfrog {T : ℝ} (R : G.toApprox.RateClass T) {x : PiLp 2 W} (hx : x ∈ R.Data) (h : κ)
    (v : G.toApprox.X h) {τ c : ℝ} (hτ : 0 ≤ τ) (hc : τ * ‖G.toApprox.L h‖ ≤ c) (hc1 : c < 1)
    {w : ℕ → G.toApprox.X h} (hw : TimeStepping.IsLeapfrog (G.toApprox.L h) τ w) (h0 : w 0 = v)
    {n : ℕ} (hn : (n : ℝ) * τ ∈ Icc 0 T) :
    ‖G.toApprox.S (n * τ) x - G.toApprox.incl h (w n)‖ ≤
      (R.C + ‖G.toApprox.incl h‖ * R.C' * (n * τ)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖G.toApprox.incl h‖ * ‖R.p x h 0 - v‖ +
        ‖G.toApprox.incl h‖ * (√(1 + c) * ‖w 1 - exp ((τ : 𝕜) • G.toApprox.L h) v‖ / √(1 - c) +
          n * τ * τ ^ 2 * ‖(G.toApprox.L h ^ 3) v‖ / (3 * (1 - c)))
  /-- the linear systems of Crank–Nicolson for the wave equation: in a basis `b` of `Xₕ` with
  signs `ε i = ±1` adapted to it (basis functions of different signs orthogonal, `Lₕ` coupling
  only opposite signs), the signed matrix `diag(ε) (M + (τₕ/2) K)` (Gram matrix `M`, stiffness `K`
  of `Lₕ`) is Hermitian and has the coefficients of the iterate `Pₕ v` as the unique solution of
  its system, so MINRES applies (bases indexed by `Fin m`, to which every finite basis
  reindexes) -/
  crankNicolson_signed {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) {m : ℕ}
    (b : Module.Basis (Fin m) 𝕜 (G.toApprox.X h)) (ε : Fin m → ℝ)
    (hε : ∀ i, ε i * ε i = 1) (hMε : ∀ i j, ⟪b i, b j⟫_𝕜 ≠ 0 → ε i = ε j)
    (hKε : ∀ i j, ⟪b i, G.toApprox.L h (b j)⟫_𝕜 ≠ 0 → ε i = -ε j) (v : G.toApprox.X h) :
    (Matrix.diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b +
        ((τ h / 2 : ℝ) : 𝕜) • TimeStepping.stiffness b (G.toApprox.L h))).IsHermitian ∧
      ∀ w, (Matrix.diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b +
          ((τ h / 2 : ℝ) : 𝕜) • TimeStepping.stiffness b (G.toApprox.L h))).mulVec w =
        (Matrix.diagonal (fun i => (ε i : 𝕜)) * (Matrix.gram 𝕜 b -
          ((τ h / 2 : ℝ) : 𝕜) • TimeStepping.stiffness b (G.toApprox.L h))).mulVec
            (b.equivFun v) ↔
      w = b.equivFun ((G.toApprox.crankNicolson τ hτ).P h v)
  /-- the time discretization of the exact wave equation by every A-stable rational scheme `r`
  of order `p`: `‖r(τL)ⁿ x - S(nτ) x‖ ≤ K nτ τᵖ ‖L^{p+1} x‖` for `x ∈ D(L^{p+1})` (a chain in the
  graph of `L`), with the constant `K` of the discrete schemes (Brenner–Thomée for the unbounded
  `L`, `DissipFEEC.norm_step_pow_sub_S_le`) -/
  exact_wave (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → PiLp 2 W}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ H.wave.graph) :
    ‖(r.step H.wave τ ^ n) (u 0) - G.toApprox.S (n * τ) (u 0)‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p * ‖u (p + 1)‖
  /-- the same for the exact heat equation, generator `-Δ` -/
  exact_heat (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → PiLp 2 W}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ (-H.hodgeLaplacian).graph) :
    ‖(r.step (-H.hodgeLaplacian) τ ^ n) (u 0) - G.toHeat.S (n * τ) (u 0)‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p * ‖u (p + 1)‖

/-- **The fully discrete FEEC theorem for a constrained FEEC discretization**: wave and heat, every
time scheme, leapfrog under the CFL condition, the Hermitian signed systems of Crank–Nicolson, and
the time discretization of the exact wave and heat equations by A-stable rational schemes. -/
theorem constrainedFEEC_fullyDiscrete (G : ConstrainedFEEC H κ) : G.FullVerdict :=
  ⟨fun Θ => dissipFEEC_fullyDiscrete G.toCore Θ,
    fun hcr hb Θ => dissipFEEC_fullyDiscrete (G.heatCore hcr hb) Θ,
    G.toApprox.norm_S_sub_leapfrog_le,
    fun hτ h _ b ε hε hMε hKε v => G.toApprox.crankNicolson_signed hτ h b ε hε hMε hKε v,
    fun r hr _ hp _ hτ n _ hu => G.toApprox.norm_step_pow_sub_S_le r hr hp hτ n hu,
    fun r hr _ hp _ hτ n _ hu => G.toHeat.norm_step_pow_sub_S_le r hr hp hτ n hu⟩

variable {ρ : Type*}

/-- **The wave rate class of a Jackson estimate**: the rate class of the wave Ritz projection
(`ConstrainedFEEC.RateClass.toApprox`) on the data of `ConstrainedFEEC.RateClass.ofJackson`. -/
abbrev ConstrainedFEEC.jacksonWaveRateClass (G : ConstrainedFEEC H κ) (J : G.Jackson ρ) (T : ℝ)
    (s : ρ) {L : ℝ} (hL : 0 ≤ L) : G.toApprox.RateClass T :=
  (ConstrainedFEEC.RateClass.ofJackson G J T s hL).toApprox

/-- **The fully discrete rates of a Jackson estimate** `J` of a constrained FEEC discretization
`G`: for every time scheme consistent of order `p` along trajectories and every smooth
comparison of order `p + 1` of the wave rate class (`jacksonWaveRateClass`) or of the heat rate
class (`ConstrainedFEEC.jacksonHeatRateClass` of the total Jackson estimate), the fully discrete
error is the spatial rate plus `O(τₕᵖ)`, uniformly in `h`; for every time scheme and every datum
of these classes, it is the spatial rate plus `O(τₕ^{p/(p+2)})`, uniformly in `h`. -/
structure ConstrainedFEEC.FullRate (G : ConstrainedFEEC H κ) (J : G.Jackson ρ) : Prop where
  /-- the fully discrete wave equation -/
  wave {T : ℝ} (s : ρ) {L : ℝ} (hL : 0 ≤ L) (Θ : G.toApprox.TimeScheme) {K : ℝ}
    (hΘ : Θ.IsTrajConsistent K)
    (Sm : (G.jacksonWaveRateClass J T s hL).toComparison.Smooth (Θ.p + 1)) {x : PiLp 2 W}
    (hx : x ∈ (G.jacksonWaveRateClass J T s hL).Data) (hxs : x ∈ Sm.Data) (h : κ)
    (v : G.toApprox.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖G.toApprox.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (G.jacksonWaveRateClass J T s hL).C * (G.jacksonWaveRateClass J T s hL).meshSize h ^
          (G.jacksonWaveRateClass J T s hL).α * (G.jacksonWaveRateClass J T s hL).classNorm x +
        ‖G.toApprox.incl h‖ * Θ.M T * (‖(G.jacksonWaveRateClass J T s hL).p x h 0 - v‖ +
          n * Θ.τ h * (K * Θ.τ h ^ Θ.p * Sm.B x + (G.jacksonWaveRateClass J T s hL).C' *
            (G.jacksonWaveRateClass J T s hL).meshSize h ^ (G.jacksonWaveRateClass J T s hL).α *
              (G.jacksonWaveRateClass J T s hL).classNorm x))
  /-- the fully discrete heat equation -/
  heat (hcr : ∀ i, H.ClosedRangeAt i) (hb : ∀ i, G.IsGraphBounded i) {T : ℝ} (s : ρ)
    {L : ℝ} (hL : 0 ≤ L) (Θ : G.toHeat.TimeScheme) {K : ℝ} (hΘ : Θ.IsTrajConsistent K)
    (Sm : (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).toComparison.Smooth (Θ.p + 1))
    {x : PiLp 2 W} (hx : x ∈ (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).Data)
    (hxs : x ∈ Sm.Data) (h : κ) (v : G.toHeat.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) :
    ‖G.toHeat.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).C *
          (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).meshSize h ^
            (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).α *
          (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).classNorm x +
        ‖G.toHeat.incl h‖ * Θ.M T *
          (‖(G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).p x h 0 - v‖ +
            n * Θ.τ h * (K * Θ.τ h ^ Θ.p * Sm.B x +
              (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).C' *
                (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).meshSize h ^
                  (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).α *
                (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).classNorm x))
  /-- the fully discrete wave equation for every datum of the Jackson class and every time
  scheme: the spatial rate plus `O(τₕ^{p/(p+2)})`, uniformly in `h` -/
  wave_uniform {T : ℝ} (s : ρ) {L : ℝ} (hL : 0 ≤ L) (Θ : G.toApprox.TimeScheme) {x : PiLp 2 W}
    (hx : x ∈ (G.jacksonWaveRateClass J T s hL).Data) (h : κ) (v : G.toApprox.X h) {n : ℕ}
    (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T) (hτT : Θ.τ h ^ ((Θ.p : ℝ) / (Θ.p + 2)) ≤ T) :
    ‖G.toApprox.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      ((G.jacksonWaveRateClass J T s hL).C +
          ‖G.toApprox.incl h‖ * (G.jacksonWaveRateClass J T s hL).C' * (n * Θ.τ h)) *
          ((G.jacksonWaveRateClass J T s hL).meshSize h ^ (G.jacksonWaveRateClass J T s hL).α *
            (G.jacksonWaveRateClass J T s hL).classNorm x) +
        ‖G.toApprox.incl h‖ * (Θ.M T * ‖(G.jacksonWaveRateClass J T s hL).p x h 0 - v‖ +
          (1 + Θ.M T) * (Θ.p + 1) * G.toApprox.boundConst *
            (2 * (G.jacksonWaveRateClass J T s hL).C +
              ‖G.toApprox.incl h‖ * (G.jacksonWaveRateClass J T s hL).C' * T) *
            ((G.jacksonWaveRateClass J T s hL).meshSize h ^ (G.jacksonWaveRateClass J T s hL).α *
              (G.jacksonWaveRateClass J T s hL).classNorm x) +
          Θ.τ h ^ ((Θ.p : ℝ) / (Θ.p + 2)) * ((1 + Θ.M T) * (Θ.p + 1) * G.toApprox.boundConst *
            ‖DissipFEEC.genExt H.wave x‖ + Θ.M T * Θ.K * (n * Θ.τ h) * 2 ^ (Θ.p + 1) *
              ‖(G.jacksonWaveRateClass J T s hL).p x h 0‖))
  /-- the fully discrete heat equation for every datum of the Jackson class and every time
  scheme: the spatial rate plus `O(τₕ^{p/(p+2)})`, uniformly in `h` -/
  heat_uniform (hcr : ∀ i, H.ClosedRangeAt i) (hb : ∀ i, G.IsGraphBounded i) {T : ℝ}
    (s : ρ) {L : ℝ} (hL : 0 ≤ L) (Θ : G.toHeat.TimeScheme) {x : PiLp 2 W}
    (hx : x ∈ (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).Data) (h : κ)
    (v : G.toHeat.X h) {n : ℕ} (hn : (n : ℝ) * Θ.τ h ∈ Icc 0 T)
    (hτT : Θ.τ h ^ ((Θ.p : ℝ) / (Θ.p + 2)) ≤ T) :
    ‖G.toHeat.S (n * Θ.τ h) x - Θ.sol h v n‖ ≤
      ((G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).C + ‖G.toHeat.incl h‖ *
          (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).C' * (n * Θ.τ h)) *
          ((G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).meshSize h ^
              (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).α *
            (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).classNorm x) +
        ‖G.toHeat.incl h‖ * (Θ.M T *
            ‖(G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).p x h 0 - v‖ +
          (1 + Θ.M T) * (Θ.p + 1) * G.toHeat.boundConst *
            (2 * (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).C + ‖G.toHeat.incl h‖ *
              (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).C' * T) *
            ((G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).meshSize h ^
                (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).α *
              (G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).classNorm x) +
          Θ.τ h ^ ((Θ.p : ℝ) / (Θ.p + 2)) * ((1 + Θ.M T) * (Θ.p + 1) * G.toHeat.boundConst *
            ‖DissipFEEC.genExt (-H.hodgeLaplacian) x‖ + Θ.M T * Θ.K * (n * Θ.τ h) *
              2 ^ (Θ.p + 1) * ‖(G.jacksonHeatRateClass hcr hb (G.totalJackson J) s hL T).p x h 0‖))

/-- **The fully discrete rates of a Jackson estimate** (`ConstrainedFEEC.FullRate`), the field
`rate_smooth_iterates` of the fully discrete verdicts at the Jackson rate classes. -/
theorem constrainedFEEC_fullRate (G : ConstrainedFEEC H κ) (J : G.Jackson ρ) : G.FullRate J :=
  ⟨fun _ _ _ Θ _ hΘ Sm _ hx hxs h v _ hn =>
      ((constrainedFEEC_fullyDiscrete G).wave Θ).rate_smooth_iterates hΘ _ Sm hx hxs h v hn,
    fun hcr hb _ _ _ _ Θ _ hΘ Sm _ hx hxs h v _ hn =>
      ((constrainedFEEC_fullyDiscrete G).heat hcr hb Θ).rate_smooth_iterates hΘ _ Sm hx hxs h v hn,
    fun s _ hL Θ _ hx h v _ hn hτT => ((constrainedFEEC_fullyDiscrete G).wave Θ).rate_uniform_iterates
      _ hx ((ConstrainedFEEC.RateClass.ofJackson G J _ s hL).mem_domain _ hx) h v hn hτT,
    fun hcr hb _ _ _ _ Θ _ hx h v _ hn hτT =>
      ((constrainedFEEC_fullyDiscrete G).heat hcr hb Θ).rate_uniform_iterates _ hx hx.1.1 h v hn hτT⟩

end Full

/-! ### The crown for approximating families with variational crimes -/

section Crime

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  {κ : Type*}

namespace ApproxComplexCrime

open ApproxFEEC

/-- **The conclusions of the FEEC theorem for approximating families** (`ApproxComplexCrime.feec`)
of discrete differential spaces `(Xₕ, 𝐝ₕ)` with reading maps `iₕ` that need not be cochain maps
nor isometric ([HolstStern2012], §3): the approximating, fully discrete and perturbed FEEC
theorems of the crime front `ofComplexCrime F` on its core, the discrete generator, the discrete
constraints, and the
complex-level estimates of the exact-load projection `Rₕ y = (1 - Lₕ)⁻¹ iₕ* (1 - L) y` (Strang
lemma, residual splitting into the inner-product defect, the graph-norm approximation error and
the cochain defect, defect bound, and their limits). The rates are the fields `wave.rate` and
`(full Θ).rate_*` at the rate classes of `ofComplexCrime F` (e.g. `rateClass_of_split`,
`galerkinRateClass`). -/
structure Verdict (F : ApproxComplexCrime H κ) : Prop where
  /-- the approximating FEEC theorem of the crime front on its core -/
  wave : (ofComplexCrime F).Verdict (ofComplexCrimeCore F)
  /-- the fully discrete FEEC theorem, for every time scheme -/
  full (Θ : (ofComplexCrime F).TimeScheme) : Θ.Verdict (ofComplexCrimeCore F)
  /-- explicit leapfrog under the CFL condition `τ ‖Lₕ‖ ≤ c < 1` -/
  leapfrog {T : ℝ} (R : (ofComplexCrime F).RateClass T) {x : PiLp 2 W} (hx : x ∈ R.Data) (h : κ)
    (v : (ofComplexCrime F).X h) {τ c : ℝ} (hτ : 0 ≤ τ) (hc : τ * ‖(ofComplexCrime F).L h‖ ≤ c)
    (hc1 : c < 1) {w : ℕ → (ofComplexCrime F).X h}
    (hw : TimeStepping.IsLeapfrog ((ofComplexCrime F).L h) τ w) (h0 : w 0 = v) {n : ℕ}
    (hn : (n : ℝ) * τ ∈ Icc 0 T) :
    ‖(ofComplexCrime F).S (n * τ) x - (ofComplexCrime F).incl h (w n)‖ ≤
      (R.C + ‖(ofComplexCrime F).incl h‖ * R.C' * (n * τ)) *
          (R.meshSize h ^ R.α * R.classNorm x) +
        ‖(ofComplexCrime F).incl h‖ * ‖R.p x h 0 - v‖ +
        ‖(ofComplexCrime F).incl h‖ *
          (√(1 + c) * ‖w 1 - exp ((τ : 𝕜) • (ofComplexCrime F).L h) v‖ / √(1 - c) +
            n * τ * τ ^ 2 * ‖((ofComplexCrime F).L h ^ 3) v‖ / (3 * (1 - c)))
  /-- the perturbed FEEC theorem for every bounded perturbation, when the core is dense -/
  perturbed (hZ : (ofComplexCrimeCore F).Data.topologicalClosure = ⊤)
    (P : (ofComplexCrime F).Perturbation) : P.Verdict (P.core (ofComplexCrimeCore F) hZ)
  /-- an `Lₕ`-invariant subspace of `Xₕ` is preserved exactly by the discrete solutions -/
  invariant (h : κ) (Kh : Submodule 𝕜 (F.toFamily.X h)) (hKh : ∀ v ∈ Kh, F.toFamily.L h v ∈ Kh)
    {v : F.toFamily.X h} (hv : v ∈ Kh) (t : ℝ) : ((ofComplexCrime F).group h).S t v ∈ Kh
  /-- and if it is read inside `K`, the residual of its discrete solutions is `0` -/
  residual_eq_zero (h : κ) (Kh : Submodule 𝕜 (F.toFamily.X h))
    (hKh : ∀ v ∈ Kh, F.toFamily.L h v ∈ Kh)
    (hKK : Kh.map (F.toFamily.incl h : F.toFamily.X h →ₗ[𝕜] PiLp 2 W) ≤ F.K)
    {v : F.toFamily.X h} (hv : v ∈ Kh) (t : ℝ) :
    infDist ((ofComplexCrime F).sol h v t) (F.K : Set (PiLp 2 W)) = 0
  /-- the Strang lemma: best approximation plus residual -/
  strang (h : κ) (y z : PiLp 2 W) (w : F.toFamily.X h) {ε : ℝ} (hε : 0 ≤ ε)
    (hres : ∀ v, ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪z, F.toFamily.incl h v⟫_𝕜‖ ≤
      ε * (‖v‖ + ‖F.toFamily.D h v‖)) :
    ‖y - F.toFamily.incl h (F.toFamily.load h z)‖ ≤
      ‖y - F.toFamily.incl h w‖ + 8 * F.toFamily.boundConst * ε
  /-- the residual splits into the inner-product defect, the graph-norm approximation error and
  the cochain defect -/
  residual_le (h : κ) (y : H.wave.domain) (w : F.toFamily.X h) {δ : ℝ}
    (hδ : ∀ v, ‖⟪F.toFamily.cochainDefect h y, v⟫_𝕜‖ ≤ δ * (‖v‖ + ‖F.toFamily.D h v‖))
    (v : F.toFamily.X h) :
    ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, F.toFamily.incl h v⟫_𝕜‖ ≤
      (‖1 - F.toFamily.J h‖ * (‖w‖ + ‖F.toFamily.D h w‖) +
        F.toFamily.boundConst * (‖(y : PiLp 2 W) - F.toFamily.incl h w‖ +
          ‖H.totalD ⟨y, y.2.1⟩ - F.toFamily.incl h (F.toFamily.D h w)‖) + δ) *
        (‖v‖ + ‖F.toFamily.D h v‖)
  /-- the defect bound `‖Rₕ z - iₕ* y‖ ≤ ‖1 - Jₕ‖ ‖Rₕ z‖ + C ‖y - iₕ Rₕ z‖` -/
  defect_le (h : κ) (y z : PiLp 2 W) :
    ‖F.toFamily.load h z - (F.toFamily.incl h).adjoint y‖ ≤
      ‖1 - F.toFamily.J h‖ * ‖F.toFamily.load h z‖ +
        F.toFamily.boundConst * ‖y - F.toFamily.incl h (F.toFamily.load h z)‖
  /-- the exact-load projection converges at every admissible state -/
  tendsto_reading {y : PiLp 2 W} (hy : y ∈ F.A) :
    Tendsto (fun h => ‖y - F.toFamily.incl h (F.toFamily.load h (y - waveExt H y))‖) F.l (𝓝 0)
  /-- and its defect tends to `0` there -/
  tendsto_defect {y : PiLp 2 W} (hy : y ∈ F.A) :
    Tendsto (fun h => ‖F.toFamily.load h (y - waveExt H y) - (F.toFamily.incl h).adjoint y‖) F.l
      (𝓝 0)
  /-- the discrete generator is `Lₕ = 𝐝ₕ - 𝐝ₕ*` -/
  generator (h : κ) : (ofComplexCrime F).L h = F.toFamily.D h - (F.toFamily.D h).adjoint

/-- **The FEEC theorem for approximating families with variational crimes.** For every approximating
family `F` of discrete differential spaces of a Hilbert complex (`ApproxComplexCrime`: inner-product
defect `‖1 - iₕ* iₕ‖ → 0` and consistent approximation on the admissible states, the reading maps
need not be cochain maps): the approximating FEEC theorem on the core, the discrete generator
`𝐝ₕ - 𝐝ₕ*`, the fully discrete theorems for every time scheme and for leapfrog under the CFL
condition, the perturbed theorems for every bounded perturbation (dense core), exact preservation of
discrete constraints, and the Strang, residual and defect estimates with their limits. The
conforming windows give the zero-defect instance (`ConstrainedFEEC.toCrime`,
`ConformingFamily.Verdict.crime`); scheme (6.5) is an instance
(`Feec.Instances.EinsteinBianchiFEMCrown`). [HolstStern2012], §3; [BrennerThomee1979]; [Pazy1983],
§3.4 -/
theorem feec (F : ApproxComplexCrime H κ) : F.Verdict :=
  ⟨(approxFEEC_ofComplexCrime F).1, fun Θ => dissipFEEC_fullyDiscrete _ Θ,
    fun R _ hx h v _ _ hτ hc hc1 _ hw h0 _ hn =>
      (ofComplexCrime F).norm_S_sub_leapfrog_le R hx h v hτ hc hc1 hw h0 hn,
    fun hZ P => perturbFEEC _ hZ P,
    fun h Kh hKh _ hv t => (approxFEEC_ofComplexCrime F).2.2.1 h Kh hKh _ hv t,
    fun h Kh hKh hKK _ hv t => (approxFEEC_ofComplexCrime F).2.2.2.1 h Kh hKh hKK _ hv t,
    fun h y z w _ hε hres => (approxFEEC_ofComplexCrime F).2.2.2.2.1 h y z w _ hε hres,
    fun h y w _ hδ v => (approxFEEC_ofComplexCrime F).2.2.2.2.2.1 h y w _ hδ v,
    (approxFEEC_ofComplexCrime F).2.2.2.2.2.2.1,
    fun hy => (approxFEEC_ofComplexCrime F).2.2.2.2.2.2.2.1 _ hy,
    fun hy => (approxFEEC_ofComplexCrime F).2.2.2.2.2.2.2.2 _ hy,
    (approxFEEC_ofComplexCrime F).2.1⟩

end ApproxComplexCrime

end Crime

/-! ### The crown -/

section Crown

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α]
  {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*}

namespace ConformingFamily

/-- **The conforming window with a constraint**: the window `Vₕᵃ → ⋯ → Vₕ^{a+m-1}` of `F`
(`ConformingFamily.window`) with the closed constraint `K`, a constrained FEEC discretization of
the window `H.window a m`. -/
abbrev windowFEEC (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    ConstrainedFEEC (H.window a m) κ :=
  (F.window a m).withConstraint K hK

omit [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)] in
/-- The projections of the conforming window are bounded in the graph norm in every degree. -/
theorem isGraphBounded_windowFEEC (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    ∀ i, (F.windowFEEC a m K hK).IsGraphBounded i :=
  (F.window a m).isGraphBounded_toSubcomplexFamily

/-- **The conforming window as an approximating family with variational crimes**: the window
with the constraint `K` (`windowFEEC`) read as an approximating family of discrete differential
spaces with zero inner-product and cochain defects (`ConstrainedFEEC.toCrime`). -/
abbrev windowCrime (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    ApproxComplexCrime (H.window a m) κ :=
  (F.windowFEEC a m K hK).toCrime

/-- **The conclusions of the FEEC theorem** (`feec`) for a conforming family `F`: the static FEEC
theorem in every degree, and on every window with every closed constraint the semidiscrete wave
and heat FEEC theorems, the fully discrete ones, and the perturbed ones for every bounded
dissipative `B`. -/
structure Verdict (F : ConformingFamily H κ) : Prop where
  /-- the static FEEC theorem in every degree with finite-dimensional harmonic forms
  ([AFW2010], Thms 3.4–3.9) -/
  static (hcr : ∀ i, H.ClosedRangeAt i) (j : α) [FiniteDimensional 𝕜 (H.harmonic j)] :
    F.StaticVerdict j
  /-- the approximating FEEC theorem for the wave equation on every window with every closed
  constraint, hence the skew-adjoint and dissipative ones -/
  wave (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).toApprox.Verdict (F.windowFEEC a m K hK).toCore
  /-- the constrained FEEC theorem on every window with every closed constraint
  ([QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.17) -/
  constrained (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).Verdict
  /-- the heat FEEC theorem on every window with closed range, with every closed constraint -/
  heat (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) :
    (F.windowFEEC a m K hK).toHeat.Verdict
      ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK))
  /-- the fully discrete wave and heat FEEC theorems on every window with every closed
  constraint, for every time scheme, and leapfrog under the CFL condition -/
  full (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).FullVerdict
  /-- the perturbed FEEC theorems on every window with every closed constraint and every bounded
  dissipative `B`: the damped wave and perturbed heat equations ([Pazy1983], §3.1, §3.3, §3.4) -/
  perturbed (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (B : (PiLp 2 fun i : Fin m => V (a + i)) →L[𝕜] PiLp 2 fun i : Fin m => V (a + i))
    (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) : (F.windowFEEC a m K hK).PerturbedVerdict B hB
  /-- the zero-defect instance of the FEEC theorem for approximating families
  (`ApproxComplexCrime.feec`): every window with every closed constraint, read as an approximating
  family with zero defects (`windowCrime`; [HolstStern2012], §3) -/
  crime (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowCrime a m K hK).Verdict

/-- **The FEEC theorem.** For every conforming family `F` of a Hilbert complex on `ℕ` or `ℤ`:
the static FEEC theorem in every degree (closed range, finite-dimensional harmonic forms), and on
every window with every closed constraint the semidiscrete wave FEEC theorem (approximating and
constrained), the heat FEEC theorem (closed range of the window), the fully discrete theorems for every time scheme and for leapfrog under the CFL
condition, and the perturbed theorems for every bounded dissipative perturbation. [AFW2010],
Thms 3.4–3.9; [QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.17; [BrennerThomee1979];
[Pazy1983], §3.1, §3.3, §3.4 -/
theorem feec (F : ConformingFamily H κ) : F.Verdict :=
  ⟨fun hcr j _ => F.staticFEEC hcr j,
    fun a m K hK => approxFEEC _ (F.windowFEEC a m K hK).toCore,
    fun a m K hK => constrainedFEEC (F.windowFEEC a m K hK),
    fun a m K hK hcr => (F.windowFEEC a m K hK).heatFEEC hcr (F.isGraphBounded_windowFEEC a m K hK),
    fun a m K hK => constrainedFEEC_fullyDiscrete (F.windowFEEC a m K hK),
    fun a m K hK B hB => constrainedFEEC_perturbed (F.windowFEEC a m K hK) B hB,
    fun a m K hK => (F.windowCrime a m K hK).feec⟩

variable {ρ : Type*}

/-- **The rated conclusions of the FEEC theorem** (`feec_rated`) for a conforming family `F` with a
Jackson estimate `J`: those of the FEEC theorem, and the rates `hᵒʳᵈ⁽ˢ⁾` of the mixed method, of the
semidiscrete wave and heat equations and of the fully discrete schemes for `s`-regular data. -/
structure Verdict.Rated (F : ConformingFamily H κ) (J : F.Jackson ρ) : Prop
    extends F.Verdict where
  /-- the rate of the mixed method, with closed range in the degrees of the problem
  ([AFW2010], Thm 3.9) -/
  rate_static (s : ρ) {i j k : α} (hij : (ComplexShape.up α).Rel i j)
    (hjk : (ComplexShape.up α).Rel j k) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) :
    ∃ K : ℝ, ∀ {f : V j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ {L : ℝ}, 0 ≤ L →
    J.Reg s i L (H.domainIncl i σ) → J.Reg s j L (H.domainIncl j u) →
    J.Reg s j L (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))) →
    J.Reg s j L (p : V j) → ∀ h : κ,
    (F.V h).mixedError hij hjk f σ u p ≤ K * L * J.meshSize h ^ J.ord s
  /-- the rate `(1 + C_P)(1 + 2t) C L hᵒʳᵈ⁽ˢ⁾` of the semidiscrete wave equation on every window
  ([QuennevilleBelair2015], Thm 4.14) -/
  rate_wave (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) {T : ℝ} (s : ρ) {L : ℝ}
    (hL : 0 ≤ L) {x : PiLp 2 fun i : Fin m => V (a + i)}
    (hx : x ∈ (ConstrainedFEEC.RateClass.ofJackson (F.windowFEEC a m K hK) (J.window a m) T s
      hL).Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(H.window a m).waveGroup.S t x - (H.window a m).totalD.graphFst
        ((F.windowFEEC a m K hK).discrete h (waveLift (H.window a m)
          ⟨x, (ConstrainedFEEC.RateClass.ofJackson (F.windowFEEC a m K hK) (J.window a m) T s
            hL).mem_domain x hx⟩) t)‖ ≤
      (1 + ellipticConst (H.window a m)) * (1 + 2 * t) *
        ((ConstrainedFEEC.RateClass.ofJackson (F.windowFEEC a m K hK) (J.window a m) T s hL).C *
          (ConstrainedFEEC.RateClass.ofJackson (F.windowFEEC a m K hK) (J.window a m) T s
            hL).meshSize h ^
            (ConstrainedFEEC.RateClass.ofJackson (F.windowFEEC a m K hK) (J.window a m) T s hL).α *
          (ConstrainedFEEC.RateClass.ofJackson (F.windowFEEC a m K hK) (J.window a m) T s
            hL).classNorm x)
  /-- the rate `(2 + 3t) K L hᵒʳᵈ⁽ˢ⁾` of the semidiscrete heat equation on every window, `K` the
  constant of the static rate ([AFW2010], Thm 3.9 along the heat flow) -/
  rate_heat (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) (s : ρ) :
    ∃ C, 0 ≤ C ∧ ∀ {L : ℝ}, 0 ≤ L →
    ∀ {T : ℝ} {x : PiLp 2 fun i : Fin m => V (a + i)},
      x ∈ (-(H.window a m).hodgeLaplacian).sqDomain →
      (∀ t ∈ Icc 0 T, (F.windowFEEC a m K hK).toHeat.S t x ∈
        (F.windowFEEC a m K hK).heatReg hcr ((F.windowFEEC a m K hK).totalJackson (J.window a m))
          s L) → ∀ (h : κ), ∀ t ∈ Icc 0 T,
    ‖(F.windowFEEC a m K hK).toHeat.S t x - (F.windowFEEC a m K hK).toHeat.sol h
        ((F.windowFEEC a m K hK).ritzR h (x, DissipFEEC.genExt (-(H.window a m).hodgeLaplacian) x))
          t‖ ≤
      (2 + 3 * t) * C * L * J.meshSize h ^ J.ord s
  /-- the fully discrete rates on every window: the spatial rate plus `O(τᵖ)` along smooth
  comparisons, and plus `O(τ^{p/(p+2)})` for every Jackson datum -/
  rate_full (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).FullRate (J.window a m)

/-- **The FEEC theorem with rates.** For every conforming family `F` of a Hilbert complex on `ℕ`
or `ℤ` with a Jackson estimate `J`: the FEEC theorem (`feec`), and for `s`-regular data with
bound `L` the errors of the mixed method, of the semidiscrete wave and heat equations on every
window and of the fully discrete schemes are `O(L hᵒʳᵈ⁽ˢ⁾)`, plus `O(τᵖ)` for the fully discrete
ones along smooth comparisons and `O(τ^{p/(p+2)})` for every datum. [AFW2010], Thm 3.9; [QuennevilleBelair2015], Thm 4.14; [BrennerThomee1979] -/
theorem feec_rated (F : ConformingFamily H κ) (J : F.Jackson ρ) : Verdict.Rated F J :=
  ⟨F.feec, fun s _ _ _ hij hjk hj hk => F.rate J s hij hjk hj hk,
    fun a m K hK _ s _ hL _ hx h _ ht => (F.windowFEEC a m K hK).rate_le
      (ConstrainedFEEC.RateClass.ofJackson _ (J.window a m) _ s hL) hx h ht,
    fun a m K hK hcr s => (F.windowFEEC a m K hK).rate_heat hcr
      (F.isGraphBounded_windowFEEC a m K hK) _ s,
    fun a m K hK => constrainedFEEC_fullRate (F.windowFEEC a m K hK) (J.window a m)⟩

end ConformingFamily

end Crown

end Feec.HilbertComplex
