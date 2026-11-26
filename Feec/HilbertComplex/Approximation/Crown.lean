-- leantex: show = prose
module

public import Feec.HilbertComplex.Approximation.ApproxComplexCrime
public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.HilbertComplex.Approximation.HeatCrime
public import Feec.HilbertComplex.Approximation.HeatFEEC
public import Feec.HilbertComplex.Approximation.StaticCochain
public import Feec.HilbertComplex.Approximation.PerturbFEEC
public import Feec.HilbertComplex.Approximation.RationalScheme
public import Feec.HilbertComplex.Approximation.Reweight

/-!
# The FEEC theorem

The FEEC theorem collects the approximation theory of the library for every conforming family of a
Hilbert complex on `ℕ` or `ℤ`: static, semidiscrete and fully discrete, with constraints,
perturbations, rates and variational crimes.

## Main results

* `ConformingFamily.feec`: the FEEC theorem for conforming families.
* `ConformingFamily.feec_rated`: the same with the rates of a Jackson estimate.
* `ApproxComplexCrime.feec`: the FEEC theorem for approximating families with variational crimes.
* `constrainedFEEC_fullyDiscrete`: the fully discrete theorem for constrained discretizations.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric NormedSpace

@[expose] public noncomputable section

namespace Feec.HilbertComplex

/-! ### The fully discrete verdict -/

section Full

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  {κ : Type*}

/-- **The fully discrete verdict** of a constrained FEEC discretization `G`. -/
structure ConstrainedFEEC.FullVerdict (G : ConstrainedFEEC H κ) : Prop where
  /-- the fully discrete wave equation, for every time scheme -/
  wave (Θ : G.toApprox.TimeScheme) : Θ.Verdict G.toCore
  /-- the fully discrete heat equation, for every time scheme -/
  heat (hcr : ∀ i, H.ClosedRangeAt i) (hb : ∀ i, G.IsGraphBounded i)
    (Θ : G.toHeat.TimeScheme) : Θ.Verdict (G.heatCore hcr hb)
  /-- explicit leapfrog under the CFL condition `τ ‖Lₕ‖ ≤ c < 1` -/
  leapfrog {T : ℝ} (R : G.toApprox.RateClass T) {x : PiLp 2 W} (hx : x ∈ R.Data) (h : κ)
    (v : G.toApprox.X h) {τ c : ℝ} (hτ : 0 ≤ τ) (hc : τ * ‖G.toApprox.L h‖ ≤ c) (hc1 : c < 1)
    {w : ℕ → G.toApprox.X h} (hw : TimeStepping.IsLeapfrog (G.toApprox.L h) τ w) (h0 : w 0 = v)
    {n : ℕ} (hn : (n : ℝ) * τ ∈ Icc 0 T) :
    ‖G.toApprox.S (n * τ) x - G.toApprox.incl h (w n)‖ ≤
      (R.C + ‖G.toApprox.incl h‖ * R.C' * (n * τ)) * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖G.toApprox.incl h‖ * ‖R.p x h 0 - v‖ +
        ‖G.toApprox.incl h‖ * (√(1 + c) * ‖w 1 - exp ((τ : 𝕜) • G.toApprox.L h) v‖ / √(1 - c) +
          n * τ * τ ^ 2 * ‖(G.toApprox.L h ^ 3) v‖ / (3 * (1 - c)))
  /-- the Hermitian signed linear systems of Crank–Nicolson -/
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
  /-- the A-stable rational schemes for the exact wave equation -/
  exact_wave (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {x : PiLp 2 W} (hx : x ∈ DissipFEEC.iterDomain H.wave (p + 1)) :
    ‖(r.step H.wave τ ^ n) x - G.toApprox.S (n * τ) x‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p *
        ‖(DissipFEEC.genExt H.wave)^[p + 1] x‖
  /-- the same for the exact heat equation -/
  exact_heat (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {x : PiLp 2 W}
    (hx : x ∈ DissipFEEC.iterDomain (-H.hodgeLaplacian) (p + 1)) :
    ‖(r.step (-H.hodgeLaplacian) τ ^ n) x - G.toHeat.S (n * τ) x‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p *
        ‖(DissipFEEC.genExt (-H.hodgeLaplacian))^[p + 1] x‖
  /-- the same with every bounded perturbation -/
  exact_perturbed_wave (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K κ : ℝ, 0 ≤ K ∧ 0 ≤ κ ∧
      ∀ (B : PiLp 2 W →L[𝕜] PiLp 2 W) {τ : ℝ}, 0 < τ → ‖B‖ * τ ≤ c₀ → ∀ (n : ℕ) {x : PiLp 2 W},
        x ∈ DissipFEEC.iterDomain ((B : PiLp 2 W →ₗ[𝕜] PiLp 2 W) +ᵥ H.wave) (p + 1) →
        ‖(r.step ((B : PiLp 2 W →ₗ[𝕜] PiLp 2 W) +ᵥ H.wave) τ ^ n) x -
            (G.toApprox.isMDissipative.semigroup.perturb B).S (n * τ) x‖ ≤
          K * Real.exp (κ * ‖B‖ * (n * τ)) * (n * τ) * τ ^ p *
            ‖(DissipFEEC.genExt ((B : PiLp 2 W →ₗ[𝕜] PiLp 2 W) +ᵥ H.wave))^[p + 1] x‖
  /-- the same for the heat equation -/
  exact_perturbed_heat (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K κ : ℝ, 0 ≤ K ∧ 0 ≤ κ ∧
      ∀ (B : PiLp 2 W →L[𝕜] PiLp 2 W) {τ : ℝ}, 0 < τ → ‖B‖ * τ ≤ c₀ → ∀ (n : ℕ) {x : PiLp 2 W},
        x ∈ DissipFEEC.iterDomain ((B : PiLp 2 W →ₗ[𝕜] PiLp 2 W) +ᵥ -H.hodgeLaplacian) (p + 1) →
        ‖(r.step ((B : PiLp 2 W →ₗ[𝕜] PiLp 2 W) +ᵥ -H.hodgeLaplacian) τ ^ n) x -
            (G.toHeat.isMDissipative.semigroup.perturb B).S (n * τ) x‖ ≤
          K * Real.exp (κ * ‖B‖ * (n * τ)) * (n * τ) * τ ^ p *
            ‖(DissipFEEC.genExt ((B : PiLp 2 W →ₗ[𝕜] PiLp 2 W) +ᵥ -H.hodgeLaplacian))^[p + 1] x‖
  /-- the fully discrete FEEC theorem on Banach spaces for the wave discretization -/
  banach_wave : G.toApprox.toBanachFEEC.Verdict
  /-- the same for the heat discretization -/
  banach_heat : G.toHeat.toBanachFEEC.Verdict
  /-- the Brenner–Thomée temporal error of the A-stable rational schemes -/
  brennerThomee_wave (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (hp0 : 0 < p) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) (v : G.toApprox.X h)
    (n : ℕ) :
    ‖G.toApprox.sol h v (n * τ h) - (G.toApprox.rationalScheme r hr hp hp0 τ hτ).sol h v n‖ ≤
      ‖G.toApprox.incl h‖ * (r.sharpConst p * (n * τ h) * τ h ^ p * ‖(G.toApprox.L h ^ (p + 1)) v‖)
  /-- the same for the heat discretization -/
  brennerThomee_heat (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (hp0 : 0 < p) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) (h : κ) (v : G.toHeat.X h) (n
    : ℕ) :
    ‖G.toHeat.sol h v (n * τ h) - (G.toHeat.rationalScheme r hr hp hp0 τ hτ).sol h v n‖ ≤
      ‖G.toHeat.incl h‖ * (r.sharpConst p * (n * τ h) * τ h ^ p * ‖(G.toHeat.L h ^ (p + 1)) v‖)
  /-- the Brenner–Thomée error for the exact wave equation -/
  exact_brennerThomee_wave (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {x : PiLp 2 W}
    (hx : x ∈ DissipFEEC.iterDomain H.wave (p + 1)) :
    ‖(r.step H.wave τ ^ n) x - G.toApprox.S (n * τ) x‖ ≤
      r.sharpConst p * (n * τ) * τ ^ p * ‖(DissipFEEC.genExt H.wave)^[p + 1] x‖
  /-- the same for the exact heat equation -/
  exact_brennerThomee_heat (r : TimeStepping.RationalScheme) (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {x : PiLp 2 W}
    (hx : x ∈ DissipFEEC.iterDomain (-H.hodgeLaplacian) (p + 1)) :
    ‖(r.step (-H.hodgeLaplacian) τ ^ n) x - G.toHeat.S (n * τ) x‖ ≤
      r.sharpConst p * (n * τ) * τ ^ p * ‖(DissipFEEC.genExt (-H.hodgeLaplacian))^[p + 1] x‖

/-- **The fully discrete FEEC theorem for a constrained FEEC discretization**: every time scheme,
leapfrog, Crank–Nicolson and the A-stable rational schemes, also on Banach spaces. -/
theorem constrainedFEEC_fullyDiscrete (G : ConstrainedFEEC H κ) : G.FullVerdict :=
  ⟨fun Θ => dissipFEEC_fullyDiscrete G.toCore Θ,
    fun hcr hb Θ => dissipFEEC_fullyDiscrete (G.heatCore hcr hb) Θ,
    G.toApprox.norm_S_sub_leapfrog_le,
    fun hτ h _ b ε hε hMε hKε v => G.toApprox.crankNicolson_signed hτ h b ε hε hMε hKε v,
    fun r hr _ hp _ hτ n _ hx => G.toApprox.norm_step_pow_sub_S_le r hr hp hτ n hx,
    fun r hr _ hp _ hτ n _ hx => G.toHeat.norm_step_pow_sub_S_le r hr hp hτ n hx,
    fun r hr _ hp => G.toApprox.exists_norm_step_pow_sub_perturb_le r hr hp,
    fun r hr _ hp => G.toHeat.exists_norm_step_pow_sub_perturb_le r hr hp,
    TimeStepping.banachFEEC _, TimeStepping.banachFEEC _,
    fun r hr _ hp hp0 _ hτ h v n =>
      G.toApprox.norm_sol_sub_rationalScheme_sol_le r hr hp hp0 hτ h v n,
    fun r hr _ hp hp0 _ hτ h v n =>
      G.toHeat.norm_sol_sub_rationalScheme_sol_le r hr hp hp0 hτ h v n,
    fun r hr _ hp _ hτ n _ hx => G.toApprox.norm_step_pow_sub_S_le_brennerThomee r hr hp hτ n hx,
    fun r hr _ hp _ hτ n _ hx => G.toHeat.norm_step_pow_sub_S_le_brennerThomee r hr hp hτ n hx⟩

variable {ρ : Type*}

/-- **The wave rate class of a Jackson estimate**. -/
abbrev ConstrainedFEEC.jacksonWaveRateClass (G : ConstrainedFEEC H κ) (J : G.Jackson ρ) (T : ℝ)
    (s : ρ) {L : ℝ} (hL : 0 ≤ L) : G.toApprox.RateClass T :=
  (ConstrainedFEEC.RateClass.ofJackson G J T s hL).toApprox

/-- **The fully discrete rates of a Jackson estimate**: the spatial rate plus a temporal order. -/
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
  /-- the same for every datum, at the order `τₕ^{p/(p+2)}` -/
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
  /-- the same for every datum, at the order `τₕ^{p/(p+2)}` -/
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

/-! ### The FEEC theorem for approximating families with variational crimes -/

section Crime

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  {κ : Type*}

namespace ApproxComplexCrime

open ApproxFEEC

/-- **The conclusions of the FEEC theorem for approximating families** with variational crimes. -/
structure Verdict (F : ApproxComplexCrime H κ) : Prop where
  /-- the approximating FEEC theorem on the core -/
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
  /-- the perturbed FEEC theorem, when the core is dense -/
  perturbed (hZ : (ofComplexCrimeCore F).Data.topologicalClosure = ⊤)
    (P : (ofComplexCrime F).Perturbation) : P.Verdict (P.core (ofComplexCrimeCore F) hZ)
  /-- `Lₕ`-invariant subspaces are preserved -/
  invariant (h : κ) (Kh : Submodule 𝕜 (F.toFamily.X h)) (hKh : ∀ v ∈ Kh, F.toFamily.L h v ∈ Kh)
    {v : F.toFamily.X h} (hv : v ∈ Kh) (t : ℝ) : ((ofComplexCrime F).group h).S t v ∈ Kh
  /-- with residual `0` when read inside `K` -/
  residual_eq_zero (h : κ) (Kh : Submodule 𝕜 (F.toFamily.X h))
    (hKh : ∀ v ∈ Kh, F.toFamily.L h v ∈ Kh)
    (hKK : Kh.map (F.toFamily.incl h : F.toFamily.X h →ₗ[𝕜] PiLp 2 W) ≤ F.K)
    {v : F.toFamily.X h} (hv : v ∈ Kh) (t : ℝ) :
    infDist ((ofComplexCrime F).sol h v t) (F.K : Set (PiLp 2 W)) = 0
  /-- the Strang lemma -/
  strang (h : κ) (y z : PiLp 2 W) (w : F.toFamily.X h) {ε : ℝ} (hε : 0 ≤ ε)
    (hres : ∀ v, ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪z, F.toFamily.incl h v⟫_𝕜‖ ≤
      ε * (‖v‖ + ‖F.toFamily.D h v‖)) :
    ‖y - F.toFamily.incl h (F.toFamily.load h z)‖ ≤
      ‖y - F.toFamily.incl h w‖ + 8 * F.toFamily.boundConst * ε
  /-- the splitting of the residual -/
  residual_le (h : κ) (y : H.wave.domain) (w : F.toFamily.X h) {δ : ℝ}
    (hδ : ∀ v, ‖⟪F.toFamily.cochainDefect h y, v⟫_𝕜‖ ≤ δ * (‖v‖ + ‖F.toFamily.D h v‖))
    (v : F.toFamily.X h) :
    ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, F.toFamily.incl h v⟫_𝕜‖ ≤
      (‖(1 - F.toFamily.J h) w‖ + ‖(1 - F.toFamily.J h) (F.toFamily.D h w)‖ +
        F.toFamily.boundConst * (‖(y : PiLp 2 W) - F.toFamily.incl h w‖ +
          ‖H.totalD ⟨y, y.2.1⟩ - F.toFamily.incl h (F.toFamily.D h w)‖) + δ) *
        (‖v‖ + ‖F.toFamily.D h v‖)
  /-- the defect bound -/
  defect_le (h : κ) (y z : PiLp 2 W) :
    ‖F.toFamily.load h z - (F.toFamily.incl h).adjoint y‖ ≤
      ‖(1 - F.toFamily.J h) (F.toFamily.load h z)‖ +
        F.toFamily.boundConst * ‖y - F.toFamily.incl h (F.toFamily.load h z)‖
  /-- the exact-load projection converges at admissible states -/
  tendsto_reading {y : PiLp 2 W} (hy : y ∈ F.A) :
    Tendsto (fun h => ‖y - F.toFamily.incl h (F.toFamily.load h (y - waveExt H y))‖) F.l (𝓝 0)
  /-- and its defect tends to `0` -/
  tendsto_defect {y : PiLp 2 W} (hy : y ∈ F.A) :
    Tendsto (fun h => ‖F.toFamily.load h (y - waveExt H y) - (F.toFamily.incl h).adjoint y‖) F.l
      (𝓝 0)
  /-- the discrete generator is `Lₕ = 𝐝ₕ - 𝐝ₕ*` -/
  generator (h : κ) : (ofComplexCrime F).L h = F.toFamily.D h - (F.toFamily.D h).adjoint
  /-- the fully discrete FEEC theorem on Banach spaces -/
  banach : (ofComplexCrime F).toBanachFEEC.Verdict
  /-- the static FEEC theorem with crimes -/
  static (hcr : ∀ i, H.ClosedRangeAt i) {cP : ℝ} (hcP : 1 ≤ cP)
    (hP : F.toFamily.IsPoincare cP) : F.toFamily.StaticVerdict hcr cP F.l
  /-- the heat FEEC theorem with crimes -/
  heat (hcr : ∀ i, H.ClosedRangeAt i) {cP : ℝ} (hcP : 1 ≤ cP) (hP : F.toFamily.IsPoincare cP)
    {D : Set (PiLp 2 W)} (hD : Dense D) (hc : ∀ g ∈ D, F.toFamily.StaticConsistent hcr F.l g) :
    F.toHeat.Verdict
      (F.heatCore hcr hcP hP ((F.toFamily.staticFEEC hcr F.l hcP hP).converges hD hc))
  /-- the heat rate with crimes -/
  heat_rate (hcr : ∀ i, H.ClosedRangeAt i) {cP : ℝ} (hcP : 1 ≤ cP)
    (hP : F.toFamily.IsPoincare cP) {Reg : ℝ → Set (PiLp 2 W)} {m : κ → ℝ}
    (hm : ∀ h, 0 ≤ m h) {α K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ {L : ℝ} {f : PiLp 2 W}, 0 ≤ L → f ∈ Reg L → ∀ h,
      F.toFamily.staticError hcr h f ≤ K * L * m h ^ α)
    (hJ : ∀ h, F.toFamily.graphDefect h ≤ K * m h ^ α) {L : ℝ} (hL : 0 ≤ L) {T : ℝ}
    {x : PiLp 2 W} (hx : x ∈ (-H.hodgeLaplacian).sqDomain)
    (hreg : ∀ t ∈ Icc 0 T, F.toHeat.S t x ∈ H.heatReg Reg L) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖F.toHeat.S t x - F.toHeat.sol h (F.ritzR h (x, DissipFEEC.genExt (-H.hodgeLaplacian) x)) t‖ ≤
      (2 * K + F.toFamily.boundConst *
        ((3 * F.toFamily.boundConst + 16 * cP ^ 2 * F.toFamily.boundConst) * K) * t) *
          L * m h ^ α

/-- **The FEEC theorem for approximating families with variational crimes**: every approximating
family satisfies `ApproxComplexCrime.Verdict` ([HolstStern2012], §3; [BrennerThomee1979]). -/
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
    (approxFEEC_ofComplexCrime F).2.1, TimeStepping.banachFEEC _,
    fun hcr _ hcP hP => F.toFamily.staticFEEC hcr F.l hcP hP,
    fun hcr _ hcP hP _ _ _ => F.heatFEEC hcr hcP hP _,
    fun hcr _ hcP hP _ _ hm _ _ hK0 hK hJ _ hL _ _ hx hreg h _ ht =>
      F.rate_heat_of_static hcr hcP hP hm hK0 hK hJ hL hx hreg h ht⟩

end ApproxComplexCrime

end Crime

/-! ### The FEEC theorem for conforming families -/

section Crown

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α]
  {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*}

namespace ConformingFamily

/-- **The conforming window with a constraint**, as a constrained FEEC discretization. -/
abbrev windowFEEC (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    ConstrainedFEEC (H.window a m) κ :=
  (F.window a m).withConstraint K hK

omit [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)] in
theorem isGraphBounded_windowFEEC (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    ∀ i, (F.windowFEEC a m K hK).IsGraphBounded i :=
  (F.window a m).isGraphBounded_toSubcomplexFamily

/-- **The conforming window as an approximating family with variational crimes**, zero defects. -/
abbrev windowCrime (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    ApproxComplexCrime (H.window a m) κ :=
  (F.windowFEEC a m K hK).toCrime

theorem windowCrime_isPoincare (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) :
    ∃ cP, 1 ≤ cP ∧ (F.windowCrime a m K hK).toFamily.IsPoincare cP :=
  (F.windowFEEC a m K hK).toCrime_isPoincare (zero_le_one.trans (F.window a m).one_le_projBound)
    (F.window a m).norm_π_le hcr

/-- The total cochain projections of a conforming window, bounded in `W`. -/
abbrev windowCochainProj (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowCrime a m K hK).toFamily.CochainProj (F.window a m).projBound :=
  (F.windowFEEC a m K hK).cochainProj (zero_le_one.trans (F.window a m).one_le_projBound)
    (F.window a m).norm_π_le

theorem windowCrime_tendsto_incl_π (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (x : PiLp 2 fun i : Fin m => V (a + i)) :
    Tendsto (fun h => ‖x - (F.windowCrime a m K hK).toFamily.incl h
      ((F.windowCochainProj a m K hK).π h x)‖) (F.windowCrime a m K hK).l (𝓝 0) := by
  have e : ∀ h, ‖x - (F.windowCrime a m K hK).toFamily.incl h
      ((F.windowCochainProj a m K hK).π h x)‖ ≤ ∑ i, ‖((F.window a m).π h).π i (x i) - x i‖ :=
    fun h => by
      rw [norm_sub_rev]
      exact PiLp.norm_le_sum_norm _
  refine squeeze_zero (fun _ => norm_nonneg _) e ?_
  have hs := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
    tendsto_iff_norm_sub_tendsto_zero.1 ((F.window a m).tendsto_π i (x i))
  rw [Finset.sum_const_zero] at hs
  exact hs

theorem windowCrime_tendsto_staticError (F : ConformingFamily H κ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) (f : PiLp 2 fun i : Fin m => V (a + i)) :
    Tendsto (fun h => (F.windowCrime a m K hK).toFamily.staticError hcr h f)
      (F.windowCrime a m K hK).l (𝓝 0) := by
  obtain ⟨cP, hcP, hP⟩ := F.windowCrime_isPoincare a m K hK hcr
  set G := F.windowFEEC a m K hK
  have hJ : ∀ h, G.toComplex.toFamily.toCrimeFamily.J h = 1 := G.toCrime_J
  refine (G.toComplex.toFamily.isCochain_toCrimeFamily).tendsto_staticError hcr
    (F.windowCochainProj a m K hK) hP hcP ?_ (fun x _ => F.windowCrime_tendsto_incl_π a m K hK x) f
  exact tendsto_const_nhds.congr fun h =>
    ((G.toComplex.toFamily.toCrimeFamily.graphDefect_eq_zero_iff h).2 (hJ h)).symm

theorem windowCrime_eventually_bijective_cohomologyMap (F : ConformingFamily H κ) (a : α)
    (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)] :
    ∀ᶠ h in (F.windowCrime a m K hK).l,
      Function.Bijective ((F.windowCochainProj a m K hK).cohomologyMap h) :=
  ApproxComplexCrime.Family.IsCochain.eventually_bijective_cohomologyMap
    (F.windowFEEC a m K hK).toComplex.toFamily.isCochain_toCrimeFamily
    (F.windowCochainProj a m K hK) hcr fun q _ => F.windowCrime_tendsto_incl_π a m K hK q

/-- **The conclusions of the FEEC theorem** for a conforming family `F`. -/
structure Verdict (F : ConformingFamily H κ) : Prop where
  /-- the static FEEC theorem in every degree -/
  static (hcr : ∀ i, H.ClosedRangeAt i) (j : α) [FiniteDimensional 𝕜 (H.harmonic j)] :
    F.StaticVerdict j
  /-- the approximating FEEC theorem on every window -/
  wave (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).toApprox.Verdict (F.windowFEEC a m K hK).toCore
  /-- the constrained FEEC theorem on every window -/
  constrained (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).Verdict
  /-- the heat FEEC theorem on every window with closed range -/
  heat (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) :
    (F.windowFEEC a m K hK).toHeat.Verdict
      ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK))
  /-- the fully discrete FEEC theorems on every window -/
  full (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).FullVerdict
  /-- the perturbed FEEC theorems on every window, for every bounded dissipative `B` -/
  perturbed (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (B : (PiLp 2 fun i : Fin m => V (a + i)) →L[𝕜] PiLp 2 fun i : Fin m => V (a + i))
    (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) : (F.windowFEEC a m K hK).PerturbedVerdict B hB
  /-- the FEEC theorem with crimes on every window, with zero defects -/
  crime (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowCrime a m K hK).Verdict
  /-- the static theory with crimes on every window with closed range -/
  crime_static (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) :
    (∃ cP, 1 ≤ cP ∧ (F.windowCrime a m K hK).toFamily.IsPoincare cP) ∧
      ∀ f, Tendsto (fun h => (F.windowCrime a m K hK).toFamily.staticError hcr h f)
        (F.windowCrime a m K hK).l (𝓝 0)
  /-- the cohomology with crimes on every window with closed range -/
  crime_cohomology (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)] :
    ∀ᶠ h in (F.windowCrime a m K hK).l,
      Function.Bijective ((F.windowCochainProj a m K hK).cohomologyMap h)

/-- **The FEEC theorem**: every conforming family of a Hilbert complex on `ℕ` or `ℤ` satisfies
`ConformingFamily.Verdict` ([AFW2010], Thms 3.4–3.9; [QuennevilleBelair2015], Thm 4.14). -/
theorem feec (F : ConformingFamily H κ) : F.Verdict :=
  ⟨fun hcr j _ => F.staticFEEC hcr j,
    fun a m K hK => approxFEEC _ (F.windowFEEC a m K hK).toCore,
    fun a m K hK => constrainedFEEC (F.windowFEEC a m K hK),
    fun a m K hK hcr => (F.windowFEEC a m K hK).heatFEEC hcr (F.isGraphBounded_windowFEEC a m K hK),
    fun a m K hK => constrainedFEEC_fullyDiscrete (F.windowFEEC a m K hK),
    fun a m K hK B hB => constrainedFEEC_perturbed (F.windowFEEC a m K hK) B hB,
    fun a m K hK => (F.windowCrime a m K hK).feec,
    fun a m K hK hcr => ⟨F.windowCrime_isPoincare a m K hK hcr,
      F.windowCrime_tendsto_staticError a m K hK hcr⟩,
    fun a m K hK hcr _ => F.windowCrime_eventually_bijective_cohomologyMap a m K hK hcr⟩

variable {ρ : Type*}

theorem windowCrime_rate_static (F : ConformingFamily H κ) (J : F.Jackson ρ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) (s : ρ) :
    ∃ C, 0 ≤ C ∧ ∀ {L : ℝ} {f : PiLp 2 fun i : Fin m => V (a + i)}, 0 ≤ L →
      (F.windowFEEC a m K hK).RegMixed hcr ((F.windowFEEC a m K hK).totalJackson (J.window a m))
        s L f → ∀ h, (F.windowCrime a m K hK).toFamily.staticError hcr h f ≤
          C * L * J.meshSize h ^ J.ord s := by
  obtain ⟨cP, hcP, hP⟩ := F.windowCrime_isPoincare a m K hK hcr
  set G := F.windowFEEC a m K hK
  set S := (F.windowCrime a m K hK).toFamily
  set JT := G.totalJackson (J.window a m)
  have hB := JT.B_nonneg s ()
  have hi : S.IsCochain := G.toComplex.toFamily.isCochain_toCrimeFamily
  have hCπ := zero_le_one.trans (F.window a m).one_le_projBound
  refine ⟨S.cochainRateConst (F.window a m).projBound cP * (2 * JT.B s ()),
    mul_nonneg (S.cochainRateConst_nonneg hCπ cP) (by positivity), fun {L f} hL hf h => ?_⟩
  set ε := 2 * JT.B s () * (L * J.meshSize h ^ J.ord s)
  -- the total Jackson estimate in the language of crimes
  have happ : ∀ x, (hx : JT.Reg s () L x) → ∃ v, ‖x - S.incl h v‖ +
      ‖(H.window a m).totalD ⟨x, hx.1⟩ - S.incl h (S.D h v)‖ ≤ ε := fun x hx => by
    obtain ⟨w, hw, h1, h2⟩ := JT.jackson s h () x hL hx
    obtain ⟨v, hv⟩ := G.toXh_surjective h ⟨w, hw⟩
    have hvw : G.toFamily.inclL h v = w := congrArg Subtype.val hv
    have hD : S.incl h (S.D h v) = (H.window a m).totalD ⟨w, hvw ▸ G.toFamily.inclL_mem h v⟩ := by
      change G.toFamily.inclL h (G.toFamily.D h v) = _
      rw [G.toFamily.inclL_D]
      congr 1
      exact Subtype.ext hvw
    have hd : (H.window a m).totalD ⟨x, hx.1⟩ - S.incl h (S.D h v) =
        (H.window a m).total.d () () ⟨x - w, Submodule.sub_mem _ hx.1
          (hvw ▸ G.toFamily.inclL_mem h v)⟩ := by
      rw [hD, ← LinearPMap.map_sub]; rfl
    refine ⟨v, ?_⟩
    rw [hd, show S.incl h v = w from hvw]
    have h1' : ‖x - w‖ ≤ JT.B s () * (L * J.meshSize h ^ J.ord s) := h1
    have h2' : ‖(H.window a m).total.d () () ⟨x - w, Submodule.sub_mem _ hx.1
        (hvw ▸ G.toFamily.inclL_mem h v)⟩‖ ≤ JT.B s () * (L * J.meshSize h ^ J.ord s) := h2 () hx.1
    change _ ≤ 2 * JT.B s () * (L * J.meshSize h ^ J.ord s)
    linarith
  set X := (H.window a m).totalMixedSolution hcr f
  have hcyc : ∀ x, (hx : JT.Reg s () L x) → x ∈ (H.window a m).total.cycles () →
      ∃ v, ‖x - S.incl h v‖ + ‖S.incl h (S.D h v)‖ ≤ ε := fun x hx hz => by
    obtain ⟨v, hv⟩ := happ x hx
    obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hz
    refine ⟨v, ?_⟩
    rwa [show (H.window a m).totalD ⟨(y : PiLp 2 fun i : Fin m => V (a + i)), hx.1⟩ = 0 from hy,
      zero_sub, norm_neg] at hv
  have hb : ((H.window a m).total.cycles ()).starProjection ((H.window a m).greenOp hcr f) =
      (H.window a m).total.domainIncl () ((H.window a m).total.boundaryPart ()
        ((H.window a m).total.domainIncl () X.snd.fst)) := by
    rw [HilbertComplex.boundaryPart, domainIncl_cyclesToDomainSpace]
    exact (H.window a m).total.starProjection_cycles_eq_of_mem_orthogonal ()
      ((H.window a m).greenOp_mem_orthogonal_harmonic hcr f)
  have hJ : S.graphDefect h * ‖X‖ ≤ ε := by
    rw [(S.graphDefect_eq_zero_iff h).2 (G.toCrime_J h), zero_mul]
    have := Real.rpow_nonneg (J.meshSize_nonneg h) (J.ord s)
    positivity
  refine (hi.staticError_le_of_approx hcr (F.windowCochainProj a m K hK) hP hcP h f
    (happ _ hf.1) (happ _ hf.2.1)
    (hcyc _ hf.2.2.2 ((H.window a m).total.harmonic_le_cycles () X.snd.snd.2))
    (by rw [hb]; exact hcyc _ hf.2.2.1 ((H.window a m).total.closure_boundaries_le_cycles ()
      (Submodule.starProjection_apply_mem _ _))) hJ).trans
    (le_of_eq ?_)
  ring

theorem windowCrime_rate_heat (F : ConformingFamily H κ) (J : F.Jackson ρ) (a : α) (m : ℕ)
    (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) (s : ρ) :
    ∃ cP C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 0 ≤ L → ∀ {T : ℝ} {x : PiLp 2 fun i : Fin m => V (a + i)},
      x ∈ (-(H.window a m).hodgeLaplacian).sqDomain →
      (∀ t ∈ Icc 0 T, (F.windowCrime a m K hK).toHeat.S t x ∈ (H.window a m).heatReg
        (fun L => {f | (F.windowFEEC a m K hK).RegMixed hcr
          ((F.windowFEEC a m K hK).totalJackson (J.window a m)) s L f}) L) →
      ∀ (h : κ), ∀ t ∈ Icc 0 T,
      ‖(F.windowCrime a m K hK).toHeat.S t x - (F.windowCrime a m K hK).toHeat.sol h
          ((F.windowCrime a m K hK).ritzR h
            (x, DissipFEEC.genExt (-(H.window a m).hodgeLaplacian) x)) t‖ ≤
        (2 * C + (F.windowCrime a m K hK).toFamily.boundConst *
          ((3 * (F.windowCrime a m K hK).toFamily.boundConst +
            16 * cP ^ 2 * (F.windowCrime a m K hK).toFamily.boundConst) * C) * t) *
          L * J.meshSize h ^ J.ord s := by
  obtain ⟨cP, hcP, hP⟩ := F.windowCrime_isPoincare a m K hK hcr
  obtain ⟨C, hC0, hC⟩ := F.windowCrime_rate_static J a m K hK hcr s
  refine ⟨cP, C, hC0, fun {L} hL {T x} hx hreg h t ht =>
    (F.windowCrime a m K hK).rate_heat_of_static hcr hcP hP J.meshSize_nonneg hC0
      (fun hL' hf h => hC hL' hf h) (fun h => ?_) hL hx hreg h ht⟩
  rw [((F.windowCrime a m K hK).toFamily.graphDefect_eq_zero_iff h).2
    ((F.windowFEEC a m K hK).toCrime_J h)]
  exact mul_nonneg hC0 (Real.rpow_nonneg (J.meshSize_nonneg h) _)

/-- **The rated conclusions of the FEEC theorem** for `F` with a Jackson estimate `J`. -/
structure Verdict.Rated (F : ConformingFamily H κ) (J : F.Jackson ρ) : Prop
    extends F.Verdict where
  /-- the rate of the mixed method -/
  rate_static (s : ρ) {i j k : α} (hij : (ComplexShape.up α).Rel i j)
    (hjk : (ComplexShape.up α).Rel j k) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) :
    ∃ K : ℝ, ∀ {f : V j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ {L : ℝ}, 0 ≤ L →
    J.Reg s i L (H.domainIncl i σ) → J.Reg s j L (H.domainIncl j u) →
    J.Reg s j L (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))) →
    J.Reg s j L (p : V j) → ∀ h : κ,
    (F.V h).mixedError hij hjk f σ u p ≤ K * L * J.meshSize h ^ J.ord s
  /-- the rate of the semidiscrete wave equation on every window -/
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
  /-- the rate of the semidiscrete heat equation on every window -/
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
  /-- the fully discrete rates on every window -/
  rate_full (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) :
    (F.windowFEEC a m K hK).FullRate (J.window a m)
  /-- the static rate with crimes on every window -/
  rate_crime_static (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) (s : ρ) :
    ∃ C, 0 ≤ C ∧ ∀ {L : ℝ} {f : PiLp 2 fun i : Fin m => V (a + i)}, 0 ≤ L →
      (F.windowFEEC a m K hK).RegMixed hcr ((F.windowFEEC a m K hK).totalJackson (J.window a m))
        s L f → ∀ h, (F.windowCrime a m K hK).toFamily.staticError hcr h f ≤
          C * L * J.meshSize h ^ J.ord s
  /-- the heat rate with crimes on every window -/
  rate_crime_heat (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) (s : ρ) :
    ∃ cP C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 0 ≤ L → ∀ {T : ℝ} {x : PiLp 2 fun i : Fin m => V (a + i)},
      x ∈ (-(H.window a m).hodgeLaplacian).sqDomain →
      (∀ t ∈ Icc 0 T, (F.windowCrime a m K hK).toHeat.S t x ∈ (H.window a m).heatReg
        (fun L => {f | (F.windowFEEC a m K hK).RegMixed hcr
          ((F.windowFEEC a m K hK).totalJackson (J.window a m)) s L f}) L) →
      ∀ (h : κ), ∀ t ∈ Icc 0 T,
      ‖(F.windowCrime a m K hK).toHeat.S t x - (F.windowCrime a m K hK).toHeat.sol h
          ((F.windowCrime a m K hK).ritzR h
            (x, DissipFEEC.genExt (-(H.window a m).hodgeLaplacian) x)) t‖ ≤
        (2 * C + (F.windowCrime a m K hK).toFamily.boundConst *
          ((3 * (F.windowCrime a m K hK).toFamily.boundConst +
            16 * cP ^ 2 * (F.windowCrime a m K hK).toFamily.boundConst) * C) * t) *
          L * J.meshSize h ^ J.ord s

/-- **The FEEC theorem with rates**: every conforming family with a Jackson estimate satisfies
`ConformingFamily.Verdict.Rated` ([AFW2010], Thm 3.9; [QuennevilleBelair2015], Thm 4.14). -/
theorem feec_rated (F : ConformingFamily H κ) (J : F.Jackson ρ) : Verdict.Rated F J :=
  ⟨F.feec, fun s _ _ _ hij hjk hj hk => F.rate J s hij hjk hj hk,
    fun a m K hK _ s _ hL _ hx h _ ht => (F.windowFEEC a m K hK).rate_le
      (ConstrainedFEEC.RateClass.ofJackson _ (J.window a m) _ s hL) hx h ht,
    fun a m K hK hcr s => (F.windowFEEC a m K hK).rate_heat hcr
      (F.isGraphBounded_windowFEEC a m K hK) _ s,
    fun a m K hK => constrainedFEEC_fullRate (F.windowFEEC a m K hK) (J.window a m),
    fun a m K hK hcr s => F.windowCrime_rate_static J a m K hK hcr s,
    fun a m K hK hcr s => F.windowCrime_rate_heat J a m K hK hcr s⟩

end ConformingFamily

end Crown

end Feec.HilbertComplex
