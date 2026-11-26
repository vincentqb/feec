module

public import Feec.HilbertComplex.Approximation.RationalScheme
public import Feec.Instances.Corollaries
public import Feec.TimeStepping.RationalHillePhillipsReal

/-!
# Rational and Runge–Kutta time stepping in the FEEC theorem

Every A-stable rational scheme of order `p ≥ 1`, in particular every A-stable Runge–Kutta method,
satisfies the fully discrete FEEC theorem; this file also bounds the errors of the Gauss–Legendre,
Radau IIA, SDIRK and Crank–Nicolson methods on bounded semigroups of Banach spaces.

## Main results

* `full_rationalScheme`: every A-stable rational scheme of order `p ≥ 1` in the FEEC theorem.
* `full_brennerThomee`: temporal errors with Brenner–Thomée's constants.
* `banach_sharp_of_resolvent`: Gauss–Legendre, Radau IIA and SDIRK at the rate `τᵖ` on every
  bounded semigroup of a Banach space.

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.RungeKutta

open Feec.HilbertComplex Feec.TimeStepping Feec.Instances.Corollaries

/-! ### For every conforming family -/

section Family

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α]
  {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*} (F : ConformingFamily H κ)

/-- **Every A-stable rational scheme of order `p ≥ 1` in the FEEC theorem**: the fully discrete
wave verdict on every window, and the heat verdict with closed ranges. [BrennerThomee1979] -/
theorem full_rationalScheme (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) {r : RationalScheme}
    (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) (hp0 : 0 < p) {τ : κ → ℝ}
    (hτ : ∀ h, 0 < τ h) :
    ((F.windowFEEC a m K hK).toApprox.rationalScheme r hr hp hp0 τ hτ).Verdict
        (F.windowFEEC a m K hK).toCore ∧
      ∀ (hcr : ∀ i, (H.window a m).ClosedRangeAt i),
        ((F.windowFEEC a m K hK).toHeat.rationalScheme r hr hp hp0 τ hτ).Verdict
          ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK)) :=
  ⟨(F.feec.full a m K hK).wave _,
    fun hcr => (F.feec.full a m K hK).heat hcr (F.isGraphBounded_windowFEEC a m K hK) _⟩

/-- **Maxwell's equations with the two-stage Gauss–Legendre method**: the fully discrete verdict,
exact energy conservation and Gauss-law residuals tending to `0`. [HairerWanner1996], §IV.5 -/
theorem maxwell_gaussLegendre2 (a : α) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) :
    ((Maxwell.feec F a).toApprox.gaussLegendre2 τ hτ).Verdict (Maxwell.feec F a).toCore ∧
      (∀ h v k, ‖(((Maxwell.feec F a).toApprox.gaussLegendre2 τ hτ).P h ^ k) v‖ = ‖v‖) ∧
      ∀ {x} (_ : x ∈ Maxwell.windowGauss H a) {v : ∀ h, (Maxwell.feec F a).toApprox.X h},
        (Maxwell.feec F a).toApprox.Converges v x → Tendsto τ (Maxwell.feec F a).toApprox.l (𝓝 0) →
        ∀ T {ε : ℝ}, 0 < ε → ∀ᶠ h in (Maxwell.feec F a).toApprox.l, ∀ n : ℕ,
          (n : ℝ) * τ h ∈ Icc 0 T → infDist
            (((Maxwell.feec F a).toApprox.gaussLegendre2 τ hτ).sol h (v h) n)
            (Maxwell.windowGauss H a) < ε := by
  have V := (F.feec.full a 3 _ _).wave ((Maxwell.feec F a).toApprox.gaussLegendre2 τ hτ)
  have hK := (V.isReducing_iff.1 (Maxwell.isReducing_windowGauss H a)).1
  exact ⟨V, SkewFEEC.norm_rationalScheme_pow_apply _
      RationalScheme.isSymmetric_gaussLegendre2 _ _ hτ,
    fun hx _ hv hτ0 T _ hε =>
      V.residual_tendsto_iterates hK hx ((Maxwell.feec F a).mem_toCore_closure _) hv hτ0 T hε⟩

/-- **The Hodge heat equation with the Radau IIA and SDIRK methods** on every window with closed
ranges: the fully discrete verdicts. [HairerWanner1996], §IV.5, §IV.6 -/
theorem heat_radauIIA2 (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) :
    ((F.windowFEEC a m K hK).toHeat.radauIIA2 τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK)) ∧
      ((F.windowFEEC a m K hK).toHeat.sdirk2 τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK)) :=
  ⟨(F.feec.full a m K hK).heat hcr (F.isGraphBounded_windowFEEC a m K hK) _,
    (F.feec.full a m K hK).heat hcr (F.isGraphBounded_windowFEEC a m K hK) _⟩

/-- **Gauss–Legendre, Radau IIA and SDIRK with Brenner–Thomée's constants in the FEEC theorem**:
temporal errors `‖ιₕ‖ C tₙ τₕᵖ ‖Lₕ^{p+1} v‖` with `C` independent of `h`. [BrennerThomee1979] -/
theorem full_brennerThomee (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i)))) {τ : κ → ℝ}
    (hτ : ∀ h, 0 < τ h) :
    (∀ h v (n : ℕ), ‖(F.windowFEEC a m K hK).toApprox.sol h v (n * τ h) -
        ((F.windowFEEC a m K hK).toApprox.gaussLegendre2 τ hτ).sol h v n‖ ≤
      ‖(F.windowFEEC a m K hK).toApprox.incl h‖ * (RationalScheme.gaussLegendre2.sharpConst 4 *
        (n * τ h) * τ h ^ 4 * ‖((F.windowFEEC a m K hK).toApprox.L h ^ (4 + 1)) v‖)) ∧
    (∀ h v (n : ℕ), ‖(F.windowFEEC a m K hK).toHeat.sol h v (n * τ h) -
        ((F.windowFEEC a m K hK).toHeat.radauIIA2 τ hτ).sol h v n‖ ≤
      ‖(F.windowFEEC a m K hK).toHeat.incl h‖ * (RationalScheme.radauIIA2.sharpConst 3 *
        (n * τ h) * τ h ^ 3 * ‖((F.windowFEEC a m K hK).toHeat.L h ^ (3 + 1)) v‖)) ∧
    (∀ h v (n : ℕ), ‖(F.windowFEEC a m K hK).toHeat.sol h v (n * τ h) -
        ((F.windowFEEC a m K hK).toHeat.sdirk2 τ hτ).sol h v n‖ ≤
      ‖(F.windowFEEC a m K hK).toHeat.incl h‖ * (RationalScheme.sdirk2.sharpConst 2 *
        (n * τ h) * τ h ^ 2 * ‖((F.windowFEEC a m K hK).toHeat.L h ^ (2 + 1)) v‖)) :=
  ⟨(F.feec.full a m K hK).brennerThomee_wave _ _ _ _ hτ,
    (F.feec.full a m K hK).brennerThomee_heat _ _ _ _ hτ,
    (F.feec.full a m K hK).brennerThomee_heat _ _ _ _ hτ⟩

end Family

/-! ### Bounded semigroups on Banach spaces -/

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

/-- **Radau IIA and SDIRK on every bounded semigroup of a real or complex Banach space**: error
bounds of order `τᵖ` with a factor `1 + C √n`. [BrennerThomee1979]; [HairerWanner1996], §IV.5 -/
theorem banach_radauIIA2_of_resolvent {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    (G : C0Semigroup 𝕜 F) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M) {τ : ℝ} (hτ : 0 < τ)
    {R : F →L[𝕜] F} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ)
    {u : ℕ → F} :
    ((∀ j < 3 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.radauIIA2.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
        M * (1 + RationalScheme.radauIIA2.stabilityConst * √n) *
          (M * (RationalScheme.radauIIA2.remainder 3).hpMeasure.variation +
            M / (3 + 1).factorial) * M * (n * τ) * τ ^ 3 * ‖u (3 + 1)‖) ∧
    ((∀ j < 2 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.sdirk2.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
        M * (1 + RationalScheme.sdirk2.stabilityConst * √n) *
          (M * (RationalScheme.sdirk2.remainder 2).hpMeasure.variation +
            M / (2 + 1).factorial) * M * (n * τ) * τ ^ 2 * ‖u (2 + 1)‖) :=
  ⟨RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent G hM
      RationalScheme.isLStable_radauIIA2.isStronglyAStable RationalScheme.hasOrder_radauIIA2 hτ hR
      n,
    RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent G hM
      RationalScheme.isLStable_sdirk2.isStronglyAStable RationalScheme.hasOrder_sdirk2 hτ hR n⟩

theorem banach_radauIIA2 {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E} :
    ((∀ j < 3 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.radauIIA2.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) -
          G.S (n * τ) (u 0)‖ ≤
        M * (1 + RationalScheme.radauIIA2.stabilityConst * √n) *
          (M * (RationalScheme.radauIIA2.remainder 3).hpMeasure.variation +
            M / (3 + 1).factorial) * M * (n * τ) * τ ^ 3 * ‖u (3 + 1)‖) ∧
    ((∀ j < 2 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.sdirk2.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) -
          G.S (n * τ) (u 0)‖ ≤
        M * (1 + RationalScheme.sdirk2.stabilityConst * √n) *
          (M * (RationalScheme.sdirk2.remainder 2).hpMeasure.variation +
            M / (2 + 1).factorial) * M * (n * τ) * τ ^ 2 * ‖u (2 + 1)‖) :=
  banach_radauIIA2_of_resolvent G hM hτ (fun _ _ h => G.laplaceResolvent_apply_sub hM hτ.le h) n

/-- **Crank–Nicolson on every bounded semigroup of a real or complex Banach space**: not strongly
A-stable, with error bounds of order `τ²` with a factor `1 + C √n`. [BrennerThomee1979] -/
theorem banach_implicitMidpoint_of_resolvent {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    (G : C0Semigroup 𝕜 F) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M) {τ : ℝ} (hτ : 0 < τ)
    {R : F →L[𝕜] F} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ)
    {u : ℕ → F} :
    ¬ RationalScheme.implicitMidpoint.IsStronglyAStable ∧
    ‖RationalScheme.implicitMidpoint.resolventStep R ^ n‖ ≤
      M * (1 + RationalScheme.implicitMidpoint.sqrtConst * √n) ∧
    ((∀ j < 2 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.implicitMidpoint.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
        M * (1 + RationalScheme.implicitMidpoint.sqrtConst * √n) *
          (M * (RationalScheme.implicitMidpoint.remainder 2).hpMeasure.variation +
            M / (2 + 1).factorial) * M * (n * τ) * τ ^ 2 * ‖u (2 + 1)‖) :=
  RationalScheme.isSymmetric_implicitMidpoint.norm_resolventStep_pow_sub_S_le_of_resolvent G hM
    RationalScheme.hasOrder_implicitMidpoint hτ hR n

theorem banach_implicitMidpoint {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E} :
    ¬ RationalScheme.implicitMidpoint.IsStronglyAStable ∧
    ‖RationalScheme.implicitMidpoint.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n‖ ≤
      M * (1 + RationalScheme.implicitMidpoint.sqrtConst * √n) ∧
    ((∀ j < 2 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.implicitMidpoint.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) -
          G.S (n * τ) (u 0)‖ ≤
        M * (1 + RationalScheme.implicitMidpoint.sqrtConst * √n) *
          (M * (RationalScheme.implicitMidpoint.remainder 2).hpMeasure.variation +
            M / (2 + 1).factorial) * M * (n * τ) * τ ^ 2 * ‖u (2 + 1)‖) :=
  banach_implicitMidpoint_of_resolvent G hM hτ
    (fun _ _ h => G.laplaceResolvent_apply_sub hM hτ.le h) n

/-- **Gauss–Legendre on every bounded semigroup of a real or complex Banach space**: not strongly
A-stable, with error bounds of order `τ⁴` with a factor `1 + C √n`. [BrennerThomee1979] -/
theorem banach_gaussLegendre2_of_resolvent {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    (G : C0Semigroup 𝕜 F) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M) {τ : ℝ} (hτ : 0 < τ)
    {R : F →L[𝕜] F} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ)
    {u : ℕ → F} :
    ¬ RationalScheme.gaussLegendre2.IsStronglyAStable ∧
    ‖RationalScheme.gaussLegendre2.resolventStep R ^ n‖ ≤
      M * (1 + RationalScheme.gaussLegendre2.sqrtConst * √n) ∧
    ((∀ j < 4 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.gaussLegendre2.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
        M * (1 + RationalScheme.gaussLegendre2.sqrtConst * √n) *
          (M * (RationalScheme.gaussLegendre2.remainder 4).hpMeasure.variation +
            M / (4 + 1).factorial) * M * (n * τ) * τ ^ 4 * ‖u (4 + 1)‖) :=
  RationalScheme.isSymmetric_gaussLegendre2.norm_resolventStep_pow_sub_S_le_of_resolvent G hM
    RationalScheme.hasOrder_gaussLegendre2 hτ hR n

theorem banach_gaussLegendre2 {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E} :
    ¬ RationalScheme.gaussLegendre2.IsStronglyAStable ∧
    ‖RationalScheme.gaussLegendre2.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n‖ ≤
      M * (1 + RationalScheme.gaussLegendre2.sqrtConst * √n) ∧
    ((∀ j < 4 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.gaussLegendre2.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) -
          G.S (n * τ) (u 0)‖ ≤
        M * (1 + RationalScheme.gaussLegendre2.sqrtConst * √n) *
          (M * (RationalScheme.gaussLegendre2.remainder 4).hpMeasure.variation +
            M / (4 + 1).factorial) * M * (n * τ) * τ ^ 4 * ‖u (4 + 1)‖) :=
  banach_gaussLegendre2_of_resolvent G hM hτ
    (fun _ _ h => G.laplaceResolvent_apply_sub hM hτ.le h) n

/-- **Gauss–Legendre, Radau IIA and SDIRK at the rate `τᵖ` on every bounded semigroup of a real or
complex Banach space.** [BrennerThomee1979]; [HairerWanner1996], §IV.5, §IV.6 -/
theorem banach_sharp_of_resolvent {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    (G : C0Semigroup 𝕜 F) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M) {τ : ℝ} (hτ : 0 < τ)
    {R : F →L[𝕜] F} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ)
    {u : ℕ → F} :
    ((∀ j < 4 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.gaussLegendre2.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
        RationalScheme.gaussLegendre2.sharpConst 4 * M * (n * τ) * τ ^ 4 * ‖u (4 + 1)‖) ∧
    ((∀ j < 3 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.radauIIA2.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
        RationalScheme.radauIIA2.sharpConst 3 * M * (n * τ) * τ ^ 3 * ‖u (3 + 1)‖) ∧
    ((∀ j < 2 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.sdirk2.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
        RationalScheme.sdirk2.sharpConst 2 * M * (n * τ) * τ ^ 2 * ‖u (2 + 1)‖) :=
  ⟨RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent G hM
      RationalScheme.isSymmetric_gaussLegendre2.isAStable RationalScheme.hasOrder_gaussLegendre2
      hτ hR n,
    RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent G hM
      RationalScheme.isAStable_radauIIA2 RationalScheme.hasOrder_radauIIA2 hτ hR n,
    RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent G hM
      RationalScheme.isAStable_sdirk2 RationalScheme.hasOrder_sdirk2 hτ hR n⟩

theorem banach_sharp {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E} :
    ((∀ j < 4 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.gaussLegendre2.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) -
          G.S (n * τ) (u 0)‖ ≤
        RationalScheme.gaussLegendre2.sharpConst 4 * M * (n * τ) * τ ^ 4 * ‖u (4 + 1)‖) ∧
    ((∀ j < 3 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.radauIIA2.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) -
          G.S (n * τ) (u 0)‖ ≤
        RationalScheme.radauIIA2.sharpConst 3 * M * (n * τ) * τ ^ 3 * ‖u (3 + 1)‖) ∧
    ((∀ j < 2 + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(RationalScheme.sdirk2.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) -
          G.S (n * τ) (u 0)‖ ≤
        RationalScheme.sdirk2.sharpConst 2 * M * (n * τ) * τ ^ 2 * ‖u (2 + 1)‖) :=
  banach_sharp_of_resolvent G hM hτ (fun _ _ h => G.laplaceResolvent_apply_sub hM hτ.le h) n

end Banach

/-! ### The cube -/

namespace Cube.FEM

open Feec.Models.Cube.FEM Feec.FiniteElement

variable (n : ℕ) [NeZero n]

/-- **Maxwell's equations on the cube with the Gauss–Legendre method** at every polynomial order. -/
theorem maxwell_gaussLegendre2 (S : PolySeq) (a : ℤ) {τ : ℕ → ℝ} (hτ : ∀ N, 0 < τ N) :
    (((Maxwell.cubePolyPMC n S a).toApprox.gaussLegendre2 τ hτ).Verdict
        (Maxwell.cubePolyPMC n S a).toCore ∧
      ∀ N v k, ‖(((Maxwell.cubePolyPMC n S a).toApprox.gaussLegendre2 τ hτ).P N ^ k) v‖ = ‖v‖) ∧
    (((Maxwell.cubePolyPEC n S a).toApprox.gaussLegendre2 τ hτ).Verdict
        (Maxwell.cubePolyPEC n S a).toCore ∧
      ∀ N v k, ‖(((Maxwell.cubePolyPEC n S a).toApprox.gaussLegendre2 τ hτ).P N ^ k) v‖ = ‖v‖) :=
  have hPMC := RungeKutta.maxwell_gaussLegendre2 (polyFamily n S) a hτ
  have hPEC := RungeKutta.maxwell_gaussLegendre2 (polyFamilyMin n S) a hτ
  ⟨⟨hPMC.1, hPMC.2.1⟩, ⟨hPEC.1, hPEC.2.1⟩⟩

/-- **The Hodge heat equation on the cube with Radau IIA and SDIRK**, with a nonzero datum. -/
theorem heat_radauIIA2 (S : PolySeq) {τ : ℕ → ℝ} (hτ : ∀ N, 0 < τ N) :
    ((heatFamily n S).toHeat.radauIIA2 τ hτ).Verdict
        ((heatFamily n S).heatCore (closedRangeAt_heatWindow n) (isGraphBounded_heatFamily n S)) ∧
      ((heatFamily n S).toHeat.sdirk2 τ hτ).Verdict
        ((heatFamily n S).heatCore (closedRangeAt_heatWindow n) (isGraphBounded_heatFamily n S)) ∧
      ∃ x ∈ ((heatFamily n S).heatCore (closedRangeAt_heatWindow n) (isGraphBounded_heatFamily n S)).Data, x ≠ 0 :=
  ⟨(RungeKutta.heat_radauIIA2 (polyFamily n S) 0 (n + 1) ⊤ _ _ hτ).1,
    (RungeKutta.heat_radauIIA2 (polyFamily n S) 0 (n + 1) ⊤ _ _ hτ).2,
    (crown_heat_nonvacuous n S).2⟩

end Cube.FEM

end Feec.Instances.RungeKutta
