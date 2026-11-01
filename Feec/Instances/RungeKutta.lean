module

public import Feec.HilbertComplex.Approximation.RationalScheme
public import Feec.Instances.Corollaries
public import Feec.TimeStepping.RationalHillePhillips

/-!
# Rational and Runge–Kutta time stepping in the FEEC theorem

The field `full` of the FEEC theorem (`Feec.HilbertComplex.ConformingFamily.feec`) holds for every
time scheme; every A-stable rational scheme of order `p ≥ 1`, in particular every A-stable
Runge–Kutta method, is one (`Feec.HilbertComplex.DissipFEEC.rationalScheme`). Hence, for every
conforming family `F` of a Hilbert complex on `ℕ` or `ℤ`:

* `full_rationalScheme`: on every window with every closed constraint, the fully discrete wave
  verdict, and on windows with closed range and finite-dimensional harmonic forms the fully
  discrete heat verdict, for every A-stable rational scheme (stability, the temporal error
  `‖ιₕ‖ K tₙ τₕᵖ ‖Lₕ^{p+1} v‖`, convergence as `h, τ → 0`, constraint residuals);
* `maxwell_gaussLegendre2`: **Maxwell's equations with the two-stage Gauss–Legendre method**
  (order `4`): the fully discrete verdict, exact energy conservation of the iterates, and the
  Gauss-law residuals tending to `0` as `h, τ → 0`;
* `heat_radauIIA2`: **the Hodge heat equation with the L-stable Radau IIA and SDIRK methods**
  (orders `3` and `2`; L-stability is `RationalScheme.isLStable_radauIIA2`, `isLStable_sdirk2`):
  the fully discrete verdicts;

and on the cube, at every polynomial order of the periodic table (`Cube.FEM.maxwell_gaussLegendre2`,
`Cube.FEM.heat_radauIIA2`). Off Hilbert spaces, for every bounded semigroup of a complex Banach
space (`banach_radauIIA2`): **Radau IIA and SDIRK converge with orders `3` and `2` up to a factor
`√n`**, `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C M³ (1 + C' √n) nτ τᵖ ‖A^{p+1} x‖`, by the Hille–Phillips calculus
(`Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_sqrt`).

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996],
  §IV.5, §IV.6
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [R. Hersh, T. Kato, *High-Accuracy Stable Difference Schemes for Well-Posed Initial-Value Problems*][HershKato1979]

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

/-- **Every A-stable rational scheme in the FEEC theorem**: on every window with every closed
constraint, the fully discrete wave verdict, and with closed range the fully discrete heat
verdict, for the A-stable rational scheme `r` of order
`p ≥ 1` (field `full` of the FEEC theorem). [BrennerThomee1979] -/
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

/-- **Maxwell's equations with the two-stage Gauss–Legendre method** in the window
`V a → V (a+1) → V (a+2)` with the Gauss laws (`Feec.Instances.Maxwell.feec`): the fully discrete
verdict (order `4`), exact energy conservation of the iterates (the method is symmetric), and for
every datum satisfying the Gauss laws and every family of discrete data with `ιₕ vₕ → x`, the
Gauss-law residuals of the iterates on `[0, T]` tend to `0` as `τₕ → 0`. [HairerWanner1996],
§IV.5 -/
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

/-- **The Hodge heat equation with the L-stable Radau IIA and SDIRK methods** on every window
with closed range and finite-dimensional harmonic forms, with every closed constraint: the fully
discrete verdicts, of orders `3` and `2` (field `full` of the FEEC theorem). [HairerWanner1996],
§IV.5, §IV.6 -/
theorem heat_radauIIA2 (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) :
    ((F.windowFEEC a m K hK).toHeat.radauIIA2 τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK)) ∧
      ((F.windowFEEC a m K hK).toHeat.sdirk2 τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK)) :=
  ⟨(F.feec.full a m K hK).heat hcr (F.isGraphBounded_windowFEEC a m K hK) _,
    (F.feec.full a m K hK).heat hcr (F.isGraphBounded_windowFEEC a m K hK) _⟩

end Family

/-! ### Bounded semigroups on Banach spaces -/

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

/-- **Radau IIA and SDIRK on every bounded semigroup of a complex Banach space**: with the
resolvent `R = (1 - τA)⁻¹` of the generator `A` (`C0Semigroup.laplaceResolvent`), for `τ > 0`,
every `n` and `x ∈ D(A⁴)` (resp. `D(A³)`), `‖r(τA)ⁿ x - S(nτ) x‖` is at most
`M (1 + C_r √n) (M ‖μ_ρ‖ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖` with `p = 3` (Radau IIA) and `p = 2`
(SDIRK): both are L-stable, hence strongly A-stable. [BrennerThomee1979]; [HairerWanner1996],
§IV.5, §IV.6 -/
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
  ⟨RationalScheme.norm_resolventStep_pow_sub_S_le_sqrt G hM
      RationalScheme.isLStable_radauIIA2.isStronglyAStable RationalScheme.hasOrder_radauIIA2 hτ n,
    RationalScheme.norm_resolventStep_pow_sub_S_le_sqrt G hM
      RationalScheme.isLStable_sdirk2.isStronglyAStable RationalScheme.hasOrder_sdirk2 hτ n⟩

end Banach

/-! ### The cube -/

namespace Cube.FEM

open Feec.Models.Cube.FEM Feec.FiniteElement

variable (n : ℕ) [NeZero n]

/-- **Maxwell's equations on the cube with the Gauss–Legendre method** at every polynomial order
(`Feec.Instances.Maxwell.cubePolyPMC`, `cubePolyPEC`): for both, the fully discrete verdict and
exact energy conservation of the iterates (`maxwell_gaussLegendre2`). -/
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

/-- **The Hodge heat equation on the cube with Radau IIA and SDIRK** (`heatFamily`, every
admissible sequence `S`): the fully discrete verdicts, with a nonzero datum in the core. -/
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
