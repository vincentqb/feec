module

public import Feec.HilbertComplex.Approximation.RationalScheme
public import Feec.Instances.Corollaries
public import Feec.TimeStepping.RationalHillePhillipsReal

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
* `full_brennerThomee`: **Gauss–Legendre, Radau IIA and SDIRK with Brenner–Thomée's constants**:
  on every window, the temporal error of the two-stage Gauss–Legendre iterates of the wave
  discretization, and of the Radau IIA and SDIRK iterates of the heat discretization, is at most
  `‖ιₕ‖ C_r tₙ τₕᵖ ‖Lₕ^{p+1} v‖` (`p = 4`, `3`, `2`) with Brenner–Thomée's constant of the
  smooth-data estimate, independent of `h` (fields `brennerThomee_wave`, `brennerThomee_heat` of
  the crown, from the fully discrete FEEC theorem on Banach spaces,
  `Feec.TimeStepping.banachFEEC`); Banach-route constants, not new rates (the verdicts above give
  the same orders with von Neumann's constants);

and on the cube, at every polynomial order of the periodic table (`Cube.FEM.maxwell_gaussLegendre2`,
`Cube.FEM.heat_radauIIA2`). Off Hilbert spaces, for every bounded semigroup of a real or complex
Banach space and `R = (1 - τA)⁻¹` (the `_of_resolvent` forms, by complexification; each has a
complex corollary with `R` the Laplace transform resolvent), for the exact semigroup alone: the
`√n`-lossy error bounds (corollaries of the Banach-space theory that no crown field uses), and the
sharp rate, by the smooth-data estimate that the crown consumes through
`Feec.TimeStepping.banachFEEC` (field `exact_rational` of its verdict; the stability bound of
the first two items is its field `exact_stable_rational`):

* **Radau IIA and SDIRK converge with the `√n` loss of the stability bound**,
  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C M³ (1 + C' √n) nτ τᵖ ‖A^{p+1} x‖` (`p = 3`, `2`), i.e. at fixed
  `T = nτ` with rates `τ^{5/2}` and `τ^{3/2}` (`banach_radauIIA2_of_resolvent`, `banach_radauIIA2`;
  `Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent`);
* so do **Crank–Nicolson and the Gauss–Legendre method**, which have `|r(∞)| = 1` and are not
  strongly A-stable: `‖r(τA)ⁿ‖ ≤ M (1 + C √n)` and rates `τ^{3/2}`, `τ^{7/2}`
  (`banach_implicitMidpoint_of_resolvent`, `banach_gaussLegendre2_of_resolvent`;
  `Feec.TimeStepping.RationalScheme.IsSymmetric.norm_resolventStep_pow_sub_S_le_of_resolvent`,
  for every symmetric scheme);
* without the `√n` loss, **Gauss–Legendre, Radau IIA and SDIRK converge at the sharp rate**,
  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C_r M nτ τᵖ ‖A^{p+1} x‖` (`p = 4`, `3`, `2`;
  `banach_sharp_of_resolvent`, `banach_sharp`), by Brenner–Thomée's smooth-data estimate
  (`Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`), which
  needs only A-stability.

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

/-- **Gauss–Legendre, Radau IIA and SDIRK with Brenner–Thomée's constants in the FEEC theorem**: on
every window with every closed constraint, the iterates of the two-stage Gauss–Legendre method
(order `4`) for the wave discretization satisfy
`‖ιₕ e^{tₙ Lₕ} v - ιₕ Pₕⁿ v‖ ≤ ‖ιₕ‖ C tₙ τₕ⁴ ‖Lₕ⁵ v‖`, and those of Radau IIA
(order `3`) and SDIRK (order `2`) for the heat discretization the same with `τₕ³ ‖Lₕ⁴ v‖` and
`τₕ² ‖Lₕ³ v‖`, with Brenner–Thomée's constants `C = sharpConst r p`, independent of `h` (fields
`brennerThomee_wave`, `brennerThomee_heat` of the crown, from `Feec.TimeStepping.banachFEEC`).
On these Hilbert discretizations these are the Banach-route constants, not new rates: the
verdicts of `full_rationalScheme` give the same orders with `sup_y |ρ(iy)| + 1/(p+1)!`; the Banach
theorems give new content only for discretizations that are not contractive in a Hilbert norm
(the maximum-norm heat equation, `Feec.Models.Cube.MaxNormHeat.maxNormHeat`).
[BrennerThomee1979]; [HairerWanner1996], §IV.5, §IV.6 -/
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

/-- **Radau IIA and SDIRK on every bounded semigroup of a real or complex Banach space**: on a
Banach space over `𝕜 = ℝ` or `ℂ`, with `R` such that `R (x - τ A x) = x` on `D(A)` (the resolvent
`(1 - τA)⁻¹` of the generator `A`), for `τ > 0`, every `n` and `x ∈ D(A⁴)` (resp. `D(A³)`),
`‖r(τA)ⁿ x - S(nτ) x‖` is at most `M (1 + C_r √n) (M ‖μ_ρ‖ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖` with
`p = 3` (Radau IIA) and `p = 2` (SDIRK): both are L-stable, hence strongly A-stable
(`RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent`, by complexification). The factor
`√n` is the loss of Brenner–Thomée's stability bound (rates `τ^{5/2}`, `τ^{3/2}` at fixed `nτ`).
[BrennerThomee1979]; [HairerWanner1996], §IV.5, §IV.6 -/
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

/-- **Radau IIA and SDIRK on every bounded semigroup of a complex Banach space**: the case
`𝕜 = ℂ`, `R = C0Semigroup.laplaceResolvent` of `banach_radauIIA2_of_resolvent`. -/
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

/-- **Crank–Nicolson on every bounded semigroup of a real or complex Banach space** (the implicit
midpoint rule, `r(z) = (1 + z/2)/(1 - z/2)`, order `2`): `|r(∞)| = 1`, so it is not strongly
A-stable, and yet, over `𝕜 = ℝ` or `ℂ`, for `τ > 0` and `R` with `R (x - τ A x) = x` on `D(A)`,
`‖r(τA)ⁿ‖ ≤ M (1 + C √n)` and, for `x ∈ D(A³)`,
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ M (1 + C √n) (M ‖μ_ρ‖ + M/3!) M nτ τ² ‖A³ x‖` (rate `τ^{3/2}` at fixed
`nτ`), with `C = RationalScheme.sqrtConst`
(`RationalScheme.IsSymmetric.norm_resolventStep_pow_sub_S_le_of_resolvent`, by
complexification). [BrennerThomee1979] -/
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

/-- **Crank–Nicolson on every bounded semigroup of a complex Banach space**: the case `𝕜 = ℂ`,
`R = C0Semigroup.laplaceResolvent` of `banach_implicitMidpoint_of_resolvent`. -/
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

/-- **The two-stage Gauss–Legendre method on every bounded semigroup of a real or complex Banach
space** (order `4`): `|r(∞)| = 1`, not strongly A-stable, and, over `𝕜 = ℝ` or `ℂ`, for `τ > 0`
and `R` with `R (x - τ A x) = x` on `D(A)`, `‖r(τA)ⁿ‖ ≤ M (1 + C √n)` and, for `x ∈ D(A⁵)`,
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ M (1 + C √n) (M ‖μ_ρ‖ + M/5!) M nτ τ⁴ ‖A⁵ x‖` (rate `τ^{7/2}` at fixed
`nτ`), with `C = RationalScheme.sqrtConst`. [BrennerThomee1979]; [HairerWanner1996], §IV.5 -/
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

/-- **The two-stage Gauss–Legendre method on every bounded semigroup of a complex Banach
space**: the case `𝕜 = ℂ`, `R = C0Semigroup.laplaceResolvent` of
`banach_gaussLegendre2_of_resolvent`. -/
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

/-- **Gauss–Legendre, Radau IIA and SDIRK at the sharp rate on every bounded semigroup of a real
or complex Banach space**: over `𝕜 = ℝ` or `ℂ`, for `τ > 0`, `R` with `R (x - τ A x) = x` on
`D(A)`, every `n` and `x ∈ D(A^{p+1})`, `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C_r M nτ τᵖ ‖A^{p+1} x‖` with
`p = 4` (two-stage Gauss–Legendre, A-stable with `|r(∞)| = 1`), `p = 3` (Radau IIA) and `p = 2`
(SDIRK), by Brenner–Thomée's smooth-data estimate
(`Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`, by
complexification): order `p` at fixed `nτ`, without the `√n` of `banach_radauIIA2_of_resolvent`
and `banach_gaussLegendre2_of_resolvent`; on the FEEC discretizations the same estimate gives the
crown fields `brennerThomee_wave` and `brennerThomee_heat` (`full_brennerThomee`).
[BrennerThomee1979]; [HairerWanner1996], §IV.5, §IV.6 -/
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

/-- **Gauss–Legendre, Radau IIA and SDIRK at the sharp rate on every bounded semigroup of a complex
Banach space**: the case `𝕜 = ℂ`, `R = C0Semigroup.laplaceResolvent` of
`banach_sharp_of_resolvent`. -/
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
