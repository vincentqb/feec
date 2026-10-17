module

public import Feec.Domain.Operators
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Mollification and dilation on a finite-dimensional real space

Let `E` be a finite-dimensional real normed space with an additive Haar measure (`ℝⁿ`).

* `molli φ f = f ⋆ ρ_φ` (`ρ_φ` the normalized bump), an `L²`-contraction (`eLpNorm_molli_le`),
  smooth (`contDiff_molli`), commuting with derivatives (`iterDeriv_molli`);
* `dil x₀ c f = f (x₀ + c (· - x₀))`, an `L²`-contraction for `c ≥ 1` (`eLpNorm_dil_le`), with
  `∂^{vs} (dil x₀ c f) = c^k dil x₀ c (∂^{vs} f)` (`iterDeriv_dil`);
* **convergence**: `dil x₀ c (molli φ f) → f` in `L²(E)` as `c ↓ 1` and the bump radius `→ 0`
  (`eLpNorm_dil_molli_sub_le`);
* **geometry** (`dil_mem_of_starBall`): on a domain star-shaped with respect to a ball,
  dilating towards the centre moves `cl Ω + B(0, r)` inside `Ω`;
* **constrained density** (`exists_isTestField_ker_dist_lt`): on a bounded open `Ω` star-shaped
  with respect to a ball, every `u ∈ L²(Ω; ℝ^ι)` whose zero extension satisfies `A ū = 0` in
  `𝒟'(E)`, for a row-homogeneous constant-coefficient operator `A` (each output row of a single
  order, e.g. pointwise algebraic constraints together with `div`), is an `L²` limit of test fields
  `φ` with `A φ = 0` everywhere. This is the general form of the density of smooth TSD fields in
  `L²(TSD₀)` (thesis Prop 4.17 density gap).
* **interior constraints** (`exists_contDiff_ker_on_dist_lt`): if `A u = 0` only in `𝒟'(Ω)` (no
  boundary condition), `u` is an `L²(Ω)` limit of fields smooth on `E` with `A φ = 0` on `Ω`
  (mollification followed by an expansion about the centre, `c < 1`,
  `closedBall_dil_subset_of_starBall`, with the two-sided estimates
  `eLpNorm_dil_le_of_half_le`, `eLpNorm_dil_molli_sub_le_of_abs`).

## References

* [Brezis2011], Ch. 4 (convolution, mollifiers, density of `C_c` in `L^p`)
* [QuennevilleBelair2015], §4.10 (Prop 4.17 and its proof)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution RealInnerProductSpace NNReal

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-! ## Mollification and dilation -/

/-- Mollification `f ⋆ ρ_φ` with the normalized bump `ρ_φ`. -/
def molli (φ : ContDiffBump (0 : E)) (f : E → ℝ) : E → ℝ :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ.normed volume

omit [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- `(f ⋆ ρ)(x) = ∫ f(t) ρ(x - t) dt`. -/
theorem molli_apply (φ : ContDiffBump (0 : E)) (f : E → ℝ) (x : E) :
    molli φ f x = ∫ t, f t * φ.normed volume (x - t) := by
  simp [molli, convolution_def]

/-- **Mollification is an `L²`-contraction** (squared form): by Cauchy–Schwarz against the
probability density `ρ(x - ·)`, `|(f ⋆ ρ)(x)|² ≤ ∫ ρ(x - t) |f(t)|² dt`, and Tonelli. -/
theorem lintegral_sq_molli_le (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖molli φ f x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  set ρ := φ.normed volume with hρ
  have hρc : Continuous ρ := φ.continuous_normed
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => φ.nonneg_normed y
  have hρm : ∀ x, Measurable fun t : E => ENNReal.ofReal (ρ (x - t)) := fun x =>
    ENNReal.measurable_ofReal.comp (hρc.measurable.comp (measurable_const.sub measurable_id))
  have hint0 : ∫⁻ t, ENNReal.ofReal (ρ t) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (φ.integrable_normed) (Eventually.of_forall hρ0),
      φ.integral_normed, ENNReal.ofReal_one]
  have hint : ∀ x, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) = 1 := by
    intro x
    rw [lintegral_sub_left_eq_self (fun t => ENNReal.ofReal (ρ t)) x, hint0]
  have key : ∀ x, ‖molli φ f x‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t‖ₑ ^ (2 : ℝ) := by
    intro x
    set ν := volume.withDensity fun t : E => ENNReal.ofReal (ρ (x - t))
    have hν : ν univ = 1 := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hint]
    have hfν : AEStronglyMeasurable f ν :=
      hf.mono_ac (withDensity_absolutelyContinuous _ _)
    have h1 : ‖molli φ f x‖ₑ ≤ ∫⁻ t, ‖f t‖ₑ ∂ν := by
      rw [molli_apply, lintegral_withDensity_eq_lintegral_mul₀ (hρm x).aemeasurable
        hf.enorm]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun t => ?_
      simp only [Pi.mul_apply, enorm_mul]
      rw [← hρ, Real.enorm_of_nonneg (hρ0 _), mul_comm]
    have h2 : ∫⁻ t, ‖f t‖ₑ ∂ν ≤ (∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
      have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hfν
      rw [hν, ENNReal.one_rpow, mul_one, eLpNorm_one_eq_lintegral_enorm hfν,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfν] at this
      simpa using this
    have h3 := ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num : (0 : ℝ) ≤ 2)
    rw [← ENNReal.rpow_mul, show 1 / (2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
      lintegral_withDensity_eq_lintegral_mul₀ (hρm x).aemeasurable
        (hf.enorm.pow_const _)] at h3
    exact h3
  calc ∫⁻ x, ‖molli φ f x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t‖ₑ ^ (2 : ℝ) := lintegral_mono key
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ (x - t)) * ‖f t‖ₑ ^ (2 : ℝ) := by
      refine lintegral_lintegral_swap ?_
      refine AEMeasurable.mul ?_ ((hf.enorm.pow_const _).comp_snd)
      exact (ENNReal.measurable_ofReal.comp
        (hρc.measurable.comp (measurable_fst.sub measurable_snd))).aemeasurable
    _ = ∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) := by
      refine lintegral_congr fun t => ?_
      rw [lintegral_mul_const' _ _ (by simp),
        lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (ρ y)) t, hint0, one_mul]

/-- Dilation `f ↦ f(x₀ + c (x - x₀))`; for `c = 1/λ > 1` it shrinks the support towards `x₀`. -/
def dil (x₀ : E) (c : ℝ) (f : E → ℝ) : E → ℝ := fun x => f (x₀ + c • (x - x₀))

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The dilation is a translation composed with `x ↦ c x`. -/
theorem dil_eq (x₀ : E) (c : ℝ) (f : E → ℝ) :
    dil x₀ c f = (fun y => f ((x₀ - c • x₀) + y)) ∘ (c • ·) := by
  ext x
  simp only [dil, Function.comp_apply, smul_sub]
  congr 1
  abel

/-- **Dilation with `c ≥ 1` is an `L²`-contraction**: `‖f(x₀ + c (· - x₀))‖₂ ≤ ‖f‖₂`. (The norm
scales by `c^{-3/2}`; only the inequality is proved.) -/
theorem eLpNorm_dil_le (x₀ : E) {c : ℝ} (hc : 1 ≤ c) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (dil x₀ c f) 2 volume ≤ eLpNorm f 2 volume := by
  have hc0 : c ≠ 0 := by positivity
  set g : E → ℝ := fun y => f ((x₀ - c • x₀) + y)
  have hmp : MeasurePreserving (fun y : E => (x₀ - c • x₀) + y) volume volume :=
    measurePreserving_add_left volume _
  have hg : AEStronglyMeasurable g volume := hf.comp_measurePreserving hmp
  have hgn : eLpNorm g 2 volume = eLpNorm f 2 volume := eLpNorm_comp_measurePreserving hf hmp
  have hmap := Measure.map_addHaar_smul (volume : Measure E) hc0
  rw [dil_eq, ← eLpNorm_map_measure (by rw [hmap]; exact hg.smul_measure _)
    (measurable_const_smul c).aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_top (by norm_num), ← hgn]
  swap; · exact hg
  have h1 : ENNReal.ofReal |(c ^ Module.finrank ℝ E)⁻¹| ≤ 1 := by
    rw [ENNReal.ofReal_le_one, abs_inv, abs_pow, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hc)
  calc ENNReal.ofReal |(c ^ Module.finrank ℝ E)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm g 2 volume
      ≤ (1 : ℝ≥0∞) * eLpNorm g 2 volume := by
        rw [smul_eq_mul]
        exact mul_le_mul_left (ENNReal.rpow_le_one h1 (by simp)) _
    _ = eLpNorm g 2 volume := one_mul _

/-- Mollifications of locally integrable functions are continuous. -/
theorem continuous_molli (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : LocallyIntegrable f volume) : Continuous (molli φ f) :=
  (φ.hasCompactSupport_normed).continuous_convolution_right _ hf φ.continuous_normed

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- Dilations of continuous functions are continuous. -/
theorem continuous_dil (x₀ : E) (c : ℝ) {f : E → ℝ} (hf : Continuous f) :
    Continuous (dil x₀ c f) :=
  hf.comp (by fun_prop)

/-- **Mollification is an `L²`-contraction.** -/
theorem eLpNorm_molli_le (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm (molli φ f) 2 volume ≤ eLpNorm f 2 volume := by
  have hm := (continuous_molli φ (hf.locallyIntegrable (by norm_num))).aestronglyMeasurable
    (μ := volume)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow (lintegral_sq_molli_le φ hf.aestronglyMeasurable) (by norm_num)

/-- `f ⋆ ρ = ρ ⋆ f`, in the form used by `ContDiffBump.dist_normed_convolution_le`. -/
theorem molli_eq_normed_convolution (φ : ContDiffBump (0 : E)) (f : E → ℝ) :
    molli φ f = φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  rw [molli, ← convolution_flip]
  congr 1
  ext
  simp

/-- Pointwise and support estimates for a continuous compactly supported `g`: the dilated
mollification is uniformly close to `g`, with support in a fixed ball. -/
theorem eLpNorm_dil_molli_sub_le_of_continuous (x₀ : E) {g : E → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ c : ℝ, 1 ≤ c → c < 1 + η → ∀ φ : ContDiffBump (0 : E), φ.rOut < η →
      eLpNorm (dil x₀ c (molli φ g) - g) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR0, hR⟩ : ∃ R > 0, tsupport g ⊆ Metric.closedBall x₀ R := by
    obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall x₀
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hsupp : ∀ x, g x ≠ 0 → dist x x₀ ≤ R := fun x hx =>
    hR (subset_tsupport _ hx)
  set K := Metric.closedBall x₀ (R + 1)
  have hK : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  set M := (volume K).toReal
  have hKM : volume K ^ (1 / ENNReal.toReal 2) = ENNReal.ofReal (Real.sqrt M) := by
    rw [← ENNReal.ofReal_toReal hK, Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg
      ENNReal.toReal_nonneg (by norm_num)]
    norm_num
    rfl
  set ε' := ε / (Real.sqrt M + 1)
  have hε' : 0 < ε' := by positivity
  have hε'M : ε' * Real.sqrt M ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg M]
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1
    (hgs.uniformContinuous_of_continuous hgc) (ε' / 2) (by positivity)
  refine ⟨min 1 (δ / (R + 1)), by positivity, fun c hc1 hc2 φ hφ => ?_⟩
  have hφ1 : φ.rOut < 1 := hφ.trans_le (min_le_left _ _)
  have hφδ : φ.rOut < δ := hφ.trans_le ((min_le_right _ _).trans
    (div_le_self hδ.le (by linarith)))
  have hcR : (c - 1) * R < δ := by
    have : c - 1 < δ / (R + 1) := by linarith [min_le_right 1 (δ / (R + 1))]
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  have hgl : LocallyIntegrable g volume := hgc.locallyIntegrable
  -- the dilated point
  have hy : ∀ x, dist (x₀ + c • (x - x₀)) x₀ = c * dist x x₀ := by
    intro x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg
      (by linarith)]
  have hyx : ∀ x, dist (x₀ + c • (x - x₀)) x = (c - 1) * dist x x₀ := by
    intro x
    rw [dist_eq_norm, dist_eq_norm, show x₀ + c • (x - x₀) - x = (c - 1) • (x - x₀) by
      rw [sub_smul, one_smul]; abel, norm_smul, Real.norm_of_nonneg (by linarith)]
  have hpt : ∀ x, dist (dil x₀ c (molli φ g) x) (g x) ≤ ε' := by
    intro x
    set y := x₀ + c • (x - x₀)
    have h1 : dist (molli φ g y) (g y) ≤ ε' / 2 := by
      rw [molli_eq_normed_convolution]
      refine φ.dist_normed_convolution_le hgc.aestronglyMeasurable fun z hz => ?_
      exact (hδg (lt_of_lt_of_le (Metric.mem_ball.1 hz) hφδ.le)).le
    have h2 : dist (g y) (g x) ≤ ε' / 2 := by
      by_cases h : g y = 0 ∧ g x = 0
      · rw [h.1, h.2, dist_self]; positivity
      have hxR : dist x x₀ ≤ R := by
        rcases not_and_or.1 h with h | h
        · have := hsupp y h
          rw [hy] at this
          nlinarith [dist_nonneg (x := x) (y := x₀)]
        · exact hsupp x h
      refine (hδg ?_).le
      rw [hyx]
      calc (c - 1) * dist x x₀ ≤ (c - 1) * R := mul_le_mul_of_nonneg_left hxR (by linarith)
        _ < δ := hcR
    calc dist (dil x₀ c (molli φ g) x) (g x) ≤ dist (molli φ g y) (g y) + dist (g y) (g x) :=
          dist_triangle _ _ _
      _ ≤ ε' := by linarith
  have hs1 : Function.support (dil x₀ c (molli φ g)) ⊆ K := by
    intro x hx
    have hm : x₀ + c • (x - x₀) ∈ Function.support (molli φ g) := hx
    obtain ⟨u, hu, v, hv, huv⟩ := support_convolution_subset _ hm
    rw [φ.support_normed_eq] at hv
    have hu' := hsupp u hu
    have hv' : ‖v‖ < φ.rOut := by simpa using hv
    have : dist (x₀ + c • (x - x₀)) x₀ ≤ R + 1 := by
      rw [← huv, dist_eq_norm, show u + v - x₀ = (u - x₀) + v by abel]
      calc ‖(u - x₀) + v‖ ≤ ‖u - x₀‖ + ‖v‖ := norm_add_le _ _
        _ ≤ R + 1 := by rw [← dist_eq_norm]; linarith
    rw [hy] at this
    show dist x x₀ ≤ R + 1
    nlinarith [dist_nonneg (x := x) (y := x₀)]
  have hs2 : Function.support g ⊆ K := fun x hx =>
    (hsupp x hx).trans (by linarith)
  have hmeas : AEStronglyMeasurable (dil x₀ c (molli φ g) - g) volume :=
    ((continuous_dil x₀ c (continuous_molli φ hgl)).sub hgc).aestronglyMeasurable
  refine (eLpNorm_sub_le_of_dist_bdd volume (by norm_num) measurableSet_closedBall.nullMeasurableSet
    hε'.le hmeas hpt hs1 hs2).trans ?_
  rw [hKM, ← ENNReal.ofReal_mul hε'.le]
  exact ENNReal.ofReal_le_ofReal hε'M

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The dilation is additive. -/
theorem dil_add (x₀ : E) (c : ℝ) (f g : E → ℝ) : dil x₀ c (f + g) = dil x₀ c f + dil x₀ c g :=
  rfl

/-- Mollification is additive on locally integrable functions. -/
theorem molli_add (φ : ContDiffBump (0 : E)) {f g : E → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) : molli φ (f + g) = molli φ f + molli φ g :=
  ConvolutionExists.add_distrib
    (φ.hasCompactSupport_normed.convolutionExists_right _ hf φ.continuous_normed)
    (φ.hasCompactSupport_normed.convolutionExists_right _ hg φ.continuous_normed)

/-- **Dilated mollification converges in `L²(ℝ³)`**: for `f ∈ L²(ℝ³)` and `ε > 0`, the field
`x ↦ (f ⋆ ρ_φ)(x₀ + c (x - x₀))` is `ε`-close to `f` once `c ≥ 1` is close to `1` and the bump
radius is small. Proof: approximate `f` by a smooth compactly supported `g`
(`MemLp.exist_eLpNorm_sub_le`); both operations are `L²`-contractions
(`eLpNorm_molli_le`, `eLpNorm_dil_le`), and converge uniformly with supports in a fixed ball
for `g`. -/
theorem eLpNorm_dil_molli_sub_le (x₀ : E) {f : E → ℝ} (hf : MemLp f 2 volume) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, ∀ c : ℝ, 1 ≤ c → c < 1 + η → ∀ φ : ContDiffBump (0 : E), φ.rOut < η →
      eLpNorm (dil x₀ c (molli φ f) - f) 2 volume ≤ ENNReal.ofReal ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨g, hgs, hgd, hfg⟩ := hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε3
  have hgc : Continuous g := hgd.continuous
  have hgm : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport hgs
  obtain ⟨η, hη, hηg⟩ := eLpNorm_dil_molli_sub_le_of_continuous x₀ hgc hgs hε3
  refine ⟨η, hη, fun c hc1 hc2 φ hφ => ?_⟩
  have hfgm : MemLp (f - g) 2 volume := hf.sub hgm
  have hli : LocallyIntegrable (f - g) volume := hfgm.locallyIntegrable (by norm_num)
  have hgl : LocallyIntegrable g volume := hgc.locallyIntegrable
  have e : dil x₀ c (molli φ f) - f =
      dil x₀ c (molli φ (f - g)) + (dil x₀ c (molli φ g) - g) + -(f - g) := by
    have : f = (f - g) + g := by abel
    conv_lhs => rw [this, molli_add φ hli hgl, dil_add]
    abel
  have b1 : eLpNorm (dil x₀ c (molli φ (f - g))) 2 volume ≤ ENNReal.ofReal (ε / 3) :=
    (eLpNorm_dil_le x₀ hc1 (continuous_molli φ hli).aestronglyMeasurable).trans
      ((eLpNorm_molli_le φ hfgm).trans hfg)
  rw [e]
  calc eLpNorm (dil x₀ c (molli φ (f - g)) + (dil x₀ c (molli φ g) - g) + -(f - g)) 2 volume
      ≤ eLpNorm (dil x₀ c (molli φ (f - g)) + (dil x₀ c (molli φ g) - g)) 2 volume +
          eLpNorm (-(f - g)) 2 volume := eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (dil x₀ c (molli φ (f - g))) 2 volume +
          eLpNorm (dil x₀ c (molli φ g) - g) 2 volume) + eLpNorm (f - g) 2 volume := by
        rw [eLpNorm_neg]
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) + ENNReal.ofReal (ε / 3) := by
        gcongr
        exact hηg c hc1 hc2 φ hφ
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε3.le hε3.le, ← ENNReal.ofReal_add (by positivity) hε3.le]
        congr 1; ring

/-! ## Structural properties -/

/-- Mollifications are smooth. -/
theorem contDiff_molli (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (molli φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_right _ hf φ.contDiff_normed

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- Dilations of smooth functions are smooth. -/
theorem contDiff_dil (x₀ : E) (c : ℝ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dil x₀ c f) :=
  hf.comp (by fun_prop)


/-! ## Geometry -/

variable {Ω : Set E}

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- **Dilation towards the center of a ball of star-shapedness.** If `Ω` is star-shaped with
respect to every point of `B(x₀, s)`, `c > 1` and `r < s (c - 1) / 2`, then
`x₀ + c⁻¹ (q + v - x₀) ∈ Ω` for every `q ∈ closure Ω` and `‖v‖ ≤ r`. -/
theorem dil_mem_of_starBall {x₀ : E} {s : ℝ}
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {c r : ℝ} (hc : 1 < c)
    (hr : r < s * (c - 1) / 2) {q : E} (hq : q ∈ closure Ω) {v : E} (hv : ‖v‖ ≤ r) :
    x₀ + c⁻¹ • (q + v - x₀) ∈ Ω := by
  have hc0 : 0 < c := by linarith
  have hc1 : 0 < c - 1 := by linarith
  have hs : 0 < s := by
    have : 0 ≤ r := (norm_nonneg v).trans hv
    nlinarith
  obtain ⟨q', hq', hqq'⟩ := Metric.mem_closure_iff.1 hq (s * (c - 1) / 2) (by positivity)
  set w : E := (c - 1)⁻¹ • (v + (q - q'))
  have hw : ‖w‖ < s := by
    have h1 : ‖v + (q - q')‖ < s * (c - 1) := by
      calc ‖v + (q - q')‖ ≤ ‖v‖ + ‖q - q'‖ := norm_add_le _ _
        _ < s * (c - 1) := by rw [← dist_eq_norm]; linarith
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc1.le), inv_mul_lt_iff₀ hc1]
    linarith
  have hz : x₀ + w ∈ Metric.ball x₀ s := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hw
  refine hstar q' hq' (x₀ + w) hz ⟨1 - c⁻¹, c⁻¹, by
    rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hc.le, by positivity, by ring, ?_⟩
  have e : (1 - c⁻¹) * (c - 1)⁻¹ = c⁻¹ := by field_simp
  simp only [w, smul_add, smul_smul, e, smul_sub, sub_smul, one_smul]
  abel

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The compact set containing the support of the dilated mollification. -/
theorem isCompact_dilImage (hb : Bornology.IsBounded Ω) (x₀ : E) (c r : ℝ) :
    IsCompact ((fun p : E × E => x₀ + c⁻¹ • (p.1 + p.2 - x₀)) ''
      (closure Ω ×ˢ Metric.closedBall 0 r)) :=
  (hb.isCompact_closure.prod (isCompact_closedBall 0 r)).image (by fun_prop)


/-! ## Derivatives of mollifications, dilations and reflections -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The convolution `f ⋆ ρ` of a locally integrable `f` with a smooth compactly supported `ρ`. -/
theorem convolution_apply_mul (ρ f : E → ℝ) (y : E) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y = ∫ t, f t * ρ (y - t) := by
  simp [convolution_def]

/-- `∂_v (f ⋆ ρ) = f ⋆ ∂_v ρ`. -/
theorem fderiv_convolution_apply {ρ : E → ℝ} (hρ : IsTest (univ : Set E) ρ) {f : E → ℝ}
    (hf : LocallyIntegrable f volume) (y v : E) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y v =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => fderiv ℝ ρ x v) y := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.contDiff.of_le (by simp)
  have hd := hρ.hasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hf hρ1 y
  rw [hd.fderiv, convolution_precompR_apply _ hf (hρ.hasCompactSupport.fderiv ℝ)
    (hρ1.continuous_fderiv one_ne_zero)]

/-- `∂^{vs} (f ⋆ ρ) = f ⋆ ∂^{vs} ρ`. -/
theorem iterDeriv_convolution {ρ : E → ℝ} (hρ : IsTest (univ : Set E) ρ) {f : E → ℝ}
    (hf : LocallyIntegrable f volume) (vs : List E) :
    iterDeriv vs (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] iterDeriv vs ρ := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext y
    rw [iterDeriv_cons]
    simp only
    rw [ih, fderiv_convolution_apply (hρ.iterDeriv vs) hf]
    rfl

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- `∂^l [t ↦ g (y - t)] = (-1)^{#l} (∂^l g)(y - ·)`. -/
theorem iterDeriv_comp_sub {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (y : E) (l : List E) :
    iterDeriv l (fun t => g (y - t)) = fun t => (-1) ^ l.length * iterDeriv l g (y - t) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    funext t
    rw [iterDeriv_cons]
    simp only
    rw [ih]
    have hd : Differentiable ℝ (iterDeriv l g) :=
      (contDiff_iterDeriv hg l).differentiable (by simp)
    have h1 : HasFDerivAt (fun t => iterDeriv l g (y - t))
        ((fderiv ℝ (iterDeriv l g) (y - t)).comp (-ContinuousLinearMap.id ℝ E)) t :=
      (hd (y - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub y)
    rw [fderiv_const_mul (h1.differentiableAt), h1.fderiv, List.length_cons, pow_succ]
    simp [iterDeriv_cons]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- Moving the first derivative to the end (Schwarz). -/
theorem iterDeriv_append_singleton {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (v : E) (l : List E) :
    iterDeriv (l ++ [v]) g = iterDeriv (v :: l) g := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    funext x
    rw [List.cons_append, iterDeriv_cons, ih, iterDeriv_cons, iterDeriv_cons, iterDeriv_cons]
    exact fderiv_fderiv_comm ((contDiff_iterDeriv hg l).of_le (by simp)) v w x

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- **Partial derivatives of a smooth function commute**: `∂^{rev l} g = ∂^l g`. -/
theorem iterDeriv_reverse {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (l : List E) :
    iterDeriv l.reverse g = iterDeriv l g := by
  induction l generalizing g with
  | nil => rfl
  | cons v l ih =>
    rw [List.reverse_cons, iterDeriv_append, ih (contDiff_iterDeriv hg [v]), ← iterDeriv_append,
      iterDeriv_append_singleton hg v l]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- `∂^{vs} (dil x₀ c f) = c^{#vs} dil x₀ c (∂^{vs} f)`. -/
theorem iterDeriv_dil (x₀ : E) (c : ℝ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (vs : List E) :
    iterDeriv vs (dil x₀ c f) = fun x => c ^ vs.length * iterDeriv vs f (x₀ + c • (x - x₀)) := by
  induction vs with
  | nil => funext x; simp [dil]
  | cons v vs ih =>
    funext x
    rw [iterDeriv_cons]
    simp only
    rw [ih]
    have hd : Differentiable ℝ (iterDeriv vs f) :=
      (contDiff_iterDeriv hf vs).differentiable (by simp)
    have hA : HasFDerivAt (fun x : E => x₀ + c • (x - x₀)) (c • ContinuousLinearMap.id ℝ E) x :=
      (((hasFDerivAt_id x).sub_const x₀).const_smul c).const_add x₀
    have h1 : HasFDerivAt (fun x => iterDeriv vs f (x₀ + c • (x - x₀)))
        ((fderiv ℝ (iterDeriv vs f) (x₀ + c • (x - x₀))).comp (c • ContinuousLinearMap.id ℝ E)) x :=
      (hd _).hasFDerivAt.comp x hA
    rw [(h1.const_mul (c ^ vs.length)).fderiv, List.length_cons, pow_succ]
    simp [iterDeriv_cons]
    ring

/-! ## Operators applied to mollifications and dilations -/

namespace ConstCoeffOp

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `A` is **row-homogeneous** of orders `k`: every term of the output row `j` has order `k j`
(for example zeroth-order algebraic constraints together with first-order `div`). -/
def IsRowHomogeneous (A : ConstCoeffOp E ℝ ι κ) (k : κ → ℕ) : Prop :=
  ∀ j i, ∀ t ∈ A.coeff j i, t.1.length = k j

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype κ] in
/-- Row-homogeneous operators commute with dilations up to the factor `c^{k j}`. -/
theorem apply_dil {A : ConstCoeffOp E ℝ ι κ} {k : κ → ℕ} (hA : A.IsRowHomogeneous k) (x₀ : E)
    (c : ℝ) {f : ι → E → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i)) (j : κ) (x : E) :
    A.apply (fun i => dil x₀ c (f i)) j x = c ^ k j * A.apply f j (x₀ + c • (x - x₀)) := by
  simp only [apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key : ∀ P : List (List E × ℝ), (∀ t ∈ P, t.1.length = k j) →
      applyEntry P (dil x₀ c (f i)) x = c ^ k j * applyEntry P (f i) (x₀ + c • (x - x₀)) := by
    intro P hP
    induction P with
    | nil => simp [applyEntry]
    | cons t P ih =>
      rw [applyEntry_cons, applyEntry_cons]
      simp only
      rw [ih fun t' ht' => hP t' (List.mem_cons_of_mem _ ht'), iterDeriv_dil x₀ c (hf i),
        hP t List.mem_cons_self]
      ring
  exact key _ (hA j i)

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
theorem _root_.Feec.Domain.integrable_mul_isTest {f g : E → ℝ} (hf : LocallyIntegrable f volume)
    (hg : IsTest (univ : Set E) g) : Integrable (fun s => f s * g s) := by
  refine (hf.integrable_smul_left_of_hasCompactSupport hg.continuous hg.hasCompactSupport).congr
    (Eventually.of_forall fun s => ?_)
  all_goals simp [smul_eq_mul, mul_comm]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- The reflected kernel `s ↦ ρ (y - s)` is a test function on `E`. -/
theorem _root_.Feec.Domain.IsTest.comp_sub {ρ : E → ℝ} (hρ : IsTest (univ : Set E) ρ) (y : E) :
    IsTest (univ : Set E) (fun s => ρ (y - s)) :=
  ⟨hρ.contDiff.comp (contDiff_const.sub contDiff_id),
    hρ.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft y), subset_univ _⟩

omit [Fintype ι] [Fintype κ] in
/-- `P (f ⋆ ρ) (y)` is the pairing of `f` with the formal adjoint of `P` applied to the reflected
kernel (real scalars). -/
theorem applyEntry_convolution (P : List (List E × ℝ)) {ρ : E → ℝ}
    (hρ : IsTest (univ : Set E) ρ) {f : E → ℝ} (hf : LocallyIntegrable f volume) (y : E) :
    applyEntry P (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y =
      ∫ t, f t * applyEntry (adjEntry P) (fun s => ρ (y - s)) t := by
  induction P with
  | nil => simp [applyEntry, adjEntry]
  | cons t P ih =>
    obtain ⟨vs, c⟩ := t
    have hρr : ContDiff ℝ ∞ ρ := hρ.contDiff
    have hterm : ∀ s, f s * applyEntry (adjEntry ((vs, c) :: P)) (fun s => ρ (y - s)) s =
        c * (f s * iterDeriv vs ρ (y - s)) +
          f s * applyEntry (adjEntry P) (fun s => ρ (y - s)) s := by
      intro s
      simp only [adjEntry, List.map_cons]
      rw [applyEntry_cons]
      simp only [starRingEnd_apply, star_trivial]
      rw [iterDeriv_comp_sub hρr y, iterDeriv_reverse hρr, List.length_reverse]
      have h1 : ((-1 : ℝ) ^ vs.length) * ((-1) ^ vs.length) = 1 := by
        rw [← mul_pow]; norm_num
      simp only [adjEntry] at *
      linear_combination (c * f s * iterDeriv vs ρ (y - s)) * h1
    rw [applyEntry_cons]
    simp only
    rw [iterDeriv_convolution hρ hf, convolution_apply_mul, ih,
      integral_congr_ae (Eventually.of_forall hterm), integral_add, integral_const_mul]
    · exact (integrable_mul_isTest hf ((hρ.iterDeriv vs).comp_sub y)).const_mul c
    · exact integrable_mul_isTest hf (IsTest.applyEntry (adjEntry P) (hρ.comp_sub y))

/-- **`A (f ⋆ ρ)` is a distributional pairing**: `(A (f ⋆ ρ))ⱼ (y) = Σᵢ ∫ fᵢ (Aᵗ ψ)ᵢ` with
`ψ = eⱼ ρ (y - ·)`. -/
theorem apply_convolution (A : ConstCoeffOp E ℝ ι κ) {ρ : E → ℝ}
    (hρ : IsTest (univ : Set E) ρ) {f : ι → E → ℝ} (hf : ∀ i, LocallyIntegrable (f i) volume)
    [DecidableEq κ] (j : κ) (y : E) :
    A.apply (fun i => f i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) j y =
      ∑ i, ∫ t, f i t * A.formalAdj.apply (Pi.single j fun s => ρ (y - s)) i t := by
  simp only [apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [applyEntry_convolution _ hρ (hf i)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [formalAdj]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    rw [Pi.single_eq_of_ne hj']
    exact congrFun (applyEntry_zero _) t
  · simp

end ConstCoeffOp


/-! ## Dilated mollifications of zero extensions are test functions -/

/-- The support of the dilated mollification of a function vanishing off `Ω` lies in the image
of `cl Ω × B̄(0, r)` under `(q, v) ↦ x₀ + c⁻¹ (q + v - x₀)`. -/
theorem support_dil_molli_indicator_subset (f : E → ℝ) (x₀ : E) {c : ℝ} (hc : c ≠ 0)
    (φ : ContDiffBump (0 : E)) :
    Function.support (dil x₀ c (molli φ (Ω.indicator f))) ⊆
      (fun p : E × E => x₀ + c⁻¹ • (p.1 + p.2 - x₀)) ''
        (closure Ω ×ˢ Metric.closedBall 0 φ.rOut) := by
  intro x hx
  have hm : x₀ + c • (x - x₀) ∈ Function.support (molli φ (Ω.indicator f)) := hx
  obtain ⟨u, hu, v, hv, huv⟩ := support_convolution_subset _ hm
  rw [φ.support_normed_eq] at hv
  have hu' : u ∈ Ω := by
    by_contra h
    exact hu (Set.indicator_of_notMem h _)
  refine ⟨(u, v), ⟨subset_closure hu', Metric.ball_subset_closedBall hv⟩, ?_⟩
  simp only at huv ⊢
  rw [huv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul, add_sub_cancel]

/-- **The dilated mollification of a zero extension is a test function on `Ω`** (`Ω` bounded,
star-shaped with respect to every point of `B(x₀, s)`, `c > 1`, bump radius `< s (c - 1) / 2`). -/
theorem isTest_dil_molli_indicator (hb : Bornology.IsBounded Ω) {x₀ : E} {s : ℝ}
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {f : E → ℝ}
    (hf : LocallyIntegrable (Ω.indicator f) volume) {c : ℝ} (hc : 1 < c)
    (φ : ContDiffBump (0 : E)) (hφ : φ.rOut < s * (c - 1) / 2) :
    IsTest Ω (dil x₀ c (molli φ (Ω.indicator f))) := by
  set K := (fun p : E × E => x₀ + c⁻¹ • (p.1 + p.2 - x₀)) ''
    (closure Ω ×ˢ Metric.closedBall 0 φ.rOut)
  have hK := isCompact_dilImage hb x₀ c φ.rOut
  have hsub := support_dil_molli_indicator_subset f x₀ (by linarith : c ≠ 0) φ (Ω := Ω)
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨⟨q, v⟩, ⟨hq, hv⟩, rfl⟩
    exact dil_mem_of_starBall hstar hc hφ hq (by simpa using hv)
  refine ⟨contDiff_dil x₀ c (contDiff_molli φ hf), HasCompactSupport.intro hK fun x hx => ?_, ?_⟩
  · by_contra h
    exact hx (hsub h)
  · exact (closure_minimal hsub hK.isClosed).trans hKΩ

/-! ## Density of constrained test fields -/

/-- **Density of constrained test fields** on a bounded open `Ω` star-shaped with respect to a
ball. Let `A` be a row-homogeneous constant-coefficient operator and `u ∈ L²(Ω; ℝ^ι)` whose zero
extension `ū` satisfies `A ū = 0` in `𝒟'(E)` (tested against all of `C_c^∞(E)`: a boundary
condition, e.g. `B n = 0` on `∂Ω` for `A = div`). Then `u` is an `L²` limit of test fields
`φ ∈ C_c^∞(Ω; ℝ^ι)` with `A φ = 0` everywhere: `φ = ū ⋆ ρ` dilated towards the centre. -/
theorem exists_isTestField_ker_dist_lt {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : E} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω)
    (A : ConstCoeffOp E ℝ ι κ) {k : κ → ℕ} (hA : A.IsRowHomogeneous k) (u : L2F ℝ Ω ι)
    (hu : ∀ ψ : κ → E → ℝ, IsTestField (univ : Set E) ψ →
      ∑ i, ∫ x, Ω.indicator (u i) x * A.formalAdj.apply ψ i x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : ι → E → ℝ) (hφ : IsTestField Ω φ), A.apply φ = 0 ∧ dist u (testField hφ) < ε := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hφ : IsTestField Ω (fun i : ι => (isEmptyElim i : E → ℝ)) := fun i => isEmptyElim i
    refine ⟨_, hφ, ?_, ?_⟩
    · funext j x
      simp [ConstCoeffOp.apply]
    · rw [Subsingleton.elim u (testField hφ), dist_self]; exact hε
  have hm : ∀ i, MemLp (Ω.indicator (u i : E → ℝ)) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).2 (Lp.memLp (u i))
  have hl : ∀ i, LocallyIntegrable (Ω.indicator (u i : E → ℝ)) volume := fun i =>
    (hm i).locallyIntegrable (by norm_num)
  set N : ℝ := (Fintype.card ι : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  set ε' := ε / N with hε'd
  have hε' : 0 < ε' := by positivity
  have hex := fun i => eLpNorm_dil_molli_sub_le x₀ (hm i) hε'
  choose η hη hηP using hex
  set η₀ := Finset.univ.inf' Finset.univ_nonempty η
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff _).2 fun i _ => hη i
  have hη₀le : ∀ i, η₀ ≤ η i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set c := 1 + η₀ / 2 with hcd
  have hc : 1 < c := by linarith
  set r := min (η₀ / 2) (s * (c - 1) / 4)
  have hr : 0 < r := lt_min (by positivity) (by nlinarith)
  set φ : ContDiffBump (0 : E) := ⟨r / 2, r, by positivity, by linarith⟩
  have hφr : φ.rOut = r := rfl
  have hφs : φ.rOut < s * (c - 1) / 2 := by
    rw [hφr]
    exact (min_le_right _ _).trans_lt (by nlinarith)
  set Φ : ι → E → ℝ := fun i => dil x₀ c (molli φ (Ω.indicator (u i)))
  have hΦ : IsTestField Ω Φ := fun i => isTest_dil_molli_indicator hb hstar (hl i) hc φ hφs
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · -- `A Φ = c^k (A (ū ⋆ ρ)) ∘ dil = 0`
    funext j x
    have hρ : IsTest (univ : Set E) (φ.normed volume) :=
      ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, subset_univ _⟩
    rw [ConstCoeffOp.apply_dil hA x₀ c (fun i => contDiff_molli φ (hl i)) j x]
    have e := ConstCoeffOp.apply_convolution A hρ hl j (x₀ + c • (x - x₀))
    have h0 := hu _ (IsTestField.single j (hρ.comp_sub (x₀ + c • (x - x₀))))
    simp only [Pi.zero_apply]
    rw [show (fun i => molli φ (Ω.indicator (u i : E → ℝ))) = fun i =>
      Ω.indicator (u i : E → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ.normed volume
      from rfl, e, h0, mul_zero]
  · -- componentwise estimate
    have hcomp : ∀ i, dist (u i) (testField hΦ i) ≤ ε' := by
      intro i
      have hlt : c < 1 + η i := by linarith [hη₀le i]
      have hφη : φ.rOut < η i := by
        rw [hφr]; exact (min_le_left _ _).trans_lt (by linarith [hη₀le i])
      have hest := hηP i c hc.le hlt φ hφη
      have e1 : testField hΦ i = (hΦ i).memLp.toLp (Φ i) := rfl
      rw [e1, dist_edist, ← Lp.toLp_coeFn (u i) (Lp.memLp _), Lp.edist_toLp_toLp]
      refine ENNReal.toReal_le_of_le_ofReal hε'.le ?_
      calc eLpNorm ((u i : E → ℝ) - Φ i) 2 (volume.restrict Ω)
          = eLpNorm (Ω.indicator (u i : E → ℝ) - Φ i) 2 (volume.restrict Ω) := by
            refine eLpNorm_congr_ae ?_
            filter_upwards [indicator_ae_eq_restrict (μ := volume) (f := (u i : E → ℝ))
              hΩ.measurableSet.nullMeasurableSet] with x hx
            simp only [Pi.sub_apply, hx]
        _ ≤ eLpNorm (Ω.indicator (u i : E → ℝ) - Φ i) 2 volume :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm (Φ i - Ω.indicator (u i : E → ℝ)) 2 volume := eLpNorm_sub_comm _ _ _ _
        _ ≤ ENNReal.ofReal ε' := hest
    rw [PiLp.dist_eq_of_L2, Real.sqrt_lt' hε]
    calc ∑ i, dist (u i) (testField hΦ i) ^ 2 ≤ ∑ _i : ι, ε' ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg (hcomp i) 2
      _ = (Fintype.card ι : ℝ) * ε' ^ 2 := by simp
      _ < ε ^ 2 := by
          rw [hε'd, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
          have : (Fintype.card ι : ℝ) < N ^ 2 := by rw [hN]; nlinarith
          nlinarith [sq_nonneg ε, sq_pos_of_pos hε]

/-! ## Expansion: density of smooth fields satisfying an interior constraint

Running the dilation the other way (`c < 1`, expanding `Ω` about the centre `x₀`) after
mollifying gives fields smooth on all of `E` that satisfy an *interior* constraint pointwise on a
neighbourhood of `cl Ω`, but are not compactly supported in `Ω`. -/

/-- **Dilation with `c ≥ 1/2`** is bounded on `L²(E)`: `‖f(x₀ + c (· - x₀))‖₂ ≤ 2ⁿ ‖f‖₂`,
`n = dim E` (the norm scales by `c^{-n/2}`). -/
theorem eLpNorm_dil_le_of_half_le (x₀ : E) {c : ℝ} (hc : 1 / 2 ≤ c) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (dil x₀ c f) 2 volume ≤ 2 ^ Module.finrank ℝ E * eLpNorm f 2 volume := by
  have hcpos : 0 < c := by linarith
  have hc0 : c ≠ 0 := hcpos.ne'
  set n := Module.finrank ℝ E
  set g : E → ℝ := fun y => f ((x₀ - c • x₀) + y)
  have hmp : MeasurePreserving (fun y : E => (x₀ - c • x₀) + y) volume volume :=
    measurePreserving_add_left volume _
  have hg : AEStronglyMeasurable g volume := hf.comp_measurePreserving hmp
  have hgn : eLpNorm g 2 volume = eLpNorm f 2 volume := eLpNorm_comp_measurePreserving hf hmp
  have hmap := Measure.map_addHaar_smul (volume : Measure E) hc0
  rw [dil_eq, ← eLpNorm_map_measure (by rw [hmap]; exact hg.smul_measure _)
    (measurable_const_smul c).aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_top (by norm_num), ← hgn]
  swap; · exact hg
  have h1 : ENNReal.ofReal |(c ^ n)⁻¹| ≤ ((2 : ℝ≥0∞) ^ n) ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, ← pow_mul, show ((2 : ℝ≥0∞) ^ (n * 2)) = ENNReal.ofReal (2 ^ (n * 2))
      by rw [ENNReal.ofReal_pow (by norm_num)]; simp, ENNReal.ofReal_le_ofReal_iff (by positivity),
      abs_inv, abs_pow, abs_of_pos hcpos]
    have h2 : ((1 : ℝ) / 2) ^ n ≤ c ^ n := pow_le_pow_left₀ (by norm_num) hc n
    calc (c ^ n)⁻¹ ≤ (((1 : ℝ) / 2) ^ n)⁻¹ := inv_anti₀ (by positivity) h2
      _ = 2 ^ n := by rw [one_div, inv_pow, inv_inv]
      _ ≤ 2 ^ (n * 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : ENNReal.ofReal |(c ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal ≤ 2 ^ n := by
    have e : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
    rw [e]
    calc ENNReal.ofReal |(c ^ n)⁻¹| ^ (1 / 2 : ℝ)
        ≤ (((2 : ℝ≥0∞) ^ n) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = 2 ^ n := by rw [← ENNReal.rpow_mul]; norm_num
  rw [smul_eq_mul]
  exact mul_le_mul_left h2 _

/-- Two-sided version of `eLpNorm_dil_molli_sub_le_of_continuous`: for a continuous compactly
supported `g`, `dil x₀ c (g ⋆ ρ_φ)` is `ε`-close to `g` in `L²` once `|c - 1|` and the bump radius
are small. -/
theorem eLpNorm_dil_molli_sub_le_of_continuous_of_abs (x₀ : E) {g : E → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∀ c : ℝ, |c - 1| < η → ∀ φ : ContDiffBump (0 : E), φ.rOut < η →
      eLpNorm (dil x₀ c (molli φ g) - g) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR0, hR⟩ : ∃ R > 0, tsupport g ⊆ Metric.closedBall x₀ R := by
    obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall x₀
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hsupp : ∀ x, g x ≠ 0 → dist x x₀ ≤ R := fun x hx =>
    hR (subset_tsupport _ hx)
  set K := Metric.closedBall x₀ (2 * (R + 1))
  have hK : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  set M := (volume K).toReal
  have hKM : volume K ^ (1 / ENNReal.toReal 2) = ENNReal.ofReal (Real.sqrt M) := by
    rw [← ENNReal.ofReal_toReal hK, Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg
      ENNReal.toReal_nonneg (by norm_num)]
    norm_num
    rfl
  set ε' := ε / (Real.sqrt M + 1)
  have hε' : 0 < ε' := by positivity
  have hε'M : ε' * Real.sqrt M ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg M]
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1
    (hgs.uniformContinuous_of_continuous hgc) (ε' / 2) (by positivity)
  refine ⟨min (1 / 2) (δ / (2 * (R + 1))), by positivity, min_le_left _ _,
    fun c hc φ hφ => ?_⟩
  have hc12 : 1 / 2 ≤ c := by
    have := hc.trans_le (min_le_left _ _)
    rw [abs_lt] at this
    linarith
  have hcpos : 0 < c := by linarith
  have hφδ : φ.rOut < δ := hφ.trans_le ((min_le_right _ _).trans
    (div_le_self hδ.le (by linarith)))
  have hcR : |c - 1| * (2 * (R + 1)) < δ := by
    have : |c - 1| < δ / (2 * (R + 1)) := hc.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at this
  have hgl : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hy : ∀ x, dist (x₀ + c • (x - x₀)) x₀ = c * dist x x₀ := by
    intro x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg
      hcpos.le]
  have hyx : ∀ x, dist (x₀ + c • (x - x₀)) x = |c - 1| * dist x x₀ := by
    intro x
    rw [dist_eq_norm, dist_eq_norm, show x₀ + c • (x - x₀) - x = (c - 1) • (x - x₀) by
      rw [sub_smul, one_smul]; abel, norm_smul, Real.norm_eq_abs]
  have hpt : ∀ x, dist (dil x₀ c (molli φ g) x) (g x) ≤ ε' := by
    intro x
    set y := x₀ + c • (x - x₀)
    have h1 : dist (molli φ g y) (g y) ≤ ε' / 2 := by
      rw [molli_eq_normed_convolution]
      refine φ.dist_normed_convolution_le hgc.aestronglyMeasurable fun z hz => ?_
      exact (hδg (lt_of_lt_of_le (Metric.mem_ball.1 hz) hφδ.le)).le
    have h2 : dist (g y) (g x) ≤ ε' / 2 := by
      by_cases h : g y = 0 ∧ g x = 0
      · rw [h.1, h.2, dist_self]; positivity
      have hxR : dist x x₀ ≤ 2 * (R + 1) := by
        rcases not_and_or.1 h with h | h
        · have := hsupp y h
          rw [hy] at this
          nlinarith [dist_nonneg (x := x) (y := x₀)]
        · linarith [hsupp x h]
      refine (hδg ?_).le
      rw [hyx]
      calc |c - 1| * dist x x₀ ≤ |c - 1| * (2 * (R + 1)) :=
            mul_le_mul_of_nonneg_left hxR (abs_nonneg _)
        _ < δ := hcR
    calc dist (dil x₀ c (molli φ g) x) (g x) ≤ dist (molli φ g y) (g y) + dist (g y) (g x) :=
          dist_triangle _ _ _
      _ ≤ ε' := by linarith
  have hφ1 : φ.rOut < 1 := hφ.trans_le ((min_le_left _ _).trans (by norm_num))
  have hs1 : Function.support (dil x₀ c (molli φ g)) ⊆ K := by
    intro x hx
    have hm : x₀ + c • (x - x₀) ∈ Function.support (molli φ g) := hx
    obtain ⟨u, hu, v, hv, huv⟩ := support_convolution_subset _ hm
    rw [φ.support_normed_eq] at hv
    have hu' := hsupp u hu
    have hv' : ‖v‖ < φ.rOut := by simpa using hv
    have : dist (x₀ + c • (x - x₀)) x₀ ≤ R + 1 := by
      rw [← huv, dist_eq_norm, show u + v - x₀ = (u - x₀) + v by abel]
      calc ‖(u - x₀) + v‖ ≤ ‖u - x₀‖ + ‖v‖ := norm_add_le _ _
        _ ≤ R + 1 := by rw [← dist_eq_norm]; linarith
    rw [hy] at this
    show dist x x₀ ≤ 2 * (R + 1)
    nlinarith [dist_nonneg (x := x) (y := x₀)]
  have hs2 : Function.support g ⊆ K := fun x hx =>
    (hsupp x hx).trans (by linarith)
  have hmeas : AEStronglyMeasurable (dil x₀ c (molli φ g) - g) volume :=
    ((continuous_dil x₀ c (continuous_molli φ hgl)).sub hgc).aestronglyMeasurable
  refine (eLpNorm_sub_le_of_dist_bdd volume (by norm_num) measurableSet_closedBall.nullMeasurableSet
    hε'.le hmeas hpt hs1 hs2).trans ?_
  rw [hKM, ← ENNReal.ofReal_mul hε'.le]
  exact ENNReal.ofReal_le_ofReal hε'M

/-- **Two-sided dilated mollification converges in `L²(E)`**: for `f ∈ L²(E)` and `ε > 0`,
`x ↦ (f ⋆ ρ_φ)(x₀ + c (x - x₀))` is `ε`-close to `f` once `|c - 1|` and the bump radius are
small (`c < 1` allowed). -/
theorem eLpNorm_dil_molli_sub_le_of_abs (x₀ : E) {f : E → ℝ} (hf : MemLp f 2 volume) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∀ c : ℝ, |c - 1| < η → ∀ φ : ContDiffBump (0 : E), φ.rOut < η →
      eLpNorm (dil x₀ c (molli φ f) - f) 2 volume ≤ ENNReal.ofReal ε := by
  set N : ℝ := 2 ^ Module.finrank ℝ E with hN
  have hN0 : 0 < N := by positivity
  set ε₀ := ε / (N + 2) with hε₀d
  have hε₀ : 0 < ε₀ := by positivity
  obtain ⟨g, hgs, hgd, hfg⟩ := hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε₀
  have hgc : Continuous g := hgd.continuous
  have hgm : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport hgs
  obtain ⟨η, hη, hη2, hηg⟩ := eLpNorm_dil_molli_sub_le_of_continuous_of_abs x₀ hgc hgs hε₀
  refine ⟨η, hη, hη2, fun c hc φ hφ => ?_⟩
  have hc12 : 1 / 2 ≤ c := by
    have := hc.trans_le hη2
    rw [abs_lt] at this
    linarith
  have hfgm : MemLp (f - g) 2 volume := hf.sub hgm
  have hli : LocallyIntegrable (f - g) volume := hfgm.locallyIntegrable (by norm_num)
  have hgl : LocallyIntegrable g volume := hgc.locallyIntegrable
  have e : dil x₀ c (molli φ f) - f =
      dil x₀ c (molli φ (f - g)) + (dil x₀ c (molli φ g) - g) + -(f - g) := by
    have : f = (f - g) + g := by abel
    conv_lhs => rw [this, molli_add φ hli hgl, dil_add]
    abel
  have b1 : eLpNorm (dil x₀ c (molli φ (f - g))) 2 volume ≤ ENNReal.ofReal (N * ε₀) := by
    refine (eLpNorm_dil_le_of_half_le x₀ hc12 (continuous_molli φ hli).aestronglyMeasurable).trans
      ?_
    rw [ENNReal.ofReal_mul hN0.le, hN, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
    exact (eLpNorm_molli_le φ hfgm).trans hfg
  rw [e]
  calc eLpNorm (dil x₀ c (molli φ (f - g)) + (dil x₀ c (molli φ g) - g) + -(f - g)) 2 volume
      ≤ eLpNorm (dil x₀ c (molli φ (f - g)) + (dil x₀ c (molli φ g) - g)) 2 volume +
          eLpNorm (-(f - g)) 2 volume := eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (dil x₀ c (molli φ (f - g))) 2 volume +
          eLpNorm (dil x₀ c (molli φ g) - g) 2 volume) + eLpNorm (f - g) 2 volume := by
        rw [eLpNorm_neg]
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (ENNReal.ofReal (N * ε₀) + ENNReal.ofReal ε₀) + ENNReal.ofReal ε₀ := by
        gcongr
        exact hηg c hc φ hφ
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) hε₀.le,
          ← ENNReal.ofReal_add (by positivity) hε₀.le]
        congr 1
        rw [hε₀d]; field_simp; ring

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- **Expansion about the centre of a ball of star-shapedness.** If `Ω` is star-shaped with
respect to every point of `B(x₀, s)`, `1/2 ≤ c < 1` and `r < s (1 - c) / 4`, then for
`x ∈ cl Ω` the ball `B̄(x₀ + c (x - x₀), r)` lies in `Ω`. -/
theorem closedBall_dil_subset_of_starBall {x₀ : E} {s : ℝ}
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {c r : ℝ} (hc2 : 1 / 2 ≤ c)
    (hc1 : c < 1) (hr : r < s * (1 - c) / 4) {x : E} (hx : x ∈ closure Ω) :
    Metric.closedBall (x₀ + c • (x - x₀)) r ⊆ Ω := by
  intro t ht
  have hcpos : 0 < c := by linarith
  have hc' : 1 < c⁻¹ := one_lt_inv₀ hcpos |>.2 hc1
  have hr0 : 0 ≤ r := Metric.nonempty_closedBall.1 ⟨t, ht⟩
  have hs : 0 < s := by nlinarith
  set v : E := c⁻¹ • (t - (x₀ + c • (x - x₀)))
  have hv : ‖v‖ ≤ 2 * r := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hcpos.le), ← dist_eq_norm]
    have hd : dist t (x₀ + c • (x - x₀)) ≤ r := ht
    have hci : c⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hcpos (by norm_num)]; linarith
    exact mul_le_mul hci hd dist_nonneg (by norm_num)
  have hr' : 2 * r < s * (c⁻¹ - 1) / 2 := by
    have : 1 - c ≤ c⁻¹ - 1 := by
      have : c ≤ c⁻¹ := (le_of_lt hc1).trans hc'.le
      have h2 : c * c⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
      nlinarith
    nlinarith
  have hmem := dil_mem_of_starBall hstar hc' hr' hx hv
  convert hmem using 1
  simp only [v, inv_inv, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hcpos.ne',
    mul_inv_cancel_left₀ hcpos.ne', one_smul]
  abel

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The reflected kernel `s ↦ ρ(y - s)` of a bump supported in `B̄(0, r)` is a test function on
`Ω` when `B̄(y, r) ⊆ Ω`. -/
theorem isTest_comp_sub_of_closedBall_subset {ρ : E → ℝ} (hρ : IsTest (univ : Set E) ρ)
    {r : ℝ} (hsupp : tsupport ρ ⊆ Metric.closedBall 0 r) {y : E}
    (hy : Metric.closedBall y r ⊆ Ω) : IsTest Ω (fun s => ρ (y - s)) := by
  have hz : ∀ z, z ∉ Metric.closedBall y r → ρ (y - z) = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (by
      have := hsupp h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      rwa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev])
  refine ⟨(hρ.comp_sub y).contDiff, HasCompactSupport.intro (isCompact_closedBall y r) hz, ?_⟩
  refine (closure_minimal (fun z hz' => ?_) Metric.isClosed_closedBall).trans hy
  by_contra hc
  exact hz' (hz z hc)

/-- **Density of smooth fields satisfying an interior constraint** on a bounded open `Ω`
star-shaped with respect to a ball. Let `A` be a row-homogeneous constant-coefficient operator
and `u ∈ L²(Ω; ℝ^ι)` with `A u = 0` in `𝒟'(Ω)` (tested against `C_c^∞(Ω)` only: **no** boundary
condition). Then `u` is an `L²(Ω)` limit of fields `φ` smooth on all of `E` with `A φ = 0` at every
point of `Ω`: `φ = ū ⋆ ρ` expanded about the centre (`c < 1`), so that only points whose
`ρ`-ball lies in `Ω` are sampled. Compare `exists_isTestField_ker_dist_lt`, where a boundary
condition gives test fields. -/
theorem exists_contDiff_ker_on_dist_lt {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : E} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω)
    (A : ConstCoeffOp E ℝ ι κ) {k : κ → ℕ} (hA : A.IsRowHomogeneous k) (u : L2F ℝ Ω ι)
    (hu : ∀ ψ : κ → E → ℝ, IsTestField Ω ψ →
      ∑ i, ∫ x, Ω.indicator (u i) x * A.formalAdj.apply ψ i x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : ι → E → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)), (∀ j, ∀ x ∈ Ω, A.apply φ j x = 0) ∧
      dist u (toL2F fun i => memLp_of_continuous hΩ.measurableSet hb (hφ i).continuous) < ε := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun j x _ => ?_, ?_⟩
    · simp [ConstCoeffOp.apply]
    · rw [Subsingleton.elim u (toL2F fun i => isEmptyElim i), dist_self]; exact hε
  have hm : ∀ i, MemLp (Ω.indicator (u i : E → ℝ)) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).2 (Lp.memLp (u i))
  have hl : ∀ i, LocallyIntegrable (Ω.indicator (u i : E → ℝ)) volume := fun i =>
    (hm i).locallyIntegrable (by norm_num)
  set N : ℝ := (Fintype.card ι : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  set ε' := ε / N with hε'd
  have hε' : 0 < ε' := by positivity
  have hex := fun i => eLpNorm_dil_molli_sub_le_of_abs x₀ (hm i) hε'
  choose η hη hη2 hηP using hex
  set η₀ := Finset.univ.inf' Finset.univ_nonempty η
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff _).2 fun i _ => hη i
  have hη₀le : ∀ i, η₀ ≤ η i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨i₀⟩ := hι
  have hη₀2 : η₀ ≤ 1 / 2 := (hη₀le i₀).trans (hη2 _)
  set c := 1 - η₀ / 2 with hcd
  have hc1 : c < 1 := by linarith
  have hc2 : 1 / 2 ≤ c := by linarith
  set r := min (η₀ / 2) (s * (1 - c) / 8)
  have hr : 0 < r := lt_min (by positivity) (by nlinarith)
  set φ : ContDiffBump (0 : E) := ⟨r / 2, r, by positivity, by linarith⟩
  have hφr : φ.rOut = r := rfl
  have hφs : φ.rOut < s * (1 - c) / 4 := by
    rw [hφr]
    exact (min_le_right _ _).trans_lt (by nlinarith)
  set Φ : ι → E → ℝ := fun i => dil x₀ c (molli φ (Ω.indicator (u i)))
  have hΦ : ∀ i, ContDiff ℝ ∞ (Φ i) := fun i => contDiff_dil x₀ c (contDiff_molli φ (hl i))
  refine ⟨Φ, hΦ, fun j x hx => ?_, ?_⟩
  · -- `A Φ = c^k (A (ū ⋆ ρ)) ∘ dil`, and the kernel at the dilated point is a test field on `Ω`
    have hρ : IsTest (univ : Set E) (φ.normed volume) :=
      ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, subset_univ _⟩
    rw [ConstCoeffOp.apply_dil hA x₀ c (fun i => contDiff_molli φ (hl i)) j x]
    have e := ConstCoeffOp.apply_convolution A hρ hl j (x₀ + c • (x - x₀))
    have hball := closedBall_dil_subset_of_starBall hstar hc2 hc1 hφs (subset_closure hx)
    have hker := isTest_comp_sub_of_closedBall_subset hρ φ.tsupport_normed_eq.subset hball
    have h0 := hu _ (IsTestField.single j hker)
    rw [show (fun i => molli φ (Ω.indicator (u i : E → ℝ))) = fun i =>
      Ω.indicator (u i : E → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ.normed volume
      from rfl, e, h0, mul_zero]
  · -- componentwise estimate
    have hcomp : ∀ i, dist (u i) ((toL2F fun i => memLp_of_continuous hΩ.measurableSet hb
        (hΦ i).continuous : L2F ℝ Ω ι) i) ≤ ε' := by
      intro i
      have hlt : |c - 1| < η i := by
        rw [abs_lt]; constructor <;> linarith [hη₀le i]
      have hφη : φ.rOut < η i := by
        rw [hφr]; exact (min_le_left _ _).trans_lt (by linarith [hη₀le i])
      have hest := hηP i c hlt φ hφη
      have e1 : (toL2F fun i => memLp_of_continuous hΩ.measurableSet hb (hΦ i).continuous :
          L2F ℝ Ω ι) i = (memLp_of_continuous hΩ.measurableSet hb (hΦ i).continuous).toLp (Φ i) :=
        rfl
      rw [e1, dist_edist, ← Lp.toLp_coeFn (u i) (Lp.memLp _), Lp.edist_toLp_toLp]
      refine ENNReal.toReal_le_of_le_ofReal hε'.le ?_
      calc eLpNorm ((u i : E → ℝ) - Φ i) 2 (volume.restrict Ω)
          = eLpNorm (Ω.indicator (u i : E → ℝ) - Φ i) 2 (volume.restrict Ω) := by
            refine eLpNorm_congr_ae ?_
            filter_upwards [indicator_ae_eq_restrict (μ := volume) (f := (u i : E → ℝ))
              hΩ.measurableSet.nullMeasurableSet] with x hx
            simp only [Pi.sub_apply, hx]
        _ ≤ eLpNorm (Ω.indicator (u i : E → ℝ) - Φ i) 2 volume :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm (Φ i - Ω.indicator (u i : E → ℝ)) 2 volume := eLpNorm_sub_comm _ _ _ _
        _ ≤ ENNReal.ofReal ε' := hest
    rw [PiLp.dist_eq_of_L2, Real.sqrt_lt' hε]
    calc ∑ i, dist (u i) ((toL2F fun i => memLp_of_continuous hΩ.measurableSet hb
          (hΦ i).continuous : L2F ℝ Ω ι) i) ^ 2 ≤ ∑ _i : ι, ε' ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg (hcomp i) 2
      _ = (Fintype.card ι : ℝ) * ε' ^ 2 := by simp
      _ < ε ^ 2 := by
          rw [hε'd, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
          have : (Fintype.card ι : ℝ) < N ^ 2 := by rw [hN]; nlinarith
          nlinarith [sq_nonneg ε, sq_pos_of_pos hε]

end Feec.Domain
