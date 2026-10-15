module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Feec.Ch4.BoundedSalvage

/-!
# Density of smooth TSD fields in `L²(TSD₀)` on star-shaped domains ("Thm B")

`Feec.Ch4.BoundedSalvage` proves that on a bounded open `Ω ⊆ ℝ³` the closure of
`Z = L²(TSD) ∩ H̊(curl, M)` lies in the closed subspace `L²(TSD₀)` of TSD fields orthogonal to every
gradient `∇φ`, `φ ∈ C¹(ℝ³; ℝ³)` (weakly `B n = 0` on `∂Ω`), and that the obstruction
`obstr = L²(TSD) ⊓ L²(TSD₀)ᗮ` is infinite-dimensional. This file proves the converse inclusion on
domains star-shaped with respect to a ball, so that the description is exact:

* `exists_smooth_TSD_dist_lt`, `mem_closure_TSD_inter_HcurlZero_of_mem_TSD0`: if `Ω` is
  bounded, open and star-shaped with respect to every point of a ball `B(x₀, s)`, `s > 0`, every
  `B ∈ L²(TSD₀)` is an `L²` limit of fields with components in `C_c^∞(Ω)` that are pointwise
  symmetric, trace-free and divergence-free; such fields lie in `L²(TSD) ∩ H̊(curl, M)`
  (`testField_mem_TSD`, `Feec.BoundedDomain.testField_mem_HcurlZero`).
* `closure_TSD_inter_HcurlZero_eq`: hence `closure Z = L²(TSD₀)`; for convex `Ω`
  (`closure_TSD_inter_HcurlZero_eq_of_convex`, e.g. a ball, `closure_TSD_inter_HcurlZero_eq_ball`)
  the hypothesis holds automatically (`exists_starBall_of_convex`).
* `obstr_eq_of_convex`, `mem_obstr_iff_of_convex`: the obstruction space is exactly the
  orthogonal complement of `Z` in `L²(TSD)`, i.e. a TSD field is in `obstr` iff it is orthogonal to
  every TSD field in `H̊(curl, M)`.

## The mathematics

Let `B ∈ L²(TSD₀)` and let `b` be its zero extension to `ℝ³` (`zext`).
1. *Zero extension is divergence-free on `ℝ³`.* For a test field `ψ` on `ℝ³`,
   `∫_{ℝ³} b : ∇ψ = ∫_Ω B : ∇ψ = 0`, because the definition of `L²(TSD₀)` tests against gradients
   of `C¹` fields with **no** boundary condition. (For `B ∈ L²(TSD)` alone this fails: the
   constant `diag(1, -1, 0)` is TSD but not in `L²(TSD₀)`,
   `Feec.BoundedDomain.constField_diagA_not_mem_TSD0`.)
2. *Mollification* (`molli`, `b ⋆ ρ` with a normalized `ContDiffBump`): smooth, symmetric
   (`zext_symm`: the components of `B` are equal in `L²`), trace-free (`sum_molli_zext_diag`) and
   pointwise divergence-free (`sum_pd_molli_zext`, from `∂_k (b ⋆ ρ) = b ⋆ ∂_k ρ` and step 1 with
   `ψ = ρ(y - ·) e_j`). Its support lies in `Ω + B(0, r)`, `r` the bump radius.
3. *Dilation* (`dil`, `x ↦ F(x₀ + c (x - x₀))`, `c > 1`): keeps the three pointwise properties
   (`pd_dil`) and maps `closure Ω + closedBall(0, r)` into `Ω` once `r < s (c - 1) / 2`
   (`dil_mem_of_starBall`); so the result has compact support in `Ω` (`isTest_dil_molli_zext`).
4. *Convergence in `L²(ℝ³)`* (`eLpNorm_dil_molli_sub_le`): both operations are `L²`-contractions
   (`eLpNorm_molli_le`, by Cauchy–Schwarz against the probability density `ρ(x - ·)` and Tonelli;
   `eLpNorm_dil_le`, by the change of variables `x ↦ c x`), and for a continuous compactly
   supported `g` the dilated mollification converges uniformly with support in a fixed ball
   (`eLpNorm_dil_molli_sub_le_of_continuous`); the density of `C_c^∞(ℝ³)` in `L²(ℝ³)`
   (`MeasureTheory.MemLp.exist_eLpNorm_sub_le`) and an `ε/3` argument conclude. Restricting to `Ω`
   only decreases the norm.

## Status

Verified: items 1-4 and the corollaries above, for every bounded open `Ω` star-shaped with
respect to a ball (in particular every nonempty bounded open convex `Ω`). Not formalized: the
Lipschitz case (finite unions of star-shaped pieces need a partition of unity compatible with
the divergence constraint, i.e. a Bogovskii-type right inverse of `div` on symmetric trace-free
fields), and the identification `L²(TSD₀) = L²(TSD) ∩ H̊(div, M)` for Lipschitz `Ω`.

Correction: the proof of [QuennevilleBelair2015, §4.10, Prop 4.17] infers that
`H̊(curl, M) ∩ L²(TSD)` is dense in `L²(TSD)`. On a domain star-shaped with respect to a ball its
closure is exactly `L²(TSD₀)`, the TSD fields with `B n = 0` weakly on `∂Ω`, a closed subspace of
infinite codimension in `L²(TSD)` (`Feec.BoundedDomain.not_finiteDimensional_obstr` in
`Feec.Ch4.BoundedSalvageDim`).

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17 and its proof)
* [Brezis2011], Ch. 4 (convolution, mollifiers, density of `C_c` in `L^p`)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution RealInnerProductSpace

namespace Feec.BoundedDomain

/-! ## Mollification and dilation on `ℝ³` -/

/-- Mollification `f ⋆ ρ_φ` with the normalized bump `ρ_φ`. -/
def molli (φ : ContDiffBump (0 : R3)) (f : R3 → ℝ) : R3 → ℝ :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ.normed volume

/-- `(f ⋆ ρ)(x) = ∫ f(t) ρ(x - t) dt`. -/
theorem molli_apply (φ : ContDiffBump (0 : R3)) (f : R3 → ℝ) (x : R3) :
    molli φ f x = ∫ t, f t * φ.normed volume (x - t) := by
  simp [molli, convolution_def]

/-- **Mollification is an `L²`-contraction** (squared form): by Cauchy–Schwarz against the
probability density `ρ(x - ·)`, `|(f ⋆ ρ)(x)|² ≤ ∫ ρ(x - t) |f(t)|² dt`, and Tonelli. -/
theorem lintegral_sq_molli_le (φ : ContDiffBump (0 : R3)) {f : R3 → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖molli φ f x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  set ρ := φ.normed volume with hρ
  have hρc : Continuous ρ := φ.continuous_normed
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => φ.nonneg_normed y
  have hρm : ∀ x, Measurable fun t : R3 => ENNReal.ofReal (ρ (x - t)) := fun x =>
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
    set ν := volume.withDensity fun t : R3 => ENNReal.ofReal (ρ (x - t))
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
def dil (x₀ : R3) (c : ℝ) (f : R3 → ℝ) : R3 → ℝ := fun x => f (x₀ + c • (x - x₀))

/-- The dilation is a translation composed with `x ↦ c x`. -/
theorem dil_eq (x₀ : R3) (c : ℝ) (f : R3 → ℝ) :
    dil x₀ c f = (fun y => f ((x₀ - c • x₀) + y)) ∘ (c • ·) := by
  ext x
  simp only [dil, Function.comp_apply, smul_sub]
  congr 1
  abel

/-- **Dilation with `c ≥ 1` is an `L²`-contraction**: `‖f(x₀ + c (· - x₀))‖₂ = c^{-3/2} ‖f‖₂`. -/
theorem eLpNorm_dil_le (x₀ : R3) {c : ℝ} (hc : 1 ≤ c) {f : R3 → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (dil x₀ c f) 2 volume ≤ eLpNorm f 2 volume := by
  have hc0 : c ≠ 0 := by positivity
  set g : R3 → ℝ := fun y => f ((x₀ - c • x₀) + y)
  have hmp : MeasurePreserving (fun y : R3 => (x₀ - c • x₀) + y) volume volume :=
    measurePreserving_add_left volume _
  have hg : AEStronglyMeasurable g volume := hf.comp_measurePreserving hmp
  have hgn : eLpNorm g 2 volume = eLpNorm f 2 volume := eLpNorm_comp_measurePreserving hf hmp
  have hmap := Measure.map_addHaar_smul (volume : Measure R3) hc0
  rw [dil_eq, ← eLpNorm_map_measure (by rw [hmap]; exact hg.smul_measure _)
    (measurable_const_smul c).aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_top (by norm_num), ← hgn]
  swap; · exact hg
  have h1 : ENNReal.ofReal |(c ^ Module.finrank ℝ R3)⁻¹| ≤ 1 := by
    rw [ENNReal.ofReal_le_one, abs_inv, abs_pow, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hc)
  calc ENNReal.ofReal |(c ^ Module.finrank ℝ R3)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm g 2 volume
      ≤ (1 : ℝ≥0∞) * eLpNorm g 2 volume := by
        rw [smul_eq_mul]
        exact mul_le_mul_left (ENNReal.rpow_le_one h1 (by simp)) _
    _ = eLpNorm g 2 volume := one_mul _

/-- Mollifications of locally integrable functions are continuous. -/
theorem continuous_molli (φ : ContDiffBump (0 : R3)) {f : R3 → ℝ}
    (hf : LocallyIntegrable f volume) : Continuous (molli φ f) :=
  (φ.hasCompactSupport_normed).continuous_convolution_right _ hf φ.continuous_normed

/-- Dilations of continuous functions are continuous. -/
theorem continuous_dil (x₀ : R3) (c : ℝ) {f : R3 → ℝ} (hf : Continuous f) :
    Continuous (dil x₀ c f) :=
  hf.comp (by fun_prop)

/-- **Mollification is an `L²`-contraction.** -/
theorem eLpNorm_molli_le (φ : ContDiffBump (0 : R3)) {f : R3 → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm (molli φ f) 2 volume ≤ eLpNorm f 2 volume := by
  have hm := (continuous_molli φ (hf.locallyIntegrable (by norm_num))).aestronglyMeasurable
    (μ := volume)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow (lintegral_sq_molli_le φ hf.aestronglyMeasurable) (by norm_num)

/-- `f ⋆ ρ = ρ ⋆ f`, in the form used by `ContDiffBump.dist_normed_convolution_le`. -/
theorem molli_eq_normed_convolution (φ : ContDiffBump (0 : R3)) (f : R3 → ℝ) :
    molli φ f = φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  rw [molli, ← convolution_flip]
  congr 1
  ext
  simp

/-- Pointwise and support estimates for a continuous compactly supported `g`: the dilated
mollification is uniformly close to `g`, with support in a fixed ball. -/
theorem eLpNorm_dil_molli_sub_le_of_continuous (x₀ : R3) {g : R3 → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ c : ℝ, 1 ≤ c → c < 1 + η → ∀ φ : ContDiffBump (0 : R3), φ.rOut < η →
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

/-- The dilation is additive. -/
theorem dil_add (x₀ : R3) (c : ℝ) (f g : R3 → ℝ) : dil x₀ c (f + g) = dil x₀ c f + dil x₀ c g :=
  rfl

/-- Mollification is additive on locally integrable functions. -/
theorem molli_add (φ : ContDiffBump (0 : R3)) {f g : R3 → ℝ} (hf : LocallyIntegrable f volume)
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
theorem eLpNorm_dil_molli_sub_le (x₀ : R3) {f : R3 → ℝ} (hf : MemLp f 2 volume) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, ∀ c : ℝ, 1 ≤ c → c < 1 + η → ∀ φ : ContDiffBump (0 : R3), φ.rOut < η →
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
theorem contDiff_molli (φ : ContDiffBump (0 : R3)) {f : R3 → ℝ}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (molli φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_right _ hf φ.contDiff_normed

/-- Dilations of smooth functions are smooth. -/
theorem contDiff_dil (x₀ : R3) (c : ℝ) {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dil x₀ c f) :=
  hf.comp (by fun_prop)

/-- `∂_k (f ⋆ ρ) = f ⋆ ∂_k ρ`. -/
theorem pd_molli (φ : ContDiffBump (0 : R3)) {f : R3 → ℝ} (hf : LocallyIntegrable f volume)
    (k : Fin 3) (y : R3) :
    pd k (molli φ f) y = ∫ t, f t * pd k (φ.normed volume) (y - t) := by
  have hd := φ.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hf (φ.contDiff_normed (μ := volume) (n := 1)) y
  simp only [pd]
  rw [molli, hd.fderiv, convolution_precompR_apply _ hf
    (φ.hasCompactSupport_normed.fderiv ℝ)
    ((φ.contDiff_normed (μ := volume) (n := 1)).continuous_fderiv one_ne_zero)]
  simp [convolution_def]

/-- `∂_k [h(y - t)] = -(∂_k h)(y - t)`. -/
theorem pd_comp_sub {h : R3 → ℝ} (hh : Differentiable ℝ h) (y : R3) (k : Fin 3) (t : R3) :
    pd k (fun t => h (y - t)) t = -pd k h (y - t) := by
  have := ((hh (y - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub y)).fderiv
  simp only [pd]
  rw [show (fun t => h (y - t)) = h ∘ fun t => y - t from rfl, this]
  simp

/-- `∂_k (f(x₀ + c (x - x₀))) = c (∂_k f)(x₀ + c (x - x₀))`. -/
theorem pd_dil (x₀ : R3) (c : ℝ) {f : R3 → ℝ} (hf : Differentiable ℝ f) (k : Fin 3) (x : R3) :
    pd k (dil x₀ c f) x = c * pd k f (x₀ + c • (x - x₀)) := by
  have hA : HasFDerivAt (fun x : R3 => x₀ + c • (x - x₀)) (c • ContinuousLinearMap.id ℝ R3) x :=
    (((hasFDerivAt_id x).sub_const x₀).const_smul c).const_add x₀
  have := ((hf _).hasFDerivAt.comp x hA).fderiv
  simp only [pd]
  rw [show dil x₀ c f = f ∘ fun x => x₀ + c • (x - x₀) from rfl, this]
  simp

variable {Ω : Set R3}

/-- The zero extension of the components of `B ∈ L²(Ω; ℝ³ˣ³)` to `ℝ³`. -/
def zext (B : L2M Ω) (ij : Ix) : R3 → ℝ := Ω.indicator (B ij : R3 → ℝ)

/-- The zero extension of an `L²(Ω)` component is in `L²(ℝ³)`. -/
theorem memLp_zext (hΩ : IsOpen Ω) (B : L2M Ω) (ij : Ix) : MemLp (zext B ij) 2 volume :=
  (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).2 (Lp.memLp _)

/-- The zero extension is locally integrable on `ℝ³`. -/
theorem locallyIntegrable_zext (hΩ : IsOpen Ω) (B : L2M Ω) (ij : Ix) :
    LocallyIntegrable (zext B ij) volume :=
  (memLp_zext hΩ B ij).locallyIntegrable (by norm_num)

/-- **Mollification keeps the weak divergence zero**: for `B ∈ L²(TSD₀)` the mollified zero
extension is pointwise divergence-free on all of `ℝ³`. This is where the boundary condition of
`L²(TSD₀)` (testing against `∇φ` with no boundary condition on `φ`) is used: the test field
`t ↦ ρ(y - t) e_j` need not vanish on `∂Ω`. -/
theorem sum_pd_molli_zext (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω}
    (hB : B ∈ TSD0 Ω hΩ hb) (φ : ContDiffBump (0 : R3)) (j : Fin 3) (y : R3) :
    ∑ k, pd k (molli φ (zext B (j, k))) y = 0 := by
  set ρ := φ.normed volume
  have hρ : ContDiff ℝ ∞ ρ := φ.contDiff_normed
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  set ψ : Fin 3 → R3 → ℝ := fun i => if i = j then (fun t => ρ (y - t)) else 0 with hψd
  have hψ : ∀ i, ContDiff ℝ 1 (ψ i) := fun i => by
    simp only [hψd]
    split_ifs
    · exact (hρ.comp (by fun_prop : ContDiff ℝ ∞ fun t : R3 => y - t)).of_le (by simp)
    · exact contDiff_const
  have hpd : ∀ k i t, pd k (ψ i) t = if i = j then -pd k ρ (y - t) else 0 := by
    intro k i t
    by_cases hi : i = j
    · simp only [hψd, hi, ite_true]
      exact pd_comp_sub hρd y k t
    · simp only [hψd, hi, ite_false]
      simp [pd]
  have e := ((mem_TSD0 hΩ hb).1 hB).2 ψ hψ
  simp only [hpd, mul_ite, mul_zero, Fintype.sum_prod_type] at e
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at e
  calc ∑ k, pd k (molli φ (zext B (j, k))) y
      = ∑ k, ∫ t in Ω, B (j, k) t * pd k ρ (y - t) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pd_molli φ (locallyIntegrable_zext hΩ B _), zext,
          show (fun t => Ω.indicator (B (j, k) : R3 → ℝ) t * pd k ρ (y - t)) =
            Ω.indicator (fun t => B (j, k) t * pd k ρ (y - t)) from
            funext fun t => by by_cases ht : t ∈ Ω <;> simp [ht],
          integral_indicator hΩ.measurableSet]
    _ = -∑ k, ∫ t in Ω, (if j = j then B (j, k) t * -pd k ρ (y - t) else 0) := by
        simp [integral_neg]
    _ = 0 := by rw [e, neg_zero]

/-- Symmetry passes to the zero extension literally (the components are equal in `L²`). -/
theorem zext_symm {B : L2M Ω} (hB : B ∈ TSD Ω) (i j : Fin 3) : zext B (i, j) = zext B (j, i) := by
  simp only [zext, hB.1 i j]

/-- The mollification of an a.e. vanishing function vanishes. -/
theorem molli_eq_zero_of_ae (φ : ContDiffBump (0 : R3)) {f : R3 → ℝ} (hf : f =ᵐ[volume] 0)
    (y : R3) : molli φ f y = 0 := by
  rw [molli_apply]
  refine (integral_congr_ae (hf.mono fun t ht => ?_)).trans (integral_zero _ _)
  simp [ht]

/-- Trace-freeness passes to the mollified zero extension (pointwise). -/
theorem sum_molli_zext_diag (hΩ : IsOpen Ω) {B : L2M Ω} (hB : B ∈ TSD Ω)
    (φ : ContDiffBump (0 : R3)) (y : R3) : ∑ i, molli φ (zext B (i, i)) y = 0 := by
  have hl := locallyIntegrable_zext hΩ B
  have hsum : zext B (0, 0) + zext B (1, 1) + zext B (2, 2) =ᵐ[volume] 0 := by
    have h0 : (fun x => B (0, 0) x + B (1, 1) x + B (2, 2) x) =ᵐ[volume.restrict Ω] 0 := by
      have htr := hB.2.1
      simp only [Fin.sum_univ_three] at htr
      filter_upwards [Lp.coeFn_add (B (0, 0) + B (1, 1)) (B (2, 2)),
        Lp.coeFn_add (B (0, 0)) (B (1, 1)), Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
        with x h1 h2 h3
      rw [htr, h3] at h1
      simp only [Pi.add_apply, Pi.zero_apply] at h1 h2
      rw [Pi.zero_apply, ← h2, ← h1]
    have := indicator_ae_eq_zero_of_restrict_ae_eq_zero hΩ.measurableSet h0
    refine EventuallyEq.trans (Eventually.of_forall fun x => ?_) this
    simp only [zext, Pi.add_apply]
    by_cases hx : x ∈ Ω <;> simp [hx]
  rw [Fin.sum_univ_three, ← Pi.add_apply (molli φ _), ← Pi.add_apply (molli φ _ + _),
    ← molli_add φ (hl _) (hl _), ← molli_add φ ((hl _).add (hl _)) (hl _)]
  exact molli_eq_zero_of_ae φ hsum y

/-! ## Smooth TSD test fields lie in `L²(TSD) ∩ H̊(curl)` -/

/-- **Smooth compactly supported TSD fields are in `L²(TSD) ∩ H̊(curl, M)`**: a matrix field with
components in `C_c^∞(Ω)` that is pointwise symmetric, trace-free and divergence-free defines an
element of `L²(TSD)` (weak divergence by integration by parts, `integral_pd_mul`), and it lies in
`H̊(curl, M)` by definition of the graph closure (`testField_mem_HcurlZero`). -/
theorem testField_mem_TSD {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij))
    (hsym : ∀ i j, Φ (i, j) = Φ (j, i)) (htr : ∀ x, ∑ i, Φ (i, i) x = 0)
    (hdiv : ∀ j x, ∑ k, pd k (Φ (j, k)) x = 0) : testField hΦ ∈ TSD Ω := by
  set T := testField hΦ
  have hT := coeFn_testField hΦ
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [hT (i, j), hT (j, i)] with x h1 h2
    rw [h1, h2, hsym]
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (T (0, 0) + T (1, 1)) (T (2, 2)),
      Lp.coeFn_add (T (0, 0)) (T (1, 1)), hT (0, 0), hT (1, 1), hT (2, 2),
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6]
    simpa [Fin.sum_univ_three] using htr x
  · have hL : ∀ ij : Ix, ∫ x, T ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
        -∫ x, pd ij.2 (Φ ij) x * φ ij.1 x ∂volume.restrict Ω := by
      intro ij
      rw [integral_pd_mul (hΦ ij) (hφ ij.1).contDiff_one, neg_neg]
      exact integral_congr_ae ((hT ij).mono fun x hx => by simp only; rw [hx])
    simp only [hL, Finset.sum_neg_distrib, neg_eq_zero, Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← integral_finsetSum _ fun k _ => integrable_mul_of_compact
      (continuous_pd (hΦ _).contDiff_one _) ((hΦ _).pdiff _).hasCompactSupport (hφ j).continuous]
    simp only [← Finset.sum_mul, hdiv, zero_mul, integral_zero]

/-! ## Geometry: dilation moves the support inside -/

/-- **Dilation towards the center of a ball of star-shapedness.** If `Ω` is star-shaped with
respect to every point of `B(x₀, s)`, `c > 1` and `r < s (c - 1) / 2`, then
`x₀ + c⁻¹ (q + v - x₀) ∈ Ω` for every `q ∈ closure Ω` and `‖v‖ ≤ r`. -/
theorem dil_mem_of_starBall {x₀ : R3} {s : ℝ}
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {c r : ℝ} (hc : 1 < c)
    (hr : r < s * (c - 1) / 2) {q : R3} (hq : q ∈ closure Ω) {v : R3} (hv : ‖v‖ ≤ r) :
    x₀ + c⁻¹ • (q + v - x₀) ∈ Ω := by
  have hc0 : 0 < c := by linarith
  have hc1 : 0 < c - 1 := by linarith
  have hs : 0 < s := by
    have : 0 ≤ r := (norm_nonneg v).trans hv
    nlinarith
  obtain ⟨q', hq', hqq'⟩ := Metric.mem_closure_iff.1 hq (s * (c - 1) / 2) (by positivity)
  set w : R3 := (c - 1)⁻¹ • (v + (q - q'))
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

/-- The compact set containing the support of the dilated mollification. -/
theorem isCompact_dilImage (hb : Bornology.IsBounded Ω) (x₀ : R3) (c r : ℝ) :
    IsCompact ((fun p : R3 × R3 => x₀ + c⁻¹ • (p.1 + p.2 - x₀)) ''
      (closure Ω ×ˢ Metric.closedBall 0 r)) :=
  (hb.isCompact_closure.prod (isCompact_closedBall 0 r)).image (by fun_prop)

/-- The support of the dilated mollification of a zero extension lies in the image of
`closure Ω × closedBall(0, r)` under `(q, v) ↦ x₀ + c⁻¹ (q + v - x₀)`. -/
theorem support_dil_molli_zext_subset (B : L2M Ω) (ij : Ix) (x₀ : R3) {c : ℝ} (hc : c ≠ 0)
    (φ : ContDiffBump (0 : R3)) :
    Function.support (dil x₀ c (molli φ (zext B ij))) ⊆
      (fun p : R3 × R3 => x₀ + c⁻¹ • (p.1 + p.2 - x₀)) ''
        (closure Ω ×ˢ Metric.closedBall 0 φ.rOut) := by
  intro x hx
  have hm : x₀ + c • (x - x₀) ∈ Function.support (molli φ (zext B ij)) := hx
  obtain ⟨u, hu, v, hv, huv⟩ := support_convolution_subset _ hm
  rw [φ.support_normed_eq] at hv
  have hu' : u ∈ Ω := by
    by_contra h
    exact hu (Set.indicator_of_notMem h _)
  refine ⟨(u, v), ⟨subset_closure hu', Metric.ball_subset_closedBall hv⟩, ?_⟩
  simp only at huv ⊢
  rw [huv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul, add_sub_cancel]

/-- **The dilated mollification is a test function on `Ω`.** -/
theorem isTest_dil_molli_zext (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : R3} {s : ℝ}
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (B : L2M Ω) (ij : Ix)
    {c : ℝ} (hc : 1 < c) (φ : ContDiffBump (0 : R3)) (hφ : φ.rOut < s * (c - 1) / 2) :
    IsTest Ω (dil x₀ c (molli φ (zext B ij))) := by
  set K := (fun p : R3 × R3 => x₀ + c⁻¹ • (p.1 + p.2 - x₀)) ''
    (closure Ω ×ˢ Metric.closedBall 0 φ.rOut)
  have hK := isCompact_dilImage hb x₀ c φ.rOut
  have hsub := support_dil_molli_zext_subset B ij x₀ (by linarith : c ≠ 0) φ
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨⟨q, v⟩, ⟨hq, hv⟩, rfl⟩
    exact dil_mem_of_starBall hstar hc hφ hq (by simpa using hv)
  refine ⟨contDiff_dil x₀ c (contDiff_molli φ (locallyIntegrable_zext hΩ B ij)),
    HasCompactSupport.intro hK fun x hx => ?_, ?_⟩
  · by_contra h
    exact hx (hsub h)
  · exact (closure_minimal hsub hK.isClosed).trans hKΩ

/-! ## Density -/

/-- **Thm B (density of smooth TSD fields in `L²(TSD₀)`).** Let `Ω ⊆ ℝ³` be bounded, open and
star-shaped with respect to every point of a ball `B(x₀, s)`, `s > 0`. Then every
`B ∈ L²(TSD₀)` is an `L²` limit of smooth compactly supported fields in `Ω` that are pointwise
symmetric, trace-free and divergence-free (such fields lie in `L²(TSD) ∩ H̊(curl, M)`,
`testField_mem_TSD`, `testField_mem_HcurlZero`).

Proof: the zero extension `b` of `B` is weakly divergence-free on all of `ℝ³`, because the
definition of `L²(TSD₀)` tests against `∇φ` for `φ ∈ C¹(ℝ³)` with no boundary condition. The
mollification `b ⋆ ρ` is smooth, symmetric, trace-free and pointwise divergence-free
(`sum_pd_molli_zext`, `sum_molli_zext_diag`); the dilation `x ↦ (b ⋆ ρ)(x₀ + c (x - x₀))`,
`c > 1`, keeps these properties and, for a bump radius `< s (c - 1) / 2`, has compact support
in `Ω` (`isTest_dil_molli_zext`). Both operations are `L²`-contractions converging to the
identity (`eLpNorm_dil_molli_sub_le`). -/
theorem exists_smooth_TSD_dist_lt (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {B : L2M Ω}
    (hB : B ∈ TSD0 Ω hΩ hb) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Φ : Ix → R3 → ℝ) (hΦ : ∀ ij, IsTest Ω (Φ ij)), (∀ i j, Φ (i, j) = Φ (j, i)) ∧
      (∀ x, ∑ i, Φ (i, i) x = 0) ∧ (∀ j x, ∑ k, pd k (Φ (j, k)) x = 0) ∧
      dist B (testField hΦ) < ε := by
  set ε' := ε / 4 with hε'd
  have hε' : 0 < ε' := by positivity
  have hex := fun ij => eLpNorm_dil_molli_sub_le x₀ (memLp_zext hΩ B ij) hε'
  choose η hη hηP using hex
  set η₀ := Finset.univ.inf' Finset.univ_nonempty η
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff _).2 fun ij _ => hη ij
  have hη₀le : ∀ ij, η₀ ≤ η ij := fun ij => Finset.inf'_le _ (Finset.mem_univ ij)
  set c := 1 + η₀ / 2 with hcd
  have hc : 1 < c := by linarith
  set r := min (η₀ / 2) (s * (c - 1) / 4)
  have hr : 0 < r := lt_min (by positivity) (by nlinarith)
  set φ : ContDiffBump (0 : R3) := ⟨r / 2, r, by positivity, by linarith⟩
  have hφr : φ.rOut = r := rfl
  have hφs : φ.rOut < s * (c - 1) / 2 := by
    rw [hφr]
    exact (min_le_right _ _).trans_lt (by nlinarith)
  set Φ : Ix → R3 → ℝ := fun ij => dil x₀ c (molli φ (zext B ij))
  have hΦ : ∀ ij, IsTest Ω (Φ ij) := fun ij =>
    isTest_dil_molli_zext hΩ hb hstar B ij hc φ hφs
  have hBT : B ∈ TSD Ω := TSD0_le_TSD hΩ hb hB
  refine ⟨Φ, hΦ, fun i j => ?_, fun x => ?_, fun j x => ?_, ?_⟩
  · simp only [Φ, zext_symm hBT i j]
  · exact sum_molli_zext_diag hΩ hBT φ _
  · simp only [Φ]
    rw [Finset.sum_congr rfl fun k _ => pd_dil x₀ c
      ((contDiff_molli φ (locallyIntegrable_zext hΩ B _)).differentiable (by simp)) k x,
      ← Finset.mul_sum, sum_pd_molli_zext hΩ hb hB φ j, mul_zero]
  -- componentwise estimate
  have hcomp : ∀ ij, dist (B ij) (testField hΦ ij) ≤ ε' := by
    intro ij
    have hc1 : 1 ≤ c := hc.le
    have hlt : c < 1 + η ij := by linarith [hη₀le ij]
    have hφη : φ.rOut < η ij := by
      rw [hφr]; exact (min_le_left _ _).trans_lt (by linarith [hη₀le ij])
    have hest := hηP ij c hc1 hlt φ hφη
    have e1 : testField hΦ ij = (hΦ ij).memLp.toLp (Φ ij) := rfl
    rw [e1, dist_edist, ← Lp.toLp_coeFn (B ij) (Lp.memLp _), Lp.edist_toLp_toLp]
    refine ENNReal.toReal_le_of_le_ofReal hε'.le ?_
    calc eLpNorm ((B ij : R3 → ℝ) - Φ ij) 2 (volume.restrict Ω)
        = eLpNorm (zext B ij - Φ ij) 2 (volume.restrict Ω) := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [indicator_ae_eq_restrict (μ := volume) (f := (B ij : R3 → ℝ))
            hΩ.measurableSet.nullMeasurableSet] with x hx
          simp only [Pi.sub_apply, zext, hx]
      _ ≤ eLpNorm (zext B ij - Φ ij) 2 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (Φ ij - zext B ij) 2 volume := eLpNorm_sub_comm _ _ _ _
      _ ≤ ENNReal.ofReal ε' := hest
  rw [PiLp.dist_eq_of_L2, Real.sqrt_lt' hε]
  calc ∑ ij, dist (B ij) (testField hΦ ij) ^ 2 ≤ ∑ _ij : Ix, ε' ^ 2 :=
        Finset.sum_le_sum fun ij _ => pow_le_pow_left₀ dist_nonneg (hcomp ij) 2
    _ = 9 * ε' ^ 2 := by simp
    _ < ε ^ 2 := by rw [hε'd]; nlinarith

/-- **Thm B, closure form**: on a bounded open `Ω` star-shaped with respect to a ball, every
`B ∈ L²(TSD₀)` lies in the closure of `L²(TSD) ∩ H̊(curl, M)`. -/
theorem mem_closure_TSD_inter_HcurlZero_of_mem_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {B : L2M Ω}
    (hB : B ∈ TSD0 Ω hΩ hb) : B ∈ closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨Φ, hΦ, hsym, htr, hdiv, hd⟩ := exists_smooth_TSD_dist_lt hΩ hb hs hstar hB hε
  exact ⟨testField hΦ, ⟨testField_mem_TSD hΦ hsym htr hdiv, testField_mem_HcurlZero hΩ hb hΦ⟩, hd⟩

/-- **`closure (L²(TSD) ∩ H̊(curl, M)) = L²(TSD₀)`** on a bounded open `Ω` star-shaped with
respect to a ball. -/
theorem closure_TSD_inter_HcurlZero_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) = TSD0 Ω hΩ hb :=
  (closure_TSD_inter_HcurlZero_subset hΩ hb).antisymm fun _ hB =>
    mem_closure_TSD_inter_HcurlZero_of_mem_TSD0 hΩ hb hs hstar hB

/-- A nonempty open convex set is star-shaped with respect to a ball. -/
theorem exists_starBall_of_convex (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    ∃ x₀ : R3, ∃ s > 0, ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  exact ⟨x₀, s, hs, fun y hy z hz => hc.segment_subset (hsub hz) hy⟩

/-- **Thm B for convex domains** (e.g. a ball or a cube): on a nonempty bounded open convex
`Ω ⊆ ℝ³`, `closure (L²(TSD) ∩ H̊(curl, M)) = L²(TSD₀)`. -/
theorem closure_TSD_inter_HcurlZero_eq_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) = TSD0 Ω hΩ hb := by
  obtain ⟨x₀, s, hs, hstar⟩ := exists_starBall_of_convex hΩ hc hne
  exact closure_TSD_inter_HcurlZero_eq hΩ hb hs hstar

/-- The span of the closure is `L²(TSD₀)` itself. -/
theorem span_closure_TSD_inter_HcurlZero_eq_of_convex (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    Submodule.span ℝ (closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω)) = TSD0 Ω hΩ hb := by
  rw [closure_TSD_inter_HcurlZero_eq_of_convex hΩ hb hc hne, Submodule.span_eq]

/-- **The obstruction space is exactly the orthogonal complement of `L²(TSD) ∩ H̊(curl, M)` in
`L²(TSD)`** on a nonempty bounded open convex `Ω`: `obstr = L²(TSD) ⊓ (closure Z)ᗮ`. -/
theorem obstr_eq_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hc : Convex ℝ Ω)
    (hne : Ω.Nonempty) :
    obstr Ω hΩ hb = TSD Ω ⊓
      (Submodule.span ℝ (closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω)))ᗮ := by
  rw [span_closure_TSD_inter_HcurlZero_eq_of_convex hΩ hb hc hne]
  rfl

/-- **Characterization of the obstruction space** (convex `Ω`): a TSD field is in `obstr` iff it
is orthogonal to every TSD field in `H̊(curl, M)`. -/
theorem mem_obstr_iff_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hc : Convex ℝ Ω)
    (hne : Ω.Nonempty) {G : L2M Ω} :
    G ∈ obstr Ω hΩ hb ↔
      G ∈ TSD Ω ∧ ∀ Z ∈ TSD Ω, Z ∈ HcurlZero Ω → ⟪G, Z⟫ = 0 := by
  refine ⟨fun h => ⟨h.1, fun Z hZ hZ' => inner_eq_zero_of_mem_obstr hΩ hb h hZ hZ'⟩,
    fun ⟨hG, h⟩ => ⟨hG, ?_⟩⟩
  show G ∈ (TSD0 Ω hΩ hb)ᗮ
  rw [Submodule.mem_orthogonal']
  intro B hB
  rw [← SetLike.mem_coe, ← closure_TSD_inter_HcurlZero_eq_of_convex hΩ hb hc hne] at hB
  have hcl : IsClosed {B : L2M Ω | ⟪G, B⟫ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have := closure_minimal (s := (TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω)
    (fun Z (hZ : Z ∈ (TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) => h Z hZ.1 hZ.2) hcl hB
  rw [Set.mem_ofPred_eq] at this
  exact this

/-- **Thm B on a ball**: `closure (L²(TSD) ∩ H̊(curl, M)) = L²(TSD₀)` for `Ω = B(x₀, R)`. -/
theorem closure_TSD_inter_HcurlZero_eq_ball (x₀ : R3) {R : ℝ} (hR : 0 < R) :
    closure ((TSD (Metric.ball x₀ R) : Set (L2M (Metric.ball x₀ R))) ∩
      HcurlZero (Metric.ball x₀ R)) =
      TSD0 (Metric.ball x₀ R) Metric.isOpen_ball Metric.isBounded_ball :=
  closure_TSD_inter_HcurlZero_eq_of_convex _ _ (convex_ball x₀ R) (Metric.nonempty_ball.2 hR)

end Feec.BoundedDomain
