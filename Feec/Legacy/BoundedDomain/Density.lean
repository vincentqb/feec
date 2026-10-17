module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Feec.Legacy.BoundedDomain.Salvage
public import Feec.Models.BoundedDomain.Density

/-!
# Density of smooth TSD fields in `L²(TSD₀)` and `L²(TSD)` on star-shaped domains ("Thm B")

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

`Feec.Legacy.BoundedDomain.Salvage` proves that on a bounded open `Ω ⊆ ℝ³` the closure of
`Z = L²(TSD) ∩ H̊(curl, M)` lies in the closed subspace `L²(TSD₀)` of TSD fields orthogonal to every
gradient `∇φ`, `φ ∈ C¹(ℝ³; ℝ³)` (weakly `B n = 0` on `∂Ω`), and that the obstruction
`obstr = L²(TSD) ⊓ L²(TSD₀)ᗮ` is infinite-dimensional. This file proves the converse inclusion on
domains star-shaped with respect to a ball, so that the description is exact:

* `Feec.Domain.exists_isTestField_ker_dist_lt`, `Feec.Models.BoundedDomain.tsd₀_le_closure`: if `Ω` is
  bounded, open and star-shaped with respect to every point of a ball `B(x₀, s)`, `s > 0`, every
  `B ∈ L²(TSD₀)` is an `L²` limit of fields with components in `C_c^∞(Ω)` that are pointwise
  symmetric, trace-free and divergence-free; such fields lie in `L²(TSD) ∩ H̊(curl, M)`
  (`Feec.Models.BoundedDomain.testField_mem_of_tsdOp_eq_zero`, `Feec.Legacy.BoundedDomain.testField_mem_HcurlZero`).
* `closure_TSD_inter_HcurlZero_eq`: hence `closure Z = L²(TSD₀)`; for convex `Ω`
  (`closure_TSD_inter_HcurlZero_eq_of_convex`, e.g. a ball, `closure_TSD_inter_HcurlZero_eq_ball`)
  the hypothesis holds automatically (`exists_starBall_of_convex`).
* `obstr_eq`, `mem_obstr_iff` (and `_of_convex` forms): the obstruction space is exactly the
  orthogonal complement of `Z` in `L²(TSD)`, i.e. a TSD field is in `obstr` iff it is orthogonal to
  every TSD field in `H̊(curl, M)`.
* `exists_smooth_TSD_HcurlM_dist_lt`, `closure_TSD_inter_HcurlM_eq` (and `_of_convex`, `_ball`):
  without the boundary condition the density holds in full, `closure (L²(TSD) ∩ H(curl, M)) =
  L²(TSD)`: every `B ∈ L²(TSD)` is an `L²` limit of fields smooth on `ℝ³`, symmetric and
  trace-free, divergence-free on `Ω`, which lie in `L²(TSD) ∩ H(curl, M)`
  (`smoothField_mem_TSD_of_div_on`, `smoothField_mem_HcurlM`).
* `density_dichotomy`: the two `L²(TSD)` density statements that the proof of Prop 4.17 *infers*
  from its conjectured `H(div, M, 0)` densities, decided on the same domains: the `H(curl, M)` one
  holds, the `H̊(curl, M)` one fails, with closure exactly `L²(TSD₀)`.
* `density_gap`: the gap stated as an invalid inference. The literal conjectures
  (`H̊(curl, M) ∩ H(div, M, 0)` and `H(curl, M) ∩ H(div, M, 0)` dense in `H(div, M, 0)`) are true
  (`Feec.Legacy.BoundedDomain.thesisComplex_dense_literal`, `dense_HcurlM_inter_HdivZero`), yet the
  inferred `H̊(curl, M) ∩ L²(TSD)` density in `L²(TSD)` is false.
* `closure_TSD_inter_HcurlM_inter_HdivM_eq`: the `H(curl, M)` density also holds within
  `H(curl, M) ∩ H(div, M)`, the `B`-component of `D(L)` in Prop 4.17 (trivially, since
  `L²(TSD) ⊆ H(div, M)`).

## The mathematics

Let `B ∈ L²(TSD₀)` and let `b` be its zero extension to `ℝ³` (`zext`).
1. *Zero extension is divergence-free on `ℝ³`.* For a test field `ψ` on `ℝ³`,
   `∫_{ℝ³} b : ∇ψ = ∫_Ω B : ∇ψ = 0`, because the definition of `L²(TSD₀)` tests against gradients
   of `C¹` fields with **no** boundary condition. (For `B ∈ L²(TSD)` alone this fails: the
   constant `diag(1, -1, 0)` is TSD but not in `L²(TSD₀)`,
   `Feec.Legacy.BoundedDomain.constField_diagA_not_mem_TSD0`.)
2. *Mollification* (`molli`, `b ⋆ ρ` with a normalized `ContDiffBump`): smooth, symmetric
   (`zext_symm`: the components of `B` are equal in `L²`), trace-free (`sum_molli_zext_diag`) and
   pointwise divergence-free (`sum_pd_molli_zext`, from `∂_k (b ⋆ ρ) = b ⋆ ∂_k ρ` and step 1 with
   `ψ = ρ(y - ·) e_j`). Its support lies in `Ω + B(0, r)`, `r` the bump radius.
3. *Dilation* (`dil`, `x ↦ F(x₀ + c (x - x₀))`, `c > 1`): keeps the three pointwise properties
   (`pd_dil`) and maps `closure Ω + closedBall(0, r)` into `Ω` once `r < s (c - 1) / 2`
   (`dil_mem_of_starBall`); so the result has compact support in `Ω` (`Feec.Domain.isTest_dil_molli_indicator`).
4. *Convergence in `L²(ℝ³)`* (`eLpNorm_dil_molli_sub_le`): both operations are `L²`-contractions
   (`eLpNorm_molli_le`, by Cauchy–Schwarz against the probability density `ρ(x - ·)` and Tonelli;
   `eLpNorm_dil_le`, by the change of variables `x ↦ c x`), and for a continuous compactly
   supported `g` the dilated mollification converges uniformly with support in a fixed ball
   (`eLpNorm_dil_molli_sub_le_of_continuous`); the density of `C_c^∞(ℝ³)` in `L²(ℝ³)`
   (`MeasureTheory.MemLp.exist_eLpNorm_sub_le`) and an `ε`-splitting argument conclude. Restricting to `Ω`
   only decreases the norm.

For `B ∈ L²(TSD)` without the boundary condition, step 1 fails at `∂Ω`, so the order is reversed
in space: the mollified zero extension is divergence-free at every `y` whose `r`-ball lies in `Ω`
(`sum_pd_molli_zext_of_TSD`), and the *expansion* `x ↦ (b ⋆ ρ)(x₀ + c (x - x₀))`, `1/2 ≤ c < 1`,
`r < s (1 - c) / 4`, samples only such `y` for `x ∈ closure Ω`
(`closedBall_dil_subset_of_starBall`). The result is smooth on `ℝ³` and pointwise TSD on `Ω`
but not compactly supported in `Ω`, so it lies in `H(curl, M)` and not in general in
`H̊(curl, M)`. Dilation with `c ≥ 1/2` is bounded on `L²` by `8` (`eLpNorm_dil_le_eight`), which
suffices for the same `ε`-argument (`eLpNorm_dil_molli_sub_le₂`).

## Status

Verified: items 1-4, the `L²(TSD)` variant and the corollaries above, for every bounded open `Ω`
star-shaped with respect to a ball (in particular every nonempty bounded open convex `Ω`). Not
formalized: the Lipschitz case (finite unions of star-shaped pieces need a partition of unity
compatible with the divergence constraint, i.e. a Bogovskii-type right inverse of `div` on
symmetric trace-free fields), and the identification `L²(TSD₀) = L²(TSD) ∩ H̊(div, M)` for Lipschitz `Ω`.

Thesis gap: for the second hypothesis of Thm 4.5, the proof of
[QuennevilleBelair2015, §4.10, Prop 4.17] conjectures (and Prop 4.17 assumes) that
`H̊(curl, M) ∩ H(div, M, 0)` and `H(curl, M) ∩ H(div, M, 0)` are dense in `H(div, M, 0)`,
"so that" `H̊(curl, M) ∩ L²(TSD)` and `H(curl, M) ∩ L²(TSD)` are dense in `L²(TSD)`. The two
conjectures themselves are true on every bounded open `Ω`
(`Feec.Legacy.BoundedDomain.thesisComplex_dense_literal`, `dense_HcurlM_inter_HdivZero`); the error is
the inference. On a domain star-shaped with respect to a ball the inferred `H(curl, M)` density
holds (`closure_TSD_inter_HcurlM_eq`), but the inferred `H̊(curl, M)` density is false: the
closure of `H̊(curl, M) ∩ L²(TSD)` is exactly `L²(TSD₀)`, the TSD fields with `B n = 0` weakly on
`∂Ω`, a closed subspace of infinite codimension in `L²(TSD)`
(`Feec.Legacy.BoundedDomain.not_finiteDimensional_obstr` in `Feec.Legacy.BoundedDomain.SalvageDim`). Density of a
set in `H(div, M, 0)` does not give density of its intersection with the closed subspace
`L²(TSD) ⊆ H(div, M, 0)`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17 and its proof)
* [Brezis2011], Ch. 4 (convolution, mollifiers, density of `C_c` in `L^p`)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution RealInnerProductSpace

namespace Feec.Legacy.BoundedDomain

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

/-- **Dilation with `c ≥ 1` is an `L²`-contraction**: `‖f(x₀ + c (· - x₀))‖₂ ≤ ‖f‖₂`. (The norm
scales by `c^{-3/2}`; only the inequality is proved.) -/
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

/-! ## Density -/

/-- **`closure (L²(TSD) ∩ H̊(curl, M)) = L²(TSD₀)`** on a bounded open `Ω` star-shaped with
respect to a ball. -/
theorem closure_TSD_inter_HcurlZero_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) = TSD0 Ω hΩ hb := by
  have hT : TSD0 Ω hΩ hb = Feec.Models.BoundedDomain.tsd₀ Ω hΩ hb := by
    ext B
    rw [mem_TSD0, Feec.Models.BoundedDomain.mem_tsd₀, TSD_eq_tsd]
    rfl
  have hZ : (TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω = ((Feec.Models.BoundedDomain.tsd Ω ⊓
      ((Feec.Domain.curlOp 3 : Feec.Domain.ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain :
        Submodule ℝ (L2M Ω)) : Set (L2M Ω)) := by
    ext B
    rw [Submodule.coe_inf, mem_inter_iff, mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe,
      TSD_eq_tsd, mem_HcurlZero_iff_minimal]
    rfl
  rw [hT, hZ, ← Submodule.topologicalClosure_coe,
    Feec.Models.BoundedDomain.closure_eq_tsd₀ hΩ hb hs hstar]

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

/-- The span of the closure is `L²(TSD₀)` itself (star-shaped with respect to a ball). -/
theorem span_closure_TSD_inter_HcurlZero_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    Submodule.span ℝ (closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω)) = TSD0 Ω hΩ hb := by
  rw [closure_TSD_inter_HcurlZero_eq hΩ hb hs hstar, Submodule.span_eq]

/-- The span of the closure is `L²(TSD₀)` itself (convex `Ω`). -/
theorem span_closure_TSD_inter_HcurlZero_eq_of_convex (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    Submodule.span ℝ (closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω)) = TSD0 Ω hΩ hb := by
  rw [closure_TSD_inter_HcurlZero_eq_of_convex hΩ hb hc hne, Submodule.span_eq]

/-- **`obstr = L²(TSD) ⊓ (closure Z)ᗮ`** on a bounded open `Ω` star-shaped with respect to a ball,
`Z = L²(TSD) ∩ H̊(curl, M)`. Given `closure_TSD_inter_HcurlZero_eq` this is a rewrite of the
definition `obstr = L²(TSD) ⊓ L²(TSD₀)ᗮ`; the content is in `mem_obstr_iff`. -/
theorem obstr_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    obstr Ω hΩ hb = TSD Ω ⊓
      (Submodule.span ℝ (closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω)))ᗮ := by
  rw [span_closure_TSD_inter_HcurlZero_eq hΩ hb hs hstar]
  rfl

/-- `obstr_eq` for a nonempty bounded open convex `Ω`. -/
theorem obstr_eq_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hc : Convex ℝ Ω)
    (hne : Ω.Nonempty) :
    obstr Ω hΩ hb = TSD Ω ⊓
      (Submodule.span ℝ (closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω)))ᗮ := by
  obtain ⟨x₀, s, hs, hstar⟩ := exists_starBall_of_convex hΩ hc hne
  exact obstr_eq hΩ hb hs hstar

/-- **Characterization of the obstruction space** (star-shaped with respect to a ball): a TSD
field is in `obstr` iff it is orthogonal to every TSD field in `H̊(curl, M)`. -/
theorem mem_obstr_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {G : L2M Ω} :
    G ∈ obstr Ω hΩ hb ↔
      G ∈ TSD Ω ∧ ∀ Z ∈ TSD Ω, Z ∈ HcurlZero Ω → ⟪G, Z⟫ = 0 := by
  refine ⟨fun h => ⟨h.1, fun Z hZ hZ' => inner_eq_zero_of_mem_obstr hΩ hb h hZ hZ'⟩,
    fun ⟨hG, h⟩ => ⟨hG, ?_⟩⟩
  show G ∈ (TSD0 Ω hΩ hb)ᗮ
  rw [Submodule.mem_orthogonal']
  intro B hB
  rw [← SetLike.mem_coe, ← closure_TSD_inter_HcurlZero_eq hΩ hb hs hstar] at hB
  have hcl : IsClosed {B : L2M Ω | ⟪G, B⟫ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have := closure_minimal (s := (TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω)
    (fun Z (hZ : Z ∈ (TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) => h Z hZ.1 hZ.2) hcl hB
  rw [Set.mem_ofPred_eq] at this
  exact this

/-- `mem_obstr_iff` for a nonempty bounded open convex `Ω`. -/
theorem mem_obstr_iff_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hc : Convex ℝ Ω)
    (hne : Ω.Nonempty) {G : L2M Ω} :
    G ∈ obstr Ω hΩ hb ↔
      G ∈ TSD Ω ∧ ∀ Z ∈ TSD Ω, Z ∈ HcurlZero Ω → ⟪G, Z⟫ = 0 := by
  obtain ⟨x₀, s, hs, hstar⟩ := exists_starBall_of_convex hΩ hc hne
  exact mem_obstr_iff hΩ hb hs hstar

/-- **Thm B on a ball**: `closure (L²(TSD) ∩ H̊(curl, M)) = L²(TSD₀)` for `Ω = B(x₀, R)`. -/
theorem closure_TSD_inter_HcurlZero_eq_ball (x₀ : R3) {R : ℝ} (hR : 0 < R) :
    closure ((TSD (Metric.ball x₀ R) : Set (L2M (Metric.ball x₀ R))) ∩
      HcurlZero (Metric.ball x₀ R)) =
      TSD0 (Metric.ball x₀ R) Metric.isOpen_ball Metric.isBounded_ball :=
  closure_TSD_inter_HcurlZero_eq_of_convex _ _ (convex_ball x₀ R) (Metric.nonempty_ball.2 hR)

/-! ## Density of smooth TSD fields in `L²(TSD)`: the inferred `H(curl, M)` density

Running the dilation the other way (`c < 1`, expanding `Ω` about `x₀`) and mollifying gives fields
that are smooth on all of `ℝ³` and pointwise TSD on a neighbourhood of `closure Ω`, but not
compactly supported in `Ω`. They lie in `H(curl, M)` (no boundary condition). This is why the
inferred `H(curl, M)` density in the proof of Prop 4.17 holds while the inferred `H̊(curl, M)`
density fails. -/

/-- **Dilation with `c ≥ 1/2`**: `‖f(x₀ + c (· - x₀))‖₂ ≤ 8 ‖f‖₂`. (The norm scales by
`c^{-3/2}`, at most `2^{3/2} < 8` for `c ≥ 1/2`; only the bound is proved.) -/
theorem eLpNorm_dil_le_eight (x₀ : R3) {c : ℝ} (hc : 1 / 2 ≤ c) {f : R3 → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (dil x₀ c f) 2 volume ≤ 8 * eLpNorm f 2 volume := by
  have hcpos : 0 < c := by linarith
  have hc0 : c ≠ 0 := hcpos.ne'
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
  have h1 : ENNReal.ofReal |(c ^ Module.finrank ℝ R3)⁻¹| ≤ (8 : ℝ≥0∞) ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, show ((8 : ℝ≥0∞) ^ 2) = ENNReal.ofReal 64 by norm_num,
      ENNReal.ofReal_le_ofReal_iff (by norm_num), abs_inv, abs_pow, abs_of_pos hcpos,
      Module.finrank_fin_fun]
    have : (1 / 8 : ℝ) ≤ c ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hc 3]
    calc (c ^ 3)⁻¹ ≤ (1 / 8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
      _ ≤ 64 := by norm_num
  have h2 : ENNReal.ofReal |(c ^ Module.finrank ℝ R3)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal ≤ 8 := by
    have e : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
    rw [e]
    calc ENNReal.ofReal |(c ^ Module.finrank ℝ R3)⁻¹| ^ (1 / 2 : ℝ)
        ≤ ((8 : ℝ≥0∞) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = 8 := by rw [← ENNReal.rpow_mul]; norm_num
  rw [smul_eq_mul]
  exact mul_le_mul_left h2 _

/-- Two-sided version of `eLpNorm_dil_molli_sub_le_of_continuous`: for a continuous compactly
supported `g`, `dil x₀ c (g ⋆ ρ_φ)` is `ε`-close to `g` in `L²` once `|c - 1|` and the bump radius
are small. -/
theorem eLpNorm_dil_molli_sub_le_of_continuous₂ (x₀ : R3) {g : R3 → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∀ c : ℝ, |c - 1| < η → ∀ φ : ContDiffBump (0 : R3), φ.rOut < η →
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

/-- **Two-sided dilated mollification converges in `L²(ℝ³)`**: for `f ∈ L²(ℝ³)` and `ε > 0`,
`x ↦ (f ⋆ ρ_φ)(x₀ + c (x - x₀))` is `ε`-close to `f` once `|c - 1|` and the bump radius are
small (`c < 1` allowed). Same `ε`-argument as `eLpNorm_dil_molli_sub_le`, with the dilation bound
`eLpNorm_dil_le_eight` in place of the contraction. -/
theorem eLpNorm_dil_molli_sub_le₂ (x₀ : R3) {f : R3 → ℝ} (hf : MemLp f 2 volume) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∀ c : ℝ, |c - 1| < η → ∀ φ : ContDiffBump (0 : R3), φ.rOut < η →
      eLpNorm (dil x₀ c (molli φ f) - f) 2 volume ≤ ENNReal.ofReal ε := by
  have hε10 : 0 < ε / 10 := by positivity
  obtain ⟨g, hgs, hgd, hfg⟩ := hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε10
  have hgc : Continuous g := hgd.continuous
  have hgm : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport hgs
  obtain ⟨η, hη, hη2, hηg⟩ := eLpNorm_dil_molli_sub_le_of_continuous₂ x₀ hgc hgs hε10
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
  have b1 : eLpNorm (dil x₀ c (molli φ (f - g))) 2 volume ≤ ENNReal.ofReal (8 * (ε / 10)) := by
    refine (eLpNorm_dil_le_eight x₀ hc12 (continuous_molli φ hli).aestronglyMeasurable).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
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
    _ ≤ (ENNReal.ofReal (8 * (ε / 10)) + ENNReal.ofReal (ε / 10)) + ENNReal.ofReal (ε / 10) := by
        gcongr
        exact hηg c hc φ hφ
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) hε10.le,
          ← ENNReal.ofReal_add (by positivity) hε10.le]
        congr 1; ring

/-- **Mollifying a TSD field away from the boundary**: for `B ∈ L²(TSD)` (no boundary condition)
the mollified zero extension is pointwise divergence-free at every `y` with
`closedBall y r ⊆ Ω`, `r` the bump radius: the test field `t ↦ ρ(y - t) e_j` is then in
`C_c^∞(Ω)`. -/
theorem sum_pd_molli_zext_of_TSD (hΩ : IsOpen Ω) {B : L2M Ω} (hB : B ∈ TSD Ω)
    (φ : ContDiffBump (0 : R3)) (j : Fin 3) {y : R3}
    (hy : Metric.closedBall y φ.rOut ⊆ Ω) :
    ∑ k, pd k (molli φ (zext B (j, k))) y = 0 := by
  set ρ := φ.normed volume
  have hρ : ContDiff ℝ ∞ ρ := φ.contDiff_normed
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hsup : ∀ t, ρ (y - t) ≠ 0 → t ∈ Metric.closedBall y φ.rOut := by
    intro t ht
    have : y - t ∈ Function.support ρ := ht
    rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact this.le
  have hT : IsTest Ω (fun t => ρ (y - t)) := by
    refine ⟨hρ.comp (by fun_prop), HasCompactSupport.intro (isCompact_closedBall y φ.rOut)
      fun t ht => ?_, ?_⟩
    · by_contra h
      exact ht (hsup t h)
    · exact (closure_minimal (fun t ht => hsup t ht) Metric.isClosed_closedBall).trans hy
  set ψ : Fin 3 → R3 → ℝ := fun i => if i = j then (fun t => ρ (y - t)) else 0 with hψd
  have hψ : ∀ i, IsTest Ω (ψ i) := fun i => by
    simp only [hψd]
    split_ifs
    · exact hT
    · exact IsTest.zero
  have hpd : ∀ k i t, pd k (ψ i) t = if i = j then -pd k ρ (y - t) else 0 := by
    intro k i t
    by_cases hi : i = j
    · simp only [hψd, hi, ite_true]
      exact pd_comp_sub hρd y k t
    · simp only [hψd, hi, ite_false]
      simp [pd]
  have e := (mem_TSD.1 hB).2.2 ψ hψ
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

/-- **Expansion about the center of a ball of star-shapedness.** If `Ω` is star-shaped with
respect to every point of `B(x₀, s)`, `1/2 ≤ c < 1` and `r < s (1 - c) / 4`, then for
`x ∈ closure Ω` the ball `closedBall (x₀ + c (x - x₀)) r` lies in `Ω`. -/
theorem closedBall_dil_subset_of_starBall {x₀ : R3} {s : ℝ}
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {c r : ℝ} (hc2 : 1 / 2 ≤ c)
    (hc1 : c < 1) (hr : r < s * (1 - c) / 4) {x : R3} (hx : x ∈ closure Ω) :
    Metric.closedBall (x₀ + c • (x - x₀)) r ⊆ Ω := by
  intro t ht
  have hcpos : 0 < c := by linarith
  have hc' : 1 < c⁻¹ := one_lt_inv₀ hcpos |>.2 hc1
  have hr0 : 0 ≤ r := Metric.nonempty_closedBall.1 ⟨t, ht⟩
  have hs : 0 < s := by nlinarith
  set v : R3 := c⁻¹ • (t - (x₀ + c • (x - x₀)))
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

/-- A `C¹` matrix field on `ℝ³` that is symmetric, trace-free and divergence-free at every point
of `Ω` defines an element of `L²(TSD)` (weak divergence by integration by parts against
`C_c^∞(Ω)`, `integral_pd_mul`). -/
theorem smoothField_mem_TSD_of_div_on (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (hsym : ∀ i j, Ψ (i, j) = Ψ (j, i))
    (htr : ∀ x, ∑ i, Ψ (i, i) x = 0) (hdiv : ∀ j, ∀ x ∈ Ω, ∑ k, pd k (Ψ (j, k)) x = 0) :
    smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous) ∈ TSD Ω := by
  set K := smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous)
  have hKc := coeFn_smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous)
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [hKc (i, j), hKc (j, i)] with x h1 h2
    rw [h1, h2, hsym]
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (K (0, 0) + K (1, 1)) (K (2, 2)),
      Lp.coeFn_add (K (0, 0)) (K (1, 1)), hKc (0, 0), hKc (1, 1), hKc (2, 2),
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6]
    simpa [Fin.sum_univ_three] using htr x
  · have h1 : ∀ ij : Ix, ∫ x, K ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
        -∫ x, φ ij.1 x * pd ij.2 (Ψ ij) x ∂volume.restrict Ω := fun ij => by
      rw [integral_congr_ae (g := fun x => pd ij.2 (φ ij.1) x * Ψ ij x)
        ((hKc ij).mono fun x hx => by simp only; rw [hx, mul_comm]),
        integral_pd_mul (hφ ij.1) (hΨ ij) ij.2]
    simp only [h1, Fintype.sum_prod_type, Finset.sum_neg_distrib, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← integral_finsetSum _ fun j _ => integrable_mul_of_compact (hφ i).continuous
      (hφ i).hasCompactSupport (continuous_pd (hΨ _) _)]
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
    simp only [← Finset.mul_sum]
    by_cases hx : x ∈ Ω
    · rw [hdiv i x hx, mul_zero]
    · rw [(hφ i).eq_zero_of_notMem hx, zero_mul]

/-- A `C¹` matrix field on `ℝ³` lies in `H(curl, M)` (weak curl = classical curl, by integration by
parts against `C_c^∞(Ω; ℝ³ˣ³)`; no boundary condition). -/
theorem smoothField_mem_HcurlM (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous) ∈ HcurlM Ω :=
  (thesisComplex_adjoint_d1_iff hΩ hb).1 (smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
    (mem_closure_curlClosure hΩ hb) hΨ).1

/-- **Density of smooth TSD fields in `L²(TSD)`.** Let `Ω ⊆ ℝ³` be bounded, open and star-shaped
with respect to every point of a ball `B(x₀, s)`, `s > 0`. Every `B ∈ L²(TSD)` (no boundary
condition) is an `L²(Ω)` limit of fields smooth on `ℝ³` that are symmetric and trace-free
everywhere and divergence-free on `Ω`; these lie in `L²(TSD) ∩ H(curl, M)`
(`smoothField_mem_TSD_of_div_on`, `smoothField_mem_HcurlM`).

Proof: with `b` the zero extension of `B`, `b ⋆ ρ` is pointwise divergence-free at every `y`
whose `r`-ball lies in `Ω` (`sum_pd_molli_zext_of_TSD`). The expanded field
`x ↦ (b ⋆ ρ)(x₀ + c (x - x₀))`, `1/2 ≤ c < 1`, `r < s (1 - c) / 4`, only samples such `y` for
`x ∈ Ω` (`closedBall_dil_subset_of_starBall`). `L²` convergence: `eLpNorm_dil_molli_sub_le₂`. -/
theorem exists_smooth_TSD_HcurlM_dist_lt (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) {B : L2M Ω}
    (hB : B ∈ TSD Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ψ : Ix → R3 → ℝ) (hΨ : ∀ ij, ContDiff ℝ ∞ (Ψ ij)), (∀ i j, Ψ (i, j) = Ψ (j, i)) ∧
      (∀ x, ∑ i, Ψ (i, i) x = 0) ∧ (∀ j, ∀ x ∈ Ω, ∑ k, pd k (Ψ (j, k)) x = 0) ∧
      dist B (smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous)) < ε := by
  set ε' := ε / 4 with hε'd
  have hε' : 0 < ε' := by positivity
  have hex := fun ij => eLpNorm_dil_molli_sub_le₂ x₀ (memLp_zext hΩ B ij) hε'
  choose η hη hη2 hηP using hex
  set η₀ := Finset.univ.inf' Finset.univ_nonempty η
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff _).2 fun ij _ => hη ij
  have hη₀le : ∀ ij, η₀ ≤ η ij := fun ij => Finset.inf'_le _ (Finset.mem_univ ij)
  have hη₀2 : η₀ ≤ 1 / 2 := (hη₀le (0, 0)).trans (hη2 _)
  set c := 1 - η₀ / 2 with hcd
  have hc1 : c < 1 := by linarith
  have hc2 : 1 / 2 ≤ c := by linarith
  set r := min (η₀ / 2) (s * (1 - c) / 8)
  have hr : 0 < r := lt_min (by positivity) (by nlinarith)
  set φ : ContDiffBump (0 : R3) := ⟨r / 2, r, by positivity, by linarith⟩
  have hφr : φ.rOut = r := rfl
  have hφs : φ.rOut < s * (1 - c) / 4 := by
    rw [hφr]
    exact (min_le_right _ _).trans_lt (by nlinarith)
  set Ψ : Ix → R3 → ℝ := fun ij => dil x₀ c (molli φ (zext B ij))
  have hΨ : ∀ ij, ContDiff ℝ ∞ (Ψ ij) := fun ij =>
    contDiff_dil x₀ c (contDiff_molli φ (locallyIntegrable_zext hΩ B ij))
  refine ⟨Ψ, hΨ, fun i j => ?_, fun x => ?_, fun j x hx => ?_, ?_⟩
  · simp only [Ψ, zext_symm hB i j]
  · exact sum_molli_zext_diag hΩ hB φ _
  · simp only [Ψ]
    rw [Finset.sum_congr rfl fun k _ => pd_dil x₀ c
      ((contDiff_molli φ (locallyIntegrable_zext hΩ B _)).differentiable (by simp)) k x,
      ← Finset.mul_sum, sum_pd_molli_zext_of_TSD hΩ hB φ j
        (closedBall_dil_subset_of_starBall hstar hc2 hc1 hφs (subset_closure hx)), mul_zero]
  have hcomp : ∀ ij, dist (B ij) (smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous) ij) ≤ ε' := by
    intro ij
    have hlt : |c - 1| < η ij := by
      rw [abs_lt]; constructor <;> linarith [hη₀le ij]
    have hφη : φ.rOut < η ij := by
      rw [hφr]; exact (min_le_left _ _).trans_lt (by linarith [hη₀le ij])
    have hest := hηP ij c hlt φ hφη
    have e1 : smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous) ij =
        (memLp_of_continuous hΩ hb (hΨ ij).continuous).toLp (Ψ ij) := rfl
    rw [e1, dist_edist, ← Lp.toLp_coeFn (B ij) (Lp.memLp _), Lp.edist_toLp_toLp]
    refine ENNReal.toReal_le_of_le_ofReal hε'.le ?_
    calc eLpNorm ((B ij : R3 → ℝ) - Ψ ij) 2 (volume.restrict Ω)
        = eLpNorm (zext B ij - Ψ ij) 2 (volume.restrict Ω) := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [indicator_ae_eq_restrict (μ := volume) (f := (B ij : R3 → ℝ))
            hΩ.measurableSet.nullMeasurableSet] with x hx
          simp only [Pi.sub_apply, zext, hx]
      _ ≤ eLpNorm (zext B ij - Ψ ij) 2 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (Ψ ij - zext B ij) 2 volume := eLpNorm_sub_comm _ _ _ _
      _ ≤ ENNReal.ofReal ε' := hest
  rw [PiLp.dist_eq_of_L2, Real.sqrt_lt' hε]
  calc ∑ ij, dist (B ij) (smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous) ij) ^ 2
        ≤ ∑ _ij : Ix, ε' ^ 2 :=
        Finset.sum_le_sum fun ij _ => pow_le_pow_left₀ dist_nonneg (hcomp ij) 2
    _ = 9 * ε' ^ 2 := by simp
    _ < ε ^ 2 := by rw [hε'd]; nlinarith

/-- **`closure (L²(TSD) ∩ H(curl, M)) = L²(TSD)`** on a bounded open `Ω` star-shaped with respect
to a ball: the `H(curl, M)` density in `L²(TSD)` that the proof of
[QuennevilleBelair2015, Prop 4.17] infers from its conjectured `H(div, M, 0)` density holds. Compare `closure_TSD_inter_HcurlZero_eq`: with the
boundary condition of `H̊(curl, M)` the closure is the proper subspace `L²(TSD₀)`. -/
theorem closure_TSD_inter_HcurlM_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlM Ω) = TSD Ω := by
  refine (closure_minimal inter_subset_left isClosed_TSD).antisymm fun B hB => ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨Ψ, hΨ, hsym, htr, hdiv, hd⟩ := exists_smooth_TSD_HcurlM_dist_lt hΩ hb hs hstar hB hε
  have hΨ1 : ∀ ij, ContDiff ℝ 1 (Ψ ij) := fun ij => (hΨ ij).of_le (by simp)
  exact ⟨_, ⟨smoothField_mem_TSD_of_div_on hΩ hb hΨ1 hsym htr hdiv,
    smoothField_mem_HcurlM hΩ hb hΨ1⟩, hd⟩

/-- `closure (L²(TSD) ∩ H(curl, M)) = L²(TSD)` on a nonempty bounded open convex `Ω`. -/
theorem closure_TSD_inter_HcurlM_eq_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlM Ω) = TSD Ω := by
  obtain ⟨x₀, s, hs, hstar⟩ := exists_starBall_of_convex hΩ hc hne
  exact closure_TSD_inter_HcurlM_eq hΩ hb hs hstar

/-- `closure (L²(TSD) ∩ H(curl, M)) = L²(TSD)` on a ball. -/
theorem closure_TSD_inter_HcurlM_eq_ball (x₀ : R3) {R : ℝ} (hR : 0 < R) :
    closure ((TSD (Metric.ball x₀ R) : Set (L2M (Metric.ball x₀ R))) ∩
      HcurlM (Metric.ball x₀ R)) = TSD (Metric.ball x₀ R) :=
  closure_TSD_inter_HcurlM_eq_of_convex Metric.isOpen_ball Metric.isBounded_ball
    (convex_ball x₀ R) (Metric.nonempty_ball.2 hR)

/-- **The two inferred `L²(TSD)` densities of Prop 4.17, decided.** The proof of
[QuennevilleBelair2015, §4.10, Prop 4.17] conjectures densities in `H(div, M, 0)` (true,
`density_gap`) and infers from them the two statements below. On a nonempty bounded open
`Ω ⊆ ℝ³` star-shaped with respect to a ball (e.g. a ball, a cube, any nonempty bounded open
convex set):
* `closure (L²(TSD) ∩ H(curl, M)) = L²(TSD)`: the inferred `B`-field density holds;
* `closure (L²(TSD) ∩ H̊(curl, M)) = L²(TSD₀) ≠ L²(TSD)`: the inferred `E`-field density fails,
  and the closure is identified exactly (the constant `diag(1, -1, 0)` is TSD but not in it,
  `not_dense_TSD_inter_HcurlZero`).

The whole difference is the boundary condition carried by `H̊(curl, M)`. -/
theorem density_dichotomy (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlM Ω) = TSD Ω ∧
      closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) = TSD0 Ω hΩ hb ∧
      closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) ≠ TSD Ω := by
  refine ⟨closure_TSD_inter_HcurlM_eq hΩ hb hs hstar,
    closure_TSD_inter_HcurlZero_eq hΩ hb hs hstar, fun h => ?_⟩
  obtain ⟨h1, h2⟩ := not_dense_TSD_inter_HcurlZero hΩ hb hne
  exact h2 (by rw [h]; exact h1)

/-- `H̊(curl, M) ⊆ H(curl, M)`: the graph-closure limit `C` of `curl Φₙ` is a weak curl. -/
theorem HcurlZero_subset_HcurlM (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HcurlZero Ω ⊆ HcurlM Ω := by
  rintro B ⟨C, hC⟩
  exact ⟨C, fun Φ hΦ =>
    (closure_curlGraph_identity hΩ hb hC fun ij => (hΦ ij).contDiff_one).symm⟩

/-- **The literal `H(curl, M)` conjecture of Prop 4.17 holds** on every bounded open `Ω`:
`H(curl, M) ∩ H(div, M, 0)` is dense in `H(div, M, 0)` [QuennevilleBelair2015, §4.10]. It follows
from the `H̊(curl, M)` one (`thesisComplex_dense_literal`) since `H̊(curl, M) ⊆ H(curl, M)`. -/
theorem dense_HcurlM_inter_HdivZero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∀ k ∈ HdivZero Ω, k ∈ closure (HcurlM Ω ∩ HdivZero Ω) := fun k hk =>
  closure_mono (inter_subset_inter_left _ (HcurlZero_subset_HcurlM hΩ hb))
    (thesisComplex_dense_literal hΩ hb k hk)

/-- **Thesis gap in the proof of Prop 4.17, stated in Lean.** On a nonempty bounded open
`Ω ⊆ ℝ³` star-shaped with respect to a ball, the two density conjectures of
[QuennevilleBelair2015, §4.10, Prop 4.17] hold:
* `H̊(curl, M) ∩ H(div, M, 0)` is dense in `H(div, M, 0)` (`thesisComplex_dense_literal`);
* `H(curl, M) ∩ H(div, M, 0)` is dense in `H(div, M, 0)` (`dense_HcurlM_inter_HdivZero`);

and so does the inferred `H(curl, M)` density in `L²(TSD)`. The inferred `H̊(curl, M)` density does
not: `closure (L²(TSD) ∩ H̊(curl, M)) = L²(TSD₀) ≠ L²(TSD)`. So the step "so that
`H̊(curl, M) ∩ L²(TSD)` is dense in `L²(TSD)`" is an invalid inference. The first two items need
only `Ω` bounded and open. -/
theorem density_gap (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    (∀ k ∈ HdivZero Ω, k ∈ closure (HcurlZero Ω ∩ HdivZero Ω)) ∧
      (∀ k ∈ HdivZero Ω, k ∈ closure (HcurlM Ω ∩ HdivZero Ω)) ∧
      closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlM Ω) = TSD Ω ∧
      closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) = TSD0 Ω hΩ hb ∧
      closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) ≠ TSD Ω :=
  ⟨thesisComplex_dense_literal hΩ hb, dense_HcurlM_inter_HdivZero hΩ hb,
    density_dichotomy hΩ hb hne hs hstar⟩

/-- **`closure (L²(TSD) ∩ H(curl, M) ∩ H(div, M)) = L²(TSD)`** on a bounded open `Ω` star-shaped
with respect to a ball: density inside the `B`-component `H(curl, M) ∩ H(div, M)` of the domain
`D(L)` used in [QuennevilleBelair2015, Prop 4.17]. Since `L²(TSD) ⊆ H(div, M)`
(`TSD_subset_HdivM`) this is `closure_TSD_inter_HcurlM_eq` rewritten. -/
theorem closure_TSD_inter_HcurlM_inter_HdivM_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    closure ((TSD Ω : Set (L2M Ω)) ∩ (HcurlM Ω ∩ HdivM Ω)) = TSD Ω := by
  have : (TSD Ω : Set (L2M Ω)) ∩ (HcurlM Ω ∩ HdivM Ω) = (TSD Ω : Set (L2M Ω)) ∩ HcurlM Ω := by
    ext B
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, TSD_subset_HdivM h.1⟩⟩
  rw [this, closure_TSD_inter_HcurlM_eq hΩ hb hs hstar]

end Feec.Legacy.BoundedDomain
