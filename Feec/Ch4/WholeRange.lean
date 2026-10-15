module

public import Feec.Ch4.WholeWeak

/-!
# The whole-space curl does not have closed range

`Feec.Whole.not_isClosed_range_gradW` shows that on `ℝ³` the gradient has non-closed range: there
is no Poincaré inequality at low frequencies. This file proves the same for the row-wise curl of
`Feec.Whole.wholeComplex`, so neither differential of the whole-space complex has closed range.
Prop 4.17 and the existence theory (`Feec.Whole.prop_4_17_whole_exists`) do not use closed
range.

## Main results

* **`not_isClosed_range_curlW`**: the range of `curl : H(curl) → L²(M)` on `ℝ³` is not closed.
  The test fields are `u = curl w` with `ŵ = 𝟙_{|ξ|<r} M₀`. They are orthogonal to `ker curl`
  (`curl* = curl`), and `‖curl u‖ ≤ 2πr ‖u‖`, which contradicts every Poincaré constant as
  `r → 0`.
* `not_isClosed_range_d1_wholeComplex`: the same, stated for `wholeComplex.d1`.

## References

* [QuennevilleBelair2015], §4.2 (closed Hilbert complexes, Thm 4.2)
* [AFW2010], [BruningLesch1992] (closed range and Poincaré inequalities)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology
open MeasureTheory LinearPMap Set Filter

namespace Feec.WholeRange

open Feec.Torus Feec.Whole Feec.WholeWeak

/-- The coordinate hyperplane `{ξ | ξ₂ = 0}`. -/
def hyperplane : Submodule ℝ Freq where
  carrier := {ξ | ξ 2 = 0}
  zero_mem' := by simp
  add_mem' := fun ha hb => by simp_all
  smul_mem' := fun c x hx => by simp_all

theorem volume_hyperplane : volume (hyperplane : Set Freq) = 0 := by
  refine Measure.addHaar_submodule volume hyperplane fun h => ?_
  have : (EuclideanSpace.single 2 1 : Freq) ∈ hyperplane := h ▸ Submodule.mem_top
  simp [hyperplane] at this

/-- The test matrix `M₀ = e₀ e₀ᵀ`. -/
abbrev M₀ : Mat3 := EuclideanSpace.single (0, 0) 1

/-- The `(0, 1)` entry of `curl_ζ M₀` is `i ζ₂`. -/
theorem curlSym_M₀_apply (ζ : Freq) : curlSym ζ M₀ (0, 1) = Complex.I * ζ 2 := by
  simp [curlSym_apply, jM_apply, curlR_apply, cross]

/-- **On `ℝ³` the row-wise curl does not have closed range.** -/
theorem not_isClosed_range_curlW : ¬ IsClosed (LinearMap.range curlW.toFun : Set Whole.L2M) := by
  intro hR
  have hcl : curlW.IsClosed := isClosed_mulOp stronglyMeasurable_curlW
  obtain ⟨c, hc⟩ := (isClosed_range_iff_poincare hcl).1 hR
  set r : ℝ := 1 / (4 * Real.pi * (|c| + 1)) with hr_def
  have hr : 0 < r := by positivity
  set S := Metric.ball (0 : Freq) r
  have hball : MeasurableSet S := measurableSet_ball
  have hfin : volume S ≠ ∞ := measure_ball_lt_top.ne
  -- the symbol bound on the ball
  have hsym : ∀ ξ ∈ S, ∀ M : Mat3, ‖curlSym (freqW ξ) M‖ ≤ (2 * Real.pi * r) * ‖M‖ := by
    intro ξ hξ M
    refine (norm_curlSym_le _ _).trans ?_
    rw [norm_freqW]
    have : ‖ξ‖ < r := mem_ball_zero_iff.1 hξ
    gcongr
  set w : Whole.L2M := indicatorConstLp 2 hball hfin M₀
  have hw_ae := indicatorConstLp_coeFn (p := 2) (hs := hball) (hμs := hfin) (c := M₀)
  have hwb : ∀ᵐ ξ ∂(volume : Measure Freq),
      ‖curlSym (freqW ξ) (w ξ)‖ ≤ (2 * Real.pi * r) * ‖w ξ‖ := by
    filter_upwards [hw_ae] with ξ h
    rw [h]
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]; exact hsym ξ hξ _
    · simp [Set.indicator_of_notMem hξ]
  have hw : w ∈ curlW.domain :=
    MemLp.of_le_mul (Lp.memLp w) (aestronglyMeasurable_apply
      stronglyMeasurable_curlW.aestronglyMeasurable (Lp.aestronglyMeasurable w)) hwb
  set u : Whole.L2M := curlW ⟨w, hw⟩
  have hu_ae : u =ᵐ[volume] fun ξ => curlSym (freqW ξ) (S.indicator (fun _ => M₀) ξ) := by
    filter_upwards [coeFn_curlW ⟨w, hw⟩, hw_ae] with ξ h1 h2
    rw [h1]; exact congrArg _ h2
  have hub : ∀ᵐ ξ ∂(volume : Measure Freq),
      ‖curlSym (freqW ξ) (u ξ)‖ ≤ (2 * Real.pi * r) * ‖u ξ‖ := by
    filter_upwards [hu_ae] with ξ h
    rw [h]
    by_cases hξ : ξ ∈ S
    · exact hsym ξ hξ _
    · simp [Set.indicator_of_notMem hξ]
  have hu : u ∈ curlW.domain :=
    MemLp.of_le_mul (Lp.memLp u) (aestronglyMeasurable_apply
      stronglyMeasurable_curlW.aestronglyMeasurable (Lp.aestronglyMeasurable u)) hub
  -- `u = curl w` is orthogonal to `ker curl`
  have horth : u ∈ curlW.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hk
    rw [← inner_curlW_symm y ⟨w, hw⟩, hy, inner_zero_left]
  have h1 := hc ⟨u, hu⟩ horth
  have h2 : ‖curlW ⟨u, hu⟩‖ ≤ (2 * Real.pi * r) * ‖u‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_curlW ⟨u, hu⟩, hub] with ξ h3 h4
    rw [h3]; exact h4
  have hkey : |c| * (2 * Real.pi * r) ≤ 1 / 2 := by
    rw [hr_def]
    have hpi := Real.pi_pos
    rw [show |c| * (2 * Real.pi * (1 / (4 * Real.pi * (|c| + 1)))) = |c| / (2 * (|c| + 1)) by
      field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg c]
  have hle : ‖u‖ ≤ ‖u‖ / 2 := by
    calc ‖u‖ = ‖((⟨u, hu⟩ : curlW.domain) : Whole.L2M)‖ := rfl
      _ ≤ c * ‖curlW ⟨u, hu⟩‖ := h1
      _ ≤ |c| * ‖curlW ⟨u, hu⟩‖ := mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)
      _ ≤ |c| * ((2 * Real.pi * r) * ‖u‖) := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
      _ = (|c| * (2 * Real.pi * r)) * ‖u‖ := by ring
      _ ≤ (1 / 2) * ‖u‖ := mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
      _ = ‖u‖ / 2 := by ring
  have hu0 : u = 0 := norm_eq_zero.1 (le_antisymm (by linarith [norm_nonneg u]) (norm_nonneg u))
  -- but `u ≠ 0`: its `(0,1)` entry is `2πi ξ₂` on the ball
  have hae : ∀ᵐ ξ ∂(volume : Measure Freq), ξ ∈ S → ξ ∈ hyperplane := by
    filter_upwards [hu_ae, Lp.coeFn_zero Mat3 2 (volume : Measure Freq)] with ξ h1 h2
    intro hξ
    have h3 : curlSym (freqW ξ) M₀ = 0 := by
      rw [Set.indicator_of_mem hξ] at h1
      rw [← h1, hu0, h2, Pi.zero_apply]
    have h4 := congrArg (fun M : Mat3 => M (0, 1)) h3
    simp only [curlSym_M₀_apply, freqW] at h4
    change ξ 2 = 0
    simpa [Real.pi_ne_zero] using h4
  have hnull : volume (S \ (hyperplane : Set Freq)) = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun ξ hξ => ?_) hae
    simp only [Set.mem_ofPred_eq, not_imp]
    exact ⟨hξ.1, hξ.2⟩
  have hS : volume S = 0 :=
    measure_mono_null (fun ξ hξ => by
      by_cases h : ξ ∈ (hyperplane : Set Freq)
      · exact Or.inr h
      · exact Or.inl ⟨hξ, h⟩)
      (measure_union_null hnull volume_hyperplane)
  exact (Metric.measure_ball_pos volume (0 : Freq) hr).ne' hS

/-- The second differential of `wholeComplex` does not have closed range. -/
theorem not_isClosed_range_d1_wholeComplex :
    ¬ IsClosed (LinearMap.range wholeComplex.d1.toFun : Set Whole.L2M) :=
  not_isClosed_range_curlW

end Feec.WholeRange
