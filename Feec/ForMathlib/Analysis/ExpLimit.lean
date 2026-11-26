module

public import Feec.ForMathlib.Analysis.ExpFlow
public import Feec.ForMathlib.Analysis.StrongConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Strong limits of exponentials of bounded operators

If `e^{sB_n} → S s` strongly with `‖e^{sB_n}‖ ≤ 1` and `B_n x → v` boundedly, then
`S t x - x = ∫₀ᵗ S s v ds`, so `t ↦ S t x` has derivative `v` at `0` when `s ↦ S s v` is
continuous.
-/

open Set Filter Topology NormedSpace

@[expose] public noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `ℚ`-algebra structure on operators, for `NormedSpace.exp`. -/
local instance instNormedAlgebraRatExpLimit : NormedAlgebra ℚ (E →L[𝕜] E) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 _

theorem cauchySeq_exp_apply {B : ℕ → E →L[𝕜] E} {t : ℝ}
    (hS : ∀ n y, ‖exp ((t : 𝕜) • B n) y‖ ≤ ‖y‖)
    (hsub : ∀ n m y, ‖exp ((t : 𝕜) • B n) y - exp ((t : 𝕜) • B m) y‖ ≤ |t| * ‖B n y - B m y‖)
    {D : Set E} (hD : Dense D) (hB : ∀ y ∈ D, CauchySeq fun n => B n y) (x : E) :
    CauchySeq fun n => exp ((t : 𝕜) • B n) x := by
  refine cauchySeq_apply_of_dense hS hD (fun y hy => Metric.cauchySeq_iff.2 fun ε hε => ?_) x
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hB y hy) (ε / (|t| + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h := hN m hm n hn
  rw [dist_eq_norm] at h ⊢
  calc _ ≤ |t| * ‖B m y - B n y‖ := hsub m n y
    _ ≤ |t| * (ε / (|t| + 1)) := mul_le_mul_of_nonneg_left h.le (abs_nonneg t)
    _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg t]

theorem continuous_apply_of_lipschitz {A : E →ₗ.[𝕜] E} {S : ℝ → E →L[𝕜] E}
    (hD : Dense (A.domain : Set E)) (hS : ∀ t x, ‖S t x‖ ≤ ‖x‖)
    (hL : ∀ (x : A.domain) t s, ‖S t x - S s x‖ ≤ |t - s| * ‖A x‖) (x : E) :
    Continuous fun t => S t x := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.1 hD x ε hε
  rw [Metric.mem_ball] at hd
  refine ⟨fun t => S t d, ?_, fun t => hεu ?_⟩
  · refine (LipschitzWith.of_dist_le_mul (K := ‖A ⟨d, hdD⟩‖₊) fun t s => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, coe_nnnorm, mul_comm]
    exact hL ⟨d, hdD⟩ t s
  · rw [dist_eq_norm, ← _root_.map_sub]
    exact (hS t _).trans_lt (by rw [← dist_eq_norm, dist_comm]; exact hd)

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

theorem sub_eq_integral_of_tendsto_exp {B : ℕ → E →L[𝕜] E}
    {S : ℝ → E →L[𝕜] E} {t C : ℝ} {x v : E} (hS : ∀ s ∈ uIcc 0 t, ∀ n, ‖exp ((s : 𝕜) • B n)‖ ≤ 1)
    (hlim : ∀ s ∈ uIcc 0 t, ∀ y, Tendsto (fun n => exp ((s : 𝕜) • B n) y) atTop (𝓝 (S s y)))
    (hB : Tendsto (fun n => B n x) atTop (𝓝 v)) (hC : ∀ n, ‖B n x‖ ≤ C) :
    S t x - x = ∫ s in (0 : ℝ)..t, S s v := by
  have hcont : ∀ n, Continuous fun s : ℝ => exp ((s : 𝕜) • B n) (B n x) := fun n =>
    (B n).continuous_exp_ofReal_smul.clm_apply continuous_const
  have hftc : ∀ n, exp ((t : 𝕜) • B n) x - x = ∫ s in (0 : ℝ)..t, exp ((s : 𝕜) • B n) (B n x) := by
    intro n
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => exp ((s : 𝕜) • B n) x)
      (fun s _ => ?_) ((hcont n).intervalIntegrable _ _)]
    · simp
    · have hc : B n (exp ((s : 𝕜) • B n) x) = exp ((s : 𝕜) • B n) (B n x) :=
        congrArg (fun T : E →L[𝕜] E => T x) ((B n).commute_exp_ofReal_smul s).eq
      exact hc ▸ (B n).hasDerivAt_exp_ofReal_smul_apply x s
  have hlim' : Tendsto (fun n => ∫ s in (0 : ℝ)..t, exp ((s : 𝕜) • B n) (B n x)) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, S s v)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall fun n => (hcont n).aestronglyMeasurable) ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun n => Eventually.of_forall fun s hs => ?_
      exact ((exp ((s : 𝕜) • B n)).le_opNorm _).trans ((mul_le_mul (hS s (uIoc_subset_uIcc hs) n)
        (hC n) (norm_nonneg _) zero_le_one).trans_eq (one_mul C))
    · exact Eventually.of_forall fun s hs => tendsto_apply_of_tendsto
        (hS s (uIoc_subset_uIcc hs)) (hlim s (uIoc_subset_uIcc hs)) hB
  refine tendsto_nhds_unique ((hlim t right_mem_uIcc x).sub_const x) ?_
  simp_rw [hftc]; exact hlim'

omit [IsScalarTower ℝ 𝕜 E] in
theorem hasDerivWithinAt_of_sub_eq_integral {S : ℝ → E →L[𝕜] E} {x v : E}
    {T : Set ℝ} (hc : Continuous fun s => S s v) (h0 : S 0 = 1)
    (h : ∀ t ∈ T, S t x - x = ∫ s in (0 : ℝ)..t, S s v) (hT : (0 : ℝ) ∈ T) :
    HasDerivWithinAt (fun t => S t x) v T 0 := by
  have hd := (hc.integral_hasStrictDerivAt 0 0).hasDerivAt.const_add x
  rw [h0, one_apply_eq_self] at hd
  exact hd.hasDerivWithinAt.congr_of_mem (fun t ht => by rw [← h t ht, add_sub_cancel]) hT

end ContinuousLinearMap
