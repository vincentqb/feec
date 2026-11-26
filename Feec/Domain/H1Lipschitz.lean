module

public import Feec.Domain.H1Restriction
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.Order.ProjIcc

/-!
# Lipschitz fields have `H¹(ℝⁿ)` data

Fields that are a.e. restrictions of compactly supported Lipschitz functions on `ℝⁿ` have
`H¹(ℝⁿ)` data, as do `C¹` functions bounded with their derivatives on a closed cube.

## Main results

* `H1Data.ofLipschitz`: fields of compactly supported Lipschitz functions have `H¹(ℝⁿ)` data.
* `exists_h1Data_closedBall`: the bound on a closed cube.
-/

open scoped InnerProductSpace RealInnerProductSpace NNReal ContDiff
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Domain

variable {n : ℕ}

/-! ### Weak derivatives of Lipschitz functions -/

theorem integral_mul_fderiv_eq_of_lipschitzWith {F : (Fin n → ℝ) → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {φ : (Fin n → ℝ) → ℝ} (hφ : IsTest univ φ) (m : Fin n) :
    ∫ y, F y * fderiv ℝ φ y (coordDir m) = -∫ y, lineDeriv ℝ F y (coordDir m) * φ y := by
  obtain ⟨D, hD⟩ := hφ.contDiff.lipschitzWith_of_hasCompactSupport hφ.hasCompactSupport
    (by simp)
  rw [hF.integral_lineDeriv_mul_eq hD hφ.hasCompactSupport (coordDir m)]
  have e : ∀ y, lineDeriv ℝ φ y (-coordDir m) * F y = -(F y * fderiv ℝ φ y (coordDir m)) :=
    fun y => by
      rw [(hφ.differentiable y).lineDeriv_eq_fderiv, map_neg]; ring
  simp_rw [e, integral_neg, neg_neg]

theorem lineDeriv_eq_zero_of_notMem_tsupport {F : (Fin n → ℝ) → ℝ} {y v : Fin n → ℝ}
    (hy : y ∉ tsupport F) : lineDeriv ℝ F y v = 0 := by
  have h : F =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hy] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  have hd : HasFDerivAt F (0 : (Fin n → ℝ) →L[ℝ] ℝ) y :=
    (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq h
  simpa using hd.hasLineDerivAt v |>.lineDeriv

theorem norm_toLp_le_of_bound {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) (hSf : ∀ y ∉ S, f y = 0) {A : ℝ} (hA : ∀ y, |f y| ≤ A)
    (hV : volume S < ⊤) : ‖hf.toLp f‖ ≤ A * √(volume.real S) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hsq : ‖hf.toLp f‖ ^ 2 = ∫ y, f y ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [hy, real_inner_eq_re_inner, RCLike.inner_apply]
    simp [sq]
  have hle : ∫ y, f y ^ 2 ≤ ∫ y, S.indicator (fun _ => A ^ 2) y := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) ?_
      (Eventually.of_forall fun y => ?_)
    · exact (integrable_indicator_iff hS).2 (integrableOn_const hV.ne)
    · by_cases hy : y ∈ S
      · rw [indicator_of_mem hy]
        exact (sq_abs (f y)).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (hA y) 2)
      · rw [indicator_of_notMem hy]; simp [hSf y hy]
  rw [integral_indicator_const _ hS, smul_eq_mul] at hle
  have h2 : ‖hf.toLp f‖ ^ 2 ≤ (A * √(volume.real S)) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt measureReal_nonneg]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- **`H¹(ℝⁿ)` data of fields of compactly supported Lipschitz functions.** -/
def H1Data.ofLipschitz {Ω : Set (Fin n → ℝ)} {ι : Type*} {u : L2F ℝ Ω ι}
    (F : ι → (Fin n → ℝ) → ℝ) {K : ℝ≥0} (hF : ∀ i, LipschitzWith K (F i))
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSF : ∀ i, ∀ y ∉ S, F i y = 0) {A : ℝ}
    (hA : ∀ i y, |F i y| ≤ A) (hu : ∀ i, (u i : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω] F i) :
    H1Data Ω u (max A K * √(volume.real S)) := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hV : volume S < ⊤ := hS.measure_lt_top
  have hcs : ∀ i, HasCompactSupport (F i) := fun i =>
    HasCompactSupport.intro hS fun y hy => hSF i y hy
  have hts : ∀ i, tsupport (F i) ⊆ S := fun i =>
    closure_minimal (fun z hz => by_contra fun hzS => hz (hSF i z hzS)) hS.isClosed
  have hG0 : ∀ i m, ∀ y ∉ S, lineDeriv ℝ (F i) y (coordDir m) = 0 := fun i m y hy =>
    lineDeriv_eq_zero_of_notMem_tsupport fun h => hy (hts i h)
  have hGb : ∀ i m y, |lineDeriv ℝ (F i) y (coordDir m)| ≤ K := fun i m y => by
    have h := norm_lineDeriv_le_of_lipschitz ℝ (x₀ := y) (v := coordDir m) (hF i)
    have hn : ‖(coordDir m : Fin n → ℝ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      by_cases hj : j = m
      · subst hj; simp [coordDir]
      · simp [coordDir, hj]
    exact (Real.norm_eq_abs _ ▸ h).trans (by nlinarith [K.coe_nonneg])
  have hmG : ∀ i m, MemLp (fun y => lineDeriv ℝ (F i) y (coordDir m)) 2 volume := fun i m => by
    have hmeas : AEStronglyMeasurable (fun y => lineDeriv ℝ (F i) y (coordDir m)) volume :=
      aestronglyMeasurable_lineDeriv (hF i).continuous volume
    have he : (fun y => lineDeriv ℝ (F i) y (coordDir m)) =
        S.indicator fun y => lineDeriv ℝ (F i) y (coordDir m) := by
      ext y
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy, hG0 i m y hy]
    rw [he, memLp_indicator_iff_restrict hSm.nullMeasurableSet]
    have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hV.ne
    exact MemLp.of_bound hmeas.restrict K (Eventually.of_forall fun y => (hGb i m y))
  refine {
    F := F
    G := fun i m y => lineDeriv ℝ (F i) y (coordDir m)
    memF := fun i => (hF i).continuous.memLp_of_hasCompactSupport (hcs i)
    memG := hmG
    weak := fun i m φ hφ => integral_mul_fderiv_eq_of_lipschitzWith (hF i) hφ m
    ae := hu
    normF := fun i => (norm_toLp_le_of_bound _ hSm (hSF i) (hA i) hV).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
    normG := fun i m => (norm_toLp_le_of_bound _ hSm (hG0 i m) (hGb i m) hV).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)) }

/-! ### Closed cubes -/

/-- **The nearest-point retraction onto the closed cube `closedBall x₀ r`** of the sup norm. -/
def ballRetract (x₀ : Fin n → ℝ) (r : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max (min (y i) (x₀ i + r)) (x₀ i - r)

theorem ballRetract_mem (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) (y : Fin n → ℝ) :
    ballRetract x₀ r y ∈ Metric.closedBall x₀ r := by
  rw [Metric.mem_closedBall, dist_pi_le_iff hr]
  intro i
  have h1 := le_max_right (min (y i) (x₀ i + r)) (x₀ i - r)
  have h2 : max (min (y i) (x₀ i + r)) (x₀ i - r) ≤ x₀ i + r :=
    max_le (min_le_right _ _) (by linarith)
  rw [Real.dist_eq, abs_le]
  simp only [ballRetract]
  constructor <;> linarith

theorem ballRetract_of_mem {x₀ y : Fin n → ℝ} {r : ℝ} (hy : y ∈ Metric.closedBall x₀ r) :
    ballRetract x₀ r y = y := by
  funext i
  have h := (dist_le_pi_dist y x₀ i).trans (Metric.mem_closedBall.1 hy)
  rw [Real.dist_eq, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  simp only [ballRetract]
  rw [min_eq_left (by linarith), max_eq_left (by linarith)]

theorem lipschitzWith_ballRetract (x₀ : Fin n → ℝ) (r : ℝ) :
    LipschitzWith 1 (ballRetract x₀ r) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  rw [Real.dist_eq]
  refine (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), ← Real.dist_eq]
  exact dist_le_pi_dist y z i

/-- **`C¹` functions bounded with their derivative on a closed cube have `H¹(ℝⁿ)` data.** -/
theorem exists_h1Data_closedBall (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ι : Type*} {Ω : Set (Fin n → ℝ)}, MeasurableSet Ω →
    Ω ⊆ Metric.closedBall x₀ r → ∀ {u : L2F ℝ Ω ι} (f : ι → (Fin n → ℝ) → ℝ) {L : ℝ},
    0 ≤ L → (∀ i, ContDiff ℝ 1 (f i)) → (∀ i, ∀ y ∈ Metric.closedBall x₀ r, |f i y| ≤ L) →
    (∀ i, ∀ y ∈ Metric.closedBall x₀ r, ‖fderiv ℝ (f i) y‖ ≤ L) →
    (∀ i, (u i : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω] f i) →
    Nonempty (H1Data Ω u (c * L)) := by
  set χ : ContDiffBump x₀ := ⟨r, 2 * r, hr, by linarith⟩
  obtain ⟨Kχ, hKχ⟩ := (χ.contDiff (n := 1)).lipschitzWith_of_hasCompactSupport
    χ.hasCompactSupport (by simp)
  set S := Metric.closedBall x₀ (2 * r)
  have hS : IsCompact S := isCompact_closedBall _ _
  refine ⟨(1 + Kχ) * √(volume.real S), by positivity,
    fun {ι Ω} hΩm hΩ {u} f {L} hL hf hb hd hu => ?_⟩
  -- `g = f ∘ ρ` is `L`-Lipschitz and bounded by `L`
  have hLip : ∀ i, LipschitzOnWith (Real.toNNReal L) (f i) (Metric.closedBall x₀ r) := fun i =>
    (convex_closedBall x₀ r).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y _ => ((hf i).differentiable one_ne_zero) y) (fun y hy => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL]; exact hd i y hy)
  have hg : ∀ i y z, |f i (ballRetract x₀ r y) - f i (ballRetract x₀ r z)| ≤ L * dist y z :=
    fun i y z => by
      have h := (hLip i).dist_le_mul _ (ballRetract_mem x₀ hr.le y) _ (ballRetract_mem x₀ hr.le z)
      have h' := (lipschitzWith_ballRetract x₀ r).dist_le_mul y z
      rw [NNReal.coe_one, one_mul] at h'
      rw [Real.coe_toNNReal _ hL, Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left h' hL)
  have hgb : ∀ i y, |f i (ballRetract x₀ r y)| ≤ L := fun i y =>
    hb i _ (ballRetract_mem x₀ hr.le y)
  -- `F = χ · g`
  set F : ι → (Fin n → ℝ) → ℝ := fun i y => χ y * f i (ballRetract x₀ r y) with hFdef
  have hχ1 : ∀ y, |χ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (χ.nonneg' y)]; exact χ.le_one
  have hKL : 0 ≤ (1 + (Kχ : ℝ)) * L := mul_nonneg (by positivity) hL
  have hF : ∀ i, LipschitzWith (Real.toNNReal ((1 + Kχ) * L)) (F i) := fun i => by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [Real.coe_toNNReal _ hKL, Real.dist_eq]
    have e : F i y - F i z = χ y * (f i (ballRetract x₀ r y) - f i (ballRetract x₀ r z)) +
        (χ y - χ z) * f i (ballRetract x₀ r z) := by simp only [F]; ring
    rw [e]
    have h2 := hKχ.dist_le_mul y z
    rw [Real.dist_eq] at h2
    calc |χ y * (f i (ballRetract x₀ r y) - f i (ballRetract x₀ r z)) +
          (χ y - χ z) * f i (ballRetract x₀ r z)|
        ≤ |χ y| * |f i (ballRetract x₀ r y) - f i (ballRetract x₀ r z)| +
            |χ y - χ z| * |f i (ballRetract x₀ r z)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (L * dist y z) + (Kχ * dist y z) * L := by
          gcongr
          · exact hχ1 y
          · exact hg i y z
          · exact hgb i z
      _ = (1 + Kχ) * L * dist y z := by ring
  have hSF : ∀ i, ∀ y ∉ S, F i y = 0 := fun i y hy => by
    have : χ y = 0 := by
      refine χ.zero_of_le_dist ?_
      rw [Metric.mem_closedBall, not_le] at hy
      exact hy.le
    simp [F, this]
  have hA : ∀ i y, |F i y| ≤ L := fun i y => by
    simp only [F, abs_mul]
    calc |χ y| * |f i (ballRetract x₀ r y)| ≤ 1 * L := by
          gcongr
          · exact hχ1 y
          · exact hgb i y
      _ = L := one_mul L
  have hFu : ∀ i, (u i : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω] F i := fun i => by
    filter_upwards [hu i, ae_restrict_mem hΩm] with y hy hyΩ
    have hyB := hΩ hyΩ
    have h1 : χ y = 1 := χ.one_of_mem_closedBall hyB
    rw [hy]
    simp only [F, h1, one_mul, ballRetract_of_mem hyB]
  refine ⟨(H1Data.ofLipschitz F hF hS hSF hA hFu).mono ?_⟩
  rw [Real.coe_toNNReal _ hKL, max_eq_right (le_mul_of_one_le_left hL (by
    linarith [Kχ.coe_nonneg]))]
  exact le_of_eq (by ring)

end Feec.Domain
