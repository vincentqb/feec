module

public import Feec.Domain.H1Restriction
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.Order.ProjIcc

/-!
# Lipschitz fields have `H¹(ℝⁿ)` data

A compactly supported Lipschitz function `F : ℝⁿ → ℝ` has weak first derivatives, its line
derivatives `∂ₘF` (defined almost everywhere by Rademacher's theorem), bounded by the Lipschitz
constant: `∫ F ∂ₘφ = -∫ (∂ₘF) φ` for every test function `φ`
(`integral_mul_fderiv_eq_of_lipschitzWith`, from Mathlib's `LipschitzWith.integral_lineDeriv_mul_eq`).
So a field of `L²(Ω; ℝ^ι)` that is almost everywhere on `Ω` the restriction of compactly supported
Lipschitz functions, bounded by `A` with Lipschitz constant `K` and supported in a set of volume
`V`, has `H¹(ℝⁿ)` data with bound `max A K · √V` (`H1Data.ofLipschitz`).

On the closed cube `[0, ½]ⁿ`, a `C¹` function on `ℝⁿ` whose values and first derivatives are
bounded by `L` on `[0, ½]ⁿ` agrees there with `χ · (f ∘ r)`, `r` the nearest-point retraction onto
`[0, ½]ⁿ` (`cubeRetract`: each coordinate clamped) and `χ` a fixed bump equal to `1` on `[0, ½]ⁿ`
(`cubeBump`); this function is Lipschitz with constant `c L` and supported in a fixed compact set,
so the fields of `L²((0, ½)ⁿ; ℝ^ι)` that are restrictions of such functions have `H¹(ℝⁿ)` data
with bound `c L`, `c` depending only on `n` (`exists_h1Data_cube`). In particular the `C²` classes
with bounded first derivatives on the closed cube (for instance `C²` forms with vanishing
tangential traces, the classes of the `C²` rates of the finite element methods on the cube) lie
in the `H¹` classes.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2, §5.8

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace NNReal ContDiff
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Domain

variable {n : ℕ}

/-! ### Weak derivatives of Lipschitz functions -/

/-- **Weak derivatives of a Lipschitz function**: `∫ F ∂ₘφ = -∫ (∂ₘF) φ` for every test function
`φ`, with `∂ₘF = lineDeriv ℝ F · eₘ`. -/
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

/-- The line derivatives of a function vanish off its topological support. -/
theorem lineDeriv_eq_zero_of_notMem_tsupport {F : (Fin n → ℝ) → ℝ} {y v : Fin n → ℝ}
    (hy : y ∉ tsupport F) : lineDeriv ℝ F y v = 0 := by
  have h : F =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hy] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  have hd : HasFDerivAt F (0 : (Fin n → ℝ) →L[ℝ] ℝ) y :=
    (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq h
  simpa using hd.hasLineDerivAt v |>.lineDeriv

/-- `‖toLp f‖ ≤ A √V` for `|f| ≤ A` supported in a set of volume `V`. -/
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

/-- **Fields of compactly supported Lipschitz functions have `H¹(ℝⁿ)` data.** If, for every
component `i`, `u_i` agrees almost everywhere on `Ω` with `F_i`, `|F_i| ≤ A`, `F_i` is
`K`-Lipschitz and vanishes off a compact set `S`, then `u` has `H¹(ℝⁿ)` data with bound
`max A K · √|S|`, the weak derivatives being the line derivatives `∂ₘF_i`. -/
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

/-! ### The closed cube -/

/-- The closed cube `[0, ½]ⁿ`. -/
def closedHalfCube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Icc 0 (1 / 2)

/-- **The nearest-point retraction onto `[0, ½]ⁿ`**: each coordinate clamped to `[0, ½]`. -/
def cubeRetract (y : Fin n → ℝ) : Fin n → ℝ := fun i => max (min (y i) (1 / 2)) 0

theorem cubeRetract_mem (y : Fin n → ℝ) : cubeRetract y ∈ closedHalfCube n := fun i _ =>
  ⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩

theorem cubeRetract_of_mem {y : Fin n → ℝ} (hy : y ∈ closedHalfCube n) : cubeRetract y = y := by
  funext i
  obtain ⟨h0, h1⟩ := hy i (mem_univ i)
  have h1' : y i ≤ 2⁻¹ := by norm_num at h1 ⊢; exact h1
  simp [cubeRetract, min_eq_left h1', max_eq_left h0]

theorem lipschitzWith_cubeRetract : LipschitzWith 1 (cubeRetract (n := n)) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  rw [Real.dist_eq]
  refine (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), ← Real.dist_eq]
  exact dist_le_pi_dist y z i

theorem convex_closedHalfCube : Convex ℝ (closedHalfCube n) :=
  convex_pi fun _ _ => convex_Icc 0 (1 / 2)

/-- The center `(¼, …, ¼)` of the cube; `[0, ½]ⁿ` is its closed ball of radius `¼`. -/
def cubeCenter (n : ℕ) : Fin n → ℝ := fun _ => 1 / 4

theorem closedHalfCube_eq_closedBall : closedHalfCube n = Metric.closedBall (cubeCenter n) (1 / 4) := by
  ext y
  rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
  refine ⟨fun hy i => ?_, fun hy i _ => ?_⟩
  · obtain ⟨h0, h1⟩ := hy i (mem_univ i)
    rw [Real.dist_eq, abs_le]; simp only [cubeCenter]; constructor <;> linarith
  · have := hy i
    rw [Real.dist_eq, abs_le] at this; simp only [cubeCenter] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **The bump of the cube**: smooth, `1` on `[0, ½]ⁿ`, with values in `[0, 1]`, supported in the
closed ball of radius `½` about the center. -/
def cubeBump (n : ℕ) : ContDiffBump (cubeCenter n) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- **`C¹` functions bounded with their derivative on `[0, ½]ⁿ` have `H¹(ℝⁿ)` data with a
universal constant**: for every family `f` of `C¹` functions on `ℝⁿ` with `|f_i| ≤ L` and
`‖Df_i‖ ≤ L` on `[0, ½]ⁿ`, a field of `L²((0, ½)ⁿ; ℝ^ι)` equal to `f` almost everywhere has
`H¹(ℝⁿ)` data with bound `c L`; `c` depends only on `n`. -/
theorem exists_h1Data_cube (n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ {ι : Type*} {Ω : Set (Fin n → ℝ)},
    MeasurableSet Ω → Ω ⊆ closedHalfCube n → ∀ {u : L2F ℝ Ω ι} (f : ι → (Fin n → ℝ) → ℝ) {L : ℝ},
    0 ≤ L → (∀ i, ContDiff ℝ 1 (f i)) → (∀ i, ∀ y ∈ closedHalfCube n, |f i y| ≤ L) →
    (∀ i, ∀ y ∈ closedHalfCube n, ‖fderiv ℝ (f i) y‖ ≤ L) →
    (∀ i, (u i : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω] f i) →
    Nonempty (H1Data Ω u (c * L)) := by
  set χ := cubeBump n
  obtain ⟨Kχ, hKχ⟩ := (χ.contDiff (n := 1)).lipschitzWith_of_hasCompactSupport
    χ.hasCompactSupport (by simp)
  set S := Metric.closedBall (cubeCenter n) (1 / 2 : ℝ)
  have hS : IsCompact S := isCompact_closedBall _ _
  refine ⟨(1 + Kχ) * √(volume.real S), by positivity,
    fun {ι Ω} hΩm hΩ {u} f {L} hL hf hb hd hu => ?_⟩
  -- `g = f ∘ r` is `L`-Lipschitz and bounded by `L`
  have hLip : ∀ i, LipschitzOnWith (Real.toNNReal L) (f i) (closedHalfCube n) := fun i =>
    convex_closedHalfCube.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y _ => ((hf i).differentiable one_ne_zero) y) (fun y hy => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL]; exact hd i y hy)
  have hg : ∀ i y z, |f i (cubeRetract y) - f i (cubeRetract z)| ≤ L * dist y z := fun i y z => by
    have h := (hLip i).dist_le_mul _ (cubeRetract_mem y) _ (cubeRetract_mem z)
    have h' := lipschitzWith_cubeRetract.dist_le_mul y z
    rw [NNReal.coe_one, one_mul] at h'
    rw [Real.coe_toNNReal _ hL, Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left h' hL)
  have hgb : ∀ i y, |f i (cubeRetract y)| ≤ L := fun i y => hb i _ (cubeRetract_mem y)
  -- `F = χ · g`
  set F : ι → (Fin n → ℝ) → ℝ := fun i y => χ y * f i (cubeRetract y) with hFdef
  have hχ1 : ∀ y, |χ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (χ.nonneg' y)]; exact χ.le_one
  have hKL : 0 ≤ (1 + (Kχ : ℝ)) * L := mul_nonneg (by positivity) hL
  have hF : ∀ i, LipschitzWith (Real.toNNReal ((1 + Kχ) * L)) (F i) := fun i => by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [Real.coe_toNNReal _ hKL, Real.dist_eq]
    have e : F i y - F i z = χ y * (f i (cubeRetract y) - f i (cubeRetract z)) +
        (χ y - χ z) * f i (cubeRetract z) := by simp only [F]; ring
    rw [e]
    have h2 := hKχ.dist_le_mul y z
    rw [Real.dist_eq] at h2
    calc |χ y * (f i (cubeRetract y) - f i (cubeRetract z)) + (χ y - χ z) * f i (cubeRetract z)|
        ≤ |χ y| * |f i (cubeRetract y) - f i (cubeRetract z)| +
            |χ y - χ z| * |f i (cubeRetract z)| := by
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
    calc |χ y| * |f i (cubeRetract y)| ≤ 1 * L := by
          gcongr
          · exact hχ1 y
          · exact hgb i y
      _ = L := one_mul L
  have hFu : ∀ i, (u i : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω] F i := fun i => by
    filter_upwards [hu i, ae_restrict_mem hΩm] with y hy hyΩ
    have hyQ := hΩ hyΩ
    have h1 : χ y = 1 := χ.one_of_mem_closedBall (by
      change y ∈ Metric.closedBall (cubeCenter n) (1 / 4)
      rw [← closedHalfCube_eq_closedBall]; exact hyQ)
    rw [hy]
    simp only [F, h1, one_mul, cubeRetract_of_mem hyQ]
  refine ⟨(H1Data.ofLipschitz F hF hS hSF hA hFu).mono ?_⟩
  rw [Real.coe_toNNReal _ hKL, max_eq_right (le_mul_of_one_le_left hL (by
    linarith [Kχ.coe_nonneg]))]
  exact le_of_eq (by ring)

end Feec.Domain
