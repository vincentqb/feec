module

public import Feec.Domain.ConstCoeffOp
public import Feec.Domain.DeRham
public import Feec.ForMathlib.Analysis.Inequalities

/-!
# Restrictions of `H¹(ℝⁿ)` fields and first-order operators

A field of `L²(Ω; ℝ^ι)` that is the restriction of a field on `ℝⁿ` with weak first derivatives in
`L²` ([Evans2010], §5.2) lies in the weak domain of every first-order operator with constant
coefficients; for `d`, `d_min x` is the weak `dx` and `x ∈ D((d_min)†)` with value the weak `d*x`.

## Main results

* `H1Data.inner_eq`: integration by parts against `H¹(ℝⁿ)` data.
* `H1Data.minimal_apply`, `H1Data.mem_adjoint`: `d_min` and `(d_min)†` on forms with such data.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open MeasureTheory Set

@[expose] public noncomputable section

namespace Feec.Domain

variable {n : ℕ} {Ω : Set (Fin n → ℝ)} {ι κ : Type*}

/-- **`H¹(ℝⁿ)` data** of `u ∈ L²(Ω; ℝ^ι)`: a field on `ℝⁿ` restricting to `u`, with bound `B`. -/
structure H1Data (Ω : Set (Fin n → ℝ)) (u : L2F ℝ Ω ι) (B : ℝ) where
  /-- the field on `ℝⁿ` -/
  F : ι → (Fin n → ℝ) → ℝ
  /-- its weak first derivatives -/
  G : ι → Fin n → (Fin n → ℝ) → ℝ
  memF : ∀ i, MemLp (F i) 2 volume
  memG : ∀ i m, MemLp (G i m) 2 volume
  /-- `G_{i m} = ∂_m F_i` weakly -/
  weak : ∀ i m (φ : (Fin n → ℝ) → ℝ), IsTest univ φ →
    ∫ y, F i y * fderiv ℝ φ y (coordDir m) = -∫ y, G i m y * φ y
  /-- `u = F|_Ω` -/
  ae : ∀ i, (u i : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω] F i
  normF : ∀ i, ‖(memF i).toLp (F i)‖ ≤ B
  normG : ∀ i m, ‖(memG i m).toLp (G i m)‖ ≤ B

/-- The coefficient sum `Σ_{j, i, m} |a_{j i m}|` of a first-order operator. -/
def coefSum [Fintype ι] [Fintype κ] (a : κ → ι → Fin n → ℝ) : ℝ := ∑ j, ∑ i, ∑ m, |a j i m|

theorem coefSum_nonneg [Fintype ι] [Fintype κ] (a : κ → ι → Fin n → ℝ) : 0 ≤ coefSum a := by
  unfold coefSum; positivity

namespace H1Data

variable {u : L2F ℝ Ω ι} {B : ℝ} (h : H1Data Ω u B)

/-- The restriction of `G i m` to `Ω`. -/
def gres (i : ι) (m : Fin n) : L2 ℝ Ω := ((h.memG i m).restrict Ω).toLp (h.G i m)

/-- The weak value `w_j = Σ_{i, m} a_{j i m} G_{i m}|_Ω` of the operator with coefficients `a`. -/
def weak' [Fintype ι] (a : κ → ι → Fin n → ℝ) : L2F ℝ Ω κ :=
  WithLp.toLp 2 fun j => ∑ i, ∑ m, a j i m • h.gres i m

theorem norm_toLp_restrict_le {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    ‖(hf.restrict Ω).toLp f‖ ≤ ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem norm_gres_le (i : ι) (m : Fin n) : ‖h.gres i m‖ ≤ B :=
  (norm_toLp_restrict_le (h.memG i m)).trans (h.normG i m)

theorem eq_toL2F [Fintype ι] : u = toL2F (fun i => (h.memF i).restrict Ω) := by
  refine PiLp.ext fun i => Lp.ext ?_
  exact (h.ae i).trans (((h.memF i).restrict Ω).coeFn_toLp).symm

theorem norm_weak_le [Fintype ι] [Fintype κ] (a : κ → ι → Fin n → ℝ) :
    ‖h.weak' a‖ ≤ coefSum a * B := by
  rw [coefSum, Finset.sum_mul]
  refine (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h.norm_gres_le i m) (abs_nonneg _)

include h in
theorem norm_le [Fintype ι] : ‖u‖ ≤ Fintype.card ι * B := by
  rw [h.eq_toL2F, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact (norm_toLp_restrict_le (h.memF i)).trans (h.normF i)

theorem inner_toL2_gres {φ : (Fin n → ℝ) → ℝ} (hφ : IsTest Ω φ) (i : ι) (m : Fin n) :
    ⟪h.gres i m, toL2 hφ⟫ = ∫ y, h.G i m y * φ y := by
  rw [toL2, inner_toLp, ← integral_restrict_of_eq_zero (Ω := Ω) fun x hx => by
    rw [hφ.eq_zero_of_notMem hx, mul_zero]]
  refine integral_congr_ae ?_
  filter_upwards [((h.memG i m).restrict Ω).coeFn_toLp] with x hx
  simp [gres, hx]

/-- **Integration by parts against `H¹(ℝⁿ)` data**: `⟪u, Aᵗ φ⟫ = ⟪w, φ⟫` for test fields `φ`. -/
theorem inner_eq [Fintype ι] [Fintype κ] (a : κ → ι → Fin n → ℝ) {φ : κ → (Fin n → ℝ) → ℝ}
    (hφ : IsTestField Ω φ)
    {ψ : ι → (Fin n → ℝ) → ℝ} (hψ : IsTestField Ω ψ)
    (hψφ : ∀ i x, ψ i x = -∑ j, ∑ m, a j i m * fderiv ℝ (φ j) x (coordDir m)) :
    ⟪u, testField hψ⟫ = ⟪h.weak' a, testField hφ⟫ := by
  have hd : ∀ j m, IsTest univ (fun x => fderiv ℝ (φ j) x (coordDir m)) := fun j m =>
    ((hφ j).fderiv_apply _).mono (subset_univ _)
  have hint : ∀ i j m, Integrable (fun y => h.F i y * fderiv ℝ (φ j) y (coordDir m)) :=
    fun i j m => (h.memF i).integrable_mul
      ((hd j m).continuous.memLp_of_hasCompactSupport (p := 2) (hd j m).hasCompactSupport)
  have hL : ⟪u, testField hψ⟫ = ∑ i, ∑ j, ∑ m, a j i m * ∫ y, h.G i m y * φ j y := by
    rw [real_inner_comm]
    refine (congrArg (fun v => ⟪testField hψ, v⟫) h.eq_toL2F).trans ?_
    rw [inner_testField_toL2F]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun x => (starRingEnd ℝ) (ψ i x) * h.F i x) = fun x =>
        ∑ j, ∑ m, -a j i m * (h.F i x * fderiv ℝ (φ j) x (coordDir m)) := by
      funext x
      rw [starRingEnd_apply, star_trivial, hψφ, neg_mul, Finset.sum_mul,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [e, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun m _ =>
      (hint i j m).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun m _ => (hint i j m).const_mul _]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, h.weak i m _ ((hφ j).mono (subset_univ _))]
    ring
  have hR : ⟪h.weak' a, testField hφ⟫ = ∑ j, ∑ i, ∑ m, a j i m * ∫ y, h.G i m y * φ j y := by
    rw [L2F.inner_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ⟪∑ i, ∑ m, a j i m • h.gres i m, toL2 (hφ j)⟫ = _
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_inner]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [real_inner_smul_left, h.inner_toL2_gres (hφ j)]
  rw [hL, hR, Finset.sum_comm]

end H1Data

namespace H1Data

variable {u : L2F ℝ Ω ι} {B : ℝ}

/-- A larger bound. -/
def mono (h : H1Data Ω u B) {B' : ℝ} (hB : B ≤ B') : H1Data Ω u B' :=
  { h with
    normF := fun i => (h.normF i).trans hB
    normG := fun i m => (h.normG i m).trans hB }

/-- `c u` has the data `c F`, `c G`, with bound `|c| B`. -/
def smul (h : H1Data Ω u B) (c : ℝ) : H1Data Ω (c • u) (|c| * B) where
  F i := c • h.F i
  G i m := c • h.G i m
  memF i := (h.memF i).const_smul c
  memG i m := (h.memG i m).const_smul c
  weak i m φ hφ := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, h.weak i m φ hφ]
    ring
  ae i := by
    filter_upwards [Lp.coeFn_smul c (u i), h.ae i] with y h1 h2
    simp only [PiLp.smul_apply] at h1 ⊢
    rw [h1, Pi.smul_apply, h2, Pi.smul_apply]
  normF i := by
    rw [MemLp.toLp_const_smul, norm_smul, Real.norm_eq_abs]
    · exact mul_le_mul_of_nonneg_left (h.normF i) (abs_nonneg c)
    · exact h.memF i
  normG i m := by
    rw [MemLp.toLp_const_smul, norm_smul, Real.norm_eq_abs]
    · exact mul_le_mul_of_nonneg_left (h.normG i m) (abs_nonneg c)
    · exact h.memG i m

/-- The zero field has the zero data. -/
def zero : H1Data Ω (0 : L2F ℝ Ω ι) 0 where
  F _ := 0
  G _ _ := 0
  memF _ := MemLp.zero
  memG _ _ := MemLp.zero
  weak _ _ _ _ := by simp
  ae _ := by
    simp only [PiLp.zero_apply]
    exact Lp.coeFn_zero _ _ _
  normF _ := by rw [MemLp.toLp_zero, norm_zero]
  normG _ _ := by rw [MemLp.toLp_zero, norm_zero]

end H1Data

theorem exists_h1Data_testField [Fintype ι] {φ : ι → (Fin n → ℝ) → ℝ} (hφ : IsTestField Ω φ) :
    ∃ B, Nonempty (H1Data Ω (testField hφ) B) := by
  have hm : ∀ i, MemLp (φ i) 2 volume := fun i =>
    (hφ i).continuous.memLp_of_hasCompactSupport (hφ i).hasCompactSupport
  have hd : ∀ i m, IsTest Ω (fun y => fderiv ℝ (φ i) y (coordDir m)) := fun i m =>
    (hφ i).fderiv_apply _
  have hdm : ∀ i m, MemLp (fun y => fderiv ℝ (φ i) y (coordDir m)) 2 volume := fun i m =>
    (hd i m).continuous.memLp_of_hasCompactSupport (hd i m).hasCompactSupport
  set B := ∑ i, (‖(hm i).toLp (φ i)‖ + ∑ m, ‖(hdm i m).toLp _‖)
  have hB : ∀ i, ‖(hm i).toLp (φ i)‖ + ∑ m, ‖(hdm i m).toLp _‖ ≤ B := fun i =>
    Finset.single_le_sum (f := fun i => ‖(hm i).toLp (φ i)‖ + ∑ m, ‖(hdm i m).toLp _‖)
      (fun i _ => by positivity) (Finset.mem_univ i)
  refine ⟨B, ⟨{
    F := φ
    G := fun i m y => fderiv ℝ (φ i) y (coordDir m)
    memF := hm
    memG := hdm
    weak := fun i m ψ hψ => by
      have e := integral_conj_fderiv_mul hψ ((hφ i).contDiff.of_le (by simp)) (coordDir m)
      simp only [RCLike.conj_to_real] at e
      simp only [mul_comm (φ i _), mul_comm (fderiv ℝ (φ i) _ _)]
      exact e
    ae := coeFn_testField hφ
    normF := fun i => le_trans (le_add_of_nonneg_right (by positivity)) (hB i)
    normG := fun i m => le_trans ((Finset.single_le_sum (f := fun m => ‖(hdm i m).toLp _‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ m)).trans (le_add_of_nonneg_left
        (norm_nonneg _))) (hB i) }⟩⟩

/-- The coefficients of `d`: `(dω)_t = Σ_{r, m} dCoef k t r m ∂_m ω_r`. -/
def dCoef (k : ℤ) (t : formIdx n (k + 1)) (r : formIdx n k) (m : Fin n) : ℝ :=
  if m ∈ t.1 ∧ t.1.erase m = r.1 then Feec.ExteriorFibre.sgn m t.1 else 0

theorem sum_dCoef_mul (k : ℤ) (t : formIdx n (k + 1)) (r : formIdx n k) (g : Fin n → ℝ) :
    ∑ m, dCoef k t r m * g m = ∑ j ∈ t.1 with t.1.erase j = r.1,
      Feec.ExteriorFibre.sgn j t.1 * g j := by
  rw [Finset.sum_filter]
  simp only [dCoef, ite_mul, zero_mul, ite_and]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem extDerivOp_apply_eq_dCoef (k : ℤ) (φ : formIdx n k → (Fin n → ℝ) → ℝ)
    (t : formIdx n (k + 1)) (x : Fin n → ℝ) : (extDerivOp ℝ n k).apply φ t x =
      ∑ r, ∑ m, dCoef k t r m * fderiv ℝ (φ r) x (coordDir m) := by
  simp only [ConstCoeffOp.apply, applyEntry_extDerivOp_coeff, sum_dCoef_mul]

theorem formalAdj_apply_eq_dCoef (k : ℤ) (ψ : formIdx n (k + 1) → (Fin n → ℝ) → ℝ)
    (r : formIdx n k) (x : Fin n → ℝ) : (extDerivOp ℝ n k).formalAdj.apply ψ r x =
      -∑ t, ∑ m, dCoef k t r m * fderiv ℝ (ψ t) x (coordDir m) := by
  have hc : ∀ t : formIdx n (k + 1),
      ConstCoeffOp.applyEntry ((extDerivOp ℝ n k).formalAdj.coeff r t) (ψ t) x =
        -∑ m, dCoef k t r m * fderiv ℝ (ψ t) x (coordDir m) := by
    intro t
    rw [sum_dCoef_mul, ← Finset.sum_neg_distrib]
    simp only [ConstCoeffOp.formalAdj, ConstCoeffOp.adjEntry, extDerivOp,
      ConstCoeffOp.applyEntry, List.map_map]
    rw [← Finset.sum_map_toList]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp [iterDeriv_singleton]
  simp only [ConstCoeffOp.apply, hc, Finset.sum_neg_distrib]

namespace H1Data

variable {B : ℝ}

/-- **`d_min x` is the weak `dx`** for a form with `H¹(ℝⁿ)` data. -/
theorem minimal_apply (hΩ : IsOpen Ω) {k : ℤ} {x : L2F ℝ Ω (formIdx n k)}
    (hx : x ∈ ((extDerivOp ℝ n k).minimal Ω).domain) (h : H1Data Ω x B) :
    (extDerivOp ℝ n k).minimal Ω ⟨x, hx⟩ = h.weak' (dCoef k) := by
  have hmax : x ∈ ((extDerivOp ℝ n k).maximal Ω).domain :=
    ((extDerivOp ℝ n k).minimal_le_maximal hΩ).1 hx
  rw [((extDerivOp ℝ n k).minimal_le_maximal hΩ).2 (x := ⟨x, hx⟩) (y := ⟨x, hmax⟩) rfl]
  refine (extDerivOp ℝ n k).maximal_apply_eq hΩ ⟨x, hmax⟩ fun φ hφ => ?_
  exact (h.inner_eq (dCoef k) hφ ((extDerivOp ℝ n k).formalAdj.isTestField_apply hφ)
    fun i y => formalAdj_apply_eq_dCoef k φ i y).symm

/-- **A form with `H¹(ℝⁿ)` data lies in the domain of `(d_min)†`**, with value the weak `d*x`. -/
theorem mem_adjoint (hΩ : IsOpen Ω) {k : ℤ} {x : L2F ℝ Ω (formIdx n (k + 1))}
    (h : H1Data Ω x B) : ∃ hx : x ∈ ((extDerivOp ℝ n k).minimal Ω)†.domain,
      ((extDerivOp ℝ n k).minimal Ω)† ⟨x, hx⟩ = h.weak' fun r t m => -dCoef k t r m := by
  have key : ∀ φ : formIdx n k → (Fin n → ℝ) → ℝ, ∀ hφ : IsTestField Ω φ,
      ⟪h.weak' fun r t m => -dCoef k t r m, testField hφ⟫ =
        ⟪x, testField ((extDerivOp ℝ n k).isTestField_apply hφ)⟫ := fun φ hφ =>
    (h.inner_eq _ hφ ((extDerivOp ℝ n k).isTestField_apply hφ) fun i y => by
      rw [extDerivOp_apply_eq_dCoef]
      simp [neg_mul, Finset.sum_neg_distrib]).symm
  have hx := ((extDerivOp ℝ n k).mem_adjoint_minimal_domain_iff hΩ).2 ⟨_, key⟩
  exact ⟨hx, (extDerivOp ℝ n k).adjoint_minimal_apply_eq hΩ ⟨x, hx⟩ key⟩

end H1Data

end Feec.Domain
