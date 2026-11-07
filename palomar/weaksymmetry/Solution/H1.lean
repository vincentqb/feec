module

public import Feec.Domain.ConstCoeffOp
public import Feec.Domain.Operators

/-!
# First-order operators on restrictions of `H¹(ℝⁿ)` fields

A field `u ∈ L²(Ω; ℝ^ι)` that is the restriction of `F ∈ L²(ℝⁿ; ℝ^ι)` with weak first derivatives
`G_{i m} = ∂_m F_i ∈ L²(ℝⁿ)` (`H1Data`) lies in the weak domain of every first-order operator with
constant coefficients `a`, `(A f)_j = Σ_{i, m} a_{j i m} ∂_m f_i`: tested against a test field `φ`,
`⟪u, Aᵗφ⟫ = ⟪w, φ⟫` with `w_j = Σ_{i, m} a_{j i m} G_{i m}|_Ω` (`H1Data.inner_eq`), and
`‖w‖ ≤ Σ |a| B` when `‖G_{i m}‖ ≤ B` (`H1Data.norm_weak_le`).

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain

variable {n : ℕ} {Ω : Set (Fin n → ℝ)} {ι κ : Type*}

/-- `u ∈ L²(Ω; ℝ^ι)` is the restriction to `Ω` of `F ∈ L²(ℝⁿ; ℝ^ι)` whose components have weak
first derivatives `G i m = ∂_m F_i ∈ L²(ℝⁿ)`, with `‖F_i‖, ‖G_{i m}‖ ≤ B`. -/
structure H1Data (Ω : Set (Fin n → ℝ)) (u : L2F ℝ Ω ι) (B : ℝ) where
  /-- the field on `ℝⁿ` -/
  F : ι → (Fin n → ℝ) → ℝ
  /-- its weak first derivatives -/
  G : ι → Fin n → (Fin n → ℝ) → ℝ
  memF : ∀ i, MemLp (F i) 2 volume
  memG : ∀ i m, MemLp (G i m) 2 volume
  weak : ∀ i m (φ : (Fin n → ℝ) → ℝ), IsTest univ φ →
    ∫ y, F i y * fderiv ℝ φ y (coordDir m) = -∫ y, G i m y * φ y
  ae : ∀ i, (u i : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω] F i
  normF : ∀ i, ‖(memF i).toLp (F i)‖ ≤ B
  normG : ∀ i m, ‖(memG i m).toLp (G i m)‖ ≤ B

namespace H1Data

variable {u : L2F ℝ Ω ι} {B : ℝ} (h : H1Data Ω u B)

/-- The restriction of `G i m` to `Ω`. -/
def gres (i : ι) (m : Fin n) : L2 ℝ Ω := ((h.memG i m).restrict Ω).toLp (h.G i m)

/-- The weak value `w_j = Σ_{i, m} a_{j i m} G_{i m}|_Ω` of the operator with coefficients
`a`. -/
def weak' [Fintype ι] (a : κ → ι → Fin n → ℝ) : L2F ℝ Ω κ :=
  WithLp.toLp 2 fun j => ∑ i, ∑ m, a j i m • h.gres i m

theorem norm_toLp_restrict_le {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    ‖(hf.restrict Ω).toLp f‖ ≤ ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem norm_gres_le (i : ι) (m : Fin n) : ‖h.gres i m‖ ≤ B :=
  (norm_toLp_restrict_le (h.memG i m)).trans (h.normG i m)

/-- `u` is the class of `F|_Ω`. -/
theorem eq_toL2F [Fintype ι] : u = toL2F (fun i => (h.memF i).restrict Ω) := by
  refine PiLp.ext fun i => Lp.ext ?_
  exact (h.ae i).trans (((h.memF i).restrict Ω).coeFn_toLp).symm

theorem norm_le_sum [Fintype κ] {V : κ → Type*} [∀ j, NormedAddCommGroup (V j)] (x : PiLp 2 V) :
    ‖x‖ ≤ ∑ j, ‖x j‖ := by
  rw [PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _

/-- `‖w‖ ≤ Σ_{j, i, m} |a_{j i m}| B`. -/
theorem norm_weak_le [Fintype ι] [Fintype κ] (a : κ → ι → Fin n → ℝ) :
    ‖h.weak' a‖ ≤ ∑ j, ∑ i, ∑ m, |a j i m| * B := by
  refine (norm_le_sum _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h.norm_gres_le i m) (abs_nonneg _)

include h in
theorem norm_le [Fintype ι] : ‖u‖ ≤ ∑ _i : ι, B := by
  rw [h.eq_toL2F]
  refine (norm_le_sum _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact (norm_toLp_restrict_le (h.memF i)).trans (h.normF i)

theorem inner_toL2_gres {φ : (Fin n → ℝ) → ℝ} (hφ : IsTest Ω φ) (i : ι) (m : Fin n) :
    ⟪h.gres i m, toL2 hφ⟫ = ∫ y, h.G i m y * φ y := by
  rw [toL2, inner_toLp, ← integral_restrict_of_eq_zero (Ω := Ω) fun x hx => by
    rw [hφ.eq_zero_of_notMem hx, mul_zero]]
  refine integral_congr_ae ?_
  filter_upwards [((h.memG i m).restrict Ω).coeFn_toLp] with x hx
  simp [gres, hx]

/-- **Integration by parts against `H¹(ℝⁿ)` data**: if `ψ = Aᵗφ`,
`ψ_i = -Σ_{j, m} a_{j i m} ∂_m φ_j`, for test fields `φ`, `ψ` on `Ω`, then
`⟪u, ψ⟫ = ⟪w, φ⟫` with `w = Σ a G|_Ω` (`weak'`). -/
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

end FEEC
