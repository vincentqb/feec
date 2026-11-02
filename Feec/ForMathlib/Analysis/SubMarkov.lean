module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Sub-Markov generators: positive contraction semigroups in the maximum norm

On `ℝ^ι` (`ι` finite) with the maximum norm `‖v‖ = maxᵢ |vᵢ|`, a bounded operator `L` is a
**sub-Markov generator** (`IsSubMarkovGenerator L`) if `L + c` is positive for some `c ≥ 0` and
`L 𝟙 ≤ 0`; for a matrix `(aᵢⱼ)` this says that the off-diagonal entries are nonnegative and the
row sums nonpositive (a Metzler matrix with nonpositive row sums, the negative of a weakly
diagonally dominant M-matrix). Then `e^{tL}` is, for `t ≥ 0`,

* positive (`IsSubMarkovGenerator.exp_smul_apply_nonneg`: `v ≥ 0 ⇒ e^{tL} v ≥ 0`),
* a contraction in the maximum norm (`IsSubMarkovGenerator.norm_exp_smul_le_one`), and
* satisfies the **discrete maximum principle** (`IsSubMarkovGenerator.exp_smul_apply_le`,
  `IsSubMarkovGenerator.le_exp_smul_apply`): `-a ≤ v ≤ a` with `a ≥ 0` gives
  `-a ≤ e^{tL} v ≤ a`.

The proofs avoid matrix entries: a positive operator `P` has `|P v| ≤ P |v| ≤ ‖v‖ P 𝟙`, so
`‖P‖ ≤ c` as soon as `P 𝟙 ≤ c` (`ContinuousLinearMap.norm_le_of_nonneg_of_apply_one_le`), and
`e^{tL} = e^{-ct} e^{t(L + c)}` with `‖e^{t(L + c)}‖ ≤ e^{t ‖L + c‖} ≤ e^{ct}`
(`NormedSpace.norm_exp_le_exp_norm`, in every complete normed algebra with `‖1‖ ≤ 1`).

## References

* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method and the maximum principle)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open NormedSpace

@[expose] public noncomputable section

/-- `‖exp x‖ ≤ e^{‖x‖}` in a complete normed `ℝ`-algebra with `‖1‖ ≤ 1` (the exponential
series is dominated by the scalar one). -/
theorem NormedSpace.norm_exp_le_exp_norm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hpow : ∀ n : ℕ, ‖x ^ n‖ ≤ ‖x‖ ^ n := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h1
    · exact norm_pow_le' x hn
  rw [exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' x)).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (norm_expSeries_summable' x)
    ((norm_expSeries_summable' ‖x‖).of_norm)
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hpow n) (by positivity)

namespace ContinuousLinearMap

variable {ι : Type*}

/-- A positive operator on `ℝ^ι` satisfies `|(P v)ᵢ| ≤ (P |v|)ᵢ`. -/
theorem abs_apply_le_of_nonneg {P : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hP : ∀ v, 0 ≤ v → 0 ≤ P v)
    (v : ι → ℝ) (i : ι) : |P v i| ≤ P |v| i := by
  have h1 := hP (|v| - v) fun j => by simp [le_abs_self]
  have h2 := hP (|v| + v) fun j => by
    simp only [Pi.add_apply, Pi.abs_apply, Pi.zero_apply]; linarith [neg_abs_le (v j)]
  rw [map_sub] at h1
  rw [map_add] at h2
  have a1 := h1 i
  have a2 := h2 i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at a1 a2
  exact abs_le.2 ⟨by linarith, by linarith⟩

variable [Fintype ι]

/-- **The norm of a positive operator in the maximum norm**: `P 𝟙 ≤ c` gives `‖P‖ ≤ c`. -/
theorem norm_le_of_nonneg_of_apply_one_le {P : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hP : ∀ v, 0 ≤ v → 0 ≤ P v) {c : ℝ} (hc : 0 ≤ c) (h1 : ∀ i, P (fun _ => 1) i ≤ c) :
    ‖P‖ ≤ c := by
  refine opNorm_le_bound _ hc fun v => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hb : |v| ≤ ‖v‖ • (fun _ => (1 : ℝ)) := fun j => by
    simpa using norm_le_pi_norm v j
  have h2 := hP _ (sub_nonneg.2 hb)
  rw [map_sub, map_smul, sub_nonneg] at h2
  rw [Real.norm_eq_abs]
  calc |P v i| ≤ P |v| i := abs_apply_le_of_nonneg hP v i
    _ ≤ ‖v‖ * P (fun _ => 1) i := h2 i
    _ ≤ ‖v‖ * c := mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg v)
    _ = c * ‖v‖ := mul_comm _ _

/-- **The exponential of a positive operator is positive**: `v ≥ 0 ⇒ e^{tP} v ≥ 0`, `t ≥ 0`. -/
theorem exp_smul_apply_nonneg {P : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hP : ∀ v, 0 ≤ v → 0 ≤ P v)
    {t : ℝ} (ht : 0 ≤ t) {v : ι → ℝ} (hv : 0 ≤ v) : 0 ≤ exp (t • P) v := by
  have hpow : ∀ k : ℕ, 0 ≤ (P ^ k) v := fun k => by
    induction k with
    | zero => simpa using hv
    | succ k ih => rw [pow_succ']; exact hP _ ih
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℝ) (t • P)
  have e := (ContinuousLinearMap.apply ℝ (ι → ℝ) v).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at e
  rw [exp_eq_tsum ℝ]
  dsimp only
  rw [e]
  refine tsum_nonneg fun k => ?_
  rw [smul_pow, smul_smul, _root_.smul_apply]
  exact smul_nonneg (by positivity) (hpow k)

end ContinuousLinearMap

variable {ι : Type*} [Fintype ι]

/-- `L` is a **sub-Markov generator** on `ℝ^ι` (maximum norm): `L + c` is positive for some
`c ≥ 0`, and `L 𝟙 ≤ 0`. For a matrix: nonnegative off-diagonal entries and nonpositive row
sums. -/
structure IsSubMarkovGenerator (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Prop where
  exists_shift : ∃ c : ℝ, 0 ≤ c ∧ ∀ v, 0 ≤ v → 0 ≤ L v + c • v
  apply_one_nonpos : ∀ i, L (fun _ => 1) i ≤ 0

namespace IsSubMarkovGenerator

/-- `ℚ`-algebra structure on operators, for `NormedSpace.exp_add_of_commute`. -/
local instance instNormedAlgebraRat : NormedAlgebra ℚ ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- `e^{tL} = e^{-ct} e^{t(L + c)}`. -/
theorem _root_.ContinuousLinearMap.exp_smul_eq_smul_exp_smul_add (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) (c t : ℝ) :
    exp (t • L) = Real.exp (-(t * c)) • exp (t • (L + c • 1)) := by
  have e : t • L = t • (L + c • 1) + algebraMap ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ)) (-(t * c)) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_add, smul_smul]; module
  rw [e, exp_add_of_commute (Algebra.commutes _ _).symm, ← algebraMap_exp_comm,
    ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

variable {L : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hL : IsSubMarkovGenerator L)
include hL

/-- **Positivity**: `v ≥ 0 ⇒ e^{tL} v ≥ 0` for `t ≥ 0`. -/
theorem exp_smul_apply_nonneg {t : ℝ} (ht : 0 ≤ t) {v : ι → ℝ} (hv : 0 ≤ v) :
    0 ≤ exp (t • L) v := by
  obtain ⟨c, -, hc⟩ := hL.exists_shift
  rw [L.exp_smul_eq_smul_exp_smul_add c t, _root_.smul_apply]
  exact smul_nonneg (Real.exp_pos _).le
    (ContinuousLinearMap.exp_smul_apply_nonneg (fun w hw => by simpa using hc w hw) ht hv)

/-- **Contraction in the maximum norm**: `‖e^{tL}‖ ≤ 1` for `t ≥ 0`. -/
theorem norm_exp_smul_le_one {t : ℝ} (ht : 0 ≤ t) : ‖exp (t • L)‖ ≤ 1 := by
  obtain ⟨c, hc0, hc⟩ := hL.exists_shift
  have hP : ∀ v, 0 ≤ v → 0 ≤ (L + c • 1) v := fun v hv => by simpa using hc v hv
  have hn : ‖L + c • 1‖ ≤ c :=
    ContinuousLinearMap.norm_le_of_nonneg_of_apply_one_le hP hc0 fun i => by
      simpa using hL.apply_one_nonpos i
  rw [L.exp_smul_eq_smul_exp_smul_add c t, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-(t * c)) * ‖exp (t • (L + c • 1))‖
      ≤ Real.exp (-(t * c)) * Real.exp (t * c) := by
        gcongr
        refine (NormedSpace.norm_exp_le_exp_norm ContinuousLinearMap.norm_id_le _).trans ?_
        gcongr
        rw [norm_smul, Real.norm_of_nonneg ht]
        exact mul_le_mul_of_nonneg_left hn ht
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **The discrete maximum principle**: for `t ≥ 0` and `a ≥ 0`, `v ≤ a` gives
`e^{tL} v ≤ a`. -/
theorem exp_smul_apply_le {t : ℝ} (ht : 0 ≤ t) {a : ℝ} (ha : 0 ≤ a) {v : ι → ℝ}
    (hv : v ≤ fun _ => a) : exp (t • L) v ≤ fun _ => a := by
  have h1 := hL.exp_smul_apply_nonneg ht (sub_nonneg.2 hv)
  rw [map_sub, sub_nonneg] at h1
  refine fun i => (h1 i).trans ?_
  have := (norm_le_pi_norm (exp (t • L) fun _ => a) i).trans
    (((exp (t • L)).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (hL.norm_exp_smul_le_one ht)))
  rw [Real.norm_eq_abs] at this
  refine (le_abs_self _).trans (this.trans ?_)
  exact (pi_norm_le_iff_of_nonneg ha).2 fun _ => by rw [Real.norm_of_nonneg ha]

/-- **The discrete maximum principle**, lower bound: `-a ≤ v` gives `-a ≤ e^{tL} v`. -/
theorem le_exp_smul_apply {t : ℝ} (ht : 0 ≤ t) {a : ℝ} (ha : 0 ≤ a) {v : ι → ℝ}
    (hv : (fun _ => -a) ≤ v) : (fun _ => -a) ≤ exp (t • L) v := by
  have := hL.exp_smul_apply_le ht ha (v := -v) fun i => by simpa using neg_le.1 (hv i)
  intro i
  have h := this i
  simp only [map_neg, Pi.neg_apply] at h
  exact neg_le.1 h

end IsSubMarkovGenerator
