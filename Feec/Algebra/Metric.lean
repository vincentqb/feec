module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

/-!
# Constant metrics in components: index raising, traces and trace reversal

A constant (pseudo-)metric on an index type `ι` is a symmetric matrix `g` with inverse `gi`
(`gi * g = 1`); the Minkowski metric `diag(-1, 1, …, 1)` is the main instance. Tensors carry
lower indices; contractions use `gi`.

## Main definitions

* `Feec.Metric.minkowski R n : Fin (n + 1) → R`, the diagonal `(-1, 1, …, 1)`, and
  `minkowskiMatrix R n = diagonal (minkowski R n)` (its own inverse).
* `Feec.Metric.trace gi h = gi^{ab} h_ab`.
* `Feec.Metric.trRev g gi h = h - ½ (tr h) g`, the trace reversal `h̄`.

## Main results

* `isSymm_of_mul_eq_one`: the inverse of a symmetric matrix is symmetric;
  `mul_eq_one_comm'`: `gi * g = 1 ↔ g * gi = 1`.
* `trace_metric`: `gi^{ab} g_ab = n`; `trace_trRev`: `tr h̄ = (1 - n/2) tr h` (any dimension).
* `trRev_trRev`: trace reversal is an involution in dimension `4`; `eq_trRev_sub`: in every
  dimension `n ≠ 2`, `h = h̄ - (n - 2)⁻¹ (tr h̄) g`; `exists_trRev_trRev_ne`: in dimension
  `n ∉ {0, 4}` trace reversal is not an involution.
* `trRev_add_sym`: the gauge law (2.5), `h ↦ h + P + Pᵀ` gives `h̄ ↦ h̄ + P + Pᵀ - (tr P) g`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §2.2 (signature (−+++)), §2.7 ((2.5), trace reversal)
* [R. M. Wald, *General Relativity*][Wald1984], §4.4
-/

open Matrix

@[expose] public noncomputable section

namespace Feec.Metric

/-! ### Inverses of symmetric matrices -/

section CommRing

variable {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]

/-- A left inverse of a symmetric matrix is symmetric. -/
theorem isSymm_of_mul_eq_one [DecidableEq ι] {g gi : Matrix ι ι R} (hg : g.IsSymm) (hinv : gi * g = 1) :
    gi.IsSymm := by
  have h1 : g * gi.transpose = 1 := by
    rw [← hg.eq, ← transpose_mul, hinv, transpose_one]
  unfold Matrix.IsSymm
  calc gi.transpose = (gi * g) * gi.transpose := by rw [hinv, Matrix.one_mul]
    _ = gi * (g * gi.transpose) := Matrix.mul_assoc _ _ _
    _ = gi := by rw [h1, Matrix.mul_one]

/-- A left inverse is a right inverse. -/
theorem mul_eq_one_comm' [DecidableEq ι] {g gi : Matrix ι ι R} : gi * g = 1 ↔ g * gi = 1 := mul_eq_one_comm

/-! ### The Minkowski metric -/

variable (R) in
/-- The Minkowski signature `(-1, 1, …, 1)` on `Fin (n + 1)` (time index `0`).
[QuennevilleBelair2015], §2.2 -/
def minkowski (n : ℕ) : Fin (n + 1) → R := Fin.cons (-1) fun _ => 1

variable (R) in
/-- The Minkowski metric `η = diag(-1, 1, …, 1)`. [QuennevilleBelair2015], §2.2 -/
def minkowskiMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R := diagonal (minkowski R n)

@[simp] theorem minkowski_zero (n : ℕ) : minkowski R n 0 = -1 := rfl

@[simp] theorem minkowski_succ (n : ℕ) (i : Fin n) : minkowski R n i.succ = 1 := rfl

/-- The four-dimensional Minkowski signature as an explicit vector. -/
theorem minkowski_three : minkowski R 3 = ![-1, 1, 1, 1] := by
  funext i; fin_cases i <;> rfl

variable (R) in
/-- The four-dimensional Minkowski signature `(-1, 1, 1, 1)` indexed by `Fin 4` (thesis
convention; `= minkowski R 3`). [QuennevilleBelair2015], §2.2 -/
def minkowski4 : Fin 4 → R := ![-1, 1, 1, 1]

theorem minkowski4_eq_minkowski : minkowski4 R = minkowski R 3 := minkowski_three.symm

theorem minkowski4_mul_self (i : Fin 4) : minkowski4 R i * minkowski4 R i = 1 := by
  fin_cases i <;> simp [minkowski4]

theorem minkowski_mul_self (n : ℕ) (i : Fin (n + 1)) : minkowski R n i * minkowski R n i = 1 := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem minkowskiMatrix_mul_self (n : ℕ) :
    minkowskiMatrix R n * minkowskiMatrix R n = 1 := by
  rw [minkowskiMatrix, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; exact minkowski_mul_self n i

theorem minkowskiMatrix_isSymm (n : ℕ) : (minkowskiMatrix R n).IsSymm := by
  simp [minkowskiMatrix, Matrix.IsSymm]

/-! ### Traces and trace reversal -/

/-- The metric trace `gi^{ab} h_ab`. [QuennevilleBelair2015], §2.7 -/
def trace (gi h : Matrix ι ι R) : R := ∑ a, ∑ b, gi a b * h a b

theorem trace_eq_trace_mul (gi h : Matrix ι ι R) (hh : hᵀ = h) :
    trace gi h = (gi * h).trace := by
  simp only [trace, Matrix.trace, diag, mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show h b a = h a b by simpa using congrFun (congrFun hh a) b]

theorem trace_add (gi h k : Matrix ι ι R) : trace gi (h + k) = trace gi h + trace gi k := by
  simp [trace, mul_add, Finset.sum_add_distrib]

theorem trace_smul (gi h : Matrix ι ι R) (c : R) : trace gi (c • h) = c * trace gi h := by
  simp [trace, Finset.mul_sum, mul_left_comm]

theorem trace_sub (gi h k : Matrix ι ι R) : trace gi (h - k) = trace gi h - trace gi k := by
  simp [trace, mul_sub, Finset.sum_sub_distrib]

/-- `gi^{ab} g_ab = n` for a symmetric metric with inverse `gi`. -/
theorem trace_metric [DecidableEq ι] {g gi : Matrix ι ι R} (hg : g.IsSymm) (hinv : gi * g = 1) :
    trace gi g = Fintype.card ι := by
  rw [trace_eq_trace_mul gi g hg, hinv, Matrix.trace_one]

variable [Invertible (2 : R)]

/-- The trace reversal `h̄ = h - ½ (tr h) g`. [QuennevilleBelair2015], §2.7, (2.5) -/
def trRev (g gi h : Matrix ι ι R) : Matrix ι ι R := h - (⅟2 * trace gi h) • g

theorem trRev_apply (g gi h : Matrix ι ι R) (a b : ι) :
    trRev g gi h a b = h a b - ⅟2 * trace gi h * g a b := by
  simp [trRev, mul_assoc]

/-- `tr h̄ = (1 - n/2) tr h`, in every dimension `n`. [QuennevilleBelair2015], (2.5) -/
theorem trace_trRev [DecidableEq ι] {g gi : Matrix ι ι R} (hg : g.IsSymm) (hinv : gi * g = 1)
    (h : Matrix ι ι R) :
    trace gi (trRev g gi h) = (1 - ⅟2 * Fintype.card ι) * trace gi h := by
  rw [trRev, trace_sub, trace_smul, trace_metric hg hinv]; ring

/-- Trace reversal of a symmetric tensor is symmetric. -/
theorem transpose_trRev {g gi h : Matrix ι ι R} (hg : g.IsSymm) (hh : hᵀ = h) :
    (trRev g gi h)ᵀ = trRev g gi h := by
  rw [trRev, transpose_sub, transpose_smul, hh, hg.eq]

/-- Trace reversal is linear. -/
theorem trRev_add (g gi h k : Matrix ι ι R) :
    trRev g gi (h + k) = trRev g gi h + trRev g gi k := by
  simp only [trRev, trace_add, mul_add, add_smul]; abel

theorem trRev_smul (g gi h : Matrix ι ι R) (c : R) :
    trRev g gi (c • h) = c • trRev g gi h := by
  simp only [trRev, trace_smul, smul_sub, smul_smul]; ring_nf

/-- In general dimension, `trRev (trRev h) = h - (1 - n/4) (tr h) g`. -/
theorem trRev_trRev_eq [DecidableEq ι] {g gi : Matrix ι ι R} (hg : g.IsSymm) (hinv : gi * g = 1)
    (h : Matrix ι ι R) :
    trRev g gi (trRev g gi h) = h - ((1 - ⅟2 * ⅟2 * Fintype.card ι) * trace gi h) • g := by
  rw [trRev, trace_trRev hg hinv, trRev, sub_sub, ← add_smul]
  congr 2
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (trace gi h) * h2

/-- **(2.5)**: trace reversal is an involution in dimension four, `h = h̄ - ½ (tr h̄) g`.
[QuennevilleBelair2015], (2.5) -/
theorem trRev_trRev [DecidableEq ι] {g gi : Matrix ι ι R} (hg : g.IsSymm) (hinv : gi * g = 1)
    (hn : Fintype.card ι = 4) (h : Matrix ι ι R) : trRev g gi (trRev g gi h) = h := by
  rw [trRev_trRev_eq hg hinv, hn]
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  have : (1 - ⅟2 * ⅟2 * ((4 : ℕ) : R)) = 0 := by
    push_cast; linear_combination (-(1 : R) - 2 * ⅟2) * h2
  rw [this, zero_mul, zero_smul, sub_zero]

/-- The gauge law (2.5): if `h ↦ h + P + Pᵀ` (`P_ab = ∂_a ξ_b`), then
`h̄ ↦ h̄ + P + Pᵀ - (gi^{ab} P_ab) g`. [QuennevilleBelair2015], (2.5) -/
theorem trRev_add_sym {g gi : Matrix ι ι R} (hgi : gi.IsSymm) (h P : Matrix ι ι R) :
    trRev g gi (h + P + Pᵀ) = trRev g gi h + P + Pᵀ - (trace gi P) • g := by
  have hT : trace gi Pᵀ = trace gi P := by
    simp only [trace, transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hgi.apply a b]
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [trRev, trace_add, hT]
  have e : ⅟2 * (trace gi h + trace gi P + trace gi P) = ⅟2 * trace gi h + trace gi P := by
    linear_combination (trace gi P) * h2
  rw [e, add_smul]; abel

end CommRing

section Field

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Invertible (2 : K)]

/-- In every dimension `n ≠ 2`, the trace reversal is invertible:
`h = h̄ - (n - 2)⁻¹ (tr h̄) g`. [QuennevilleBelair2015], (2.5) (the thesis uses `n = 4` silently). -/
theorem eq_trRev_sub {g gi : Matrix ι ι K} (hg : g.IsSymm) (hinv : gi * g = 1)
    (hn : (Fintype.card ι : K) ≠ 2) (h : Matrix ι ι K) :
    h = trRev g gi h - (((Fintype.card ι : K) - 2)⁻¹ * trace gi (trRev g gi h)) • g := by
  rw [trace_trRev hg hinv, trRev, sub_sub, ← add_smul]
  have hn' : (Fintype.card ι : K) - 2 ≠ 0 := sub_ne_zero.2 hn
  have h2 : (⅟2 : K) * 2 = 1 := invOf_mul_self 2
  have e : (1 - ⅟2 * (Fintype.card ι : K)) = -(⅟2 * ((Fintype.card ι : K) - 2)) := by
    linear_combination -h2
  have : ⅟2 * trace gi h + ((Fintype.card ι : K) - 2)⁻¹ *
      ((1 - ⅟2 * (Fintype.card ι : K)) * trace gi h) = 0 := by
    rw [e, show ((Fintype.card ι : K) - 2)⁻¹ * (-(⅟2 * ((Fintype.card ι : K) - 2)) * trace gi h)
      = -(⅟2 * trace gi h) * (((Fintype.card ι : K) - 2)⁻¹ * ((Fintype.card ι : K) - 2)) by ring,
      inv_mul_cancel₀ hn']
    ring
  rw [this, zero_smul, sub_zero]

/-- In dimension `n ∉ {0, 4}` (as elements of `K`) trace reversal is not an involution. -/
theorem exists_trRev_trRev_ne {g gi : Matrix ι ι K} (hg : g.IsSymm) (hinv : gi * g = 1)
    (hn0 : (Fintype.card ι : K) ≠ 0) (hn : (Fintype.card ι : K) ≠ 4) :
    ∃ h, trRev g gi (trRev g gi h) ≠ h := by
  refine ⟨g, fun h => ?_⟩
  have hne : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    exact hn0 (by simp [Fintype.card_eq_zero])
  obtain ⟨i⟩ := hne
  have hg0 : g ≠ 0 := by
    rintro rfl
    have := congrFun (congrFun hinv i) i
    simp at this
  rw [trRev_trRev_eq hg hinv, trace_metric hg hinv, sub_eq_self, smul_eq_zero] at h
  refine h.elim (fun h => ?_) hg0
  have h2 : (⅟2 : K) * 2 = 1 := invOf_mul_self 2
  rcases mul_eq_zero.1 h with h | h
  · exact hn (by linear_combination (-4 : K) * h - (Fintype.card ι : K) * (1 + 2 * ⅟2) * h2)
  · exact hn0 h

end Field

end Feec.Metric
