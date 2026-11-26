module

public import Feec.Algebra.PolynomialFormDim

/-!
# The classical polynomial form spaces in dimensions two and three

Closed forms of `dim P_rΛᵏ` and `dim P_r⁻Λᵏ` on `K³` and `K²`, over every field `K` (of
characteristic `0` for the trimmed spaces): the Lagrange, Nédélec, Brezzi–Douglas–Marini,
Raviart–Thomas and discontinuous elements ([AFW2006], §3; [AFW2010], §5.1).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [J.-C. Nédélec, *Mixed finite elements in ℝ³*][Nedelec1980]
* [J.-C. Nédélec, *A new family of mixed finite elements in ℝ³*][Nedelec1986]
* [P.-A. Raviart, J.-M. Thomas, *A mixed finite element method for 2-nd order elliptic problems*][RaviartThomas1977]
* [F. Brezzi, J. Douglas, Jr., L. D. Marini, *Two families of mixed finite elements for second order elliptic problems*][BrezziDouglasMarini1985]

Bibliography: [references.bib](../../docs/references.bib)
-/

public section

namespace Feec.Koszul

private theorem two_mul_choose_two (m : ℕ) : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := by
  have := Nat.add_one_mul_choose_eq (m + 1) 1
  simp only [Nat.choose_one_right] at this
  linarith

private theorem six_mul_choose_three (m : ℕ) :
    6 * (m + 3).choose 3 = (m + 3) * (m + 2) * (m + 1) := by
  have h := Nat.add_one_mul_choose_eq (m + 2) 2
  have h2 := two_mul_choose_two m
  nlinarith

variable {K : Type*} [Field K] {d : Type*} [LinearOrder d] [Fintype d]

theorem finrank_polyForm_three_zero (hd : Fintype.card d = 3) (r : ℕ) :
    6 * Module.finrank K (polyForm K d r 0) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polyForm, hd, add_zero, Nat.choose_zero_right, mul_one,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 3 by rfl), six_mul_choose_three]
  ring

/-- Nédélec edge elements of the second kind ([Nedelec1986]). -/
theorem finrank_polyForm_three_one (hd : Fintype.card d = 3) (r : ℕ) :
    2 * Module.finrank K (polyForm K d r 1) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polyForm, hd, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 1 + 2 by omega), ← mul_assoc,
    two_mul_choose_two (r + 1)]
  ring

/-- Brezzi–Douglas–Marini face elements ([BrezziDouglasMarini1985], [Nedelec1986]). -/
theorem finrank_polyForm_three_two (hd : Fintype.card d = 3) (r : ℕ) :
    2 * Module.finrank K (polyForm K d r 2) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polyForm, hd, Nat.choose_symm_of_eq_add (show r + 3 = r + 2 + 1 by omega),
    Nat.choose_one_right, mul_left_comm, two_mul_choose_two r]
  ring

theorem finrank_polyForm_three_three (hd : Fintype.card d = 3) (r : ℕ) :
    6 * Module.finrank K (polyForm K d r 3) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polyForm, hd, Nat.choose_self, one_mul, six_mul_choose_three]
  ring

theorem finrank_polyForm_two_zero (hd : Fintype.card d = 2) (r : ℕ) :
    2 * Module.finrank K (polyForm K d r 0) = (r + 1) * (r + 2) := by
  rw [finrank_polyForm, hd, add_zero, Nat.choose_zero_right, mul_one,
    Nat.choose_symm_of_eq_add (show r + 2 = r + 2 by rfl), two_mul_choose_two]
  ring

/-- Brezzi–Douglas–Marini elements on triangles ([BrezziDouglasMarini1985]). -/
theorem finrank_polyForm_two_one (hd : Fintype.card d = 2) (r : ℕ) :
    Module.finrank K (polyForm K d r 1) = (r + 1) * (r + 2) := by
  rw [finrank_polyForm, hd, Nat.choose_symm_of_eq_add (show r + 2 = r + 1 + 1 by omega),
    Nat.choose_one_right, Nat.choose_one_right]
  ring

theorem finrank_polyForm_two_two (hd : Fintype.card d = 2) (r : ℕ) :
    2 * Module.finrank K (polyForm K d r 2) = (r + 1) * (r + 2) := by
  rw [finrank_polyForm, hd, Nat.choose_self, one_mul, two_mul_choose_two]
  ring

variable [CharZero K]

/-- Nédélec edge elements of the first kind ([Nedelec1980]). -/
theorem finrank_polyFormMinus_three_one (hd : Fintype.card d = 3) {r : ℕ} (hr : 1 ≤ r) :
    2 * Module.finrank K (polyFormMinus K d r 1) = r * (r + 2) * (r + 3) := by
  rw [finrank_polyFormMinus hr, hd, Nat.add_sub_cancel, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 1 + 2 by omega), ← mul_assoc,
    two_mul_choose_two (r + 1)]
  ring

/-- Raviart–Thomas–Nédélec face elements ([RaviartThomas1977], [Nedelec1980]). -/
theorem finrank_polyFormMinus_three_two (hd : Fintype.card d = 3) {r : ℕ} (hr : 1 ≤ r) :
    2 * Module.finrank K (polyFormMinus K d r 2) = r * (r + 1) * (r + 3) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  rw [finrank_polyFormMinus hr, hd, Nat.choose_symm_of_eq_add
    (show t + 1 + 3 = t + 1 + 2 + 1 by omega), Nat.choose_one_right,
    show t + 1 + 2 - 1 = t + 2 by omega, mul_left_comm, two_mul_choose_two t]
  ring

/-- Raviart–Thomas elements on triangles ([RaviartThomas1977]). -/
theorem finrank_polyFormMinus_two_one (hd : Fintype.card d = 2) {r : ℕ} (hr : 1 ≤ r) :
    Module.finrank K (polyFormMinus K d r 1) = r * (r + 2) := by
  rw [finrank_polyFormMinus hr, hd, Nat.add_sub_cancel, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 2 = r + 1 + 1 by omega), Nat.choose_one_right]
  ring

end Feec.Koszul
