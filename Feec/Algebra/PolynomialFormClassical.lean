module

public import Feec.Algebra.PolynomialFormDim

/-!
# The classical polynomial form spaces in dimensions two and three

The local spaces of the periodic table ([ArnoldLogg2014]; [AFW2006], §3; [AFW2010], §5.1) on
`K^d` with `#d = 3` or `#d = 2`, in closed form over every field `K` (of characteristic `0` for the
trimmed spaces), specializing `Feec.Koszul.finrank_polyForm` and `Feec.Koszul.finrank_polyFormMinus`
of `Feec.Algebra.PolynomialFormDim`:

* in three dimensions, `dim P_rΛ⁰ = dim P_rΛ³ = (r+1)(r+2)(r+3)/6` (Lagrange, discontinuous `P_r`),
  `dim P_rΛ¹ = dim P_rΛ² = (r+1)(r+2)(r+3)/2` (Nédélec second kind [Nedelec1986],
  Brezzi–Douglas–Marini [BrezziDouglasMarini1985]), `dim P_r⁻Λ¹ = r(r+2)(r+3)/2` (Nédélec first
  kind [Nedelec1980]), `dim P_r⁻Λ² = r(r+1)(r+3)/2` (Raviart–Thomas–Nédélec [RaviartThomas1977]):
  `finrank_polyForm_three_zero`, …, `finrank_polyFormMinus_three_two`;
* in two dimensions, `dim P_rΛ⁰ = dim P_rΛ² = (r+1)(r+2)/2`, `dim P_rΛ¹ = (r+1)(r+2)`,
  `dim P_r⁻Λ¹ = r(r+2)` (Raviart–Thomas): `finrank_polyForm_two_zero`, …,
  `finrank_polyFormMinus_two_one`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.1
* [D. N. Arnold, A. Logg, *Periodic table of the finite elements*][ArnoldLogg2014]
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

/-- **Lagrange `P_r` on tetrahedra**: `dim P_rΛ⁰(K³) = (r+1)(r+2)(r+3)/6`. [AFW2006], §3 -/
theorem finrank_polyForm_three_zero (hd : Fintype.card d = 3) (r : ℕ) :
    6 * Module.finrank K (polyForm K d r 0) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polyForm, hd, add_zero, Nat.choose_zero_right, mul_one,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 3 by rfl), six_mul_choose_three]
  ring

/-- **Nédélec edge elements of the second kind** ([Nedelec1986]):
`dim P_rΛ¹(K³) = (r+1)(r+2)(r+3)/2`. -/
theorem finrank_polyForm_three_one (hd : Fintype.card d = 3) (r : ℕ) :
    2 * Module.finrank K (polyForm K d r 1) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polyForm, hd, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 1 + 2 by omega), ← mul_assoc,
    two_mul_choose_two (r + 1)]
  ring

/-- **Brezzi–Douglas–Marini face elements** ([BrezziDouglasMarini1985], [Nedelec1986]):
`dim P_rΛ²(K³) = (r+1)(r+2)(r+3)/2`. -/
theorem finrank_polyForm_three_two (hd : Fintype.card d = 3) (r : ℕ) :
    2 * Module.finrank K (polyForm K d r 2) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polyForm, hd, Nat.choose_symm_of_eq_add (show r + 3 = r + 2 + 1 by omega),
    Nat.choose_one_right, mul_left_comm, two_mul_choose_two r]
  ring

/-- **Discontinuous `P_r` on tetrahedra**: `dim P_rΛ³(K³) = (r+1)(r+2)(r+3)/6`. [AFW2006], §3 -/
theorem finrank_polyForm_three_three (hd : Fintype.card d = 3) (r : ℕ) :
    6 * Module.finrank K (polyForm K d r 3) = (r + 1) * (r + 2) * (r + 3) := by
  rw [finrank_polyForm, hd, Nat.choose_self, one_mul, six_mul_choose_three]
  ring

/-- **Lagrange `P_r` on triangles**: `dim P_rΛ⁰(K²) = (r+1)(r+2)/2`. [AFW2006], §3 -/
theorem finrank_polyForm_two_zero (hd : Fintype.card d = 2) (r : ℕ) :
    2 * Module.finrank K (polyForm K d r 0) = (r + 1) * (r + 2) := by
  rw [finrank_polyForm, hd, add_zero, Nat.choose_zero_right, mul_one,
    Nat.choose_symm_of_eq_add (show r + 2 = r + 2 by rfl), two_mul_choose_two]
  ring

/-- **Brezzi–Douglas–Marini elements on triangles** ([BrezziDouglasMarini1985]):
`dim P_rΛ¹(K²) = (r+1)(r+2)`. -/
theorem finrank_polyForm_two_one (hd : Fintype.card d = 2) (r : ℕ) :
    Module.finrank K (polyForm K d r 1) = (r + 1) * (r + 2) := by
  rw [finrank_polyForm, hd, Nat.choose_symm_of_eq_add (show r + 2 = r + 1 + 1 by omega),
    Nat.choose_one_right, Nat.choose_one_right]
  ring

/-- **Discontinuous `P_r` on triangles**: `dim P_rΛ²(K²) = (r+1)(r+2)/2`. [AFW2006], §3 -/
theorem finrank_polyForm_two_two (hd : Fintype.card d = 2) (r : ℕ) :
    2 * Module.finrank K (polyForm K d r 2) = (r + 1) * (r + 2) := by
  rw [finrank_polyForm, hd, Nat.choose_self, one_mul, two_mul_choose_two]
  ring

variable [CharZero K]

/-- **Nédélec edge elements of the first kind** ([Nedelec1980]):
`dim P_r⁻Λ¹(K³) = r(r+2)(r+3)/2`. -/
theorem finrank_polyFormMinus_three_one (hd : Fintype.card d = 3) {r : ℕ} (hr : 1 ≤ r) :
    2 * Module.finrank K (polyFormMinus K d r 1) = r * (r + 2) * (r + 3) := by
  rw [finrank_polyFormMinus hr, hd, Nat.add_sub_cancel, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 3 = r + 1 + 2 by omega), ← mul_assoc,
    two_mul_choose_two (r + 1)]
  ring

/-- **Raviart–Thomas–Nédélec face elements** ([RaviartThomas1977], [Nedelec1980]):
`dim P_r⁻Λ²(K³) = r(r+1)(r+3)/2`. -/
theorem finrank_polyFormMinus_three_two (hd : Fintype.card d = 3) {r : ℕ} (hr : 1 ≤ r) :
    2 * Module.finrank K (polyFormMinus K d r 2) = r * (r + 1) * (r + 3) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  rw [finrank_polyFormMinus hr, hd, Nat.choose_symm_of_eq_add
    (show t + 1 + 3 = t + 1 + 2 + 1 by omega), Nat.choose_one_right,
    show t + 1 + 2 - 1 = t + 2 by omega, mul_left_comm, two_mul_choose_two t]
  ring

/-- **Raviart–Thomas elements on triangles** ([RaviartThomas1977]; the rotated Nédélec edge
elements of the first kind): `dim P_r⁻Λ¹(K²) = r(r+2)`. -/
theorem finrank_polyFormMinus_two_one (hd : Fintype.card d = 2) {r : ℕ} (hr : 1 ≤ r) :
    Module.finrank K (polyFormMinus K d r 1) = r * (r + 2) := by
  rw [finrank_polyFormMinus hr, hd, Nat.add_sub_cancel, Nat.choose_one_right,
    Nat.choose_symm_of_eq_add (show r + 2 = r + 1 + 1 by omega), Nat.choose_one_right]
  ring

end Feec.Koszul
