module

public import Feec.Algebra.Koszul

/-!
# Vector proxies in three dimensions

On `R³` (index type `Fin 3`), polynomial `0`-, `1`-, `2`-, `3`-forms are identified with scalar
and vector fields: `f = ω_∅`, `v_i = ω_{i}`, `u = (ω_{12}, -ω_{02}, ω_{01})`, `g = ω_{012}`.
Under these identifications the exterior derivative is `grad`, `curl`, `div`, and the Koszul
differential is `x ·`, `· × x`, `· x`:

* `vec1_extDeriv` (`d = grad`), `vec2_extDeriv` (`d = curl`), `vol_extDeriv` (`d = div`);
* `koszul_empty` (`κ v = x · v`), `vec1_koszul` (`κ u = u × x`), `vec2_koszul` (`κ g = g x`).

These are the 3D formulas of [AFW2006], §3 used for the Nédélec spaces `P_r⁻Λ¹`, `P_r⁻Λ²` in
thesis §4.10 (`P_r⁻Λ¹ = P_{r-1}³ ⊕ H_{r-1}³ × x`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.7, §4.10
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul.Proxy3

open ExteriorFibre

variable {R : Type*} [CommRing R]

/-- Polynomial vector fields on `R³`. -/
abbrev PolyVec (R : Type*) [CommRing R] := Fin 3 → MvPolynomial (Fin 3) R

/-- The gradient of a polynomial. -/
def grad (f : MvPolynomial (Fin 3) R) : PolyVec R := fun i => pderiv i f

/-- The curl of a polynomial vector field. -/
def curl (v : PolyVec R) : PolyVec R :=
  ![pderiv 1 (v 2) - pderiv 2 (v 1), pderiv 2 (v 0) - pderiv 0 (v 2),
    pderiv 0 (v 1) - pderiv 1 (v 0)]

/-- The divergence of a polynomial vector field. -/
def div (v : PolyVec R) : MvPolynomial (Fin 3) R := ∑ i, pderiv i (v i)

/-- The position field `x`. -/
def pos : PolyVec R := fun i => X i

/-- The cross product of polynomial vector fields. -/
def cross (u v : PolyVec R) : PolyVec R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The proxy of a `1`-form: `v_i = ω_{i}`. -/
def vec1 (ω : PolyForm R (Fin 3)) : PolyVec R := fun i => ω {i}

/-- The proxy of a `2`-form: `u = (ω_{12}, -ω_{02}, ω_{01})`. -/
def vec2 (ω : PolyForm R (Fin 3)) : PolyVec R := ![ω {1, 2}, -ω {0, 2}, ω {0, 1}]

/-- The proxy of a `3`-form: `g = ω_{012}`. -/
def vol (ω : PolyForm R (Fin 3)) : MvPolynomial (Fin 3) R := ω {0, 1, 2}

/-- `d = grad` on `0`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vec1_extDeriv (ω : PolyForm R (Fin 3)) : vec1 (extDeriv ω) = grad (ω ∅) := by
  funext i
  simp [vec1, grad, extDeriv_apply, sgn, Finset.filter_singleton]

/-- `d = curl` on `1`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vec2_extDeriv (ω : PolyForm R (Fin 3)) : vec2 (extDeriv ω) = curl (vec1 ω) := by
  funext i
  fin_cases i <;> simp [vec2, vec1, curl, extDeriv_apply, sgn, Finset.filter_insert,
    Finset.filter_singleton, Finset.erase_insert_eq_erase, Finset.erase_insert_of_ne,
    Finset.erase_singleton] <;> ring

/-- `d = div` on `2`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vol_extDeriv (ω : PolyForm R (Fin 3)) : vol (extDeriv ω) = div (vec2 ω) := by
  simp [vol, vec2, div, Fin.sum_univ_three, extDeriv_apply, sgn, Finset.filter_insert,
    Finset.filter_singleton, Finset.erase_insert_eq_erase, Finset.erase_insert_of_ne,
    Finset.erase_singleton]
  ring

private theorem compl_0 : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
private theorem compl_1 : ({1} : Finset (Fin 3))ᶜ = {0, 2} := by decide
private theorem compl_2 : ({2} : Finset (Fin 3))ᶜ = {0, 1} := by decide
private theorem compl_12 : ({1, 2} : Finset (Fin 3))ᶜ = {0} := by decide
private theorem compl_02 : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide
private theorem compl_01 : ({0, 1} : Finset (Fin 3))ᶜ = {2} := by decide
private theorem ins_10 : (insert 1 {0} : Finset (Fin 3)) = {0, 1} := by decide
private theorem ins_20 : (insert 2 {0} : Finset (Fin 3)) = {0, 2} := by decide
private theorem ins_21 : (insert 2 {1} : Finset (Fin 3)) = {1, 2} := by decide
private theorem ins_0_12 : (insert 0 {1, 2} : Finset (Fin 3)) = {0, 1, 2} := by decide
private theorem ins_1_02 : (insert 1 {0, 2} : Finset (Fin 3)) = {0, 1, 2} := by decide
private theorem ins_2_01 : (insert 2 {0, 1} : Finset (Fin 3)) = {0, 1, 2} := by decide

/-- `κ = x ·` on `1`-forms. [QuennevilleBelair2015], §4.10 -/
theorem koszul_empty (ω : PolyForm R (Fin 3)) : koszul ω ∅ = ∑ i, pos i * vec1 ω i := by
  simp [koszul_apply, pos, vec1, Fin.sum_univ_three, sgn]

/-- `κ = · × x` on `2`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vec1_koszul (ω : PolyForm R (Fin 3)) : vec1 (koszul ω) = cross (vec2 ω) pos := by
  funext i
  fin_cases i <;> simp [vec1, vec2, cross, pos, koszul_apply, compl_0, compl_1, compl_2, sgn,
    Finset.filter_singleton, ins_10, ins_20, ins_21] <;> ring

/-- `κ = · x` on `3`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vec2_koszul (ω : PolyForm R (Fin 3)) : vec2 (koszul ω) = fun i => vol ω * pos i := by
  funext i
  fin_cases i
  · show koszul ω {1, 2} = ω {0, 1, 2} * X 0
    rw [koszul_apply, compl_12, sum_singleton, ins_0_12]
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, mul_comm]
  · show -koszul ω {0, 2} = ω {0, 1, 2} * X 1
    rw [koszul_apply, compl_02, sum_singleton, ins_1_02]
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, mul_comm]
  · show koszul ω {0, 1} = ω {0, 1, 2} * X 2
    rw [koszul_apply, compl_01, sum_singleton, ins_2_01]
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, mul_comm]

end Feec.Koszul.Proxy3
