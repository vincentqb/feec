module

public import Feec.Algebra.ExteriorFibre
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Polynomial differential forms: the de Rham and Koszul differentials

Polynomial differential forms on `R^d` as coefficient functions `ω : Finset d → R[x_d]`, with the
exterior derivative `d`, the Koszul differential `κ`, `d² = 0`, `κ² = 0` and the homotopy formula
([AFW2006], §3; [QuennevilleBelair2015], §4.7).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul

open ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d] [Fintype d]

variable (R d) in
/-- Polynomial differential forms on `R^d`, as coefficient functions in the basis `dx_s`. -/
abbrev PolyForm := Finset d → MvPolynomial d R

/-- The exterior derivative `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}`. -/
def extDeriv (ω : PolyForm R d) : PolyForm R d :=
  fun s => ∑ j ∈ s, sgn j s * pderiv j (ω (s.erase j))

/-- The Koszul differential `(κω)_s = Σ_{j ∉ s} ε(j, s) x_j ω_{s ∪ j}`. -/
def koszul (ω : PolyForm R d) : PolyForm R d := interior (fun j => X j) ω

omit [Fintype d] in
theorem extDeriv_apply (ω : PolyForm R d) (s : Finset d) :
    extDeriv ω s = ∑ j ∈ s, sgn j s * pderiv j (ω (s.erase j)) := rfl

theorem koszul_apply (ω : PolyForm R d) (s : Finset d) :
    koszul ω s = ∑ j ∈ sᶜ, sgn j s * X j * ω (insert j s) := rfl

omit [Fintype d] in
theorem pderiv_sgn (i j : d) (s : Finset d) :
    pderiv i (sgn j s : MvPolynomial d R) = 0 := by
  rw [sgn, (pderiv i).leibniz_pow, map_neg, pderiv_one, neg_zero]
  simp

omit [Fintype d] in
theorem pderiv_sgn_mul (i j : d) (s : Finset d) (f : MvPolynomial d R) :
    pderiv i (sgn j s * f) = sgn j s * pderiv i f := by
  rw [pderiv_mul, pderiv_sgn, zero_mul, zero_add]

omit [Fintype d] in
@[simp] theorem extDeriv_zero : extDeriv (0 : PolyForm R d) = 0 := by
  funext s; simp [extDeriv_apply]

@[simp] theorem koszul_zero : koszul (0 : PolyForm R d) = 0 := by
  funext s; simp [koszul_apply]

omit [Fintype d] in
theorem extDeriv_add (ω η : PolyForm R d) : extDeriv (ω + η) = extDeriv ω + extDeriv η := by
  funext s; simp [extDeriv, mul_add, sum_add_distrib]

theorem koszul_add (ω η : PolyForm R d) : koszul (ω + η) = koszul ω + koszul η :=
  interior_add _ ω η

omit [Fintype d] in
theorem extDeriv_extDeriv (ω : PolyForm R d) : extDeriv (extDeriv ω) = 0 := by
  funext s
  simp only [extDeriv_apply, Pi.zero_apply, map_sum, pderiv_sgn_mul, mul_sum]
  refine sum_sum_erase_eq_zero s (fun j l => sgn j s * (sgn l (s.erase j) *
      pderiv j (pderiv l (ω ((s.erase j).erase l))))) fun j hj l hl hjl => ?_
  rw [sgn_erase hj, sgn_erase hl, show (s.erase l).erase j = (s.erase j).erase l from
    erase_right_comm, pderiv_comm l j]
  have := ite_lt_add_ite_lt (R := MvPolynomial d R) hjl
  linear_combination (sgn j s * sgn l s * pderiv j (pderiv l (ω ((s.erase j).erase l)))) * this

theorem koszul_koszul (ω : PolyForm R d) : koszul (koszul ω) = 0 :=
  interior_interior_self _ ω

/-- **The homotopy formula** `((dκ + κd) ω)_s = #s ω_s + Σⱼ x_j ∂_j ω_s`
([QuennevilleBelair2015], §4.7; [AFW2006], (3.9)). -/
theorem extDeriv_koszul_add_koszul_extDeriv (ω : PolyForm R d) (s : Finset d) :
    extDeriv (koszul ω) s + koszul (extDeriv ω) s =
      (#s : MvPolynomial d R) * ω s + ∑ j, X j * pderiv j (ω s) := by
  simp only [extDeriv_apply, koszul_apply]
  -- `dκ`: the diagonal terms `l = j` and the cross terms
  have hA : ∀ j ∈ s, sgn j s * pderiv j (∑ l ∈ (s.erase j)ᶜ, sgn l (s.erase j) * X l *
      ω (insert l (s.erase j))) = (ω s + X j * pderiv j (ω s)) + ∑ l ∈ sᶜ,
        sgn j s * (sgn l (s.erase j) * X l * pderiv j (ω (insert l (s.erase j)))) := by
    intro j hj
    rw [compl_erase, sum_insert (by simp [hj]), map_add, mul_add, sgn_erase_self, insert_erase hj,
      map_sum, mul_sum]
    congr 1
    · rw [mul_assoc, pderiv_sgn_mul, pderiv_mul, pderiv_X_self, one_mul, ← mul_assoc,
        sgn_mul_self, one_mul]
    · refine sum_congr rfl fun l hl => ?_
      have hlj : l ≠ j := fun h => (mem_compl.1 hl) (h ▸ hj)
      rw [mul_assoc, pderiv_sgn_mul, pderiv_mul, pderiv_X_of_ne hlj, zero_mul, zero_add]
      ring
  have hB : ∀ l ∈ sᶜ, sgn l s * X l * ∑ j ∈ insert l s, sgn j (insert l s) *
      pderiv j (ω ((insert l s).erase j)) = X l * pderiv l (ω s) + ∑ j ∈ s,
        sgn l s * X l * (sgn j (insert l s) * pderiv j (ω ((insert l s).erase j))) := by
    intro l hl
    have hl' : l ∉ s := mem_compl.1 hl
    rw [sum_insert hl', mul_add, mul_sum, sgn_insert_self, erase_insert hl']
    congr 1
    have := sgn_mul_self (R := MvPolynomial d R) l s
    linear_combination (X l * pderiv l (ω s)) * this
  rw [sum_congr rfl hA, sum_congr rfl hB, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  have hcross : ∑ j ∈ s, ∑ l ∈ sᶜ, sgn j s * (sgn l (s.erase j) * X l *
      pderiv j (ω (insert l (s.erase j)))) + ∑ l ∈ sᶜ, ∑ j ∈ s, sgn l s * X l *
        (sgn j (insert l s) * pderiv j (ω ((insert l s).erase j))) = 0 := by
    rw [sum_comm (s := sᶜ), ← sum_add_distrib]
    refine sum_eq_zero fun j hj => ?_
    rw [← sum_add_distrib]
    refine sum_eq_zero fun l hl => ?_
    have hl' : l ∉ s := mem_compl.1 hl
    have hjl : j ≠ l := fun h => hl' (h ▸ hj)
    rw [sgn_erase hj, sgn_insert hl', erase_insert_of_ne hjl.symm]
    have := ite_lt_add_ite_lt (R := MvPolynomial d R) hjl
    linear_combination (sgn j s * sgn l s * X l * pderiv j (ω (insert l (s.erase j)))) * this
  have hsum : ∑ j ∈ s, ω s + (∑ j ∈ s, X j * pderiv j (ω s) + ∑ l ∈ sᶜ, X l * pderiv l (ω s)) =
      (#s : MvPolynomial d R) * ω s + ∑ j, X j * pderiv j (ω s) := by
    rw [sum_add_sum_compl, sum_const, nsmul_eq_mul]
  linear_combination hcross + hsum

/-- All coefficients of `ω` are homogeneous of degree `r`. -/
def IsHomogeneousForm (r : ℕ) (ω : PolyForm R d) : Prop := ∀ s, (ω s).IsHomogeneous r

theorem extDeriv_koszul_add_koszul_extDeriv_of_isHomogeneous {r k : ℕ} {ω : PolyForm R d}
    (hr : IsHomogeneousForm r ω) (hk : IsDeg k ω) :
    extDeriv (koszul ω) + koszul (extDeriv ω) = ((r + k : ℕ) : MvPolynomial d R) • ω := by
  funext s
  rw [Pi.add_apply, extDeriv_koszul_add_koszul_extDeriv, (hr s).sum_X_mul_pderiv, Pi.smul_apply,
    smul_eq_mul, nsmul_eq_mul]
  by_cases hs : #s = k
  · rw [hs]; push_cast; ring
  · rw [hk s hs]; ring

omit [Fintype d] in
theorem isHomogeneous_sgn (j : d) (s : Finset d) :
    (sgn j s : MvPolynomial d R).IsHomogeneous 0 := by
  rw [show (sgn j s : MvPolynomial d R) = C (sgn j s) by simp [sgn]]
  exact isHomogeneous_C _ _

omit [Fintype d] in
theorem IsHomogeneousForm.extDeriv {r : ℕ} {ω : PolyForm R d} (h : IsHomogeneousForm r ω) :
    IsHomogeneousForm (r - 1) (extDeriv ω) := fun s =>
  IsHomogeneous.sum _ _ _ fun j _ => by
    have := (isHomogeneous_sgn (R := R) j s).mul ((h (s.erase j)).pderiv (i := j))
    simpa using this

theorem IsHomogeneousForm.koszul {r : ℕ} {ω : PolyForm R d}
    (h : IsHomogeneousForm r ω) : IsHomogeneousForm (r + 1) (koszul ω) := fun s =>
  IsHomogeneous.sum _ _ _ fun j _ => by
    have := ((isHomogeneous_sgn (R := R) j s).mul (isHomogeneous_X R j)).mul (h (insert j s))
    rwa [zero_add, add_comm] at this

omit [Fintype d] in
theorem IsDeg.extDeriv {k : ℕ} {ω : PolyForm R d} (hω : IsDeg k ω) :
    IsDeg (k + 1) (extDeriv ω) := fun s hs => by
  refine sum_eq_zero fun j hj => ?_
  have := card_pos.2 ⟨j, hj⟩
  rw [hω (s.erase j) (by rw [card_erase_of_mem hj]; omega), map_zero, mul_zero]

theorem IsDeg.koszul {k : ℕ} {ω : PolyForm R d} (hω : IsDeg (k + 1) ω) :
    IsDeg k (koszul ω) := hω.interior _

end Feec.Koszul
