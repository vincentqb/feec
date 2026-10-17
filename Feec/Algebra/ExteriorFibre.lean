module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# The exterior algebra in coordinates, over any commutative ring

Alternating forms on `R^d` (`d` a finite linearly ordered index type, `R` any commutative ring)
in the basis `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (`s₁ < ⋯ < s_k`): a form is its coefficient function
`ω : Finset d → R`, and `k`-forms are those supported on `k`-subsets. With the sign
`ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` into place:

* exterior multiplication by a covector `ξ`: `(ξ ∧ ω)_s = Σ_{j ∈ s} ε(j, s) ξ_j ω_{s ∖ j}`;
* interior multiplication (contraction) by a vector `ζ`:
  `(ι_ζ ω)_s = Σ_{j ∉ s} ε(j, s) ζ_j ω_{s ∪ j}`.

This is the algebraic layer under the de Rham and Koszul complexes of polynomial forms
(`Feec.Algebra.Koszul`) in any dimension; the analytic symbol version over `RCLike` is
`Feec.Fourier.Exterior`.

## Main results

* `wedge_wedge_add_wedge_wedge`, `wedge_wedge_self`: `ξ ∧ η ∧ ω = -η ∧ ξ ∧ ω`, `ξ ∧ ξ ∧ ω = 0`;
* `interior_interior_add_interior_interior`, `interior_interior_self`: the same for contractions;
* **Cartan** `wedge_interior_add_interior_wedge`: `ξ ∧ ι_ζ ω + ι_ζ (ξ ∧ ω) = ⟨ξ, ζ⟩ ω`;
* degrees: `wedge_of_card_ne`, `interior_of_card_ne` (`∧` raises, `ι` lowers the form degree);
* `sum_wedge_single_interior_single`: `Σⱼ dx_j ∧ ι_{e_j} ω = (form degree) · ω`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3 (the Koszul complex)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6
-/

open Finset

@[expose] public noncomputable section

namespace Feec.ExteriorFibre

variable {R : Type*} [CommRing R] {d : Type*} [LinearOrder d]

/-! ### Signs -/

/-- The sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}` of moving `dx_j` to its place in `dx_s`. -/
def sgn (j : d) (s : Finset d) : R := (-1) ^ #({l ∈ s | l < j})

theorem sgn_mul_self (j : d) (s : Finset d) : (sgn j s : R) * sgn j s = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul]; simp

theorem sgn_erase_self (j : d) (s : Finset d) : (sgn j (s.erase j) : R) = sgn j s := by
  rw [sgn, sgn, filter_erase, erase_eq_of_notMem (by simp)]

theorem sgn_insert_self (j : d) (s : Finset d) : (sgn j (insert j s) : R) = sgn j s := by
  rw [sgn, sgn, filter_insert]
  simp

theorem sgn_erase {j l : d} {s : Finset d} (hj : j ∈ s) :
    (sgn l (s.erase j) : R) = (if j < l then -1 else 1) * sgn l s := by
  rw [sgn, sgn, filter_erase]
  split_ifs with h
  · have hm : j ∈ {x ∈ s | x < l} := mem_filter.2 ⟨hj, h⟩
    rw [card_erase_of_mem hm]
    obtain ⟨n, hn⟩ : ∃ n, #({x ∈ s | x < l}) = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (card_pos.2 ⟨j, hm⟩)).symm⟩
    rw [hn, Nat.add_sub_cancel, pow_succ]; ring
  · rw [Finset.erase_eq_of_notMem (s := {x ∈ s | x < l}) (fun hm => h (mem_filter.1 hm).2),
      one_mul]

theorem sgn_insert {j l : d} {s : Finset d} (hj : j ∉ s) :
    (sgn l (insert j s) : R) = (if j < l then -1 else 1) * sgn l s := by
  rw [sgn, sgn, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun hm => hj (mem_filter.1 hm).1), pow_succ]; ring
  · rw [one_mul]

theorem ite_lt_add_ite_lt {j l : d} (hjl : j ≠ l) :
    ((if j < l then -1 else 1) + (if l < j then -1 else 1) : R) = 0 := by
  rcases lt_or_gt_of_ne hjl with h | h
  · simp only [h, not_lt.2 h.le, ↓reduceIte]; ring
  · simp only [h, not_lt.2 h.le, ↓reduceIte]; ring

/-- A sum over ordered pairs of distinct elements of `s` of an antisymmetric function vanishes
(no division by `2`: the pairs `(j, l)` and `(l, j)` cancel). -/
theorem sum_sum_erase_eq_zero (s : Finset d) (F : d → d → R)
    (hF : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → F l j = -F j l) :
    ∑ j ∈ s, ∑ l ∈ s.erase j, F j l = 0 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) (fun x hx => ?_) (fun x hx _ => ?_)
    (fun x hx => ?_) (fun x _ => rfl)
  · obtain ⟨hj, hl⟩ := Finset.mem_sigma.1 hx
    rw [hF x.1 hj x.2 (mem_of_mem_erase hl) (ne_of_mem_erase hl).symm, add_neg_cancel]
  · obtain ⟨-, hl⟩ := Finset.mem_sigma.1 hx
    intro h
    exact (ne_of_mem_erase hl) (by simpa using congrArg Sigma.fst h)
  · obtain ⟨hj, hl⟩ := Finset.mem_sigma.1 hx
    exact Finset.mem_sigma.2 ⟨mem_of_mem_erase hl, mem_erase.2 ⟨(ne_of_mem_erase hl).symm, hj⟩⟩

/-! ### Exterior and interior multiplication -/

/-- Exterior multiplication by a covector, `(ξ ∧ ω)_s = Σ_{j ∈ s} ε(j, s) ξ_j ω_{s ∖ j}`. -/
def wedge (ξ : d → R) (ω : Finset d → R) (s : Finset d) : R :=
  ∑ j ∈ s, sgn j s * ξ j * ω (s.erase j)

variable [Fintype d]

/-- Interior multiplication by a vector, `(ι_ζ ω)_s = Σ_{j ∉ s} ε(j, s) ζ_j ω_{s ∪ j}`. -/
def interior (ζ : d → R) (ω : Finset d → R) (s : Finset d) : R :=
  ∑ j ∈ sᶜ, sgn j s * ζ j * ω (insert j s)

omit [Fintype d] in
theorem wedge_apply (ξ : d → R) (ω : Finset d → R) (s : Finset d) :
    wedge ξ ω s = ∑ j ∈ s, sgn j s * ξ j * ω (s.erase j) := rfl

theorem interior_apply (ζ : d → R) (ω : Finset d → R) (s : Finset d) :
    interior ζ ω s = ∑ j ∈ sᶜ, sgn j s * ζ j * ω (insert j s) := rfl

omit [Fintype d] in
theorem wedge_add (ξ : d → R) (ω η : Finset d → R) : wedge ξ (ω + η) = wedge ξ ω + wedge ξ η := by
  funext s; simp [wedge, mul_add, sum_add_distrib]

omit [Fintype d] in
theorem wedge_smul (ξ : d → R) (c : R) (ω : Finset d → R) : wedge ξ (c • ω) = c • wedge ξ ω := by
  funext s; simp [wedge, mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem interior_add (ζ : d → R) (ω η : Finset d → R) :
    interior ζ (ω + η) = interior ζ ω + interior ζ η := by
  funext s; simp [interior, mul_add, sum_add_distrib]

theorem interior_smul (ζ : d → R) (c : R) (ω : Finset d → R) :
    interior ζ (c • ω) = c • interior ζ ω := by
  funext s; simp [interior, mul_sum]; exact sum_congr rfl fun _ _ => by ring

omit [Fintype d] in
/-- `ξ ∧ ·` is `R`-linear in `ξ`. -/
theorem wedge_add_left (ξ η : d → R) (ω : Finset d → R) :
    wedge (ξ + η) ω = wedge ξ ω + wedge η ω := by
  funext s; simp [wedge, mul_add, add_mul, sum_add_distrib]

theorem interior_add_left (ζ ζ' : d → R) (ω : Finset d → R) :
    interior (ζ + ζ') ω = interior ζ ω + interior ζ' ω := by
  funext s; simp [interior, mul_add, add_mul, sum_add_distrib]

omit [Fintype d] in
/-- **Anticommutation** `ξ ∧ η ∧ ω + η ∧ ξ ∧ ω = 0`. -/
theorem wedge_wedge_add_wedge_wedge (ξ η : d → R) (ω : Finset d → R) :
    wedge ξ (wedge η ω) + wedge η (wedge ξ ω) = 0 := by
  funext s
  simp only [Pi.add_apply, Pi.zero_apply, wedge_apply, mul_sum, ← sum_add_distrib]
  refine sum_sum_erase_eq_zero s (fun j l => sgn j s * ξ j * (sgn l (s.erase j) * η l *
      ω ((s.erase j).erase l)) + sgn j s * η j * (sgn l (s.erase j) * ξ l *
        ω ((s.erase j).erase l))) fun j hj l hl hjl => ?_
  rw [sgn_erase hj, sgn_erase hl, erase_right_comm]
  have := ite_lt_add_ite_lt (R := R) hjl
  linear_combination (sgn j s * sgn l s * ω ((s.erase j).erase l) * (ξ j * η l + η j * ξ l)) * this

omit [Fintype d] in
theorem wedge_wedge_self (ξ : d → R) (ω : Finset d → R) : wedge ξ (wedge ξ ω) = 0 := by
  funext s
  simp only [Pi.zero_apply, wedge_apply, mul_sum]
  refine sum_sum_erase_eq_zero s (fun j l => sgn j s * ξ j * (sgn l (s.erase j) * ξ l *
      ω ((s.erase j).erase l))) fun j hj l hl hjl => ?_
  rw [sgn_erase hj, sgn_erase hl, erase_right_comm]
  have := ite_lt_add_ite_lt (R := R) hjl
  linear_combination (sgn j s * sgn l s * ξ j * ξ l * ω ((s.erase j).erase l)) * this

/-- **Cartan identity** `ξ ∧ ι_ζ ω + ι_ζ (ξ ∧ ω) = ⟨ξ, ζ⟩ ω`. -/
theorem wedge_interior_add_interior_wedge (ξ ζ : d → R) (ω : Finset d → R) :
    wedge ξ (interior ζ ω) + interior ζ (wedge ξ ω) = (∑ j, ξ j * ζ j) • ω := by
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wedge_apply, interior_apply]
  have hA : ∀ j ∈ s, sgn j s * ξ j * ∑ l ∈ (s.erase j)ᶜ, sgn l (s.erase j) * ζ l *
      ω (insert l (s.erase j)) = ξ j * ζ j * ω s + ∑ l ∈ sᶜ,
        sgn j s * ξ j * (sgn l (s.erase j) * ζ l * ω (insert l (s.erase j))) := by
    intro j hj
    rw [compl_erase, sum_insert (by simp [hj]), mul_add, mul_sum, sgn_erase_self, insert_erase hj]
    congr 1
    have := sgn_mul_self (R := R) j s
    linear_combination (ξ j * ζ j * ω s) * this
  have hB : ∀ l ∈ sᶜ, sgn l s * ζ l * ∑ j ∈ insert l s, sgn j (insert l s) * ξ j *
      ω ((insert l s).erase j) = ξ l * ζ l * ω s + ∑ j ∈ s,
        sgn l s * ζ l * (sgn j (insert l s) * ξ j * ω ((insert l s).erase j)) := by
    intro l hl
    have hl' : l ∉ s := mem_compl.1 hl
    rw [sum_insert hl', mul_add, mul_sum, sgn_insert_self, erase_insert hl']
    congr 1
    have := sgn_mul_self (R := R) l s
    linear_combination (ξ l * ζ l * ω s) * this
  rw [sum_congr rfl hA, sum_congr rfl hB, sum_add_distrib, sum_add_distrib]
  have hcross : ∑ j ∈ s, ∑ l ∈ sᶜ, sgn j s * ξ j * (sgn l (s.erase j) * ζ l *
      ω (insert l (s.erase j))) + ∑ l ∈ sᶜ, ∑ j ∈ s, sgn l s * ζ l *
        (sgn j (insert l s) * ξ j * ω ((insert l s).erase j)) = 0 := by
    rw [sum_comm (s := sᶜ), ← sum_add_distrib]
    refine sum_eq_zero fun j hj => ?_
    rw [← sum_add_distrib]
    refine sum_eq_zero fun l hl => ?_
    have hl' : l ∉ s := mem_compl.1 hl
    have hjl : j ≠ l := fun h => hl' (h ▸ hj)
    rw [sgn_erase hj, sgn_insert hl', erase_insert_of_ne hjl.symm]
    have := ite_lt_add_ite_lt (R := R) hjl
    linear_combination (sgn j s * sgn l s * ξ j * ζ l * ω (insert l (s.erase j))) * this
  have hsum : ∑ j ∈ s, ξ j * ζ j * ω s + ∑ l ∈ sᶜ, ξ l * ζ l * ω s =
      (∑ j, ξ j * ζ j) * ω s := by
    rw [← sum_mul, ← sum_mul, ← add_mul, sum_add_sum_compl]
  linear_combination hcross + hsum

/-- Contractions anticommute: `ι_ζ ι_ζ' ω + ι_ζ' ι_ζ ω = 0`. -/
theorem interior_interior_add_interior_interior (ζ ζ' : d → R) (ω : Finset d → R) :
    interior ζ (interior ζ' ω) + interior ζ' (interior ζ ω) = 0 := by
  funext s
  simp only [Pi.add_apply, Pi.zero_apply, interior_apply, mul_sum, ← sum_add_distrib]
  -- reindex the inner sums over `(s ∪ j)ᶜ = sᶜ ∖ j`
  have e : ∀ j ∈ sᶜ, (insert j s)ᶜ = sᶜ.erase j := fun j _ => by
    ext x; simp [eq_comm]
  rw [sum_congr rfl fun j hj => by rw [e j hj]]
  refine sum_sum_erase_eq_zero sᶜ (fun j l => sgn j s * ζ j * (sgn l (insert j s) * ζ' l *
      ω (insert l (insert j s))) + sgn j s * ζ' j * (sgn l (insert j s) * ζ l *
        ω (insert l (insert j s)))) fun j hj l hl hjl => ?_
  rw [sgn_insert (mem_compl.1 hj), sgn_insert (mem_compl.1 hl), Finset.insert_comm]
  have := ite_lt_add_ite_lt (R := R) hjl
  linear_combination (sgn j s * sgn l s * ω (insert l (insert j s)) *
    (ζ j * ζ' l + ζ' j * ζ l)) * this

theorem interior_interior_self (ζ : d → R) (ω : Finset d → R) :
    interior ζ (interior ζ ω) = 0 := by
  funext s
  simp only [Pi.zero_apply, interior_apply, mul_sum]
  have e : ∀ j ∈ sᶜ, (insert j s)ᶜ = sᶜ.erase j := fun j _ => by
    ext x; simp [eq_comm]
  rw [sum_congr rfl fun j hj => by rw [e j hj]]
  refine sum_sum_erase_eq_zero sᶜ (fun j l => sgn j s * ζ j * (sgn l (insert j s) * ζ l *
      ω (insert l (insert j s)))) fun j hj l hl hjl => ?_
  rw [sgn_insert (mem_compl.1 hj), sgn_insert (mem_compl.1 hl), Finset.insert_comm]
  have := ite_lt_add_ite_lt (R := R) hjl
  linear_combination (sgn j s * sgn l s * ζ j * ζ l * ω (insert l (insert j s))) * this

/-! ### Form degree -/

/-- `ω` is a `k`-form: it vanishes off `k`-subsets. -/
def IsDeg (k : ℕ) (ω : Finset d → R) : Prop := ∀ s, #s ≠ k → ω s = 0

omit [Fintype d] in
/-- Exterior multiplication raises the form degree by one. -/
theorem IsDeg.wedge {k : ℕ} {ω : Finset d → R} (hω : IsDeg k ω) (ξ : d → R) :
    IsDeg (k + 1) (wedge ξ ω) := fun s hs => by
  refine sum_eq_zero fun j hj => ?_
  have := card_pos.2 ⟨j, hj⟩
  rw [hω (s.erase j) (by rw [card_erase_of_mem hj]; omega), mul_zero]

/-- Interior multiplication lowers the form degree by one. -/
theorem IsDeg.interior {k : ℕ} {ω : Finset d → R} (hω : IsDeg (k + 1) ω) (ζ : d → R) :
    IsDeg k (interior ζ ω) := fun s hs => by
  refine sum_eq_zero fun j hj => ?_
  rw [hω (insert j s) (by rw [card_insert_of_notMem (mem_compl.1 hj)]; omega), mul_zero]

/-- The **form-degree (number) operator**: `Σⱼ dx_j ∧ ι_{e_j} ω = |s| ω_s` componentwise. -/
theorem sum_wedge_single_interior_single (ω : Finset d → R) (s : Finset d) :
    ∑ j, wedge (Pi.single j 1) (interior (Pi.single j 1) ω) s = #s * ω s := by
  have h := fun j => congrFun (wedge_interior_add_interior_wedge
    (Pi.single j (1 : R)) (Pi.single j 1) ω) s
  have hw : ∀ j, interior (Pi.single j (1 : R)) (wedge (Pi.single j 1) ω) s =
      if j ∈ s then 0 else ω s := by
    intro j
    split_ifs with hj
    · refine sum_eq_zero fun l hl => ?_
      have hl' : l ∉ s := mem_compl.1 hl
      have : l ≠ j := fun h => hl' (h ▸ hj)
      simp [this]
    · rw [interior_apply, sum_eq_single j]
      · rw [wedge_apply, sum_eq_single j]
        · rw [sgn_insert_self, erase_insert hj, Pi.single_eq_same, mul_one, ← mul_assoc,
            sgn_mul_self, one_mul]
        · intro l _ hlj; simp [hlj]
        · intro h; exact absurd (mem_insert_self j s) h
      · intro l _ hlj; simp [hlj]
      · intro h; exact absurd (mem_compl.2 hj) h
  have hsum : ∀ j, (∑ i, (Pi.single j (1 : R) : d → R) i * (Pi.single j 1 : d → R) i) = 1 := by
    intro j; rw [sum_eq_single j] <;> simp [Pi.single_apply]; tauto
  calc ∑ j, wedge (Pi.single j 1) (interior (Pi.single j 1) ω) s
      = ∑ j, (ω s - if j ∈ s then 0 else ω s) := by
        refine sum_congr rfl fun j _ => ?_
        have := h j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsum, one_mul, hw] at this
        linear_combination this
    _ = ∑ j, if j ∈ s then ω s else 0 := sum_congr rfl fun j _ => by split_ifs <;> ring
    _ = #s * ω s := by rw [Finset.sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]

end Feec.ExteriorFibre
