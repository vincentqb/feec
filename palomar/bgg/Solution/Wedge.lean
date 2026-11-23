module

public import Solution.Forms
public import Feec.FiniteElement.WeakSymmetryMaps

/-!
# The connecting map of the challenge is `Feec`'s

`wedge Ω k`, `S v = Σₐ dxₐ ∧ vₐ`, is `Feec.FiniteElement.wsL2` (`wedge_eq`), through the
coefficients `wsCoeff_eq` of `S(eₐ ⊗ dx_r) = dxₐ ∧ dx_r`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement

variable {n : ℕ}


/-- The coefficients of `S(eₐ ⊗ dx_r) = dxₐ ∧ dx_r`. -/
theorem wsCoeff_eq {k : ℤ} (t : FormIdx n (k + 1)) (a : Fin n) (r : FormIdx n k) :
    wsCoeff k t (a, r) = if a ∈ t.1 ∧ r.1 = t.1.erase a then sgn a t.1 else 0 := by
  rw [wsCoeff, coordWedgeSum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single a (fun i _ hia => by simp [hia]) (by simp)]
  simp only [ite_true]
  split_ifs with h
  · rw [Finset.sum_eq_single a (fun j _ hja => by simp [hja]) (fun ha => absurd h.1 ha)]
    simp [h.2, sgn_eq]
  · refine Finset.sum_eq_zero fun j hj => ?_
    by_cases hja : j = a
    · subst hja
      have : ¬ t.1.erase j = r.1 := fun e => h ⟨hj, e.symm⟩
      simp [this]
    · simp [hja]

theorem card_erase_of_mem {k : ℤ} (t : FormIdx n (k + 1)) {a : Fin n} (ha : a ∈ t.1) :
    ((t.1.erase a).card : ℤ) = k := by
  rw [Finset.card_erase_of_mem ha, Nat.cast_sub (Finset.card_pos.2 ⟨a, ha⟩), t.2]
  ring

/-- **The connecting map of the challenge is `Feec`'s `wsL2`.** -/
theorem wedge_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) : wedge Ω k = wsL2 (Ω := Ω) k := by
  ext v t : 2
  rw [wsL2_apply, Fintype.sum_prod_type]
  simp only [wedge, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
    ContinuousLinearMap.pi_apply, _root_.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ t.1
  · rw [dite_eq_left ha, Finset.sum_eq_single ⟨t.1.erase a, card_erase_of_mem t ha⟩]
    · simp [wsCoeff_eq, ha]
    · intro r _ hr
      rw [wsCoeff_eq, ite_eq_right_iff.2 (fun h => absurd (Subtype.ext h.2) hr), zero_smul]
    · simp
  · rw [dite_eq_right ha]
    change (0 : _) = _
    exact (Finset.sum_eq_zero fun r _ => by
      rw [wsCoeff_eq, ite_eq_right_iff.2 (fun h => absurd h.1 ha), zero_smul]).symm

end FEEC
