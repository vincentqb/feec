module

public import Solution.Poly
public import Feec.FiniteElement.AffineInvariantForm
public import Feec.Counterexamples.PositiveCharacteristic

/-!
# The bridge for the affinely invariant spaces of polynomial forms

The pullback of the challenge, `(φ^*ω)_t = Σ_{#s = #t} det B_{s,t} (ω_s ∘ φ)`, is
`Feec.FiniteElement.polyPullback` (`pullback_eq`): the minors are the coefficients
`Feec.ExteriorFibre.wedgeProd B s t` (`Feec.ExteriorFibre.wedgeProd_apply_eq_det_submatrix`,
zero off the degree `#s`). The invariance predicates are those of `Feec`
(`isAffineInvariant_iff`, `isLinearInvariant_iff`, `isGLInvariant_iff`), and with the spaces and
differentials of `Solution.Poly` the classification is that of
`Feec.FiniteElement.InvariantForm` and `Feec.FiniteElement.AffineInvariantForm`
(`affineInvariantForms_of_feec`); that characteristic `0` is necessary is
`Feec.Counterexamples.PositiveCharacteristic.charZero_iff_classification` and
`charZero_iff_closed_eq_exact`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace FEEC

variable {K : Type*} [Field K] {n : ℕ}

/-- **The pullback of the challenge is `Feec`'s `polyPullback`.** -/
theorem pullback_eq (B : Fin n → Fin n → K) (b : Fin n → K) (ω : PolyForm K n) :
    pullback K n (Matrix.of B) b ω = Feec.FiniteElement.polyPullback B b ω := by
  funext t
  rw [Feec.FiniteElement.polyPullback_apply, pullback, LinearMap.pi_apply, LinearMap.sum_apply]
  refine sum_congr rfl fun s _ => ?_
  split_ifs with h
  · rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_C_mul,
      mul_comm, Feec.ExteriorFibre.wedgeProd_apply_eq_det_submatrix _ h rfl]
    rfl
  · rw [LinearMap.zero_apply, Feec.ExteriorFibre.isDeg_wedgeProd B s t (Ne.symm h), map_zero,
      mul_zero]

theorem pullback_eq' (B : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (ω : PolyForm K n) :
    pullback K n B b ω = Feec.FiniteElement.polyPullback (Matrix.of.symm B) b ω :=
  pullback_eq (Matrix.of.symm B) b ω

theorem isAffineInvariant_iff (V : Submodule K (PolyForm K n)) :
    IsAffineInvariant K n V ↔ Feec.FiniteElement.IsAffineInvariant V := by
  refine ⟨fun h B b ω hω => ?_, fun h B b => ?_⟩
  · rw [← pullback_eq]; exact h (Matrix.of B) b ⟨ω, hω, rfl⟩
  · rintro _ ⟨ω, hω, rfl⟩; rw [pullback_eq']; exact h _ b ω hω

theorem isLinearInvariant_iff (V : Submodule K (PolyForm K n)) :
    IsLinearInvariant K n V ↔ Feec.FiniteElement.IsLinearInvariant V := by
  refine ⟨fun h B ω hω => ?_, fun h B => ?_⟩
  · rw [← pullback_eq]; exact h (Matrix.of B) ⟨ω, hω, rfl⟩
  · rintro _ ⟨ω, hω, rfl⟩; rw [pullback_eq']; exact h _ ω hω

theorem isGLInvariant_iff (V : Submodule K (PolyForm K n)) :
    IsGLInvariant K n V ↔ Feec.FiniteElement.IsGLInvariant V := by
  refine ⟨fun h g ω hω => ?_, fun h g => ?_⟩
  · have := h g ⟨ω, hω, rfl⟩
    rw [pullback_eq'] at this
    exact this
  · rintro _ ⟨ω, hω, rfl⟩; rw [pullback_eq']; exact h g ω hω

theorem invariantForm_eq (r s k : ℕ) :
    invariantForm K n r s k =
      (Feec.Koszul.polyForm K (Fin n) (r + 1) (k - 1)).map (Feec.Koszul.extDerivₗ K (Fin n)) ⊔
        (Feec.Koszul.polyForm K (Fin n) s (k + 1)).map (Feec.Koszul.koszulₗ K (Fin n)) := by
  rw [invariantForm, polyForm_eq, polyForm_eq, polyExtDeriv_eq, koszul_eq]

variable (K n) in
theorem affineInvariantForms_of_feec [CharZero K] : AffineInvariantForms K n where
  isLinearInvariant_map_homForm r k := by
    rw [isLinearInvariant_iff, isLinearInvariant_iff, homForm_eq, polyExtDeriv_eq, koszul_eq]
    exact ⟨Feec.FiniteElement.isLinearInvariant_map_extDeriv_homForm r k,
      Feec.FiniteElement.isLinearInvariant_map_koszul_homForm r k⟩
  eq_of_le_homForm r k W hW hle := by
    rw [homForm_eq] at hle
    simpa only [homForm_eq, polyExtDeriv_eq, koszul_eq] using
      ((isGLInvariant_iff W).1 hW).eq_of_le_homForm_succ hle
  isAffineInvariant_map_extDeriv r k := by
    rw [isAffineInvariant_iff, polyForm_eq, polyExtDeriv_eq]
    exact Feec.FiniteElement.isAffineInvariant_map_extDeriv _ _
  isAffineInvariant_invariantForm r s k hk hs := by
    rw [isAffineInvariant_iff, invariantForm_eq]
    exact Feec.FiniteElement.isAffineInvariant_sup hk hs
  invariantForm_eq_polyFormMinus r k hk := by
    rw [invariantForm_eq, polyFormMinus_eq]
    exact Feec.FiniteElement.sup_eq_polyFormMinus hk
  invariantForm_eq_polyForm r k hk := by
    rw [invariantForm_eq, polyForm_eq]
    exact Feec.FiniteElement.sup_eq_polyForm hk
  map_extDeriv_polyForm_one k hk := by
    rw [polyForm_eq, polyForm_eq, polyExtDeriv_eq]
    exact Feec.FiniteElement.map_extDeriv_polyForm_one_eq hk
  eq_invariantForm k hk hkn V _ hV hdeg hne := by
    have hA : Feec.FiniteElement.IsAffineInvariant V :=
      Feec.FiniteElement.isAffineInvariant_of_forall_units fun g b ω hω => by
        have := hV g b ⟨ω, hω, rfl⟩
        rw [pullback_eq'] at this
        exact this
    obtain ⟨r, h⟩ := hA.eq_sup (fun ω hω => hdeg ω hω) hk hkn hne
    refine ⟨r, ?_⟩
    rw [polyForm_eq, polyExtDeriv_eq]
    simpa only [invariantForm_eq] using h

variable (K) in
theorem charZero_iff_classification_of_feec :
    CharZero K ↔ ∀ (n r k : ℕ) (W : Submodule K (PolyForm K n)), IsGLInvariant K n W →
      W ≤ homForm K n (r + 1) (k + 1) →
        W = ⊥ ∨ W = (homForm K n (r + 2) k).map (polyExtDeriv K n) ∨
          W = (homForm K n r (k + 2)).map (koszul K n) ∨ W = homForm K n (r + 1) (k + 1) := by
  rw [Feec.Counterexamples.PositiveCharacteristic.charZero_iff_classification K]
  simp only [homForm_eq, polyExtDeriv_eq, koszul_eq, isGLInvariant_iff]
  exact ⟨fun h n r k W hW hle => h n W hW r k hle, fun h n W hW r k hle => h n r k W hW hle⟩

variable (K) in
theorem charZero_iff_closed_eq_exact_of_feec :
    CharZero K ↔ ∀ n r k : ℕ, LinearMap.ker (polyExtDeriv K n) ⊓ homForm K n r (k + 1) =
      (homForm K n (r + 1) k).map (polyExtDeriv K n) := by
  rw [Feec.Counterexamples.PositiveCharacteristic.charZero_iff_closed_eq_exact K]
  simp only [homForm_eq, polyExtDeriv_eq, inf_comm]

end FEEC
