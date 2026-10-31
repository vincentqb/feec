module

public import Solution.Bridge
public import Feec.FiniteElement.AffineInvariantForm

/-!
# The bridge for the affinely invariant spaces

The pullback `pullback n B b` of the challenge, `(p ∘ φ) ⊗ Λ(Bᵀ)`, is carried by
`Feec.Koszul.formEquiv` to the pullback `Feec.FiniteElement.polyPullback B b` of the coefficient
forms (`formEquiv_pullback`): on the exterior algebra, `Λ(Bᵀ)` acts on the coefficients as the
fibre pullback `Feec.ExteriorFibre.pullback B` (`coeffs_map_dualMap`), both being multiplicative
and agreeing on the covectors. The invariance predicates and the spaces `X(r, s, k)` correspond
(`isAffineInvariant_iff`, `isLinearInvariant_iff`, `map_invariantForm`), and the conclusions are
those of `Feec.FiniteElement.InvariantForm` and `Feec.FiniteElement.AffineInvariantForm`
(`affineInvariantForms_of_feec`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset MvPolynomial Module LinearMap

@[expose] public noncomputable section

namespace FEEC

universe u

variable {K : Type u} [Field K] {n : ℕ}

local notation "Φ" => Feec.Koszul.formEquiv K (Fin n)

open Feec.ExteriorFibre in
/-- `Λ(Bᵀ)` acts on the coefficients as the fibre pullback by `B`. -/
theorem coeffs_map_dualMap (B : Fin n → Fin n → K)
    (x : ExteriorAlgebra K (Module.Dual K (Fin n → K))) :
    coeffs K (Fin n) (ExteriorAlgebra.map (Matrix.toLin' (Matrix.of B)).dualMap x) =
      Feec.ExteriorFibre.pullback B (coeffs K (Fin n) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c =>
    rw [AlgHom.commutes, coeffs_algebraMap, pullback_smul, pullback_single_empty]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, pullback_add]
  | ι_mul x ξ hx =>
    have hξ : coord K (Fin n) ((Matrix.toLin' (Matrix.of B)).dualMap ξ) =
        covPullback B (coord K (Fin n) ξ) := by
      funext l
      rw [coord_apply, LinearMap.dualMap_apply, covPullback]
      rw [show Matrix.toLin' (Matrix.of B) (Pi.single l 1) =
          ∑ i, B i l • (Pi.single i 1 : Fin n → K) by
        funext i
        rw [Matrix.toLin'_apply]
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]]
      simp [map_sum, mul_comm]
    rw [map_mul, ExteriorAlgebra.map_apply_ι, coeffs_ι_mul, coeffs_ι_mul, hx, hξ, pullback_wedge]

/-- **`formEquiv` carries the pullback of the challenge to the pullback of `Feec`.** -/
theorem formEquiv_pullback (B : Fin n → Fin n → K) (b : Fin n → K) (ω : Form K n) :
    Φ (pullback K n (Matrix.of B) b ω) = Feec.FiniteElement.polyPullback B b (Φ ω) := by
  induction ω using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Feec.FiniteElement.polyPullback_add]
  | tmul p x =>
    funext t
    simp only [pullback, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      Feec.Koszul.formEquiv_tmul, coeffs_map_dualMap, Feec.FiniteElement.polyPullback_apply,
      Feec.ExteriorFibre.pullback_apply, Finset.sum_smul]
    refine sum_congr rfl fun s _ => ?_
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, Feec.FiniteElement.polySubst]
    simp only [algHom_C, algebraMap_eq, Matrix.of_apply]
    ring

theorem map_pullback (B : Fin n → Fin n → K) (b : Fin n → K) (V : Submodule K (Form K n)) :
    (V.map (pullback K n (Matrix.of B) b)).map (Φ).toLinearMap =
      (V.map (Φ).toLinearMap).map (Feec.FiniteElement.polyPullbackₗ B b) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun ω => formEquiv_pullback B b ω

theorem isAffineInvariant_iff (V : Submodule K (Form K n)) :
    IsAffineInvariant K n V ↔ Feec.FiniteElement.IsAffineInvariant (V.map (Φ).toLinearMap) := by
  refine ⟨fun h B b ω hω => ?_, fun h B b => ?_⟩
  · have := (map_le_iff (n := n)).2 (h (Matrix.of B) b)
    rw [map_pullback] at this
    exact this ⟨ω, hω, rfl⟩
  · rw [← map_le_iff, ← Matrix.of.apply_symm_apply B, map_pullback]
    rintro _ ⟨ω, hω, rfl⟩
    exact h _ b ω hω

theorem isLinearInvariant_iff (V : Submodule K (Form K n)) :
    IsLinearInvariant K n V ↔ Feec.FiniteElement.IsLinearInvariant (V.map (Φ).toLinearMap) := by
  refine ⟨fun h B ω hω => ?_, fun h B => ?_⟩
  · have := (map_le_iff (n := n)).2 (h (Matrix.of B))
    rw [map_pullback] at this
    exact this ⟨ω, hω, rfl⟩
  · rw [← map_le_iff, ← Matrix.of.apply_symm_apply B, map_pullback]
    rintro _ ⟨ω, hω, rfl⟩
    exact h _ ω hω

theorem isGLInvariant_iff (V : Submodule K (Form K n)) :
    IsGLInvariant K n V ↔ Feec.FiniteElement.IsGLInvariant (V.map (Φ).toLinearMap) := by
  refine ⟨fun h g ω hω => ?_, fun h g => ?_⟩
  · have := (map_le_iff (n := n)).2 (h g)
    rw [← Matrix.of.apply_symm_apply (g : Matrix (Fin n) (Fin n) K), map_pullback] at this
    exact this ⟨ω, hω, rfl⟩
  · rw [← map_le_iff, ← Matrix.of.apply_symm_apply (g : Matrix (Fin n) (Fin n) K), map_pullback]
    rintro _ ⟨ω, hω, rfl⟩
    exact h g ω hω

/-- Invariance under the invertible affine maps is affine invariance (`K` infinite). -/
theorem isAffineInvariant_of_forall_units [Infinite K] {V : Submodule K (Form K n)}
    (hV : ∀ (g : GL (Fin n) K) b, V.map (pullback K n g b) ≤ V) : IsAffineInvariant K n V := by
  rw [isAffineInvariant_iff]
  refine Feec.FiniteElement.isAffineInvariant_of_forall_units fun g b ω hω => ?_
  have := (map_le_iff (n := n)).2 (hV g b)
  rw [← Matrix.of.apply_symm_apply (g : Matrix (Fin n) (Fin n) K), map_pullback] at this
  exact this ⟨ω, hω, rfl⟩

theorem map_invariantForm (r s k : ℕ) :
    (invariantForm K n r s k).map (Φ).toLinearMap =
      (Feec.Koszul.polyForm K (Fin n) (r + 1) (k - 1)).map (Feec.Koszul.extDerivₗ K (Fin n)) ⊔
        (Feec.Koszul.polyForm K (Fin n) s (k + 1)).map (Feec.Koszul.koszulₗ K (Fin n)) := by
  rw [invariantForm, Submodule.map_sup, map_map_extDeriv, map_map_koszul, map_polyForm,
    map_polyForm]

theorem map_map_extDeriv_polyForm (r k : ℕ) :
    ((polyForm K n r k).map (extDeriv K n)).map (Φ).toLinearMap =
      (Feec.Koszul.polyForm K (Fin n) r k).map (Feec.Koszul.extDerivₗ K (Fin n)) := by
  rw [map_map_extDeriv, map_polyForm]

variable (K n) in
theorem affineInvariantForms_of_feec [CharZero K] : AffineInvariantForms K n where
  isLinearInvariant_map_homForm r k := by
    rw [isLinearInvariant_iff, isLinearInvariant_iff, map_map_extDeriv, map_map_koszul, map_homForm]
    exact ⟨Feec.FiniteElement.isLinearInvariant_map_extDeriv_homForm r k,
      Feec.FiniteElement.isLinearInvariant_map_koszul_homForm r k⟩
  eq_of_le_homForm m k W hW hle := by
    have h := ((isGLInvariant_iff W).1 hW).eq_of_le_homForm_succ
      (by rw [← map_homForm]; exact (map_le_iff (n := n)).2 hle)
    rcases h with h | h | h | h
    · left
      exact map_eq_iff.1 (h.trans (Submodule.map_bot _).symm)
    · right; left
      exact map_eq_iff.1 (h.trans (by rw [map_map_extDeriv, map_homForm]))
    · right; right; left
      exact map_eq_iff.1 (h.trans (by rw [map_map_koszul, map_homForm]))
    · right; right; right
      exact map_eq_iff.1 (h.trans (map_homForm _ _).symm)
  isAffineInvariant_map_extDeriv r k := by
    rw [isAffineInvariant_iff, map_map_extDeriv_polyForm]
    exact Feec.FiniteElement.isAffineInvariant_map_extDeriv _ _
  isAffineInvariant_invariantForm r s k hk hs := by
    rw [isAffineInvariant_iff, map_invariantForm]
    exact Feec.FiniteElement.isAffineInvariant_sup hk hs
  invariantForm_eq_polyFormMinus r k hk := by
    rw [← map_eq_iff, map_invariantForm, map_polyFormMinus]
    exact Feec.FiniteElement.sup_eq_polyFormMinus hk
  invariantForm_eq_polyForm r k hk := by
    rw [← map_eq_iff, map_invariantForm, map_polyForm]
    exact Feec.FiniteElement.sup_eq_polyForm hk
  map_extDeriv_polyForm_one k hk := by
    rw [← map_eq_iff, map_map_extDeriv_polyForm, map_polyForm]
    exact Feec.FiniteElement.map_extDeriv_polyForm_one_eq hk
  eq_invariantForm k hk hkn V hfin hV hdeg hne := by
    have : FiniteDimensional K (V.map (Φ).toLinearMap) := Module.Finite.map V _
    have hdeg' : ∀ ω ∈ V.map (Φ).toLinearMap, Feec.ExteriorFibre.IsDeg k ω := by
      intro ω hω
      have := (map_le_iff (n := n)).2 hdeg hω
      rw [map_kForm] at this
      exact this.1
    have hne' : V.map (Φ).toLinearMap ≠ ⊥ := by
      rwa [Ne, ← Submodule.map_bot (Φ).toLinearMap, map_eq_iff]
    obtain ⟨r, h⟩ := ((isAffineInvariant_iff V).1 (isAffineInvariant_of_forall_units hV)).eq_sup
      hdeg' hk hkn hne'
    refine ⟨r, ?_⟩
    rcases h with h | ⟨s, hs, h⟩
    · left
      rwa [← map_map_extDeriv_polyForm, map_eq_iff] at h
    · right
      refine ⟨s, hs, ?_⟩
      rwa [← map_invariantForm, map_eq_iff] at h

end FEEC
