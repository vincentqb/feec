module

public import Solution.Affine
public import Solution.Dof

/-!
# Affinely invariant polynomial forms and their degrees of freedom (solution)

The compared theorems of `Challenge.lean`. `FEEC.affineInvariantForms` and the characteristic-`0`
theorems are `Feec.FiniteElement.InvariantForm`, `Feec.FiniteElement.AffineInvariantForm` and
`Feec.Counterexamples.PositiveCharacteristic` through `Solution.Affine`; `FEEC.unisolvent` is
`Feec.FiniteElement.LocalDof` through `Solution.Dof`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4, §4

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

universe u

namespace FEEC

variable {n : ℕ}

theorem unisolvent (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (∀ w ∈ (polyForm ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyFormMinus ℝ m (r + k - m) (m - k)).map evalForm,
        faceMoment T.points e η w = 0) → w = 0) ∧
    (∀ w ∈ (polyFormMinus ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyForm ℝ m (r + k - m - 1) (m - k)).map evalForm,
        faceMoment T.points e η w = 0) → w = 0) ∧
    Module.finrank ℝ (polyForm ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyFormMinus ℝ m (r + k - m) (m - k)) else 0) ∧
    Module.finrank ℝ (polyFormMinus ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyForm ℝ m (r + k - m - 1) (m - k))
        else 0) :=
  unisolvent_of_feec T hr k

theorem affineInvariantForms (K : Type u) [Field K] [CharZero K] (n : ℕ) :
    AffineInvariantForms K n :=
  affineInvariantForms_of_feec K n

theorem charZero_iff_classification (K : Type u) [Field K] :
    CharZero K ↔ ∀ (n r k : ℕ) (W : Submodule K (PolyForm K n)), IsGLInvariant K n W →
      W ≤ homForm K n (r + 1) (k + 1) →
        W = ⊥ ∨ W = (homForm K n (r + 2) k).map (polyExtDeriv K n) ∨
          W = (homForm K n r (k + 2)).map (koszul K n) ∨ W = homForm K n (r + 1) (k + 1) :=
  charZero_iff_classification_of_feec K

theorem charZero_iff_closed_eq_exact (K : Type u) [Field K] :
    CharZero K ↔ ∀ n r k : ℕ, LinearMap.ker (polyExtDeriv K n) ⊓ homForm K n r (k + 1) =
      (homForm K n (r + 1) k).map (polyExtDeriv K n) :=
  charZero_iff_closed_eq_exact_of_feec K

end FEEC
