module

public import Feec.FiniteElement.AffineInvariantForm

/-!
# Regression test: the classification of invariant polynomial forms over `ℝ`

`Feec.FiniteElement.InvariantForm` and `Feec.FiniteElement.AffineInvariantForm` were stated over
`ℝ`, with the pullback `polyPullback` of real matrices and invariance under all linear (affine)
maps. They now hold over every field (of characteristic `0` for the classifications), and
`IsGLInvariant.isLinearInvariant`, `isAffineInvariant_of_forall_units` reduce invariance under
`GL(n)` to it. The theorems below state the old real results verbatim and derive them from the
new ones at `K = ℝ`.

This file is part of the `FeecCheck` library, not of `Feec`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4, Theorems 3.5–3.6

Bibliography: [references.bib](../../docs/references.bib)
-/

public section

namespace FeecCheck.InvariantForms

open Feec Feec.FiniteElement
open Koszul (PolyForm homForm polyForm koszulₗ extDerivₗ)

variable {n : ℕ}

/-- The earlier `polyPullback_extDeriv` (proved through the evaluated form fields). -/
theorem polyPullback_extDeriv_old (B : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (ω : PolyForm ℝ (Fin n)) :
    polyPullback B b (Koszul.extDeriv ω) = Koszul.extDeriv (polyPullback B b ω) :=
  polyPullback_extDeriv B b ω

/-- The earlier `IsLinearInvariant.eq_of_le_homForm` over `ℝ`. -/
theorem eq_of_le_homForm_old {W : Submodule ℝ (PolyForm ℝ (Fin n))} (hW : IsLinearInvariant W)
    {m k : ℕ} (hmk : 0 < m + k) (hle : W ≤ homForm ℝ (Fin n) m k) :
    W = ⊥ ∨ W = homForm ℝ (Fin n) m k ⊓ LinearMap.ker (extDerivₗ ℝ (Fin n)) ∨
      W = homForm ℝ (Fin n) m k ⊓ LinearMap.ker (koszulₗ ℝ (Fin n)) ∨
        W = homForm ℝ (Fin n) m k :=
  hW.eq_of_le_homForm hmk hle

/-- The earlier `IsAffineInvariant.eq_sup` ([AFW2006], Theorem 3.6) over `ℝ`. -/
theorem eq_sup_old {V : Submodule ℝ (PolyForm ℝ (Fin n))} (hV : IsAffineInvariant V)
    [FiniteDimensional ℝ V] {k : ℕ} (hdeg : ∀ ω ∈ V, ExteriorFibre.IsDeg k ω) (hk : 0 < k)
    (hkn : k < n) (hne : V ≠ ⊥) :
    ∃ r, V = (polyForm ℝ (Fin n) (r + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ∨
      ∃ s ≤ r, V = (polyForm ℝ (Fin n) (r + 1) (k - 1)).map (extDerivₗ ℝ (Fin n)) ⊔
        (polyForm ℝ (Fin n) s (k + 1)).map (koszulₗ ℝ (Fin n)) :=
  hV.eq_sup hdeg hk hkn hne

end FeecCheck.InvariantForms
