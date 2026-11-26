module

public import Feec.FiniteElement.FormBGGCohomology
public import Feec.Models.Parallelepiped.BGGFEEC

/-!
# The Hessian, elasticity and div–div complexes of forms on parallelepipeds

On the parallelepiped `Ω = A · Q + b`, the Hessian, elasticity (`n = 3`) and div–div complexes of
forms have closed range and cohomology of dimension `n + 1`, `6`, resp. `n + 1` in degree `0` and
`0` in the other degrees.

## Main results

* `hessianBGG_domain`, `elasticityBGG_domain`, `divDivBGG_domain`: closed range and cohomology.
* `elasticityBGG_domain_homology_zero`: `H⁰` of the elasticity complex is the rigid motions.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Parallelepiped.FormBGG

open MeasureTheory
open Feec.Domain Feec.FiniteElement
open Feec.Models.Parallelepiped (domain isOpen_domain isBounded_domain preimage_Q_domain
  finrank_cohomology deRham_hasRegularDecomposition_affine
  finiteDimensional_cohomology_deRham_affine)

section Forms

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)
include hA

theorem deRham_hasRegularDecomposition_domain :
    (deRham ℝ n).HasRegularDecomposition (domain A b) 0 :=
  deRham_hasRegularDecomposition_affine (isUnit_det_inv hA) _ (preimage_Q_domain A b)

theorem finiteDimensional_formRow_cohomology_domain (k : ℤ) :
    FiniteDimensional ℝ ((formRow n (isOpen_domain A b)).cohomology k) :=
  finiteDimensional_cohomology_deRham_affine (isUnit_det_inv hA) _ _ (preimage_Q_domain A b) k

/-- The Hessian complex of forms on `Ω = A · Q + b` has closed range, and cohomology of dimension
`n + 1` in degree `0` and `0` elsewhere. [ArnoldHu2021], §4.2, Theorem 6 -/
theorem hessianBGG_domain (i : ℤ) :
    (hessianFormData (isOpen_domain A b)).BGGVerdict 0 i ∧
      Module.finrank ℝ (((hessianFormData (isOpen_domain A b)).domainData.bgg 0).homology i) =
        if i = 0 then n + 1 else 0 :=
  have := finiteDimensional_formRow_cohomology_domain A hA b
  hessianFormData_bggVerdict _ (deRham_hasRegularDecomposition_domain A hA b)
    (finrank_cohomology A hA b) i

/-- The div–div complex of forms on `Ω = A · Q + b ⊆ ℝⁿ`, `n ≥ 1`, has closed range, and cohomology
of dimension `n + 1` in degree `0` and `0` elsewhere. [ArnoldHu2021], §4.2, Theorem 6 -/
theorem divDivBGG_domain [NeZero n] (i : ℤ) :
    (divDivFormData (isOpen_domain A b)).BGGVerdict ((n : ℤ) - 1) i ∧
      Module.finrank ℝ
        (((divDivFormData (isOpen_domain A b)).domainData.bgg ((n : ℤ) - 1)).homology i) =
          if i = 0 then n + 1 else 0 :=
  have := finiteDimensional_formRow_cohomology_domain A hA b
  have hn := NeZero.pos n
  divDivFormData_bggVerdict _ ((deRham_hasRegularDecomposition_domain A hA b).mono (by omega))
    (finrank_cohomology A hA b) i

theorem finrank_formRow_cohomology_zero_domain :
    Module.finrank ℝ ((formRow n (isOpen_domain A b)).cohomology 0) = 1 := by
  simpa using finrank_cohomology A hA b 0

theorem hessianBGG_domain_homology_zero :
    (hessianFormData (isOpen_domain A b)).HomologyIs 0 0
      {u | ∃ (a : ℝ) (c : Fin n → ℝ),
        ∀ s, ⇑(u s) =ᵐ[volume.restrict (domain A b)] fun x => a + c ⬝ᵥ x} :=
  hessianFormData_homologyIs_zero _ (isBounded_domain A hA b)
    (finrank_formRow_cohomology_zero_domain A hA b)

theorem divDivBGG_domain_homology_zero [NeZero n] :
    (divDivFormData (isOpen_domain A b)).HomologyIs ((n : ℤ) - 1) 0
      {u | ∃ (a : Fin n → ℝ) (c : ℝ),
        ∀ i s, ⇑(u i s) =ᵐ[volume.restrict (domain A b)] fun x => a i + c * x i} :=
  divDivFormData_homologyIs_zero _ (isBounded_domain A hA b)
    (finrank_formRow_cohomology_zero_domain A hA b)

end Forms

section Elasticity

/-- The elasticity complex of forms on `Ω = A · Q + b ⊆ ℝ³` has closed range, and cohomology of
dimension `6` in degree `0` and `0` elsewhere. [ArnoldHu2021], §4.1, Theorem 6 -/
theorem elasticityBGG_domain (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsUnit A.det) (b : Fin 3 → ℝ)
    (i : ℤ) :
    (elasticityFormData (isOpen_domain A b)).BGGVerdict 1 i ∧
      Module.finrank ℝ (((elasticityFormData (isOpen_domain A b)).domainData.bgg 1).homology i) =
        if i = 0 then 6 else 0 :=
  have := finiteDimensional_formRow_cohomology_domain A hA b
  elasticityFormData_bggVerdict _ ((deRham_hasRegularDecomposition_domain A hA b).mono zero_le_one)
    (finrank_cohomology A hA b) i

open scoped Matrix in
/-- `H⁰` of the elasticity complex of forms on `Ω` is the space of rigid motions. -/
theorem elasticityBGG_domain_homology_zero (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsUnit A.det)
    (b : Fin 3 → ℝ) :
    (elasticityFormData (isOpen_domain A b)).HomologyIs 1 0
      {u | ∃ a c : Fin 3 → ℝ,
        ∀ i s, ⇑(u i s) =ᵐ[volume.restrict (domain A b)] fun x => a i + (c ⨯₃ x) i} :=
  elasticityFormData_homologyIs_zero _ (isBounded_domain A hA b)
    (finrank_formRow_cohomology_zero_domain A hA b)

end Elasticity

end Feec.Models.Parallelepiped.FormBGG
