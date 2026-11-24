module

public import Feec.FiniteElement.FormBGGCohomology
public import Feec.Models.Parallelepiped.BGGFEEC

/-!
# The Hessian, elasticity and div–div complexes of forms on parallelepipeds

On the parallelepiped `Ω = A · Q + b` (`Feec.Models.Parallelepiped.domain A b`, `A` invertible,
`Q = (0, ½)ⁿ`; every open box is one) the two hypotheses of `Feec.FiniteElement.FormBGGCohomology`
hold, both transported from the cube along the pullback of forms `T^*`, `T x = A x + b`:

* **the regular decompositions** of `HΛ(Ω)` from `0` on (`deRham_hasRegularDecomposition_domain`,
  from `Feec.Models.Parallelepiped.deRham_hasRegularDecomposition_affine`);
* **the cohomology of a point**, `dim Hᵏ(HΛ(Ω)) = [k = 0]`
  (`Feec.Models.Parallelepiped.finrank_cohomology`).

So **the Hessian, elasticity (`n = 3`) and div–div (`n ≥ 1`) complexes of forms of `Ω` have closed
range in every degree and finite-dimensional cohomology, of dimension `n + 1`, `6`, resp. `n + 1`
in degree `0` and `0` in the other degrees** (`hessianBGG_domain`, `elasticityBGG_domain`,
`divDivBGG_domain`), and `[(σ, φ)] ↦ ι σ` is a linear isomorphism of `H⁰` onto the affine
functions, the rigid motions, resp. the fields `a + b x` of `Ω` (`hessianBGG_domain_homology_zero`,
`elasticityBGG_domain_homology_zero`, `divDivBGG_domain_homology_zero`).

The diagrams themselves are not transported: on every `Ω` they are the diagrams of
`Feec.FiniteElement.FormBGG` and `Feec.FiniteElement.FormBGGElasticity`, linked by the same maps
built from `dxₐ ∧ ·`, and only the hypotheses on the rows are carried from `Q`.

## Main results

* `deRham_hasRegularDecomposition_domain`, `finiteDimensional_formRow_cohomology_domain`.
* **`hessianBGG_domain`**, **`elasticityBGG_domain`**, **`divDivBGG_domain`**.
* **`hessianBGG_domain_homology_zero`**, **`elasticityBGG_domain_homology_zero`**,
  **`divDivBGG_domain_homology_zero`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2 (Theorem 3), §4.1–4.2,
  Theorem 6
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
  (affine-equivalent domains, change of variables)

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

/-- **The `H¹`-regular decompositions of `HΛ(Ω)`** from `0` on, on the parallelepiped
`Ω = A · Q + b`. -/
theorem deRham_hasRegularDecomposition_domain :
    (deRham ℝ n).HasRegularDecomposition (domain A b) 0 :=
  deRham_hasRegularDecomposition_affine (isUnit_det_inv hA) _ (preimage_Q_domain A b)

/-- The cohomology of `HΛ(Ω)` is finite-dimensional in every degree. -/
theorem finiteDimensional_formRow_cohomology_domain (k : ℤ) :
    FiniteDimensional ℝ ((formRow n (isOpen_domain A b)).cohomology k) :=
  finiteDimensional_cohomology_deRham_affine (isUnit_det_inv hA) _ _ (preimage_Q_domain A b) k

/-- **The Hessian complex of forms on the parallelepiped** `Ω = A · Q + b` ([ArnoldHu2021], §4.2,
Theorem 6): the BGG complex `bgg 0` of the domain complexes of `HΛ(Ω)` over `HΛ(Ω) ⊗ ℝⁿ` has
closed range and finite-dimensional cohomology, of dimension `n + 1` in degree `0` and `0` in the
other degrees. -/
theorem hessianBGG_domain (i : ℤ) :
    (hessianFormData (isOpen_domain A b)).BGGVerdict 0 i ∧
      Module.finrank ℝ (((hessianFormData (isOpen_domain A b)).domainData.bgg 0).homology i) =
        if i = 0 then n + 1 else 0 :=
  have := finiteDimensional_formRow_cohomology_domain A hA b
  hessianFormData_bggVerdict _ (deRham_hasRegularDecomposition_domain A hA b)
    (finrank_cohomology A hA b) i

/-- **The div–div complex of forms on the parallelepiped** `Ω = A · Q + b ⊆ ℝⁿ`, `n ≥ 1`
([ArnoldHu2021], §4.2, Theorem 6): the BGG complex `bgg (n - 1)` of `HΛ(Ω) ⊗ ℝⁿ` over `HΛ(Ω)`
has closed range and finite-dimensional cohomology, of dimension `n + 1` in degree `0` and `0` in
the other degrees. -/
theorem divDivBGG_domain [NeZero n] (i : ℤ) :
    (divDivFormData (isOpen_domain A b)).BGGVerdict ((n : ℤ) - 1) i ∧
      Module.finrank ℝ
        (((divDivFormData (isOpen_domain A b)).domainData.bgg ((n : ℤ) - 1)).homology i) =
          if i = 0 then n + 1 else 0 :=
  have := finiteDimensional_formRow_cohomology_domain A hA b
  have hn := NeZero.pos n
  divDivFormData_bggVerdict _ ((deRham_hasRegularDecomposition_domain A hA b).mono (by omega))
    (finrank_cohomology A hA b) i

/-- `dim H⁰(HΛ(Ω)) = 1`: the parallelepiped is connected. -/
theorem finrank_formRow_cohomology_zero_domain :
    Module.finrank ℝ ((formRow n (isOpen_domain A b)).cohomology 0) = 1 := by
  simpa using finrank_cohomology A hA b 0

/-- **`H⁰` of the Hessian complex of forms on the parallelepiped `Ω` is the space of affine
functions**: `[(σ, φ)] ↦ ι σ` is a linear isomorphism of `H⁰(bgg 0)` onto `{a + c ⬝ᵥ x}`. -/
theorem hessianBGG_domain_homology_zero :
    (hessianFormData (isOpen_domain A b)).HomologyIs 0 0
      {u | ∃ (a : ℝ) (c : Fin n → ℝ),
        ∀ s, ⇑(u s) =ᵐ[volume.restrict (domain A b)] fun x => a + c ⬝ᵥ x} :=
  hessianFormData_homologyIs_zero _ (isBounded_domain A hA b)
    (finrank_formRow_cohomology_zero_domain A hA b)

/-- **`H⁰` of the div–div complex of forms on the parallelepiped `Ω ⊆ ℝⁿ`, `n ≥ 1`, is the space
of the fields `a + c x`**: `[(σ, φ)] ↦ ι σ` is a linear isomorphism of `H⁰(bgg (n - 1))` onto
`{a + c x}`. -/
theorem divDivBGG_domain_homology_zero [NeZero n] :
    (divDivFormData (isOpen_domain A b)).HomologyIs ((n : ℤ) - 1) 0
      {u | ∃ (a : Fin n → ℝ) (c : ℝ),
        ∀ i s, ⇑(u i s) =ᵐ[volume.restrict (domain A b)] fun x => a i + c * x i} :=
  divDivFormData_homologyIs_zero _ (isBounded_domain A hA b)
    (finrank_formRow_cohomology_zero_domain A hA b)

end Forms

section Elasticity

/-- **The elasticity complex of forms on the parallelepiped** `Ω = A · Q + b ⊆ ℝ³`
([ArnoldHu2021], §4.1, Theorem 6): the BGG complex `bgg 1` of `HΛ(Ω) ⊗ ℝ³` over itself has
closed range and finite-dimensional cohomology, of dimension `6` in degree `0` and `0` in the
other degrees. -/
theorem elasticityBGG_domain (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsUnit A.det) (b : Fin 3 → ℝ)
    (i : ℤ) :
    (elasticityFormData (isOpen_domain A b)).BGGVerdict 1 i ∧
      Module.finrank ℝ (((elasticityFormData (isOpen_domain A b)).domainData.bgg 1).homology i) =
        if i = 0 then 6 else 0 :=
  have := finiteDimensional_formRow_cohomology_domain A hA b
  elasticityFormData_bggVerdict _ ((deRham_hasRegularDecomposition_domain A hA b).mono zero_le_one)
    (finrank_cohomology A hA b) i

open scoped Matrix in
/-- **`H⁰` of the elasticity complex of forms on the parallelepiped `Ω ⊆ ℝ³` is the space of
rigid motions**: `[(σ, φ)] ↦ ι σ` is a linear isomorphism of `H⁰(bgg 1)` onto `{a + c ⨯₃ x}`. -/
theorem elasticityBGG_domain_homology_zero (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsUnit A.det)
    (b : Fin 3 → ℝ) :
    (elasticityFormData (isOpen_domain A b)).HomologyIs 1 0
      {u | ∃ a c : Fin 3 → ℝ,
        ∀ i s, ⇑(u i s) =ᵐ[volume.restrict (domain A b)] fun x => a i + (c ⨯₃ x) i} :=
  elasticityFormData_homologyIs_zero _ (isBounded_domain A hA b)
    (finrank_formRow_cohomology_zero_domain A hA b)

end Elasticity

end Feec.Models.Parallelepiped.FormBGG
