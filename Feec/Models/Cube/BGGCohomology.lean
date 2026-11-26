module

public import Feec.FiniteElement.FormBGGCohomology
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Cube.MaximalRegularDecomposition

/-!
# The Hessian, elasticity and div–div complexes of forms on the cube: closed range and cohomology

On `Q = (0, ½)ⁿ` (`n = 3` for elasticity) the Hessian, elasticity and div–div complexes of forms
have closed range and cohomology concentrated in degree `0`: affine functions, rigid motions and
fields `a + b x`.

## Main results

* `hessianBGG_Q`, `elasticityBGG_Q`, `divDivBGG_Q`: closed range and the dimensions.
* `hessianBGG_Q_homology_zero`, `elasticityBGG_Q_homology_zero`, `divDivBGG_Q_homology_zero`: `H⁰`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.FormBGG

open MeasureTheory
open Feec.Domain Feec.FiniteElement Feec.HilbertComplex
open Feec.Models.Cube.FEM (cubeDomain isOpen_cubeDomain isBounded_cubeDomain cubeDomain_eq_Q)

variable {n : ℕ}

theorem deRham_hasRegularDecomposition_cube :
    (deRham ℝ n).HasRegularDecomposition (cubeDomain n) 0 :=
  (cubeDomain_eq_Q n) ▸ Sobolev.deRham_hasRegularDecomposition_Q

instance finiteDimensional_formRow_cohomology (k : ℤ) :
    FiniteDimensional ℝ ((formRow n (isOpen_cubeDomain n)).cohomology k) :=
  ((FEM.complex n).cohomologyEquivHarmonic (FEM.closedRangeAt k)).symm.finiteDimensional

theorem finrank_formRow_cohomology (k : ℤ) :
    Module.finrank ℝ ((formRow n (isOpen_cubeDomain n)).cohomology k) = if k = 0 then 1 else 0 :=
  FEM.finrank_cohomology k

/-- **The Hessian complex of forms on `Q = (0, ½)ⁿ`** has closed range and cohomology of dimension
`n + 1` in degree `0` and `0` elsewhere ([ArnoldHu2021], §4.2, Theorem 6). -/
theorem hessianBGG_Q (i : ℤ) :
    (hessianFormData (isOpen_cubeDomain n)).BGGVerdict 0 i ∧
      Module.finrank ℝ (((hessianFormData (isOpen_cubeDomain n)).domainData.bgg 0).homology i) =
        if i = 0 then n + 1 else 0 :=
  hessianFormData_bggVerdict _ deRham_hasRegularDecomposition_cube finrank_formRow_cohomology i

/-- **The elasticity complex of forms on `Q = (0, ½)³`** has closed range and cohomology of
dimension `6` in degree `0` and `0` elsewhere ([ArnoldHu2021], §4.1, Theorem 6). -/
theorem elasticityBGG_Q (i : ℤ) :
    (elasticityFormData (isOpen_cubeDomain 3)).BGGVerdict 1 i ∧
      Module.finrank ℝ (((elasticityFormData (isOpen_cubeDomain 3)).domainData.bgg 1).homology i) =
        if i = 0 then 6 else 0 :=
  elasticityFormData_bggVerdict _ (deRham_hasRegularDecomposition_cube.mono zero_le_one)
    finrank_formRow_cohomology i

/-- **The div–div complex of forms on `Q = (0, ½)ⁿ`**, `n ≥ 1`, has closed range and cohomology of
dimension `n + 1` in degree `0` and `0` elsewhere ([ArnoldHu2021], §4.2, Theorem 6). -/
theorem divDivBGG_Q [NeZero n] (i : ℤ) :
    (divDivFormData (isOpen_cubeDomain n)).BGGVerdict ((n : ℤ) - 1) i ∧
      Module.finrank ℝ
        (((divDivFormData (isOpen_cubeDomain n)).domainData.bgg ((n : ℤ) - 1)).homology i) =
          if i = 0 then n + 1 else 0 :=
  have hn := NeZero.pos n
  divDivFormData_bggVerdict _ ((deRham_hasRegularDecomposition_cube (n := n)).mono (by omega))
    finrank_formRow_cohomology i

theorem finrank_formRow_cohomology_zero :
    Module.finrank ℝ ((formRow n (isOpen_cubeDomain n)).cohomology 0) = 1 := by
  simp [finrank_formRow_cohomology]

/-- **`H⁰` of the Hessian complex on `Q` is the space of affine functions**, by `[(σ, φ)] ↦ ι σ`. -/
theorem hessianBGG_Q_homology_zero :
    (hessianFormData (isOpen_cubeDomain n)).HomologyIs 0 0
      {u | ∃ (a : ℝ) (b : Fin n → ℝ),
        ∀ s, ⇑(u s) =ᵐ[volume.restrict (cubeDomain n)] fun x => a + b ⬝ᵥ x} :=
  hessianFormData_homologyIs_zero _ (isBounded_cubeDomain n) finrank_formRow_cohomology_zero

open scoped Matrix in
/-- **`H⁰` of the elasticity complex on `Q` is the space of rigid motions**, by `[(σ, φ)] ↦ ι σ`. -/
theorem elasticityBGG_Q_homology_zero :
    (elasticityFormData (isOpen_cubeDomain 3)).HomologyIs 1 0
      {u | ∃ a b : Fin 3 → ℝ,
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cubeDomain 3)] fun x => a c + (b ⨯₃ x) c} :=
  elasticityFormData_homologyIs_zero _ (isBounded_cubeDomain 3) finrank_formRow_cohomology_zero

/-- **`H⁰` of the div–div complex on `Q` is the space of fields `a + b x`**, by `[(σ, φ)] ↦ ι σ`. -/
theorem divDivBGG_Q_homology_zero [NeZero n] :
    (divDivFormData (isOpen_cubeDomain n)).HomologyIs ((n : ℤ) - 1) 0
      {u | ∃ (a : Fin n → ℝ) (b : ℝ),
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cubeDomain n)] fun x => a c + b * x c} :=
  divDivFormData_homologyIs_zero _ (isBounded_cubeDomain n) finrank_formRow_cohomology_zero

end Feec.Models.Cube.FormBGG
