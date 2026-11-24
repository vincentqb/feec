module

public import Feec.FiniteElement.FormBGGCohomology
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Cube.MaximalRegularDecomposition

/-!
# The Hessian, elasticity and div–div complexes of forms on the cube: closed range and cohomology

On the cube `Q = (0, ½)ⁿ` (`Feec.Models.Cube.FEM.cubeDomain n`) the two hypotheses of
`Feec.FiniteElement.FormBGGCohomology` hold:

* **the regular decompositions**: `HΛ(Q)` has the `H¹`-regular decompositions from `0` on
  (`deRham_hasRegularDecomposition_cube`, from
  `Feec.Models.Cube.Sobolev.deRham_hasRegularDecomposition_Q`, Gaffney's identity on the torus);
* **the cohomology of a point**: `dim Hᵏ(HΛ(Q)) = [k = 0]`
  (`finrank_formRow_cohomology`, from `Feec.Models.Cube.FEM.finrank_cohomology`).

So **the Hessian, elasticity and div–div complexes of `Q` have closed range in every degree and
finite-dimensional cohomology, concentrated in degree `0`**: `dim H⁰ = n + 1` for the Hessian and
div–div complexes (the dimension of the affine functions, resp. of the fields `a + b x`), `6` for
the elasticity complex on `Q ⊆ ℝ³` (the dimension of the rigid motions), `Hⁱ = 0` for `i ≠ 0`
(`hessianBGG_Q`, `elasticityBGG_Q`, `divDivBGG_Q`), and **`H⁰` is identified**:
`[(σ, φ)] ↦ ι σ` (`ι` the inclusion of the domain of `d` in `L²`) is a linear isomorphism of `H⁰`
onto the affine functions `a + b ⬝ᵥ x`, the rigid motions `a + b ⨯₃ x` of `Q ⊆ ℝ³` and the fields
`a + b x` (`hessianBGG_Q_homology_zero`, `elasticityBGG_Q_homology_zero`,
`divDivBGG_Q_homology_zero`).

## Main results

* `deRham_hasRegularDecomposition_cube`, `finrank_formRow_cohomology`.
* **`hessianBGG_Q`**, **`elasticityBGG_Q`**, **`divDivBGG_Q`**.
* **`hessianBGG_Q_homology_zero`**, **`elasticityBGG_Q_homology_zero`**,
  **`divDivBGG_Q_homology_zero`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2 (Theorem 3), §4.1–4.2,
  Theorem 6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (closed range, harmonic forms and cohomology)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.FormBGG

open MeasureTheory
open Feec.Domain Feec.FiniteElement Feec.HilbertComplex
open Feec.Models.Cube.FEM (cubeDomain isOpen_cubeDomain isBounded_cubeDomain cubeDomain_eq_Q)

variable {n : ℕ}

/-- **The `H¹`-regular decompositions of `HΛ(Q)`** from `0` on, on `cubeDomain n`. -/
theorem deRham_hasRegularDecomposition_cube :
    (deRham ℝ n).HasRegularDecomposition (cubeDomain n) 0 :=
  (cubeDomain_eq_Q n) ▸ Sobolev.deRham_hasRegularDecomposition_Q

instance finiteDimensional_formRow_cohomology (k : ℤ) :
    FiniteDimensional ℝ ((formRow n (isOpen_cubeDomain n)).cohomology k) :=
  ((FEM.complex n).cohomologyEquivHarmonic (FEM.closedRangeAt k)).symm.finiteDimensional

/-- `dim Hᵏ(HΛ(Q)) = [k = 0]`. -/
theorem finrank_formRow_cohomology (k : ℤ) :
    Module.finrank ℝ ((formRow n (isOpen_cubeDomain n)).cohomology k) = if k = 0 then 1 else 0 :=
  FEM.finrank_cohomology k

/-- **The Hessian complex of forms on the cube** `Q = (0, ½)ⁿ` ([ArnoldHu2021], §4.2,
Theorem 6): the BGG complex `bgg 0` of the domain complexes of `HΛ(Q)` over `HΛ(Q) ⊗ ℝⁿ` has
closed range and finite-dimensional cohomology (`Feec.BGG.HilbertData.BGGVerdict`), of dimension
`n + 1` in degree `0` and `0` in the other degrees. -/
theorem hessianBGG_Q (i : ℤ) :
    (hessianFormData (isOpen_cubeDomain n)).BGGVerdict 0 i ∧
      Module.finrank ℝ (((hessianFormData (isOpen_cubeDomain n)).domainData.bgg 0).homology i) =
        if i = 0 then n + 1 else 0 :=
  hessianFormData_bggVerdict _ deRham_hasRegularDecomposition_cube finrank_formRow_cohomology i

/-- **The elasticity complex of forms on the cube** `Q = (0, ½)³` ([ArnoldHu2021], §4.1,
Theorem 6): the BGG complex `bgg 1` of `HΛ(Q) ⊗ ℝ³` over itself has closed range and
finite-dimensional cohomology, of dimension `6` in degree `0` and `0` in the other degrees. -/
theorem elasticityBGG_Q (i : ℤ) :
    (elasticityFormData (isOpen_cubeDomain 3)).BGGVerdict 1 i ∧
      Module.finrank ℝ (((elasticityFormData (isOpen_cubeDomain 3)).domainData.bgg 1).homology i) =
        if i = 0 then 6 else 0 :=
  elasticityFormData_bggVerdict _ (deRham_hasRegularDecomposition_cube.mono zero_le_one)
    finrank_formRow_cohomology i

/-- **The div–div complex of forms on the cube** `Q = (0, ½)ⁿ`, `n ≥ 1` ([ArnoldHu2021], §4.2,
Theorem 6): the BGG complex `bgg (n - 1)` of `HΛ(Q) ⊗ ℝⁿ` over `HΛ(Q)` has closed range and
finite-dimensional cohomology, of dimension `n + 1` in degree `0` and `0` in the other degrees. -/
theorem divDivBGG_Q [NeZero n] (i : ℤ) :
    (divDivFormData (isOpen_cubeDomain n)).BGGVerdict ((n : ℤ) - 1) i ∧
      Module.finrank ℝ
        (((divDivFormData (isOpen_cubeDomain n)).domainData.bgg ((n : ℤ) - 1)).homology i) =
          if i = 0 then n + 1 else 0 :=
  have hn := NeZero.pos n
  divDivFormData_bggVerdict _ ((deRham_hasRegularDecomposition_cube (n := n)).mono (by omega))
    finrank_formRow_cohomology i

/-- `dim H⁰(HΛ(Q)) = 1`: `Q` is connected. -/
theorem finrank_formRow_cohomology_zero :
    Module.finrank ℝ ((formRow n (isOpen_cubeDomain n)).cohomology 0) = 1 := by
  simp [finrank_formRow_cohomology]

/-- **`H⁰` of the Hessian complex of forms on `Q = (0, ½)ⁿ` is the space of affine functions**:
`[(σ, φ)] ↦ ι σ` is a linear isomorphism of `H⁰(bgg 0)` onto `{a + b ⬝ᵥ x}`. -/
theorem hessianBGG_Q_homology_zero :
    (hessianFormData (isOpen_cubeDomain n)).HomologyIs 0 0
      {u | ∃ (a : ℝ) (b : Fin n → ℝ),
        ∀ s, ⇑(u s) =ᵐ[volume.restrict (cubeDomain n)] fun x => a + b ⬝ᵥ x} :=
  hessianFormData_homologyIs_zero _ (isBounded_cubeDomain n) finrank_formRow_cohomology_zero

open scoped Matrix in
/-- **`H⁰` of the elasticity complex of forms on `Q = (0, ½)³` is the space of rigid motions**:
`[(σ, φ)] ↦ ι σ` is a linear isomorphism of `H⁰(bgg 1)` onto `{a + b ⨯₃ x}`. -/
theorem elasticityBGG_Q_homology_zero :
    (elasticityFormData (isOpen_cubeDomain 3)).HomologyIs 1 0
      {u | ∃ a b : Fin 3 → ℝ,
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cubeDomain 3)] fun x => a c + (b ⨯₃ x) c} :=
  elasticityFormData_homologyIs_zero _ (isBounded_cubeDomain 3) finrank_formRow_cohomology_zero

/-- **`H⁰` of the div–div complex of forms on `Q = (0, ½)ⁿ`, `n ≥ 1`, is the space of the fields
`a + b x`**: `[(σ, φ)] ↦ ι σ` is a linear isomorphism of `H⁰(bgg (n - 1))` onto `{a + b x}`. -/
theorem divDivBGG_Q_homology_zero [NeZero n] :
    (divDivFormData (isOpen_cubeDomain n)).HomologyIs ((n : ℤ) - 1) 0
      {u | ∃ (a : Fin n → ℝ) (b : ℝ),
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cubeDomain n)] fun x => a c + b * x c} :=
  divDivFormData_homologyIs_zero _ (isBounded_cubeDomain n) finrank_formRow_cohomology_zero

end Feec.Models.Cube.FormBGG
