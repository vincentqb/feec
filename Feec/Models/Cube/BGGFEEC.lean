module

public import Feec.Domain.BGGFEEC
public import Feec.Models.Cube.MaximalRegularDecomposition

/-!
# The FEEC theorem for the Hessian, elasticity and div-div complexes on the cube

On `Q = (0, ½)³` the FEEC theorem holds for every stacked conforming family of the discrete
Hessian, elasticity and div-div complexes (`hessianFEEC_Q`, `elasticityFEEC_Q`, `divDivFEEC_Q`).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube

open Feec.Domain
open Feec.Models.Cube.Geometry (isOpen_Q)
open Feec.Models.Cube.Sobolev (deRhamVec_hasRegularDecomposition_Q)

variable {𝕜 : Type*} [RCLike 𝕜]

theorem hessianMaximalData_regularDecomposition_Q :
    (hessianMaximalData 𝕜 (isOpen_Q (d := Fin 3))).RegularDecomposition 0 :=
  hessianMaximalData_regularDecomposition isOpen_Q (deRhamVec_hasRegularDecomposition_Q 1)

theorem elasticityMaximalData_regularDecomposition_Q :
    (elasticityMaximalData 𝕜 (isOpen_Q (d := Fin 3))).RegularDecomposition 1 :=
  elasticityMaximalData_regularDecomposition isOpen_Q
    ((deRhamVec_hasRegularDecomposition_Q 3).mono zero_le_one)

theorem divDivMaximalData_regularDecomposition_Q :
    (divDivMaximalData 𝕜 (isOpen_Q (d := Fin 3))).RegularDecomposition 2 :=
  divDivMaximalData_regularDecomposition isOpen_Q
    ((deRhamVec_hasRegularDecomposition_Q 3).mono zero_le_two)

/-- **The `𝕜ᵐ`-valued de Rham complexes of `Q ⊆ ℝ³` have finite-dimensional cohomology.** -/
instance finiteDimensional_cohomology_deRhamVec_Q (m : ℕ) (i : ℤ) :
    FiniteDimensional 𝕜 (((deRhamVec 𝕜 m).maximalComplex (isOpen_Q (d := Fin 3))).cohomology i) :=
  have := deRhamVec_finiteDimensional_cohomology isOpen_Q m i
  deRhamVec_ofReal (𝕜 := 𝕜) m ▸ (deRhamVec ℝ m).finiteDimensional_cohomology_ofReal isOpen_Q i

variable {κ : Type*}

/-- **The FEEC theorem for discrete Hessian complexes on the cube** `Q = (0, ½)³`, for every
stacked conforming family of the rows linked by `I`, `2 vskw`, `tr` ([ArnoldHu2021], §4.1). -/
theorem hessianFEEC_Q (G : (hessianMaximalData 𝕜 (isOpen_Q (d := Fin 3))).StackedFamily κ) :
    G.Verdict (0 < ·) (· < 0) :=
  hessianFEEC isOpen_Q hessianMaximalData_regularDecomposition_Q G

/-- **The FEEC theorem for discrete elasticity complexes on the cube** `Q = (0, ½)³` (`bgg 1` of
two `𝕜³`-valued de Rham complexes linked by `-mskw`, `T - tr`, `2 vskw`; [ArnoldHu2021], §4.1). -/
theorem elasticityFEEC_Q
    (G : (elasticityMaximalData 𝕜 (isOpen_Q (d := Fin 3))).StackedFamily κ) :
    G.Verdict (1 < ·) (· < 1) :=
  elasticityFEEC isOpen_Q elasticityMaximalData_regularDecomposition_Q G

/-- **The FEEC theorem for discrete div-div complexes on the cube** `Q = (0, ½)³` (`bgg 2` of the
`𝕜³`-valued and scalar de Rham complexes linked by `· I`, `-mskw`, `I`; [ArnoldHu2021], §4.1). -/
theorem divDivFEEC_Q (G : (divDivMaximalData 𝕜 (isOpen_Q (d := Fin 3))).StackedFamily κ) :
    G.Verdict (2 < ·) (· < 2) :=
  divDivFEEC isOpen_Q divDivMaximalData_regularDecomposition_Q G

end Feec.Models.Cube
