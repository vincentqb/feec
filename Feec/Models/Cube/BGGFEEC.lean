module

public import Feec.Domain.BGGFEEC
public import Feec.Models.Cube.MaximalRegularDecomposition

/-!
# The FEEC theorem for the Hessian, elasticity and div-div complexes on the cube

On the cube `Q = (0, ½)³` the regular decompositions of the maximal realizations of the Hessian,
elasticity and div-div diagrams (`Feec.BGG.HilbertData.RegularDecomposition`, the hypothesis of
`Feec.Domain.hessianFEEC`, `elasticityFEEC`, `divDivFEEC`) hold
(`hessianMaximalData_regularDecomposition_Q`, …): the rows are de Rham complexes with values in
`ℝᵐ`, which have the `H¹`-regular decompositions `H(curl) = grad H¹ + H¹`,
`H(div) = curl H(curl) + H¹`, `L² = div H(div) + H¹` on `Q`
(`Feec.Models.Cube.Sobolev.deRhamVec_hasRegularDecomposition_Q`, Gaffney's identity in the
absolute parity class), and the connecting matrices from `J` on have right inverses
(`Feec.Domain.hessianMaximalData_regularDecomposition`). So **the FEEC theorem for discrete
Hessian, elasticity and div-div complexes on `Q` holds wherever the two de Rham complexes have
finite-dimensional cohomology** (`hessianFEEC_Q`, `elasticityFEEC_Q`, `divDivFEEC_Q`), over `ℝ`.
The finite-dimensionality of the cohomology of `deRhamVec ℝ m` on `Q` remains a hypothesis: it
is not transported from the harmonic forms of `HΛ(Q)`
(`Feec.Models.Cube.DeRhamIdent.Hmax_harmonic_eq_bot`, `Hmax_harmonic_zero`) through the
proxies. As in `Feec.Domain.BGGFEEC`, no stacked conforming
family of these diagrams is constructed.

## Main results

* `hessianMaximalData_regularDecomposition_Q`, `elasticityMaximalData_regularDecomposition_Q`,
  `divDivMaximalData_regularDecomposition_Q`.
* **`hessianFEEC_Q`**, **`elasticityFEEC_Q`**, **`divDivFEEC_Q`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2 (Theorem 3), §4.1 ((32)),
  Theorem 6

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube

open Feec.Domain
open Feec.Models.Cube.Geometry (isOpen_Q)
open Feec.Models.Cube.Sobolev (deRhamVec_hasRegularDecomposition_Q)

/-- **The regular decompositions of the Hessian diagram on `Q`**. -/
theorem hessianMaximalData_regularDecomposition_Q :
    (hessianMaximalData ℝ (isOpen_Q (d := Fin 3))).RegularDecomposition 0 :=
  hessianMaximalData_regularDecomposition isOpen_Q (deRhamVec_hasRegularDecomposition_Q 1)

/-- **The regular decompositions of the elasticity diagram on `Q`**. -/
theorem elasticityMaximalData_regularDecomposition_Q :
    (elasticityMaximalData ℝ (isOpen_Q (d := Fin 3))).RegularDecomposition 1 :=
  elasticityMaximalData_regularDecomposition isOpen_Q
    ((deRhamVec_hasRegularDecomposition_Q 3).mono zero_le_one)

/-- **The regular decompositions of the div-div diagram on `Q`**. -/
theorem divDivMaximalData_regularDecomposition_Q :
    (divDivMaximalData ℝ (isOpen_Q (d := Fin 3))).RegularDecomposition 2 :=
  divDivMaximalData_regularDecomposition isOpen_Q
    ((deRhamVec_hasRegularDecomposition_Q 3).mono zero_le_two)

variable {κ : Type*}

/-- **The FEEC theorem for discrete Hessian complexes on the cube** `Q = (0, ½)³`: for every
stacked conforming family of the scalar and `ℝ³`-valued `L²` de Rham complexes of `Q` linked by
`I`, `2 vskw`, `tr`, the FEEC theorem holds for the discrete Hessian complexes `bgg 0` wherever
the two de Rham complexes have finite-dimensional cohomology (`Feec.Domain.hessianFEEC` with the
regular decompositions `hessianMaximalData_regularDecomposition_Q`). -/
theorem hessianFEEC_Q
    [∀ i, FiniteDimensional ℝ
      (((deRhamVec ℝ 1).maximalComplex (isOpen_Q (d := Fin 3))).cohomology i)]
    [∀ i, FiniteDimensional ℝ
      (((deRhamVec ℝ 3).maximalComplex (isOpen_Q (d := Fin 3))).cohomology i)]
    (G : (hessianMaximalData ℝ (isOpen_Q (d := Fin 3))).StackedFamily κ) :
    G.Verdict (0 < ·) (· < 0) :=
  hessianFEEC isOpen_Q hessianMaximalData_regularDecomposition_Q G

/-- **The FEEC theorem for discrete elasticity complexes on the cube** `Q = (0, ½)³` (`bgg 1` of
two `ℝ³`-valued de Rham complexes linked by `-mskw`, `T - tr`, `2 vskw`), wherever the
`ℝ³`-valued de Rham complex has finite-dimensional cohomology. -/
theorem elasticityFEEC_Q
    [∀ i, FiniteDimensional ℝ
      (((deRhamVec ℝ 3).maximalComplex (isOpen_Q (d := Fin 3))).cohomology i)]
    (G : (elasticityMaximalData ℝ (isOpen_Q (d := Fin 3))).StackedFamily κ) :
    G.Verdict (1 < ·) (· < 1) :=
  elasticityFEEC isOpen_Q elasticityMaximalData_regularDecomposition_Q G

/-- **The FEEC theorem for discrete div-div complexes on the cube** `Q = (0, ½)³` (`bgg 2` of the
`ℝ³`-valued and scalar de Rham complexes linked by `· I`, `-mskw`, `I`), wherever the two de Rham
complexes have finite-dimensional cohomology. -/
theorem divDivFEEC_Q
    [∀ i, FiniteDimensional ℝ
      (((deRhamVec ℝ 3).maximalComplex (isOpen_Q (d := Fin 3))).cohomology i)]
    [∀ i, FiniteDimensional ℝ
      (((deRhamVec ℝ 1).maximalComplex (isOpen_Q (d := Fin 3))).cohomology i)]
    (G : (divDivMaximalData ℝ (isOpen_Q (d := Fin 3))).StackedFamily κ) :
    G.Verdict (2 < ·) (· < 2) :=
  divDivFEEC isOpen_Q divDivMaximalData_regularDecomposition_Q G

end Feec.Models.Cube
