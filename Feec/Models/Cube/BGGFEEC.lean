module

public import Feec.Domain.BGGFEEC
public import Feec.Models.Cube.MaximalRegularDecomposition

/-!
# The FEEC theorem for the Hessian, elasticity and div-div complexes on the cube

On the cube `Q = (0, ½)³` the two hypotheses of the FEEC theorems for discrete Hessian,
elasticity and div-div complexes (`Feec.Domain.hessianFEEC`, `elasticityFEEC`, `divDivFEEC`) are
theorems, over every `RCLike 𝕜` (`ℝ`, `ℂ`):

* **the regular decompositions** of the maximal realizations
  (`Feec.BGG.HilbertData.RegularDecomposition`; `hessianMaximalData_regularDecomposition_Q`, …):
  the rows are de Rham complexes with values in `ℝᵐ`, which have the `H¹`-regular decompositions
  `H(curl) = grad H¹ + H¹`, `H(div) = curl H(curl) + H¹`, `L² = div H(div) + H¹` on `Q`
  (`Feec.Models.Cube.Sobolev.deRhamVec_hasRegularDecomposition_Q`, Gaffney's identity in the
  absolute parity class), and the connecting matrices from `J` on have right inverses
  (`Feec.Domain.hessianMaximalData_regularDecomposition`);
* **the finite-dimensional cohomology of the rows** (`finiteDimensional_cohomology_deRhamVec_Q`):
  `HΛ(Q)` has closed range and the harmonic forms `ℌᵏ = 0` for `k ≠ 0`, `ℌ⁰ = ℝ · 1`
  (`Feec.Models.Cube.DeRhamIdent.Hmax_finiteDimensional_cohomology`), and the cohomology passes
  to the `ℝᵐ`-valued complexes row by row through the vector proxies
  (`Feec.Domain.deRhamVec_finiteDimensional_cohomology`).

Both pass from `ℝ` to `𝕜`: the rows have real coefficients, so a `𝕜`-valued field lies in a
maximal domain iff its real and imaginary parts do
(`Feec.Domain.ConstCoeffComplex.HasRegularDecomposition.ofReal`,
`Feec.Domain.ConstCoeffComplex.finiteDimensional_cohomology_ofReal`).

So **the FEEC theorem holds for every stacked conforming family of the discrete Hessian,
elasticity and div-div complexes on `Q`**, with no hypothesis (`hessianFEEC_Q`, `elasticityFEEC_Q`,
`divDivFEEC_Q`). As in `Feec.Domain.BGGFEEC`, no stacked conforming family of these diagrams is
constructed.

## Main results

* `hessianMaximalData_regularDecomposition_Q`, `elasticityMaximalData_regularDecomposition_Q`,
  `divDivMaximalData_regularDecomposition_Q`; `finiteDimensional_cohomology_deRhamVec_Q`.
* **`hessianFEEC_Q`**, **`elasticityFEEC_Q`**, **`divDivFEEC_Q`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2 (Theorem 3), §4.1 ((32)),
  Theorem 6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (closed range, harmonic forms and cohomology)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube

open Feec.Domain
open Feec.Models.Cube.Geometry (isOpen_Q)
open Feec.Models.Cube.Sobolev (deRhamVec_hasRegularDecomposition_Q)

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The regular decompositions of the Hessian diagram on `Q`** ([ArnoldHu2021], §2, Theorem 3
for the rows). -/
theorem hessianMaximalData_regularDecomposition_Q :
    (hessianMaximalData 𝕜 (isOpen_Q (d := Fin 3))).RegularDecomposition 0 :=
  hessianMaximalData_regularDecomposition isOpen_Q (deRhamVec_hasRegularDecomposition_Q 1)

/-- **The regular decompositions of the elasticity diagram on `Q`** ([ArnoldHu2021], §2,
Theorem 3 for the rows). -/
theorem elasticityMaximalData_regularDecomposition_Q :
    (elasticityMaximalData 𝕜 (isOpen_Q (d := Fin 3))).RegularDecomposition 1 :=
  elasticityMaximalData_regularDecomposition isOpen_Q
    ((deRhamVec_hasRegularDecomposition_Q 3).mono zero_le_one)

/-- **The regular decompositions of the div-div diagram on `Q`** ([ArnoldHu2021], §2, Theorem 3
for the rows). -/
theorem divDivMaximalData_regularDecomposition_Q :
    (divDivMaximalData 𝕜 (isOpen_Q (d := Fin 3))).RegularDecomposition 2 :=
  divDivMaximalData_regularDecomposition isOpen_Q
    ((deRhamVec_hasRegularDecomposition_Q 3).mono zero_le_two)

/-- **The de Rham complexes of `Q ⊆ ℝ³` with values in `𝕜ᵐ` have finite-dimensional
cohomology** in every degree (from `HΛ(Q)`, row by row through the vector proxies, and from `ℝ`
to `𝕜` through the real and imaginary parts). -/
instance finiteDimensional_cohomology_deRhamVec_Q (m : ℕ) (i : ℤ) :
    FiniteDimensional 𝕜 (((deRhamVec 𝕜 m).maximalComplex (isOpen_Q (d := Fin 3))).cohomology i) :=
  have := deRhamVec_finiteDimensional_cohomology isOpen_Q m i
  deRhamVec_ofReal (𝕜 := 𝕜) m ▸ (deRhamVec ℝ m).finiteDimensional_cohomology_ofReal isOpen_Q i

variable {κ : Type*}

/-- **The FEEC theorem for discrete Hessian complexes on the cube** `Q = (0, ½)³`: for every
stacked conforming family of the scalar and `𝕜³`-valued `L²` de Rham complexes of `Q` linked by
`I`, `2 vskw`, `tr`, the FEEC theorem holds for the discrete Hessian complexes `bgg 0`
(`Feec.Domain.hessianFEEC` with the regular decompositions
`hessianMaximalData_regularDecomposition_Q` and the finite-dimensional cohomology
`finiteDimensional_cohomology_deRhamVec_Q`; the complexes of [ArnoldHu2021], §4.1). -/
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
