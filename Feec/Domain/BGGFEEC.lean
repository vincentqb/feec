module

public import Feec.Domain.BGGRealization
public import Feec.HilbertComplex.BGG.Conforming

/-!
# The FEEC theorem for the Hessian, elasticity and div-div complexes

The Hessian, elasticity and div-div complexes are the BGG complexes `bgg J` (`J = 0, 1, 2`) of
stacked `L²` de Rham complexes on an open `Ω ⊆ ℝ³` linked by constant matrices
(`Feec.Domain.hessianMaximalData`, `elasticityMaximalData`, `divDivMaximalData`). For discrete BGG
data of them, stacked conforming families of the two de Rham complexes with `S Ṽₕ ⊆ Vₕ` and
`πₕ S = S π̃ₕ` (`Feec.BGG.HilbertData.StackedFamily`), the FEEC theorem for discrete BGG complexes
(`Feec.BGG.HilbertData.StackedFamily.bggVerdict`) applies: the matrices up to `J` have left inverses
(`hessianSMat_leftInv`, …), so **wherever the two de Rham complexes have finite-dimensional
cohomology and the regular decompositions after `J` hold, the discrete Hessian, elasticity and
div-div complexes satisfy the FEEC theorem** (`hessianFEEC`, `elasticityFEEC`, `divDivFEEC`; for
general constant-coefficient diagrams, `ConstCoeffBGG.maximalData_feecVerdict`). The regular
decompositions of the maximal realizations (`Feec.BGG.HilbertData.RegularDecomposition`) are
hypotheses here: they follow from the `H¹`-regular decompositions of the rows
(`hessianMaximalData_regularDecomposition`, …, in `Feec.Domain.RegularDecomposition`) and are a
theorem on the cube `Q = (0, ½)³` over `ℝ`, where the FEEC theorems hold without them
(`Feec.Models.Cube.hessianFEEC_Q`, `Feec.Models.Cube.elasticityFEEC_Q`,
`Feec.Models.Cube.divDivFEEC_Q`). The finite-dimensional cohomology of `deRhamVec m` is a
hypothesis here too; over `ℝ` it follows from that of the forms `deRham ℝ 3` on every open
`Ω ⊆ ℝ³` (`Feec.Domain.deRhamVec_finiteDimensional_cohomology`) and is a theorem on `Q`
(`Feec.Models.Cube.finiteDimensional_cohomology_deRhamVec_Q`), so the FEEC theorems on `Q` have
no hypothesis. **No stacked family of the maximal data is known to exist here**: the theorems
quantify over `G`, and no finite element family with `S Ṽₕ ⊆ Vₕ`, `πₕ S = S π̃ₕ` is constructed.
The conditions are strong: the connecting maps `I`, `2 vskw`, `tr` of the Hessian data are onto,
so they force `Vₕ¹ = Ṽₕ⁰`, `πₕ¹ = π̃ₕ⁰`, `Vₕ² = 2 vskw Ṽₕ¹`, `Vₕ³ = tr Ṽₕ²`, and `π̃ₕ¹` must
preserve the symmetric matrix fields `ker (2 vskw)` (as for the tensor-product splines of
[BonizzoniHuKanschatSap2024], not formalized). The non-vacuity witnesses
of the abstract theorem are the full families of finite-dimensional data
(`Feec.BGG.BoundedData.idShift_toHilbertData_bggVerdict`). The verdicts concern the derived complex
of the domain complexes in the graph norms, not the hand-built `L²` complexes
`Feec.Domain.HessianComplex`, `Feec.Domain.Elasticity`, `Feec.Domain.DivDivComplex`.

## Main results

* `ConstCoeffBGG.maximalData_feecVerdict`.
* **`hessianFEEC`**, **`elasticityFEEC`**, **`divDivFEEC`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §4.1 ((32), the Hessian,
  elasticity and div-div complexes), Theorem 6
* [F. Bonizzoni, K. Hu, G. Kanschat, D. Sap, *Discrete tensor product BGG sequences: splines and finite elements*][BonizzoniHuKanschatSap2024]
  (discrete BGG diagrams)
* [D. Pauly, W. Zulehner, *The divDiv-complex and applications to biharmonic equations*][PaulyZulehner2020]
  (the Hessian and div-div complexes)

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]
  [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {Ω : Set E} {κ : Type*}

namespace ConstCoeffBGG

variable (B : ConstCoeffBGG E 𝕜) (M : ∀ k, Matrix (B.top.ι (k + 1)) (B.bot.ι k) 𝕜)
  (hM : ∀ k f, (B.S k).apply f = (ConstCoeffOp.ofMatrix (M k)).apply f)

/-- **The FEEC theorem for discrete BGG complexes of the maximal realizations**: if the matrices
`M k`, `k ≤ J`, have left inverses, the regular decompositions hold after `J` and the maximal
complexes of the two rows have finite-dimensional cohomology, then for every stacked conforming
family of the two rows (`S Ṽₕ ⊆ Vₕ`, `πₕ S = S π̃ₕ`) the FEEC theorem holds for the discrete BGG
complexes `bgg J` (`BGG.HilbertData.StackedFamily.bggVerdict`). -/
theorem maximalData_feecVerdict [∀ k, DecidableEq (B.bot.ι k)] (hΩ : IsOpen Ω) {J : ℤ}
    (hN : ∀ k ≤ J, ∃ N : Matrix (B.bot.ι k) (B.top.ι (k + 1)) 𝕜, N * M k = 1)
    (htop : (B.maximalData M hM hΩ).RegularDecomposition J)
    [∀ i, FiniteDimensional 𝕜 ((B.top.maximalComplex hΩ).cohomology i)]
    [∀ i, FiniteDimensional 𝕜 ((B.bot.maximalComplex hΩ).cohomology i)]
    (G : (B.maximalData M hM hΩ).StackedFamily κ) : G.Verdict (J < ·) (· < J) :=
  have : ∀ i, FiniteDimensional 𝕜 ((B.maximalData M hM hΩ).H.cohomology i) := fun i =>
    ‹∀ i, FiniteDimensional 𝕜 ((B.top.maximalComplex hΩ).cohomology i)› i
  have : ∀ i, FiniteDimensional 𝕜 ((B.maximalData M hM hΩ).Ht.cohomology i) := fun i =>
    ‹∀ i, FiniteDimensional 𝕜 ((B.bot.maximalComplex hΩ).cohomology i)› i
  G.bggVerdict (fun k hk => by
    obtain ⟨N, hN⟩ := hN k hk
    rw [maximalData_S]
    exact ⟨_, L2F.antilipschitz_ofMatrixCLM hN⟩) htop

end ConstCoeffBGG

/-! ### The Hessian, elasticity and div-div complexes on an open `Ω ⊆ ℝ³` -/

section Instances

variable {Ω : Set (Fin 3 → ℝ)} {κ : Type*}

/-- **The FEEC theorem for discrete Hessian complexes** on an open `Ω ⊆ ℝ³`: for every stacked
conforming family of the scalar and `𝕜³`-valued `L²` de Rham complexes of `Ω` linked by `I`,
`2 vskw`, `tr`, the FEEC theorem holds for the discrete Hessian complexes `bgg 0`, wherever the
two de Rham complexes have finite-dimensional cohomology and the regular decompositions after `0`
hold. -/
theorem hessianFEEC (hΩ : IsOpen Ω) (htop : (hessianMaximalData 𝕜 hΩ).RegularDecomposition 0)
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)]
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    (G : (hessianMaximalData 𝕜 hΩ).StackedFamily κ) : G.Verdict (0 < ·) (· < 0) :=
  (hessianBGG 𝕜).maximalData_feecVerdict hessianSMat hessianS_apply_eq hΩ hessianSMat_leftInv
    htop G

/-- **The FEEC theorem for discrete elasticity complexes** on an open `Ω ⊆ ℝ³` (`bgg 1` of two
`𝕜³`-valued de Rham complexes linked by `-mskw`, `T - tr`, `2 vskw`), under the regular
decompositions after `1`. -/
theorem elasticityFEEC (hΩ : IsOpen Ω)
    (htop : (elasticityMaximalData 𝕜 hΩ).RegularDecomposition 1)
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    (G : (elasticityMaximalData 𝕜 hΩ).StackedFamily κ) : G.Verdict (1 < ·) (· < 1) :=
  (elasticityBGG 𝕜).maximalData_feecVerdict elasticitySMat elasticityS_apply_eq hΩ
    elasticitySMat_leftInv htop G

/-- **The FEEC theorem for discrete div-div complexes** on an open `Ω ⊆ ℝ³` (`bgg 2` of the
`𝕜³`-valued and scalar de Rham complexes linked by `· I`, `-mskw`, `I`), under the regular
decompositions after `2`. -/
theorem divDivFEEC (hΩ : IsOpen Ω) (htop : (divDivMaximalData 𝕜 hΩ).RegularDecomposition 2)
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)]
    (G : (divDivMaximalData 𝕜 hΩ).StackedFamily κ) : G.Verdict (2 < ·) (· < 2) :=
  (divDivBGG 𝕜).maximalData_feecVerdict divDivSMat divDivS_apply_eq hΩ divDivSMat_leftInv htop G

end Instances

end Feec.Domain
