module

public import Feec.Domain.BGGRealization
public import Feec.HilbertComplex.BGG.Conforming

/-!
# The FEEC theorem for the Hessian, elasticity and div-div complexes

Stacked conforming families of BGG data of maximal realizations linked by matrices with left
inverses up to `J` satisfy the FEEC theorem for `bgg J`, given the regular decompositions after
`J` and finite-dimensional cohomology of the rows.

## Main results

* `ConstCoeffBGG.maximalData_feecVerdict`: the general case.
* `hessianFEEC`, `elasticityFEEC`, `divDivFEEC`: the Hessian, elasticity and div-div cases.
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

/-- **The FEEC theorem for discrete BGG complexes of the maximal realizations.** -/
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

/-- **The FEEC theorem for discrete Hessian complexes** `bgg 0` on an open `Ω ⊆ ℝ³`. -/
theorem hessianFEEC (hΩ : IsOpen Ω) (htop : (hessianMaximalData 𝕜 hΩ).RegularDecomposition 0)
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)]
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    (G : (hessianMaximalData 𝕜 hΩ).StackedFamily κ) : G.Verdict (0 < ·) (· < 0) :=
  (hessianBGG 𝕜).maximalData_feecVerdict hessianSMat hessianS_apply_eq hΩ hessianSMat_leftInv
    htop G

/-- **The FEEC theorem for discrete elasticity complexes** `bgg 1` on an open `Ω ⊆ ℝ³`. -/
theorem elasticityFEEC (hΩ : IsOpen Ω)
    (htop : (elasticityMaximalData 𝕜 hΩ).RegularDecomposition 1)
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    (G : (elasticityMaximalData 𝕜 hΩ).StackedFamily κ) : G.Verdict (1 < ·) (· < 1) :=
  (elasticityBGG 𝕜).maximalData_feecVerdict elasticitySMat elasticityS_apply_eq hΩ
    elasticitySMat_leftInv htop G

/-- **The FEEC theorem for discrete div-div complexes** `bgg 2` on an open `Ω ⊆ ℝ³`. -/
theorem divDivFEEC (hΩ : IsOpen Ω) (htop : (divDivMaximalData 𝕜 hΩ).RegularDecomposition 2)
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 3).maximalComplex hΩ).cohomology i)]
    [∀ i, FiniteDimensional 𝕜 (((deRhamVec 𝕜 1).maximalComplex hΩ).cohomology i)]
    (G : (divDivMaximalData 𝕜 hΩ).StackedFamily κ) : G.Verdict (2 < ·) (· < 2) :=
  (divDivBGG 𝕜).maximalData_feecVerdict divDivSMat divDivS_apply_eq hΩ divDivSMat_leftInv htop G

end Instances

end Feec.Domain
