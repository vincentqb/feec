module

public import Solution.CubeStatic
public import Feec.Models.Cube.PolyFiniteElementConvergence

/-!
# The hypotheses of `FEEC.WeakSymmetryData.weakSymmetry_of` on the cube, with one constant

With the smoothers of `Feec.Models.Cube.FEM.tableRows_uniform_cochainProjection` and the
regularity constant of `Feec.Models.Cube.WeakSymmetry.exists_curlPotential_bound`, one constant
`C` bounds the continuous hypotheses, the projections and the consistency (`cube_hyps`), and the
spaces of `cubeQ` are those of Table 5.1 (`cubeQ_spaces`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Table 5.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Filter

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

theorem IsBounded.mono {Q : 𝒟.Discretization} {C C' : ℝ} (h : Q.IsBounded C) (hC : C ≤ C') :
    Q.IsBounded C' :=
  ⟨h.1.trans hC, h.2.1.trans hC, h.2.2.1.trans hC, h.2.2.2.1.trans hC, h.2.2.2.2.1.trans hC,
    h.2.2.2.2.2.trans hC⟩

/-- **The hypotheses of `FEEC.WeakSymmetryData.weakSymmetry_of` on the cube with one constant.** -/
theorem cube_hyps : ∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C₀ : ℝ)
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C₀)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C₀) (C : ℝ),
    𝒟.IsStable C ∧ ∀ N, (cubeQ hT hB N).IsBounded C ∧ (cubeQ hT hB N).Compatible ∧
      (cubeQ hT hB N).IsConsistent C (Feec.Models.Cube.FEM.meshSize N) := by
  obtain ⟨p, C₀, hT, hB, -⟩ := tableRows_uniform_cochainProjection
  obtain ⟨CR, hCR0, hCR⟩ := exists_curlPotential_bound
  obtain ⟨A, hA0, hA⟩ := cubeQ_isConsistent hT hB hCR0 hCR
  have h2C := hT.two_mul_nonneg
  have hpi : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hs : 0 ≤ √2 := Real.sqrt_nonneg 2
  refine ⟨p, C₀, hT, hB, (2 * Real.pi)⁻¹ + CR + √2 + 2 * C₀ + A,
    isStable_𝒟 hCR0 hCR (by linarith) (by linarith) (by linarith), fun N =>
    ⟨IsBounded.mono (cubeQ_isBounded hT hB N) (by linarith), cubeQ_compatible hT hB N,
      hA _ (by linarith) N⟩⟩

/-- **The spaces of `cubeQ` are the elements of Table 5.1.** -/
theorem cubeQ_spaces {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C₀ : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C₀)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C₀) (N : ℕ) :
    ((cubeQ hT hB N).V0 : Set W0) = femSpaceMinOn (cubeDomain 3) (cubeMesh N) topSeq 0 ∧
      ((cubeQ hT hB N).V1 : Set W1) = femSpaceMinOn (cubeDomain 3) (cubeMesh N) topSeq 1 ∧
      ((cubeQ hT hB N).V2 : Set W2) = femSpaceMinOn (cubeDomain 3) (cubeMesh N) topSeq 2 ∧
      ((cubeQ hT hB N).Vt0 : Set (Wv W0)) =
        {v | ∀ a, v a ∈ femSpaceMinOn (cubeDomain 3) (cubeMesh N) bottomSeq 0} ∧
      ((cubeQ hT hB N).Vt1 : Set (Wv W1)) =
        {v | ∀ a, v a ∈ femSpaceMinOn (cubeDomain 3) (cubeMesh N) bottomSeq 1} ∧
      ((cubeQ hT hB N).Vt2 : Set (Wv W2)) =
        {v | ∀ a, v a ∈ femSpaceMinOn (cubeDomain 3) (cubeMesh N) bottomSeq 2} := by
  have hT' := fun k => polyMin_V_eq topSeq N k
  have hB' := fun k => polyMin_V_eq bottomSeq N k
  rw [topSeq_toFeec] at hT'
  rw [bottomSeq_toFeec] at hB'
  refine ⟨hT' 0, hT' 1, hT' 2, ?_, ?_, ?_⟩ <;>
  · ext v
    exact forall_congr' fun a => by rw [← hB']; rfl

end FEEC
