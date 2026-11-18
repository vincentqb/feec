module

public import Solution.CubeSpaces

/-!
# The projection errors of the cube discretizations

The projection errors of `cubeQ` in the norms of `projErrorSq` are those of `Feec`'s
`Feec.Models.Cube.WeakSymmetry.cubeFEM` (`projErr0_eq`, `projErr1_eq`, `projErr2_eq`): the input
of the static rate of `FEEC.weakSymmetry_cube` (`Solution.CubeSobolev`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 5.5, Prop 5.9

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

section FEM

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

theorem projErr0_eq (N : ℕ) (σ : 𝒟.d0.domain) :
    ‖(cubeQ hT hB N).π0 σ - σ‖ = ‖(cubeFEM hT hB N).P0 σ - (σ : U0)‖ ∧
      ‖(cubeQ hT hB N).π1 (𝒟.d0 σ) - 𝒟.d0 σ‖ =
        ‖bggSegment.d0 ((cubeFEM hT hB N).P0 σ - (σ : U0))‖ := by
  refine ⟨rfl, ?_⟩
  have e : D0 (projU0 (hT.proj N) σ - (σ : U0)) = (hT.proj N).π 1 (D0 σ) - D0 σ := by
    rw [LinearPMap.map_sub]; congr 1; exact D0_π (hT.proj N) σ
  change _ = ‖D0 (projU0 (hT.proj N) σ - (σ : U0))‖
  rw [e]
  rfl

theorem projErr1_eq (N : ℕ) (φ : 𝒟.dt0.domain) :
    ‖(cubeQ hT hB N).πt0 φ - φ‖ = ‖(cubeFEM hT hB N).Pt0 (e0 φ) - e0 φ‖ ∧
      ‖(cubeQ hT hB N).πt1 (𝒟.dt0 φ) - 𝒟.dt0 φ‖ =
        ‖bggSegment.dt0 ((cubeFEM hT hB N).Pt0 (e0 φ) - e0 φ)‖ := by
  have e0' : (cubeQ hT hB N).πt0 φ - φ = incl0 ((cubeFEM hT hB N).Pt0 (e0 φ) - e0 φ) := by
    rw [map_sub]; rfl
  refine ⟨by rw [e0']; exact norm_incl0 _, ?_⟩
  have e : (cubeQ hT hB N).πt1 (𝒟.dt0 φ) - 𝒟.dt0 φ =
      incl1 (bggSegment.dt0 ((cubeFEM hT hB N).Pt0 (e0 φ) - e0 φ)) := by
    refine PiLp.ext fun a => ?_
    change (hB.proj N).π 1 (D0 ⟨_, φ.2 a⟩) - D0 ⟨_, φ.2 a⟩ =
      D0 (projU0 (hB.proj N) ⟨_, φ.2 a⟩ - ⟨_, φ.2 a⟩)
    rw [LinearPMap.map_sub]; congr 1; exact (D0_π (hB.proj N) ⟨_, φ.2 a⟩).symm
  rw [e]
  exact norm_incl1 _

theorem projErr2_eq (N : ℕ) (u : 𝒟.dt1.domain) :
    ‖(cubeQ hT hB N).πt1 u - u‖ = ‖(cubeFEM hT hB N).Pt1 (e1 u) - e1 u‖ ∧
      ‖(cubeQ hT hB N).π2 (𝒟.S1 ((cubeQ hT hB N).πt1 u - u))‖ =
        ‖(cubeFEM hT hB N).S1h ((cubeFEM hT hB N).Pt1 (e1 u) - e1 u)‖ ∧
      ‖(cubeQ hT hB N).πt2 (𝒟.dt1 u) - 𝒟.dt1 u‖ =
        ‖bggSegment.dt1 ((cubeFEM hT hB N).Pt1 (e1 u) - e1 u)‖ := by
  have e : (cubeQ hT hB N).πt1 u - u = incl1 ((cubeFEM hT hB N).Pt1 (e1 u) - e1 u) := by
    rw [map_sub]; rfl
  refine ⟨by rw [e]; exact norm_incl1 _, ?_, ?_⟩
  · rw [e]; rfl
  · congr 1
    refine PiLp.ext fun a => ?_
    change (hB.proj N).π 2 (D1 ⟨_, u.2 a⟩) - D1 ⟨_, u.2 a⟩ =
      D1 (projU1 (hB.proj N) ⟨_, u.2 a⟩ - ⟨_, u.2 a⟩)
    rw [LinearPMap.map_sub]; congr 1; exact (D1_π (hB.proj N) ⟨_, u.2 a⟩).symm

end FEM

end FEEC
