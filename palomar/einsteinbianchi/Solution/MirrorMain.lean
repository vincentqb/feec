module

public import Solution.MirrorSpaces
public import Solution.MirrorRate

/-!
# The mirror scheme (6.5) on the cube

`mirror_fem_main`: on the Freudenthal meshes of the cube, the mirror scheme `mirrorQ` (one
parity smoother for both rows, `exists_mirror_estimates`) has the spaces of Table 6.1 with the
mirror boundary conditions (`mirrorQ_spaces`), uniformly bounded projections satisfying (5.4)
and consistent at the order `h` (`mirrorQ_isBounded`, `mirrorQ_compatible`,
`mirrorQ_isConsistent`), unique solutions of (6.5) (`IsDiscreteWave.eq_of_eq`) along which the
discrete Gauss law propagates (`IsDiscreteWave.isGauss`, the mirror data being BGG data), and
the `O(h)` rate for TSD data of `D(L³)` (`mirrorQ_rate`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2, §6.3, (6.5), Table 6.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.MirrorWeakSymmetry
open WeakSymmetryData.Discretization (IsDiscreteWave.eq_of_eq IsDiscreteWave.isGauss)

/-- **The mirror scheme (6.5) on the cube**: spaces, bounds, (5.4), consistency, uniqueness,
propagation of the discrete Gauss law and the `O(h)` rate for TSD data of `D(L³)`. -/
theorem mirror_fem_main : ∃ (𝒯 : ℕ → SimplicialMesh 3) (Q : ℕ → mirrorData.Discretization)
    (C K : ℝ), IsMeshFamily (cube 3) 𝒯 ∧ IsFreudenthal 𝒯 ∧
    (∀ N, ((Q N).V0 : Set (L2Form (cube 3) 0)) = femSpace (cube 3) (𝒯 N) topSeq 0 ∧
      ((Q N).V1 : Set (L2Form (cube 3) 1)) = femSpace (cube 3) (𝒯 N) topSeq 1 ∧
      ((Q N).V2 : Set (L2Form (cube 3) 2)) = femSpace (cube 3) (𝒯 N) topSeq 2 ∧
      ((Q N).Vt0 : Set (L2Vec (cube 3) 0)) =
        {v | ∀ a, v a ∈ femSpacePart {a} (𝒯 N) bottomSeq 0} ∧
      ((Q N).Vt1 : Set (L2Vec (cube 3) 1)) =
        {v | ∀ a, v a ∈ femSpacePart {a} (𝒯 N) bottomSeq 1} ∧
      ((Q N).Vt2 : Set (L2Vec (cube 3) 2)) =
        {v | ∀ a, v a ∈ femSpacePart {a} (𝒯 N) bottomSeq 2}) ∧
    (∀ N, (Q N).IsBounded C ∧ (Q N).Compatible ∧ (Q N).IsConsistent C (meshSize (𝒯 N))) ∧
    (∀ N T σ φ u M ρ lam σ' φ' u' M' ρ' lam', 0 < T →
      (Q N).IsDiscreteWave T 0 σ φ u M ρ lam → (Q N).IsDiscreteWave T 0 σ' φ' u' M' ρ' lam' →
      σ 0 = σ' 0 → u 0 = u' 0 → M 0 = M' 0 → ρ 0 = ρ' 0 →
      ∀ t ∈ Icc 0 T, σ t = σ' t ∧ u t = u' t ∧ M t = M' t ∧ ρ t = ρ' t) ∧
    (∀ N T σ φ u M ρ lam, 0 < T → (Q N).IsDiscreteWave T 0 σ φ u M ρ lam →
      (Q N).IsGauss (σ 0) (u 0) → ∀ t ∈ Icc 0 T, (Q N).IsGauss (σ t) (u t)) ∧
    0 ≤ K ∧ ∀ N (D : Feec.Models.Cube.MirrorWeakSymmetry.TSDDatum)
      (h3 : D.LLU₀ ∈ Feec.Models.Cube.MirrorBGG.complexQ.wave.domain) (T : ℝ), 0 < T →
      ∀ U : ℝ → PiLp 2 Feec.Models.Cube.MirrorBGG.SpaceQ, U 0 = D.U₀ →
        Feec.Evolution.IsStrongSolution Feec.Models.Cube.MirrorBGG.complexQ.wave (Icc 0 T) 0 U →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T 0 σh φh uh Mh ρh lamh ∧ ∀ t ∈ Icc 0 T,
        √(‖(σh t : L2Form (cube 3) 0)‖ ^ 2 +
          ‖(show L2Vec (cube 3) 1 from Feec.Models.Cube.MirrorWeakSymmetry.rowsW1L
            (Feec.Models.Cube.MirrorWeakSymmetry.stEL (U t))) - uh t‖ ^ 2 +
          ‖Mh t‖ ^ 2 + ‖(show L2Vec (cube 3) 2 from Feec.Models.Cube.MirrorWeakSymmetry.rowsW2L
            (Feec.Models.Cube.MirrorWeakSymmetry.stBL (U t))) - ρh t‖ ^ 2) ≤
        K * (‖D.U₀‖ + ‖D.LU₀‖ + ‖D.LLU₀‖ +
          ‖Feec.Models.Cube.MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩‖) * (1 + t) *
            meshSize (𝒯 N) := by
  rw [mirrorData_eq]
  obtain ⟨ρ, C₀, hT, hB⟩ := exists_mirror_estimates
  obtain ⟨A, hA0, hA⟩ := mirrorQ_isConsistent hT hB
  obtain ⟨K, hK0, hK⟩ := mirrorQ_rate hT hB
  have h2C := hT.two_mul_nonneg
  refine ⟨cubeMesh, mirrorQ hT hB, 2 * C₀ + A, K, isMeshFamily_cube, points_cube,
    mirrorQ_spaces hT hB, fun N => ⟨(mirrorQ_isBounded hT hB N).mono (by linarith),
      mirrorQ_compatible hT hB N, ?_⟩,
    fun N T σ φ u M ρ lam σ' φ' u' M' ρ' lam' _ h1 h2 e0 e1 e2 e3 =>
      IsDiscreteWave.eq_of_eq _ h1 h2 e0 e1 e2 e3,
    fun N T σ φ u M ρ lam _ h h0 => IsDiscreteWave.isGauss _ isBGG_𝒟m h h0, hK0,
    fun N D h3 T hT0 U hU0 hU => ?_⟩
  · rw [meshSize_cubeMesh]; exact hA _ (by linarith) N
  · rw [meshSize_cubeMesh]; exact hK N D h3 T hT0 U hU0 hU

end FEEC
