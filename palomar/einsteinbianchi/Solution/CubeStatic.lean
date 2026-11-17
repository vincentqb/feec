module

public import Solution.CubeSpaces

/-!
# The static rate on the cube

The rate of `FEEC.weakSymmetry_cube` for (5.3) is `FEEC.WeakSymmetryData.weakSymmetry_of` (the
abstract Thm 5.5) applied to `cubeQ`: the projection errors of exact solutions `C²` up to `∂Q`
with vanishing tangential traces are `O(L h)` (`cubeFEM_err_P0_tr`, `cubeFEM_err_Pt0_tr`,
`cubeFEM_err_gnSq_tr`, `cubeFEM_err_S1_tr`), and `S¹u` is of the same class
(`exists_isCsFormTr_segS1`), so `‖S¹u‖` and `‖d¹*S¹u‖` are `O(L)`.

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

set_option maxHeartbeats 1000000 in
/-- **The static rate on the cube** from the abstract theorem. -/
theorem cube_static_rate {C' : ℝ} (hS : 𝒟.IsStable C') (hb : ∀ N, (cubeQ hT hB N).IsBounded C')
    (hc : ∀ N, (cubeQ hT hB N).IsConsistent C' (Feec.Models.Cube.FEM.meshSize N)) :
    ∃ K, ∀ N F σ φ u lam σh φh uh lamh L, 𝒟.IsSolution F σ φ u lam →
      IsCsFormTr 0 0 L (σ : W0) → (∀ a, IsCsFormTr 0 0 L ((φ : Wv W0) a)) →
      (∀ a, IsCsFormTr 0 1 L ((u : Wv W1) a)) → ‖lam‖ ≤ L →
      (cubeQ hT hB N).IsDiscreteSolution F σh φh uh lamh →
      (cubeQ hT hB N).errorSq σ σh φ φh u uh ≤
        (K * L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by
  obtain ⟨K₀, hK₀⟩ := WeakSymmetryData.weakSymmetry_of.{0} C'
  obtain ⟨c, hc1, hcS⟩ := exists_isCsFormTr_segS1
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧
      2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 0) ^ 2 +
      3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 0) ^ 2) +
      (1 + 8 * C ^ 2) * (3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2)) +
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * c ^ 2 ≤ A :=
    ⟨_, by positivity, le_rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = (Fintype.card (formIdx 3 2) : ℝ) * c := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂0, hc₂⟩ : ∃ c₂ : ℝ, 0 ≤ c₂ ∧ c₂ = (Fintype.card (formIdx 3 1) : ℝ) * (3 * c) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨B, hB0, hBdef⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = A + (1 + c₂) ^ 2 + c₁ ^ 2 :=
    ⟨_, by positivity, rfl⟩
  refine ⟨√(max K₀ 0 * B), fun N F σ φ u lam σh φh uh lamh L hsol hσ hφ hu hlam hdisc => ?_⟩
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hlam
  obtain ⟨h, hh0, rfl⟩ : ∃ h, 0 ≤ h ∧ h = Feec.Models.Cube.FEM.meshSize N :=
    ⟨_, (meshSize_pos N).le, rfl⟩
  have hu' : ∀ a, IsCsFormTr 0 1 L ((e1 u a : U1) : W1) := hu
  have hSu := hcS (e1 u) hL0 hu'
  rw [S1_e1] at hSu
  have hcL : 0 ≤ c * L := mul_nonneg (by linarith) hL0
  have hn := hSu.norm_le hcL
  have hz : ∀ w : 𝒟.d1.domain, |⟪𝒟.S1 u, 𝒟.d1 w⟫_ℝ| ≤ (L + c₂ * L) * ‖(w : W1)‖ := fun w => by
    have := hSu.abs_inner_D1_le hcL w
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : (Fintype.card (formIdx 3 1) : ℝ) * (3 * (c * L)) = c₂ * L := by rw [hc₂]; ring
    linarith
  obtain ⟨-, hrate⟩ := hK₀ 𝒟 (cubeQ hT hB N) isBGG_𝒟 hS (hb N) (cubeQ_compatible hT hB N)
  have key := hrate _ (L + c₂ * L) hh0 (hc N) F σ φ u lam σh φh uh lamh hsol
    (hlam.trans (le_add_of_nonneg_right (mul_nonneg hc₂0 hL0))) hz hdisc
  set P := (cubeQ hT hB N).projErrorSq σ φ u with hPdef
  set R := ‖𝒟.S1 u - (cubeQ hT hB N).π2 (𝒟.S1 u)‖ ^ 2 with hRdef
  set S := ‖𝒟.S1 u‖ with hSdef
  have hPR : P + R ≤ A * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by
    have e : P =
        (‖(cubeQ hT hB N).π0 σ - σ‖ ^ 2 + ‖(cubeQ hT hB N).π1 (𝒟.d0 σ) - 𝒟.d0 σ‖ ^ 2) +
        (‖(cubeQ hT hB N).πt0 φ - φ‖ ^ 2 + ‖(cubeQ hT hB N).πt1 (𝒟.dt0 φ) - 𝒟.dt0 φ‖ ^ 2) +
        (‖(cubeQ hT hB N).πt1 u - u‖ ^ 2 +
          ‖(cubeQ hT hB N).π2 (𝒟.S1 ((cubeQ hT hB N).πt1 u - u))‖ ^ 2 +
          ‖(cubeQ hT hB N).πt2 (𝒟.dt1 u) - 𝒟.dt1 u‖ ^ 2) := by
      rw [hPdef]; unfold WeakSymmetryData.Discretization.projErrorSq; ring
    obtain ⟨e00, e01⟩ := projErr0_eq hT hB N σ
    obtain ⟨e10, e11⟩ := projErr1_eq hT hB N φ
    obtain ⟨e20, e21, e22⟩ := projErr2_eq hT hB N u
    rw [e]
    have h0 := cubeFEM_err_P0_tr hT hB N hL0 σ hσ
    have h1 := cubeFEM_err_Pt0_tr hT hB N hL0 (e0 φ) hφ
    have h2 := cubeFEM_err_gnSq_tr hT hB N hL0 (e1 u) hu'
    unfold Feec.BGG.graphSq at h0 h1
    unfold Feec.BGG.Discrete.gnSq at h2
    rw [← e00, ← e01] at h0
    rw [← e10, ← e11] at h1
    rw [← e20, ← e21, ← e22] at h2
    have h3 := cubeFEM_err_S1_tr hT hB N hcL (e1 u) (by rw [S1_e1]; exact hSu)
    rw [S1h_e1, S1_e1] at h3
    have hLh := sq_nonneg (L * Feec.Models.Cube.FEM.meshSize N)
    have e4 : (c * L * Feec.Models.Cube.FEM.meshSize N) ^ 2 =
        c ^ 2 * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by ring
    rw [e4] at h3
    have hA' := mul_le_mul_of_nonneg_right hA hLh
    linarith
  have hS1 : S ≤ c₁ * L := hn.trans (le_of_eq (by rw [hc₁]; ring))
  have hS2 : S ^ 2 ≤ c₁ ^ 2 * L ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hS1 2
    rw [mul_pow] at this; exact this
  have hX : P + Feec.Models.Cube.FEM.meshSize N ^ 2 * ((L + c₂ * L) ^ 2 + S ^ 2) + R ≤
      B * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hS2 (sq_nonneg (Feec.Models.Cube.FEM.meshSize N))
    rw [hBdef]
    nlinarith [sq_nonneg (L * Feec.Models.Cube.FEM.meshSize N)]
  have hX0 : 0 ≤ P + Feec.Models.Cube.FEM.meshSize N ^ 2 * ((L + c₂ * L) ^ 2 + S ^ 2) + R := by
    have : 0 ≤ P := by rw [hPdef]; unfold WeakSymmetryData.Discretization.projErrorSq; positivity
    positivity
  calc _ ≤ _ := key
    _ ≤ max K₀ 0 * (B * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2) :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0).trans
          (mul_le_mul_of_nonneg_left hX (le_max_right _ _))
    _ = (√(max K₀ 0 * B) * L * Feec.Models.Cube.FEM.meshSize N) ^ 2 := by
        have hs : √(max K₀ 0 * B) ^ 2 = max K₀ 0 * B :=
          Real.sq_sqrt (mul_nonneg (le_max_right _ _) hB0)
        rw [show (√(max K₀ 0 * B) * L * Feec.Models.Cube.FEM.meshSize N) ^ 2 =
          √(max K₀ 0 * B) ^ 2 * (L * Feec.Models.Cube.FEM.meshSize N) ^ 2 by ring, hs]
        ring

end FEM

end FEEC
