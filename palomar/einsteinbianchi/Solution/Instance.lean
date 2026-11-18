module

public import Solution.CubeMain
public import Solution.MirrorSpaces
public import Solution.Bounded
public import Feec.Models.Cube.WeakSymmetryEstimates

/-!
# The cube instance of the abstract theorem: `Sₕ ≠ S`, and no best approximation of `S¹`

On the bottom space `Ṽₕ⁰` of the cube discretizations, `S⁰ₕ = π¹S⁰ ≠ S⁰` (`cube_S0h_ne`): for
BGG data, `S⁰ψ ∈ Vₕ¹` forces `S¹d̃ψ = -d¹S⁰ψ ∈ Vₕ²` (`π1_S0_ne_of_pos`), and the row-wise
gradient `v_N = d̃ψ_N` of `Feec.Models.Cube.WeakSymmetry.phiN` has `S¹ v_N` away from the
Raviart–Thomas space (`le_norm_sq_wsL2_vN_sub_glue`, read on the glued spaces by
`gradApprox_of`). No element of the Raviart–Thomas space approximates `S¹` of the bottom space at
the order `h` (`cube_bestApprox`: `Feec.Models.Cube.WeakSymmetry.exists_bestApproxError_ge`, read
on the glued spaces with `Feec.FiniteElement.LocalElement.glue_mem_minimal`, `bestApprox_of`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Prop 5.9

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

/-! ### `Sₕ ≠ S` on the discrete space -/

namespace WeakSymmetryData.Discretization

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2}

/-- **`S⁰ₕψ ≠ S⁰ψ` when `S¹d̃ψ` is away from `Vₕ²`**: for BGG data, `S⁰ψ ∈ Vₕ¹` would give
`S¹d̃ψ = -d¹S⁰ψ ∈ Vₕ²`. -/
theorem π1_S0_ne_of_pos (hD : D.IsBGG) (Q : D.Discretization) (ψ : D.dt0.domain)
    (h : ∀ w ∈ Q.V2, 0 < ‖D.S1 (D.dt0 ψ) - w‖) : Q.π1 (D.S0 ψ) ≠ D.S0 ψ := by
  intro he
  obtain ⟨hd, hS⟩ := hD.2.2 ψ
  have hV : D.d1 ⟨_, hd⟩ ∈ Q.V2 := Q.d1_mem ⟨_, hd⟩ (show D.S0 ψ ∈ Q.V1 from he ▸ Q.π1_mem _)
  rw [hS] at hV
  have := h _ (neg_mem_iff.1 hV)
  rw [sub_self, norm_zero] at this
  exact lt_irrefl _ this

end WeakSymmetryData.Discretization

/-- **The glued form of `le_norm_sq_wsL2_vN_sub_glue`**, on any mesh `m` of `Ω = m.domain`: a
row-wise gradient `ψ = glue φ`, `φ ∈ P₂Λ̊⁰ ⊗ ℝ³`, of the glued space, in `D(d̊)³`, whose
`S¹ d̊ψ` is away from every glued `P₁⁻Λ²` field. -/
theorem gradApprox_of {m : Feec.Mesh.SimplicialMesh 3} {Ω : Set (Fin 3 → ℝ)} (h : m.domain = Ω)
    (hm : IsOpen m.domain) (hΩ : IsOpen Ω) (x₀ : Fin 3 → ℝ)
    (hstar : ∀ x ∈ closure m.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ m.domain)
    (φ : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace m 0)
    (hφ0 : ∀ a, (φ a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 0) ∈
      (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ m 0)
    (hb : ∀ w : (polyElement 3 PolySeq.lowestOrder).Piecewise m 2,
      0 < ‖wsL2 (Ω := m.domain) ((1 : ℕ) : ℤ)
          ((polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((0 + 1 : ℕ) : ℤ)
            fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise m 0
              (φ a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 0)) -
        (polyElement 3 PolySeq.lowestOrder).glue m (((1 : ℕ) : ℤ) + 1) w‖) :
    ∃ ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0)),
      (∀ a, ψ a ∈ ((deRham ℝ 3).minimalSubcomplexOfEq h hm hΩ
        (PolySeq.lagrangeP2.subcomplexMin m hm x₀ hstar)).V 0) ∧
      ∃ hψ : ∀ a, ψ a ∈ ((extDerivOp ℝ 3 0).minimal Ω).domain,
        ∀ w ∈ ((deRham ℝ 3).minimalSubcomplexOfEq h hm hΩ
          (PolySeq.lowestOrder.subcomplexMin m hm x₀ hstar)).V 2,
          0 < ‖@id (L2F ℝ Ω (formIdx 3 2)) (wsL2 (Ω := Ω) 1
              (vecOpC (n := 3) ((extDerivOp ℝ 3 0).minimal Ω) ⟨ψ, hψ⟩)) -
            @id (L2F ℝ Ω (formIdx 3 2)) w‖ := by
  subst h
  have hg := fun a => (polyElement 3 PolySeq.lagrangeP2).glue_mem_minimal m hm x₀ hstar 0
    ⟨_, hφ0 a⟩
  set Ψ := (polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((0 : ℕ) : ℤ)
    (fun a => (φ a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 0)) with hΨ
  have hdom : ∀ a, Ψ a ∈ ((extDerivOp ℝ 3 0).minimal m.domain).domain := fun a => (hg a).1
  refine ⟨Ψ, fun a => ⟨⟨_, hφ0 a⟩, rfl⟩, hdom, fun w hw => ?_⟩
  obtain ⟨w', rfl⟩ := hw
  have hd : vecOpC (n := 3) ((extDerivOp ℝ 3 0).minimal m.domain) ⟨Ψ, hdom⟩ =
      (polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((0 + 1 : ℕ) : ℤ)
        (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise m 0
          (φ a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 0)) :=
    PiLp.ext fun a => (hg a).2
  rw [hd]
  exact hb w'.1

/-- **`S⁰ₕ ≠ S⁰` on the bottom space** `Ṽₕ⁰` of the cube discretizations (`N ≥ 2`): the field
`ψ_N = (0, 0, φ_N)` of `Feec.Models.Cube.WeakSymmetry.phiN`, whose gradient `v_N` has `S¹ v_N`
away from the Raviart–Thomas space (`le_norm_sq_wsL2_vN_sub_glue`). -/
theorem cube_S0h_ne {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C₀ : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C₀)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C₀) :
    ∀ N, 2 ≤ N → ∃ ψ : 𝒟.dt0.domain, (ψ : Wv W0) ∈ (cubeQ hT hB N).Vt0 ∧
      (cubeQ hT hB N).π1 (𝒟.S0 ψ) ≠ 𝒟.S0 ψ := by
  intro N h2
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hφ0 : ∀ a, ((Pi.single 2 (phiN M) : Fin 3 → _) a :
      (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (M + 2)) 0) ∈
        (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ (mesh 3 (M + 2)) 0 := fun a => by
    by_cases ha : a = 2
    · subst ha; rw [Pi.single_eq_same]; exact phiN_mem₀ M
    · rw [Pi.single_eq_of_ne ha]; exact Submodule.zero_mem _
  have hv : (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 (M + 2)) 0
      (((Pi.single 2 (phiN M) : Fin 3 → _) a :
        (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (M + 2)) 0))) =
      fun a => (vN M a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (M + 2)) 1) := by
    funext a
    by_cases ha : a = 2
    · subst ha; rw [Pi.single_eq_same, vN, Pi.single_eq_same]; rfl
    · rw [Pi.single_eq_of_ne ha, vN_ne_two ha]; exact map_zero _
  obtain ⟨ψ, hmem, hψ, hpos⟩ := gradApprox_of (mesh_domain 3 (M + 2))
    (isOpen_mesh_domain 3 (M + 2)) (isOpen_cubeDomain 3) (center 3) (strictStar_mesh 3 (M + 2))
    (Pi.single 2 (phiN M)) hφ0 fun w => by
      have hL := le_norm_sq_wsL2_vN_sub_glue M w
      have h0 : 0 < hN (M + 2) * refDist ^ 2 := mul_pos (hN_pos _) (pow_pos refDist_pos 2)
      rw [hv]
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
        (by rw [zero_pow two_ne_zero]; exact h0.trans_le hL)
  exact ⟨⟨ψ, hψ⟩, hmem, WeakSymmetryData.Discretization.π1_S0_ne_of_pos isBGG_𝒟 _ _ hpos⟩

/-! ### No best approximation of `S¹` at the order `h` -/

/-- **The glued form of `exists_bestApproxError_ge`**, on any mesh `m` of `Ω = m.domain`. -/
theorem bestApprox_of {m : Feec.Mesh.SimplicialMesh 3} {Ω : Set (Fin 3 → ℝ)} (h : m.domain = Ω)
    (hm : IsOpen m.domain) (hΩ : IsOpen Ω) (x₀ : Fin 3 → ℝ)
    (hstar : ∀ x ∈ closure m.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ m.domain)
    {c : ℝ} (v : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace m 1)
    (hv0 : ∀ a, (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 1) ∈
      (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ m 1)
    (hpos : 0 < ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((1 : ℕ) : ℤ)
      (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 1))‖)
    (hb : ∀ w : (polyElement 3 PolySeq.lowestOrder).Piecewise m 2,
      c * √(‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((1 : ℕ) : ℤ)
          (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 1))‖ ^ 2 +
        ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((1 + 1 : ℕ) : ℤ)
          (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise m 1
            (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 1))‖ ^ 2) ≤
      ‖wsL2 (Ω := m.domain) ((1 : ℕ) : ℤ)
          ((polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((1 : ℕ) : ℤ)
            fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 1)) -
        (polyElement 3 PolySeq.lowestOrder).glue m (((1 : ℕ) : ℤ) + 1) w‖) :
    ∃ v' : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 1)),
      (∀ a, v' a ∈ ((deRham ℝ 3).minimalSubcomplexOfEq h hm hΩ
        (PolySeq.lagrangeP2.subcomplexMin m hm x₀ hstar)).V 1) ∧ v' ≠ 0 ∧
      ∃ hv' : ∀ a, v' a ∈ ((extDerivOp ℝ 3 1).minimal Ω).domain,
        ∀ w ∈ ((deRham ℝ 3).minimalSubcomplexOfEq h hm hΩ
          (PolySeq.lowestOrder.subcomplexMin m hm x₀ hstar)).V 2,
          c * √(‖v'‖ ^ 2 + ‖vecOpC (n := 3) ((extDerivOp ℝ 3 1).minimal Ω) ⟨v', hv'⟩‖ ^ 2) ≤
            ‖@id (L2F ℝ Ω (formIdx 3 2)) (wsL2 (Ω := Ω) 1 v') - @id (L2F ℝ Ω (formIdx 3 2)) w‖ := by
  subst h
  have hg := fun a => (polyElement 3 PolySeq.lagrangeP2).glue_mem_minimal m hm x₀ hstar 1
    ⟨_, hv0 a⟩
  set V := (polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((1 : ℕ) : ℤ)
    (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 1)) with hV
  have hdom : ∀ a, V a ∈ ((extDerivOp ℝ 3 1).minimal m.domain).domain := fun a => (hg a).1
  refine ⟨V, fun a => ⟨⟨_, hv0 a⟩, rfl⟩, fun h0 => hpos.ne' (by rw [h0, norm_zero]), hdom,
    fun w hw => ?_⟩
  obtain ⟨w', rfl⟩ := hw
  have hd : vecOpC (n := 3) ((extDerivOp ℝ 3 1).minimal m.domain) ⟨V, hdom⟩ =
      (polyElement 3 PolySeq.lagrangeP2).tensorGlue m 3 ((1 + 1 : ℕ) : ℤ)
        (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise m 1
          (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise m 1)) :=
    PiLp.ext fun a => (hg a).2
  rw [hd]
  exact hb w'.1

/-- **No `O(h)` best approximation of `S¹` on the bottom space by the Raviart–Thomas space.** -/
theorem cube_bestApprox {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C₀ : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C₀)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C₀) :
    ∃ c > 0, ∀ N, 2 ≤ N → ∃ v : 𝒟.dt1.domain, (v : Wv W1) ∈ (cubeQ hT hB N).Vt1 ∧
      (v : Wv W1) ≠ 0 ∧ ∀ w ∈ (cubeQ hT hB N).V2,
        c * √(‖(v : Wv W1)‖ ^ 2 + ‖𝒟.dt1 v‖ ^ 2) ≤ ‖𝒟.S1 v - w‖ := by
  obtain ⟨c, hc, hex⟩ := exists_bestApproxError_ge
  refine ⟨c, hc, fun N hN => ?_⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  obtain ⟨v, hv0, -, hpos, hb⟩ := hex M
  obtain ⟨v', hmem, hne, hv', hle⟩ := bestApprox_of (mesh_domain 3 (M + 2))
    (isOpen_mesh_domain 3 (M + 2)) (isOpen_cubeDomain 3) (center 3) (strictStar_mesh 3 (M + 2))
    v hv0 hpos hb
  exact ⟨⟨v', hv'⟩, hmem, hne, hle⟩

end FEEC
