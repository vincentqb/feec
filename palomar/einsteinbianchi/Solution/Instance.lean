module

public import Solution.CubeMain
public import Solution.MirrorSpaces
public import Solution.Bounded
public import Feec.Models.Cube.WeakSymmetryEstimates

/-!
# The cube instance of the abstract theorem: no best approximation of `S¹`

No element of the Raviart–Thomas space approximates `S¹` of the bottom space of the cube
discretizations at the order `h` (`cube_bestApprox`:
`Feec.Models.Cube.WeakSymmetry.exists_bestApproxError_ge`, read on the glued spaces with
`Feec.FiniteElement.LocalElement.glue_mem_minimal`, `bestApprox_of`).

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
