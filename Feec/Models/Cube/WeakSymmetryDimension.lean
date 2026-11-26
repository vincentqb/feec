module

public import Feec.Models.Cube.DeRhamPartialFEM
public import Feec.Models.Cube.WeakSymmetryFEM

/-!
# Dimensions of the finite element spaces of the weak-symmetry method on the cube

On the Freudenthal meshes of `Q = (0, ½)³`, the top space `P₁⁻Λ¹` of the weak-symmetry method has
a smaller dimension than its bottom space of `P₂Λ⁰` fields, both with vanishing traces on `∂Q` and
with the mirror conditions.

## Main results

* `finrank_polyMin_lt`: `dim P₁⁻Λ̊¹ < 3 dim P₂Λ̊⁰`.
* `finrank_polyPartial_lt`: `dim P₁⁻Λ¹ < Σₐ dim P₂Λ⁰_{Γₐ}`, `Γₐ` the faces of `Q` in `{x_a = 0, ½}`.
-/

open Set Finset

@[expose] public noncomputable section

namespace Feec.Domain.ConstCoeffComplex

theorem finrank_minimalSubcomplexOfEq {n : ℕ} (C : ConstCoeffComplex (Fin n → ℝ) ℝ)
    {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (S : (C.minimalComplex hΩ).Subcomplex) (k : ℤ) :
    Module.finrank ℝ ((C.minimalSubcomplexOfEq h hΩ hΩ' S).V k) =
      Module.finrank ℝ (S.V k) := by
  subst h; rfl

end Feec.Domain.ConstCoeffComplex

namespace Feec.FiniteElement.PolySeq

theorem finrank_lowestOrder_test_one (m : ℕ) :
    Module.finrank ℝ (lowestOrder.test 1 m) = if m = 1 then 1 else 0 := by
  rw [finrank_test]
  rcases m with _ | _ | m <;> simp [PolyKind.testDim, lowestOrder]

theorem finrank_lagrangeP2_test_zero (m : ℕ) :
    Module.finrank ℝ (lagrangeP2.test 0 m) = if m ≤ 1 then 1 else 0 := by
  rw [finrank_test]
  rcases m with _ | _ | m <;> simp [PolyKind.testDim, lagrangeP2]

theorem finrank_V₀_lowestOrder_one_le {n : ℕ} (M : Feec.Mesh.SimplicialMesh n)
    (hΩ : IsOpen M.domain) :
    Module.finrank ℝ ((polyElement n lowestOrder).V₀ M ((1 : ℕ) : ℤ)) ≤
      Module.finrank ℝ ((polyElement n lagrangeP2).V₀ M ((0 : ℕ) : ℤ)) := by
  rw [finrank_V₀ _ M hΩ, finrank_V₀ _ M hΩ]
  refine Finset.sum_le_sum fun m _ => Nat.mul_le_mul_left _ ?_
  rw [finrank_lowestOrder_test_one, finrank_lagrangeP2_test_zero]
  split_ifs <;> omega

end Feec.FiniteElement.PolySeq

namespace Feec.Models.Cube.WeakSymmetry

theorem finrank_tsub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : Submodule ℝ V) [FiniteDimensional ℝ P] :
    Module.finrank ℝ (tsub P) = 3 * Module.finrank ℝ P := by
  let e : tsub P ≃ₗ[ℝ] (Fin 3 → P) :=
    { toFun := fun x a => ⟨(x : Wv V) a, x.2 a⟩
      invFun := fun y => ⟨WithLp.toLp 2 fun a => (y a : V), fun a => (y a).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

end Feec.Models.Cube.WeakSymmetry

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.FiniteElement

/-! ### Vanishing traces on `∂Q` -/

theorem finrank_polyMin_V (S : PolySeq) (N : ℕ) (k : ℤ) :
    Module.finrank ℝ ((polyMin 3 S N).V k) =
      Module.finrank ℝ ((polyElement 3 S).V₀ (mesh 3 N) k) :=
  ConstCoeffComplex.finrank_minimalSubcomplexOfEq (deRham ℝ 3) (mesh_domain 3 N)
    (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3)
    (S.subcomplexMin (mesh 3 N) (isOpen_mesh_domain 3 N) (center 3) (strictStar_mesh 3 N)) k

/-- **`dim P₁⁻Λ̊¹ < 3 dim P₂Λ̊⁰`** on the Freudenthal meshes of the cube. -/
theorem finrank_polyMin_lt (N : ℕ) :
    Module.finrank ℝ ((polyMin 3 PolySeq.lowestOrder N).V 1) <
      3 * Module.finrank ℝ ((polyMin 3 PolySeq.lagrangeP2 N).V 0) := by
  rw [finrank_polyMin_V, finrank_polyMin_V]
  have hle := PolySeq.finrank_V₀_lowestOrder_one_le (mesh 3 N) (isOpen_mesh_domain 3 N)
  have hpos : 0 < Module.finrank ℝ ((polyElement 3 PolySeq.lagrangeP2).V₀ (mesh 3 N)
      ((0 : ℕ) : ℤ)) :=
    PolySeq.lagrangeP2.finrank_V₀_freudenthalMesh_pos_zero (by norm_num) (by decide)
  push_cast at hle hpos ⊢
  omega

/-! ### The mirror conditions -/

theorem finrank_partialSubcomplexOfEq {n : ℕ} {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω')
    (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω')
    (hΩQ' : Ω' ⊆ Geometry.Q (Fin n)) (J : Finset (Fin n))
    (S : (DeRhamIdent.HQpartZ hΩ hΩQ J).Subcomplex) (k : ℤ) :
    Module.finrank ℝ ((partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J S).V k) =
      Module.finrank ℝ (S.V k) := by
  subst h; rfl

theorem finrank_polyPartial_V (S : PolySeq) (N : ℕ) (J : Finset (Fin 3)) (k : ℕ) :
    Module.finrank ℝ ((polyPartial 3 S N J).V k) = ∑ m ∈ Finset.range 4,
      {g | g ∈ (mesh 3 N).faces m ∧ ¬ ∃ F ∈ partialFaces 3 J, g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  rw [polyPartial, finrank_partialSubcomplexOfEq]
  change Module.finrank ℝ ((polyElement 3 S).VPartial (mesh 3 N) (partialFaces 3 J) k) = _
  rw [LocalElement.finrank_VPartial _ _ _ (isOpen_mesh_domain 3 N),
    ← LocalElement.finrank_globalSpacePartial, PolySeq.finrank_globalSpacePartial]

theorem faces_one_eq (M : Feec.Mesh.SimplicialMesh 3) :
    M.faces 1 = ↑((LocalElement.meshFaces M).filter fun g => g.card = 2) := by
  ext g
  simp only [Feec.Mesh.SimplicialMesh.faces, Finset.coe_filter, LocalElement.mem_meshFaces,
    Set.mem_ofPred_eq]
  tauto

theorem exists_free_of_card_eq_two {g : Finset (Fin 3 → ℝ)} (hg : g.card = 2) :
    ∃ a : Fin 3, ¬ ∃ F ∈ partialFaces 3 {a}, g ⊆ F := by
  by_contra! h
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.1 (by omega : 1 < g.card)
  refine hvw (funext fun a => ?_)
  obtain ⟨F, ⟨j, hj, h0 | h0⟩, hgF⟩ := h a
  · rw [Finset.mem_singleton.1 hj] at h0
    rw [h0 v (hgF hv), h0 w (hgF hw)]
  · rw [Finset.mem_singleton.1 hj] at h0
    rw [h0 v (hgF hv), h0 w (hgF hw)]

theorem not_exists_partialFaces_of_mem_convexHull {g : Finset (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (hx : x ∈ convexHull ℝ (g : Set (Fin 3 → ℝ))) (hxΩ : x ∈ cubeDomain 3) (a : Fin 3) :
    ¬ ∃ F ∈ partialFaces 3 {a}, g ⊆ F := by
  rintro ⟨F, ⟨j, hj, hF⟩, hgF⟩
  rw [Finset.mem_singleton.1 hj] at hF
  have hxa := hxΩ a (Set.mem_univ a)
  have key : ∀ c : ℝ, (∀ v ∈ F, v a = c) → x a = c := fun c hc => by
    have hsub : (g : Set (Fin 3 → ℝ)) ⊆ {y | y a = c} := fun v hv => hc v (hgF hv)
    have hconv : Convex ℝ {y : Fin 3 → ℝ | y a = c} :=
      convex_hyperplane (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) a).isLinear c
    exact convexHull_min hsub hconv hx
  rcases hF with h0 | h0
  · rw [key 0 h0] at hxa; exact lt_irrefl _ hxa.1
  · rw [key (1 / 2) h0] at hxa; exact lt_irrefl _ hxa.2

theorem ncard_faces_one_lt (N : ℕ) : ((mesh 3 N).faces 1).ncard <
    ∑ a : Fin 3, {g | g ∈ (mesh 3 N).faces 1 ∧ ¬ ∃ F ∈ partialFaces 3 {a}, g ⊆ F}.ncard := by
  classical
  set E := (LocalElement.meshFaces (mesh 3 N)).filter fun g => g.card = 2
  have hE : (mesh 3 N).faces 1 = ↑E := faces_one_eq _
  have hEa : ∀ a : Fin 3,
      {g | g ∈ (E : Set (Finset (Fin 3 → ℝ))) ∧ ¬ ∃ F ∈ partialFaces 3 {a}, g ⊆ F} =
        ↑(E.filter fun g => ¬ ∃ F ∈ partialFaces 3 {a}, g ⊆ F) := fun a => by
    ext g; simp
  simp only [hE]
  simp only [hEa, Set.ncard_coe_finset, Finset.card_filter]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones]
  obtain ⟨g₀, hg₀, hc₀, x, hx, hxΩ⟩ := exists_meshFace_freudenthalMesh (n := 3)
    (b := 0) (s := 1 / 2) (by norm_num) (N := N + 1) (d := 1) le_rfl (by norm_num)
  have hxΩ' : x ∈ cubeDomain 3 := by rw [← mesh_domain 3 N]; exact hxΩ
  refine Finset.sum_lt_sum (fun g hg => ?_) ⟨g₀, Finset.mem_filter.2 ⟨hg₀, hc₀⟩, ?_⟩
  · obtain ⟨a, ha⟩ := exists_free_of_card_eq_two (Finset.mem_filter.1 hg).2
    exact (Finset.single_le_sum (f := fun a : Fin 3 =>
      if ¬ ∃ F ∈ partialFaces 3 {a}, g ⊆ F then 1 else 0) (fun _ _ => by positivity)
      (Finset.mem_univ a)).trans_eq' (by simp [ha])
  · simp [not_exists_partialFaces_of_mem_convexHull hx hxΩ']

/-- **`dim P₁⁻Λ¹ < Σₐ dim P₂Λ⁰_{Γₐ}`** on the Freudenthal meshes of the cube. -/
theorem finrank_polyPartial_lt (N : ℕ) :
    Module.finrank ℝ ((polyPartial 3 PolySeq.lowestOrder N ∅).V 1) <
      ∑ a : Fin 3, Module.finrank ℝ ((polyPartial 3 PolySeq.lagrangeP2 N {a}).V 0) := by
  have hV1 : Module.finrank ℝ ((polyPartial 3 PolySeq.lowestOrder N ∅).V ((1 : ℕ) : ℤ)) =
      ((mesh 3 N).faces 1).ncard := by
    rw [finrank_polyPartial_V]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      PolySeq.finrank_lowestOrder_test_one, partialFaces_empty]
    simp
  have hVa : ∀ a : Fin 3,
      {g | g ∈ (mesh 3 N).faces 1 ∧ ¬ ∃ F ∈ partialFaces 3 {a}, g ⊆ F}.ncard ≤
        Module.finrank ℝ ((polyPartial 3 PolySeq.lagrangeP2 N {a}).V ((0 : ℕ) : ℤ)) := by
    intro a
    rw [finrank_polyPartial_V]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      PolySeq.finrank_lagrangeP2_test_zero]
    simp
  have h := (ncard_faces_one_lt N).trans_le (Finset.sum_le_sum fun a _ => hVa a)
  rw [← hV1] at h
  exact_mod_cast h

end Feec.Models.Cube.FEM
