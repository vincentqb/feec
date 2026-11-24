module

public import Feec.Models.Cube.DeRhamPartialFEM
public import Feec.Models.Cube.WeakSymmetryFEM

/-!
# Dimensions of the finite element spaces of the weak-symmetry method on the cube

The semi-discrete system (6.5) couples the bottom space `Ṽₕ⁰` to the top space `Vₕ¹` by the
linear map `S₀,ₕ = π¹S⁰ : Ṽₕ⁰ → Vₕ¹`, and its solutions satisfy the hidden constraint
`uₕ ⊥ d̃(ker S₀,ₕ)` (`Feec.BGG.DiscreteSolution.hidden_constraint`). For the elements of Table 6.1
on the Freudenthal meshes of `Q = (0, ½)³`, `dim Vₕ¹ < dim Ṽₕ⁰`, so every linear map
`Ṽₕ⁰ → Vₕ¹` has a nonzero kernel and, `d̃` being injective on `Ṽₕ⁰`, the hidden constraint is a
restriction on the initial values:

* with vanishing traces on `∂Q` (the spaces `P₁⁻Λ̊¹` and `(P₂Λ̊⁰)³` of `polyMin`):
  `dim P₁⁻Λ̊¹ ≤ dim P₂Λ̊⁰` on every mesh, since on every face the Whitney `1`-forms have at most as
  many degrees of freedom as the Lagrange `P₂` functions (one on every edge; one on every vertex
  and every edge: `PolySeq.finrank_lowestOrder_test_one`, `PolySeq.finrank_lagrangeP2_test_zero`,
  `PolySeq.finrank_V₀_lowestOrder_one_le`), and `P₂Λ̊⁰ ≠ 0`
  (`Feec.FiniteElement.PolySeq.finrank_V₀_freudenthalMesh_pos_zero`): `finrank_polyMin_lt`;
* with the mirror conditions (the spaces `P₁⁻Λ¹` and `∏ₐ P₂Λ⁰_{Γₐ}` of `polyPartial`, `Γₐ` the faces
  in `{x_a = 0}` or `{x_a = ½}`): `P₁⁻Λ¹` has one degree of freedom on every edge, component `a`
  one on every edge in no face of `Γₐ`; an edge has two distinct vertices, so it lies in such
  faces for at most two directions `a` (`exists_free_of_card_eq_two`), and the edge of the mesh
  through the open cube (`Feec.FiniteElement.exists_meshFace_freudenthalMesh`) for none
  (`not_exists_partialFaces_of_mem_convexHull`): `ncard_faces_one_lt`, `finrank_polyPartial_lt`.

The dimensions of the transported spaces are those of the spaces on the mesh
(`Feec.Domain.ConstCoeffComplex.finrank_minimalSubcomplexOfEq`, `finrank_partialSubcomplexOfEq`),
counted by `Feec.FiniteElement.PolySeq.finrank_V₀` and
`Feec.FiniteElement.PolySeq.finrank_globalSpacePartial` (`finrank_polyMin_V`,
`finrank_polyPartial_V`); `Feec.Models.Cube.WeakSymmetry.finrank_tsub`: `dim (Vₕ)³ = 3 dim Vₕ`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4, §5 (degrees of freedom and dimensions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2, §6.3, Table 6.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Finset

@[expose] public noncomputable section

namespace Feec.Domain.ConstCoeffComplex

/-- The spaces of a subcomplex transported along `Ω = Ω'` have the same dimensions. -/
theorem finrank_minimalSubcomplexOfEq {n : ℕ} (C : ConstCoeffComplex (Fin n → ℝ) ℝ)
    {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (S : (C.minimalComplex hΩ).Subcomplex) (k : ℤ) :
    Module.finrank ℝ ((C.minimalSubcomplexOfEq h hΩ hΩ' S).V k) =
      Module.finrank ℝ (S.V k) := by
  subst h; rfl

end Feec.Domain.ConstCoeffComplex

namespace Feec.FiniteElement.PolySeq

/-- The Whitney `1`-forms have one degree of freedom on every edge, none elsewhere. -/
theorem finrank_lowestOrder_test_one (m : ℕ) :
    Module.finrank ℝ (lowestOrder.test 1 m) = if m = 1 then 1 else 0 := by
  rw [finrank_test]
  rcases m with _ | _ | m <;> simp [PolyKind.testDim, lowestOrder]

/-- The Lagrange `P₂` functions have one degree of freedom on every vertex and every edge. -/
theorem finrank_lagrangeP2_test_zero (m : ℕ) :
    Module.finrank ℝ (lagrangeP2.test 0 m) = if m ≤ 1 then 1 else 0 := by
  rw [finrank_test]
  rcases m with _ | _ | m <;> simp [PolyKind.testDim, lagrangeP2]

/-- **`dim P₁⁻Λ̊¹ ≤ dim P₂Λ̊⁰` on every mesh**: on every face the Whitney `1`-forms have at most
as many degrees of freedom as the Lagrange `P₂` functions. -/
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

/-- `dim (Vₕ)³ = 3 dim Vₕ`. -/
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

/-- The dimensions of the spaces of `polyMin` are those of the interior degrees of freedom. -/
theorem finrank_polyMin_V (S : PolySeq) (N : ℕ) (k : ℤ) :
    Module.finrank ℝ ((polyMin 3 S N).V k) =
      Module.finrank ℝ ((polyElement 3 S).V₀ (mesh 3 N) k) :=
  ConstCoeffComplex.finrank_minimalSubcomplexOfEq (deRham ℝ 3) (mesh_domain 3 N)
    (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3)
    (S.subcomplexMin (mesh 3 N) (isOpen_mesh_domain 3 N) (center 3) (strictStar_mesh 3 N)) k

/-- **`dim P₁⁻Λ̊¹ < 3 dim P₂Λ̊⁰`** on the Freudenthal meshes of the cube: the top space `Vₕ¹` and
the bottom space `Ṽₕ⁰ = (P₂Λ̊⁰)³` of Table 6.1 with vanishing traces on `∂Q`. -/
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

/-- The spaces of a partial-boundary subcomplex transported along `Ω = Ω'` have the same
dimensions. -/
theorem finrank_partialSubcomplexOfEq {n : ℕ} {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω')
    (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω')
    (hΩQ' : Ω' ⊆ Geometry.Q (Fin n)) (J : Finset (Fin n))
    (S : (DeRhamIdent.HQpartZ hΩ hΩQ J).Subcomplex) (k : ℤ) :
    Module.finrank ℝ ((partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J S).V k) =
      Module.finrank ℝ (S.V k) := by
  subst h; rfl

/-- The dimensions of the spaces of `polyPartial`: the degrees of freedom on the faces not lying
in a face `{x_j = 0}`, `{x_j = ½}`, `j ∈ J`, of the cube. -/
theorem finrank_polyPartial_V (S : PolySeq) (N : ℕ) (J : Finset (Fin 3)) (k : ℕ) :
    Module.finrank ℝ ((polyPartial 3 S N J).V k) = ∑ m ∈ Finset.range 4,
      {g | g ∈ (mesh 3 N).faces m ∧ ¬ ∃ F ∈ partialFaces 3 J, g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  rw [polyPartial, finrank_partialSubcomplexOfEq]
  change Module.finrank ℝ ((polyElement 3 S).VPartial (mesh 3 N) (partialFaces 3 J) k) = _
  rw [LocalElement.finrank_VPartial _ _ _ (isOpen_mesh_domain 3 N),
    ← LocalElement.finrank_globalSpacePartial, PolySeq.finrank_globalSpacePartial]

/-- The edges of a mesh, as a finite set of vertex sets. -/
theorem faces_one_eq (M : Feec.Mesh.SimplicialMesh 3) :
    M.faces 1 = ↑((LocalElement.meshFaces M).filter fun g => g.card = 2) := by
  ext g
  simp only [Feec.Mesh.SimplicialMesh.faces, Finset.coe_filter, LocalElement.mem_meshFaces,
    Set.mem_ofPred_eq]
  tauto

/-- An edge lies in a face `{x_a = c}` of the cube for at most two directions `a`: its vertices
are distinct. -/
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

/-- A face whose convex hull meets the open cube lies in no face `{x_a = c}`, `c ∈ {0, ½}`. -/
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

/-- **Edges counted with their free directions**: on the Freudenthal meshes of the cube, the
number of edges is less than the number of pairs (edge, direction `a`) with the edge in no face
`{x_a = c}` of the cube. -/
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

/-- **`dim P₁⁻Λ¹ < Σₐ dim P₂Λ⁰_{Γₐ}`** on the Freudenthal meshes of the cube: the top space `Vₕ¹`
and the bottom space `Ṽₕ⁰` of Table 6.1 with the mirror conditions. -/
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
