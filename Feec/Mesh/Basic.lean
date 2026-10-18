module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Order.CompletePartialOrder

/-!
# Simplicial meshes

A simplicial mesh of a set `Ω ⊆ ℝⁿ` (coordinates `Fin n → ℝ`, with Mathlib's sup norm) is a
finite set of `n`-simplices, given as Mathlib's vertex tuples `Affine.Simplex ℝ (Fin n → ℝ) n`,
whose closed simplices `T.closedInterior = conv {p₀, …, pₙ}` cover `closure Ω`, have pairwise
disjoint interiors, and meet face to face: the intersection of two closed simplices is the
convex hull of their common vertices ([Arnold2018], Ch. 7; [Ciarlet2002], Ch. 2).

## Main definitions

* `vertexSet T`: the vertex set of a simplex, as a `Finset`.
* `refSimplex n`: the reference simplex `T̂ = conv {0, e₀, …, e_{n-1}}`.
* `Affine.Simplex.linearPart T` (`B_T`, columns `pᵢ₊₁ - p₀`), `T.refMap` (`F_T x = B_T x + p₀`)
  and `T.linearEquiv` (`B_T` as a continuous linear equivalence).
* `SimplicialMesh n`: a conforming simplicial mesh of `closure Ω`.
* `SimplicialMesh.faces M k` (vertex sets of the `k`-faces), `M.facets`, `M.cofaces F` (the
  `n`-simplices containing a facet), `M.IsInteriorFacet F`, `M.IsBoundaryFacet F`.
* `SimplicialMesh.toSimplicialComplex M`: the Mathlib `Geometry.SimplicialComplex` of all faces.
* `diam T` (`h_T`) and `SimplicialMesh.meshSize M` (`h = max_T h_T`).
* `SimplicialMesh.map M e`: the image of a mesh under an affine equivalence;
  `SimplicialMesh.Refines M₁ M₂`: every simplex of `M₁` lies in one of `M₂`.

## Main results

* `refMap_refPoints`, `map_refSimplex`, `closedInterior_eq_image_refMap`: every simplex is
  `T = F_T(T̂)`; `mem_closedInterior_refSimplex`: `T̂ = {x ≥ 0, ∑ xᵢ ≤ 1}`.
* `interior_closedInterior_nonempty`: an `n`-simplex of `ℝⁿ` has nonempty interior.
* `disjoint_interior_of_inter_eq`: face-to-face meeting and distinct vertex sets give disjoint
  interiors (`SimplicialMesh.ofConforming` builds a mesh from conformity alone).
* `SimplicialMesh.space_toSimplicialComplex`: the complex of faces has underlying space
  `closure Ω`; `faces_eq`: the `k`-faces are its faces with `k + 1` vertices.
* `SimplicialMesh.sOppSide_of_mem_cofaces`: two distinct `n`-simplices sharing a facet `F` lie
  strictly on opposite sides of `aff F` (they induce opposite orientations on `F`).
* `SimplicialMesh.card_cofaces_le_two`, `isInteriorFacet_or_isBoundaryFacet`: every facet lies
  in one or two `n`-simplices; `isInteriorFacet_iff`, `isBoundaryFacet_iff`: with two it is an
  interior facet, with one its closed hull lies in the topological boundary of `closure Ω`.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (simplicial meshes)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Ch. 2
  (triangulations, affine families)
-/

@[expose] public section

noncomputable section

open Set Filter Topology

namespace Feec.Mesh

variable {n k : ℕ}

/-! ### Vertex sets -/

/-- The vertex set `{p₀, …, p_k}` of a simplex. -/
def vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) k) : Finset (Fin n → ℝ) := by
  classical exact Finset.univ.image T.points

@[simp] theorem coe_vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    (vertexSet T : Set (Fin n → ℝ)) = Set.range T.points := by
  simp [vertexSet]

theorem mem_vertexSet {T : Affine.Simplex ℝ (Fin n → ℝ) k} {x : Fin n → ℝ} :
    x ∈ vertexSet T ↔ ∃ i, T.points i = x := by
  rw [← Finset.mem_coe, coe_vertexSet]; rfl

theorem points_mem_vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) k) (i : Fin (k + 1)) :
    T.points i ∈ vertexSet T :=
  mem_vertexSet.2 ⟨i, rfl⟩

theorem card_vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) k) : (vertexSet T).card = k + 1 := by
  rw [vertexSet, Finset.card_image_of_injective _ T.independent.injective, Finset.card_univ,
    Fintype.card_fin]

theorem affineIndependent_vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    AffineIndependent ℝ ((↑) : vertexSet T → Fin n → ℝ) :=
  T.independent.range.mono (subset_of_eq (coe_vertexSet T))

theorem convexHull_vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    convexHull ℝ (vertexSet T : Set (Fin n → ℝ)) = T.closedInterior := by
  rw [coe_vertexSet, Affine.Simplex.convexHull_eq_closedInterior]

theorem vertexSet_map (T : Affine.Simplex ℝ (Fin n → ℝ) k)
    (f : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ)) (hf : Function.Injective f) :
    (vertexSet (T.map f hf) : Set (Fin n → ℝ)) = f '' vertexSet T := by
  simp only [coe_vertexSet, Affine.Simplex.map_points, Set.range_comp]

theorem convex_closedInterior (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    Convex ℝ T.closedInterior := by
  rw [← convexHull_vertexSet]; exact convex_convexHull ℝ _

/-- An `n`-simplex of `ℝⁿ` has nonempty interior. -/
theorem interior_closedInterior_nonempty (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    (interior T.closedInterior).Nonempty := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior,
    (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top, affineSpan_convexHull,
    T.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
  simp

/-- The convex hull of at most `n` points of `ℝⁿ` has empty interior. -/
theorem interior_convexHull_eq_empty_of_card_le {s : Finset (Fin n → ℝ)} (hs : s.card ≤ n) :
    interior (convexHull ℝ (s : Set (Fin n → ℝ))) = ∅ := by
  classical
  rw [← Set.not_nonempty_iff_eq_empty,
    (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top, affineSpan_convexHull]
  intro htop
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp at htop
  · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by have := hne.card_pos; omega⟩
    have h1 := finrank_vectorSpan_image_finset_le ℝ (id : (Fin n → ℝ) → Fin n → ℝ) s
      (by simpa using hm)
    rw [Finset.image_id, ← direction_affineSpan, htop, AffineSubspace.direction_top,
      finrank_top, Module.finrank_fin_fun] at h1
    omega

/-- If two `n`-simplices with distinct vertex sets meet face to face, their interiors are
disjoint. -/
theorem disjoint_interior_of_inter_eq {T T' : Affine.Simplex ℝ (Fin n → ℝ) n}
    (h : T.closedInterior ∩ T'.closedInterior =
      convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T'))
    (hne : vertexSet T ≠ vertexSet T') :
    Disjoint (interior T.closedInterior) (interior T'.closedInterior) := by
  classical
  rw [Set.disjoint_iff_inter_eq_empty, ← interior_inter, h, ← Finset.coe_inter]
  apply interior_convexHull_eq_empty_of_card_le
  have hlt : (vertexSet T ∩ vertexSet T').card < (vertexSet T).card := by
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, ?_⟩)
    intro heq
    apply hne
    refine Finset.eq_of_subset_of_card_le (heq ▸ Finset.inter_subset_right) ?_
    rw [card_vertexSet, card_vertexSet]
  rw [card_vertexSet] at hlt
  omega

/-! ### The reference simplex and the affine map `F_T` -/

/-- The vertices `0, e₀, …, e_{n-1}` of the reference simplex. -/
def refPoints (n : ℕ) : Fin (n + 1) → Fin n → ℝ :=
  Fin.cons 0 fun i => Pi.single i 1

@[simp] theorem refPoints_zero : refPoints n 0 = 0 := rfl

@[simp] theorem refPoints_succ (i : Fin n) : refPoints n i.succ = Pi.single i 1 := rfl

theorem affineIndependent_refPoints (n : ℕ) : AffineIndependent ℝ (refPoints n) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin (n + 1))]
  have : (fun i : {x : Fin (n + 1) // x ≠ 0} => (refPoints n i -ᵥ refPoints n 0 : Fin n → ℝ)) =
      (fun j : Fin n => (Pi.single j (1 : ℝ) : Fin n → ℝ)) ∘ fun i => Fin.pred i.1 i.2 := by
    funext ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi
    simp
  rw [this]
  refine (Pi.linearIndependent_single_one (Fin n) ℝ).comp _ fun a b hab => ?_
  exact Subtype.ext ((Fin.pred_inj (ha := a.2) (hb := b.2)).1 hab)

/-- The reference simplex `T̂ = conv {0, e₀, …, e_{n-1}}`. -/
def refSimplex (n : ℕ) : Affine.Simplex ℝ (Fin n → ℝ) n :=
  ⟨refPoints n, affineIndependent_refPoints n⟩

@[simp] theorem refSimplex_points : (refSimplex n).points = refPoints n := rfl

theorem sum_smul_refPoints (w : Fin (n + 1) → ℝ) :
    ∑ i, w i • refPoints n i = fun k => w k.succ := by
  rw [Fin.sum_univ_succ]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- `T̂ = {x | x ≥ 0, ∑ xᵢ ≤ 1}`. -/
theorem mem_closedInterior_refSimplex {x : Fin n → ℝ} :
    x ∈ (refSimplex n).closedInterior ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  constructor
  · rintro ⟨w, hw1, hw, rfl⟩
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1, refSimplex_points,
      sum_smul_refPoints]
    rw [Fin.sum_univ_succ] at hw1
    exact ⟨fun i => (hw i.succ).1, by linarith [(hw 0).1]⟩
  · rintro ⟨h0, h1⟩
    have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => h0 i
    refine ⟨Fin.cons (1 - ∑ i, x i) x, by simp [Fin.sum_univ_succ], ?_, ?_⟩
    · refine Fin.cases ⟨by simp; linarith, by simp; linarith⟩ fun i => ?_
      simp only [Fin.cons_succ, Set.mem_Icc]
      exact ⟨h0 i, (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)).trans h1⟩
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simp [Fin.sum_univ_succ]),
        refSimplex_points, sum_smul_refPoints]
      rfl

end Feec.Mesh

namespace Affine.Simplex

open Feec.Mesh

variable {n : ℕ}

/-- The linear part `B_T` of the affine map `F_T : T̂ → T`: the matrix with columns
`pᵢ₊₁ - p₀`. -/
def linearPart (T : Affine.Simplex ℝ (Fin n → ℝ) n) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Fintype.linearCombination ℝ fun i => T.points i.succ - T.points 0

theorem linearPart_apply (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    T.linearPart x = ∑ i, x i • (T.points i.succ - T.points 0) := by
  simp [linearPart, Fintype.linearCombination_apply]

theorem linearPart_single (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin n) :
    T.linearPart (Pi.single i 1) = T.points i.succ - T.points 0 := by
  simp [linearPart]

theorem linearPart_injective (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    Function.Injective T.linearPart := by
  have hli : LinearIndependent ℝ fun i : Fin n => T.points i.succ - T.points 0 := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ T.points 0).1 T.independent
    exact h.comp (fun i : Fin n => ⟨i.succ, Fin.succ_ne_zero i⟩) fun a b hab => by
      simpa using congrArg Subtype.val hab
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [linearPart_apply] at hx
  funext i
  exact Fintype.linearIndependent_iff.1 hli x hx i

/-- `B_T` as a continuous linear equivalence of `ℝⁿ`. -/
def linearEquiv (T : Affine.Simplex ℝ (Fin n → ℝ) n) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (LinearEquiv.ofInjectiveEndo T.linearPart T.linearPart_injective).toContinuousLinearEquiv

@[simp] theorem linearEquiv_apply (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    T.linearEquiv x = T.linearPart x := rfl

/-- The affine map `F_T x̂ = B_T x̂ + p₀` sending the reference simplex onto `T`. -/
def refMap (T : Affine.Simplex ℝ (Fin n → ℝ) n) : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ) where
  toFun x := T.linearPart x + T.points 0
  linear := T.linearPart
  map_vadd' _ _ := by simp [add_assoc]

theorem refMap_apply (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    T.refMap x = T.linearPart x + T.points 0 := rfl

@[simp] theorem refMap_linear (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    T.refMap.linear = T.linearPart := rfl

theorem refMap_injective (T : Affine.Simplex ℝ (Fin n → ℝ) n) : Function.Injective T.refMap :=
  fun _ _ h => T.linearPart_injective (add_right_cancel h)

@[simp] theorem refMap_refPoints (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1)) :
    T.refMap (refPoints n i) = T.points i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [refMap_apply]
  · simp [refMap_apply, linearPart_single]

/-- Every `n`-simplex is the image `F_T(T̂)` of the reference simplex. -/
theorem map_refSimplex (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    (refSimplex n).map T.refMap T.refMap_injective = T :=
  Affine.Simplex.ext fun i => by simp

theorem closedInterior_eq_image_refMap (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    T.closedInterior = T.refMap '' (refSimplex n).closedInterior := by
  conv_lhs => rw [← T.map_refSimplex]
  exact Affine.Simplex.closedInterior_map _ _

/-- The barycentric coordinates of an `n`-simplex of `ℝⁿ`, as an affine basis. -/
def affineBasis (T : Affine.Simplex ℝ (Fin n → ℝ) n) : AffineBasis (Fin (n + 1)) ℝ (Fin n → ℝ) :=
  ⟨T.points, T.independent, by
    rw [T.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one]; simp⟩

@[simp] theorem coe_affineBasis (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ⇑T.affineBasis = T.points := rfl

@[simp] theorem coord_points_self (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1)) :
    T.affineBasis.coord i (T.points i) = 1 :=
  T.affineBasis.coord_apply_eq i

theorem coord_points_ne (T : Affine.Simplex ℝ (Fin n → ℝ) n) {i j : Fin (n + 1)} (h : i ≠ j) :
    T.affineBasis.coord i (T.points j) = 0 :=
  T.affineBasis.coord_apply_ne h

theorem mem_closedInterior_iff_coord_nonneg (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {x : Fin n → ℝ} : x ∈ T.closedInterior ↔ ∀ i, 0 ≤ T.affineBasis.coord i x := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior, ← coe_affineBasis,
    AffineBasis.convexHull_eq_nonneg_coord]; rfl

theorem interior_closedInterior_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    interior T.closedInterior = {x | ∀ i, 0 < T.affineBasis.coord i x} := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior, ← coe_affineBasis,
    AffineBasis.interior_convexHull]

end Affine.Simplex

namespace Feec.Mesh

variable {n k : ℕ}

/-- `h_T`: the diameter of the closed simplex `T`. -/
def diam (T : Affine.Simplex ℝ (Fin n → ℝ) k) : ℝ := Metric.diam T.closedInterior

theorem diam_nonneg (T : Affine.Simplex ℝ (Fin n → ℝ) k) : 0 ≤ diam T := Metric.diam_nonneg

/-! ### Simplicial meshes -/

/-- A conforming simplicial mesh of `closure domain ⊆ ℝⁿ`: a finite set of `n`-simplices whose
closed simplices cover `closure domain`, have pairwise disjoint interiors, and meet face to face
(the intersection of two closed simplices is the convex hull of their common vertices). Every
`n`-simplex of `ℝⁿ` has nonempty interior (`interior_closedInterior_nonempty`). -/
structure SimplicialMesh (n : ℕ) where
  /-- The `n`-simplices of the mesh. -/
  simplices : Finset (Affine.Simplex ℝ (Fin n → ℝ) n)
  /-- The meshed set `Ω`; the mesh covers its closure. -/
  domain : Set (Fin n → ℝ)
  biUnion_closedInterior : ⋃ T ∈ simplices, T.closedInterior = closure domain
  pairwise_disjoint_interior :
    (simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)).Pairwise fun T T' =>
      Disjoint (interior T.closedInterior) (interior T'.closedInterior)
  inter_closedInterior : ∀ T ∈ simplices, ∀ T' ∈ simplices,
    T.closedInterior ∩ T'.closedInterior =
      convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T')

namespace SimplicialMesh

variable (M : SimplicialMesh n)

/-- Build a mesh from a covering, face-to-face family of simplices with pairwise distinct vertex
sets: disjointness of interiors follows (`disjoint_interior_of_inter_eq`). -/
def ofConforming (simplices : Finset (Affine.Simplex ℝ (Fin n → ℝ) n))
    (domain : Set (Fin n → ℝ))
    (hcover : ⋃ T ∈ simplices, T.closedInterior = closure domain)
    (hconf : ∀ T ∈ simplices, ∀ T' ∈ simplices, T.closedInterior ∩ T'.closedInterior =
      convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T'))
    (hinj : Set.InjOn vertexSet (simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n))) :
    SimplicialMesh n where
  simplices := simplices
  domain := domain
  biUnion_closedInterior := hcover
  pairwise_disjoint_interior T hT T' hT' hne :=
    disjoint_interior_of_inter_eq (hconf T hT T' hT') fun h => hne (hinj hT hT' h)
  inter_closedInterior := hconf

theorem closedInterior_subset_closure {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) : T.closedInterior ⊆ closure M.domain :=
  M.biUnion_closedInterior ▸ Set.subset_biUnion_of_mem (u := fun T => T.closedInterior) hT

/-- Distinct simplices of a mesh have distinct vertex sets. -/
theorem vertexSet_injOn :
    Set.InjOn vertexSet (M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  intro T hT T' hT' h
  by_contra hne
  have hd : Disjoint (interior T.closedInterior) (interior T'.closedInterior) :=
    M.pairwise_disjoint_interior hT hT' hne
  rw [← convexHull_vertexSet T, ← convexHull_vertexSet T', h, disjoint_self,
    convexHull_vertexSet] at hd
  exact (interior_closedInterior_nonempty T').ne_empty (by simpa using hd)

/-- The mesh size `h = max_T h_T`. -/
def meshSize : ℝ := ⨆ T : M.simplices, diam (T : Affine.Simplex ℝ (Fin n → ℝ) n)

theorem diam_le_meshSize {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    diam T ≤ M.meshSize :=
  le_ciSup (f := fun T : M.simplices => diam (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (Set.finite_range _).bddAbove ⟨T, hT⟩

theorem meshSize_le {h : ℝ} (h0 : 0 ≤ h) (hT : ∀ T ∈ M.simplices, diam T ≤ h) :
    M.meshSize ≤ h :=
  Real.iSup_le (fun T => hT T T.2) h0

theorem meshSize_eq {h : ℝ} (hne : M.simplices.Nonempty) (hT : ∀ T ∈ M.simplices, diam T = h) :
    M.meshSize = h := by
  obtain ⟨T, hT0⟩ := hne
  refine le_antisymm (M.meshSize_le ?_ fun T hT' => (hT T hT').le) ?_
  · rw [← hT T hT0]; exact diam_nonneg T
  · rw [← hT T hT0]; exact M.diam_le_meshSize hT0

/-- `M₁` refines `M₂`: every simplex of `M₁` lies in a simplex of `M₂`. -/
def Refines (M₁ M₂ : SimplicialMesh n) : Prop :=
  ∀ T ∈ M₁.simplices, ∃ T' ∈ M₂.simplices, T.closedInterior ⊆ T'.closedInterior

/-! ### Faces -/

/-- The vertex sets of the `k`-faces of the mesh. -/
def faces (k : ℕ) : Set (Finset (Fin n → ℝ)) :=
  {F | F.card = k + 1 ∧ ∃ T ∈ M.simplices, F ⊆ vertexSet T}

/-- The vertex sets of the facets (`(n-1)`-faces) of the mesh. -/
def facets : Set (Finset (Fin n → ℝ)) :=
  {F | F.card = n ∧ ∃ T ∈ M.simplices, F ⊆ vertexSet T}

theorem facets_eq_faces [NeZero n] : M.facets = M.faces (n - 1) := by
  ext F
  simp only [facets, faces, Set.mem_ofPred_eq]
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))]

/-- The `n`-simplices of the mesh having `F` among their faces. -/
def cofaces (F : Finset (Fin n → ℝ)) : Finset (Affine.Simplex ℝ (Fin n → ℝ) n) := by
  classical exact M.simplices.filter fun T => F ⊆ vertexSet T

theorem mem_cofaces {F : Finset (Fin n → ℝ)} {T : Affine.Simplex ℝ (Fin n → ℝ) n} :
    T ∈ M.cofaces F ↔ T ∈ M.simplices ∧ F ⊆ vertexSet T := by
  simp [cofaces]

/-- An interior facet: a facet shared by exactly two `n`-simplices of the mesh, which induce
opposite orientations on it, i.e. whose opposite vertices lie strictly on opposite sides of
the hyperplane `aff F` (`isInteriorFacet_iff`: the orientation condition is automatic). -/
def IsInteriorFacet (F : Finset (Fin n → ℝ)) : Prop :=
  F ∈ M.facets ∧ (M.cofaces F).card = 2 ∧
    ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, T ≠ T' →
      ∀ a ∈ vertexSet T, a ∉ F → ∀ a' ∈ vertexSet T', a' ∉ F →
        (affineSpan ℝ (F : Set (Fin n → ℝ))).SOppSide a a'

/-- A boundary facet: a facet of exactly one `n`-simplex of the mesh, whose closed hull lies in
the topological boundary of `closure Ω = ⋃ T` (`isBoundaryFacet_iff`: this is automatic). -/
def IsBoundaryFacet (F : Finset (Fin n → ℝ)) : Prop :=
  F ∈ M.facets ∧ (M.cofaces F).card = 1 ∧
    convexHull ℝ (F : Set (Fin n → ℝ)) ⊆ frontier (closure M.domain)

/-! ### The simplicial complex of faces -/

/-- The Mathlib simplicial complex whose faces are all nonempty sets of vertices of a simplex of
the mesh. -/
def toSimplicialComplex : Geometry.SimplicialComplex ℝ (Fin n → ℝ) :=
  Geometry.SimplicialComplex.ofErase {F | ∃ T ∈ M.simplices, F ⊆ vertexSet T}
    (fun _ ⟨T, _, hF⟩ => (affineIndependent_vertexSet T).mono (Finset.coe_subset.2 hF))
    (fun _ _ hGF ⟨T, hT, hF⟩ => ⟨T, hT, fun _ hx => hF (hGF hx)⟩)
    (by
      classical
      rintro F ⟨T, hT, hF⟩ G ⟨T', hT', hG⟩ x ⟨hxF, hxG⟩
      have hxT : x ∈ convexHull ℝ ((vertexSet T ∩ vertexSet T' : Finset _) : Set (Fin n → ℝ)) := by
        rw [Finset.coe_inter, ← M.inter_closedInterior T hT T' hT', ← convexHull_vertexSet,
          ← convexHull_vertexSet]
        exact ⟨convexHull_mono (Finset.coe_subset.2 hF) hxF,
          convexHull_mono (Finset.coe_subset.2 hG) hxG⟩
      have h1 : x ∈ convexHull ℝ ((F ∩ (vertexSet T ∩ vertexSet T') : Finset _) :
          Set (Fin n → ℝ)) := by
        rw [Finset.coe_inter, (affineIndependent_vertexSet T).convexHull_inter hF
          Finset.inter_subset_left]
        exact ⟨hxF, hxT⟩
      have h2 : x ∈ convexHull ℝ ((G ∩ (F ∩ (vertexSet T ∩ vertexSet T')) : Finset _) :
          Set (Fin n → ℝ)) := by
        rw [Finset.coe_inter, (affineIndependent_vertexSet T').convexHull_inter hG
          ((Finset.inter_subset_right.trans Finset.inter_subset_right))]
        exact ⟨hxG, h1⟩
      refine convexHull_mono ?_ h2
      intro y hy
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hy ⊢
      exact ⟨hy.2.1, hy.1⟩)

theorem mem_toSimplicialComplex_faces {F : Finset (Fin n → ℝ)} :
    F ∈ M.toSimplicialComplex.faces ↔ F.Nonempty ∧ ∃ T ∈ M.simplices, F ⊆ vertexSet T := by
  simp [toSimplicialComplex, Finset.nonempty_iff_ne_empty, and_comm]

/-- The `k`-faces of the mesh are the faces of its simplicial complex with `k + 1` vertices. -/
theorem faces_eq (k : ℕ) :
    M.faces k = {F | F ∈ M.toSimplicialComplex.faces ∧ F.card = k + 1} := by
  ext F
  simp only [faces, mem_toSimplicialComplex_faces, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hc, h⟩; exact ⟨⟨Finset.card_pos.1 (by omega), h⟩, hc⟩
  · rintro ⟨⟨_, h⟩, hc⟩; exact ⟨hc, h⟩

/-- The underlying space of the simplicial complex of faces is `closure Ω`. -/
theorem space_toSimplicialComplex : M.toSimplicialComplex.space = closure M.domain := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨F, hF, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.1 hx
    obtain ⟨-, T, hT, hFT⟩ := M.mem_toSimplicialComplex_faces.1 hF
    exact M.closedInterior_subset_closure hT
      (convexHull_vertexSet T ▸ convexHull_mono (Finset.coe_subset.2 hFT) hx)
  · rw [← M.biUnion_closedInterior]
    refine Set.iUnion₂_subset fun T hT => ?_
    rw [← convexHull_vertexSet]
    refine Geometry.SimplicialComplex.convexHull_subset_space ?_
    exact M.mem_toSimplicialComplex_faces.2
      ⟨⟨T.points 0, points_mem_vertexSet T 0⟩, T, hT, subset_rfl⟩

/-! ### Images of meshes under affine equivalences -/

end SimplicialMesh

theorem injective_toAffineMap (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) :
    Function.Injective e.toAffineMap := by
  rw [AffineEquiv.coe_toAffineMap]; exact e.injective

/-- The image of a simplex under an affine equivalence. -/
def mapEquiv (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    Affine.Simplex ℝ (Fin n → ℝ) k :=
  T.map e.toAffineMap (injective_toAffineMap e)

@[simp] theorem mapEquiv_points (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (T : Affine.Simplex ℝ (Fin n → ℝ) k) (i : Fin (k + 1)) :
    (mapEquiv e T).points i = e (T.points i) := by
  simp [mapEquiv]

theorem closedInterior_mapEquiv (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    (mapEquiv e T).closedInterior = e '' T.closedInterior := by
  rw [mapEquiv, Affine.Simplex.closedInterior_map, AffineEquiv.coe_toAffineMap]

theorem vertexSet_mapEquiv (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    (vertexSet (mapEquiv e T) : Set (Fin n → ℝ)) = e '' vertexSet T := by
  rw [mapEquiv, vertexSet_map, AffineEquiv.coe_toAffineMap]

namespace SimplicialMesh

variable (M : SimplicialMesh n)


/-- The image of a mesh under an affine equivalence of `ℝⁿ`. -/
def map (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) : SimplicialMesh n := by
  classical
  exact ofConforming (M.simplices.image fun T => mapEquiv e T) (e '' M.domain)
    (by
      have hcl : closure (e '' M.domain) = e '' closure M.domain :=
        ((AffineEquiv.toContinuousAffineEquiv e).toHomeomorph.image_closure M.domain).symm
      rw [hcl, ← M.biUnion_closedInterior, Set.image_iUnion₂]
      ext x
      simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
      constructor
      · rintro ⟨_, ⟨T, hT, rfl⟩, hx⟩
        exact ⟨T, hT, by rwa [closedInterior_mapEquiv] at hx⟩
      · rintro ⟨T, hT, hx⟩
        exact ⟨_, ⟨T, hT, rfl⟩, by rwa [closedInterior_mapEquiv]⟩)
    (by
      simp only [Finset.mem_image]
      rintro _ ⟨T, hT, rfl⟩ _ ⟨T', hT', rfl⟩
      rw [closedInterior_mapEquiv, closedInterior_mapEquiv,
        ← Set.image_inter e.injective, M.inter_closedInterior T hT T' hT', vertexSet_mapEquiv,
        vertexSet_mapEquiv, ← Set.image_inter e.injective]
      have := AffineMap.image_convexHull e.toAffineMap
        ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T')
      rwa [AffineEquiv.coe_toAffineMap] at this)
    (by
      simp only [Finset.coe_image]
      rintro _ ⟨T, hT, rfl⟩ _ ⟨T', hT', rfl⟩ h
      have h' := congrArg (fun s : Finset (Fin n → ℝ) => (s : Set (Fin n → ℝ))) h
      simp only [vertexSet_mapEquiv] at h'
      rw [M.vertexSet_injOn hT hT' (Finset.coe_injective (e.injective.image_injective h'))])

theorem mem_map_simplices {e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} :
    T ∈ (M.map e).simplices ↔ ∃ T' ∈ M.simplices, mapEquiv e T' = T := by
  classical
  simp [map, ofConforming]

@[simp] theorem map_domain (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) :
    (M.map e).domain = e '' M.domain := rfl

end SimplicialMesh

/-! ### Facets: the two sides of an interior facet, and boundary facets -/

section Facets

variable {F : Finset (Fin n → ℝ)}

/-- A facet `F` of a simplex `T` misses exactly one vertex, the apex `T.points i`. -/
theorem exists_apex {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hF : F ⊆ vertexSet T)
    (hc : F.card = n) : ∃ i, T.points i ∉ F ∧ ∀ j, j ≠ i → T.points j ∈ F := by
  classical
  have hcard : (vertexSet T \ F).card = 1 := by
    rw [Finset.card_sdiff_of_subset hF, card_vertexSet, hc]; omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
  have haV : a ∈ vertexSet T \ F := ha ▸ Finset.mem_singleton_self a
  obtain ⟨i, rfl⟩ := mem_vertexSet.1 (Finset.mem_sdiff.1 haV).1
  refine ⟨i, (Finset.mem_sdiff.1 haV).2, fun j hj => ?_⟩
  by_contra hjF
  have : T.points j ∈ vertexSet T \ F := Finset.mem_sdiff.2 ⟨points_mem_vertexSet T j, hjF⟩
  rw [ha, Finset.mem_singleton] at this
  exact hj (T.independent.injective this)

/-- A barycentric coordinate vanishes on the hull of vertices not containing its vertex. -/
theorem coord_eq_zero_of_mem_convexHull (T : Affine.Simplex ℝ (Fin n → ℝ) n) {i : Fin (n + 1)}
    {S : Set (Fin n → ℝ)} (hS : S ⊆ Set.range T.points) (hi : T.points i ∉ S) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ S) : T.affineBasis.coord i x = 0 := by
  have hsub : S ⊆ T.affineBasis.coord i ⁻¹' {0} := by
    intro y hy
    obtain ⟨j, rfl⟩ := hS hy
    have hji : i ≠ j := fun h => hi (h ▸ hy)
    simpa using T.affineBasis.coord_apply_ne hji
  exact convexHull_min hsub ((convex_singleton (0 : ℝ)).affine_preimage _) hx

/-- The centroid of a finite set of points. -/
def centroid (F : Finset (Fin n → ℝ)) : Fin n → ℝ := (F.card : ℝ)⁻¹ • ∑ v ∈ F, v

theorem image_filter_points {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hF : F ⊆ vertexSet T) :
    (Finset.univ.filter fun j => T.points j ∈ F).image T.points = F := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun ⟨j, hj, h⟩ => h ▸ hj, fun hv => ?_⟩
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 (hF hv)
  exact ⟨j, hv, rfl⟩

/-- The barycentric coordinates of the centroid of `F ⊆ vertexSet T`. -/
theorem coord_centroid {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hF : F ⊆ vertexSet T)
    (hne : F.Nonempty) (j : Fin (n + 1)) :
    T.affineBasis.coord j (centroid F) = if T.points j ∈ F then (F.card : ℝ)⁻¹ else 0 := by
  classical
  set w : Fin (n + 1) → ℝ := fun j => if T.points j ∈ F then (F.card : ℝ)⁻¹ else 0 with hw
  have hcard : (Finset.univ.filter fun j => T.points j ∈ F).card = F.card := by
    conv_rhs => rw [← image_filter_points hF]
    rw [Finset.card_image_of_injective _ T.independent.injective]
  have hF0 : (F.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hw1 : ∑ j, w j = 1 := by
    simp only [hw]
    rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul, mul_inv_cancel₀ hF0]
  have hc : centroid F = Finset.univ.affineCombination ℝ T.affineBasis w := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1, centroid]
    simp only [hw, Affine.Simplex.coe_affineBasis, ite_smul, zero_smul]
    rw [← Finset.sum_filter, ← Finset.smul_sum]
    congr 1
    conv_lhs => rw [← image_filter_points hF]
    rw [Finset.sum_image fun a _ b _ h => T.independent.injective h]
  rw [hc, T.affineBasis.coord_apply_combination_of_mem (Finset.mem_univ j) hw1]

theorem eventually_pos_lineMap {u v : ℝ} (hu : 0 ≤ u) (huv : u = 0 → 0 < v) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < AffineMap.lineMap u v δ := by
  rcases hu.eq_or_lt with h | h
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [← h, AffineMap.lineMap_apply_ring']
    have := huv h.symm
    have : (0 : ℝ) < δ := hδ
    simp only [sub_zero, add_zero]
    positivity
  · have ht : Filter.Tendsto (fun δ : ℝ => AffineMap.lineMap u v δ) (𝓝 0) (𝓝 u) := by
      simp only [AffineMap.lineMap_apply_ring']
      have := ((continuous_id.mul continuous_const).add continuous_const).tendsto (0 : ℝ)
        (f := fun δ : ℝ => δ * (v - u) + u)
      simpa using this
    exact (ht.eventually (lt_mem_nhds h)).filter_mono nhdsWithin_le_nhds

namespace SimplicialMesh

variable (M : SimplicialMesh n)

/-- Two `n`-simplices sharing a facet `F`: the apex coordinate of the second is a multiple of
the apex coordinate of the first (both vanish exactly on `aff F`). -/
theorem coord_apex_eq_mul {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} (hF' : F ⊆ vertexSet T') {i i' : Fin (n + 1)} (hi : T.points i ∉ F)
    (hiF : ∀ j, j ≠ i → T.points j ∈ F) (hi' : T'.points i' ∉ F) (x : Fin n → ℝ) :
    T'.affineBasis.coord i' x =
      T'.affineBasis.coord i' (T.points i) * T.affineBasis.coord i x := by
  have h := AffineMap.ext_on (f := T'.affineBasis.coord i')
    (g := T'.affineBasis.coord i' (T.points i) • T.affineBasis.coord i)
    (s := Set.range T.points) (by rw [← Affine.Simplex.coe_affineBasis]; exact T.affineBasis.tot) ?_
  · have := congrArg (fun f : (Fin n → ℝ) →ᵃ[ℝ] ℝ => f x) h
    simpa [AffineMap.coe_smul] using this
  rintro _ ⟨j, rfl⟩
  by_cases hj : j = i
  · subst hj; simp [AffineMap.coe_smul]
  · have hjF := hiF j hj
    obtain ⟨j', hj'⟩ := mem_vertexSet.1 (hF' hjF)
    have hne : i' ≠ j' := by rintro rfl; exact hi' (hj' ▸ hjF)
    have h1 : T'.affineBasis.coord i' (T.points j) = 0 := by
      rw [← hj']; exact T'.coord_points_ne hne
    have h2 : T.affineBasis.coord i (T.points j) = 0 := T.coord_points_ne (Ne.symm hj)
    simp [h1, h2, AffineMap.coe_smul]

/-- **Opposite sides.** If two distinct `n`-simplices of a mesh share a facet `F`, the apex of the
second has negative barycentric coordinate with respect to the apex of the first. -/
theorem coord_apex_neg {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.cofaces F)
    (hT' : T' ∈ M.cofaces F) (hne : T ≠ T') (hc : F.card = n) {i i' : Fin (n + 1)}
    (hi : T.points i ∉ F) (hiF : ∀ j, j ≠ i → T.points j ∈ F) (hi' : T'.points i' ∉ F)
    (hiF' : ∀ j, j ≠ i' → T'.points j ∈ F) :
    T.affineBasis.coord i (T'.points i') < 0 := by
  rw [mem_cofaces] at hT hT'
  have hd : Disjoint (interior T.closedInterior) (interior T'.closedInterior) :=
    M.pairwise_disjoint_interior hT.1 hT'.1 hne
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exfalso
    obtain ⟨x, hx⟩ := interior_closedInterior_nonempty T
    obtain ⟨y, hy⟩ := interior_closedInterior_nonempty T'
    exact Set.disjoint_left.1 hd hx (Subsingleton.elim y x ▸ hy)
  have hFne : F.Nonempty := Finset.card_pos.1 (by omega)
  have hprop := coord_apex_eq_mul hT'.2 hi hiF hi'
  have hprop' := coord_apex_eq_mul hT.2 hi' hiF' hi
  -- the apex coordinate of `T'` at its own apex is `1`
  have h1 : T.affineBasis.coord i (T'.points i') ≠ 0 := by
    intro h0
    have := hprop (T'.points i')
    rw [h0, mul_zero, Affine.Simplex.coord_points_self] at this
    exact one_ne_zero this
  have hcF : (0 : ℝ) < (F.card : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hFne.card_pos)
  refine lt_of_le_of_ne (not_lt.1 fun hpos => ?_) h1
  -- otherwise points near the centroid of `F` towards `T'.points i'` lie in both interiors
  have hqT := coord_centroid hT.2 hFne
  have hqT' := coord_centroid hT'.2 hFne
  set q := centroid F
  set a' := T'.points i'
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ j, 0 < T.affineBasis.coord j (AffineMap.lineMap q a' δ)) ∧
      (∀ j, 0 < T'.affineBasis.coord j (AffineMap.lineMap q a' δ)) := by
    refine (Filter.eventually_all.2 fun j => ?_).and (Filter.eventually_all.2 fun j => ?_)
    · refine (eventually_pos_lineMap (u := T.affineBasis.coord j q)
        (v := T.affineBasis.coord j a') ?_ fun h0 => ?_).mono fun δ h => by
          rwa [AffineMap.apply_lineMap]
      · rw [hqT j]; split_ifs; exacts [hcF.le, le_rfl]
      · have hj : j = i := by
          by_contra hj; rw [hqT j] at h0; simp only [hiF j hj, ite_true] at h0; exact hcF.ne' h0
        subst hj; exact hpos
    · refine (eventually_pos_lineMap (u := T'.affineBasis.coord j q)
        (v := T'.affineBasis.coord j a') ?_ fun h0 => ?_).mono fun δ h => by
          rwa [AffineMap.apply_lineMap]
      · rw [hqT' j]; split_ifs; exacts [hcF.le, le_rfl]
      · have hj : j = i' := by
          by_contra hj; rw [hqT' j] at h0; simp only [hiF' j hj, ite_true] at h0; exact hcF.ne' h0
        subst hj; simp [a', Affine.Simplex.coord_points_self]
  obtain ⟨δ, hδ, hδ'⟩ := hev.exists
  rw [← Set.mem_ofPred_eq (p := fun x => ∀ j, 0 < T.affineBasis.coord j x),
    ← Affine.Simplex.interior_closedInterior_eq] at hδ
  rw [← Set.mem_ofPred_eq (p := fun x => ∀ j, 0 < T'.affineBasis.coord j x),
    ← Affine.Simplex.interior_closedInterior_eq] at hδ'
  exact Set.disjoint_left.1 hd hδ hδ'

theorem affineSpan_eq_faceOpposite [NeZero n] {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hF : F ⊆ vertexSet T) {i : Fin (n + 1)} (hi : T.points i ∉ F)
    (hiF : ∀ j, j ≠ i → T.points j ∈ F) :
    (F : Set (Fin n → ℝ)) = Set.range (T.faceOpposite i).points := by
  rw [Affine.Simplex.range_faceOpposite_points]
  ext v
  constructor
  · intro hv
    obtain ⟨j, rfl⟩ := mem_vertexSet.1 (hF hv)
    exact ⟨j, fun h => hi (by rw [Set.mem_singleton_iff] at h; exact h ▸ hv), rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact hiF j hj

/-- **Interior facets are oriented oppositely.** Two distinct `n`-simplices of a mesh sharing a
facet `F` lie strictly on opposite sides of the hyperplane `aff F`; equivalently they induce
opposite orientations on `F`. -/
theorem sOppSide_of_mem_cofaces {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} (hF : F ∈ M.facets)
    (hT : T ∈ M.cofaces F) (hT' : T' ∈ M.cofaces F) (hne : T ≠ T') {a a' : Fin n → ℝ}
    (ha : a ∈ vertexSet T) (haF : a ∉ F) (ha' : a' ∈ vertexSet T') (haF' : a' ∉ F) :
    (affineSpan ℝ (F : Set (Fin n → ℝ))).SOppSide a a' := by
  have hTF := (M.mem_cofaces.1 hT).2
  have hTF' := (M.mem_cofaces.1 hT').2
  obtain ⟨i, hi, hiF⟩ := exists_apex hTF hF.1
  obtain ⟨i', hi', hiF'⟩ := exists_apex hTF' hF.1
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 ha
  obtain ⟨j', rfl⟩ := mem_vertexSet.1 ha'
  obtain rfl : j = i := by_contra fun h => haF (hiF j h)
  obtain rfl : j' = i' := by_contra fun h => haF' (hiF' j' h)
  have hneg := M.coord_apex_neg hT hT' hne hF.1 hi hiF hi' hiF'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exfalso
    have hd := M.pairwise_disjoint_interior (M.mem_cofaces.1 hT).1 (M.mem_cofaces.1 hT').1 hne
    obtain ⟨x, hx⟩ := interior_closedInterior_nonempty T
    obtain ⟨y, hy⟩ := interior_closedInterior_nonempty T'
    exact Set.disjoint_left.1 hd hx (Subsingleton.elim y x ▸ hy)
  have : NeZero n := ⟨hn.ne'⟩
  rw [affineSpan_eq_faceOpposite hTF hi hiF]
  have h := T.sOppSide_affineSpan_faceOpposite_point_left_iff
    (T.affineBasis.sum_coord_apply_eq_one (T'.points j')) (i := j)
  have e : Finset.univ.affineCombination ℝ T.points
      (fun j => T.affineBasis.coord j (T'.points j')) = T'.points j' :=
    T.affineBasis.affineCombination_coord_eq_self _
  rw [e] at h
  exact h.2 hneg

/-- A facet of a mesh lies in at most two `n`-simplices. -/
theorem card_cofaces_le_two (hF : F ∈ M.facets) : (M.cofaces F).card ≤ 2 := by
  by_contra h
  obtain ⟨T₁, h₁, T₂, h₂, T₃, h₃, h12, h13, h23⟩ := Finset.two_lt_card.1 (not_le.1 h)
  have hF₁ := (M.mem_cofaces.1 h₁).2
  have hF₂ := (M.mem_cofaces.1 h₂).2
  have hF₃ := (M.mem_cofaces.1 h₃).2
  obtain ⟨i₁, hi₁, hiF₁⟩ := exists_apex hF₁ hF.1
  obtain ⟨i₂, hi₂, hiF₂⟩ := exists_apex hF₂ hF.1
  obtain ⟨i₃, hi₃, hiF₃⟩ := exists_apex hF₃ hF.1
  have a := M.coord_apex_neg h₂ h₃ h23 hF.1 hi₂ hiF₂ hi₃ hiF₃
  have b := M.coord_apex_neg h₂ h₁ (Ne.symm h12) hF.1 hi₂ hiF₂ hi₁ hiF₁
  have c := M.coord_apex_neg h₁ h₃ h13 hF.1 hi₁ hiF₁ hi₃ hiF₃
  rw [coord_apex_eq_mul hF₂ hi₁ hiF₁ hi₂] at a
  nlinarith

theorem one_le_card_cofaces (hF : F ∈ M.facets) : 1 ≤ (M.cofaces F).card := by
  obtain ⟨T, hT, hFT⟩ := hF.2
  exact Finset.card_pos.2 ⟨T, M.mem_cofaces.2 ⟨hT, hFT⟩⟩

/-- A facet with two `n`-simplices is an interior facet: the orientation condition holds. -/
theorem isInteriorFacet_iff :
    M.IsInteriorFacet F ↔ F ∈ M.facets ∧ (M.cofaces F).card = 2 :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun _ hT _ hT' hne _ ha haF _ ha' haF' =>
    M.sOppSide_of_mem_cofaces h.1 hT hT' hne ha haF ha' haF'⟩⟩

/-- Points of the relative interior of a facet of exactly one `n`-simplex lie in the topological
boundary of the mesh. -/
theorem mem_frontier_of_card_cofaces_eq_one {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : M.cofaces F = {T}) {i : Fin (n + 1)} (hi : T.points i ∉ F)
    (hiF : ∀ j, j ≠ i → T.points j ∈ F) {y : Fin n → ℝ}
    (hyi : T.affineBasis.coord i y = 0) (hy : ∀ j, j ≠ i → 0 < T.affineBasis.coord j y) :
    y ∈ frontier (closure M.domain) := by
  classical
  have hTm : T ∈ M.cofaces F := hT ▸ Finset.mem_singleton_self T
  have hTF := (M.mem_cofaces.1 hTm).2
  have hyT : y ∈ T.closedInterior := by
    rw [T.mem_closedInterior_iff_coord_nonneg]
    intro j
    by_cases hj : j = i
    · rw [hj, hyi]
    · exact (hy j hj).le
  have hyU : y ∈ closure M.domain := M.closedInterior_subset_closure (M.mem_cofaces.1 hTm).1 hyT
  refine ⟨subset_closure hyU, fun hint => ?_⟩
  -- move from `y` away from the apex
  set p := AffineMap.lineMap (T.points i) y (2 : ℝ)
  set z : ℝ → Fin n → ℝ := fun δ => AffineMap.lineMap y p δ
  have hz : Filter.Tendsto z (𝓝[>] 0) (𝓝 y) := by
    have hc : Continuous fun t : ℝ => AffineMap.lineMap y p t := AffineMap.lineMap_continuous
    have := hc.tendsto 0
    simp only [AffineMap.lineMap_apply_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hzi : ∀ δ : ℝ, 0 < δ → T.affineBasis.coord i (z δ) < 0 := by
    intro δ hδ
    simp only [z, p, AffineMap.apply_lineMap, hyi, Affine.Simplex.coord_points_self,
      AffineMap.lineMap_apply_ring']
    nlinarith
  have hzU : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ T'' ∈ M.simplices, z δ ∈ T''.closedInterior := by
    filter_upwards [hz (isOpen_interior.mem_nhds hint)] with δ hδ
    have := interior_subset hδ
    rw [← M.biUnion_closedInterior, Set.mem_iUnion₂] at this
    obtain ⟨T'', hT'', h⟩ := this
    exact ⟨T'', hT'', h⟩
  -- pigeonhole over the finitely many simplices
  obtain ⟨T'', hT'', hfreq⟩ : ∃ T'' ∈ M.simplices, ∃ᶠ δ in 𝓝[>] (0 : ℝ),
      z δ ∈ T''.closedInterior := by
    by_contra hcon
    simp only [not_exists, not_and, Filter.not_frequently] at hcon
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ T'' ∈ M.simplices, z δ ∉ T''.closedInterior :=
      (Filter.eventually_all_finset _).2 fun T'' hT'' => hcon T'' hT''
    obtain ⟨δ, ⟨T'', hT'', h⟩, h'⟩ := (hzU.and h1).exists
    exact h' T'' hT'' h
  have hyT'' : y ∈ T''.closedInterior :=
    T''.isClosed_closedInterior.mem_of_frequently_of_tendsto hfreq hz
  have hne : T'' ≠ T := by
    obtain ⟨δ, h1, h2⟩ := (hfreq.and_eventually self_mem_nhdsWithin).exists
    rintro rfl
    exact absurd ((T''.mem_closedInterior_iff_coord_nonneg.1 h1) i) (not_le.2 (hzi δ h2))
  -- `T''` contains `F`
  have hFT'' : F ⊆ vertexSet T'' := by
    intro v hv
    by_contra hvT''
    obtain ⟨j, rfl⟩ := mem_vertexSet.1 (hTF hv)
    have hj : j ≠ i := fun h => hi (h ▸ hv)
    have hmem : y ∈ convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T'') := by
      rw [← M.inter_closedInterior T (M.mem_cofaces.1 hTm).1 T'' hT'']; exact ⟨hyT, hyT''⟩
    have := coord_eq_zero_of_mem_convexHull T (i := j)
      (Set.inter_subset_left.trans (coe_vertexSet T).subset) (fun h => hvT'' h.2) hmem
    exact (hy j hj).ne' this
  have : T'' ∈ M.cofaces F := M.mem_cofaces.2 ⟨hT'', hFT''⟩
  rw [hT, Finset.mem_singleton] at this
  exact hne this

/-- A facet of exactly one `n`-simplex is a boundary facet: its closed hull lies in the
topological boundary of `closure Ω`. -/
theorem isBoundaryFacet_iff :
    M.IsBoundaryFacet F ↔ F ∈ M.facets ∧ (M.cofaces F).card = 1 := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨hF, h1⟩ => ⟨hF, h1, ?_⟩⟩
  obtain ⟨T, hT⟩ := Finset.card_eq_one.1 h1
  have hTm : T ∈ M.cofaces F := hT ▸ Finset.mem_singleton_self T
  have hTF := (M.mem_cofaces.1 hTm).2
  obtain ⟨i, hi, hiF⟩ := exists_apex hTF hF.1
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · simp
  intro x hx
  have hxi : T.affineBasis.coord i x = 0 :=
    coord_eq_zero_of_mem_convexHull T (by rw [← coe_vertexSet]; exact Finset.coe_subset.2 hTF)
      hi hx
  have hxT : x ∈ T.closedInterior :=
    convexHull_vertexSet T ▸ convexHull_mono (Finset.coe_subset.2 hTF) hx
  have hqT := coord_centroid hTF hFne
  have hcF : (0 : ℝ) < (F.card : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hFne.card_pos)
  set x' : ℝ → Fin n → ℝ := fun t => AffineMap.lineMap x (centroid F) t
  have hx' : Filter.Tendsto x' (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous fun t : ℝ => AffineMap.lineMap x (centroid F) t :=
      AffineMap.lineMap_continuous
    have := hc.tendsto 0
    simp only [AffineMap.lineMap_apply_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine isClosed_frontier.mem_of_tendsto hx' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  refine M.mem_frontier_of_card_cofaces_eq_one hT hi hiF ?_ fun j hj => ?_
  · simp [x', AffineMap.apply_lineMap, hxi, hqT i, hi]
  · simp only [x', AffineMap.apply_lineMap, hqT j, hiF j hj, ite_true, AffineMap.lineMap_apply_ring']
    have h0 := (T.mem_closedInterior_iff_coord_nonneg.1 hxT) j
    nlinarith [ht.1, ht.2]

/-- Every facet of a mesh is an interior facet or a boundary facet. -/
theorem isInteriorFacet_or_isBoundaryFacet (hF : F ∈ M.facets) :
    M.IsInteriorFacet F ∨ M.IsBoundaryFacet F := by
  rw [isInteriorFacet_iff, isBoundaryFacet_iff]
  have h1 := M.one_le_card_cofaces hF
  have h2 := M.card_cofaces_le_two hF
  rcases (by omega : (M.cofaces F).card = 2 ∨ (M.cofaces F).card = 1) with h | h
  · exact Or.inl ⟨hF, h⟩
  · exact Or.inr ⟨hF, h⟩

end SimplicialMesh

end Facets

end Feec.Mesh
