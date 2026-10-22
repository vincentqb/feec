module

public import Feec.FiniteElement.PolyElement

/-!
# Higher-order finite element complexes on meshes

For an admissible sequence `S` (`Feec.FiniteElement.PolySeq`) the element family
`Feec.FiniteElement.polyElement n S` gives, on every conforming simplicial mesh `M` of an open
`Ω ⊆ ℝⁿ`, the global spaces of piecewise `P_{r_k}Λᵏ` / `P_{r_k}⁻Λᵏ` forms with continuous
tangential traces, a subcomplex of `HΛ(Ω)` and, with vanishing boundary degrees of freedom, of
`H̊Λ(Ω)` for strictly star-shaped `Ω`; this file names the classical sequences, computes the
dimensions, and specializes to the Freudenthal meshes of cubes.

* Named sequences: `PolySeq.trimmed r` (`P_r⁻Λ⁰ → ⋯ → P_r⁻Λⁿ`), `PolySeq.full r`
  (`P_rΛ⁰ → P_{r-1}Λ¹ → ⋯`: Lagrange `P_r`, Nédélec of the second kind, BDM), and the two rows of
  Tables 5.1 and 6.1 of [QuennevilleBelair2015] (§5.3, §6.3): `PolySeq.lowestOrder`
  (`P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ² → P₁⁻Λ³`) and `PolySeq.lagrangeP2` (`P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³`).
* Dimensions: `PolySeq.finrank_globalSpace`: `Σ_m #{m-faces} · dim(test forms on m-faces)`;
  `PolySeq.finrank_globalSpace₀`, `PolySeq.finrank_V₀`: the same with the faces not contained in
  a boundary facet.
* Subcomplexes: `PolySeq.subcomplex`, `PolySeq.subcomplexMin`, and on the level-`N` Freudenthal
  mesh of a cube `PolySeq.freudenthalSubcomplexMin`.
* **Nonzero interior spaces**: a face of `M` whose convex hull meets `Ω` is not contained in a
  boundary facet (`LocalElement.not_isBoundaryDof_of_mem_convexHull`), and on the Freudenthal
  meshes the faces of `b + (s/N) K_id` containing the diagonal from `b` to `b + (s/N)(1, …, 1)`
  are such faces (`exists_meshFace_freudenthalMesh`). Hence `V̊ₕᵏ ≠ 0` for `1 ≤ k ≤ n` for every
  admissible sequence (`PolySeq.finrank_V₀_freudenthalMesh_pos_of_one_le`) and for the Whitney
  forms (`finrank_whitney_V₀_freudenthalMesh_pos`), and for `k = 0` when `r₀ ≥ 2`
  (`PolySeq.finrank_V₀_freudenthalMesh_pos_zero`), on every level `N ≥ 1`. In particular the
  interior spaces of the second row of Tables 5.1/6.1 on the level-`(N+1)` Freudenthal mesh of
  `(0, ½)³` are nonzero in every degree (`PolySeq.lagrangeP2_V₀_ne_bot`). For `k = 0` and
  `r₀ = 1` an interior vertex is needed: on every level `N ≥ 2` the lattice point
  `b + (s/N)(1, …, 1)` is one (`exists_vertex_freudenthalMesh`), so `V̊ₕᵏ ≠ 0` in every degree
  for every admissible sequence (`PolySeq.finrank_V₀_freudenthalMesh_pos_of_two_le`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (assembly, dimension counts, Thms 4.9, 4.13)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Table 5.1; §6.3, Table 6.1
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh Feec.Domain

variable {n : ℕ}

/-! ### Named admissible sequences -/

namespace PolySeq

/-- The trimmed sequence `P_r⁻Λ⁰ → P_r⁻Λ¹ → ⋯ → P_r⁻Λⁿ` (`r ≥ 1`; `r = 1`: the Whitney forms). -/
def trimmed (r : ℕ) (hr : 1 ≤ r) : PolySeq where
  kind _ := .trimmed
  deg _ := r
  one_le_deg _ := hr
  transition _ := Or.inl ⟨rfl, rfl⟩

/-- The full sequence `P_rΛ⁰ → P_{r-1}Λ¹ → ⋯ → P_{r-k}Λᵏ → ⋯` (Lagrange `P_r`, Nédélec edge
elements of the second kind `P_{r-1}Λ¹`, Brezzi–Douglas–Marini `P_{r-2}Λ²` in `ℝ³`), continued by
`P_1⁻Λᵏ` in the degrees `k ≥ r` (so for `r ≥ n` it is `P_{r-k}Λᵏ` in every degree `k ≤ n`, with
`P_0Λⁿ = P_1⁻Λⁿ`). -/
def full (r : ℕ) : PolySeq where
  kind k := if k < r then .full else .trimmed
  deg k := if k < r then r - k else 1
  one_le_deg k := by split_ifs <;> omega
  transition k := by
    by_cases h1 : k + 1 < r
    · simp only [h1, show k < r by omega, ↓reduceIte]
      exact Or.inr ⟨rfl, by omega⟩
    · by_cases h2 : k < r
      · simp only [h1, h2, ↓reduceIte]
        exact Or.inl ⟨rfl, by omega⟩
      · simp only [h1, h2, ↓reduceIte]
        exact Or.inl ⟨rfl, rfl⟩

/-- **The first row of Tables 5.1 and 6.1** of [QuennevilleBelair2015] (§5.3, §6.3), in `ℝ³`:
`P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ² → P₁⁻Λ³`, i.e. Lagrange `P₁`, the lowest-order Nédélec `H(curl)`
elements of the first kind, the lowest-order Raviart–Thomas elements, and piecewise
constants (the Whitney forms, with moment degrees of freedom). -/
def lowestOrder : PolySeq where
  kind k := if k = 0 then .full else .trimmed
  deg _ := 1
  one_le_deg _ := le_rfl
  transition _ := Or.inl ⟨by simp, rfl⟩

/-- **The second row of Tables 5.1 and 6.1** of [QuennevilleBelair2015] (§5.3, §6.3), in `ℝ³`:
`P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` (with `P₀Λ³ = P₁⁻Λ³`), i.e. Lagrange `P₂`, the second-lowest-order
Nédélec `H(curl)` elements of the first kind, the lowest-order Brezzi–Douglas–Marini elements
`BDM₁`, and piecewise constants. -/
def lagrangeP2 : PolySeq where
  kind k := if k = 0 ∨ k = 2 then .full else .trimmed
  deg k := if k ≤ 1 then 2 else 1
  one_le_deg k := by split_ifs <;> omega
  transition k := by
    rcases k with _ | _ | _ | k
    · exact Or.inl ⟨by simp, rfl⟩
    · exact Or.inr ⟨by simp, rfl⟩
    · exact Or.inl ⟨by simp, rfl⟩
    · exact Or.inl ⟨by simp, by simp⟩

@[simp] theorem lagrangeP2_kind_zero : lagrangeP2.kind 0 = .full := rfl
@[simp] theorem lagrangeP2_kind_one : lagrangeP2.kind 1 = .trimmed := rfl
@[simp] theorem lagrangeP2_kind_two : lagrangeP2.kind 2 = .full := rfl
@[simp] theorem lagrangeP2_kind_three : lagrangeP2.kind 3 = .trimmed := rfl
@[simp] theorem lagrangeP2_deg_zero : lagrangeP2.deg 0 = 2 := rfl
@[simp] theorem lagrangeP2_deg_one : lagrangeP2.deg 1 = 2 := rfl
@[simp] theorem lagrangeP2_deg_two : lagrangeP2.deg 2 = 1 := rfl
@[simp] theorem lagrangeP2_deg_three : lagrangeP2.deg 3 = 1 := rfl

/-! ### Counting the degrees of freedom on a set of faces -/

variable (S : PolySeq)

/-- The degrees of freedom of a set `F` of faces (of at most `n + 1` vertices):
`Σ_{m ≤ n} #{m-faces in F} · dim(test forms on m-faces)`. -/
theorem card_sigma_dofIdx_eq_sum (F : Finset (Finset (Fin n → ℝ)))
    (hF : ∀ g ∈ F, #g ≤ n + 1) (k : ℕ) :
    Fintype.card (Σ g : F, S.DofIdx (g : Finset (Fin n → ℝ)) k) =
      ∑ m ∈ range (n + 1), #(F.filter fun g => #g = m + 1) *
        Module.finrank ℝ (S.test k m) := by
  classical
  rw [Fintype.card_sigma]
  simp only [card_dofIdx]
  rw [Finset.sum_coe_sort F (fun g => if g.Nonempty then
    Module.finrank ℝ (S.test k (#g - 1)) else 0), ← sum_filter]
  rw [← sum_fiberwise_of_maps_to (s := F.filter fun g => g.Nonempty) (t := range (n + 1))
    (g := fun g => #g - 1) (fun g hg => by
      have h1 := hF g (mem_filter.1 hg).1
      have h2 := card_pos.2 (mem_filter.1 hg).2
      simp only [Finset.mem_range]; omega)]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_congr rfl fun g hg => by rw [(mem_filter.1 hg).2], sum_const, smul_eq_mul,
    filter_filter]
  congr 2
  refine filter_congr fun g _ => ?_
  rw [← card_pos]
  omega

end PolySeq

/-! ### The global spaces on a mesh -/

theorem card_le_of_mem_meshFaces (M : SimplicialMesh n) {g : Finset (Fin n → ℝ)}
    (hg : g ∈ LocalElement.meshFaces M) : #g ≤ n + 1 := by
  obtain ⟨T, -, hgT⟩ := (LocalElement.mem_meshFaces M).1 hg
  exact (Finset.card_le_card hgT).trans (card_vertexSet T).le

namespace PolySeq

variable (S : PolySeq) (M : SimplicialMesh n)

theorem card_globalDofIdx (k : ℕ) :
    Fintype.card ((polyElement n S).GlobalDofIdx M k) =
      ∑ m ∈ range (n + 1), (M.faces m).ncard * Module.finrank ℝ (S.test k m) := by
  classical
  refine (S.card_sigma_dofIdx_eq_sum _ (fun g hg => card_le_of_mem_meshFaces M hg) k).trans ?_
  refine sum_congr rfl fun m _ => ?_
  rw [← coe_filter_meshFaces M m, Set.ncard_coe_finset]

/-- **`dim Λ_hᵏ(M) = Σ_{m ≤ n} #{m-faces of M} · dim(test forms on m-faces)`** for the
global `P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`) space ([AFW2006], Thms 4.9, 4.13 and §5.1). -/
theorem finrank_globalSpace (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).globalSpace M k) =
      ∑ m ∈ range (n + 1), (M.faces m).ncard * Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_globalSpace, card_globalDofIdx]

/-- The faces of `M` not contained in a boundary facet. -/
def interiorFaces (M : SimplicialMesh n) : Finset (Finset (Fin n → ℝ)) := by
  classical
  exact (LocalElement.meshFaces M).filter fun g => ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F

theorem mem_interiorFaces {g : Finset (Fin n → ℝ)} :
    g ∈ interiorFaces M ↔
      g ∈ LocalElement.meshFaces M ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F := by
  classical
  unfold interiorFaces; exact mem_filter

theorem card_interiorDofIdx (k : ℕ) :
    Fintype.card ((polyElement n S).InteriorDofIdx M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  classical
  have e : (polyElement n S).InteriorDofIdx M k ≃
      Σ g : interiorFaces M, S.DofIdx (g : Finset (Fin n → ℝ)) k :=
    { toFun := fun p => ⟨⟨p.1.1.1, (mem_interiorFaces M).2 ⟨p.1.1.2, p.2⟩⟩, p.1.2⟩
      invFun := fun q => ⟨⟨⟨q.1.1, ((mem_interiorFaces M).1 q.1.2).1⟩, q.2⟩,
        ((mem_interiorFaces M).1 q.1.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, S.card_sigma_dofIdx_eq_sum _ (fun g hg => card_le_of_mem_meshFaces M
    ((mem_interiorFaces M).1 hg).1) k]
  refine sum_congr rfl fun m _ => ?_
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext g
  simp only [coe_filter, mem_interiorFaces, LocalElement.mem_meshFaces,
    SimplicialMesh.faces, Set.mem_ofPred_eq]
  tauto

/-- **`dim Λ̊_hᵏ(M) = Σ_{m ≤ n} #{m-faces not in a boundary facet} · dim(test forms)`** for the
global spaces with vanishing boundary degrees of freedom. -/
theorem finrank_globalSpace₀ (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).globalSpace₀ M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_globalSpace₀, card_interiorDofIdx]

theorem finrank_V₀ (hΩ : IsOpen M.domain) (k : ℕ) :
    Module.finrank ℝ ((polyElement n S).V₀ M k) =
      ∑ m ∈ range (n + 1), {g | g ∈ M.faces m ∧ ¬ ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F}.ncard *
        Module.finrank ℝ (S.test k m) := by
  rw [LocalElement.finrank_V₀ _ M hΩ, card_interiorDofIdx]

/-- `dim` of the test forms, in closed form ([AFW2006], Thms 4.9, 4.13). -/
theorem finrank_test (k m : ℕ) :
    Module.finrank ℝ (S.test k m) = (S.kind k).testDim (S.deg k) k m :=
  PolyKind.finrank_test _ (S.one_le_deg k) k m

/-- **The global space is the space of piecewise `P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`) forms with
continuous tangential traces** (for meshes with facet-connected face stars; [AFW2006], §5.1,
[AFW2010], §5.2). -/
theorem mem_globalSpace_iff (hM : LocalElement.FacetConnected M) {k : ℕ}
    {u : (polyElement n S).Piecewise M k} :
    u ∈ (polyElement n S).globalSpace M k ↔ ∀ F ∈ M.facets, ∀ T T' : M.simplices,
      F ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) →
        F ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) →
          ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
            TangentialTraceEq F k ((u T : FormField n) x) ((u T' : FormField n) x) :=
  (polyElement n S).mem_globalSpace_iff M hM (inferInstanceAs (IsEmpty (S.DofIdx ∅ k)))

/-! ### The finite element subcomplexes -/

/-- **The finite element subcomplex** `Vₕ ⊆ HΛ(Ω)` of the admissible sequence `S` on a conforming
mesh of an open `Ω ⊆ ℝⁿ`. -/
def subcomplex [NeZero n] (hΩ : IsOpen M.domain) :
    ((deRham ℝ n).maximalComplex hΩ).Subcomplex :=
  (polyElement n S).subcomplex M hΩ

/-- **The finite element subcomplex with vanishing boundary degrees of freedom**
`V̊ₕ ⊆ H̊Λ(Ω)`, for `Ω` strictly star-shaped with respect to `x₀` (e.g. convex). -/
def subcomplexMin [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    ((deRham ℝ n).minimalComplex hΩ).Subcomplex :=
  (polyElement n S).subcomplexMin M hΩ x₀ hstar

/-- **The finite element subcomplex with vanishing boundary degrees of freedom on the level-`N`
Freudenthal mesh of a cube**, a subcomplex of `H̊Λ` of the cube. -/
def freudenthalSubcomplexMin [NeZero n] (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ)
    [NeZero N] :
    ((deRham ℝ n).minimalComplex (isOpen_freudenthalMesh_domain b s hs N)).Subcomplex :=
  S.subcomplexMin (freudenthalMesh b s hs N) (isOpen_freudenthalMesh_domain b s hs N) _
    (add_smul_sub_mem_of_convex (isOpen_freudenthalMesh_domain b s hs N)
      (convex_freudenthalMesh_domain b s hs N) (center_mem_freudenthalMesh_domain b s hs N))

end PolySeq

/-! ### Nonzero spaces with vanishing boundary degrees of freedom -/

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n)

/-- A face whose convex hull meets the (open) domain carries **interior degrees of freedom**: it
is not contained in a boundary facet (boundary facets lie in `∂Ω`). -/
theorem not_isBoundaryDof_of_mem_convexHull (hΩ : IsOpen M.domain) {k : ℕ}
    (p : E.GlobalDofIdx M k) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ ((p.1 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (hxΩ : x ∈ M.domain) : ¬ E.IsBoundaryDof M p := by
  rintro ⟨F, hF, hpF⟩
  have h := hF.2.2 (convexHull_mono (Finset.coe_subset.2 hpF) hx)
  exact h.2 (interior_mono subset_closure (hΩ.interior_eq.symm ▸ hxΩ))

/-- **`V̊ₕᵏ ≠ 0`** as soon as some face of `M` whose convex hull meets `Ω` carries a degree of
freedom of degree `k`. -/
theorem finrank_V₀_pos (hΩ : IsOpen M.domain) {k : ℕ} {g : Finset (Fin n → ℝ)}
    (hg : g ∈ meshFaces M) (i : E.DofIdx g k) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (g : Set (Fin n → ℝ))) (hxΩ : x ∈ M.domain) :
    0 < Module.finrank ℝ (E.V₀ M k) := by
  rw [E.finrank_V₀ M hΩ k]
  exact Fintype.card_pos_iff.2
    ⟨⟨⟨⟨g, hg⟩, i⟩, E.not_isBoundaryDof_of_mem_convexHull M hΩ ⟨⟨g, hg⟩, i⟩ hx hxΩ⟩⟩

end LocalElement

/-- A `(d+1)`-subset of the vertices `{0, …, n}` containing `0` and `n`. -/
theorem exists_finset_zero_last_mem {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    ∃ f : Finset (Fin (n + 1)), 0 ∈ f ∧ Fin.last n ∈ f ∧ #f = d + 1 := by
  classical
  have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  set u := Finset.univ \ {0, Fin.last n}
  have hu : #u = n - 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, card_pair hne]
    omega
  obtain ⟨t, htu, htc⟩ := exists_subset_card_eq (show d - 1 ≤ #u by omega)
  have h0t : (0 : Fin (n + 1)) ∉ t := fun h => by
    have := htu h; simp [u] at this
  have hlt : Fin.last n ∉ t := fun h => by
    have := htu h; simp [u] at this
  refine ⟨insert 0 (insert (Fin.last n) t), mem_insert_self _ _,
    mem_insert_of_mem (mem_insert_self _ _), ?_⟩
  rw [card_insert_of_notMem (by simp [hne, h0t]), card_insert_of_notMem hlt, htc]
  omega

/-- **Faces of the Freudenthal mesh through the interior**: for `1 ≤ d ≤ n`, the level-`N`
Freudenthal mesh of the box `∏ (bᵢ, bᵢ + s)` has a `d`-face whose convex hull meets the open
box (a face of the simplex `b + (s/N) K_id` containing the diagonal from `b` to
`b + (s/N)(1, …, 1)`). -/
theorem exists_meshFace_freudenthalMesh {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N]
    {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    ∃ g ∈ LocalElement.meshFaces (freudenthalMesh b s hs N), #g = d + 1 ∧
      ∃ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), x ∈ (freudenthalMesh b s hs N).domain := by
  classical
  obtain ⟨f, hf0, hfl, hfc⟩ := exists_finset_zero_last_mem hd1 hdn
  set T₀ := mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
    (freudenthalSimplex (finLattice (0 : Fin n → Fin N)) 1)
  have hT₀ : T₀ ∈ (freudenthalMesh b s hs N).simplices :=
    mem_freudenthalMesh_simplices.2 ⟨0, 1, rfl⟩
  have hpts : ∀ j, T₀.points j = b + (s / N) • kuhnVertex 1 j := fun j => by
    have : latticePoint (finLattice (0 : Fin n → Fin N)) = 0 := by
      funext i; simp [finLattice]
    simp [T₀, this]
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hh : 0 < s / N := div_pos hs (by linarith)
  have hhs : s / N ≤ s := div_le_self hs.le hN
  set g := f.image T₀.points
  refine ⟨g, (LocalElement.mem_meshFaces _).2 ⟨T₀, hT₀, fun x hx => ?_⟩, ?_, ?_⟩
  · obtain ⟨j, -, rfl⟩ := mem_image.1 hx
    exact points_mem_vertexSet T₀ j
  · rw [card_image_of_injective _ T₀.independent.injective, hfc]
  · refine ⟨(1 / 2 : ℝ) • T₀.points 0 + (1 / 2 : ℝ) • T₀.points (Fin.last n),
      convex_convexHull ℝ _ (subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem _ hf0)))
        (subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem _ hfl))) (by norm_num) (by norm_num)
        (by norm_num), ?_⟩
    rw [freudenthalMesh_domain]
    intro i _
    simp only [hpts, kuhnVertex_zero, kuhnVertex_last, smul_zero, add_zero, Pi.add_apply,
      Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Set.mem_Ioo]
    constructor <;> nlinarith

namespace PolySeq

variable (S : PolySeq)

/-- **The interior spaces of every admissible sequence are nonzero** on every Freudenthal mesh of a
box, in degree `k` as soon as some `d`-face, `1 ≤ d ≤ n`, carries degrees of freedom of degree
`k`. -/
theorem finrank_V₀_freudenthalMesh_pos [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ}
    [NeZero N] {k d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (hdim : 0 < Module.finrank ℝ (S.test k d)) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_meshFace_freudenthalMesh (b := b) hs (N := N) hd1 hdn
  have hgd : #g - 1 = d := by omega
  have hne : g.Nonempty := card_pos.1 (by omega)
  have hdim' : 0 < Module.finrank ℝ (S.test k (#g - 1)) := by rw [hgd]; exact hdim
  exact (polyElement n S).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨⟨0, hdim'⟩, hne⟩ : S.DofIdx g k) hx hxΩ

theorem _root_.Feec.FiniteElement.PolyKind.testDim_self_pos (κ : PolyKind) {r : ℕ} (hr : 1 ≤ r)
    (k : ℕ) : 0 < κ.testDim r k k := by
  cases κ <;>
  · simp only [PolyKind.testDim, le_refl, true_and, show k < r + k by omega, ↓reduceIte,
      Nat.sub_self, Nat.choose_zero_right, mul_one]
    exact Nat.choose_pos (by omega)

/-- **`V̊ₕᵏ ≠ 0` for `1 ≤ k ≤ n`** on every Freudenthal mesh of a box, for every admissible
sequence (the `k`-faces through the interior carry degrees of freedom). -/
theorem finrank_V₀_freudenthalMesh_pos_of_one_le [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) :=
  S.finrank_V₀_freudenthalMesh_pos hs hk1 hkn
    (by rw [finrank_test]; exact PolyKind.testDim_self_pos _ (S.one_le_deg k) k)

/-- **`V̊ₕ⁰ ≠ 0` for polynomial degree `r₀ ≥ 2`** on every Freudenthal mesh of a box (even the
coarsest one, without interior vertices: the edge through the interior carries a degree of
freedom). -/
theorem finrank_V₀_freudenthalMesh_pos_zero [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] (h2 : 2 ≤ S.deg 0) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) 0) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  refine S.finrank_V₀_freudenthalMesh_pos hs le_rfl hn ?_
  rw [finrank_test]
  cases h : S.kind 0 <;>
  · simp only [PolyKind.testDim, zero_le, true_and, show 1 < S.deg 0 + 0 by omega, ↓reduceIte,
      Nat.sub_zero]
    refine Nat.mul_pos (Nat.choose_pos (by omega)) ?_
    rw [Nat.choose_one_right]
    omega

/-- **The interior spaces of the second row of Tables 5.1/6.1 are nonzero**: on the
level-`(N+1)` Freudenthal mesh of `(0, ½)³`, the spaces `P₂Λ⁰`, `P₂⁻Λ¹`, `P₁Λ²`, `P₀Λ³` with
vanishing boundary degrees of freedom are nonzero, for every `N`. (These are the boundary
conditions of Ch. 5, imposed in every degree; for the Ch. 6 pattern `V̊ₕ⁰, V̊ₕ¹, Vₕ²` see
`PolySeq.lagrangeP2_VPartial_bcFacets_ne_bot` in `Feec.FiniteElement.PolyElementMixed`.) -/
theorem lagrangeP2_V₀_ne_bot (N k : ℕ) (hk : k ≤ 3) :
    (polyElement 3 lagrangeP2).V₀ (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)) k ≠ ⊥ := by
  intro h
  have hpos : 0 < Module.finrank ℝ
      ((polyElement 3 lagrangeP2).V₀ (freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)) k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact lagrangeP2.finrank_V₀_freudenthalMesh_pos_zero _ (by simp)
    · exact lagrangeP2.finrank_V₀_freudenthalMesh_pos_of_one_le _ hk1 hk
  rw [h, finrank_bot] at hpos
  exact lt_irrefl 0 hpos

end PolySeq

/-- **The interior Whitney spaces are nonzero in the degrees `1 ≤ k ≤ n`** on every Freudenthal
mesh of a box: the `k`-faces through the interior are not contained in boundary facets. (For
`k = 0`, `V̊ₕ⁰ ≠ 0` needs an interior vertex, i.e. level `N ≥ 2`.) -/
theorem finrank_whitney_V₀_freudenthalMesh_pos [NeZero n] {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    {N : ℕ} [NeZero N] {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((whitneyElement n).V₀ (freudenthalMesh b s hs N) k) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_meshFace_freudenthalMesh (b := b) hs (N := N) hk1 hkn
  exact (whitneyElement n).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨(), hgc⟩ : WhitneyDofIdx g k) hx hxΩ

/-- **An interior vertex of the Freudenthal mesh**: for `N ≥ 2`, the lattice point
`b + (s/N)(1, …, 1)` (the first vertex of `b + (s/N)((1, …, 1) + K_id)`) is a vertex of the
level-`N` Freudenthal mesh of `∏ (bᵢ, bᵢ + s)` lying in the open box. -/
theorem exists_vertex_freudenthalMesh {b : Fin n → ℝ} {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) :
    ∃ g ∈ LocalElement.meshFaces (freudenthalMesh b s hs N), #g = 0 + 1 ∧
      ∃ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), x ∈ (freudenthalMesh b s hs N).domain := by
  classical
  set m : Fin n → Fin N := fun _ => ⟨1, by omega⟩
  set T₁ := mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
    (freudenthalSimplex (finLattice m) 1)
  have hT₁ : T₁ ∈ (freudenthalMesh b s hs N).simplices :=
    mem_freudenthalMesh_simplices.2 ⟨m, 1, rfl⟩
  have hpt : T₁.points 0 = b + (s / N) • (1 : Fin n → ℝ) := by
    have : latticePoint (finLattice m) = 1 := by
      funext i; simp [finLattice, m]
    simp [T₁, this]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 < s / N := div_pos hs (by linarith)
  have hhs : s / N < s := div_lt_self hs (by linarith)
  refine ⟨{T₁.points 0}, (LocalElement.mem_meshFaces _).2 ⟨T₁, hT₁, fun x hx => ?_⟩,
    card_singleton _, T₁.points 0, subset_convexHull ℝ _ (by simp), ?_⟩
  · rw [mem_singleton.1 hx]
    exact points_mem_vertexSet T₁ 0
  · rw [freudenthalMesh_domain, hpt]
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Set.mem_Ioo]
    constructor <;> linarith

namespace PolySeq

/-- **`V̊ₕ⁰ ≠ 0` on Freudenthal meshes of level `N ≥ 2`** for every admissible sequence (in
particular for `r₀ = 1`): the interior vertex carries a degree of freedom. -/
theorem finrank_V₀_freudenthalMesh_pos_zero_of_two_le (S : PolySeq) [NeZero n] {b : Fin n → ℝ}
    {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) 0) := by
  obtain ⟨g, hg, hgc, x, hx, hxΩ⟩ := exists_vertex_freudenthalMesh (b := b) hs hN
  have hdim : 0 < Module.finrank ℝ (S.test 0 (#g - 1)) := by
    rw [hgc, finrank_test]; exact PolyKind.testDim_self_pos _ (S.one_le_deg 0) 0
  exact (polyElement n S).finrank_V₀_pos _ (isOpen_freudenthalMesh_domain b s hs N) hg
    (⟨⟨0, hdim⟩, card_pos.1 (by omega)⟩ : S.DofIdx g 0) hx hxΩ

/-- **`V̊ₕᵏ ≠ 0` in every degree `k ≤ n`** on the Freudenthal meshes of level `N ≥ 2`, for every
admissible sequence. -/
theorem finrank_V₀_freudenthalMesh_pos_of_two_le (S : PolySeq) [NeZero n] {b : Fin n → ℝ}
    {s : ℝ} (hs : 0 < s) {N : ℕ} [NeZero N] (hN : 2 ≤ N) {k : ℕ} (hkn : k ≤ n) :
    0 < Module.finrank ℝ ((polyElement n S).V₀ (freudenthalMesh b s hs N) k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact S.finrank_V₀_freudenthalMesh_pos_zero_of_two_le hs hN
  · exact S.finrank_V₀_freudenthalMesh_pos_of_one_le hs hk1 hkn

end PolySeq

end Feec.FiniteElement
