module

public import Feec.FiniteElement.ShapeRegularInverse

/-!
# Mesh geometry for smoothed projections on shape-regular meshes

draft
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology

namespace Feec.FiniteElement

open Feec.Mesh ExteriorFibre

variable {n : ℕ}

/-! ### Barycentric coordinates -/

theorem coord_eq_baryCoord (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1))
    (y : Fin n → ℝ) : T.affineBasis.coord i y = baryCoord T.points y i := by
  have hw := T.affineBasis.sum_coord_apply_eq_one y
  have e := T.affineBasis.affineCombination_coord_eq_self y
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at e
  conv_rhs => rw [← e]
  rw [baryCoord_sum_smul T.points univ hw]
  simp only [Affine.Simplex.coe_affineBasis, baryCoord_vertex (isUnit_det_edgeMatrix T),
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The barycentric coordinates of `T` are Lipschitz with constant `n (n + 1) ‖B_T⁻¹‖`. -/
theorem abs_coord_sub_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1))
    (y y' : Fin n → ℝ) :
    |T.affineBasis.coord i y - T.affineBasis.coord i y'| ≤
      n * ((n + 1) * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) * ‖y - y'‖ := by
  rw [coord_eq_baryCoord, coord_eq_baryCoord, baryCoord_sub]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |baryGrad T.points i l * (y l - y' l)|
      ≤ ∑ _l : Fin n, ((n + 1) * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖) *
          ‖y - y'‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul]
        refine mul_le_mul (abs_baryGrad_le T i l) ?_ (abs_nonneg _) (by positivity)
        have := norm_le_pi_norm (y - y') l
        rwa [Real.norm_eq_abs, Pi.sub_apply] at this
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The barycentric coordinates of a point of a face `q` of `T` (`q` an enumeration of vertices
of `T`, `x = Σₐ wₐ qₐ`, `Σ wₐ = 1`). -/
theorem coord_sum_smul (T : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    {q : Fin (k + 1) → Fin n → ℝ} {w : Fin (k + 1) → ℝ} (hw : ∑ a, w a = 1) (i : Fin (n + 1)) :
    T.affineBasis.coord i (∑ a, w a • q a) = ∑ a, w a * T.affineBasis.coord i (q a) := by
  rw [coord_eq_baryCoord, baryCoord_sum_smul T.points univ hw]
  simp only [coord_eq_baryCoord]

theorem coord_face_point (T : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    {q : Fin (k + 1) → Fin n → ℝ} (hq : Function.Injective q)
    (hqT : ∀ b, ∃ j, T.points j = q b) {w : Fin (k + 1) → ℝ}
    (hw : ∑ a, w a = 1) {i : Fin (n + 1)} {a : Fin (k + 1)} (ha : q a = T.points i) :
    T.affineBasis.coord i (∑ b, w b • q b) = w a := by
  classical
  rw [coord_sum_smul T hw i, Finset.sum_eq_single a]
  · rw [ha, Affine.Simplex.coord_points_self, mul_one]
  · intro b _ hb
    have hqb : q b ≠ T.points i := fun h => hb (hq (h.trans ha.symm))
    obtain ⟨j, hj⟩ := hqT b
    rw [← hj, T.coord_points_ne (fun h => hqb (by rw [← hj, h])), mul_zero]
  · simp


/-! ### The star of a face -/

namespace StarGeom

variable (M : SimplicialMesh n)

/-- The union of the simplices of `M` having `g` among their faces. -/
def starSet (g : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  ⋃ T ∈ M.simplices.filter (fun T => g ⊆ vertexSet T), T.closedInterior

/-- The union of the other simplices of `M`. -/
def restSet (g : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  ⋃ T ∈ M.simplices.filter (fun T => ¬ g ⊆ vertexSet T), T.closedInterior

variable {M}

theorem isClosed_starSet (g : Finset (Fin n → ℝ)) : IsClosed (starSet M g) :=
  isClosed_biUnion_finset fun T _ => T.isClosed_closedInterior

theorem isClosed_restSet (g : Finset (Fin n → ℝ)) : IsClosed (restSet M g) :=
  isClosed_biUnion_finset fun T _ => T.isClosed_closedInterior

theorem mem_starSet {g : Finset (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ starSet M g ↔ ∃ T ∈ M.simplices, g ⊆ vertexSet T ∧ x ∈ T.closedInterior := by
  simp [starSet, and_assoc]

theorem mem_restSet {g : Finset (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ restSet M g ↔ ∃ T ∈ M.simplices, ¬ g ⊆ vertexSet T ∧ x ∈ T.closedInterior := by
  simp [restSet, and_assoc]

theorem closure_domain_subset (g : Finset (Fin n → ℝ)) :
    closure M.domain ⊆ starSet M g ∪ restSet M g := by
  intro x hx
  rw [← M.biUnion_closedInterior, Set.mem_iUnion₂] at hx
  obtain ⟨T, hT, hxT⟩ := hx
  by_cases hg : g ⊆ vertexSet T
  · exact Or.inl (mem_starSet.2 ⟨T, hT, hg, hxT⟩)
  · exact Or.inr (mem_restSet.2 ⟨T, hT, hg, hxT⟩)

/-- **A simplex not containing `g` meets a simplex containing `g` only where some barycentric
coordinate of a vertex of `g` vanishes.** -/
theorem exists_coord_eq_zero {T₁ T₂ : Affine.Simplex ℝ (Fin n → ℝ) n} (h1 : T₁ ∈ M.simplices)
    (h2 : T₂ ∈ M.simplices) {g : Finset (Fin n → ℝ)} (hg1 : g ⊆ vertexSet T₁)
    (hg2 : ¬ g ⊆ vertexSet T₂) {z : Fin n → ℝ} (hz1 : z ∈ T₁.closedInterior)
    (hz2 : z ∈ T₂.closedInterior) :
    ∃ i, T₁.points i ∈ g ∧ T₁.affineBasis.coord i z = 0 := by
  classical
  obtain ⟨v, hvg, hv2⟩ := Finset.not_subset.1 hg2
  obtain ⟨i, rfl⟩ := mem_vertexSet.1 (hg1 hvg)
  refine ⟨i, hvg, ?_⟩
  have hz : z ∈ convexHull ℝ ((vertexSet T₁ : Set (Fin n → ℝ)) ∩ vertexSet T₂) := by
    rw [← M.inter_closedInterior T₁ h1 T₂ h2]; exact ⟨hz1, hz2⟩
  refine coord_eq_zero_of_mem_convexHull T₁ ?_
    (fun h : T₁.points i ∈ (vertexSet T₁ : Set (Fin n → ℝ)) ∩ vertexSet T₂ => hv2 h.2) hz
  exact Set.inter_subset_left.trans (coe_vertexSet T₁).subset

/-- A face point: in every simplex of `M` containing `g`, the barycentric coordinates of `x` at
the vertices of `g` are at least `θ`. -/
def IsFacePoint (M : SimplicialMesh n) (g : Finset (Fin n → ℝ)) (θ : ℝ) (x : Fin n → ℝ) :
    Prop :=
  ∀ T ∈ M.simplices, g ⊆ vertexSet T → ∀ i, T.points i ∈ g → θ ≤ T.affineBasis.coord i x

/-- The points `Σₐ wₐ qₐ` of a face `g = {qₐ}` with weights `wₐ ≥ θ` are face points. -/
theorem isFacePoint_sum_smul {k : ℕ} {q : Fin (k + 1) → Fin n → ℝ} (hq : Function.Injective q)
    {g : Finset (Fin n → ℝ)} (hqg : Set.range q = g) {w : Fin (k + 1) → ℝ} {θ : ℝ}
    (hw : ∀ a, θ ≤ w a) (hw1 : ∑ a, w a = 1) : IsFacePoint M g θ (∑ a, w a • q a) := by
  intro T _ hgT i hi
  have hi' : T.points i ∈ Set.range q := by rw [hqg]; exact hi
  obtain ⟨a, ha⟩ := hi'
  have hqT : ∀ b, ∃ j, T.points j = q b := fun b => by
    have : q b ∈ (g : Set (Fin n → ℝ)) := hqg ▸ ⟨b, rfl⟩
    exact mem_vertexSet.1 (hgT this)
  rw [coord_face_point T hq hqT hw1 ha]
  exact hw a

/-- Lipschitz bound of all the barycentric coordinates of the mesh. -/
def CoordLip (M : SimplicialMesh n) (L : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∀ i y y', |T.affineBasis.coord i y - T.affineBasis.coord i y'| ≤ L * ‖y - y'‖

theorem not_mem_starSet_inter_restSet {L θ : ℝ} (hL : CoordLip M L) {g : Finset (Fin n → ℝ)}
    {x : Fin n → ℝ} (hx : IsFacePoint M g θ x) {z : Fin n → ℝ} (hz : L * ‖z - x‖ < θ) :
    z ∉ starSet M g ∩ restSet M g := by
  rintro ⟨h1, h2⟩
  obtain ⟨T₁, hT₁, hg1, hz1⟩ := mem_starSet.1 h1
  obtain ⟨T₂, hT₂, hg2, hz2⟩ := mem_restSet.1 h2
  obtain ⟨i, hig, hi0⟩ := exists_coord_eq_zero hT₁ hT₂ hg1 hg2 hz1 hz2
  have hθ := hx T₁ hT₁ hg1 i hig
  have hl := hL T₁ hT₁ i x z
  rw [hi0, sub_zero, norm_sub_rev] at hl
  linarith [le_abs_self (T₁.affineBasis.coord i x)]

/-- **Propagation along connected sets**: a preconnected subset of `cl Ω` near a face point `x`
of `g` meeting the star of `g` lies in it. -/
theorem subset_starSet_of_isPreconnected {L θ : ℝ} (hL : CoordLip M L)
    {g : Finset (Fin n → ℝ)} {x : Fin n → ℝ} (hx : IsFacePoint M g θ x) {S : Set (Fin n → ℝ)}
    (hS : IsPreconnected S) (hSΩ : S ⊆ closure M.domain) (hnear : ∀ p ∈ S, L * ‖p - x‖ < θ)
    {z : Fin n → ℝ} (hzS : z ∈ S) (hz : z ∈ starSet M g) : S ⊆ starSet M g := by
  intro w hwS
  by_contra hw
  have hw' : w ∈ restSet M g := by
    rcases closure_domain_subset g (hSΩ hwS) with h | h
    · exact absurd h hw
    · exact h
  obtain ⟨p, hp, hp'⟩ := isPreconnected_closed_iff.1 hS _ _ (isClosed_starSet g)
    (isClosed_restSet g) (hSΩ.trans (closure_domain_subset g)) ⟨z, hzS, hz⟩ ⟨w, hwS, hw'⟩
  exact not_mem_starSet_inter_restSet hL hx (hnear p hp) hp'

/-- **Propagation along segments**: a segment inside `cl Ω` near a face point `x` of `g` starting
in the star of `g` stays in it. -/
theorem mem_starSet_of_segment {L θ : ℝ} (hL : CoordLip M L) {g : Finset (Fin n → ℝ)}
    {x : Fin n → ℝ} (hx : IsFacePoint M g θ x) {z w : Fin n → ℝ}
    (hseg : segment ℝ z w ⊆ closure M.domain) (hnear : ∀ p ∈ segment ℝ z w, L * ‖p - x‖ < θ)
    (hz : z ∈ starSet M g) : w ∈ starSet M g :=
  subset_starSet_of_isPreconnected hL hx (convex_segment z w).isPreconnected hseg hnear
    (left_mem_segment ℝ z w) hz (right_mem_segment ℝ z w)

/-- **Samples near a face point lie in simplices containing the face** (the geometric lemma of
the smoothed-projection estimates, [AFW2010], §5.4): if `t` lies in the interior of `T'` and
is joined to the face point `x` by two segments in `cl Ω` near `x`, then `g` is a face of `T'`. -/
theorem subset_vertexSet_of_segments {L θ : ℝ} (hL : CoordLip M L) {g : Finset (Fin n → ℝ)}
    {x : Fin n → ℝ} (hx : IsFacePoint M g θ x) (hxs : x ∈ starSet M g) {y t : Fin n → ℝ}
    (h1 : segment ℝ x y ⊆ closure M.domain) (h1' : ∀ p ∈ segment ℝ x y, L * ‖p - x‖ < θ)
    (h2 : segment ℝ y t ⊆ closure M.domain) (h2' : ∀ p ∈ segment ℝ y t, L * ‖p - x‖ < θ)
    {T' : Affine.Simplex ℝ (Fin n → ℝ) n} (hT' : T' ∈ M.simplices)
    (ht : t ∈ interior T'.closedInterior) : g ⊆ vertexSet T' := by
  have hy := mem_starSet_of_segment hL hx h1 h1' hxs
  have ht' := mem_starSet_of_segment hL hx h2 h2' hy
  obtain ⟨T'', hT'', hgT'', htT''⟩ := mem_starSet.1 ht'
  by_cases he : T'' = T'
  · exact he ▸ hgT''
  · exfalso
    have hd := M.pairwise_disjoint_interior hT' hT'' (Ne.symm he)
    have hd' := hd.closure_right isOpen_interior
    rw [SimplicialMesh.closure_interior_closedInterior] at hd'
    exact Set.disjoint_left.1 hd' ht htT''


/-! ### Boundary facets near frontier points -/

theorem continuous_coord (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1)) :
    Continuous (T.affineBasis.coord i) :=
  (T.affineBasis.coord i).continuous_of_finiteDimensional

/-- **Barycentric coordinates on a common face**: if every vertex of `T` carrying a nonzero
coordinate of `z` is a vertex of `T'`, the coordinates of `z` in `T'` are those in `T`. -/
theorem coord_eq_of_vertices {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} {z : Fin n → ℝ}
    (hV : ∀ l, T.affineBasis.coord l z ≠ 0 → T.points l ∈ Set.range T'.points)
    {j l₀ : Fin (n + 1)} (hl₀ : T.points l₀ = T'.points j) :
    T'.affineBasis.coord j z = T.affineBasis.coord l₀ z := by
  classical
  have hw := T.affineBasis.sum_coord_apply_eq_one z
  have e := T.affineBasis.affineCombination_coord_eq_self z
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at e
  conv_lhs => rw [← e]
  rw [coord_sum_smul T' hw j]
  simp only [Affine.Simplex.coe_affineBasis]
  rw [Finset.sum_eq_single l₀]
  · rw [hl₀, Affine.Simplex.coord_points_self, mul_one]
  · intro l _ hl
    by_cases h0 : T.affineBasis.coord l z = 0
    · rw [h0, zero_mul]
    · obtain ⟨m, hm⟩ := hV l h0
      have hmj : j ≠ m := by
        rintro rfl
        exact hl (T.independent.injective (hm.symm.trans hl₀.symm))
      rw [← hm, T'.coord_points_ne hmj, mul_zero]
  · simp

/-- The coordinates of a point of `T ∩ T'` (a common face). -/
theorem coord_eq_of_mem_inter {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices)
    (hT' : T' ∈ M.simplices) {z : Fin n → ℝ} (hz : z ∈ T.closedInterior)
    (hz' : z ∈ T'.closedInterior) {i : Fin (n + 1)} (hi : T.affineBasis.coord i z ≠ 0) :
    ∃ j, T'.points j = T.points i ∧ T'.affineBasis.coord j z = T.affineBasis.coord i z := by
  have hzc : z ∈ convexHull ℝ ((vertexSet T : Set (Fin n → ℝ)) ∩ vertexSet T') := by
    rw [← M.inter_closedInterior T hT T' hT']; exact ⟨hz, hz'⟩
  have hV : ∀ l, T.affineBasis.coord l z ≠ 0 → T.points l ∈ Set.range T'.points := by
    intro l hl
    by_contra hlT'
    refine hl (coord_eq_zero_of_mem_convexHull T ?_ ?_ hzc)
    · exact Set.inter_subset_left.trans (coe_vertexSet T).subset
    · intro h; exact hlT' (by rw [← coe_vertexSet]; exact h.2)
  obtain ⟨j, hj⟩ := hV i hi
  exact ⟨j, hj, coord_eq_of_vertices hV hj.symm⟩

/-- **Relative interior points of an interior facet are interior points of `cl Ω`**. -/
theorem mem_interior_of_isInteriorFacet {F : Finset (Fin n → ℝ)} (hF : M.IsInteriorFacet F)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.cofaces F) {i : Fin (n + 1)}
    (hi : T.points i ∉ F) (hiF : ∀ j, j ≠ i → T.points j ∈ F) {z : Fin n → ℝ}
    (hzi : T.affineBasis.coord i z = 0) (hz : ∀ j, j ≠ i → 0 < T.affineBasis.coord j z) :
    z ∈ interior (closure M.domain) := by
  classical
  obtain ⟨hFf, hcard, -⟩ := hF
  obtain ⟨T', hT', hne⟩ : ∃ T' ∈ M.cofaces F, T' ≠ T := by
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.1 hcard
    by_cases h : a = T
    · exact ⟨b, by rw [he]; simp, fun hb => hab (h.trans hb.symm)⟩
    · exact ⟨a, by rw [he]; simp, h⟩
  have hTF := (M.mem_cofaces.1 hT).2
  have hT'F := (M.mem_cofaces.1 hT').2
  obtain ⟨i', hi', hiF'⟩ := exists_apex hT'F hFf.1
  have hα := M.coord_apex_neg hT' hT hne hFf.1 hi' hiF' hi hiF
  have hmul := SimplicialMesh.coord_apex_eq_mul hT'F hi hiF hi'
  have hV : ∀ l, T.affineBasis.coord l z ≠ 0 → T.points l ∈ Set.range T'.points := by
    intro l hl
    have hli : l ≠ i := fun h => hl (h ▸ hzi)
    rw [← coe_vertexSet]; exact hT'F (hiF l hli)
  have hz' : ∀ j, j ≠ i' → 0 < T'.affineBasis.coord j z := by
    intro j hj
    obtain ⟨l, hl⟩ := mem_vertexSet.1 (hTF (hiF' j hj))
    have hli : l ≠ i := fun h => hi (h ▸ hl ▸ hiF' j hj)
    rw [coord_eq_of_vertices hV hl]
    exact hz l hli
  have h1 : ∀ᶠ p in 𝓝 z, ∀ j, j ≠ i → 0 < T.affineBasis.coord j p := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun p h => absurd hj h
    · exact ((continuous_coord T j).continuousAt.eventually (lt_mem_nhds (hz j hj))).mono
        fun p hp _ => hp
  have h2 : ∀ᶠ p in 𝓝 z, ∀ j, j ≠ i' → 0 < T'.affineBasis.coord j p := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i'
    · exact Filter.Eventually.of_forall fun p h => absurd hj h
    · exact ((continuous_coord T' j).continuousAt.eventually (lt_mem_nhds (hz' j hj))).mono
        fun p hp _ => hp
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [h1, h2] with p hp hp'
  by_cases hpi : 0 ≤ T.affineBasis.coord i p
  · have : p ∈ T.closedInterior := by
      rw [T.mem_closedInterior_iff_coord_nonneg]
      intro j
      by_cases hj : j = i
      · exact hj ▸ hpi
      · exact (hp j hj).le
    exact M.closedInterior_subset_closure (M.mem_cofaces.1 hT).1 this
  · have hneg : T.affineBasis.coord i p < 0 := lt_of_not_ge hpi
    have : p ∈ T'.closedInterior := by
      rw [T'.mem_closedInterior_iff_coord_nonneg]
      intro j
      by_cases hj : j = i'
      · subst hj; rw [hmul p]; nlinarith
      · exact (hp' j hj).le
    exact M.closedInterior_subset_closure (M.mem_cofaces.1 hT').1 this

theorem affineSpan_ne_top_of_card_le {s : Finset (Fin n → ℝ)} (hs : s.card ≤ n) :
    affineSpan ℝ (s : Set (Fin n → ℝ)) ≠ ⊤ := by
  classical
  intro htop
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.coe_empty, AffineSubspace.span_empty] at htop
    exact AffineSubspace.bot_ne_top ℝ (Fin n → ℝ) (Fin n → ℝ) htop
  · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by have := hne.card_pos; omega⟩
    have h1 := finrank_vectorSpan_image_finset_le ℝ (id : (Fin n → ℝ) → Fin n → ℝ) s hm
    rw [Finset.image_id] at h1
    have h2 : vectorSpan ℝ (s : Set (Fin n → ℝ)) = ⊤ := by
      rw [← direction_affineSpan, htop, AffineSubspace.direction_top]
    rw [h2, finrank_top, Module.finrank_fin_fun] at h1
    omega

theorem volume_affineSpan_eq_zero {s : Finset (Fin n → ℝ)} (hs : s.card ≤ n) :
    volume (affineSpan ℝ (s : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) = 0 :=
  Measure.addHaar_affineSubspace volume _ (affineSpan_ne_top_of_card_le hs)


/-- The union of the affine spans of `y` and at most `n - 1` vertices of a simplex of `M`: a
null set. -/
def badSet (M : SimplicialMesh n) (y : Fin n → ℝ) : Set (Fin n → ℝ) :=
  ⋃ T ∈ M.simplices, ⋃ s ∈ (Finset.univ : Finset (Finset (Fin (n + 1)))).filter
    (fun s => s.card + 2 ≤ n + 1),
    (affineSpan ℝ ((insert y (s.image T.points) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :
      Set (Fin n → ℝ))

theorem volume_badSet (y : Fin n → ℝ) : volume (badSet M y) = 0 := by
  classical
  refine (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun T _ => ?_
  refine (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun s hs => ?_
  refine volume_affineSpan_eq_zero ?_
  have hs' : s.card + 2 ≤ n + 1 := (Finset.mem_filter.1 hs).2
  calc (insert y (s.image T.points)).card ≤ (s.image T.points).card + 1 := Finset.card_insert_le _ _
    _ ≤ s.card + 1 := by have := Finset.card_image_le (s := s) (f := T.points); omega
    _ ≤ n := by omega

/-- **Frontier points lie on boundary facets** (the pseudo-manifold property of conforming
meshes): if a point `z` of `T₁ ∈ M` lies in the topological boundary of `cl Ω`, some boundary
facet contains every vertex of `T₁` at which the barycentric coordinate of `z` is positive.
Proof: from a point `y` of the interior of `T₁` near `z`, go towards a generic point `w ∉ cl Ω`
near `z` (outside the null set `badSet M y`); at the first exit point `z'` from `cl Ω`, `z'`
lies on exactly one facet of a simplex containing `z`, which contains the positive vertices of
`z` and cannot be an interior facet (`mem_interior_of_isInteriorFacet`). -/
theorem exists_isBoundaryFacet_of_mem_frontier {T₁ : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT₁ : T₁ ∈ M.simplices) {z : Fin n → ℝ} (hz : z ∈ T₁.closedInterior)
    (hzf : z ∈ frontier (closure M.domain)) :
    ∃ F, M.IsBoundaryFacet F ∧ ∀ i, 0 < T₁.affineBasis.coord i z → T₁.points i ∈ F := by
  classical
  -- a ball around `z` meeting only simplices containing `z`, keeping positive coordinates
  set R : Set (Fin n → ℝ) := ⋃ T ∈ M.simplices.filter (fun T => z ∉ T.closedInterior),
    T.closedInterior
  have hR : IsClosed R := isClosed_biUnion_finset fun T _ => T.isClosed_closedInterior
  have hzR : z ∉ R := by
    intro h
    simp only [R, Set.mem_iUnion, Finset.mem_filter] at h
    obtain ⟨T, ⟨_, hzT⟩, h⟩ := h
    exact hzT h
  have hU1 : Rᶜ ∈ 𝓝 z := hR.isOpen_compl.mem_nhds hzR
  have hU2 : ∀ᶠ p in 𝓝 z, ∀ T ∈ M.simplices, ∀ j, 0 < T.affineBasis.coord j z →
      0 < T.affineBasis.coord j p := by
    rw [Filter.eventually_all_finset]
    intro T _
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : 0 < T.affineBasis.coord j z
    · exact ((continuous_coord T j).continuousAt.eventually (lt_mem_nhds hj)).mono
        fun p hp _ => hp
    · exact Filter.Eventually.of_forall fun p h => absurd h hj
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU1 hU2)
  -- a point `y` of the interior of `T₁` near `z`
  have hzcl : z ∈ closure (interior T₁.closedInterior) := by
    rw [SimplicialMesh.closure_interior_closedInterior]; exact hz
  obtain ⟨y, hyi, hyz⟩ := Metric.mem_closure_iff.1 hzcl ε hε
  have hyint : y ∈ interior (closure M.domain) :=
    interior_mono (M.closedInterior_subset_closure hT₁) hyi
  have hyb : y ∈ Metric.ball z ε := by rw [Metric.mem_ball, dist_comm]; exact hyz
  -- a generic point `w ∉ cl Ω` near `z`
  have hzc : z ∈ closure (closure M.domain)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hzf; exact hzf.2
  set W := Metric.ball z ε ∩ (closure M.domain)ᶜ
  have hWo : IsOpen W := Metric.isOpen_ball.inter isClosed_closure.isOpen_compl
  have hWne : W.Nonempty := by
    obtain ⟨w, hw, hwz⟩ := Metric.mem_closure_iff.1 hzc ε hε
    exact ⟨w, by rw [Metric.mem_ball, dist_comm]; exact hwz, hw⟩
  obtain ⟨w, hwW, hwB⟩ : ∃ w ∈ W, w ∉ badSet M y := by
    by_contra hcon
    push Not at hcon
    have h1 : volume W ≤ volume (badSet M y) := measure_mono hcon
    rw [volume_badSet] at h1
    exact (hWo.measure_pos volume hWne).ne' (le_antisymm h1 bot_le)
  -- the first exit point `z'` of the segment `[y, w]` from `cl Ω`
  set φ : ℝ → Fin n → ℝ := fun s => AffineMap.lineMap y w s
  have hφc : Continuous φ := AffineMap.lineMap_continuous
  set I : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ φ s ∉ closure M.domain}
  have h1I : (1 : ℝ) ∈ I := ⟨⟨zero_le_one, le_rfl⟩, by simpa [φ] using hwW.2⟩
  have hbdd : BddBelow I := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf I
  have hs0 : 0 ≤ s₀ := le_csInf ⟨1, h1I⟩ fun s hs => hs.1.1
  have hs1 : s₀ ≤ 1 := csInf_le hbdd h1I
  set z' := φ s₀
  have hz'c : z' ∈ closure (closure M.domain)ᶜ :=
    map_mem_closure hφc (csInf_mem_closure ⟨1, h1I⟩ hbdd) fun s hs => hs.2
  have hcompl : closure (closure M.domain)ᶜ = (interior (closure M.domain))ᶜ := closure_compl
  have hs0pos : 0 < s₀ := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso
      have : z' = y := by simp [z', φ, ← h]
      rw [hcompl, this] at hz'c
      exact hz'c hyint
  have hz'Ω : z' ∈ closure M.domain := by
    have hsub : Set.MapsTo φ (Set.Ico 0 s₀) (closure M.domain) := by
      intro s hs
      by_contra hns
      exact (notMem_of_lt_csInf hs.2 hbdd) ⟨⟨hs.1, hs.2.le.trans hs1⟩, hns⟩
    have hmem : s₀ ∈ closure (Set.Ico 0 s₀) := by
      rw [closure_Ico hs0pos.ne]; exact ⟨hs0, le_rfl⟩
    exact closure_closure (s := M.domain) ▸ map_mem_closure hφc hmem hsub
  have hz'b : z' ∈ Metric.ball z ε := by
    have hseg : z' ∈ segment ℝ y w := by
      rw [segment_eq_image_lineMap]; exact ⟨s₀, ⟨hs0, hs1⟩, rfl⟩
    exact (convex_ball z ε).segment_subset hyb hwW.1 hseg
  have hz'U := hball hz'b
  have hz'int : z' ∉ interior (closure M.domain) := by
    rw [hcompl] at hz'c; exact hz'c
  -- the simplex `T₂` containing `z'`
  have hz'cov := hz'Ω
  rw [← M.biUnion_closedInterior, Set.mem_iUnion₂] at hz'cov
  obtain ⟨T₂, hT₂, hz'T₂⟩ := hz'cov
  have hzT₂ : z ∈ T₂.closedInterior := by
    by_contra hzT₂
    refine hz'U.1 ?_
    simp only [R, Set.mem_iUnion, Finset.mem_filter]
    exact ⟨T₂, ⟨hT₂, hzT₂⟩, hz'T₂⟩
  have hpos : ∀ i, 0 < T₁.affineBasis.coord i z →
      ∃ j, T₂.points j = T₁.points i ∧ 0 < T₂.affineBasis.coord j z' := by
    intro i hi
    obtain ⟨j, hj, hjc⟩ := coord_eq_of_mem_inter hT₁ hT₂ hz hzT₂ hi.ne'
    exact ⟨j, hj, hz'U.2 T₂ hT₂ j (hjc ▸ hi)⟩
  have hnn : ∀ j, 0 ≤ T₂.affineBasis.coord j z' := T₂.mem_closedInterior_iff_coord_nonneg.1 hz'T₂
  -- `z'` has a zero coordinate
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, T₂.affineBasis.coord i₀ z' = 0 := by
    by_contra hcon
    push Not at hcon
    refine hz'int (interior_mono (M.closedInterior_subset_closure hT₂) ?_)
    rw [Affine.Simplex.interior_closedInterior_eq]
    exact fun j => lt_of_le_of_ne (hnn j) (hcon j).symm
  -- and only one
  have honly : ∀ j, j ≠ i₀ → 0 < T₂.affineBasis.coord j z' := by
    intro j₁ hj₁
    refine lt_of_le_of_ne (hnn j₁) fun h0 => ?_
    set s : Finset (Fin (n + 1)) := (Finset.univ.erase i₀).erase j₁
    have hscard : s.card + 2 = n + 1 := by
      have h1 : j₁ ∈ Finset.univ.erase i₀ := Finset.mem_erase.2 ⟨hj₁, Finset.mem_univ _⟩
      rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      have : 2 ≤ n + 1 := by
        have := Finset.card_le_univ ({i₀, j₁} : Finset (Fin (n + 1)))
        rw [Finset.card_pair hj₁.symm, Fintype.card_fin] at this; exact this
      omega
    set S : Finset (Fin n → ℝ) := s.image T₂.points
    have hz'S : z' ∈ affineSpan ℝ ((insert y S : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
      have hw1 := T₂.affineBasis.sum_coord_apply_eq_one z'
      have e := T₂.affineBasis.affineCombination_coord_eq_self z'
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at e
      have hoff : ∀ l ∈ Finset.univ, l ∉ s → T₂.affineBasis.coord l z' • T₂.points l = 0 := by
        intro l _ hl
        have : l = i₀ ∨ l = j₁ := by
          by_contra h; push Not at h
          exact hl (Finset.mem_erase.2 ⟨h.2, Finset.mem_erase.2 ⟨h.1, Finset.mem_univ _⟩⟩)
        rcases this with rfl | rfl
        · rw [hi₀, zero_smul]
        · rw [← h0, zero_smul]
      have hsum : ∑ l ∈ s, T₂.affineBasis.coord l z' = 1 := by
        rw [← hw1, ← Finset.sum_subset (Finset.subset_univ s)]
        intro l _ hl
        have : l = i₀ ∨ l = j₁ := by
          by_contra h; push Not at h
          exact hl (Finset.mem_erase.2 ⟨h.2, Finset.mem_erase.2 ⟨h.1, Finset.mem_univ _⟩⟩)
        rcases this with rfl | rfl
        · exact hi₀
        · exact h0.symm
      have hz'eq : z' = ∑ l ∈ s, T₂.affineBasis.coord l z' • T₂.points l := by
        rw [Finset.sum_subset (Finset.subset_univ s) hoff]
        simpa using e.symm
      have hconv : z' ∈ convexHull ℝ ((S : Set (Fin n → ℝ))) := by
        rw [hz'eq]
        refine (convex_convexHull ℝ _).sum_mem (fun l _ => hnn l) hsum fun l hl => ?_
        exact subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hl))
      refine affineSpan_mono ℝ ?_ (convexHull_subset_affineSpan _ hconv)
      exact Finset.coe_subset.2 (Finset.subset_insert _ _)
    have hyS : y ∈ affineSpan ℝ ((insert y S : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
      subset_affineSpan ℝ _ (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    have hwS := AffineMap.lineMap_mem s₀⁻¹ hyS hz'S
    have hwe : AffineMap.lineMap y z' s₀⁻¹ = w := by
      simp only [z', φ, AffineMap.lineMap_apply_module']
      rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hs0pos.ne', one_smul, sub_add_cancel]
    rw [hwe] at hwS
    refine hwB ?_
    simp only [badSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨T₂, hT₂, s, by omega, hwS⟩
  -- the facet of `T₂` opposite to `T₂.points i₀`
  set F := (vertexSet T₂).erase (T₂.points i₀)
  have hFT : F ⊆ vertexSet T₂ := Finset.erase_subset _ _
  have hFc : F.card = n := by
    rw [Finset.card_erase_of_mem (points_mem_vertexSet T₂ i₀), card_vertexSet]; omega
  have hFf : F ∈ M.facets := ⟨hFc, T₂, hT₂, hFT⟩
  have hi : T₂.points i₀ ∉ F := Finset.notMem_erase _ _
  have hiF : ∀ j, j ≠ i₀ → T₂.points j ∈ F := fun j hj =>
    Finset.mem_erase.2 ⟨fun h => hj (T₂.independent.injective h), points_mem_vertexSet T₂ j⟩
  have hT₂F : T₂ ∈ M.cofaces F := M.mem_cofaces.2 ⟨hT₂, hFT⟩
  refine ⟨F, ?_, fun i hi' => ?_⟩
  · rcases M.isInteriorFacet_or_isBoundaryFacet hFf with h | h
    · exact absurd (mem_interior_of_isInteriorFacet h hT₂F hi hiF hi₀ honly) hz'int
    · exact h
  · obtain ⟨j, hj, hjpos⟩ := hpos i hi'
    have hji : j ≠ i₀ := fun h => by rw [h, hi₀] at hjpos; exact lt_irrefl _ hjpos
    rw [← hj]; exact hiF j hji


/-- **The first exit point** of a segment from a closed set. -/
theorem exists_mem_frontier_lineMap {K : Set (Fin n → ℝ)} (hK : IsClosed K) {a b : Fin n → ℝ}
    (ha : a ∈ K) (hb : b ∉ K) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, AffineMap.lineMap a b s ∈ frontier K ∧
      AffineMap.lineMap a b '' Set.Icc 0 s ⊆ K := by
  set φ : ℝ → Fin n → ℝ := fun s => AffineMap.lineMap a b s
  have hφc : Continuous φ := AffineMap.lineMap_continuous
  set I : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ φ s ∉ K}
  have h1I : (1 : ℝ) ∈ I := ⟨⟨zero_le_one, le_rfl⟩, by simpa [φ] using hb⟩
  have hbdd : BddBelow I := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf I
  have hs0 : 0 ≤ s₀ := le_csInf ⟨1, h1I⟩ fun s hs => hs.1.1
  have hs1 : s₀ ≤ 1 := csInf_le hbdd h1I
  have hc : φ s₀ ∈ closure Kᶜ :=
    map_mem_closure hφc (csInf_mem_closure ⟨1, h1I⟩ hbdd) fun s hs => hs.2
  have hsub : φ '' Set.Icc 0 s₀ ⊆ K := by
    rintro _ ⟨s, hs, rfl⟩
    rcases hs.2.lt_or_eq with hlt | heq
    · by_contra hns
      exact (notMem_of_lt_csInf hlt hbdd) ⟨⟨hs.1, hlt.le.trans hs1⟩, hns⟩
    · subst heq
      rcases hs0.lt_or_eq with hpos | h0
      · have hmaps : Set.MapsTo φ (Set.Ico 0 s₀) K := by
          intro s' hs'
          by_contra hns
          exact (notMem_of_lt_csInf hs'.2 hbdd) ⟨⟨hs'.1, hs'.2.le.trans hs1⟩, hns⟩
        have hmem : s₀ ∈ closure (Set.Ico 0 s₀) := by
          rw [closure_Ico hpos.ne]; exact ⟨hs0, le_rfl⟩
        exact hK.closure_eq ▸ map_mem_closure hφc hmem hmaps
      · have : φ s₀ = a := by simp [φ, ← h0]
        rw [this]; exact ha
  refine ⟨s₀, ⟨hs0, hs1⟩, ?_, hsub⟩
  rw [frontier_eq_closure_inter_closure, hK.closure_eq]
  exact ⟨hsub ⟨s₀, ⟨hs0, le_rfl⟩, rfl⟩, hc⟩

/-- **Boundary faces near outside points** (the geometric lemma for the vanishing-trace family):
if a point `t` outside the interior of `cl Ω` is near a face point `x` of `g` lying in a simplex
`T ⊇ g` of `M`, then `g` lies in a boundary facet of `M`. -/
theorem exists_isBoundaryFacet_of_near {L θ : ℝ} (hL0 : 0 ≤ L) (hL : CoordLip M L)
    {g : Finset (Fin n → ℝ)} {x : Fin n → ℝ} (hx : IsFacePoint M g θ x)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) (hgT : g ⊆ vertexSet T)
    (hxT : x ∈ T.closedInterior) {t : Fin n → ℝ}
    (ht : t ∉ interior (closure M.domain)) (htx : L * ‖t - x‖ < θ) :
    ∃ F, M.IsBoundaryFacet F ∧ g ⊆ F := by
  classical
  set B : Set (Fin n → ℝ) := {p | L * ‖p - x‖ < θ}
  have hBo : IsOpen B := isOpen_lt (continuous_const.mul (continuous_id.sub continuous_const).norm)
    continuous_const
  have htc : t ∈ closure (closure M.domain)ᶜ := by rw [closure_compl]; exact ht
  obtain ⟨t', ht'B, ht'c⟩ := (mem_closure_iff.1 htc) B hBo htx
  have hxΩ : x ∈ closure M.domain := M.closedInterior_subset_closure hT hxT
  obtain ⟨s, hs, hzf, hsub⟩ := exists_mem_frontier_lineMap isClosed_closure hxΩ ht'c
  set z := AffineMap.lineMap x t' s
  have hnorm : ∀ s' ∈ Set.Icc (0 : ℝ) s, ‖AffineMap.lineMap x t' s' - x‖ ≤ ‖t' - x‖ := by
    intro s' hs'
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg hs'.1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hs'.2.trans hs.2)
  have hnear : ∀ p ∈ AffineMap.lineMap x t' '' Set.Icc 0 s, L * ‖p - x‖ < θ := by
    rintro _ ⟨s', hs', rfl⟩
    exact (mul_le_mul_of_nonneg_left (hnorm s' hs') hL0).trans_lt ht'B
  have hS : IsPreconnected (AffineMap.lineMap x t' '' Set.Icc 0 s) :=
    isPreconnected_Icc.image _ (AffineMap.lineMap_continuous).continuousOn
  have hxS : x ∈ AffineMap.lineMap x t' '' Set.Icc 0 s :=
    ⟨0, ⟨le_rfl, hs.1⟩, AffineMap.lineMap_apply_zero _ _⟩
  have hxs : x ∈ starSet M g := mem_starSet.2 ⟨T, hT, hgT, hxT⟩
  have hzs := subset_starSet_of_isPreconnected hL hx hS hsub hnear hxS hxs
    ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩
  obtain ⟨T₁, hT₁, hgT₁, hzT₁⟩ := mem_starSet.1 hzs
  obtain ⟨F, hF, hPF⟩ := exists_isBoundaryFacet_of_mem_frontier hT₁ hzT₁ hzf
  refine ⟨F, hF, fun v hv => ?_⟩
  obtain ⟨i, rfl⟩ := mem_vertexSet.1 (hgT₁ hv)
  refine hPF i ?_
  have h1 := hx T₁ hT₁ hgT₁ i hv
  have h2 := hL T₁ hT₁ i x z
  have h3 : L * ‖x - z‖ < θ := by
    rw [norm_sub_rev]; exact hnear z ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩
  have := (abs_sub_lt_iff.1 (h2.trans_lt h3)).1
  linarith

end StarGeom


/-! ### Volumes and bounded overlap on quasi-uniform shape-regular meshes -/

theorem refSimplex_closedInterior_eq :
    (Mesh.refSimplex n).closedInterior = FiniteElement.refSimplex n := by
  ext x; rw [mem_closedInterior_refSimplex, mem_refSimplex_iff]

/-- `|T| = |det B_T| / n!`. -/
theorem volume_real_closedInterior (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    volume.real T.closedInterior = |LinearMap.det T.linearPart| / n.factorial := by
  have h := volume_closedInterior_eq T
  rw [Measure.real, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    refSimplex_closedInterior_eq, ← Measure.real, volume_real_refSimplex]
  ring

theorem volume_closedInterior_lt_top (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    volume T.closedInterior < ⊤ := T.isCompact_closedInterior.measure_lt_top

theorem volume_interior_closedInterior (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    volume (interior T.closedInterior) = volume T.closedInterior :=
  measure_congr (interior_ae_eq_of_null_frontier
    (Convex.addHaar_frontier volume (convex_closedInterior T)))

/-- **Counting by volume**: simplices of a mesh lying in a ball `B̄(x, r)` and of volume at least
`v` number at most `(2 r)ⁿ / v`. -/
theorem card_mul_le_of_subset_closedBall (M : SimplicialMesh n)
    {S : Finset (Affine.Simplex ℝ (Fin n → ℝ) n)} (hS : S ⊆ M.simplices) {x : Fin n → ℝ}
    {r v : ℝ} (hr : 0 ≤ r) (hsub : ∀ T ∈ S, T.closedInterior ⊆ Metric.closedBall x r)
    (hv : ∀ T ∈ S, v ≤ volume.real T.closedInterior) :
    S.card * v ≤ (2 * r) ^ n := by
  classical
  have hdisj : (S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)).PairwiseDisjoint
      fun T => interior T.closedInterior := fun T hT T' hT' hne =>
    M.pairwise_disjoint_interior (hS hT) (hS hT') hne
  have hU : volume (⋃ T ∈ S, interior T.closedInterior) =
      ∑ T ∈ S, volume (interior T.closedInterior) :=
    measure_biUnion_finset hdisj fun T _ => isOpen_interior.measurableSet
  have hle : volume (⋃ T ∈ S, interior T.closedInterior) ≤ volume (Metric.closedBall x r) :=
    measure_mono (Set.iUnion₂_subset fun T hT => interior_subset.trans (hsub T hT))
  rw [hU, Real.volume_pi_closedBall x hr, Fintype.card_fin] at hle
  have hle' : ∑ T ∈ S, volume.real T.closedInterior ≤ (2 * r) ^ n := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_sum
      (fun T _ => (measure_mono interior_subset).trans_lt (volume_closedInterior_lt_top T) |>.ne)]
      at this
    simpa only [volume_interior_closedInterior, Measure.real] using this
  calc S.card * v = ∑ _T ∈ S, v := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ T ∈ S, volume.real T.closedInterior := Finset.sum_le_sum hv
    _ ≤ _ := hle'

/-- A mesh is **quasi-uniform** with constant `q`: `q h ≤ h_T` for all its simplices. -/
def IsQuasiUniform (M : SimplicialMesh n) (q : ℝ) : Prop :=
  ∀ T ∈ M.simplices, q * M.meshSize ≤ diam T

theorem mem_cthickening_closedInterior {T : Affine.Simplex ℝ (Fin n → ℝ) n} {r : ℝ}
    (hr : 0 ≤ r) {x : Fin n → ℝ} (hx : x ∈ Metric.cthickening r T.closedInterior) :
    ∃ y ∈ T.closedInterior, dist x y ≤ r := by
  rw [Metric.cthickening_eq_biUnion_closedBall _ hr, T.isClosed_closedInterior.closure_eq,
    Set.mem_iUnion₂] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨y, hy, hxy⟩

open Classical in
/-- **Bounded overlap on quasi-uniform shape-regular meshes**: a point lies in the
`r`-neighbourhoods of at most `(2 (r + h))ⁿ n! / (c (q h)ⁿ)` simplices. -/
theorem card_filter_mem_cthickening_le (M : SimplicialMesh n) {C c q : ℝ}
    (hS : IsShapeRegular (M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) C c)
    (hc : 0 < c) (hq : 0 < q) (hQ : IsQuasiUniform M q) (hh : 0 < M.meshSize) {r : ℝ}
    (hr : 0 ≤ r) (x : Fin n → ℝ) :
    ((M.simplices.filter fun T : Affine.Simplex ℝ (Fin n → ℝ) n =>
        x ∈ Metric.cthickening r T.closedInterior).card : ℝ) ≤
      (2 * (r + M.meshSize)) ^ n * n.factorial / (c * (q * M.meshSize) ^ n) := by
  classical
  set h := M.meshSize
  set S := M.simplices.filter fun T : Affine.Simplex ℝ (Fin n → ℝ) n =>
    x ∈ Metric.cthickening r T.closedInterior
  have hv0 : 0 < c * (q * h) ^ n / n.factorial := by positivity
  have hsub : ∀ T ∈ S, T.closedInterior ⊆ Metric.closedBall x (r + h) := by
    intro T hT p hp
    obtain ⟨hTM, hxT⟩ := Finset.mem_filter.1 hT
    obtain ⟨y, hy, hxy⟩ := mem_cthickening_closedInterior hr hxT
    rw [Metric.mem_closedBall]
    calc dist p x ≤ dist p y + dist y x := dist_triangle _ _ _
      _ ≤ h + r := add_le_add ((Metric.dist_le_diam_of_mem
          T.isCompact_closedInterior.isBounded hp hy).trans (M.diam_le_meshSize hTM))
          (by rw [dist_comm]; exact hxy)
      _ = r + h := add_comm _ _
  have hv : ∀ T ∈ S, c * (q * h) ^ n / n.factorial ≤ volume.real T.closedInterior := by
    intro T hT
    have hTM := (Finset.mem_filter.1 hT).1
    rw [volume_real_closedInterior]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    obtain ⟨-, -, hdet⟩ := hS T hTM
    refine le_trans ?_ hdet
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hQ T hTM) n) hc.le
  have := card_mul_le_of_subset_closedBall M (Finset.filter_subset _ _) (by positivity) hsub hv
  rw [le_div_iff₀ (by positivity)]
  calc (S.card : ℝ) * (c * (q * h) ^ n) = S.card * (c * (q * h) ^ n / n.factorial) *
        n.factorial := by field_simp
    _ ≤ (2 * (r + h)) ^ n * n.factorial :=
        mul_le_mul_of_nonneg_right this (by positivity)

open Classical in
/-- **Bounded overlap, integrated**: if every point lies in at most `K` of the sets `A_T`,
`Σ_T ∫_{A_T} f ≤ K ∫ f` for `f ≥ 0` integrable. -/
theorem sum_integral_le_of_card_le {ι : Type*} (S : Finset ι) (A : ι → Set (Fin n → ℝ))
    (hA : ∀ T, MeasurableSet (A T)) {K : ℝ}
    (hK : ∀ x, ((S.filter fun T => x ∈ A T).card : ℝ) ≤ K) {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∑ T ∈ S, ∫ x in A T, f x ≤ K * ∫ x, f x := by
  classical
  have hint : ∀ T ∈ S, Integrable ((A T).indicator f) := fun T _ => hf.indicator (hA T)
  calc ∑ T ∈ S, ∫ x in A T, f x = ∫ x, ∑ T ∈ S, (A T).indicator f x := by
        rw [integral_finsetSum _ hint]
        exact Finset.sum_congr rfl fun T _ => (integral_indicator (hA T)).symm
    _ ≤ ∫ x, K * f x := by
        refine integral_mono (integrable_finsetSum _ hint) (hf.const_mul _) fun x => ?_
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hK x) (hf0 x)
    _ = _ := integral_const_mul _ _


/-! ### Faces and integrals on a simplex -/

theorem vertexSet_subset_closedInterior' (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    (vertexSet T : Set (Fin n → ℝ)) ⊆ T.closedInterior := by
  rw [← convexHull_vertexSet]; exact subset_convexHull ℝ _

theorem faceEnum_mem_closedInterior {T : Affine.Simplex ℝ (Fin n → ℝ) n} {k : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : g.card = k + 1) (a : Fin (k + 1)) :
    faceEnum g (k + 1) a ∈ T.closedInterior := by
  refine vertexSet_subset_closedInterior' T (hgT ?_)
  have : faceEnum g (k + 1) a ∈ Set.range (faceEnum g (k + 1)) := ⟨a, rfl⟩
  rwa [range_faceEnum hg] at this

theorem simplexMap_faceEnum_mem' {T : Affine.Simplex ℝ (Fin n → ℝ) n} {k : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : g.card = k + 1) {x : Fin k → ℝ}
    (hx : x ∈ FiniteElement.refSimplex k) :
    simplexMap (faceEnum g (k + 1)) x ∈ T.closedInterior := by
  rw [← convexHull_vertexSet]
  refine convexHull_mono ?_ (simplexMap_mem_convexHull _ hx)
  rw [range_faceEnum hg]; exact Finset.coe_subset.2 hgT

/-- The minors of a `k`-face of `T` are `O(h_Tᵏ)`: `Σₛ |minorₛ| ≤ 2ⁿ k! h_Tᵏ`. -/
theorem sum_abs_minor_face_le' {T : Affine.Simplex ℝ (Fin n → ℝ) n} {k : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : g.card = k + 1) :
    ∑ s, |wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ| ≤
      2 ^ n * (k.factorial * diam T ^ k) := by
  refine sum_abs_wedgeProd_simplexMatrix_le (diam_nonneg T) fun i l => ?_
  have h1 := Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded
    (faceEnum_mem_closedInterior hgT hg l.succ) (faceEnum_mem_closedInterior hgT hg 0)
  rw [dist_eq_norm] at h1
  refine le_trans ?_ h1
  have h := norm_le_pi_norm (faceEnum g (k + 1) l.succ - faceEnum g (k + 1) 0) i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at h

/-- **Face integrals on a simplex**: `|∫_g ω| ≤ 2ⁿ h_Tᵏ sup_T |ω|` for a `k`-face `g` of `T`. -/
theorem abs_simplexIntegral_face_le' {T : Affine.Simplex ℝ (Fin n → ℝ) n} {k : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : g.card = k + 1) {ω : FormField n}
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ x ∈ T.closedInterior, ∀ s, |ω x s| ≤ A) :
    |simplexIntegral (faceEnum g (k + 1)) ω| ≤ 2 ^ n * diam T ^ k * A := by
  have h := abs_simplexIntegral_le (p := faceEnum g (k + 1)) (ω := ω) (M := A)
    fun x hx s => hA _ (simplexMap_faceEnum_mem' hgT hg hx) s
  have hm := sum_abs_minor_face_le' hgT hg
  have hk : (0 : ℝ) < k.factorial := by positivity
  refine h.trans ?_
  rw [div_le_iff₀ hk]
  calc (∑ s, |wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ|) * A
      ≤ 2 ^ n * (k.factorial * diam T ^ k) * A := mul_le_mul_of_nonneg_right hm hA0
    _ = _ := by ring

/-- `|T| ≤ (2 h_T)ⁿ`. -/
theorem volume_real_closedInterior_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    volume.real T.closedInterior ≤ (2 * diam T) ^ n := by
  have hsub : T.closedInterior ⊆ Metric.closedBall (T.points 0) (diam T) := fun p hp =>
    Metric.mem_closedBall.2 (Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded hp
      (T.point_mem_closedInterior 0))
  have h := measure_mono (μ := volume) hsub
  rw [Real.volume_pi_closedBall _ (diam_nonneg T), Fintype.card_fin] at h
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by have := diam_nonneg T; positivity) h

/-- `∫_T f ≤ (2 h_T)ⁿ sup_T f` for `0 ≤ f` continuous. -/
theorem integral_closedInterior_le {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) {A : ℝ}
    (hA : ∀ x ∈ T.closedInterior, f x ≤ A) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ x in T.closedInterior, f x ≤ (2 * diam T) ^ n * A := by
  have hA0 : 0 ≤ A := (hf0 _).trans (hA _ (T.point_mem_closedInterior 0))
  have hfin : volume T.closedInterior ≠ ⊤ := (volume_closedInterior_lt_top T).ne
  calc ∫ x in T.closedInterior, f x ≤ ∫ _x in T.closedInterior, A :=
        setIntegral_mono_on (hf.continuousOn.integrableOn_compact T.isCompact_closedInterior)
          (integrableOn_const hfin) T.isClosed_closedInterior.measurableSet hA
    _ = volume.real T.closedInterior * A := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ (2 * diam T) ^ n * A := mul_le_mul_of_nonneg_right (volume_real_closedInterior_le T) hA0

end Feec.FiniteElement
