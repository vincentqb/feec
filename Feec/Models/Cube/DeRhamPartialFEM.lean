module

public import Feec.Models.Cube.DeRhamPartialIdent
public import Feec.Models.Cube.MirrorWeakSymmetryFEM

/-!
# Hodge theory of `HΛ_J((0, ½)ⁿ)` and its finite element subcomplexes

For a set `J` of directions, `FEM.complexPart n J = HΛ_J(Q)` is the `L²` de Rham complex of the cube
`Q = (0, ½)ⁿ` (`FEM.cubeDomain n`) with vanishing tangential traces on the faces normal to the
directions of `J` (`Feec.Models.Cube.DeRhamIdent.HQpartZ`). This file states its Hodge theory in
the form consumed by the finite element method, and builds its conforming finite element
subcomplexes.

**Hodge theory** (from the identification with the mixed parity class,
`Feec.Models.Cube.DeRhamIdent.HQpart_eq_compress`): the Poincaré inequality
`‖z‖ ≤ (2π)⁻¹ ‖d z‖` on `D(d) ∩ (𝔷ⁱ)ᗮ` (`norm_le_of_mem_orthogonal_cycles_part`), closed
range (`closedRangeAt_part`), and the harmonic forms `ℌᵏ = 0` for `k ≠ |J|` and
`ℌ^{|J|} = ℝ · dx_J` (`harmonic_eq_bot_part`, `harmonic_card_eq_span_part`). For `J = ∅` the complex is
`FEM.complex n = HΛ(Q)`, for `J = univ` it is `FEM.complexMin n = H̊Λ(Q)`.

**Finite element subcomplexes.** The partial-boundary spaces `Λ_{h,Γ}ᵏ`
(`Feec.FiniteElement.LocalElement.globalSpacePartial`) with `Γ = partialFaces J`, the vertex sets
lying in a face `{x_j ∈ {0, ½}}`, `j ∈ J`, are **conforming in `D(d_J)`**
(`glue_mem_dPart`): integration by parts on the mesh
(`Feec.FiniteElement.sum_integral_conj_apply_mul_eq`) gives Green's identity
`Feec.Models.Cube.DeRhamIdent.GreenForJ` for the glued fields (`greenForJ_pieceL2`), since on a
boundary facet (which lies in a face of `Q`, `exists_plane_of_isBoundaryFacet`, with normal
`± e_i`, `isFaceNormal_eq_zero`) either `i ∈ J` and the tangential trace vanishes (the degrees of
freedom vanish), or `i ∉ J` and the normal component of the test form vanishes; the
identification with the torus (`Feec.Models.Cube.DeRhamIdent.mem_dPart_of_JfJ`) then puts the
glued field in `D(d_J)`. With `d Λ_{h,Γ}ᵏ ⊆ Λ_{h,Γ}ᵏ⁺¹` they form subcomplexes of `HΛ_J(Q)`
(`LocalElement.subcomplexPart`), on the Freudenthal meshes of the cube for every admissible
sequence `S` (`FEM.polyPartial n S N J`) and for the Whitney forms (`FEM.whitneyPartial n N J`).

* `J = ∅`: `polyPartial ∅` has the spaces of `FEM.poly`;
* `J = univ`: it has the spaces of `FEM.polyMin` (`polyPartial_univ_V`): every boundary facet lies in a face of `Q`
  (`isBoundaryFacet_subset_partialFaces_univ`), and on the Freudenthal meshes every face lying in
  a face of `Q` lies in a boundary facet (`exists_isBoundaryFacet_of_plane`), so
  `Λ_{h,Γ_univ} = Λ̊_h` (`globalSpacePartial_univ_eq`).
* **Monotonicity and non-vacuity**: the spaces decrease with `J` (`polyPartial_V_anti`), so
  `V̊_h ⊆ V_{h,Γ_J}` (`polyMin_V_le_polyPartial_V`), and on `(0, ½)³` they are nonzero in every
  degree for every `J` (`lagrangeP2_polyPartial_V_ne_bot`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (the de Rham complex with boundary conditions), §5 (finite element subcomplexes)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (boundary conditions on
  part of the boundary), Ch. 7 (finite element spaces)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3, (6.5) (the mirror scheme)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace Topology Finset
open Set MeasureTheory Filter LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.HilbertComplex Feec.Mesh Feec.FiniteElement ExteriorFibre
open Feec.Models.Cube.DeRhamIdent (HQpartZ dPart Hpart)

variable (n : ℕ)

/-- **`HΛ_J(Q)`**: the de Rham complex of the cube with vanishing tangential traces on the faces
normal to the directions of `J`. -/
abbrev complexPart (J : Finset (Fin n)) :
    HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (cubeDomain n) (formIdx n k) :=
  HQpartZ (isOpen_cubeDomain n) (cubeDomain_subset_Q n) J

variable {n}

theorem complexPart_d (J : Finset (Fin n)) (k : ℤ) :
    (complexPart n J).d k (k + 1) = dPart (cubeDomain n) J k :=
  DeRhamIdent.HQpartZ_d _ _ J k

/-- **The Poincaré inequality of `HΛ_J(Q)`**: `‖z‖ ≤ (2π)⁻¹ ‖d z‖` for `z ∈ D(d) ∩ (𝔷ⁱ)ᗮ`, in
every degree. -/
theorem norm_le_of_mem_orthogonal_cycles_part (J : Finset (Fin n)) {i j : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (z : ((complexPart n J).d i j).domain)
    (hz : (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈ ((complexPart n J).cycles i)ᗮ) :
    ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤ (2 * Real.pi)⁻¹ * ‖(complexPart n J).d i j z‖ := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω)
      (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (z : ((HQpartZ hΩ hΩQ J).d i j).domain),
      z.1 ∈ ((HQpartZ hΩ hΩQ J).cycles i)ᗮ →
      ‖z.1‖ ≤ (2 * Real.pi)⁻¹ * ‖(HQpartZ hΩ hΩQ J).d i j z‖ := by
    rintro Ω rfl hΩ hΩQ z hz
    exact DeRhamIdent.Hpart_norm_le J hij z hz
  exact key _ (cubeDomain_eq_Q n) _ _ z hz

/-- **Closed range of `HΛ_J(Q)` in every degree.** -/
theorem closedRangeAt_part (J : Finset (Fin n)) (j : ℤ) : (complexPart n J).ClosedRangeAt j :=
  ((complexPart n J).closedRangeAt_iff_poincare_of_rel (DeRhamIdent.rel_sub_one j)).2
    ⟨_, norm_le_of_mem_orthogonal_cycles_part J (DeRhamIdent.rel_sub_one j)⟩

/-- **`HΛ_J(Q)` has no harmonic forms in degrees `k ≠ |J|`.** -/
theorem harmonic_eq_bot_part {J : Finset (Fin n)} {k : ℤ} (hk : k ≠ (#J : ℤ)) :
    (complexPart n J).harmonic k = ⊥ := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω)
      (hΩQ : Ω ⊆ Geometry.Q (Fin n)), (HQpartZ hΩ hΩQ J).harmonic k = ⊥ := by
    rintro Ω rfl hΩ hΩQ
    exact DeRhamIdent.Hpart_harmonic_eq_bot hk
  exact key _ (cubeDomain_eq_Q n) _ _

variable (n) in
/-- The constant form `dx_J` on `Q`. -/
abbrev formPart (J : Finset (Fin n)) : L2F ℝ (cubeDomain n) (formIdx n (#J : ℤ)) :=
  DeRhamIdent.constForm (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ⟨J, rfl⟩

/-- **The harmonic `|J|`-forms of `HΛ_J(Q)` are the constant forms `c dx_J`.** -/
theorem harmonic_card_eq_span_part (J : Finset (Fin n)) :
    (complexPart n J).harmonic (#J : ℤ) = ℝ ∙ formPart n J := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω)
      (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω),
      (HQpartZ hΩ hΩQ J).harmonic (#J : ℤ) =
        ℝ ∙ DeRhamIdent.constForm hm hb (⟨J, rfl⟩ : formIdx n (#J : ℤ)) := by
    rintro Ω rfl hΩ hΩQ hm hb
    exact DeRhamIdent.Hpart_harmonic_card J
  exact key _ (cubeDomain_eq_Q n) _ _ _ _

instance finiteDimensional_harmonic_part (J : Finset (Fin n)) (k : ℤ) :
    FiniteDimensional ℝ ((complexPart n J).harmonic k) := by
  by_cases hk : k = (#J : ℤ)
  · subst hk; rw [harmonic_card_eq_span_part]; infer_instance
  · rw [harmonic_eq_bot_part hk]; infer_instance

/-! ### The faces with a boundary condition and the boundary facets -/

variable (n) in
/-- **The faces with a boundary condition**: the vertex sets lying in one of the faces
`{x_j = 0}`, `{x_j = ½}` of `Q̄ = [0, ½]ⁿ`, `j ∈ J`. -/
def partialFaces (J : Finset (Fin n)) : Set (Finset (Fin n → ℝ)) :=
  {F | ∃ j ∈ J, (∀ v ∈ F, v j = 0) ∨ ∀ v ∈ F, v j = 1 / 2}

@[simp] theorem partialFaces_empty : partialFaces n ∅ = ∅ := by
  ext F; simp [partialFaces]

/-- The closed cube `[0, ½]ⁿ`. -/
abbrev closedCube (n : ℕ) : Set (Fin n → ℝ) := univ.pi fun _ => Icc (0 : ℝ) (1 / 2)

theorem closure_cubeDomain_eq : closure (cubeDomain n) = closedCube n := by
  rw [cubeDomain, closure_pi_set]
  congr 1
  funext i
  exact closure_Ioo (by norm_num)

/-- A point of the boundary of `[0, ½]ⁿ` lies in a face. -/
theorem exists_face_of_mem_frontier {x : Fin n → ℝ} (hx : x ∈ frontier (closedCube n)) :
    ∃ i, x i = 0 ∨ x i = 1 / 2 := by
  have hc : x ∈ closedCube n :=
    (isClosed_set_pi fun _ _ => isClosed_Icc).frontier_subset hx
  have hi : x ∉ interior (closedCube n) := hx.2
  rw [interior_pi_set finite_univ] at hi
  simp only [interior_Icc] at hi
  by_contra h
  push Not at h
  exact hi fun i _ => ⟨lt_of_le_of_ne (hc i trivial).1 (Ne.symm (h i).1),
    lt_of_le_of_ne (hc i trivial).2 (h i).2⟩

/-- **A boundary facet of a mesh of `[0, ½]ⁿ` lies in a face of the cube.** -/
theorem exists_plane_of_isBoundaryFacet {M : SimplicialMesh n}
    (hM : closure M.domain = closedCube n) {F : Finset (Fin n → ℝ)} (hF : M.IsBoundaryFacet F)
    (hne : F.Nonempty) : ∃ i, (∀ v ∈ F, v i = 0) ∨ ∀ v ∈ F, v i = 1 / 2 := by
  obtain ⟨T, hT, hFT⟩ := hF.1.2
  have hv : ∀ v ∈ F, v ∈ closedCube n := fun v hv => by
    rw [← hM]
    refine M.closedInterior_subset_closure hT ?_
    rw [← convexHull_vertexSet]
    exact subset_convexHull ℝ _ (hFT hv)
  set c := F.centerMass (fun _ => (1 : ℝ)) id
  have hpos : 0 < ∑ _v ∈ F, (1 : ℝ) := by simpa using hne.card_pos
  have hc : c ∈ frontier (closure M.domain) :=
    hF.2.2 (F.centerMass_id_mem_convexHull (fun _ _ => zero_le_one) hpos)
  rw [hM] at hc
  obtain ⟨i, hi⟩ := exists_face_of_mem_frontier hc
  have hci : c i = (#F : ℝ)⁻¹ * ∑ v ∈ F, v i := by
    simp [c, Finset.centerMass, Finset.sum_apply]
  have hcard : (0 : ℝ) < #F := by exact_mod_cast hne.card_pos
  refine ⟨i, hi.imp (fun h0 => ?_) fun h1 => ?_⟩
  · rw [hci, mul_eq_zero, inv_eq_zero] at h0
    have hs : ∑ v ∈ F, v i = 0 := h0.resolve_left hcard.ne'
    intro v hvF
    exact (Finset.sum_eq_zero_iff_of_nonneg fun w hw => (hv w hw i trivial).1).1 hs v hvF
  · rw [hci] at h1
    have hs : ∑ v ∈ F, (1 / 2 - v i) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp at h1 ⊢
      linarith
    intro v hvF
    have := (Finset.sum_eq_zero_iff_of_nonneg fun w hw =>
      sub_nonneg.2 (hv w hw i trivial).2).1 hs v hvF
    linarith

/-- **The normals of a facet lying in a coordinate hyperplane** `{x_i = a}` are multiples of
`e_i`. -/
theorem isFaceNormal_eq_zero [NeZero n] {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {F : Finset (Fin n → ℝ)} (hFT : F ⊆ vertexSet T) (hc : #F = n) {i : Fin n} {a : ℝ}
    (hF : ∀ v ∈ F, v i = a) {ν : Fin n → ℝ} (hν : IsFaceNormal F ν) {l : Fin n} (hl : l ≠ i) :
    ν l = 0 := by
  classical
  have hai : AffineIndependent ℝ ((↑) : F → Fin n → ℝ) :=
    (affineIndependent_vertexSet T).mono (s := (F : Set (Fin n → ℝ)))
      (t := (vertexSet T : Set (Fin n → ℝ))) (Finset.coe_subset.2 hFT)
  have hrange : Set.range ((↑) : F → Fin n → ℝ) = (F : Set (Fin n → ℝ)) :=
    Subtype.range_coe_subtype
  have hn : n = (n - 1) + 1 := by have := NeZero.ne n; omega
  have hfin : Module.finrank ℝ (vectorSpan ℝ (F : Set (Fin n → ℝ))) = n - 1 := by
    have := hai.finrank_vectorSpan (n := n - 1) (by rw [Fintype.card_coe, hc]; exact hn)
    rwa [hrange] at this
  have hle : vectorSpan ℝ (F : Set (Fin n → ℝ)) ≤
      LinearMap.ker (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨v, hv, w, hw, rfl⟩
    simp [hF v hv, hF w hw]
  have hW : Module.finrank ℝ (LinearMap.ker (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) =
      n - 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    have h2 : LinearMap.range (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) = ⊤ :=
      LinearMap.range_eq_top.2 fun r => ⟨Pi.single i r, by simp⟩
    rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
    omega
  have heq : vectorSpan ℝ (F : Set (Fin n → ℝ)) =
      LinearMap.ker (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hW])
  have hel : (Pi.single l (1 : ℝ) : Fin n → ℝ) ∈ vectorSpan ℝ (F : Set (Fin n → ℝ)) := by
    rw [heq]; simp [hl.symm]
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ j, ν j * x j
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring }
  have hf : vectorSpan ℝ (F : Set (Fin n → ℝ)) ≤ LinearMap.ker f := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨v, hv, w, hw, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
    exact hν v hv w hw
  have := LinearMap.mem_ker.1 (hf hel)
  simpa [f, Pi.single_apply] using this

/-! ### Green's identity for glued fields on a mesh of the cube -/

/-- **Integration of a piecewise function against a continuous function** over a set containing
the interiors of the elements: `∫_S (Σ_T 𝟙_{int T} v_T) f = Σ_T ∫_T v_T f`. -/
theorem integral_pieceFun_mul_of_subset (M : SimplicialMesh n)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → ℝ}
    (hv : ∀ T ∈ M.simplices, Continuous (v T)) {S : Set (Fin n → ℝ)}
    (hTS : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ S) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) :
    ∫ x in S, pieceFun M v x * f x =
      ∑ T ∈ M.simplices, ∫ x in T.closedInterior, v T x * f x := by
  have e : (fun x => pieceFun M v x * f x) = fun x => ∑ T ∈ M.simplices,
      (interior T.closedInterior).indicator (fun x => v T x * f x) x := by
    funext x
    simp only [pieceFun, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hx : x ∈ interior T.closedInterior <;> simp [hx]
  have hint : ∀ T ∈ M.simplices, IntegrableOn (fun x => v T x * f x) T.closedInterior :=
    fun T hT => (((hv T hT).mul hf).continuousOn).integrableOn_compact T.isCompact_closedInterior
  rw [e, integral_finsetSum _ fun T hT => ((integrable_indicator_iff
    isOpen_interior.measurableSet).2 ((hint T hT).mono_set interior_subset)).restrict]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [integral_indicator isOpen_interior.measurableSet, Measure.restrict_restrict
    isOpen_interior.measurableSet, inter_eq_left.2 (hTS T hT)]
  exact setIntegral_congr_set (interior_ae_eq_of_null_frontier (μ := volume)
    (s := T.closedInterior) (Convex.addHaar_frontier volume (Feec.Mesh.convex_closedInterior T)))

/-- `⟪u, ψ⟫ = Σ_T Σᵢ ∫_T (u_T)ᵢ ψᵢ` for a piecewise field `u` and a continuous `L²` field `ψ`. -/
theorem inner_pieceL2_toL2F (M : SimplicialMesh n) {ι : Type} [Fintype ι]
    {S : Set (Fin n → ℝ)}
    (hTS : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ S)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → ℝ}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) {ψ : ι → (Fin n → ℝ) → ℝ}
    (hψc : ∀ i, Continuous (ψ i)) (hψ : ∀ i, MemLp (ψ i) 2 (volume.restrict S)) :
    ⟪pieceL2 M S v hv, toL2F hψ⟫_ℝ =
      ∑ T ∈ M.simplices, ∑ i, ∫ x in T.closedInterior, v T i x * ψ i x := by
  rw [Feec.Domain.inner_toL2F, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_pieceFun_mul_of_subset M (fun T hT => hv T hT i) hTS (hψc i)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_pieceL2 M S v hv i] with x hx
  simp [hx]

/-- The interiors of the elements of a mesh of `Q` lie in `Q`. -/
theorem interior_subset_Q {M : SimplicialMesh n} (hM : M.domain = Geometry.Q (Fin n))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    interior T.closedInterior ⊆ Geometry.Q (Fin n) := by
  refine (interior_mono (M.closedInterior_subset_closure hT)).trans ?_
  rw [hM, ← cubeDomain_eq_Q, closure_cubeDomain_eq, interior_pi_set finite_univ]
  intro x hx
  simpa [cubeDomain, interior_Icc] using hx

theorem closure_eq_closedCube {M : SimplicialMesh n} (hM : M.domain = Geometry.Q (Fin n)) :
    closure M.domain = closedCube n := by
  rw [hM, ← cubeDomain_eq_Q, closure_cubeDomain_eq]

/-- **The boundary term vanishes** on a boundary facet `F` of a mesh of `Q`: if the tangential
trace of `α` vanishes on `F` when `F` lies in a face normal to `J`, then `φ(x) (ν ∧ α)_t = 0`
for the admissible `φ` (vanishing on the faces normal to `t ∖ J`) and the normals `ν` of `F`. -/
theorem boundary_term_eq_zero [NeZero n] {M : SimplicialMesh n}
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) {k : ℕ} {F : Finset (Fin n → ℝ)}
    (hF : M.IsBoundaryFacet F) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hFT : F ⊆ vertexSet T)
    {α : Finset (Fin n) → ℝ} (hα : IsDeg k α)
    (htr : F ∈ partialFaces n J → TangentialTraceEq F k α 0) {ν : Fin n → ℝ}
    (hν : IsFaceNormal F ν) {x : Fin n → ℝ} (hx : x ∈ convexHull ℝ (F : Set (Fin n → ℝ)))
    (t : Finset (Fin n)) {φ : (Fin n → ℝ) → ℝ}
    (hV : ∀ j ∈ t, j ∉ J → ∀ y : Fin n → ℝ, (y j = 0 ∨ y j = 1 / 2) → φ y = 0) :
    φ x * ExteriorFibre.wedge ν α t = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  have hc : #F = m + 1 := hF.1.1
  have hne : F.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨i, hi⟩ := exists_plane_of_isBoundaryFacet (closure_eq_closedCube hM) hF hne
  obtain ⟨c, hcF, hc01⟩ : ∃ c : ℝ, (∀ v ∈ F, v i = c) ∧ (c = 0 ∨ c = 1 / 2) := by
    rcases hi with h | h
    · exact ⟨0, h, Or.inl rfl⟩
    · exact ⟨1 / 2, h, Or.inr rfl⟩
  have hxi : x i = c := by
    have hsub : convexHull ℝ (F : Set (Fin (m + 1) → ℝ)) ⊆ {y | y i = c} :=
      convexHull_min (fun v hv => hcF v hv) (by
        intro y hy z hz a b _ _ hab
        change y i = c at hy
        change z i = c at hz
        show a * y i + b * z i = c
        rw [hy, hz]
        linear_combination c * hab)
    exact hsub hx
  by_cases hiJ : i ∈ J
  · have hFJ : F ∈ partialFaces (m + 1) J := ⟨i, hiJ, hi⟩
    have hw := wedge_eq_of_tangentialTraceEq hFT hc hα (fun s hs => rfl) (htr hFJ) hν
    rw [hw]
    simp [ExteriorFibre.wedge]
  · by_cases hit : i ∈ t
    · rw [hV i hit hiJ x (hxi ▸ hc01), zero_mul]
    · have h0 : ExteriorFibre.wedge ν α t = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have hli : l ≠ i := fun h => hit (h ▸ hl)
        rw [isFaceNormal_eq_zero hFT hc hcF hν hli]
        ring
      rw [h0, mul_zero]

/-- **Green's identity for the glued fields of `Λ_{h,Γ_J}ᵏ`** on a mesh of `Q`. -/
theorem greenForJ_pieceL2 [NeZero n] (E : LocalElement n) {M : SimplicialMesh n}
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) (k : ℕ)
    (u : E.globalSpacePartial M (partialFaces n J) k) :
    DeRhamIdent.GreenForJ J k
      (pieceL2 M (Geometry.Q (Fin n)) (fun T => formComp (k := (k : ℤ)) (E.extendPW M
        (u : E.Piecewise M k) T))
        (fun _T hT s => continuous_formComp (E.contDiff_extendPW M _ hT).continuous s))
      (pieceL2 M (Geometry.Q (Fin n)) (fun T => formComp (k := (k : ℤ) + 1)
        (extDeriv (E.extendPW M (u : E.Piecewise M k) T)))
        (fun _T hT s => continuous_formComp (continuous_extDeriv (E.contDiff_extendPW M _ hT)) s)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  refine DeRhamIdent.greenForJ_of_inner fun t φ hφ hadm => ?_
  obtain ⟨-, -, hV⟩ := hadm
  set η : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1) → FormField (m + 1) :=
    fun T => E.extendPW M (u : E.Piecewise M k) T
  have hη : ∀ T ∈ M.simplices, ContDiff ℝ 1 (η T) := fun T hT => E.contDiff_extendPW M _ hT
  have hdeg : ∀ T ∈ M.simplices, ∀ x, IsDeg k (η T x) := fun T hT x => E.isDeg_extendPW M _ hT x
  have huc : ∀ T ∈ M.simplices, ∀ s : formIdx (m + 1) k, ContDiff ℝ 1 (formComp (η T) s) :=
    fun T hT s => contDiff_pi.1 (hη T hT) s.1
  have hφ1 : ∀ j, ContDiff ℝ 1 (DeRhamIdent.single1 t φ j) := fun j =>
    (DeRhamIdent.contDiff_single1 t hφ j).of_le (by exact_mod_cast le_top)
  have hTS := fun T hT => interior_subset_Q hM (M := M) (T := T) hT
  have key := sum_integral_conj_apply_mul_eq (extDerivOp ℝ (m + 1) (k : ℤ))
    (extDerivOp_isOrderLE (k : ℤ)) M huc hφ1
    (fun F hF T hT T' hT' ν hν x hx => by
      have hc : F.card = m + 1 := hF.1.1
      have hw := wedge_eq_of_tangentialTraceEq (M.mem_cofaces.1 hT).2 hc
        (hdeg T (M.mem_cofaces.1 hT).1 x) (hdeg T' (M.mem_cofaces.1 hT').1 x)
        (by
          simp only [η]
          rw [E.extendPW_of_mem M _ (M.mem_cofaces.1 hT).1,
            E.extendPW_of_mem M _ (M.mem_cofaces.1 hT').1]
          exact E.tangentialTraceEq_of_mem_globalSpace M u.2.1 hF.1 _ _ (M.mem_cofaces.1 hT).2
            (M.mem_cofaces.1 hT').2 x hx) hν
      funext t'
      rw [symbolApply_extDerivOp, symbolApply_extDerivOp,
        formExt_formComp (hdeg T (M.mem_cofaces.1 hT).1 x),
        formExt_formComp (hdeg T' (M.mem_cofaces.1 hT').1 x)]
      simpa using congrFun hw t'.1)
    (fun F hF T hT ν hν x hx => by
      have hT1 := (M.mem_cofaces.1 hT).1
      have hFT := (M.mem_cofaces.1 hT).2
      rw [Finset.sum_eq_single t (fun s _ hs => by simp [DeRhamIdent.single1, hs]) (by simp)]
      simp only [DeRhamIdent.single1, Pi.single_eq_same, conj_trivial]
      rw [symbolApply_extDerivOp, formExt_formComp (hdeg T hT1 x)]
      have := boundary_term_eq_zero hM J hF hFT (hdeg T hT1 x) (x := x) (ν := ν)
        (fun hFJ => by
          have h := E.trace hFT hFT hF.1.1 ((u : E.Piecewise M k) ⟨T, hT1⟩).2 (Submodule.zero_mem _) fun g hg i => by
            have h0 := u.2.2 ⟨T, hT1⟩ g (hg.trans hFT) ⟨F, hFJ, hg⟩ i
            rw [LocalElement.localDof_apply] at h0
            rw [h0]
            exact (_root_.map_zero _).symm
          simp only [η]
          rw [E.extendPW_of_mem M _ hT1]
          simpa using h x hx) hν hx t.1 hV
      simpa using this)
  rw [inner_pieceL2_toL2F M hTS _ (fun j =>
      (DeRhamIdent.contDiff_single1 t hφ j).continuous),
    inner_pieceL2_toL2F M hTS _ (fun i =>
      ((extDerivOp ℝ (m + 1) (k : ℤ)).formalAdj.continuous_apply
        (formalAdj_extDerivOp_isOrderLE (k : ℤ))
        (fun s' => (DeRhamIdent.contDiff_single1 t hφ s').of_le (by exact_mod_cast le_top)) i))]
  simp only [conj_trivial] at key
  rw [← key]
  refine Finset.sum_congr rfl fun T hT => Finset.sum_congr rfl fun j _ => ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [extDerivOp_apply_formComp (hdeg T hT) j x]
  rfl

/-- **Conformity of `Λ_{h,Γ_J}ᵏ` in `D(d_J)`** on a mesh of `Q`: the glued field lies in the
domain of `d_J`, which is the elementwise exterior derivative. -/
theorem pieceL2_mem_dPart [NeZero n] (E : LocalElement n) {M : SimplicialMesh n}
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) (k : ℕ)
    (u : E.globalSpacePartial M (partialFaces n J) k) :
    ∃ h : pieceL2 M (Geometry.Q (Fin n)) (fun T => formComp (k := (k : ℤ)) (E.extendPW M
        (u : E.Piecewise M k) T))
        (fun _T hT s => continuous_formComp (E.contDiff_extendPW M _ hT).continuous s) ∈
        (dPart (Geometry.Q (Fin n)) J (k : ℤ)).domain,
      dPart (Geometry.Q (Fin n)) J (k : ℤ) ⟨_, h⟩ =
        pieceL2 M (Geometry.Q (Fin n)) (fun T => formComp (k := (k : ℤ) + 1)
          (extDeriv (E.extendPW M (u : E.Piecewise M k) T)))
          (fun _T hT s => continuous_formComp (continuous_extDeriv (E.contDiff_extendPW M _ hT)) s) := by
  have hG := greenForJ_pieceL2 E hM J k u
  obtain ⟨h, e⟩ := DeRhamIdent.mem_dPart_of_JfJ (J := J) (k := k)
    fun m => DeRhamIdent.coeff_d_of_greenForJ hG m
  exact ⟨h, DeRhamIdent.injective_JfJ J (k + 1) e⟩

/-- **Conformity of the glued spaces `V_{h,Γ_J}ᵏ` in `D(d_J)`**, with `d_J` the elementwise
exterior derivative. -/
theorem glue_mem_dPart [NeZero n] (E : LocalElement n) {M : SimplicialMesh n}
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) (k : ℕ)
    (u : E.globalSpacePartial M (partialFaces n J) k) :
    ∃ h : E.glue M k (u : E.Piecewise M k) ∈ (dPart M.domain J (k : ℤ)).domain,
      dPart M.domain J (k : ℤ) ⟨_, h⟩ = E.glue M ((k : ℤ) + 1) (E.dPiecewise M k u) := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)),
      ∃ h : pieceL2 M Ω (fun T => formComp (k := (k : ℤ)) (E.extendPW M
        (u : E.Piecewise M k) T))
        (fun _T hT s => continuous_formComp (E.contDiff_extendPW M _ hT).continuous s) ∈
        (dPart Ω J (k : ℤ)).domain,
      dPart Ω J (k : ℤ) ⟨_, h⟩ =
        pieceL2 M Ω (fun T => formComp (k := (k : ℤ) + 1)
          (extDeriv (E.extendPW M (u : E.Piecewise M k) T)))
          (fun _T hT s => continuous_formComp (continuous_extDeriv (E.contDiff_extendPW M _ hT)) s) := by
    rintro Ω rfl
    exact pieceL2_mem_dPart E hM J k u
  obtain ⟨h, e⟩ := key M.domain hM
  refine ⟨h, e.trans ?_⟩
  change _ = pieceL2 M M.domain
    (fun T => formComp (k := (k : ℤ) + 1) (E.extendPW M (E.dPiecewise M k (u : E.Piecewise M k)) T))
    (fun _T hT s => continuous_formComp (E.contDiff_extendPW M _ hT).continuous s)
  refine pieceL2_congr M _ _ _ fun T hT => ?_
  rw [E.extendPW_of_mem M _ hT, E.extendPW_of_mem M _ hT]
  rfl

/-! ### The finite element subcomplexes of `HΛ_J` -/

theorem isOpen_of_eq_Q {Ω : Set (Fin n → ℝ)} (hΩ : Ω = Geometry.Q (Fin n)) : IsOpen Ω :=
  hΩ ▸ Geometry.isOpen_Q

theorem VPartial_le_dPart_domain [NeZero n] (E : LocalElement n) {M : SimplicialMesh n}
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) (i : ℤ) :
    E.VPartial M (partialFaces n J) i ≤ (dPart M.domain J i).domain := by
  rintro x ⟨u, rfl⟩
  rcases i with k | k
  · exact (glue_mem_dPart E hM J k u).1
  · have := LocalElement.subsingleton_L2F_negSucc M.domain (n := n) k
    rw [Subsingleton.elim (LinearMap.comp _ _ u) 0]
    exact Submodule.zero_mem _

theorem dPart_apply_mem_VPartial [NeZero n] (E : LocalElement n) {M : SimplicialMesh n}
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) (i : ℤ)
    (y : (dPart M.domain J i).domain)
    (hy : (y : L2F ℝ M.domain (formIdx n i)) ∈ E.VPartial M (partialFaces n J) i) :
    dPart M.domain J i y ∈ E.VPartial M (partialFaces n J) (i + 1) := by
  obtain ⟨u, hu⟩ := hy
  rcases i with k | k
  · obtain ⟨h, hval⟩ := glue_mem_dPart E hM J k u
    have hy' : y = ⟨_, h⟩ := Subtype.ext hu.symm
    show dPart M.domain J (k : ℤ) y ∈ E.VPartial M (partialFaces n J) ((k : ℤ) + 1)
    rw [hy', hval]
    exact ⟨⟨_, E.dPiecewise_mem_globalSpacePartial M _ u.2⟩, rfl⟩
  · have := LocalElement.subsingleton_L2F_negSucc M.domain (n := n) k
    have : y = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [this, LinearPMap.map_zero]
    exact Submodule.zero_mem _

/-- **The finite element subcomplex `V_{h,Γ_J} ⊆ HΛ_J`** of an element family on a mesh of `Q`:
the glued partial-boundary spaces with `Γ = partialFaces J` are conforming in `D(d_J)`
(`glue_mem_dPart`) and closed under `d` (`LocalElement.dPiecewise_mem_globalSpacePartial`). -/
def subcomplexPart [NeZero n] (E : LocalElement n) (M : SimplicialMesh n)
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) :
    (HQpartZ (isOpen_of_eq_Q hM) hM.le J).Subcomplex where
  V := E.VPartial M (partialFaces n J)
  le_domain i j := by
    by_cases hij : i + 1 = j
    · subst hij
      rw [DeRhamIdent.HQpartZ_d]
      exact VPartial_le_dPart_domain E hM J i
    · rw [HilbertComplex.domain_eq_top_of_not_rel _ (by simpa using hij)]
      exact le_top
  mapsTo i j x hx := by
    by_cases hij : i + 1 = j
    · subst hij
      exact LocalElement.apply_mem_of_eq (DeRhamIdent.HQpartZ_d (isOpen_of_eq_Q hM) hM.le J i)
        _ (· ∈ E.VPartial M (partialFaces n J) (i + 1))
        fun y' hy' => dPart_apply_mem_VPartial E hM J i y' (hy' ▸ hx)
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact Submodule.zero_mem _

theorem subcomplexPart_V [NeZero n] (E : LocalElement n) (M : SimplicialMesh n)
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) (k : ℤ) :
    (subcomplexPart E M hM J).V k = E.VPartial M (partialFaces n J) k := rfl

instance [NeZero n] (E : LocalElement n) (M : SimplicialMesh n)
    (hM : M.domain = Geometry.Q (Fin n)) (J : Finset (Fin n)) (k : ℤ) :
    FiniteDimensional ℝ ((subcomplexPart E M hM J).V k) :=
  Submodule.finiteDimensional_of_le (E.VPartial_le_V M _ k)

/-- **`J = ∅`: the partial spaces are the full spaces** `V_h`. -/
theorem VPartial_empty (E : LocalElement n) (M : SimplicialMesh n) (k : ℤ) :
    E.VPartial M (partialFaces n ∅) k = E.V M k := by
  unfold LocalElement.VPartial LocalElement.V
  rw [partialFaces_empty, E.globalSpacePartial_empty]

/-- **Every boundary facet of a mesh of `Q` carries a boundary condition for `J = univ`.** -/
theorem isBoundaryFacet_subset_partialFaces_univ [NeZero n] {M : SimplicialMesh n}
    (hM : M.domain = Geometry.Q (Fin n)) :
    {F | M.IsBoundaryFacet F} ⊆ partialFaces n Finset.univ := by
  intro F hF
  have hne : F.Nonempty := Finset.card_pos.1 (by rw [hF.1.1]; exact Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨i, hi⟩ := exists_plane_of_isBoundaryFacet (closure_eq_closedCube hM) hF hne
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- A subcomplex of `HΛ_J(Ω)`, transported along `Ω = Ω'`. -/
def partialSubcomplexOfEq {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω') (hΩQ' : Ω' ⊆ Geometry.Q (Fin n))
    (J : Finset (Fin n)) (S : (HQpartZ hΩ hΩQ J).Subcomplex) :
    (HQpartZ hΩ' hΩQ' J).Subcomplex := by
  subst h; exact S

theorem finiteDimensional_partialSubcomplexOfEq {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω')
    (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω')
    (hΩQ' : Ω' ⊆ Geometry.Q (Fin n)) (J : Finset (Fin n)) (S : (HQpartZ hΩ hΩQ J).Subcomplex)
    [hS : ∀ k, FiniteDimensional ℝ (S.V k)] (k : ℤ) :
    FiniteDimensional ℝ ((partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J S).V k) := by
  subst h; exact hS k

theorem partialSubcomplexOfEq_V_eq_minimal {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω')
    (hΩ : IsOpen Ω) (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω')
    (hΩQ' : Ω' ⊆ Geometry.Q (Fin n)) (J : Finset (Fin n)) (S : (HQpartZ hΩ hΩQ J).Subcomplex)
    (S' : ((deRham ℝ n).minimalComplex hΩ).Subcomplex) (hV : ∀ k, S.V k = S'.V k) (k : ℤ) :
    (partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J S).V k =
      ((deRham ℝ n).minimalSubcomplexOfEq h hΩ hΩ' S').V k := by
  subst h; exact hV k

theorem mesh_domain_eq_Q (N : ℕ) : (mesh n N).domain = Geometry.Q (Fin n) :=
  (mesh_domain n N).trans (cubeDomain_eq_Q n)

/-! ### Faces in the boundary of the cube lie in boundary facets (Freudenthal meshes) -/

section BoundaryFaces

variable {n : ℕ}

/-- **On the Freudenthal meshes of the cube, every face lying in a face of the cube is contained
in a boundary facet** (`FEM.exists_boundaryFacet_of_lower`, `FEM.exists_boundaryFacet_of_upper`;
the empty face lies in the boundary facets of the corner simplex). -/
theorem exists_isBoundaryFacet_of_plane [NeZero n] (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {g : Finset (Fin n → ℝ)} (hg : g ⊆ vertexSet T)
    {i : Fin n} (hgc : (∀ v ∈ g, v i = 0) ∨ ∀ v ∈ g, v i = 1 / 2) :
    ∃ T'' ∈ (mesh n N).simplices, ∃ F, (mesh n N).IsBoundaryFacet F ∧
      F ⊆ vertexSet T'' ∧ g ⊆ F := by
  rcases g.eq_empty_or_nonempty with rfl | hne
  · have hsub : ({(cubeSimplex N 0 1).points 0} : Finset (Fin n → ℝ)) ⊆
        vertexSet (cubeSimplex N 0 1) :=
      Finset.singleton_subset_iff.2 (points_mem_vertexSet _ 0)
    obtain ⟨T'', hT'', F, hF, hFT, -⟩ := exists_boundaryFacet_of_lower 0 1 i hsub
      (fun v hv => by rw [Finset.mem_singleton.1 hv, cubeSimplex_points_apply]; simp)
      (Finset.singleton_nonempty _)
    exact ⟨T'', hT'', F, hF, hFT, Finset.empty_subset _⟩
  · obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
    rcases hgc with h | h
    · obtain ⟨T'', hT'', F, hF, hFT, hgF, -⟩ := exists_boundaryFacet_of_lower m σ i hg h hne
      exact ⟨T'', hT'', F, hF, hFT, hgF⟩
    · obtain ⟨T'', hT'', F, hF, hFT, hgF, -⟩ := exists_boundaryFacet_of_upper m σ i hg h hne
      exact ⟨T'', hT'', F, hF, hFT, hgF⟩

/-- **`J = univ` on the Freudenthal meshes: vanishing boundary DOFs are the partial spaces.** -/
theorem globalSpacePartial_univ_eq [NeZero n] (E : LocalElement n) (N k : ℕ) :
    E.globalSpacePartial (mesh n N) (partialFaces n Finset.univ) k =
      E.globalSpace₀ (mesh n N) k := by
  refine le_antisymm ?_ fun u hu => ⟨hu.1, fun T g hg hgF j => ?_⟩
  · rw [← E.globalSpacePartial_boundary]
    exact E.globalSpacePartial_anti _ (isBoundaryFacet_subset_partialFaces_univ
      (mesh_domain_eq_Q N)) k
  · obtain ⟨F, ⟨i, _, hFi⟩, hgF⟩ := hgF
    have hgi : (∀ v ∈ g, v i = 0) ∨ ∀ v ∈ g, v i = 1 / 2 :=
      hFi.imp (fun h v hv => h v (hgF hv)) fun h v hv => h v (hgF hv)
    obtain ⟨T'', hT'', F', hF', hF'T'', hgF'⟩ := exists_isBoundaryFacet_of_plane N T.2 hg hgi
    rw [hu.1 T ⟨T'', hT''⟩ g hg (hgF'.trans hF'T'') j]
    exact hu.2 ⟨T'', hT''⟩ F' hF' hF'T'' g hgF' j

theorem VPartial_univ_eq [NeZero n] (E : LocalElement n) (N : ℕ) (k : ℤ) :
    E.VPartial (mesh n N) (partialFaces n Finset.univ) k = E.V₀ (mesh n N) k := by
  unfold LocalElement.VPartial LocalElement.V₀
  rw [globalSpacePartial_univ_eq]

end BoundaryFaces

variable [NeZero n]

variable (n) in
/-- **The finite element subcomplex of `HΛ_J(Q)` of the admissible sequence `S`** on the
level-`(N + 1)` Freudenthal mesh of the cube: `P_{r_k}Λᵏ` / `P_{r_k}⁻Λᵏ` with vanishing degrees of
freedom on the faces lying in `{x_j ∈ {0, ½}}`, `j ∈ J`. -/
def polyPartial (S : PolySeq) (N : ℕ) (J : Finset (Fin n)) : (complexPart n J).Subcomplex :=
  partialSubcomplexOfEq (mesh_domain n N) _ _ (isOpen_cubeDomain n) (cubeDomain_subset_Q n) J
    (subcomplexPart (polyElement n S) (mesh n N) (mesh_domain_eq_Q N) J)

instance (S : PolySeq) (N : ℕ) (J : Finset (Fin n)) (k : ℤ) :
    FiniteDimensional ℝ ((polyPartial n S N J).V k) :=
  finiteDimensional_partialSubcomplexOfEq _ _ _ _ _ _ _ k

variable (n) in
/-- **The Whitney subcomplex of `HΛ_J(Q)`** (Lagrange `P₁`, Nédélec, Raviart–Thomas, piecewise
constants with vanishing degrees of freedom on the faces normal to `J`) on the level-`(N + 1)`
Freudenthal mesh of the cube. -/
def whitneyPartial (N : ℕ) (J : Finset (Fin n)) : (complexPart n J).Subcomplex :=
  partialSubcomplexOfEq (mesh_domain n N) _ _ (isOpen_cubeDomain n) (cubeDomain_subset_Q n) J
    (subcomplexPart (whitneyElement n) (mesh n N) (mesh_domain_eq_Q N) J)

instance (N : ℕ) (J : Finset (Fin n)) (k : ℤ) :
    FiniteDimensional ℝ ((whitneyPartial n N J).V k) :=
  finiteDimensional_partialSubcomplexOfEq _ _ _ _ _ _ _ k

/-- **`J = univ`: `polyPartial` has the spaces of `FEM.polyMin`** (vanishing DOFs on every face
lying in the boundary). -/
theorem polyPartial_univ_V (S : PolySeq) (N : ℕ) (k : ℤ) :
    (polyPartial n S N Finset.univ).V k = (polyMin n S N).V k :=
  partialSubcomplexOfEq_V_eq_minimal _ _ _ _ _ _ _ _
    (fun k => VPartial_univ_eq (polyElement n S) N k) k

/-! ### The bottom row of the mirror scheme -/

open MirrorWeakSymmetry (Ebot mirrorFaces)

/-! ### Monotonicity in `J` and non-vacuity -/

omit [NeZero n] in
theorem partialFaces_mono {J J' : Finset (Fin n)} (h : J ⊆ J') :
    partialFaces n J ⊆ partialFaces n J' := fun _ ⟨j, hj, hF⟩ => ⟨j, h hj, hF⟩

omit [NeZero n] in
/-- **`Λ_{h,Γ_J}` decreases with `J`**: more directions with a boundary condition, fewer free
degrees of freedom. -/
theorem VPartial_anti (E : LocalElement n) (M : SimplicialMesh n) {J J' : Finset (Fin n)}
    (h : J ⊆ J') (k : ℤ) :
    E.VPartial M (partialFaces n J') k ≤ E.VPartial M (partialFaces n J) k := by
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨u, E.globalSpacePartial_anti M (partialFaces_mono h) k.toNat u.2⟩, rfl⟩

omit [NeZero n] in
theorem partialSubcomplexOfEq_V_le {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω') (hΩQ' : Ω' ⊆ Geometry.Q (Fin n))
    {J J' : Finset (Fin n)} (S : (HQpartZ hΩ hΩQ J).Subcomplex)
    (S' : (HQpartZ hΩ hΩQ J').Subcomplex) (k : ℤ) (hV : S.V k ≤ S'.V k) :
    (partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J S).V k ≤
      (partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J' S').V k := by
  subst h; exact hV

omit [NeZero n] in
theorem partialSubcomplexOfEq_V_ne_bot {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω') (hΩQ' : Ω' ⊆ Geometry.Q (Fin n))
    (J : Finset (Fin n)) (S : (HQpartZ hΩ hΩQ J).Subcomplex) (k : ℤ) (hV : S.V k ≠ ⊥) :
    (partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J S).V k ≠ ⊥ := by
  subst h; exact hV

/-- **`polyPartial` decreases with `J`.** -/
theorem polyPartial_V_anti (S : PolySeq) (N : ℕ) {J J' : Finset (Fin n)} (h : J ⊆ J')
    (k : ℤ) : (polyPartial n S N J').V k ≤ (polyPartial n S N J).V k :=
  partialSubcomplexOfEq_V_le _ _ _ _ _ _ _ k (VPartial_anti (polyElement n S) (mesh n N) h k)

/-- **`V̊_h ⊆ V_{h,Γ_J} ⊆ V_h`** for the spaces of an admissible sequence. -/
theorem polyMin_V_le_polyPartial_V (S : PolySeq) (N : ℕ) (J : Finset (Fin n)) (k : ℤ) :
    (polyMin n S N).V k ≤ (polyPartial n S N J).V k := by
  rw [← polyPartial_univ_V]; exact polyPartial_V_anti S N (Finset.subset_univ J) k

theorem polyPartial_V_ne_bot_of_V₀ (S : PolySeq) (N : ℕ) (J : Finset (Fin n)) (k : ℤ)
    (h : (polyElement n S).V₀ (mesh n N) k ≠ ⊥) : (polyPartial n S N J).V k ≠ ⊥ := by
  refine partialSubcomplexOfEq_V_ne_bot _ _ _ _ _ J _ k fun hb => h (eq_bot_iff.2 ?_)
  rw [← hb, subcomplexPart_V, ← VPartial_univ_eq]
  exact VPartial_anti (polyElement n S) (mesh n N) (Finset.subset_univ J) k

/-- **Non-vacuity of the partial-boundary subcomplexes** (second row of Tables 5.1/6.1, every
`J`): on every Freudenthal mesh of `(0, ½)³`, the spaces `P₂Λ⁰`, `P₂⁻Λ¹`, `P₁Λ²`, `P₀Λ³` with
vanishing degrees of freedom on the faces normal to `J` are nonzero; they contain the interior
spaces (`PolySeq.lagrangeP2_V₀_ne_bot`). -/
theorem lagrangeP2_polyPartial_V_ne_bot (N k : ℕ) (hk : k ≤ 3) (J : Finset (Fin 3)) :
    (polyPartial 3 PolySeq.lagrangeP2 N J).V k ≠ ⊥ :=
  polyPartial_V_ne_bot_of_V₀ _ N J k (PolySeq.lagrangeP2_V₀_ne_bot N k hk)

end Feec.Models.Cube.FEM
