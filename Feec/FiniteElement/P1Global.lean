module

public import Feec.FiniteElement.LumpedMass
public import Feec.FiniteElement.WhitneyComplex
public import Feec.FiniteElement.MeshDivergence
public import Feec.FiniteElement.ShapeRegularSmoothing
public import Feec.ForMathlib.Calculus.SecondDifference

/-!
# The global `P₁` space: stiffness and lumped mass as integrals

On a simplicial mesh `M`, the nodal values `u : ℝⁿ → ℝ` define the **global `P₁` function**
`u_h = p1Global M u` of the global Whitney `0`-form space `P₁⁻Λ⁰(M)` (the Lagrange `P₁` space of
`Feec.FiniteElement.WhitneyComplex`): on each simplex `T` it is the `P₁` interpolant `Πₜu`
(`p1Form`), and the pieces agree at the shared vertices. Every element of `P₁⁻Λ⁰(M)` is of this
form (`exists_p1Global_eq`), and `u_h` has vanishing boundary DOFs iff `u` vanishes at the
vertices on the boundary of `cl Ω` (`p1Global_mem_globalSpace₀_iff`, by the pseudo-manifold
property `StarGeom.exists_isBoundaryFacet_of_mem_vertexSet`), so the values at the free vertices
are a linear isomorphism onto `P̊₁⁻Λ⁰(M)` (`p1GlobalEquiv₀`). Then

* **`inner_glue_dPiecewise_p1Global`**: the elementwise stiffness form of
  `Feec.FiniteElement.LumpedMass` is the `L²` inner product of the exterior derivatives of the
  glued global functions, `a(u, w) = ⟪d u_h, d w_h⟫_{L²Λ¹(Ω)} = ∫_Ω ∇u_h · ∇w_h`
  (`inner_maximal_p1Global`: `d` the exterior derivative of the `L²` de Rham complex);
* **`inner_glue_p1Global_nodalIndicator_one`**: the lumped mass is the integral of the hat
  function, `m(x) = ⟪φₓ, 1⟫_{L²(Ω)} = ∫_Ω φₓ`, the row sum of the consistent mass matrix: the vertex
  quadrature is exact for `P₁` hat functions (`integral_baryCoord`: `∫_T λⱼ = |T| / (n + 1)`);
* **in the maximum norm**: a `P₁` function attains its extreme values at the vertices,
  `|Πₜu(x)| ≤ maxⱼ |u(pⱼ)|` on `T` (`abs_p1Interp_le`), and the `P₁` interpolation error of
  `f ∈ C²` with `|∂ᵢ∂ₖ f| ≤ D` on `T` is `|f(x) - Πₜf(x)| ≤ n² D δ² / 2`, `δ` the diameter of `T`
  in the maximum norm (`abs_sub_p1Interp_le`, Taylor's formula along the segments `x → pⱼ`).

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
  (the lumped mass method)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MeasureTheory
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Mesh Feec.Domain ExteriorFibre

variable {n : ℕ}

/-! ### Barycentric coordinates: reproduction, reindexing, integrals -/

/-- **Affine reproduction**: `x = Σᵢ λᵢ(x) pᵢ`. -/
theorem sum_baryCoord_smul {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    (x : Fin n → ℝ) : ∑ i, baryCoord p x i • p i = x := by
  have e : simplexMap p (Matrix.mulVec (edgeMatrix p)⁻¹ (x - p 0)) = x := by
    have : ∀ y, simplexMap p y = Matrix.mulVec (edgeMatrix p) y + p 0 := fun y => by
      funext i; simp [simplexMap, affine_apply, Matrix.mulVec, dotProduct]
    rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hp, Matrix.one_mulVec,
      sub_add_cancel]
  conv_rhs => rw [← e]
  rw [simplexMap_eq_sum]
  rfl

/-- **Reindexing the vertices**: `λ^{p ∘ π}ᵢ = λ^p_{π i}`. -/
theorem baryCoord_comp_perm {p : Fin (n + 1) → Fin n → ℝ} (hp : IsUnit (edgeMatrix p).det)
    (π : Equiv.Perm (Fin (n + 1))) (hpπ : IsUnit (edgeMatrix (p ∘ π)).det) (x : Fin n → ℝ)
    (i : Fin (n + 1)) : baryCoord (p ∘ π) x i = baryCoord p x (π i) := by
  conv_lhs => rw [← sum_baryCoord_smul hp x]
  rw [baryCoord_sum_smul _ univ (sum_baryCoord p x)]
  have hv : ∀ k, baryCoord (p ∘ π) (p k) i = if π.symm k = i then 1 else 0 := fun k => by
    have := baryCoord_vertex hpπ i (π.symm k)
    simpa using this
  simp_rw [hv, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (π i)]
  · simp
  · intro k _ hk
    split_ifs with h
    · exact absurd (by rw [← h]; simp) hk
    · rfl
  · simp

/-- `λ ∘ F_T = λ̂` for the affine map `F_T` of the reference simplex. -/
theorem baryCoord_refMap (T : Affine.Simplex ℝ (Fin n → ℝ) n) (y : Fin n → ℝ) :
    baryCoord T.points (T.refMap y) = refBary y := by
  rw [← simplexMap_eq_refMap, baryCoord_simplexMap (isUnit_det_edgeMatrix T)]

/-- **The integral of a barycentric coordinate**: `∫_T λⱼ = |T| / (n + 1)` (the vertex
quadrature is exact for the `P₁` hat functions). -/
theorem integral_baryCoord (T : Affine.Simplex ℝ (Fin n → ℝ) n) (j : Fin (n + 1)) :
    ∫ x in T.closedInterior, baryCoord T.points x j = volume.real T.closedInterior / (n + 1) := by
  set T' := T.reindex (Equiv.swap 0 j)
  have hpts : T'.points = T.points ∘ Equiv.swap 0 j := by
    funext i; simp [T', Equiv.symm_swap]
  have hbar : ∀ x, baryCoord T'.points x 0 = baryCoord T.points x j := fun x => by
    have := baryCoord_comp_perm (isUnit_det_edgeMatrix T) (Equiv.swap 0 j)
      (hpts ▸ isUnit_det_edgeMatrix T') x 0
    rw [hpts, this, Equiv.swap_apply_left]
  have hT : T'.closedInterior = T.closedInterior := Affine.Simplex.closedInterior_reindex _ _
  have hdet : |LinearMap.det T'.linearPart| = |LinearMap.det T.linearPart| := by
    have h1 := volume_real_closedInterior T
    have h2 := volume_real_closedInterior T'
    rw [hT, h1] at h2
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp at h2
    linarith
  calc ∫ x in T.closedInterior, baryCoord T.points x j
      = ∫ x in T'.closedInterior, baryCoord T'.points x 0 := by
        rw [hT]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hbar x).symm)
    _ = |LinearMap.det T'.linearPart| *
          ∫ y in (Mesh.refSimplex n).closedInterior, (1 - ∑ i, y i) ^ 1 := by
        rw [integral_closedInterior_eq]
        simp [baryCoord_refMap]
    _ = volume.real T.closedInterior / (n + 1) := by
        rw [refSimplex_closedInterior_eq, setIntegral_refSimplex_one_sub_sum_pow, hdet,
          volume_real_closedInterior, Nat.factorial_one, add_comm 1 n, Nat.factorial_succ]
        push_cast
        field_simp

/-! ### The `P₁` interpolant as a Whitney `0`-form -/

/-- The `0`-form `Πₜu dx_∅` of the `P₁` interpolant of the nodal values `u` on `p`. -/
def p1Form (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) : FormField n :=
  fun x => Pi.single ∅ (p1Interp p u x)

/-- The Whitney `0`-form of the vertex `j` is the barycentric coordinate `λⱼ`. -/
theorem whitneyForm_singleton (p : Fin (n + 1) → Fin n → ℝ) (j : Fin (n + 1)) :
    whitneyForm p {j} = fun x => Pi.single ∅ (baryCoord p x j) := by
  funext x s
  simp [whitneyForm, whitneyFibre, sgn, Pi.single_apply, Finset.filter_singleton]

theorem p1Form_eq_sum (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) :
    p1Form p u = ∑ j, u (p j) • whitneyForm p {j} := by
  funext x s
  simp only [p1Form, whitneyForm_singleton, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    p1Interp, Pi.single_apply]
  split_ifs <;> simp

theorem p1Form_mem_whitneySpace (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ) :
    p1Form p u ∈ whitneySpace p 0 := by
  rw [p1Form_eq_sum]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (whitneyForm_mem_whitneySpace p ⟨{j}, card_singleton j⟩)

/-- **The vertex DOF is the evaluation**: `∫_{x} w = w(x)_∅`. -/
theorem whitneyFaceDof_singleton (x : Fin n → ℝ) (w : contForms n) :
    whitneyFaceDof {x} 0 w = (w : FormField n) x ∅ := by
  have hr : refSimplex 0 = Set.univ := by ext y; simp [mem_refSimplex_iff]
  have hq : faceEnum ({x} : Finset (Fin n → ℝ)) (0 + 1) 0 = x := by
    rw [faceEnum_of_lt _ _ (by simp)]
    exact Finset.mem_singleton.1 (Finset.coe_mem _)
  rw [whitneyFaceDof_apply, simplexIntegral, hr, Measure.restrict_univ,
    show (volume : Measure (Fin 0 → ℝ)) = Measure.dirac 0 from Measure.pi_of_empty _ 0,
    integral_dirac, affinePullback_apply, pullback_apply]
  have ha : affine (simplexMatrix (faceEnum ({x} : Finset (Fin n → ℝ)) (0 + 1)))
      (faceEnum ({x} : Finset (Fin n → ℝ)) (0 + 1) 0) 0 = x := by
    funext i; simp [affine_apply, hq]
  rw [ha, Finset.sum_eq_single ∅]
  · simp
  · intro s _ hs
    rw [isDeg_wedgeProd _ s _ ?_, mul_zero]
    rw [Finset.card_univ, Fintype.card_fin]
    exact fun h => hs (Finset.card_eq_zero.1 h.symm)
  · intro h; exact absurd (mem_univ _) h

/-! ### The global `P₁` function -/

/-- `Πₜ` is linear in the nodal values. -/
theorem p1Form_add (p : Fin (n + 1) → Fin n → ℝ) (u w : (Fin n → ℝ) → ℝ) :
    p1Form p (u + w) = p1Form p u + p1Form p w := by
  funext x s
  simp only [p1Form, p1Interp, Pi.add_apply, add_mul, sum_add_distrib, Pi.single_apply]
  split_ifs <;> simp

theorem p1Form_smul (p : Fin (n + 1) → Fin n → ℝ) (c : ℝ) (u : (Fin n → ℝ) → ℝ) :
    p1Form p (c • u) = c • p1Form p u := by
  funext x s
  simp only [p1Form, p1Interp, Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum,
    Pi.single_apply]
  split_ifs <;> simp

/-- The vertex values of the piece: `(Πₜu)(pⱼ) = u(pⱼ)`. -/
theorem whitneyFaceDof_of_eq_p1Form (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : (Fin n → ℝ) → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ vertexSet T) {w : contForms n}
    (hw : (w : FormField n) = p1Form T.points u) : whitneyFaceDof {x} 0 w = u x := by
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 hx
  rw [whitneyFaceDof_singleton, hw]
  simp [p1Form, p1Interp_vertex (isUnit_det_edgeMatrix T)]

/-- **The global `P₁` function** `u_h` with nodal values `u`: the `P₁` interpolants `Πₜu` on the
simplices `T` of `M`, an element of the global Whitney `0`-form (Lagrange `P₁`) space. -/
def p1Global (M : SimplicialMesh n) :
    ((Fin n → ℝ) → ℝ) →ₗ[ℝ] (whitneyElement n).globalSpace M 0 where
  toFun u := ⟨fun T => ⟨p1Form T.1.points u, by exact p1Form_mem_whitneySpace _ _⟩,
    fun T T' g hg hg' i => by
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 i.2
      have hx : x ∈ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) := hg (mem_singleton_self x)
      have hx' : x ∈ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
        hg' (mem_singleton_self x)
      exact (whitneyFaceDof_of_eq_p1Form _ u hx rfl).trans
        (whitneyFaceDof_of_eq_p1Form _ u hx' rfl).symm⟩
  map_add' u w := Subtype.ext (funext fun T => Subtype.ext (p1Form_add _ u w))
  map_smul' c u := Subtype.ext (funext fun T => Subtype.ext (p1Form_smul _ c u))

theorem p1Global_apply (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ) (T : M.simplices) :
    (((p1Global M u : (whitneyElement n).Piecewise M 0) T : FormField n)) =
      p1Form T.1.points u := rfl

/-- **Every global `P₁` function is `p1Global` of its nodal values.** -/
theorem exists_p1Global_eq (M : SimplicialMesh n) (v : (whitneyElement n).globalSpace M 0) :
    ∃ u : (Fin n → ℝ) → ℝ, p1Global M u = v := by
  classical
  set V : (whitneyElement n).Piecewise M 0 := (v : (whitneyElement n).Piecewise M 0)
  have hval : ∀ (T : M.simplices) {x : Fin n → ℝ}
      (hx : x ∈ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)),
      (whitneyElement n).localDof T 0 {x} ⟨(), card_singleton x⟩ (V T) = (V T : FormField n) x ∅ :=
    fun T x _ => whitneyFaceDof_singleton x _
  refine ⟨fun x => if h : ∃ T : M.simplices, x ∈ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    then (V h.choose : FormField n) x ∅ else 0, ?_⟩
  refine Subtype.ext (funext fun T => (whitneyElement n).localSpace_ext T 0 fun g hg i => ?_)
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 i.2
  have hx : x ∈ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) := hg (mem_singleton_self x)
  have hex : ∃ T : M.simplices, x ∈ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) := ⟨T, hx⟩
  refine (whitneyFaceDof_of_eq_p1Form _ _ hx rfl).trans ?_
  obtain rfl : i = ⟨(), card_singleton x⟩ := Subtype.ext rfl
  rw [dite_eq_left_of_eq_true (eq_true hex), ← hval _ hex.choose_spec]
  exact v.2 _ _ _ (singleton_subset_iff.2 hex.choose_spec) (singleton_subset_iff.2 hx) _

/-- **`p1Global M u` is determined by the values of `u` at the vertices** of `M`, and determines
them. -/
theorem p1Global_eq_p1Global_iff (M : SimplicialMesh n) {u w : (Fin n → ℝ) → ℝ} :
    p1Global M u = p1Global M w ↔ ∀ T ∈ M.simplices, ∀ x ∈ vertexSet T, u x = w x := by
  refine ⟨fun h T hT x hx => ?_, fun h => Subtype.ext (funext fun T => Subtype.ext ?_)⟩
  · have h1 := congrArg (fun v : (whitneyElement n).globalSpace M 0 =>
      (whitneyElement n).localDof (⟨T, hT⟩ : M.simplices) 0 {x} ⟨(), card_singleton x⟩
        ((v : (whitneyElement n).Piecewise M 0) ⟨T, hT⟩)) h
    exact (whitneyFaceDof_of_eq_p1Form _ u hx rfl).symm.trans
      (h1.trans (whitneyFaceDof_of_eq_p1Form _ w hx rfl))
  · change p1Form _ u = p1Form _ w
    rw [p1Form_eq_sum, p1Form_eq_sum]
    exact sum_congr rfl fun j _ => by rw [h _ T.2 _ (mem_vertexSet.2 ⟨j, rfl⟩)]

/-- **`u_h ∈ P̊₁⁻Λ⁰(M)` iff `u` vanishes at the vertices on the boundary** of `cl Ω`: the
boundary vertices are the vertices of the boundary facets
(`StarGeom.exists_isBoundaryFacet_of_mem_vertexSet`). -/
theorem p1Global_mem_globalSpace₀_iff (M : SimplicialMesh n) (u : (Fin n → ℝ) → ℝ) :
    (p1Global M u : (whitneyElement n).Piecewise M 0) ∈ (whitneyElement n).globalSpace₀ M 0 ↔
      ∀ T ∈ M.simplices, ∀ x ∈ vertexSet T, x ∈ frontier (closure M.domain) → u x = 0 := by
  constructor
  · intro h T hT x hx hxf
    obtain ⟨F, hF, hxF⟩ := StarGeom.exists_isBoundaryFacet_of_mem_vertexSet hT hx hxf
    obtain ⟨T', hT', hFT'⟩ := hF.1.2
    exact (whitneyFaceDof_of_eq_p1Form _ u (hFT' hxF) rfl).symm.trans
      (h.2 ⟨T', hT'⟩ F hF hFT' {x} (singleton_subset_iff.2 hxF) ⟨(), card_singleton x⟩)
  · refine fun h => ⟨(p1Global M u).2, fun T F hF hFT g hg i => ?_⟩
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 i.2
    have hxF : x ∈ F := hg (mem_singleton_self x)
    exact (whitneyFaceDof_of_eq_p1Form _ u (hFT hxF) rfl).trans
      (h T T.2 x (hFT hxF) (hF.2.2 (subset_convexHull ℝ _ (Finset.mem_coe.2 hxF))))

/-- `x` **enumerates the free vertices** of `M`: injectively, the vertices of `M` off the
boundary of `cl Ω`. -/
def IsFreeVertexEnum {ι : Type*} (M : SimplicialMesh n) (x : ι → Fin n → ℝ) : Prop :=
  Function.Injective x ∧ ∀ y, y ∈ Set.range x ↔
    (∃ T ∈ M.simplices, y ∈ vertexSet T) ∧ y ∉ frontier (closure M.domain)

section Nodes

variable {ι : Type*} [Fintype ι] (M : SimplicialMesh n) {x : ι → Fin n → ℝ}

theorem nodalFun_eq_zero_of_mem_frontier (hx : IsFreeVertexEnum M x) (U : ι → ℝ)
    {y : Fin n → ℝ} (hy : y ∈ frontier (closure M.domain)) : nodalFun x U y = 0 :=
  sum_eq_zero fun i _ => ite_eq_right_iff.2 fun e => (((hx.2 y).1 ⟨i, e⟩).2 hy).elim

/-- The global `P₁` function with the values `U` at the free vertices, `0` at the boundary
vertices: an element of `P̊₁⁻Λ⁰(M)`. -/
def p1Global₀ (hx : IsFreeVertexEnum M x) :
    (ι → ℝ) →ₗ[ℝ] (whitneyElement n).globalSpace₀ M 0 where
  toFun U := ⟨p1Global M (nodalFun x U), (p1Global_mem_globalSpace₀_iff M _).2
    fun _ _ _ _ hy => nodalFun_eq_zero_of_mem_frontier M hx U hy⟩
  map_add' U V := Subtype.ext (by
    simp only [nodalFun_eq_sum, Pi.add_apply, add_smul, sum_add_distrib, map_add,
      Submodule.coe_add])
  map_smul' c U := Subtype.ext (by
    simp only [nodalFun_eq_sum, Pi.smul_apply, smul_eq_mul, mul_smul, ← smul_sum, map_smul,
      Submodule.coe_smul, RingHom.id_apply])

theorem p1Global₀_apply (hx : IsFreeVertexEnum M x) (U : ι → ℝ) :
    (p1Global₀ M hx U : (whitneyElement n).Piecewise M 0) = p1Global M (nodalFun x U) := rfl

/-- **The nodal values at the free vertices are a linear isomorphism** `ℝ^ι ≃ P̊₁⁻Λ⁰(M)`: every
`P₁` function with vanishing boundary DOFs is `p1Global` of its values at the free vertices,
`0` at the boundary vertices. -/
def p1GlobalEquiv₀ (hx : IsFreeVertexEnum M x) :
    (ι → ℝ) ≃ₗ[ℝ] (whitneyElement n).globalSpace₀ M 0 := by
  refine LinearEquiv.ofBijective (p1Global₀ M hx) ⟨fun U V hUV => funext fun i => ?_, fun v => ?_⟩
  · obtain ⟨T, hT, hiT⟩ := ((hx.2 (x i)).1 ⟨i, rfl⟩).1
    have := (p1Global_eq_p1Global_iff (u := nodalFun x U) (w := nodalFun x V) M).1
      (Subtype.ext congr($hUV.1)) T hT _ hiT
    rwa [nodalFun_apply hx.1, nodalFun_apply hx.1] at this
  · obtain ⟨u, hu⟩ := exists_p1Global_eq M ⟨v, v.2.1⟩
    have h0 := (p1Global_mem_globalSpace₀_iff M u).1 (by rw [hu]; exact v.2)
    refine ⟨fun i => u (x i), Subtype.ext ?_⟩
    rw [p1Global₀_apply, ← congrArg Subtype.val hu]
    refine congrArg Subtype.val ((p1Global_eq_p1Global_iff M).2 fun T hT y hy => ?_)
    by_cases hyf : y ∈ frontier (closure M.domain)
    · rw [nodalFun_eq_zero_of_mem_frontier M hx _ hyf, h0 T hT y hy hyf]
    · obtain ⟨i, rfl⟩ := (hx.2 y).2 ⟨⟨T, hT, hy⟩, hyf⟩
      exact nodalFun_apply hx.1 _ i

theorem p1GlobalEquiv₀_apply (hx : IsFreeVertexEnum M x) (U : ι → ℝ) :
    (p1GlobalEquiv₀ M hx U : (whitneyElement n).Piecewise M 0) = p1Global M (nodalFun x U) :=
  rfl

end Nodes

/-! ### Inner products of glued piecewise fields -/

/-- The product of piecewise functions is piecewise. -/
theorem pieceFun_mul (M : SimplicialMesh n)
    (v w : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    pieceFun M v x * pieceFun M w x = pieceFun M (fun T x => v T x * w T x) x := by
  by_cases hx : ∃ T ∈ M.simplices, x ∈ interior T.closedInterior
  · obtain ⟨T, hT, hxT⟩ := hx
    rw [pieceFun_of_mem_interior M v hT hxT, pieceFun_of_mem_interior M w hT hxT,
      pieceFun_of_mem_interior M _ hT hxT]
  · push Not at hx
    have h0 : ∀ u : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → ℝ, pieceFun M u x = 0 :=
      fun u => Finset.sum_eq_zero fun T hT => Set.indicator_of_notMem (hx T hT) _
    rw [h0, h0, h0, mul_zero]

/-- `∫_S Σ_T 𝟙_{int T} v_T = Σ_T ∫_T v_T` when the interiors of the elements lie in `S`. -/
theorem setIntegral_pieceFun (M : SimplicialMesh n)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → ℝ}
    (hv : ∀ T ∈ M.simplices, Continuous (v T)) {S : Set (Fin n → ℝ)}
    (hTS : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ S) :
    ∫ x in S, pieceFun M v x = ∑ T ∈ M.simplices, ∫ x in T.closedInterior, v T x := by
  have hint : ∀ T ∈ M.simplices, IntegrableOn (v T) T.closedInterior :=
    fun T hT => (hv T hT).continuousOn.integrableOn_compact T.isCompact_closedInterior
  simp only [pieceFun]
  rw [integral_finsetSum _ fun T hT => ((integrable_indicator_iff
    isOpen_interior.measurableSet).2 ((hint T hT).mono_set interior_subset)).restrict]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [integral_indicator isOpen_interior.measurableSet, Measure.restrict_restrict
    isOpen_interior.measurableSet, Set.inter_eq_left.2 (hTS T hT)]
  exact setIntegral_congr_set (interior_ae_eq_of_null_frontier (μ := volume)
    (s := T.closedInterior) (Convex.addHaar_frontier volume (Feec.Mesh.convex_closedInterior T)))

/-- `⟪u, w⟫_{L²(S)} = Σ_T Σᵢ ∫_T (u_T)ᵢ (w_T)ᵢ` for piecewise continuous fields, when the interiors
of the elements lie in `S`. -/
theorem inner_pieceL2 (M : SimplicialMesh n) {ι : Type*} [Fintype ι] {S : Set (Fin n → ℝ)}
    (hTS : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ S)
    {v w : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → ℝ}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i))
    (hw : ∀ T ∈ M.simplices, ∀ i, Continuous (w T i)) :
    ⟪pieceL2 M S v hv, pieceL2 M S w hw⟫_ℝ =
      ∑ T ∈ M.simplices, ∑ i, ∫ x in T.closedInterior, v T i x * w T i x := by
  rw [show pieceL2 M S w hw = toL2F fun i =>
    memLp_pieceFun M (v := fun T => w T i) (fun T hT => hw T hT i) S from rfl, inner_toL2F,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← setIntegral_pieceFun M (v := fun T x => v T i x * w T i x)
    (fun T hT => (hv T hT i).mul (hw T hT i)) hTS]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_pieceL2 M S v hv i] with x hx
  rw [hx, starRingEnd_apply, star_trivial, pieceFun_mul]

/-! ### The stiffness form and the lumped mass as integrals -/

/-- `Σ_{s ∈ Λ¹} F(s) = Σⱼ F({j})`. -/
theorem sum_formIdx_one {X : Type*} [AddCommMonoid X] (F : Finset (Fin n) → X) :
    ∑ s : formIdx n (((0 : ℕ) : ℤ) + 1), F s.1 = ∑ j, F {j} := by
  refine (Fintype.sum_equiv (Equiv.ofBijective (fun j : Fin n =>
    (⟨{j}, by simp⟩ : formIdx n (((0 : ℕ) : ℤ) + 1))) ⟨fun i j h => by
      simpa using congrArg Subtype.val h, fun s => ?_⟩) _ _ fun j => rfl).symm
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 (by have := s.2; push_cast at this; exact_mod_cast this)
  exact ⟨j, Subtype.ext hj.symm⟩

/-- `Σ_{s ∈ Λ⁰} F(s) = F(∅)`. -/
theorem sum_formIdx_zero {X : Type*} [AddCommMonoid X] (F : Finset (Fin n) → X) :
    ∑ s : formIdx n ((0 : ℕ) : ℤ), F s.1 = F ∅ := by
  rw [Fintype.sum_eq_single ⟨∅, by simp⟩]
  intro s hs
  have h := s.2
  push_cast at h
  exact absurd (Subtype.ext (Finset.card_eq_zero.1 (by exact_mod_cast h))) hs

/-- `∂ⱼ Πₜu = (∇Πₜu)ⱼ`. -/
theorem partialDeriv_p1Interp (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ)
    (j : Fin n) (x : Fin n → ℝ) : partialDeriv j (p1Interp p u) x = p1Grad p u j := by
  have e : p1Interp p u = fun y => ∑ l, p1Grad p u l * y l + p1Interp p u 0 := by
    funext y
    have := p1Interp_sub p u y 0
    rw [sub_zero] at this
    rw [show ∑ l, p1Grad p u l * y l = p1Grad p u ⬝ᵥ y from rfl, ← this]
    ring
  rw [e]
  exact congrFun (grad_affine (p1Grad p u) (p1Interp p u 0) x) j

/-- `d Πₜu = Σⱼ (∇Πₜu)ⱼ dxⱼ`. -/
theorem extDeriv_p1Form_singleton (p : Fin (n + 1) → Fin n → ℝ) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (j : Fin n) : extDeriv (p1Form p u) x {j} = p1Grad p u j := by
  rw [extDeriv_apply, Finset.sum_singleton, Finset.erase_singleton]
  simp only [sgn, Finset.filter_singleton, lt_irrefl, ite_false, card_empty, pow_zero, one_mul]
  simpa [p1Form] using partialDeriv_p1Interp p u j x

/-- **The global `P₁` functions in `L²(Ω)`**: `⟪u_h, w_h⟫ = Σ_T ∫_T Πₜu Πₜw`. -/
theorem inner_glue_p1Global (M : SimplicialMesh n)
    (hM : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) (u w : (Fin n → ℝ) → ℝ) :
    ⟪(whitneyElement n).glue M (0 : ℕ) (p1Global M u : (whitneyElement n).Piecewise M 0),
      (whitneyElement n).glue M (0 : ℕ) (p1Global M w : (whitneyElement n).Piecewise M 0)⟫_ℝ =
      ∑ T ∈ M.simplices,
        ∫ x in T.closedInterior, p1Interp T.points u x * p1Interp T.points w x := by
  rw [LocalElement.glue_apply, LocalElement.glue_apply, inner_pieceL2 M hM]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [← integral_finsetSum _ fun s _ => ?_]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [formComp, LocalElement.extendPW_of_mem _ _ _ hT]
    refine (sum_formIdx_zero (fun s => p1Form T.points u x s * p1Form T.points w x s)).trans ?_
    simp [p1Form]
  · exact ((continuous_formComp ((whitneyElement n).contDiff_extendPW M _ hT).continuous s).mul
      (continuous_formComp ((whitneyElement n).contDiff_extendPW M _ hT).continuous s)).continuousOn
      |>.integrableOn_compact T.isCompact_closedInterior

/-- **The stiffness form is the Dirichlet form of the global `P₁` space**:
`a(u, w) = ⟪d u_h, d w_h⟫_{L²Λ¹(Ω)} = ∫_Ω ∇u_h · ∇w_h`, `d` elementwise. -/
theorem inner_glue_dPiecewise_p1Global (M : SimplicialMesh n)
    (hM : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) (u w : (Fin n → ℝ) → ℝ) :
    ⟪(whitneyElement n).glue M (((0 : ℕ) : ℤ) + 1)
        ((whitneyElement n).dPiecewise M 0 (p1Global M u)),
      (whitneyElement n).glue M (((0 : ℕ) : ℤ) + 1)
        ((whitneyElement n).dPiecewise M 0 (p1Global M w))⟫_ℝ = p1Stiffness M u w := by
  rw [LocalElement.glue_apply, LocalElement.glue_apply, inner_pieceL2 M hM, p1Stiffness]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [← integral_finsetSum _ fun s _ => ?_]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [formComp, LocalElement.extendPW_of_mem _ _ _ hT]
    refine (sum_formIdx_one (fun s => extDeriv (p1Form T.points u) x s *
      extDeriv (p1Form T.points w) x s)).trans ?_
    simp only [extDeriv_p1Form_singleton, dotProduct]
  · exact ((continuous_formComp ((whitneyElement n).contDiff_extendPW M _ hT).continuous s).mul
      (continuous_formComp ((whitneyElement n).contDiff_extendPW M _ hT).continuous s)).continuousOn
      |>.integrableOn_compact T.isCompact_closedInterior

/-- **The stiffness form is the Dirichlet form of the `L²` de Rham complex** on the global `P₁`
space: `u_h ∈ D(d)` and `a(u, w) = ⟪d u_h, d w_h⟫_{L²Λ¹(Ω)}` (`Ω` open). -/
theorem inner_maximal_p1Global [NeZero n] (M : SimplicialMesh n) (hΩ : IsOpen M.domain)
    (hM : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) (u w : (Fin n → ℝ) → ℝ) :
    ∃ (hu : (whitneyElement n).glue M (0 : ℕ) (p1Global M u : (whitneyElement n).Piecewise M 0) ∈
        ((extDerivOp ℝ n (0 : ℕ)).maximal M.domain).domain)
      (hw : (whitneyElement n).glue M (0 : ℕ) (p1Global M w : (whitneyElement n).Piecewise M 0) ∈
        ((extDerivOp ℝ n (0 : ℕ)).maximal M.domain).domain),
      ⟪(extDerivOp ℝ n (0 : ℕ)).maximal M.domain ⟨_, hu⟩,
        (extDerivOp ℝ n (0 : ℕ)).maximal M.domain ⟨_, hw⟩⟫_ℝ = p1Stiffness M u w := by
  obtain ⟨hu, eu⟩ := (whitneyElement n).glue_mem_maximal M hΩ 0 (p1Global M u)
  obtain ⟨hw, ew⟩ := (whitneyElement n).glue_mem_maximal M hΩ 0 (p1Global M w)
  exact ⟨hu, hw, by rw [eu, ew]; exact inner_glue_dPiecewise_p1Global M hM u w⟩

theorem continuous_baryCoord (p : Fin (n + 1) → Fin n → ℝ) (j : Fin (n + 1)) :
    Continuous fun x => baryCoord p x j := by
  have e : (fun x => baryCoord p x j) = fun x => ∑ l, baryGrad p j l * x l + baryCoord p 0 j :=
    funext fun x => baryCoord_apply p x j
  rw [e]
  fun_prop

/-- `Πₜ 1 = 1`. -/
theorem p1Interp_one (p : Fin (n + 1) → Fin n → ℝ) (x : Fin n → ℝ) :
    p1Interp p (fun _ => 1) x = 1 := by
  simp [p1Interp, sum_baryCoord]

/-- **The lumped mass is the integral of the hat function**: `m(x) = ⟪φₓ, 1⟫_{L²(Ω)} = ∫_Ω φₓ`,
the row sum `Σ_y ⟪φₓ, φ_y⟫` of the consistent mass matrix (`1 = Σ_y φ_y` in `P₁`): the vertex
quadrature of `Feec.FiniteElement.lumpedMass` is exact for the hat functions. [Thomee2006],
Ch. 15 -/
theorem inner_glue_p1Global_nodalIndicator_one (M : SimplicialMesh n)
    (hM : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) (x : Fin n → ℝ) :
    ⟪(whitneyElement n).glue M (0 : ℕ)
        (p1Global M (nodalIndicator x) : (whitneyElement n).Piecewise M 0),
      (whitneyElement n).glue M (0 : ℕ)
        (p1Global M (fun _ => 1) : (whitneyElement n).Piecewise M 0)⟫_ℝ = lumpedMass M x := by
  rw [inner_glue_p1Global M hM, lumpedMass]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [p1Interp_one, mul_one]
  simp only [p1Interp]
  rw [integral_finsetSum univ (f := fun j y => nodalIndicator x (T.points j) *
    baryCoord T.points y j) fun j _ => ((continuous_const.mul
    (continuous_baryCoord T.points j)).continuousOn.integrableOn_compact
      T.isCompact_closedInterior)]
  simp_rw [integral_const_mul, integral_baryCoord, nodalIndicator, ite_mul, one_mul, zero_mul,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The interiors of the simplices of a Freudenthal mesh lie in the open box. -/
theorem interior_subset_freudenthalMesh_domain (b : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ)
    [NeZero N] {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (freudenthalMesh b s hs N).simplices) :
    interior T.closedInterior ⊆ (freudenthalMesh b s hs N).domain := by
  refine (interior_mono ((freudenthalMesh b s hs N).closedInterior_subset_closure hT)).trans ?_
  rw [freudenthalMesh_domain, closure_pi_set, interior_pi_set Set.finite_univ]
  intro x hx i hi
  have := hx i hi
  simp only at this ⊢
  rwa [closure_Ioo (by linarith : b i ≠ b i + s), interior_Icc] at this

/-! ### Linearity of the stiffness form -/

section MaxNorm

open Set

/-! ### The `P₁` interpolant in the maximum norm -/

/-- **A `P₁` function attains its maximum modulus at a vertex**: on `T`,
`|Πₜu(x)| ≤ maxⱼ |u(pⱼ)|`. -/
theorem abs_p1Interp_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) {u : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hB : ∀ j, |u (T.points j)| ≤ B) {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    |p1Interp T.points u x| ≤ B := by
  rw [p1Interp]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |u (T.points j) * baryCoord T.points x j|
      ≤ ∑ j, B * baryCoord T.points x j := sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (baryCoord_mem_Icc T hx j).1]
        exact mul_le_mul_of_nonneg_right (hB j) (baryCoord_mem_Icc T hx j).1
    _ = B := by rw [← mul_sum, sum_baryCoord, mul_one]

theorem p1Interp_sub_values (p : Fin (n + 1) → Fin n → ℝ) (u w : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    p1Interp p (u - w) x = p1Interp p u x - p1Interp p w x := by
  simp [p1Interp, sub_mul, sum_sub_distrib]

/-- **The `P₁` interpolation error in the maximum norm**: for `f ∈ C²` with
`|∂ᵢ∂ₖ f| ≤ D` on `T` and `|y - z|_∞ ≤ δ` on `T`, `|f(x) - Πₜf(x)| ≤ n² D δ² / 2` on `T`
(Taylor's formula along the segments `x → pⱼ`; `Σⱼ λⱼ(x)(pⱼ - x) = 0`). -/
theorem abs_sub_p1Interp_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) {D δ : ℝ}
    (hD : ∀ y ∈ T.closedInterior, ∀ i k, |partialDeriv k (partialDeriv i f) y| ≤ D)
    (hδ : ∀ y ∈ T.closedInterior, ∀ z ∈ T.closedInterior, dist y z ≤ δ)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    |f x - p1Interp T.points f x| ≤ n ^ 2 * D * δ ^ 2 / 2 := by
  have hT := isUnit_det_edgeMatrix T
  have hconv := convex_closedInterior T
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : ∀ i, Differentiable ℝ (partialDeriv i f) := fun i =>
    (hf.partialDeriv (m := 1) (by norm_num) i).differentiable (by norm_num)
  have hp : ∀ j, T.points j ∈ T.closedInterior := fun j => by
    rw [← Affine.Simplex.convexHull_eq_closedInterior]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  set v : Fin (n + 1) → Fin n → ℝ := fun j => T.points j - x
  have hseg : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, x + t • v j ∈ T.closedInterior := fun j t ht => by
    have := hconv.add_smul_sub_mem hx (hp j) ht
    simpa [v] using this
  have hv : ∀ j i, |v j i| ≤ δ := fun j i =>
    ((norm_le_pi_norm (v j) i).trans (by
      rw [show v j = T.points j - x from rfl, ← dist_eq_norm]
      exact hδ _ (hp j) _ hx))
  have hR : ∀ j, |f (T.points j) - f x - ∑ i, v j i * partialDeriv i f x| ≤
      n ^ 2 * D * δ ^ 2 / 2 := fun j => by
    have e1 : x + v j = T.points j := by simp [v]
    have := abs_taylor_one_le (g := fun t => f (x + t • v j))
      (g₁ := fun t => ∑ i, v j i * partialDeriv i f (x + t • v j))
      (g₂ := fun t => ∑ i, v j i * ∑ k, v j k * partialDeriv k (partialDeriv i f) (x + t • v j))
      (M := n ^ 2 * D * δ ^ 2)
      (fun t _ => hasDerivAt_comp_line (hd1 _))
      (fun t _ => HasDerivAt.fun_sum fun i _ =>
        (hasDerivAt_comp_line ((hd2 i) _)).const_mul (v j i))
      (fun t ht => by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |v j i * ∑ k, v j k * partialDeriv k (partialDeriv i f) (x + t • v j)|
            ≤ ∑ _i : Fin n, ∑ _k : Fin n, δ * (δ * D) := sum_le_sum fun i _ => by
              rw [abs_mul]
              refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans ?_
              rw [mul_sum]
              refine sum_le_sum fun k _ => ?_
              rw [abs_mul]
              have h0 : 0 ≤ δ := (abs_nonneg _).trans (hv j i)
              exact mul_le_mul (hv j i) (mul_le_mul (hv j k) (hD _ (hseg j t ht) i k)
                (abs_nonneg _) h0) (by positivity) h0
          _ = n ^ 2 * D * δ ^ 2 := by simp; ring)
    simpa [e1] using this
  have hsum : ∑ j, baryCoord T.points x j * ∑ i, v j i * partialDeriv i f x = 0 := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_eq_zero fun i _ => ?_
    have h0 : ∑ j, baryCoord T.points x j * v j i = 0 := by
      have := congrFun (sum_baryCoord_smul hT x) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [v, Pi.sub_apply, mul_sub, sum_sub_distrib, ← sum_mul, sum_baryCoord, this,
        one_mul, sub_self]
    simp_rw [← mul_assoc]
    rw [← sum_mul, h0, zero_mul]
  have e : f x - p1Interp T.points f x = -∑ j, baryCoord T.points x j *
      (f (T.points j) - f x - ∑ i, v j i * partialDeriv i f x) := by
    simp only [p1Interp, mul_sub, sum_sub_distrib, hsum, ← sum_mul, sum_baryCoord, one_mul]
    simp_rw [mul_comm (baryCoord T.points x _)]
    ring
  rw [e, abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |baryCoord T.points x j * (f (T.points j) - f x - ∑ i, v j i * partialDeriv i f x)|
      ≤ ∑ j, baryCoord T.points x j * (n ^ 2 * D * δ ^ 2 / 2) := sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (baryCoord_mem_Icc T hx j).1]
        exact mul_le_mul_of_nonneg_left (hR j) (baryCoord_mem_Icc T hx j).1
    _ = _ := by rw [← sum_mul, sum_baryCoord, one_mul]

end MaxNorm

end Feec.FiniteElement
