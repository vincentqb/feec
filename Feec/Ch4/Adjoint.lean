import Feec.Foundation

/-!
# Unbounded operators: adjoints, graph relations, closed range (Thesis §4.1–4.2)

This module supplies the unbounded-operator facts that the thesis states without proof in §4.1
and uses throughout Chapter 4. Real Hilbert spaces throughout; `T†` is Mathlib's
`LinearPMap.adjoint`, and all statements carry `Dense T.domain` explicitly (Mathlib's adjoint
takes a junk value otherwise).

## Coverage

* **Graph relations** (§4.1): `graph_orthogonal` (`Γ(T)ᗮ = Γ̃(T*)`), `closure_graph`
  (`cl Γ(T) = Γ̃(T*)ᗮ`), `graph_eq_orthogonal` (`Γ(T) = Γ̃(T*)ᗮ` for closed `T`), with the
  rotated graph `Γ̃(T*) = {(x, y) | (y, -x) ∈ Γ(T*)}` taken in `E ⊕₂ F`.
* **Closed kernels**: `isClosed_ker`; the thesis' unrestricted claim (§4.3) is refuted by
  `exists_not_isClosed_ker`.
* `dense_adjoint_domain` (`D(T*)` dense) and `adjoint_adjoint` (`T** = T`), for closed densely
  defined `T`.
* **(4.1a–d)**: (4.1a) is `Feec.orth_range_eq_ker_adjoint` (foundation); (4.1b)
  `orthogonal_ker`, (4.1c) `orthogonal_range_adjoint`, (4.1d) `orthogonal_ker_adjoint`.
* **Closed range theorem**: `range_adjoint_eq_orthogonal_ker` (`R(T) closed ⇒ R(T*) = N(T)ᗮ`),
  `isClosed_range_adjoint_iff`, `range_eq_orthogonal_ker_adjoint`; the unbounded Poincaré
  inequality `poincare_of_isClosed_range` and its converse `isClosed_range_of_poincare`, combined
  in `isClosed_range_iff_poincare` (Thm 4.2, W-level form).
* **Skew-adjointness**: `IsSkewAdjoint.dense_domain`, `isSkewAdjoint_iff` (skew-symmetric and
  `D(T*) ⊂ D(T)`).
* **Dual complex** (§4.2): `HilbertComplex2.dual` (with `dual_dual`), `closedRange_dual_iff`
  ("closed ⇒ dual closed") and `range_adjoint_d0_eq` / `range_adjoint_d1_eq` (`B* = Zᗮ`).
-/

open scoped RealInnerProductSpace
open Set LinearPMap

noncomputable section

namespace Feec

/-! ### Closed kernels -/

section Kernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `N(T) = {x | (x, 0) ∈ Γ(T)}` (auxiliary, Thesis §4.1). -/
theorem ker_eq_preimage_graph (T : E →ₗ.[ℝ] F) :
    (T.ker : Set E) = (fun x => (x, (0 : F))) ⁻¹' (T.graph : Set (E × F)) := by
  ext x
  simp only [SetLike.mem_coe, mem_preimage, LinearPMap.mem_ker_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩; exact ⟨y, rfl, hy⟩
  · rintro ⟨y, hy, hy0⟩; exact ⟨y, hy.symm, hy0⟩

/-- The kernel of a **closed** unbounded operator is closed.

Thesis §4.2 (`Zᵏ` closed, used for `W = Z ⊕ Zᗮ`) and §4.3 (constraint propagation into `ker M`).
Thesis gap: the thesis (§4.3) asserts this for every "not-necessarily-bounded linear operator";
closedness of `T` is needed (see `exists_not_isClosed_ker`). -/
theorem isClosed_ker {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) : IsClosed (T.ker : Set E) := by
  rw [ker_eq_preimage_graph]
  exact hc.preimage (continuous_id.prodMk continuous_const)

end Kernel

/-! ### Graph relations, `T** = T`, (4.1a–d) -/

section Adjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The graph `Γ(T)` as a subspace of the Hilbert sum `E ⊕₂ F`. -/
def graphL2 (T : E →ₗ.[ℝ] F) : Submodule ℝ (WithLp 2 (E × F)) :=
  T.graph.comap (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap

/-- The rotated graph of the adjoint, `Γ̃(T*) = {(x, y) | (y, -x) ∈ Γ(T*)}` (Thesis §4.1),
as a subspace of `E ⊕₂ F`. -/
def rotAdjGraph (T : E →ₗ.[ℝ] F) : Submodule ℝ (WithLp 2 (E × F)) :=
  T†.graph.comap (((LinearMap.snd ℝ E F).prod (-LinearMap.fst ℝ E F)).comp
    (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Membership in `graphL2` (auxiliary, Thesis §4.1). -/
theorem mem_graphL2 {T : E →ₗ.[ℝ] F} {p : WithLp 2 (E × F)} :
    p ∈ graphL2 T ↔ WithLp.ofLp p ∈ T.graph := Iff.rfl

omit [CompleteSpace F] in
/-- Membership in the rotated graph `Γ̃(T*)` (auxiliary, Thesis §4.1). -/
theorem mem_rotAdjGraph {T : E →ₗ.[ℝ] F} {p : WithLp 2 (E × F)} :
    p ∈ rotAdjGraph T ↔ ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) ∈ T†.graph := Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- A closed operator has closed graph in `E ⊕₂ F` (auxiliary, Thesis §4.1). -/
theorem isClosed_graphL2 {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) :
    IsClosed (graphL2 T : Set (WithLp 2 (E × F))) :=
  hc.preimage (WithLp.prod_continuous_ofLp 2 E F)

omit [CompleteSpace F] in
/-- Graph relation `Γ(T)ᗮ = Γ̃(T*)` (Thesis §4.1), for densely defined `T`.

Thesis gap: stated without proof; the orthogonal complement is in the ℓ² sum `E ⊕₂ F`. -/
theorem graph_orthogonal (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    (graphL2 T)ᗮ = rotAdjGraph T := by
  ext p
  rw [Submodule.mem_orthogonal, mem_rotAdjGraph, LinearPMap.mem_graph_iff]
  constructor
  · intro h
    have key : ∀ x : T.domain, ⟪-(WithLp.ofLp p).1, (x : E)⟫ = ⟪(WithLp.ofLp p).2, T x⟫ := by
      intro x
      have := h (WithLp.toLp 2 ((x : E), T x)) (by simp [mem_graphL2])
      simp only [WithLp.prod_inner_apply] at this
      rw [inner_neg_left]
      linarith [real_inner_comm (x : E) (WithLp.ofLp p).1,
        real_inner_comm (T x) (WithLp.ofLp p).2]
    have hmem := mem_adjoint_domain_of_exists _ ⟨_, key⟩
    exact ⟨⟨_, hmem⟩, rfl, adjoint_apply_eq hT ⟨_, hmem⟩ key⟩
  · rintro ⟨y, hy, hTy⟩ u hu
    rw [mem_graphL2, LinearPMap.mem_graph_iff] at hu
    obtain ⟨x, hx, hTx⟩ := hu
    have h := adjoint_isFormalAdjoint hT y x
    rw [hTy, hy, inner_neg_left] at h
    rw [WithLp.prod_inner_apply, ← hx, ← hTx]
    linarith [real_inner_comm (x : E) (WithLp.ofLp p).1,
        real_inner_comm (T x) (WithLp.ofLp p).2]

/-- `cl Γ(T) = Γ̃(T*)ᗮ` (Thesis §4.1, second graph relation; garbled in the extracted text). -/
theorem closure_graph (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    (graphL2 T).topologicalClosure = (rotAdjGraph T)ᗮ := by
  rw [← graph_orthogonal T hT, Submodule.orthogonal_orthogonal_eq_closure]

/-- `Γ(T) = Γ̃(T*)ᗮ` for closed densely defined `T` (Thesis §4.1, third graph relation). -/
theorem graph_eq_orthogonal (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : graphL2 T = (rotAdjGraph T)ᗮ := by
  rw [← closure_graph T hT, (isClosed_graphL2 hc).submodule_topologicalClosure_eq]

/-- Weak characterisation of the graph of a closed densely defined operator:
`(x, y) ∈ Γ(T)` iff `⟪T* w, x⟫ = ⟪w, y⟫` for all `w ∈ D(T*)` (Thesis §4.1, the relation
`Γ(T) = Γ̃(T*)ᗮ` unpacked). -/
theorem mem_graph_iff_of_isClosed {T : E →ₗ.[ℝ] F} (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) {x : E} {y : F} :
    (x, y) ∈ T.graph ↔ ∀ w : T†.domain, ⟪T† w, x⟫ = ⟪(w : F), y⟫ := by
  have h : (x, y) ∈ T.graph ↔ WithLp.toLp 2 (x, y) ∈ (rotAdjGraph T)ᗮ := by
    rw [← graph_eq_orthogonal T hT hc, mem_graphL2, WithLp.ofLp_toLp]
  rw [h, Submodule.mem_orthogonal]
  constructor
  · intro H w
    have := H (WithLp.toLp 2 (-(T† w), (w : F))) (by
      rw [mem_rotAdjGraph, LinearPMap.mem_graph_iff]
      exact ⟨w, by simp⟩)
    simp only [WithLp.prod_inner_apply, inner_neg_left] at this
    linarith
  · intro H u hu
    rw [mem_rotAdjGraph, LinearPMap.mem_graph_iff] at hu
    obtain ⟨w, hw, hTw⟩ := hu
    simp only at hw hTw
    have hu1 : (WithLp.ofLp u).1 = -(T† w) := by rw [hTw, neg_neg]
    simp only [WithLp.prod_inner_apply]
    rw [hu1, ← hw, inner_neg_left, H w]
    ring

/-- The adjoint of a closed densely defined operator is densely defined (Thesis §4.1).

Thesis gap: the thesis' one-line argument is made precise: `y ⊥ D(T*)` gives
`(0, y) ∈ Γ̃(T*)ᗮ = Γ(T)`, hence `y = 0`. -/
theorem dense_adjoint_domain (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : Dense (T†.domain : Set F) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  have hg : ((0 : E), y) ∈ T.graph := by
    rw [mem_graph_iff_of_isClosed hT hc]
    intro w
    rw [inner_zero_right, real_inner_comm]
    exact ((Submodule.mem_orthogonal' _ _).1 hy _ w.2).symm
  exact T.graph_fst_eq_zero_snd hg rfl

/-- von Neumann: `T** = T` for closed densely defined `T`.

Thesis gap: used implicitly (the dual of the dual complex is the original complex; `d** = d` in
the proof of Thm 4.6) but never stated or proved. -/
theorem adjoint_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) (hc : T.IsClosed) :
    T†† = T := by
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint (dense_adjoint_domain T hT hc)]
  ext ⟨x, y⟩
  rw [Submodule.mem_adjoint_iff, mem_graph_iff_of_isClosed hT hc]
  constructor
  · intro h w
    have := h w (T† w) (T†.mem_graph w)
    linarith
  · intro h a b hab
    rw [LinearPMap.mem_graph_iff] at hab
    obtain ⟨w, rfl, rfl⟩ := hab
    simp only [h w, sub_self]

/-- Thesis (4.1c): `R(T*)ᗮ = N(T)` for closed densely defined `T`.

Thesis gap: stated without proof; closedness of `T` is essential. -/
theorem orthogonal_range_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : (LinearMap.range T†.toFun)ᗮ = T.ker := by
  ext x
  have hk : x ∈ T.ker ↔ (x, (0 : F)) ∈ T.graph := by
    rw [← SetLike.mem_coe, ker_eq_preimage_graph]; rfl
  rw [hk, mem_graph_iff_of_isClosed hT hc, Submodule.mem_orthogonal]
  simp only [inner_zero_right, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
  rfl

/-- Thesis (4.1b): `N(T)ᗮ = cl R(T*)` for closed densely defined `T`.

Thesis gap: stated without proof; follows from (4.1c) by taking `ᗮ`. -/
theorem orthogonal_ker (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) (hc : T.IsClosed) :
    T.kerᗮ = (LinearMap.range T†.toFun).topologicalClosure := by
  rw [← orthogonal_range_adjoint T hT hc, Submodule.orthogonal_orthogonal_eq_closure]

/-- Thesis (4.1d): `N(T*)ᗮ = cl R(T)`.

Thesis gap: stated without proof (and for closed `T`); only density of `D(T)` is needed, via
(4.1a) `Feec.orth_range_eq_ker_adjoint`. -/
theorem orthogonal_ker_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    T†.kerᗮ = (LinearMap.range T.toFun).topologicalClosure := by
  rw [← orth_range_eq_ker_adjoint T hT, Submodule.orthogonal_orthogonal_eq_closure]

end Adjoint

/-! ### The closed range theorem -/

section ClosedRange

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Every value of a closed operator is attained on `D(T) ∩ N(T)ᗮ` (auxiliary for the closed
range theorem, Thesis §4.2). -/
theorem exists_orth_preimage {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) (x : T.domain) :
    ∃ z : T.domain, (z : E) ∈ T.kerᗮ ∧ T z = T x := by
  have : CompleteSpace T.ker := (isClosed_ker hc).completeSpace_coe
  have hK : T.ker.starProjection (x : E) ∈ T.ker := T.ker.starProjection_apply_mem _
  refine ⟨x - ⟨_, T.ker_le_domain hK⟩, Submodule.sub_starProjection_mem_orthogonal (x : E), ?_⟩
  rw [LinearPMap.map_sub, (LinearPMap.coe_mem_ker_iff (x := ⟨_, T.ker_le_domain hK⟩)).1 hK,
    sub_zero]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T` is injective on `D(T) ∩ N(T)ᗮ` (auxiliary, Thesis §4.2). -/
theorem eq_of_mem_orthogonal_ker {T : E →ₗ.[ℝ] F} {x x' : T.domain} (hx : (x : E) ∈ T.kerᗮ)
    (hx' : (x' : E) ∈ T.kerᗮ) (h : T x = T x') : x = x' := by
  have h3 : ((x - x' : T.domain) : E) ∈ T.ker ⊓ T.kerᗮ :=
    ⟨(LinearPMap.coe_mem_ker_iff).2 (by rw [LinearPMap.map_sub, h, sub_self]), sub_mem hx hx'⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h3
  exact sub_eq_zero.1 (Subtype.ext h3)

/-- For a closed operator with closed range there is a bounded right inverse
`g : R(T) → D(T) ∩ N(T)ᗮ` (closed graph theorem). This is the bounded-inverse step behind
Thesis Thm 4.2 and the closed range theorem (§4.2). -/
theorem exists_bounded_inverse (T : E →ₗ.[ℝ] F) (hc : T.IsClosed)
    (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ g : LinearMap.range T.toFun →L[ℝ] E,
      ∀ y, g y ∈ T.kerᗮ ∧ ∃ hy : g y ∈ T.domain, T ⟨g y, hy⟩ = y := by
  have : CompleteSpace (LinearMap.range T.toFun) := hR.completeSpace_coe
  let D₀ : Submodule ℝ E := T.domain ⊓ T.kerᗮ
  let T₀ : D₀ →ₗ[ℝ] LinearMap.range T.toFun :=
    LinearMap.codRestrict _ (T.toFun.comp (Submodule.inclusion inf_le_left))
      (fun z => LinearMap.mem_range_self _ _)
  have hinj : Function.Injective T₀ := by
    intro z z' hzz'
    have := eq_of_mem_orthogonal_ker (T := T) (x := Submodule.inclusion inf_le_left z)
      (x' := Submodule.inclusion inf_le_left z') z.2.2 z'.2.2 (congrArg Subtype.val hzz')
    exact Subtype.ext (congrArg (fun w : T.domain => (w : E)) this)
  have hsurj : Function.Surjective T₀ := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨z, hz, hTz⟩ := exists_orth_preimage hc x
    exact ⟨⟨z, z.2, hz⟩, Subtype.ext hTz⟩
  let e := LinearEquiv.ofBijective T₀ ⟨hinj, hsurj⟩
  let g₀ : LinearMap.range T.toFun →ₗ[ℝ] E := D₀.subtype.comp e.symm.toLinearMap
  have hg₀ : ∀ y, g₀ y ∈ T.kerᗮ ∧ ∃ hy : g₀ y ∈ T.domain, T ⟨g₀ y, hy⟩ = y := fun y =>
    ⟨(e.symm y).2.2, (e.symm y).2.1, congrArg Subtype.val (e.apply_symm_apply y)⟩
  have hgraph : IsClosed (g₀.graph : Set (LinearMap.range T.toFun × E)) := by
    have hset : (g₀.graph : Set (LinearMap.range T.toFun × E)) =
        {p | (p.2, (p.1 : F)) ∈ T.graph} ∩ {p | p.2 ∈ T.kerᗮ} := by
      ext ⟨y, x⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl
        obtain ⟨hk, hd, hT⟩ := hg₀ y
        exact ⟨(LinearPMap.mem_graph_iff _).2 ⟨⟨_, hd⟩, rfl, hT⟩, hk⟩
      · rintro ⟨hg, hk⟩
        obtain ⟨z, hz, hTz⟩ := (LinearPMap.mem_graph_iff _).1 hg
        simp only at hz hTz
        have hw : x ∈ D₀ := ⟨hz ▸ z.2, hk⟩
        have he : e.symm y = ⟨x, hw⟩ := by
          rw [LinearEquiv.symm_apply_eq]
          apply Subtype.ext
          change (y : F) = T ⟨x, hw.1⟩
          rw [← hTz]
          congr 1
          exact Subtype.ext hz
        change x = ((e.symm y : D₀) : E)
        rw [he]
    rw [hset]
    exact (hc.preimage (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))).inter
      ((Submodule.isClosed_orthogonal _).preimage continuous_snd)
  exact ⟨⟨g₀, g₀.continuous_of_isClosed_graph hgraph⟩, hg₀⟩

/-- Abstract Poincaré inequality for a closed operator with closed range:
`‖x‖ ≤ c ‖T x‖` on `D(T) ∩ N(T)ᗮ` (Thesis Thm 4.2, unbounded/W-level form).

Thesis gap: Thm 4.2 omits the closed-range hypothesis and does not name the bounded inverse
theorem; here it is the closed graph theorem applied to the inverse on `R(T)`. -/
theorem poincare_of_isClosed_range {T : E →ₗ.[ℝ] F} (hc : T.IsClosed)
    (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ c, ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖ := by
  obtain ⟨g, hg⟩ := exists_bounded_inverse T hc hR
  refine ⟨‖g‖, fun x hx => ?_⟩
  have hy : T x ∈ LinearMap.range T.toFun := ⟨x, rfl⟩
  obtain ⟨hk, hd, hT⟩ := hg ⟨T x, hy⟩
  have hgx : (⟨g ⟨T x, hy⟩, hd⟩ : T.domain) = x := eq_of_mem_orthogonal_ker hk hx hT
  have hgx' : g ⟨T x, hy⟩ = (x : E) := congrArg Subtype.val hgx
  calc ‖(x : E)‖ = ‖g ⟨T x, hy⟩‖ := by rw [hgx']
    _ ≤ ‖g‖ * ‖(⟨T x, hy⟩ : LinearMap.range T.toFun)‖ := g.le_opNorm _
    _ = ‖g‖ * ‖T x‖ := rfl

/-- Converse of the Poincaré inequality: for a closed operator, a Poincaré bound on
`D(T) ∩ N(T)ᗮ` implies closed range (Thesis Thm 4.2, converse; missing from the thesis). -/
theorem isClosed_range_of_poincare {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) {c : ℝ}
    (hP : ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖) :
    IsClosed (LinearMap.range T.toFun : Set F) := by
  let G : Submodule ℝ (E × F) := T.graph ⊓ T.kerᗮ.comap (LinearMap.fst ℝ E F)
  have hG : IsClosed (G : Set (E × F)) :=
    hc.inter ((Submodule.isClosed_orthogonal _).preimage continuous_fst)
  have : CompleteSpace G := hG.completeSpace_coe
  let π : G →L[ℝ] F := (ContinuousLinearMap.snd ℝ E F).comp G.subtypeL
  have hbound : ∀ p : G, ‖p‖ ≤ (max c 1).toNNReal * ‖π p‖ := by
    rintro ⟨⟨a, b⟩, hab, ha⟩
    obtain ⟨x, hx, hTx⟩ := (LinearPMap.mem_graph_iff _).1 hab
    simp only at hx hTx
    have h1 : ‖a‖ ≤ c * ‖b‖ := by rw [← hx, ← hTx]; exact hP x (hx ▸ ha)
    rw [Real.coe_toNNReal _ (le_trans zero_le_one (le_max_right _ _))]
    change ‖((a, b) : E × F)‖ ≤ max c 1 * ‖b‖
    refine norm_prod_le_iff.2 ⟨h1.trans ?_, le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hrange : Set.range π = (LinearMap.range T.toFun : Set F) := by
    ext y
    constructor
    · rintro ⟨⟨⟨a, b⟩, hab, ha⟩, rfl⟩
      obtain ⟨x, -, hTx⟩ := (LinearPMap.mem_graph_iff _).1 hab
      exact ⟨x, hTx⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨z, hz, hTz⟩ := exists_orth_preimage hc x
      exact ⟨⟨((z : E), T z), T.mem_graph z, hz⟩, hTz⟩
  rw [← hrange]
  exact (π.antilipschitz_of_bound hbound).isClosed_range π.uniformContinuous

/-- Thesis Thm 4.2 (unbounded form, with converse): a closed operator has closed range iff it
satisfies a Poincaré inequality on `D(T) ∩ N(T)ᗮ`. -/
theorem isClosed_range_iff_poincare {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) :
    IsClosed (LinearMap.range T.toFun : Set F) ↔
      ∃ c, ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖ :=
  ⟨poincare_of_isClosed_range hc, fun ⟨_, h⟩ => isClosed_range_of_poincare hc h⟩

/-- **Closed range theorem**, first half: if `T` is closed, densely defined and `R(T)` is
closed, then `R(T*) = N(T)ᗮ`; in particular `R(T*)` is closed.

Thesis gap (§4.2): "if `(W, d)` is closed then so is the dual complex" and `B*ₖ = (Zᵏ)ᗮ` are
attributed to (4.1), which only gives closures; the closed range theorem is needed. Proof:
bounded inverse on `R(T)` (closed graph theorem), then Riesz representation on `R(T)`. -/
theorem range_adjoint_eq_orthogonal_ker (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    LinearMap.range T†.toFun = T.kerᗮ := by
  apply le_antisymm
  · rw [orthogonal_ker T hT hc]; exact Submodule.le_topologicalClosure _
  · intro f hf
    obtain ⟨g, hg⟩ := exists_bounded_inverse T hc hR
    have : CompleteSpace (LinearMap.range T.toFun) := hR.completeSpace_coe
    let φ : StrongDual ℝ (LinearMap.range T.toFun) := (innerSL ℝ f).comp g
    let y₀ : LinearMap.range T.toFun := (InnerProductSpace.toDual ℝ _).symm φ
    have key : ∀ x : T.domain, ⟪f, (x : E)⟫ = ⟪(y₀ : F), T x⟫ := by
      intro x
      have hy : T x ∈ LinearMap.range T.toFun := ⟨x, rfl⟩
      obtain ⟨-, hd, hTg⟩ := hg ⟨T x, hy⟩
      have h1 : ((x - ⟨_, hd⟩ : T.domain) : E) ∈ T.ker :=
        (LinearPMap.coe_mem_ker_iff).2 (by rw [LinearPMap.map_sub, hTg]; exact sub_self _)
      have h2 := Submodule.inner_left_of_mem_orthogonal h1 hf
      have h3 : ⟪(y₀ : F), T x⟫ = φ ⟨T x, hy⟩ :=
        (InnerProductSpace.toDual_symm_apply (x := (⟨T x, hy⟩ : LinearMap.range T.toFun)))
      rw [h3]
      change ⟪f, (x : E)⟫ = ⟪f, g ⟨T x, hy⟩⟫
      change ⟪f, (x : E) - g ⟨T x, hy⟩⟫ = 0 at h2
      rw [inner_sub_right] at h2
      linarith
    have hmem : (y₀ : F) ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨f, key⟩
    exact ⟨⟨_, hmem⟩, adjoint_apply_eq hT ⟨_, hmem⟩ key⟩

/-- **Closed range theorem**: for closed densely defined `T`, `R(T*)` is closed iff `R(T)` is.
This is "closed complex ⇔ closed dual complex" (Thesis §4.2), which the thesis asserts from
(4.1) alone. -/
theorem isClosed_range_adjoint_iff (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) :
    IsClosed (LinearMap.range T†.toFun : Set E) ↔ IsClosed (LinearMap.range T.toFun : Set F) := by
  constructor
  · intro h
    have := range_adjoint_eq_orthogonal_ker T† (dense_adjoint_domain T hT hc)
      (adjoint_isClosed hT) h
    rw [adjoint_adjoint T hT hc] at this
    rw [this]
    exact Submodule.isClosed_orthogonal _
  · intro h
    rw [range_adjoint_eq_orthogonal_ker T hT hc h]
    exact Submodule.isClosed_orthogonal _

/-- Under closed range, Thesis (4.1d) holds without closure: `R(T) = N(T*)ᗮ` (§4.2). -/
theorem range_eq_orthogonal_ker_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    LinearMap.range T.toFun = T†.kerᗮ := by
  rw [orthogonal_ker_adjoint T hT, hR.submodule_topologicalClosure_eq]

end ClosedRange

/-! ### Skew-adjoint operators -/

section Skew

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A skew-adjoint operator is densely defined. This holds by Mathlib's junk-value convention for
the adjoint (cf. `IsSelfAdjoint.dense_domain`), and matches the thesis' definition (§4.1),
which presupposes a dense domain. -/
theorem IsSkewAdjoint.dense_domain {L : E →ₗ.[ℝ] E} (hL : IsSkewAdjoint L) :
    Dense (L.domain : Set E) := by
  by_contra h
  have hle : -L ≤ L† := hL ▸ le_rfl
  have hzero : L.toFun = 0 := by
    ext x
    have hx : (x : E) ∈ L†.domain := hle.1 x.2
    have h1 : L† ⟨x, hx⟩ = 0 := adjoint_apply_of_not_dense h _
    have h2 : L† ⟨x, hx⟩ = -L x := (hle.2 (x := x) (y := ⟨x, hx⟩) rfl).symm
    rw [h1] at h2
    exact neg_eq_zero.1 h2.symm
  have htop : L.domain = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have hy : y ∈ L†.domain := by
      rw [mem_adjoint_domain_iff, hzero, LinearMap.comp_zero]
      exact continuous_zero
    rw [hL] at hy
    exact hy
  apply h
  rw [htop, Submodule.top_coe]
  exact dense_univ

/-- Thesis §4.1: `T` is skew-adjoint iff it is skew-symmetric and `D(T*) ⊂ D(T)`.

Thesis gap: the thesis states only the self-adjoint version; the skew version is what Thm 4.4
and Thm 4.6 use. -/
theorem isSkewAdjoint_iff (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E)) :
    IsSkewAdjoint L ↔ IsSkewSymm L ∧ L†.domain ≤ L.domain := by
  constructor
  · intro hL
    refine ⟨IsSkewAdjoint.isSkewSymm hD hL, ?_⟩
    rw [hL]
    exact le_rfl
  · rintro ⟨hS, hdom⟩
    have hfa : L.IsFormalAdjoint (-L) := fun x y => by
      rw [LinearPMap.neg_apply, inner_neg_right]
      exact hS x y
    have hle : -L ≤ L† := hfa.le_adjoint hD
    exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

end Skew

/-! ### Counterexample: kernels of non-closed operators -/

section KerCounterexample

/-- `ℓ²(ℕ, ℝ)`. -/
local notation "ℓ2" => lp (fun _ : ℕ => ℝ) 2

/-- Finitely supported sequences: the span of the `lp.single` vectors. -/
def finSupp : Submodule ℝ ℓ2 :=
  Submodule.span ℝ (Set.range fun p : ℕ × ℝ => lp.single 2 p.1 p.2)

/-- Finitely supported sequences vanish eventually (auxiliary for `exists_not_isClosed_ker`). -/
theorem finSupp_eventually_zero {f : ℓ2} (hf : f ∈ finSupp) : ∃ N, ∀ n ≥ N, f n = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, a⟩, rfl⟩ := hx
    exact ⟨i + 1, fun n hn => by
      simp only; exact lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 i a (show n ≠ i by omega)⟩
  | zero => exact ⟨0, fun n _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    refine ⟨max N M, fun n hn => ?_⟩
    rw [lp.coeFn_add, Pi.add_apply, hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn),
      add_zero]
  | smul a x _ hx =>
    obtain ⟨N, hN⟩ := hx
    exact ⟨N, fun n hn => by rw [lp.coeFn_smul, Pi.smul_apply, hN n hn, smul_zero]⟩

/-- Finitely supported sequences are dense in `ℓ²` (auxiliary for `exists_not_isClosed_ker`). -/
theorem dense_finSupp : Dense (finSupp : Set ℓ2) := by
  intro f
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨(i, f i), rfl⟩

/-- The geometric sequence `(1/2)ⁿ`, an element of `ℓ²` that is not finitely supported. -/
def geom : ℓ2 :=
  ⟨fun n => (1 / 2 : ℝ) ^ n, memℓp_gen <| by
    have h : ∀ n : ℕ, ‖(1 / 2 : ℝ) ^ n‖ ^ (2 : ENNReal).toReal = (1 / 4 : ℝ) ^ n := by
      intro n
      rw [ENNReal.toReal_ofNat, Real.norm_of_nonneg (by positivity), Real.rpow_two, ← pow_mul,
        mul_comm, pow_mul]
      norm_num
    simp_rw [h]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)⟩

/-- Finitely supported sequences are not closed in `ℓ²`: `geom` is in the closure but not in
the subspace (auxiliary for `exists_not_isClosed_ker`). -/
theorem not_isClosed_finSupp : ¬ IsClosed (finSupp : Set ℓ2) := by
  intro h
  have hg : geom ∈ finSupp := by
    have := dense_finSupp.closure_eq ▸ (Set.mem_univ geom)
    rwa [h.closure_eq] at this
  obtain ⟨N, hN⟩ := finSupp_eventually_zero hg
  have := hN N le_rfl
  change (1 / 2 : ℝ) ^ N = 0 at this
  exact pow_ne_zero N (by norm_num) this

/-- Refutation of the thesis claim (§4.3) "the kernel of a (not-necessarily-bounded) linear
operator is closed": the zero operator on the dense, non-closed subspace of finitely supported
sequences in `ℓ²` is densely defined (and bounded on its domain), but its kernel — its whole
domain — is not closed. Compare `isClosed_ker`, which needs `T` closed. -/
theorem exists_not_isClosed_ker :
    ∃ T : ℓ2 →ₗ.[ℝ] ℓ2, Dense (T.domain : Set ℓ2) ∧ (∀ x : T.domain, T x = 0) ∧
      ¬ IsClosed (T.ker : Set ℓ2) := by
  refine ⟨⟨finSupp, 0⟩, dense_finSupp, fun _ => rfl, ?_⟩
  have hker : (⟨finSupp, 0⟩ : ℓ2 →ₗ.[ℝ] ℓ2).ker = finSupp := by
    ext x
    rw [LinearPMap.mem_ker_iff]
    exact ⟨fun ⟨y, hy, _⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl, rfl⟩⟩
  rw [hker]
  exact not_isClosed_finSupp

end KerCounterexample

/-! ### The dual complex (Thesis §4.2) -/

namespace HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

/-- `⟪d1* u, d0 v⟫ = 0` (auxiliary for the dual complex, Thesis §4.2). -/
theorem inner_adjoint_d0 (u : H.d1†.domain) (v : H.d0.domain) : ⟪H.d1† u, H.d0 v⟫ = 0 := by
  have := adjoint_isFormalAdjoint H.dense1 u ⟨H.d0 v, H.map_mem v⟩
  rw [H.comp_zero, inner_zero_right] at this
  exact this

/-- `d1* V₂* ⊂ V₁*` (Thesis §4.2, dual complex). -/
theorem adjoint_map_mem (u : H.d1†.domain) : H.d1† u ∈ H.d0†.domain :=
  mem_adjoint_domain_of_exists _ ⟨0, fun v => by rw [inner_zero_left, H.inner_adjoint_d0]⟩

/-- `d0* d1* = 0` (Thesis §4.2, dual complex). -/
theorem adjoint_comp_zero (u : H.d1†.domain) : H.d0† ⟨H.d1† u, H.adjoint_map_mem u⟩ = 0 :=
  adjoint_apply_eq H.dense0 _ fun v => by rw [inner_zero_left, H.inner_adjoint_d0]

/-- The dual Hilbert complex `W2 --d1*--> W1 --d0*--> W0` (Thesis §4.2).

Thesis gap: that the `dₖ*` are closed and densely defined and satisfy `d* V* ⊂ V*`,
`d* d* = 0` is asserted without proof; density of `D(d*)` is `dense_adjoint_domain`. -/
def dual : HilbertComplex2 W2 W1 W0 where
  d0 := H.d1†
  d1 := H.d0†
  dense0 := dense_adjoint_domain _ H.dense1 H.closed1
  dense1 := dense_adjoint_domain _ H.dense0 H.closed0
  closed0 := adjoint_isClosed H.dense1
  closed1 := adjoint_isClosed H.dense0
  map_mem := H.adjoint_map_mem
  comp_zero := H.adjoint_comp_zero

/-- The dual of the dual complex is the original complex (Thesis §4.2).

Thesis gap: implicit in the thesis; it needs `T** = T` (`adjoint_adjoint`). -/
theorem dual_dual : H.dual.dual = H := by
  obtain ⟨d0, d1, dense0, dense1, closed0, closed1, _, _⟩ := H
  simp only [dual, mk.injEq]
  exact ⟨adjoint_adjoint d0 dense0 closed0, adjoint_adjoint d1 dense1 closed1⟩

/-- A Hilbert complex is closed iff its dual complex is closed (Thesis §4.2).

Correction: the thesis derives this from (4.1); it is the closed range theorem
`isClosed_range_adjoint_iff`. -/
theorem closedRange_dual_iff : H.dual.ClosedRange ↔ H.ClosedRange := by
  change IsClosed (LinearMap.range H.d1†.toFun : Set W1) ∧
      IsClosed (LinearMap.range H.d0†.toFun : Set W0) ↔ _
  rw [isClosed_range_adjoint_iff _ H.dense1 H.closed1,
    isClosed_range_adjoint_iff _ H.dense0 H.closed0]
  exact and_comm

/-- `B*₀ = (Z⁰)ᗮ` for a closed complex (Thesis §4.2, used in Thm 4.1). -/
theorem range_adjoint_d0_eq (h : H.ClosedRange) :
    LinearMap.range H.d0†.toFun = H.d0.kerᗮ :=
  range_adjoint_eq_orthogonal_ker _ H.dense0 H.closed0 h.1

/-- `B*₁ = (Z¹)ᗮ` for a closed complex (Thesis §4.2, used in Thm 4.1). -/
theorem range_adjoint_d1_eq (h : H.ClosedRange) :
    LinearMap.range H.d1†.toFun = H.d1.kerᗮ :=
  range_adjoint_eq_orthogonal_ker _ H.dense1 H.closed1 h.2

end HilbertComplex2

end Feec
