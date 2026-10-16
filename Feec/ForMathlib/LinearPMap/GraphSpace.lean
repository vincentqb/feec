module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The graph space of an unbounded operator, and `T†† = T`

For `T : E →ₗ.[𝕜] F` between Hilbert spaces over `𝕜` (`RCLike`):

* `LinearPMap.graphL2 T`: the graph of `T` as a subspace of the Hilbert sum `WithLp 2 (E × F)`,
  and `LinearPMap.GraphSpace T := ↥T.graphL2` with the graph inner product
  `⟪x, y⟫ + ⟪T x, T y⟫` (inherited from the subtype: no norm diamond).
* `LinearPMap.rotAdjGraph T = {(x, y) | (y, -x) ∈ Γ(T†)}` and the graph relations
  `graph_orthogonal` (`Γ(T)ᗮ = Γ̃(T†)`), `closure_graph`, `graph_eq_orthogonal`,
  `mem_graph_iff_of_isClosed` (weak characterization of `Γ(T)` for closed `T`).
* `LinearPMap.dense_adjoint_domain` and `LinearPMap.adjoint_adjoint` (`T†† = T`) for closed,
  densely defined `T`.
* `LinearPMap.isClosed_ker`: the kernel of a closed operator is closed (closedness is needed:
  see `Feec.exists_not_isClosed_ker`).

## References

* [QuennevilleBelair2015], §4.1 (graph relations)
* [Kato1995], §III.5 (adjoints and graphs)
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace LinearPMap

/-! ### Kernels -/

section Kernel

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- `N(T) = {x | (x, 0) ∈ Γ(T)}`. -/
theorem ker_eq_preimage_graph (T : E →ₗ.[R] F) :
    (T.ker : Set E) = (fun x => (x, (0 : F))) ⁻¹' (T.graph : Set (E × F)) := by
  ext x
  simp only [SetLike.mem_coe, mem_preimage, LinearPMap.mem_ker_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩; exact ⟨y, rfl, hy⟩
  · rintro ⟨y, hy, hy0⟩; exact ⟨y, hy.symm, hy0⟩

variable [TopologicalSpace E] [TopologicalSpace F]

/-- The kernel of a **closed** unbounded operator is closed. -/
theorem isClosed_ker {T : E →ₗ.[R] F} (hc : T.IsClosed) : _root_.IsClosed (T.ker : Set E) := by
  rw [ker_eq_preimage_graph]
  exact hc.preimage (continuous_id.prodMk continuous_const)

end Kernel

/-! ### The graph space -/

section Graph

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The graph `Γ(T)` as a subspace of the Hilbert sum `E ⊕₂ F`. -/
def graphL2 (T : E →ₗ.[𝕜] F) : Submodule 𝕜 (WithLp 2 (E × F)) :=
  T.graph.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

/-- The graph space of `T`: `D(T)` with the graph inner product `⟪x, y⟫ + ⟪T x, T y⟫`, realized
as the subspace `graphL2 T` of `E ⊕₂ F` (so it inherits its inner product structure). -/
abbrev GraphSpace (T : E →ₗ.[𝕜] F) := ↥T.graphL2

/-- The rotated graph of the adjoint, `Γ̃(T†) = {(x, y) | (y, -x) ∈ Γ(T†)}`, in `E ⊕₂ F`. -/
def rotAdjGraph [CompleteSpace E] (T : E →ₗ.[𝕜] F) : Submodule 𝕜 (WithLp 2 (E × F)) :=
  T†.graph.comap (((LinearMap.snd 𝕜 E F).prod (-LinearMap.fst 𝕜 E F)).comp
    (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap)

theorem mem_graphL2 {T : E →ₗ.[𝕜] F} {p : WithLp 2 (E × F)} :
    p ∈ T.graphL2 ↔ WithLp.ofLp p ∈ T.graph := Iff.rfl

theorem mem_rotAdjGraph [CompleteSpace E] {T : E →ₗ.[𝕜] F} {p : WithLp 2 (E × F)} :
    p ∈ T.rotAdjGraph ↔ ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) ∈ T†.graph := Iff.rfl

/-- The point `(x, T x)` of the graph space. -/
def toGraphSpace (T : E →ₗ.[𝕜] F) (x : T.domain) : T.GraphSpace :=
  ⟨WithLp.toLp 2 ((x : E), T x), by simp [mem_graphL2]⟩

/-- The first projection `Γ(T) → E`, a bounded operator. -/
def graphFst (T : E →ₗ.[𝕜] F) : T.GraphSpace →L[𝕜] E :=
  (ContinuousLinearMap.fst 𝕜 E F).comp
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).toContinuousLinearMap.comp T.graphL2.subtypeL)

/-- The second projection `Γ(T) → F`, `(x, T x) ↦ T x`, a bounded operator. -/
def graphSnd (T : E →ₗ.[𝕜] F) : T.GraphSpace →L[𝕜] F :=
  (ContinuousLinearMap.snd 𝕜 E F).comp
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).toContinuousLinearMap.comp T.graphL2.subtypeL)

@[simp] theorem graphFst_toGraphSpace (T : E →ₗ.[𝕜] F) (x : T.domain) :
    T.graphFst (T.toGraphSpace x) = x := rfl

@[simp] theorem graphSnd_toGraphSpace (T : E →ₗ.[𝕜] F) (x : T.domain) :
    T.graphSnd (T.toGraphSpace x) = T x := rfl

/-- The graph inner product: `⟪(x, T x), (y, T y)⟫ = ⟪x, y⟫ + ⟪T x, T y⟫`. -/
theorem inner_toGraphSpace (T : E →ₗ.[𝕜] F) (x y : T.domain) :
    ⟪T.toGraphSpace x, T.toGraphSpace y⟫_𝕜 = ⟪(x : E), (y : E)⟫_𝕜 + ⟪T x, T y⟫_𝕜 := by
  simp [toGraphSpace, WithLp.prod_inner_apply]

/-- A closed operator has closed graph in `E ⊕₂ F`. -/
theorem isClosed_graphL2 {T : E →ₗ.[𝕜] F} (hc : T.IsClosed) :
    _root_.IsClosed (T.graphL2 : Set (WithLp 2 (E × F))) :=
  hc.preimage (WithLp.prod_continuous_ofLp 2 E F)

/-- The graph space of a closed operator between complete spaces is complete. -/
theorem IsClosed.completeSpace_graphSpace [CompleteSpace E] [CompleteSpace F]
    {T : E →ₗ.[𝕜] F} (hc : T.IsClosed) : CompleteSpace T.GraphSpace :=
  (isClosed_graphL2 hc).completeSpace_coe

variable [CompleteSpace E]

/-- Graph relation `Γ(T)ᗮ = Γ̃(T†)` in `E ⊕₂ F`, for densely defined `T`. -/
theorem graph_orthogonal (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) :
    T.graphL2ᗮ = T.rotAdjGraph := by
  ext p
  rw [Submodule.mem_orthogonal, mem_rotAdjGraph, LinearPMap.mem_graph_iff]
  constructor
  · intro h
    have key : ∀ x : T.domain,
        ⟪-(WithLp.ofLp p).1, (x : E)⟫_𝕜 = ⟪(WithLp.ofLp p).2, T x⟫_𝕜 := by
      intro x
      have h0 := h (WithLp.toLp 2 ((x : E), T x)) (by simp [mem_graphL2])
      simp only [WithLp.prod_inner_apply] at h0
      rw [inner_neg_left, ← inner_conj_symm (WithLp.ofLp p).1 (x : E),
        ← inner_conj_symm (WithLp.ofLp p).2 (T x), eq_neg_of_add_eq_zero_left h0]
      simp
    have hmem := mem_adjoint_domain_of_exists _ ⟨_, key⟩
    exact ⟨⟨_, hmem⟩, rfl, adjoint_apply_eq hT ⟨_, hmem⟩ key⟩
  · rintro ⟨y, hy, hTy⟩ u hu
    rw [mem_graphL2, LinearPMap.mem_graph_iff] at hu
    obtain ⟨x, hx, hTx⟩ := hu
    have h := adjoint_isFormalAdjoint hT y x
    rw [hTy, hy, inner_neg_left] at h
    rw [WithLp.prod_inner_apply, ← hx, ← hTx, ← inner_conj_symm, ← inner_conj_symm (T x), ← h]
    simp

variable [CompleteSpace F]

/-- `cl Γ(T) = Γ̃(T†)ᗮ`. -/
theorem closure_graph (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) :
    T.graphL2.topologicalClosure = T.rotAdjGraphᗮ := by
  rw [← graph_orthogonal T hT, Submodule.orthogonal_orthogonal_eq_closure]

/-- `Γ(T) = Γ̃(T†)ᗮ` for closed densely defined `T`. -/
theorem graph_eq_orthogonal (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : T.graphL2 = T.rotAdjGraphᗮ := by
  rw [← closure_graph T hT, (isClosed_graphL2 hc).submodule_topologicalClosure_eq]

/-- Weak characterization of the graph of a closed densely defined operator:
`(x, y) ∈ Γ(T)` iff `⟪T† w, x⟫ = ⟪w, y⟫` for all `w ∈ D(T†)`. -/
theorem mem_graph_iff_of_isClosed {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) {x : E} {y : F} :
    (x, y) ∈ T.graph ↔ ∀ w : T†.domain, ⟪T† w, x⟫_𝕜 = ⟪(w : F), y⟫_𝕜 := by
  have h : (x, y) ∈ T.graph ↔ WithLp.toLp 2 (x, y) ∈ T.rotAdjGraphᗮ := by
    rw [← graph_eq_orthogonal T hT hc, mem_graphL2, WithLp.ofLp_toLp]
  rw [h, Submodule.mem_orthogonal]
  constructor
  · intro H w
    have := H (WithLp.toLp 2 (-(T† w), (w : F))) (by
      rw [mem_rotAdjGraph, LinearPMap.mem_graph_iff]
      exact ⟨w, by simp⟩)
    simp only [WithLp.prod_inner_apply, inner_neg_left] at this
    linear_combination -this
  · intro H u hu
    rw [mem_rotAdjGraph, LinearPMap.mem_graph_iff] at hu
    obtain ⟨w, hw, hTw⟩ := hu
    simp only at hw hTw
    have hu1 : (WithLp.ofLp u).1 = -(T† w) := by rw [hTw, neg_neg]
    simp only [WithLp.prod_inner_apply]
    rw [hu1, ← hw, inner_neg_left, H w]
    ring

/-- The adjoint of a closed densely defined operator is densely defined. -/
theorem dense_adjoint_domain (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : Dense (T†.domain : Set F) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  have hg : ((0 : E), y) ∈ T.graph := by
    rw [mem_graph_iff_of_isClosed hT hc]
    intro w
    rw [inner_zero_right]
    exact (inner_eq_zero_symm.1 ((Submodule.mem_orthogonal' _ _).1 hy _ w.2)).symm
  exact T.graph_fst_eq_zero_snd hg rfl

/-- von Neumann: `T†† = T` for closed densely defined `T`. -/
theorem adjoint_adjoint (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : T†† = T := by
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint (dense_adjoint_domain T hT hc)]
  ext ⟨x, y⟩
  rw [Submodule.mem_adjoint_iff, mem_graph_iff_of_isClosed hT hc]
  constructor
  · intro h w
    have := h w (T† w) (T†.mem_graph w)
    linear_combination this
  · intro h a b hab
    rw [LinearPMap.mem_graph_iff] at hab
    obtain ⟨w, rfl, rfl⟩ := hab
    simp only [h w, sub_self]

end Graph

end LinearPMap
