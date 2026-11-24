module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The graph space of an unbounded operator, the graph norm, and `T†† = T`

For `T : E →ₗ.[𝕜] F` between Hilbert spaces over `𝕜` (`RCLike`):

* `LinearPMap.graphL2 T`: the graph of `T` as a subspace of the Hilbert sum `WithLp 2 (E × F)`,
  and `LinearPMap.GraphSpace T := ↥T.graphL2` with the graph inner product
  `⟪x, y⟫ + ⟪T x, T y⟫` (inherited from the subtype: no norm diamond).
* Its points: `LinearPMap.toGraphSpace T x = (x, T x)`, the bounded projections
  `LinearPMap.graphFst`, `LinearPMap.graphSnd`, and `LinearPMap.graphDom T v ∈ D(T)`, the first
  component of `v` (`LinearPMap.exists_toGraphSpace_eq`: every point is `(x, T x)`;
  `LinearPMap.graphFst_injective`, `LinearPMap.range_graphSnd`, `LinearPMap.denseRange_graphFst`).
* The graph norm: `LinearPMap.inner_graphSpace`, `LinearPMap.norm_sq_graphSpace`
  (`‖v‖² = ‖v₁‖² + ‖v₂‖²`), `LinearPMap.norm_graphFst_le`, `LinearPMap.norm_graphSnd_le`,
  `LinearPMap.norm_le_norm_graphFst_add_norm_graphSnd` (`‖v‖ ≤ ‖v₁‖ + ‖v₂‖`),
  `LinearPMap.norm_graphFst_add_norm_graphSnd_le` (`‖v₁‖ + ‖v₂‖ ≤ √2 ‖v‖`),
  `LinearPMap.norm_toGraphSpace_le`.
* `ContinuousLinearMap.graphOpNorm D A`: the norm of an operator `A` in the graph norm of a
  bounded operator `D`, with `‖A v‖ ≤ D.graphOpNorm A (‖v‖ + ‖D v‖)`
  (`ContinuousLinearMap.norm_apply_le_graphOpNorm`), at most `‖A‖`
  (`ContinuousLinearMap.graphOpNorm_le`) and at most `√2 δ` when `‖A v‖ ≤ δ (‖v‖ + ‖D v‖)` for
  every `v` (`ContinuousLinearMap.graphOpNorm_le_of_forall`).
* `LinearPMap.rotAdjGraph T = {(x, y) | (y, -x) ∈ Γ(T†)}` and the graph relations
  `graph_orthogonal` (`Γ(T)ᗮ = Γ̃(T†)`), `closure_graph`, `graph_eq_orthogonal`,
  `mem_graph_iff_of_isClosed` (weak characterization of `Γ(T)` for closed `T`).
* `LinearPMap.dense_adjoint_domain` and `LinearPMap.adjoint_adjoint` (`T†† = T`) for closed,
  densely defined `T`.
* `LinearPMap.isClosed_ker`: the kernel of a closed operator is closed (closedness is needed:
  see `Feec.Counterexamples.exists_dense_not_isClosed_ker`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.1 (graph relations)
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5 (adjoints and graphs)

Bibliography: [references.bib](../../../docs/references.bib)
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

/-- The kernel of a **closed** unbounded operator is closed (closedness is needed; the thesis
asserts it for every unbounded operator). See [QuennevilleBelair2015], §4.1. -/
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

/-- Every point of the graph space is `(x, T x)` for a unique `x ∈ D(T)`. -/
theorem exists_toGraphSpace_eq (T : E →ₗ.[𝕜] F) (v : T.GraphSpace) :
    ∃ x : T.domain, T.toGraphSpace x = v ∧ (x : E) = T.graphFst v ∧ T x = T.graphSnd v := by
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 (mem_graphL2.1 v.2)
  exact ⟨x, Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext hx1 hx2)), hx1, hx2⟩

theorem graphFst_injective (T : E →ₗ.[𝕜] F) : Function.Injective T.graphFst := by
  intro u v huv
  obtain ⟨x, rfl, -, -⟩ := T.exists_toGraphSpace_eq u
  obtain ⟨y, rfl, -, -⟩ := T.exists_toGraphSpace_eq v
  have : x = y := Subtype.ext huv
  rw [this]

theorem graphFst_mem_domain (T : E →ₗ.[𝕜] F) (v : T.GraphSpace) : T.graphFst v ∈ T.domain :=
  LinearPMap.mem_domain_of_mem_graph (x := T.graphFst v) (y := T.graphSnd v) (mem_graphL2.1 v.2)

/-- The point `x ∈ D(T)` of a point `(x, T x)` of the graph space (inverse to `toGraphSpace`). -/
def graphDom (T : E →ₗ.[𝕜] F) (v : T.GraphSpace) : T.domain :=
  ⟨T.graphFst v, T.graphFst_mem_domain v⟩

@[simp] theorem coe_graphDom (T : E →ₗ.[𝕜] F) (v : T.GraphSpace) :
    (T.graphDom v : E) = T.graphFst v := rfl

theorem apply_graphDom (T : E →ₗ.[𝕜] F) (v : T.GraphSpace) : T (T.graphDom v) = T.graphSnd v :=
  ((LinearPMap.image_iff (T.graphFst_mem_domain v)).2 (mem_graphL2.1 v.2)).symm

theorem graphDom_add (T : E →ₗ.[𝕜] F) (u v : T.GraphSpace) :
    T.graphDom (u + v) = T.graphDom u + T.graphDom v :=
  Subtype.ext (_root_.map_add T.graphFst u v)

theorem graphDom_smul (T : E →ₗ.[𝕜] F) (c : 𝕜) (v : T.GraphSpace) :
    T.graphDom (c • v) = c • T.graphDom v :=
  Subtype.ext (_root_.map_smul T.graphFst c v)

theorem toGraphSpace_add (T : E →ₗ.[𝕜] F) (x y : T.domain) :
    T.toGraphSpace (x + y) = T.toGraphSpace x + T.toGraphSpace y :=
  Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (T.map_add x y)))

theorem toGraphSpace_sub (T : E →ₗ.[𝕜] F) (x y : T.domain) :
    T.toGraphSpace (x - y) = T.toGraphSpace x - T.toGraphSpace y :=
  Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (T.map_sub x y)))

theorem toGraphSpace_smul (T : E →ₗ.[𝕜] F) (c : 𝕜) (x : T.domain) :
    T.toGraphSpace (c • x) = c • T.toGraphSpace x :=
  Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (T.map_smul c x)))

/-- The second projection of the graph space has the range of `T`. -/
theorem range_graphSnd (T : E →ₗ.[𝕜] F) :
    Set.range T.graphSnd = Set.range fun x : T.domain => T x := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨T.graphDom v, T.apply_graphDom v⟩
  · rintro ⟨x, rfl⟩; exact ⟨T.toGraphSpace x, rfl⟩

/-- The first projection of the graph space of a densely defined operator has dense range. -/
theorem denseRange_graphFst (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) :
    DenseRange T.graphFst :=
  hT.mono fun x hx => ⟨T.toGraphSpace ⟨x, hx⟩, rfl⟩

/-! ### The graph norm -/

/-- The graph inner product: `⟪u, v⟫ = ⟪u₁, v₁⟫ + ⟪u₂, v₂⟫`. -/
theorem inner_graphSpace {T : E →ₗ.[𝕜] F} (u v : T.GraphSpace) :
    ⟪u, v⟫_𝕜 = ⟪T.graphFst u, T.graphFst v⟫_𝕜 + ⟪T.graphSnd u, T.graphSnd v⟫_𝕜 :=
  WithLp.prod_inner_apply (u : WithLp 2 (E × F)) v

/-- The graph norm: `‖v‖² = ‖v₁‖² + ‖v₂‖²`. -/
theorem norm_sq_graphSpace {T : E →ₗ.[𝕜] F} (v : T.GraphSpace) :
    ‖v‖ ^ 2 = ‖T.graphFst v‖ ^ 2 + ‖T.graphSnd v‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (v : WithLp 2 (E × F))

/-- The graph norm of `(x, T x)`: `‖x‖² + ‖T x‖²`. -/
theorem norm_toGraphSpace_sq (T : E →ₗ.[𝕜] F) (x : T.domain) :
    ‖T.toGraphSpace x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖T x‖ ^ 2 :=
  norm_sq_graphSpace _

theorem norm_graphFst_le {T : E →ₗ.[𝕜] F} (v : T.GraphSpace) : ‖T.graphFst v‖ ≤ ‖v‖ := by
  refine (abs_le_of_sq_le_sq' ?_ (norm_nonneg _)).2
  rw [norm_sq_graphSpace v]
  nlinarith [sq_nonneg ‖T.graphSnd v‖]

theorem norm_graphSnd_le {T : E →ₗ.[𝕜] F} (v : T.GraphSpace) : ‖T.graphSnd v‖ ≤ ‖v‖ := by
  refine (abs_le_of_sq_le_sq' ?_ (norm_nonneg _)).2
  rw [norm_sq_graphSpace v]
  nlinarith [sq_nonneg ‖T.graphFst v‖]

/-- The graph norm is at most `‖v₁‖ + ‖v₂‖`. -/
theorem norm_le_norm_graphFst_add_norm_graphSnd {T : E →ₗ.[𝕜] F} (v : T.GraphSpace) :
    ‖v‖ ≤ ‖T.graphFst v‖ + ‖T.graphSnd v‖ := by
  refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  rw [norm_sq_graphSpace v]
  nlinarith [mul_nonneg (norm_nonneg (T.graphFst v)) (norm_nonneg (T.graphSnd v))]

/-- The graph norm of `(x, T x)` is at most `‖x‖ + ‖T x‖`. -/
theorem norm_toGraphSpace_le (T : E →ₗ.[𝕜] F) (x : T.domain) :
    ‖T.toGraphSpace x‖ ≤ ‖(x : E)‖ + ‖T x‖ :=
  norm_le_norm_graphFst_add_norm_graphSnd _

/-- `‖v₁‖ + ‖v₂‖ ≤ √2 ‖v‖` in the graph space. -/
theorem norm_graphFst_add_norm_graphSnd_le {T : E →ₗ.[𝕜] F} (v : T.GraphSpace) :
    ‖T.graphFst v‖ + ‖T.graphSnd v‖ ≤ √2 * ‖v‖ := by
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt zero_le_two, norm_sq_graphSpace v]
  nlinarith [sq_nonneg (‖T.graphFst v‖ - ‖T.graphSnd v‖)]

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
`(x, y) ∈ Γ(T)` iff `⟪T† w, x⟫ = ⟪w, y⟫` for all `w ∈ D(T†)`.
See [QuennevilleBelair2015], §4.1. -/
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

/-- The adjoint of a closed densely defined operator is densely defined.
See [QuennevilleBelair2015], §4.1. -/
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

/-- von Neumann: `T†† = T` for closed densely defined `T`. See [QuennevilleBelair2015], §4.1. -/
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

/-! ### The norm of an operator in the graph norm of a bounded operator -/

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  (D : E →L[𝕜] F) (A : E →L[𝕜] G)

/-- **The norm of `A` in the graph norm of `D`**: the operator norm of `A` on the graph space of
the bounded operator `D` (`‖v‖²_D = ‖v‖² + ‖D v‖²`), the least `δ` with `‖A v‖ ≤ δ ‖v‖_D`. It is
at most `‖A‖` (`graphOpNorm_le`), and `‖A v‖ ≤ D.graphOpNorm A (‖v‖ + ‖D v‖)`
(`norm_apply_le_graphOpNorm`). At `A = 1 - iₕ* iₕ` and `D = 𝐝ₕ` it is the inner-product defect in
the graph norm of a discretization of a Hilbert complex. -/
def graphOpNorm : ℝ := ‖A ∘L ((D : E →ₗ[𝕜] F).toPMap ⊤).graphFst‖

theorem graphOpNorm_nonneg : 0 ≤ D.graphOpNorm A := norm_nonneg _

/-- `D.graphOpNorm A ≤ ‖A‖`. -/
theorem graphOpNorm_le : D.graphOpNorm A ≤ ‖A‖ :=
  opNorm_le_bound _ (norm_nonneg _) fun v =>
    (A.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (LinearPMap.norm_graphFst_le v) (norm_nonneg _))

/-- `D.graphOpNorm A = 0` iff `A = 0` (the first projection of the graph space is onto). -/
theorem graphOpNorm_eq_zero_iff : D.graphOpNorm A = 0 ↔ A = 0 := by
  refine ⟨fun h0 => ext fun v => ?_, fun hA => by rw [graphOpNorm, hA, zero_comp, norm_zero]⟩
  rw [graphOpNorm, norm_eq_zero] at h0
  exact congrArg (fun B => B (((D : E →ₗ[𝕜] F).toPMap ⊤).toGraphSpace ⟨v, Submodule.mem_top⟩)) h0

/-- `‖A v‖ ≤ D.graphOpNorm A ‖v‖_D` on the graph space of `D`. -/
theorem norm_graphFst_le_graphOpNorm (v : ((D : E →ₗ[𝕜] F).toPMap ⊤).GraphSpace) :
    ‖A (((D : E →ₗ[𝕜] F).toPMap ⊤).graphFst v)‖ ≤ D.graphOpNorm A * ‖v‖ :=
  (A ∘L ((D : E →ₗ[𝕜] F).toPMap ⊤).graphFst).le_opNorm v

/-- `‖A v‖ ≤ D.graphOpNorm A (‖v‖ + ‖D v‖)`. -/
theorem norm_apply_le_graphOpNorm (v : E) : ‖A v‖ ≤ D.graphOpNorm A * (‖v‖ + ‖D v‖) :=
  (D.norm_graphFst_le_graphOpNorm A (((D : E →ₗ[𝕜] F).toPMap ⊤).toGraphSpace
    ⟨v, Submodule.mem_top⟩)).trans (mul_le_mul_of_nonneg_left
      (LinearPMap.norm_toGraphSpace_le _ _) (D.graphOpNorm_nonneg A))

/-- `‖A v‖ ≤ D.graphOpNorm A ‖v‖` when `D v = 0`. -/
theorem norm_apply_le_graphOpNorm_of_eq_zero {v : E} (hv : D v = 0) :
    ‖A v‖ ≤ D.graphOpNorm A * ‖v‖ := by
  simpa [hv] using D.norm_apply_le_graphOpNorm A v

/-- **The norm in the graph norm from a bound**: if `‖A v‖ ≤ δ (‖v‖ + ‖D v‖)` for every `v`, then
`D.graphOpNorm A ≤ √2 δ` (`‖v‖ + ‖D v‖ ≤ √2 ‖v‖_D`). -/
theorem graphOpNorm_le_of_forall {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ v, ‖A v‖ ≤ δ * (‖v‖ + ‖D v‖)) :
    D.graphOpNorm A ≤ √2 * δ := by
  refine opNorm_le_bound _ (by positivity) fun g => ?_
  obtain ⟨x, rfl, -, -⟩ := LinearPMap.exists_toGraphSpace_eq _ g
  set g := ((D : E →ₗ[𝕜] F).toPMap ⊤).toGraphSpace x
  calc ‖A x‖ ≤ δ * (‖(x : E)‖ + ‖D x‖) := hb x
    _ ≤ δ * (√2 * ‖g‖) :=
      mul_le_mul_of_nonneg_left (LinearPMap.norm_graphFst_add_norm_graphSnd_le g) hδ
    _ = √2 * δ * ‖g‖ := by ring

end ContinuousLinearMap
