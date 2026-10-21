module

public import Feec.ForMathlib.LinearPMap.Skew
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bounded operators and bounded perturbations of unbounded operators

* `ContinuousLinearMap.isClosed_toPMap_top`, `adjoint_toPMap_top`,
  `isSkewAdjoint_toPMap_top_iff`: an everywhere-defined bounded operator as a `LinearPMap`.
* Bounded perturbations `B +ᵥ T` (Mathlib's `VAdd (E →ₗ[𝕜] F) (E →ₗ.[𝕜] F)`, domain `D(T)`):
  `IsClosed.vadd`, `adjoint_vadd` (`(B + T)† = B† + T†`), and the stability of
  skew-symmetry, dissipativity and skew-adjointness under bounded skew / dissipative
  perturbations (`IsSkewAdjoint.vadd`, `IsDissipative.vadd`, `IsSkewSymmetric.vadd`).

## References

* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §V.4.1 (bounded perturbations of
  self-adjoint operators)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.1 (bounded perturbations of generators)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

/-- An everywhere-defined continuous operator is closed. -/
theorem isClosed_toPMap_top (A : E →L[𝕜] F) : ((A : E →ₗ[𝕜] F).toPMap ⊤).IsClosed := by
  have : (((A : E →ₗ[𝕜] F).toPMap ⊤).graph : Set (E × F)) = {p | p.2 = A p.1} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hz]; rfl
    · intro h
      exact ⟨⟨x, Submodule.mem_top⟩, rfl, h.symm⟩
  rw [LinearPMap.IsClosed, this]
  exact isClosed_eq continuous_snd (A.continuous.comp continuous_fst)

/-- The adjoint of an everywhere-defined bounded operator is its Hilbert adjoint. -/
theorem adjoint_toPMap_top [CompleteSpace E] [CompleteSpace F] (A : E →L[𝕜] F) :
    ((A : E →ₗ[𝕜] F).toPMap ⊤).adjoint = ((adjoint A : F →L[𝕜] E) : F →ₗ[𝕜] E).toPMap ⊤ :=
  A.toPMap_adjoint_eq_adjoint_toPMap_of_dense (by simp [dense_univ])

theorem adjoint_eq_neg_iff [CompleteSpace E] (A : E →L[𝕜] E) :
    adjoint A = -A ↔ ∀ x y, ⟪A x, y⟫_𝕜 = -⟪x, A y⟫_𝕜 := by
  constructor
  · intro h x y
    rw [← adjoint_inner_right, h, neg_apply, inner_neg_right]
  · intro h
    symm
    rw [eq_adjoint_iff]
    intro x y
    simp [h]

/-- A bounded operator `A` is skew-adjoint as an unbounded operator iff `A† = -A`. -/
theorem isSkewAdjoint_toPMap_top_iff [CompleteSpace E] (A : E →L[𝕜] E) :
    ((A : E →ₗ[𝕜] E).toPMap ⊤).IsSkewAdjoint ↔ adjoint A = -A := by
  unfold LinearPMap.IsSkewAdjoint
  rw [adjoint_toPMap_top]
  constructor
  · intro h
    ext x
    have := (LinearPMap.ext_iff.1 h).2 (x := x) (hf := Submodule.mem_top)
      (hg := Submodule.mem_top)
    rw [LinearPMap.neg_apply] at this
    simpa using this
  · intro h
    rw [h]
    exact LinearPMap.ext (by simp) fun x _ _ => rfl

end ContinuousLinearMap

namespace LinearPMap

section VAdd

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem mem_graph_vadd_iff {B : M →ₗ[R] N} {T : M →ₗ.[R] N} {x : M} {y : N} :
    (x, y) ∈ (B +ᵥ T).graph ↔ (x, y - B x) ∈ T.graph := by
  simp only [mem_graph_iff, vadd_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, by rw [hz]; abel⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, by rw [h, hz]; abel⟩

theorem neg_vadd_neg (B : M →ₗ[R] N) (T : M →ₗ.[R] N) : (-B) +ᵥ (-T) = -(B +ᵥ T) :=
  LinearPMap.ext rfl fun _ _ _ => (neg_add _ _).symm

end VAdd

/-- A bounded perturbation of a closed operator is closed. -/
theorem IsClosed.vadd {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) (B : E →L[𝕜] F) :
    ((B : E →ₗ[𝕜] F) +ᵥ T).IsClosed := by
  have : (((B : E →ₗ[𝕜] F) +ᵥ T).graph : Set (E × F)) =
      (fun p : E × F => (p.1, p.2 - B p.1)) ⁻¹' T.graph := by
    ext ⟨x, y⟩; exact mem_graph_vadd_iff
  rw [LinearPMap.IsClosed, this]
  exact hT.preimage (continuous_fst.prodMk (continuous_snd.sub (B.continuous.comp continuous_fst)))

variable [CompleteSpace E] [CompleteSpace F]

/-- `(B + T)† = B† + T†` for a densely defined `T` and a bounded `B`. -/
theorem adjoint_vadd (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (B : E →L[𝕜] F) :
    ((B : E →ₗ[𝕜] F) +ᵥ T)† =
      ((ContinuousLinearMap.adjoint B : F →L[𝕜] E) : F →ₗ[𝕜] E) +ᵥ T† := by
  have hT' : Dense (((B : E →ₗ[𝕜] F) +ᵥ T).domain : Set E) := hT
  have hdom : ((B : E →ₗ[𝕜] F) +ᵥ T)†.domain = T†.domain := by
    ext y
    rw [mem_adjoint_domain_iff, mem_adjoint_domain_iff]
    have hc : Continuous fun x : T.domain => ⟪y, B x⟫_𝕜 :=
      continuous_const.inner (B.continuous.comp continuous_subtype_val)
    have heq : ⇑((innerₛₗ 𝕜 y).comp ((B : E →ₗ[𝕜] F) +ᵥ T).toFun) =
        (fun x : T.domain => ⟪y, B x⟫_𝕜) + ⇑((innerₛₗ 𝕜 y).comp T.toFun) := by
      ext x; simp [inner_add_right]
    rw [heq]
    constructor
    · intro h
      convert h.sub hc using 1
      ext x; simp
    · exact fun h => hc.add h
  refine LinearPMap.ext hdom fun y hy hy' => ?_
  refine adjoint_apply_eq hT' ⟨y, hy⟩ fun x => ?_
  have h := (adjoint_isFormalAdjoint hT) ⟨y, hy'⟩ x
  change ⟪ContinuousLinearMap.adjoint B y + T† ⟨y, hy'⟩, (x : E)⟫_𝕜 = ⟪y, B x + T x⟫_𝕜
  rw [inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left, h]

variable {A : E →ₗ.[𝕜] E}

omit [CompleteSpace E] in
/-- A skew-symmetric operator perturbed by a bounded skew operator is skew-symmetric. -/
theorem IsSkewSymmetric.vadd (hA : A.IsSkewSymmetric) {B : E →L[𝕜] E}
    (hB : ∀ x y, ⟪B x, y⟫_𝕜 = -⟪x, B y⟫_𝕜) : ((B : E →ₗ[𝕜] E) +ᵥ A).IsSkewSymmetric := by
  intro x y
  change ⟪B x + A x, (y : E)⟫_𝕜 = -⟪(x : E), B y + A y⟫_𝕜
  have h : ⟪A x, (y : E)⟫_𝕜 = -⟪(x : E), A y⟫_𝕜 := hA x y
  rw [inner_add_left, inner_add_right, hB, h, neg_add]

omit [CompleteSpace E] in
/-- A dissipative operator perturbed by a bounded dissipative operator is dissipative. -/
theorem IsDissipative.vadd (hA : A.IsDissipative) {B : E →L[𝕜] E}
    (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) : ((B : E →ₗ[𝕜] E) +ᵥ A).IsDissipative := by
  intro x
  change RCLike.re ⟪B x + A x, (x : E)⟫_𝕜 ≤ 0
  rw [inner_add_left, RCLike.re.map_add]
  exact add_nonpos (hB x) (hA x)

/-- A skew-adjoint operator perturbed by a bounded skew-adjoint operator is skew-adjoint. -/
theorem IsSkewAdjoint.vadd (hA : A.IsSkewAdjoint) {B : E →L[𝕜] E}
    (hB : ContinuousLinearMap.adjoint B = -B) : ((B : E →ₗ[𝕜] E) +ᵥ A).IsSkewAdjoint := by
  unfold IsSkewAdjoint
  rw [adjoint_vadd A hA.dense_domain, hA, hB, ← neg_vadd_neg]
  rfl

end LinearPMap
