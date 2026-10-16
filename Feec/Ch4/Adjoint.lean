module

public import Feec.Foundation.Complex
public import Feec.Foundation.Operators
public import Feec.Operator.Adjoint
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Unbounded operators: adjoints, graph relations, closed range (Thesis §4.1–4.2)

This module supplies the unbounded-operator facts that the thesis states without proof in §4.1
and uses throughout Chapter 4. Real Hilbert spaces throughout; `T†` is Mathlib's
`LinearPMap.adjoint`, and all statements carry `Dense T.domain` explicitly (Mathlib's adjoint
takes a junk value otherwise).

The operator-level statements are thin real-scalar specializations of the `RCLike` API in
`Feec.ForMathlib.LinearPMap.{GraphSpace,ClosedRange,Skew}` (all four (4.1) identities, the closed
range theorem and the Poincaré inequality are combined in `LinearPMap.closedRange_tfae`), and the
dual-complex lemmas are specializations of `Feec.Operator` (`Feec.Operator.Adjoint`).

## Coverage

* **Graph relations** (§4.1): `graph_orthogonal` (`Γ(T)ᗮ = Γ̃(T*)`), `closure_graph`
  (`cl Γ(T) = Γ̃(T*)ᗮ`), `graph_eq_orthogonal` (`Γ(T) = Γ̃(T*)ᗮ` for closed `T`), with the
  rotated graph `Γ̃(T*) = {(x, y) | (y, -x) ∈ Γ(T*)}` taken in `E ⊕₂ F`.
* **Closed kernels**: `isClosed_ker` (in `Feec.Foundation.Operators`); the thesis' unrestricted claim (§4.3) is refuted by
  `exists_not_isClosed_ker`.
* `dense_adjoint_domain` (`D(T*)` dense) and `adjoint_adjoint` (`T** = T`), for closed densely
  defined `T`.
* **(4.1a–d)**: (4.1a) is `Feec.orth_range_eq_ker_adjoint` (foundation); (4.1b)
  `orthogonal_ker`, (4.1c) `orthogonal_range_adjoint`, (4.1d) `orthogonal_ker_adjoint`.
* **Closed range theorem**: `range_adjoint_eq_orthogonal_ker` (`R(T) closed ⇒ R(T*) = N(T)ᗮ`),
  `isClosed_range_adjoint_iff`, `range_eq_orthogonal_ker_adjoint`; the unbounded Poincaré
  inequality `poincare_of_isClosed_range` and its converse `isClosed_range_of_poincare`, combined
  in `isClosed_range_iff_poincare` (Thm 4.2, W-level form).
* **Self-adjointness and skew-adjointness**: `isSelfAdjoint_iff` (symmetric and `D(T*) ⊂ D(T)`, the thesis'
  stated form), `isSkewAdjoint_iff` (skew version), literal forms `isSelfAdjoint_iff_le_adjoint`,
  `isSkewAdjoint_iff_neg_le_adjoint`, the thesis' definitions of (skew-)symmetric via
  `isSymm_iff_le_adjoint`, `isSkewSymm_iff_neg_le_adjoint`; density of a skew-adjoint domain is
  `IsSkewAdjoint.dense_domain` (in `Feec.Foundation.Operators`).
* **Dual complex** (§4.2): `HilbertComplex2.dual` (with `dual_dual`), `closedRange_dual_iff`
  ("closed ⇒ dual closed") and `range_adjoint_d0_eq` / `range_adjoint_d1_eq` (`B* = Zᗮ`).
* **Hodge decomposition in `W`** (Thm 4.1, `W`-level): `HilbertComplex2.hodge_W`
  (`W1 = cl B⁰ ⊕ ℌ ⊕ cl B*₁`, unconditionally), `hodge_W_of_closedRange` (no closures),
  `harmonic_eq`, `harmonic_eq_ker_inf_orthogonal_range` (thesis' `ℌ = Z¹ ∩ (B¹)ᗮ`), the end
  positions `hodge_W0` (`W0 = Z⁰ ⊕ cl B*₀`), `hodge_W2` (`W2 = cl B¹ ⊕ Z*₂`) and their
  closed-range forms, `ker_d1_eq` (`Z¹ = cl B⁰ ⊕ ℌ`), `ker_adjoint_d0_eq` (`Z*₀ = ℌ ⊕ cl B*₁`).
* Graph-norm Poincaré `poincare_graphNorm_of_isClosed_range` (literal form of Thm 4.2).

## References

* [QuennevilleBelair2015], §4.1 (unbounded operators, graph relations, (4.1a–d)), §4.2
  (Hilbert complexes, dual complex, Thm 4.1 Hodge decomposition, Thm 4.2 Poincaré inequality),
  §4.3 (closed-kernel claim), proof of Thm 4.6 (`d** = d`)
* [AFW2010], §3 (Hilbert complexes: dual complex, Hodge decomposition, Poincaré inequality;
  followed by the thesis in §4.2)
* [BruningLesch1992] (Hilbert complexes; followed by the thesis in §4.2)
* [Arnold2018] (abstract Hilbert complex framework of FEEC)
-/

open scoped RealInnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec

/-! ### Graph relations, `T** = T`, (4.1a–d), closed range, skew-adjointness

The statements below are the real-scalar (`𝕜 := ℝ`) specializations of the `RCLike` results in
`Feec.ForMathlib.LinearPMap.{GraphSpace,ClosedRange,Skew}`, kept with their old statements. -/

section Adjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The graph `Γ(T)` as a subspace of the Hilbert sum `E ⊕₂ F` (`LinearPMap.graphL2`). -/
abbrev graphL2 (T : E →ₗ.[ℝ] F) : Submodule ℝ (WithLp 2 (E × F)) := T.graphL2

/-- The rotated graph of the adjoint, `Γ̃(T*) = {(x, y) | (y, -x) ∈ Γ(T*)}` (Thesis §4.1)
(`LinearPMap.rotAdjGraph`). -/
abbrev rotAdjGraph (T : E →ₗ.[ℝ] F) : Submodule ℝ (WithLp 2 (E × F)) := T.rotAdjGraph

omit [CompleteSpace E] [CompleteSpace F] in
/-- Membership in `graphL2` (auxiliary, Thesis §4.1). -/
theorem mem_graphL2 {T : E →ₗ.[ℝ] F} {p : WithLp 2 (E × F)} :
    p ∈ graphL2 T ↔ WithLp.ofLp p ∈ T.graph := LinearPMap.mem_graphL2

omit [CompleteSpace F] in
/-- Membership in the rotated graph `Γ̃(T*)` (auxiliary, Thesis §4.1). -/
theorem mem_rotAdjGraph {T : E →ₗ.[ℝ] F} {p : WithLp 2 (E × F)} :
    p ∈ rotAdjGraph T ↔ ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) ∈ T†.graph :=
  LinearPMap.mem_rotAdjGraph

omit [CompleteSpace E] [CompleteSpace F] in
/-- A closed operator has closed graph in `E ⊕₂ F` (auxiliary, Thesis §4.1). -/
theorem isClosed_graphL2 {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) :
    IsClosed (graphL2 T : Set (WithLp 2 (E × F))) :=
  LinearPMap.isClosed_graphL2 hc

omit [CompleteSpace F] in
/-- Graph relation `Γ(T)ᗮ = Γ̃(T*)` (Thesis §4.1), for densely defined `T`.

Thesis gap: stated without proof; the orthogonal complement is in the ℓ² sum `E ⊕₂ F`.

See [QuennevilleBelair2015, §4.1]. -/
theorem graph_orthogonal (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    (graphL2 T)ᗮ = rotAdjGraph T :=
  LinearPMap.graph_orthogonal T hT

/-- `cl Γ(T) = Γ̃(T*)ᗮ` (Thesis §4.1, second graph relation; garbled in the extracted text).
See [QuennevilleBelair2015, §4.1]. -/
theorem closure_graph (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    (graphL2 T).topologicalClosure = (rotAdjGraph T)ᗮ :=
  LinearPMap.closure_graph T hT

/-- `Γ(T) = Γ̃(T*)ᗮ` for closed densely defined `T` (Thesis §4.1, third graph relation).
See [QuennevilleBelair2015, §4.1]. -/
theorem graph_eq_orthogonal (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : graphL2 T = (rotAdjGraph T)ᗮ :=
  LinearPMap.graph_eq_orthogonal T hT hc

/-- Weak characterisation of the graph of a closed densely defined operator:
`(x, y) ∈ Γ(T)` iff `⟪T* w, x⟫ = ⟪w, y⟫` for all `w ∈ D(T*)` (Thesis §4.1, the relation
`Γ(T) = Γ̃(T*)ᗮ` unpacked). -/
theorem mem_graph_iff_of_isClosed {T : E →ₗ.[ℝ] F} (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) {x : E} {y : F} :
    (x, y) ∈ T.graph ↔ ∀ w : T†.domain, ⟪T† w, x⟫ = ⟪(w : F), y⟫ :=
  LinearPMap.mem_graph_iff_of_isClosed hT hc

/-- The adjoint of a closed densely defined operator is densely defined (Thesis §4.1).
See [QuennevilleBelair2015, §4.1]. -/
theorem dense_adjoint_domain (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : Dense (T†.domain : Set F) :=
  LinearPMap.dense_adjoint_domain T hT hc

/-- von Neumann: `T** = T` for closed densely defined `T`.

Thesis gap: stated in passing in the proof of Thm 4.6 ("`d` is a closed operator and so
`d** = d`") and equivalent to the §4.1 graph relation `Γ(T) = Γ̃(T*)ᗮ`, but not proved; density
of `D(d)` is also needed and not mentioned.

See [QuennevilleBelair2015, §4.1 and proof of Thm 4.6]. -/
theorem adjoint_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) (hc : T.IsClosed) :
    T†† = T :=
  LinearPMap.adjoint_adjoint T hT hc

/-- Thesis (4.1c): `R(T*)ᗮ = N(T)` for closed densely defined `T`.
See [QuennevilleBelair2015, (4.1c)]. -/
theorem orthogonal_range_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : (LinearMap.range T†.toFun)ᗮ = T.ker :=
  LinearPMap.orthogonal_range_adjoint T hT hc

/-- Thesis (4.1b): `N(T)ᗮ = cl R(T*)` for closed densely defined `T`.
See [QuennevilleBelair2015, (4.1b)]. -/
theorem orthogonal_ker (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) (hc : T.IsClosed) :
    T.kerᗮ = (LinearMap.range T†.toFun).topologicalClosure :=
  LinearPMap.orthogonal_ker T hT hc

/-- Thesis (4.1d): `N(T*)ᗮ = cl R(T)`; only density of `D(T)` is needed.
See [QuennevilleBelair2015, (4.1d)]. -/
theorem orthogonal_ker_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    T†.kerᗮ = (LinearMap.range T.toFun).topologicalClosure :=
  LinearPMap.orthogonal_ker_adjoint T hT

end Adjoint

/-! ### The closed range theorem -/

section ClosedRange

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Every value of a closed operator is attained on `D(T) ∩ N(T)ᗮ` (auxiliary for the closed
range theorem, Thesis §4.2). -/
theorem exists_orth_preimage {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) (x : T.domain) :
    ∃ z : T.domain, (z : E) ∈ T.kerᗮ ∧ T z = T x :=
  LinearPMap.exists_mem_orthogonal_ker_eq hc x

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T` is injective on `D(T) ∩ N(T)ᗮ` (auxiliary, Thesis §4.2). -/
theorem eq_of_mem_orthogonal_ker {T : E →ₗ.[ℝ] F} {x x' : T.domain} (hx : (x : E) ∈ T.kerᗮ)
    (hx' : (x' : E) ∈ T.kerᗮ) (h : T x = T x') : x = x' :=
  LinearPMap.eq_of_mem_orthogonal_ker hx hx' h

/-- For a closed operator with closed range there is a bounded right inverse
`g : R(T) → D(T) ∩ N(T)ᗮ` (closed graph theorem). See [QuennevilleBelair2015, §4.2]. -/
theorem exists_bounded_inverse (T : E →ₗ.[ℝ] F) (hc : T.IsClosed)
    (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ g : LinearMap.range T.toFun →L[ℝ] E,
      ∀ y, g y ∈ T.kerᗮ ∧ ∃ hy : g y ∈ T.domain, T ⟨g y, hy⟩ = y :=
  LinearPMap.exists_rightInverse_of_isClosed_range T hc hR

/-- Abstract Poincaré inequality for a closed operator with closed range:
`‖x‖ ≤ c ‖T x‖` on `D(T) ∩ N(T)ᗮ` (Thesis Thm 4.2, unbounded/W-level form).

Thesis gap: the statement of Thm 4.2 does not include closed range, which is only assumed in
the surrounding text ("Assuming that `Bᵏ` is closed").

See [QuennevilleBelair2015, Thm 4.2]; cf. [AFW2010, §3] and [Arnold2018]. -/
theorem poincare_of_isClosed_range {T : E →ₗ.[ℝ] F} (hc : T.IsClosed)
    (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ c, ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖ :=
  LinearPMap.exists_norm_le_of_isClosed_range hc hR

/-- Converse of the Poincaré inequality: for a closed operator, a Poincaré bound on
`D(T) ∩ N(T)ᗮ` implies closed range (Thesis Thm 4.2, converse; missing from the thesis). -/
theorem isClosed_range_of_poincare {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) {c : ℝ}
    (hP : ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖) :
    IsClosed (LinearMap.range T.toFun : Set F) :=
  LinearPMap.isClosed_range_of_norm_le hc hP

/-- Thesis Thm 4.2 (unbounded form, with converse): a closed operator has closed range iff it
satisfies a Poincaré inequality on `D(T) ∩ N(T)ᗮ`. See [QuennevilleBelair2015, Thm 4.2]. -/
theorem isClosed_range_iff_poincare {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) :
    IsClosed (LinearMap.range T.toFun : Set F) ↔
      ∃ c, ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖ :=
  LinearPMap.isClosed_range_iff_exists_norm_le hc

/-- Thesis Thm 4.2, literal graph-norm (`V`-norm) form. See [QuennevilleBelair2015, Thm 4.2]. -/
theorem poincare_graphNorm_of_isClosed_range {T : E →ₗ.[ℝ] F} (hc : T.IsClosed)
    (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ C, ∀ x : T.domain, (∀ z : T.domain, T z = 0 → ⟪(z : E), x⟫ + ⟪T z, T x⟫ = 0) →
      Real.sqrt (‖(x : E)‖ ^ 2 + ‖T x‖ ^ 2) ≤ C * ‖T x‖ :=
  LinearPMap.exists_graphNorm_le_of_isClosed_range hc hR

/-- **Closed range theorem**, first half: if `T` is closed, densely defined and `R(T)` is
closed, then `R(T*) = N(T)ᗮ`. Thesis gap (§4.2): asserted without proof.
See [QuennevilleBelair2015, §4.2]; cf. [BruningLesch1992]. -/
theorem range_adjoint_eq_orthogonal_ker (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    LinearMap.range T†.toFun = T.kerᗮ :=
  LinearPMap.range_adjoint_eq_orthogonal_ker T hT hc hR

/-- **Closed range theorem**: for closed densely defined `T`, `R(T*)` is closed iff `R(T)` is.
See [QuennevilleBelair2015, §4.2]; cf. [BruningLesch1992], [AFW2010, §3]. -/
theorem isClosed_range_adjoint_iff (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) :
    IsClosed (LinearMap.range T†.toFun : Set E) ↔ IsClosed (LinearMap.range T.toFun : Set F) :=
  LinearPMap.isClosed_range_adjoint_iff T hT hc

/-- Under closed range, Thesis (4.1d) holds without closure: `R(T) = N(T*)ᗮ` (§4.2).
See [QuennevilleBelair2015, (4.1d), §4.2]. -/
theorem range_eq_orthogonal_ker_adjoint (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hR : IsClosed (LinearMap.range T.toFun : Set F)) :
    LinearMap.range T.toFun = T†.kerᗮ :=
  LinearPMap.range_eq_orthogonal_ker_adjoint T hT hR

end ClosedRange

/-! ### Skew-adjoint operators -/

section Skew

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Thesis §4.1: `T` is skew-adjoint iff it is skew-symmetric and `D(T*) ⊂ D(T)`.
See [QuennevilleBelair2015, §4.1]. -/
theorem isSkewAdjoint_iff (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E)) :
    IsSkewAdjoint L ↔ IsSkewSymm L ∧ L†.domain ≤ L.domain :=
  LinearPMap.isSkewAdjoint_iff hD

/-- Symmetry on the domain, `⟪A x, y⟫ = ⟪x, A y⟫` (definitionally `LinearPMap.IsSymmetric`). -/
def IsSymm (A : E →ₗ.[ℝ] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫ = ⟪(x : E), A y⟫

/-- Thesis §4.1 definition of *symmetric*: `T ≤ T*`. See [QuennevilleBelair2015, §4.1]. -/
theorem isSymm_iff_le_adjoint (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E)) :
    IsSymm L ↔ L ≤ L† :=
  LinearPMap.isSymmetric_iff_le_adjoint hD

/-- Thesis §4.1 definition of *skew-symmetric*: `-T ≤ T*`. See [QuennevilleBelair2015, §4.1]. -/
theorem isSkewSymm_iff_neg_le_adjoint (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E)) :
    IsSkewSymm L ↔ -L ≤ L† :=
  LinearPMap.isSkewSymmetric_iff_neg_le_adjoint hD

/-- Thesis §4.1, literal form: `T` is self-adjoint iff `T ≤ T*` and `D(T*) ⊂ D(T)`.
See [QuennevilleBelair2015, §4.1]. -/
theorem isSelfAdjoint_iff_le_adjoint (L : E →ₗ.[ℝ] E) :
    IsSelfAdjoint L ↔ L ≤ L† ∧ L†.domain ≤ L.domain :=
  LinearPMap.isSelfAdjoint_iff_le_adjoint

/-- Thesis §4.1: a densely defined `T` is self-adjoint iff it is symmetric and `D(T*) ⊂ D(T)`.
See [QuennevilleBelair2015, §4.1]. -/
theorem isSelfAdjoint_iff (L : E →ₗ.[ℝ] E) (hD : Dense (L.domain : Set E)) :
    IsSelfAdjoint L ↔ IsSymm L ∧ L†.domain ≤ L.domain :=
  LinearPMap.isSelfAdjoint_iff hD

/-- Thesis §4.1, literal skew form: `T` is skew-adjoint iff `-T ≤ T*` and `D(T*) ⊂ D(T)`.
See [QuennevilleBelair2015, §4.1]. -/
theorem isSkewAdjoint_iff_neg_le_adjoint (L : E →ₗ.[ℝ] E) :
    IsSkewAdjoint L ↔ -L ≤ L† ∧ L†.domain ≤ L.domain :=
  LinearPMap.isSkewAdjoint_iff_neg_le_adjoint

end Skew

/-! ### Counterexample: kernels of non-closed operators -/

section KerCounterexample

/-- `ℓ²(ℕ, ℝ)`. -/
local notation "ℓ2" => lp (fun _ : ℕ => ℝ) 2

/-! Auxiliary objects for the counterexample, namespaced to avoid clashes. -/
namespace KerCE

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

end KerCE

open KerCE in
/-- Refutation of the thesis claim (§4.3) "the kernel of a (not-necessarily-bounded) linear
operator is closed": the zero operator on the dense, non-closed subspace of finitely supported
sequences in `ℓ²` is densely defined (and bounded on its domain, hence closable), but its
kernel — its whole domain — is not closed. Compare `isClosed_ker`, which needs `T` closed.

Refutes the claim in [QuennevilleBelair2015, §4.3]. -/
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
theorem inner_adjoint_d0 (u : H.d1†.domain) (v : H.d0.domain) : ⟪H.d1† u, H.d0 v⟫ = 0 :=
  Operator.inner_adjoint_apply_eq_zero H.dense1 H.map_mem H.comp_zero u v

/-- `d1* V₂* ⊂ V₁*` (Thesis §4.2, dual complex). -/
theorem adjoint_map_mem (u : H.d1†.domain) : H.d1† u ∈ H.d0†.domain :=
  Operator.adjoint_mapsTo H.dense1 H.map_mem H.comp_zero u

/-- `d0* d1* = 0` (Thesis §4.2, dual complex). -/
theorem adjoint_comp_zero (u : H.d1†.domain) : H.d0† ⟨H.d1† u, H.adjoint_map_mem u⟩ = 0 :=
  Operator.adjoint_comp_eq_zero H.dense0 H.dense1 H.map_mem H.comp_zero u

/-- The dual Hilbert complex `W2 --d1*--> W1 --d0*--> W0` (Thesis §4.2).

Thesis gap: that the `dₖ*` are closed and densely defined and satisfy `d* V* ⊂ V*`,
`d* d* = 0` is asserted without proof; density of `D(d*)` is `dense_adjoint_domain`.

See [QuennevilleBelair2015, §4.2]; cf. [AFW2010, §3], [BruningLesch1992]. -/
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

Thesis gap: implicit in the thesis; it needs `T** = T` (`adjoint_adjoint`).

See [QuennevilleBelair2015, §4.2]. -/
theorem dual_dual : H.dual.dual = H := by
  obtain ⟨d0, d1, dense0, dense1, closed0, closed1, _, _⟩ := H
  simp only [dual, mk.injEq]
  exact ⟨adjoint_adjoint d0 dense0 closed0, adjoint_adjoint d1 dense1 closed1⟩

/-- A Hilbert complex is closed iff its dual complex is closed (Thesis §4.2).

Thesis gap: asserted without proof; it is the closed range theorem
`isClosed_range_adjoint_iff` applied to `d0` and `d1`.

See [QuennevilleBelair2015, §4.2]; cf. [AFW2010, §3], [BruningLesch1992]. -/
theorem closedRange_dual_iff : H.dual.ClosedRange ↔ H.ClosedRange := by
  change IsClosed (LinearMap.range H.d1†.toFun : Set W1) ∧
      IsClosed (LinearMap.range H.d0†.toFun : Set W0) ↔ _
  rw [isClosed_range_adjoint_iff _ H.dense1 H.closed1,
    isClosed_range_adjoint_iff _ H.dense0 H.closed0]
  exact and_comm

/-- `B*₀ = (Z⁰)ᗮ` for a closed complex (Thesis §4.2, used in Thm 4.1).
See [QuennevilleBelair2015, §4.2]. -/
theorem range_adjoint_d0_eq (h : H.ClosedRange) :
    LinearMap.range H.d0†.toFun = H.d0.kerᗮ :=
  range_adjoint_eq_orthogonal_ker _ H.dense0 H.closed0 h.1

/-- `B*₁ = (Z¹)ᗮ` for a closed complex (Thesis §4.2, used in Thm 4.1).
See [QuennevilleBelair2015, §4.2]. -/
theorem range_adjoint_d1_eq (h : H.ClosedRange) :
    LinearMap.range H.d1†.toFun = H.d1.kerᗮ :=
  range_adjoint_eq_orthogonal_ker _ H.dense1 H.closed1 h.2

/-! ### Hodge decomposition in `W` (Thesis Thm 4.1, `W`-level) -/

/-- Harmonic forms `ℌ¹ = Z¹ ∩ Z*₁ = N(d1) ∩ N(d0*)` (Thesis §4.2, Thm 4.1).
See [QuennevilleBelair2015, §4.2]; cf. [AFW2010, §3]. -/
def harmonic : Submodule ℝ W1 := H.d1.ker ⊓ H.d0†.ker

/-- `(B⁰)ᗮ = Z*₀`, i.e. (4.1a) for `d0`. -/
theorem orthogonal_range_d0 : (LinearMap.range H.d0.toFun)ᗮ = H.d0†.ker :=
  orth_range_eq_ker_adjoint _ H.dense0

/-- `(B*₁)ᗮ = Z¹`, i.e. (4.1c) for `d1`. -/
theorem orthogonal_range_adjoint_d1 : (LinearMap.range H.d1†.toFun)ᗮ = H.d1.ker :=
  orthogonal_range_adjoint _ H.dense1 H.closed1

/-- `B⁰ ⊂ Z¹` (from `d1 d0 = 0`). -/
theorem range_d0_le_ker_d1 : LinearMap.range H.d0.toFun ≤ H.d1.ker :=
  Operator.range_le_ker H.map_mem H.comp_zero

/-- `(Z¹)ᗮ ⊆ Z*₁`, i.e. `(ker d1)ᗮ ⊆ ker d0*`, **without closed range**: since `B⁰ ⊆ Z¹`,
`(Z¹)ᗮ ⊆ (B⁰)ᗮ = Z*₀` (Thesis Thm 4.6, σ-step).

Thesis gap: the thesis uses `(Z¹)ᗮ = B*₁`, which needs closed range; only the inclusion
`(ker d1)ᗮ ⊆ ker d0*` is needed, and it holds in every Hilbert complex.

See [QuennevilleBelair2015, proof of Thm 4.6]. -/
theorem orthogonal_ker_d1_le : H.d1.kerᗮ ≤ H.d0†.ker :=
  Operator.orthogonal_ker_le_ker_adjoint H.dense0 H.map_mem H.comp_zero

/-- `(Z*₁)ᗮ = cl B⁰ ⊆ Z¹`, i.e. `(ker d0*)ᗮ ⊆ ker d1`, **without closed range**
(Thesis Thm 4.6, ρ-step, omitted in the thesis as "similar").
See [QuennevilleBelair2015, proof of Thm 4.6]. -/
theorem orthogonal_ker_adjoint_d0_le : H.d0†.kerᗮ ≤ H.d1.ker :=
  Operator.orthogonal_ker_adjoint_le_ker H.dense0 H.closed1 H.map_mem H.comp_zero

/-- `ℌ = (cl B⁰)ᗮ ∩ (cl B*₁)ᗮ` (Thesis Thm 4.1, `W`-level). -/
theorem harmonic_eq :
    H.harmonic = (LinearMap.range H.d0.toFun).topologicalClosureᗮ ⊓
      (LinearMap.range H.d1†.toFun).topologicalClosureᗮ := by
  rw [Submodule.orthogonal_closure, Submodule.orthogonal_closure, orthogonal_range_d0,
    orthogonal_range_adjoint_d1, harmonic, inf_comm]

/-- `cl B⁰ ⟂ ℌ` (Thesis Thm 4.1, `W`-level). -/
theorem isOrtho_closure_range_d0_harmonic :
    (LinearMap.range H.d0.toFun).topologicalClosure ⟂ H.harmonic :=
  (Submodule.isOrtho_iff_le.2 (H.harmonic_eq ▸ inf_le_left)).symm

/-- `ℌ ⟂ cl B*₁` (Thesis Thm 4.1, `W`-level). -/
theorem isOrtho_harmonic_closure_range_adjoint_d1 :
    H.harmonic ⟂ (LinearMap.range H.d1†.toFun).topologicalClosure :=
  Submodule.isOrtho_iff_le.2 (H.harmonic_eq ▸ inf_le_right)

/-- `cl B⁰ ⟂ cl B*₁` (Thesis Thm 4.1, `W`-level). -/
theorem isOrtho_closure_range_d0_closure_range_adjoint_d1 :
    (LinearMap.range H.d0.toFun).topologicalClosure ⟂
      (LinearMap.range H.d1†.toFun).topologicalClosure := by
  rw [Submodule.isOrtho_iff_le, Submodule.orthogonal_closure, orthogonal_range_adjoint_d1]
  exact Submodule.topologicalClosure_minimal _ H.range_d0_le_ker_d1 (isClosed_ker H.closed1)

/-- `Z¹ = cl B⁰ ⊕ ℌ` (orthogonal sum; Thesis §4.2, `W`-level). -/
theorem ker_d1_eq :
    H.d1.ker = (LinearMap.range H.d0.toFun).topologicalClosure ⊔ H.harmonic := by
  set A := (LinearMap.range H.d0.toFun).topologicalClosure
  set C := (LinearMap.range H.d1†.toFun).topologicalClosure
  have : CompleteSpace A := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hC : Cᗮ = H.d1.ker := by
    rw [Submodule.orthogonal_closure, orthogonal_range_adjoint_d1]
  have hAC : A ≤ Cᗮ := Submodule.isOrtho_iff_le.1
    H.isOrtho_closure_range_d0_closure_range_adjoint_d1
  rw [H.harmonic_eq, ← hC]
  exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hAC).symm

/-- `Z*₀ = ℌ ⊕ cl B*₁` (orthogonal sum; Thesis §4.2, `W`-level). -/
theorem ker_adjoint_d0_eq :
    H.d0†.ker = H.harmonic ⊔ (LinearMap.range H.d1†.toFun).topologicalClosure := by
  set A := (LinearMap.range H.d0.toFun).topologicalClosure
  set C := (LinearMap.range H.d1†.toFun).topologicalClosure
  have : CompleteSpace C := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hA : Aᗮ = H.d0†.ker := by
    rw [Submodule.orthogonal_closure, orthogonal_range_d0]
  have hCA : C ≤ Aᗮ := Submodule.isOrtho_iff_le.1
    H.isOrtho_closure_range_d0_closure_range_adjoint_d1.symm
  rw [H.harmonic_eq, ← hA, sup_comm, inf_comm]
  exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hCA).symm

/-- **Hodge decomposition in `W`** (Thesis Thm 4.1, `W`-level, no closed-range hypothesis):
`W1 = cl B⁰ ⊕ ℌ ⊕ cl B*₁`, an orthogonal sum of closed subspaces.

Extension: the thesis states the decomposition only for closed complexes, obtaining
`B*ₖ = (Zᵏ)ᗮ` from (4.1); this unconditional form with closures strengthens it. The closed
case is `hodge_W_of_closedRange`.

See [QuennevilleBelair2015, Thm 4.1]; cf. [BruningLesch1992] (decomposition with closures,
no closed-range hypothesis), [AFW2010, §3], [Arnold2018]. -/
theorem hodge_W :
    (LinearMap.range H.d0.toFun).topologicalClosure ⊔ H.harmonic ⊔
        (LinearMap.range H.d1†.toFun).topologicalClosure = ⊤ ∧
      (LinearMap.range H.d0.toFun).topologicalClosure ⟂ H.harmonic ∧
      H.harmonic ⟂ (LinearMap.range H.d1†.toFun).topologicalClosure ∧
      (LinearMap.range H.d0.toFun).topologicalClosure ⟂
        (LinearMap.range H.d1†.toFun).topologicalClosure := by
  refine ⟨?_, H.isOrtho_closure_range_d0_harmonic, H.isOrtho_harmonic_closure_range_adjoint_d1,
    H.isOrtho_closure_range_d0_closure_range_adjoint_d1⟩
  set C := (LinearMap.range H.d1†.toFun).topologicalClosure
  have : CompleteSpace C := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hC : Cᗮ = H.d1.ker := by
    rw [Submodule.orthogonal_closure, orthogonal_range_adjoint_d1]
  rw [← H.ker_d1_eq, ← hC, sup_comm]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- **Hodge decomposition in `W` for a closed complex** (Thesis Thm 4.1, `W`-level):
`W1 = B⁰ ⊕ ℌ ⊕ B*₁` without closures, with `B*₁ = (Z¹)ᗮ` (`range_adjoint_d1_eq`).

Thesis gap: closedness of `B*₁` (needed to drop the closure) is the closed range theorem
`isClosed_range_adjoint_iff`, which the thesis does not prove.

See [QuennevilleBelair2015, Thm 4.1]; cf. [AFW2010, §3], [Arnold2018]. -/
theorem hodge_W_of_closedRange (h : H.ClosedRange) :
    LinearMap.range H.d0.toFun ⊔ H.harmonic ⊔ LinearMap.range H.d1†.toFun = ⊤ ∧
      LinearMap.range H.d0.toFun ⟂ H.harmonic ∧
      H.harmonic ⟂ LinearMap.range H.d1†.toFun ∧
      LinearMap.range H.d0.toFun ⟂ LinearMap.range H.d1†.toFun := by
  have h1 : IsClosed (LinearMap.range H.d1†.toFun : Set W1) :=
    (isClosed_range_adjoint_iff _ H.dense1 H.closed1).2 h.2
  have := H.hodge_W
  rwa [h.1.submodule_topologicalClosure_eq, h1.submodule_topologicalClosure_eq] at this

/-- The thesis' definition of the harmonic forms, `ℌ¹ = Z¹ ∩ (B¹)ᗮ` (Thesis §4.2), agrees with
`harmonic = N(d1) ∩ N(d0*)` by (4.1a). See [QuennevilleBelair2015, §4.2]. -/
theorem harmonic_eq_ker_inf_orthogonal_range :
    H.harmonic = H.d1.ker ⊓ (LinearMap.range H.d0.toFun)ᗮ := by
  rw [orthogonal_range_d0, harmonic]

/-- **Hodge decomposition at the first position** (Thesis Thm 4.1, `W`-level):
`W0 = Z⁰ ⊕ cl B*₀`, an orthogonal sum, with `B*₀ = R(d0*)`. See [QuennevilleBelair2015, Thm 4.1]. -/
theorem hodge_W0 :
    H.d0.ker ⊔ (LinearMap.range H.d0†.toFun).topologicalClosure = ⊤ ∧
      H.d0.ker ⟂ (LinearMap.range H.d0†.toFun).topologicalClosure := by
  have : CompleteSpace H.d0.ker := (isClosed_ker H.closed0).completeSpace_coe
  rw [← orthogonal_ker _ H.dense0 H.closed0]
  exact ⟨Submodule.sup_orthogonal_of_hasOrthogonalProjection, Submodule.isOrtho_orthogonal_right _⟩

/-- **Hodge decomposition at the last position** (Thesis Thm 4.1, `W`-level):
`W2 = cl B¹ ⊕ Z*₂`, an orthogonal sum, with `B¹ = R(d1)` and `Z*₂ = N(d1*)`.
See [QuennevilleBelair2015, Thm 4.1]. -/
theorem hodge_W2 :
    (LinearMap.range H.d1.toFun).topologicalClosure ⊔ H.d1†.ker = ⊤ ∧
      (LinearMap.range H.d1.toFun).topologicalClosure ⟂ H.d1†.ker := by
  set A := (LinearMap.range H.d1.toFun).topologicalClosure
  have : CompleteSpace A := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hA : Aᗮ = H.d1†.ker := by
    rw [Submodule.orthogonal_closure, orth_range_eq_ker_adjoint _ H.dense1]
  rw [← hA]
  exact ⟨Submodule.sup_orthogonal_of_hasOrthogonalProjection, Submodule.isOrtho_orthogonal_right _⟩

/-- `W0 = Z⁰ ⊕ B*₀` for a closed complex (Thesis Thm 4.1, `W`-level, no closures).
See [QuennevilleBelair2015, Thm 4.1]. -/
theorem hodge_W0_of_closedRange (h : H.ClosedRange) :
    H.d0.ker ⊔ LinearMap.range H.d0†.toFun = ⊤ ∧ H.d0.ker ⟂ LinearMap.range H.d0†.toFun := by
  have h0 : IsClosed (LinearMap.range H.d0†.toFun : Set W0) :=
    (isClosed_range_adjoint_iff _ H.dense0 H.closed0).2 h.1
  have := H.hodge_W0
  rwa [h0.submodule_topologicalClosure_eq] at this

/-- `W2 = B¹ ⊕ Z*₂` for a closed complex (Thesis Thm 4.1, `W`-level, no closures).
See [QuennevilleBelair2015, Thm 4.1]. -/
theorem hodge_W2_of_closedRange (h : H.ClosedRange) :
    LinearMap.range H.d1.toFun ⊔ H.d1†.ker = ⊤ ∧ LinearMap.range H.d1.toFun ⟂ H.d1†.ker := by
  have := H.hodge_W2
  rwa [h.2.submodule_topologicalClosure_eq] at this

end HilbertComplex2

end Feec
