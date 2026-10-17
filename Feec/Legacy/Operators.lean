module

public import Feec.ForMathlib.LinearPMap.Skew
public import Feec.ForMathlib.LinearPMap.GraphSpace
public import Feec.ForMathlib.LinearPMap.Reducing
public import Feec.ForMathlib.LinearPMap.ClosedRange

/-!
# Feec foundation §A: unbounded operators (real-scalar interface)

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

Real-scalar statements of the unbounded-operator API, kept with their old statements while the
old modules exist. Each is a thin specialization (`𝕜 := ℝ`) of the `RCLike` results in
`Feec.ForMathlib.LinearPMap.*`:

* `isClosed_ker` (`LinearPMap.isClosed_ker`), `ker_eq_preimage_graph`;
* `IsSkewAdjoint` (defeq to `LinearPMap.IsSkewAdjoint`), `IsSkewSymm` (defeq to
  `LinearPMap.IsSkewSymmetric`), `IsSkewAdjoint.dense_domain`,
  `IsSkewAdjoint.isSkewSymmetric`, `IsSkewSymm.inner_self`;
* `restrictTo` (`LinearPMap.restrict`);
* `IsReducingPair` / `IsReducing` (abbreviations of `LinearPMap.IsReducingPair` /
  `LinearPMap.IsReducing`), with `IsReducingPair.mapsTo` and `.map_orthogonal_mem`;
* `orth_range_eq_ker_adjoint` (`LinearPMap.orthogonal_range_eq_ker_adjoint`, (4.1a)).

## References

* [QuennevilleBelair2015], §4.1 (unbounded operators, adjoints, (4.1a)), Thm 4.4 (the operator `L̃`)
* [Pazy1983], §1.10 (Stone's theorem)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set

namespace Feec.Legacy

/-! ## Closed kernels -/

section Kernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The kernel of a **closed** unbounded operator is closed. Specialization of
`LinearPMap.isClosed_ker`.

Thesis gap: the thesis (§4.3) asserts this for every "not-necessarily-bounded linear operator";
closedness of `T` is needed (see `Feec.Counterexamples.exists_dense_not_isClosed_ker`).

See [QuennevilleBelair2015, §4.2, §4.3]. -/
theorem isClosed_ker {T : E →ₗ.[ℝ] F} (hc : T.IsClosed) : IsClosed (T.ker : Set E) :=
  LinearPMap.isClosed_ker hc

end Kernel

section Operators
open LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Skew-adjoint (possibly unbounded) operator: `A† = -A` (equal domains). Definitionally
`LinearPMap.IsSkewAdjoint A` (`isSkewAdjoint_iff_linearPMap`).
See [QuennevilleBelair2015, §4.1]; cf. [Pazy1983, §1.10] (Stone's theorem). -/
def IsSkewAdjoint [CompleteSpace E] (A : E →ₗ.[ℝ] E) : Prop := A† = -A

/-- Skew-symmetry on the domain: `⟪A x, y⟫ = -⟪x, A y⟫`. Definitionally
`LinearPMap.IsSkewSymmetric A` (`isSkewSymm_iff_linearPMap`).
See [QuennevilleBelair2015, §4.1] (skew-symmetric operators). -/
def IsSkewSymm (A : E →ₗ.[ℝ] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫ = -⟪(x : E), A y⟫

theorem isSkewAdjoint_iff_linearPMap [CompleteSpace E] {A : E →ₗ.[ℝ] E} :
    IsSkewAdjoint A ↔ A.IsSkewAdjoint := Iff.rfl

theorem isSkewSymm_iff_linearPMap {A : E →ₗ.[ℝ] E} : IsSkewSymm A ↔ A.IsSkewSymmetric := Iff.rfl

/-- (4.1a) `(range T)ᗮ = ker T†` for densely defined `T` (no closedness needed).
Specialization of `LinearPMap.orthogonal_range_eq_ker_adjoint`.
See [QuennevilleBelair2015, §4.1, (4.1a)] (stated there for closed `T`). -/
theorem orth_range_eq_ker_adjoint {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    (LinearMap.range T.toFun)ᗮ = T†.ker :=
  T.orthogonal_range_eq_ker_adjoint hT

/-- A skew-adjoint operator is densely defined. Specialization of
`LinearPMap.IsSkewAdjoint.dense_domain`. -/
theorem IsSkewAdjoint.dense_domain [CompleteSpace E] {A : E →ₗ.[ℝ] E} (hA : IsSkewAdjoint A) :
    Dense (A.domain : Set E) :=
  LinearPMap.IsSkewAdjoint.dense_domain hA

/-- Skew-adjoint ⇒ skew-symmetric. Specialization of
`LinearPMap.IsSkewAdjoint.isSkewSymmetric`. See [QuennevilleBelair2015, §4.1]. -/
theorem IsSkewAdjoint.isSkewSymmetric [CompleteSpace E] {L : E →ₗ.[ℝ] E}
    (hL : IsSkewAdjoint L) : IsSkewSymm L :=
  LinearPMap.IsSkewAdjoint.isSkewSymmetric hL

/-- Skew-adjoint ⇒ skew-symmetric, with a (redundant) density hypothesis; see
`IsSkewAdjoint.isSkewSymmetric`. See [QuennevilleBelair2015, §4.1]. -/
theorem IsSkewAdjoint.isSkewSymm [CompleteSpace E] {L : E →ₗ.[ℝ] E}
    (_hD : Dense (L.domain : Set E)) (hL : IsSkewAdjoint L) : IsSkewSymm L :=
  hL.isSkewSymmetric

/-- Skew-symmetry gives `⟪L x, x⟫ = 0` (the energy identity). Real case of
`LinearPMap.IsSkewSymmetric.re_inner_self`. -/
theorem IsSkewSymm.inner_self {L : E →ₗ.[ℝ] E} (hL : IsSkewSymm L) (x : L.domain) :
    ⟪L x, (x : E)⟫ = 0 :=
  LinearPMap.IsSkewSymmetric.re_inner_self (𝕜 := ℝ) hL x

end Operators

end Feec.Legacy
