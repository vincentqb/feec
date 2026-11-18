module

public import Solution.Legacy
public import Feec.HilbertComplex.Approximation.StaticCochain
public import Feec.ForMathlib.InnerProductSpace.Basic

/-!
# The bridge from the challenge to `Feec`

The vocabulary of `Challenge.lean` restates over Mathlib the objects of `Feec`: a Hilbert complex
of the challenge is a `Feec.HilbertComplex` on `ComplexShape.up ℤ` (`HilbertComplex.toFeec`, the
same fields), with the same boundaries (`HilbertComplex.boundaries_eq`), so closed ranges are
`Feec`'s (`HilbertComplex.closedRangeAt_iff`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-- The complex as a `Feec` Hilbert complex on `ComplexShape.up ℤ`. -/
def toFeec : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W where
  d := H.d
  shape := H.shape
  dense := H.dense
  closed := H.closed
  mapsTo := H.mapsTo
  d_comp_d := H.d_comp_d

theorem rel_sub_one (i : ℤ) : (ComplexShape.up ℤ).Rel (i - 1) i := sub_add_cancel i 1

theorem boundaries_eq (i : ℤ) : H.toFeec.boundaries i = H.boundaries i :=
  H.toFeec.boundaries_eq (rel_sub_one i)

theorem closedRangeAt_iff (i : ℤ) :
    H.toFeec.ClosedRangeAt i ↔ IsClosed (H.boundaries i : Set (W i)) := by
  rw [Feec.HilbertComplex.ClosedRangeAt, boundaries_eq]

theorem starProjection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K K' : Submodule 𝕜 E} (h : K = K') [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection]
    (x : E) : K.starProjection x = K'.starProjection x := by
  subst h; rfl

end HilbertComplex

end FEEC
