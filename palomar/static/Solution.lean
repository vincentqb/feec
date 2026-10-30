module

public import Solution.Bridge

/-!
# The static FEEC theorem (solution)

`FEEC.staticFEEC` of `Challenge.lean`, proved from `Feec.HilbertComplex.SubcomplexFamily.staticFEEC`
through the bridge `Solution.Bridge` (`HilbertComplex.SubcomplexFamily.staticVerdict`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open Filter Topology

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- **The static FEEC theorem** ([AFW2010], Thms 3.4–3.6, 3.8, 3.9). Let `F` be a family of
subcomplexes whose cochain projections are bounded uniformly in the graph norm in degrees `j - 1`
and `j`. If the ranges `𝔅ʲ` of `dʲ⁻¹` and `𝔅ʲ⁺¹` of `dʲ` are closed, `F` satisfies the static
verdict in degree `j` (`SubcomplexFamily.StaticVerdict`). -/
theorem staticFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} (F : H.SubcomplexFamily κ) (j : ℤ)
    (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) : F.StaticVerdict j :=
  F.staticVerdict j hπ hπ' hj hj'

end FEEC
