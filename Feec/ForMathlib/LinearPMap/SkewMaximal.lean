module

public import Feec.ForMathlib.LinearPMap.Skew

/-!
# Skew-adjoint operators are maximal skew

A skew-adjoint operator `A` (`A† = -A`) has no proper skew extension: if a pair `(x, y)` pairs
with the graph of `A` as a graph point would, `⟪y, z⟫ = -⟪x, A z⟫` for every `z ∈ D(A)`, then
`x ∈ D(A)` and `A x = y` (`LinearPMap.IsSkewAdjoint.mem_graph_of_inner`). So an operator given by
a skew relation (`⟪V, U'⟫ = -⟪U, V'⟫` on its pairs) that contains the graph of `A` is `A`: the
form in which a weak formulation is identified with a skew-adjoint generator (the skew analogue
of the maximality of self-adjoint operators among symmetric ones).
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →ₗ.[𝕜] E}

/-- **A skew-adjoint operator is maximal skew**: if `⟪y, z⟫ = -⟪x, A z⟫` for every `z ∈ D(A)`,
then `x ∈ D(A)` and `A x = y`. -/
theorem IsSkewAdjoint.mem_graph_of_inner (hA : A.IsSkewAdjoint) {x y : E}
    (h : ∀ z : A.domain, ⟪y, (z : E)⟫_𝕜 = -⟪x, A z⟫_𝕜) : (x, y) ∈ A.graph := by
  have h' : ∀ z : A.domain, ⟪-y, (z : E)⟫_𝕜 = ⟪x, A z⟫_𝕜 := fun z => by
    rw [inner_neg_left, h z, neg_neg]
  have hx : x ∈ A†.domain := mem_adjoint_domain_of_exists x ⟨-y, h'⟩
  have he : A† ⟨x, hx⟩ = -y := adjoint_apply_eq hA.dense_domain ⟨x, hx⟩ h'
  have hg : (x, -y) ∈ A†.graph := by
    rw [← he]; exact A†.mem_graph ⟨x, hx⟩
  rw [hA, mem_graph_neg_iff, neg_neg] at hg
  exact hg

end LinearPMap
