module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the theorems
`VonNeumann.inequality`, `VonNeumann.inequality_rational`, `VonNeumann.inequality_dissipative`,
`VonNeumann.inequality_mdissipative`, their real forms `VonNeumann.inequality_dissipative_real`
and `VonNeumann.inequality_mdissipative_real`, `VonNeumann.cayley_contraction`,
`VonNeumann.error_bound`, `VonNeumann.error_bound_real`, `VonNeumann.error_bound_mdissipative`
and `VonNeumann.error_bound_mdissipative_real`), compiled against Mathlib alone so that their
elaborated values are those of the challenge: its imports, opens and the one definition
`VonNeumann.IsStrongSolution`. The solution imports this module, the bridge to `Feec` and proves
the eleven theorems (`Solution.lean`).

## References

* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Polynomial Asymptotics

@[expose] public noncomputable section

namespace VonNeumann

/-- `u` is a **strong solution** of `u' = A u` on `I`: continuous on `I`, and at every `t ∈ I`,
`u t` lies in the domain of `A` and `u` has the derivative `A (u t)` within `I`. -/
def IsStrongSolution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] (A : E →ₗ.[𝕜] E) (I : Set ℝ) (u : ℝ → E) : Prop :=
  ContinuousOn u I ∧ ∀ t ∈ I, ∃ v, (u t, v) ∈ A.graph ∧ HasDerivWithinAt u v I t

end VonNeumann
