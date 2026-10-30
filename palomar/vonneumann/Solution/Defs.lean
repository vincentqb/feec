module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The definitions of the challenge

A verbatim copy of the definitions of `Challenge.lean` (everything but the theorems
`VonNeumann.inequality`, `VonNeumann.inequality_rational` and `VonNeumann.inequality_dissipative`),
compiled against Mathlib alone so that their elaborated values are those of the challenge; the
challenge defines nothing, so only its imports and opens remain. The solution imports this
module, the bridge to `Feec` and proves the three theorems (`Solution.lean`).

## References

* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Polynomial

@[expose] public noncomputable section

namespace VonNeumann

end VonNeumann
