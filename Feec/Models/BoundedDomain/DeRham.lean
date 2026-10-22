module

public import Feec.Domain.DeRham

/-!
# The `L²` de Rham complex of `ℝ³` on an open set

The `L²` de Rham complex `L²(Ω) --grad--> L²(Ω; 𝕜³) --curl--> L²(Ω; 𝕜³) --div--> L²(Ω)` on an
open `Ω ⊆ ℝ³`, with its two boundary-condition families and their duality, is the case `n = 3` of
the de Rham complex of `k`-forms `Feec.Domain.deRham` (`Feec.Domain.DeRham`, with the component
formulas `Feec.Domain.extDerivOp_zero_apply`, `Feec.Domain.extDerivOp_one_apply_pair`,
`Feec.Domain.extDerivOp_two_apply_triple` identifying `d` with grad, curl and div). This module
adds no declarations.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (the `L²` de Rham complex and
  its two boundary-condition families)

Bibliography: [references.bib](../../../docs/references.bib)
-/
