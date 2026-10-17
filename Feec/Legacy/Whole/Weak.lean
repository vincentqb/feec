module

public import Feec.Legacy.Whole.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `H(curl)` on `ℝ³`: the Fourier multiplier is the weak curl

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `WholeWeak.ev`: The coordinate vectors `e_c` of `ℝ³`.

## References

* [QuennevilleBelair2015], §3.4, §4.10 (the row-wise curl and `H(curl)`)
* Mathlib, `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier` (Fourier transform of
  derivatives of Schwartz functions), `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`
  (fundamental lemma of the calculus of variations)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology SchwartzMap FourierTransform ContDiff
open MeasureTheory Set Filter

namespace Feec.Legacy.WholeWeak

open Feec.Legacy.Torus Feec.Legacy.Whole

section Schwartz

/-- The coordinate vectors `e_c` of `ℝ³`. -/
abbrev ev (c : Fin 3) : Freq := EuclideanSpace.single c 1

end Schwartz

end Feec.Legacy.WholeWeak
