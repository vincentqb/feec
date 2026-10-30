module

public import Solution.Defs
public import Feec.TimeStepping.Rational
public import Feec.TimeStepping.Theta

/-!
# The bridge from the challenge to `Feec`

The challenge is stated over Mathlib's polynomials and bounded operators, the vocabulary of
`Feec.ForMathlib.InnerProductSpace.VonNeumann`, which proves von Neumann's inequality and its
rational form directly. For the dissipative form, a real rational function `p/q` without poles
in the closed left half-plane and bounded on the imaginary axis is a
`Feec.TimeStepping.RationalScheme` (`Feec.TimeStepping.RationalScheme.ofBounded`, whose
`deg p ≤ deg q` follows from the bound along the imaginary axis), with `sup_y |r(iy)| ≤ C`
(`Feec.TimeStepping.RationalScheme.supNorm_ofBounded_le`); its operator `r(L)` is
`p(L) q(L)⁻¹` by definition (`Feec.TimeStepping.RationalScheme.apply`).

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.11

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Polynomial Feec.TimeStepping

@[expose] public noncomputable section

namespace VonNeumann

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `p(L) q(L)⁻¹` is the operator `r(L)` of the scheme `r = p/q`. -/
theorem apply_ofBounded {p q : ℝ[X]} (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {C : ℝ}
    (hC : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ C) (L : E →L[𝕜] E) :
    (RationalScheme.ofBounded p q hq hC).apply L =
      aeval L (p.map (algebraMap ℝ 𝕜)) * Ring.inverse (aeval L (q.map (algebraMap ℝ 𝕜))) :=
  rfl

end VonNeumann
