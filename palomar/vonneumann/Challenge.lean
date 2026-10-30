module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Von Neumann's inequality and A-stable time stepping

**Von Neumann's inequality** ([VonNeumann1951]): for a contraction `T` (`‖T‖ ≤ 1`) of a complex
inner product space and a complex polynomial `p`,
`‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|` (`VonNeumann.inequality`); no completeness is needed. On a
Hilbert space it extends to rational functions `p/q` without poles in the closed unit disc:
`q(T)` is invertible and `‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1} |p(ζ)/q(ζ)|`
(`VonNeumann.inequality_rational`).

**A-stable one-step schemes** ([HairerWanner1996], §IV.3; [CrouzeixLarssonPiskarevThomee1993];
[BrennerThomee1979]): a real rational function `r = p/q` with no poles in the closed left
half-plane and `|r(z)| ≤ C` there approximates `e^{τA}` by `u ↦ r(τA) u`. For every bounded
dissipative operator `A` (`re ⟪A x, x⟫ ≤ 0`) of a real or complex Hilbert space and every step
`τ ≥ 0`, `q(τA)` is invertible and `‖r(τA)‖ ≤ C` (`VonNeumann.inequality_dissipative`), von
Neumann's inequality in the half-plane through the Cayley transform. For `C = 1`, the
definition of A-stability, the scheme is unconditionally stable: `‖r(τA)ⁿ‖ ≤ 1` for every `τ ≥ 0`
and every `n`.

The operator `p(T)` is `Polynomial.aeval T p`; `q(T)⁻¹` is `Ring.inverse` in the Banach algebra
of bounded operators; a real polynomial acts over `𝕜` through `Polynomial.map (algebraMap ℝ 𝕜)`.

## References

* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3
* [M. Crouzeix, S. Larsson, S. Piskarev, V. Thomée, *The stability of rational approximations of analytic semigroups*][CrouzeixLarssonPiskarevThomee1993]
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Polynomial

@[expose] public noncomputable section

namespace VonNeumann

/-- **Von Neumann's inequality** ([VonNeumann1951]). For a contraction `T` of a complex inner
product space `E`, not necessarily complete, and a complex polynomial `p` with `|p(ζ)| ≤ C` on
the unit circle, `‖p(T)‖ ≤ C`. -/
theorem inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T : E →L[ℂ] E}
    (hT : ‖T‖ ≤ 1) (p : ℂ[X]) {C : ℝ} (hC : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖p.eval ζ‖ ≤ C) :
    ‖aeval T p‖ ≤ C := by
  sorry

/-- **Von Neumann's inequality for rational functions** ([VonNeumann1951]). For a contraction
`T` of a complex Hilbert space `E` and complex polynomials `p`, `q` with `q` free of zeros in the
closed unit disc and `|p(ζ)/q(ζ)| ≤ C` on the unit circle, `q(T)` is invertible and
`‖p(T) q(T)⁻¹‖ ≤ C`. -/
theorem inequality_rational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) (p q : ℂ[X])
    (hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0) {C : ℝ}
    (hC : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖p.eval ζ / q.eval ζ‖ ≤ C) :
    IsUnit (aeval T q) ∧ ‖aeval T p * Ring.inverse (aeval T q)‖ ≤ C := by
  sorry

/-- **A-stable schemes are unconditionally stable** ([HairerWanner1996], §IV.3;
[CrouzeixLarssonPiskarevThomee1993]). Let `r = p/q` be a real rational function without poles
in the closed left half-plane, with `|r(z)| ≤ C` there (`C = 1`: `r` is A-stable). For every
bounded dissipative operator `A` of a Hilbert space over `𝕜 = ℝ` or `ℂ` and every `τ ≥ 0`,
`q(τA)` is invertible and `‖r(τA)‖ = ‖p(τA) q(τA)⁻¹‖ ≤ C`. -/
theorem inequality_dissipative {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →L[𝕜] E}
    (hA : ∀ x, RCLike.re ⟪A x, x⟫_𝕜 ≤ 0) (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    {C : ℝ} (hC : ∀ z : ℂ, z.re ≤ 0 → ‖aeval z p / aeval z q‖ ≤ C) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsUnit (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜))) ∧
      ‖aeval ((τ : 𝕜) • A) (p.map (algebraMap ℝ 𝕜)) *
        Ring.inverse (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜)))‖ ≤ C := by
  sorry

end VonNeumann
