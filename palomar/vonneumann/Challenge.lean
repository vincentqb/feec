module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Von Neumann's inequality and A-stable time stepping

**Von Neumann's inequality** ([VonNeumann1951]): for a contraction `T` (`‖T‖ ≤ 1`) of a complex
inner product space and a complex polynomial `p`,
`‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|` (`VonNeumann.inequality`); no completeness is needed. On a
Hilbert space it extends to rational functions `p/q` without poles in the closed unit disc:
`q(T)` is invertible and `‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1} |p(ζ)/q(ζ)|`
(`VonNeumann.inequality_rational`).

**A-stable one-step schemes** ([HairerWanner1996], §IV.3 and §IV.11): a real rational function
`r = p/q` without poles in the closed left half-plane and with `|r(iy)| ≤ C` on the imaginary
axis (by the maximum principle, `|r| ≤ C` on the closed left half-plane) defines the one-step
scheme `u ↦ r(τA) u` for `u' = A u` (an approximation of `e^{τA}` when `r` is consistent). For
every bounded dissipative operator `A` (`re ⟪A x, x⟫ ≤ 0`) of a real or complex Hilbert space
and every step `τ ≥ 0`, `q(τA)` is invertible and `‖r(τA)‖ ≤ C`
(`VonNeumann.inequality_dissipative`). For `C = 1`, the definition of A-stability, the scheme is
unconditionally stable: `‖r(τA)ⁿ‖ ≤ 1` for every `τ ≥ 0` and every `n`.

**m-dissipative operators**: for a possibly unbounded `A` that is dissipative with `μ - A` onto
for some `μ > 0` (m-dissipative, the generators of contraction semigroups, [Pazy1983], §1.4), and every `τ > 0`, exactly one bounded operator `C_τ` maps
`x - τAx` to `x + τAx` on the domain of `A`, the Cayley transform `(1 + τA)(1 - τA)⁻¹`, and it
is a contraction (`VonNeumann.cayley_contraction`). This is how von Neumann's inequality reaches
the half-plane: `r(τA)` is `r̃(C_τ)` for the rational function `r̃(w) = r((w - 1)/(w + 1))`, which
has no poles in the closed unit disc, so `VonNeumann.inequality_rational` bounds it by
`sup_y |r(iy)|` for every m-dissipative `A` (over `ℝ` through the complexification).

The operator `p(T)` is `Polynomial.aeval T p`; `q(T)⁻¹` is `Ring.inverse` in the Banach algebra
of bounded operators; a real polynomial acts over `𝕜` through `Polynomial.map (algebraMap ℝ 𝕜)`.

## References

* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3
  (A-stability), §IV.11 (contractivity, von Neumann's theorem)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983], §1.4
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

/-- **A-stable schemes are unconditionally stable** ([HairerWanner1996], §IV.11). Let
`r = p/q` be a real rational function without poles in the closed left half-plane, with
`|r(iy)| ≤ C` on the imaginary axis (`C = 1`: `r` is A-stable). For every bounded dissipative
operator `A` of a Hilbert space over `𝕜 = ℝ` or `ℂ` and every `τ ≥ 0`, `q(τA)` is invertible
and `‖r(τA)‖ = ‖p(τA) q(τA)⁻¹‖ ≤ C`. -/
theorem inequality_dissipative {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →L[𝕜] E}
    (hA : ∀ x, RCLike.re ⟪A x, x⟫_𝕜 ≤ 0) (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    {C : ℝ} (hC : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ C) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    IsUnit (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜))) ∧
      ‖aeval ((τ : 𝕜) • A) (p.map (algebraMap ℝ 𝕜)) *
        Ring.inverse (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜)))‖ ≤ C := by
  sorry

/-- **The Cayley transform of an m-dissipative operator is a contraction**. Let `A` be a
possibly unbounded operator of a Hilbert space over `𝕜 = ℝ` or `ℂ`, dissipative
(`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A` onto for some `μ > 0` (m-dissipative,
[Pazy1983], §1.4). For every `τ > 0`, exactly one bounded operator `T` satisfies
`T (x - τAx) = x + τAx` for all `x` in the domain, the Cayley transform
`C_τ = (1 + τA)(1 - τA)⁻¹`, and `‖C_τ‖ ≤ 1`. -/
theorem cayley_contraction {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y) {τ : ℝ}
    (hτ : 0 < τ) :
    ∃ Cτ : E →L[𝕜] E, ‖Cτ‖ ≤ 1 ∧ ∀ T : E →L[𝕜] E,
      (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x + (τ : 𝕜) • A x) ↔ T = Cτ := by
  sorry

end VonNeumann
