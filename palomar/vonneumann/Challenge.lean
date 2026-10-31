module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Von Neumann's inequality and A-stable time stepping

**Von Neumann's inequality** ([VonNeumann1951]): for a contraction `T` (`‖T‖ ≤ 1`) of a complex
inner product space and a complex polynomial `p`, `‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|`
(`VonNeumann.inequality`); no completeness is needed. On a Hilbert space it extends to rational
functions `p/q` without poles in the closed unit disc: `q(T)` is invertible and
`‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1} |p(ζ)/q(ζ)|` (`VonNeumann.inequality_rational`).

**Von Neumann's theorem in the half-plane and A-stable one-step schemes** ([HairerWanner1996],
§IV.3 and §IV.11): a rational function `r = p/q` without poles in the closed left half-plane
defines the one-step scheme `u ↦ r(τA) u` for `u' = A u`; it is A-stable if `|r(iy)| ≤ 1` on the
imaginary axis (by the maximum principle, `|r| ≤ 1` on the closed left half-plane). For every
dissipative operator `A` (`re ⟪A x, x⟫ ≤ 0`), every step `τ` and every `n`,
`‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ`: for bounded `A` and `τ ≥ 0` with `r(τA) = p(τA) q(τA)⁻¹`
(`VonNeumann.inequality_dissipative`), and for m-dissipative, possibly unbounded, `A` (the
generators of contraction semigroups, [Pazy1983], §1.4) and `τ > 0` with `r(τA)` through the
resolvent `S = (1 - τA)⁻¹`: `r(τA) = P(S) Q(S)⁻¹` for `P(s) = sᴺ p(1 - 1/s)` and
`Q(s) = sᴺ q(1 - 1/s)`, `N = deg q`, polynomials since `1 - 1/s = τA` at `s = S`; for bounded `A`
this is `p(τA) Sᴺ (q(τA) Sᴺ)⁻¹ = p(τA) q(τA)⁻¹` (`VonNeumann.inequality_mdissipative`). These are
stated for complex `r` on complex Hilbert spaces, and for real `r` (the stability functions of
Runge–Kutta methods) on real or complex Hilbert spaces (`VonNeumann.inequality_dissipative_real`,
`VonNeumann.inequality_mdissipative_real`). The suprema are taken in `[0, ∞]`. So an A-stable
scheme is unconditionally stable, `‖r(τA)ⁿ‖ ≤ 1` for every step and every `n`. The proof is von
Neumann's inequality for the Cayley transform `C_τ = (1 + τA)(1 - τA)⁻¹`, the unique bounded
operator mapping `x - τAx` to `x + τAx`, a contraction (`VonNeumann.cayley_contraction`), and
`r̃(w) = r((w - 1)/(w + 1))`.

**The error of an A-stable scheme of order `m`** ([BrennerThomee1979]): if moreover
`r(z) - e^z = O(z^{m+1})` at `0`, there is a constant `K`, depending on `r` only, such that
`‖r(τA)ⁿ x - e^{nτA} x‖ ≤ K nτ τᵐ ‖A^{m+1} x‖` for every bounded dissipative `A` of every real
or complex Hilbert space, `τ ≥ 0`, `n` and `x` (`VonNeumann.error_bound`).

The operator `p(T)` is `Polynomial.aeval T p`; `q(T)⁻¹` is `Ring.inverse` in the Banach algebra
of bounded operators; a real polynomial acts over `𝕜` through `Polynomial.map (algebraMap ℝ 𝕜)`;
`e^{tA}` is `NormedSpace.exp`.

## References

* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3
  (A-stability, order), §IV.11 (contractivity, von Neumann's theorem)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983], §1.4
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Polynomial Asymptotics

@[expose] public noncomputable section

namespace VonNeumann

/-- **Von Neumann's inequality** ([VonNeumann1951]). For a contraction `T` of a complex inner
product space `E`, not necessarily complete, and a complex polynomial `p`,
`‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|`. -/
theorem inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T : E →L[ℂ] E}
    (hT : ‖T‖ ≤ 1) (p : ℂ[X]) :
    ‖aeval T p‖ₑ ≤ ⨆ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖p.eval ζ‖ₑ := by
  sorry

/-- **Von Neumann's inequality for rational functions** ([VonNeumann1951]). For a contraction
`T` of a complex Hilbert space `E` and complex polynomials `p`, `q` with `q` free of zeros in the
closed unit disc, `q(T)` is invertible and `‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1} |p(ζ)/q(ζ)|`. -/
theorem inequality_rational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) (p q : ℂ[X])
    (hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0) :
    IsUnit (aeval T q) ∧
      ‖aeval T p * Ring.inverse (aeval T q)‖ₑ ≤
        ⨆ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖p.eval ζ / q.eval ζ‖ₑ := by
  sorry

/-- **Von Neumann's theorem for dissipative operators** ([HairerWanner1996], §IV.11). Let
`r = p/q` be a complex rational function without poles in the closed left half-plane. For every
bounded dissipative operator `A` of a complex Hilbert space and every `τ ≥ 0`, `q(τA)` is
invertible and `r(τA) = p(τA) q(τA)⁻¹` satisfies `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every `n`. -/
theorem inequality_dissipative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →L[ℂ] E} (hA : ∀ x, (⟪A x, x⟫_ℂ).re ≤ 0) (p q : ℂ[X])
    (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsUnit (aeval ((τ : ℂ) • A) q) ∧ ∀ n : ℕ,
      ‖(aeval ((τ : ℂ) • A) p * Ring.inverse (aeval ((τ : ℂ) • A) q)) ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ₑ) ^ n := by
  sorry

/-- **Von Neumann's theorem for m-dissipative operators**. Let `A` be a possibly unbounded
operator of a complex Hilbert space, dissipative (`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A`
onto for some `μ > 0` (m-dissipative, [Pazy1983], §1.4), `r = p/q` a complex rational function
without poles in the closed left half-plane, `N = deg q` and `τ > 0`. Exactly one bounded
operator `S` satisfies `S (x - τAx) = x` on the domain, the resolvent `(1 - τA)⁻¹`;
`Q(S) = ∑_{k ≤ N} qₖ (S - 1)ᵏ S^{N-k}` is invertible, and `r(τA) = P(S) Q(S)⁻¹`,
`P(S) = ∑_{k ≤ N} pₖ (S - 1)ᵏ S^{N-k}`, satisfies `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every
`n`. -/
theorem inequality_mdissipative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →ₗ.[ℂ] E} (hA : ∀ x : A.domain, (⟪A x, (x : E)⟫_ℂ).re ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : ℂ) • (x : E) - A x = y)
    (p q : ℂ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ S : E →L[ℂ] E,
      (∀ T : E →L[ℂ] E, (∀ x : A.domain, T ((x : E) - (τ : ℂ) • A x) = x) ↔ T = S) ∧
      let P := ∑ k ∈ Finset.range (q.natDegree + 1),
        p.coeff k • ((S - 1) ^ k * S ^ (q.natDegree - k))
      let Q := ∑ k ∈ Finset.range (q.natDegree + 1),
        q.coeff k • ((S - 1) ^ k * S ^ (q.natDegree - k))
      IsUnit Q ∧ ∀ n : ℕ, ‖(P * Ring.inverse Q) ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ₑ) ^ n := by
  sorry

/-- **A-stable schemes are unconditionally stable** ([HairerWanner1996], §IV.11). Let
`r = p/q` be a real rational function without poles in the closed left half-plane. For every
bounded dissipative operator `A` of a Hilbert space over `𝕜 = ℝ` or `ℂ` and every `τ ≥ 0`,
`q(τA)` is invertible and `r(τA) = p(τA) q(τA)⁻¹` satisfies `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for
every `n`. -/
theorem inequality_dissipative_real {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →L[𝕜] E}
    (hA : ∀ x, RCLike.re ⟪A x, x⟫_𝕜 ≤ 0) (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    IsUnit (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜))) ∧ ∀ n : ℕ,
      ‖(aeval ((τ : 𝕜) • A) (p.map (algebraMap ℝ 𝕜)) *
          Ring.inverse (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜)))) ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ₑ) ^ n := by
  sorry

/-- **A-stable schemes are unconditionally stable, for m-dissipative operators**: the real form
of `VonNeumann.inequality_mdissipative`, over `𝕜 = ℝ` or `ℂ`. Let `A` be a
possibly unbounded operator of a Hilbert space over `𝕜`, dissipative
(`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A` onto for some `μ > 0` (m-dissipative,
[Pazy1983], §1.4), `r = p/q` a real rational function without poles in the closed left
half-plane, `N = deg q` and `τ > 0`. Exactly one bounded operator `S` satisfies `S (x - τAx) = x`
on the domain, the resolvent `(1 - τA)⁻¹`; `Q(S) = ∑_{k ≤ N} qₖ (S - 1)ᵏ S^{N-k}` is invertible,
and `r(τA) = P(S) Q(S)⁻¹`, `P(S) = ∑_{k ≤ N} pₖ (S - 1)ᵏ S^{N-k}`, satisfies
`‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every `n`. -/
theorem inequality_mdissipative_real {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y)
    (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ S : E →L[𝕜] E,
      (∀ T : E →L[𝕜] E, (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x) ↔ T = S) ∧
      let P := ∑ k ∈ Finset.range (q.natDegree + 1),
        (p.coeff k : 𝕜) • ((S - 1) ^ k * S ^ (q.natDegree - k))
      let Q := ∑ k ∈ Finset.range (q.natDegree + 1),
        (q.coeff k : 𝕜) • ((S - 1) ^ k * S ^ (q.natDegree - k))
      IsUnit Q ∧ ∀ n : ℕ, ‖(P * Ring.inverse Q) ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ₑ) ^ n := by
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

/-- **The error of an A-stable scheme of order `m`** ([BrennerThomee1979]). Let `r = p/q` be a
real rational function without poles in the closed left half-plane, A-stable (`|r(iy)| ≤ 1`),
of order `m` (`r(z) - e^z = O(z^{m+1})` at `0`). There is a constant `K` such that, for every
bounded dissipative operator `A` of a Hilbert space over `𝕜 = ℝ` or `ℂ`, every `τ ≥ 0`, `n` and
`x`, `‖r(τA)ⁿ x - e^{nτA} x‖ ≤ K nτ τᵐ ‖A^{m+1} x‖`. -/
theorem error_bound (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    (hr : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ 1) {m : ℕ}
    (hm : (fun z : ℂ => aeval z p / aeval z q - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1)) :
    ∃ K : ℝ, ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
      [CompleteSpace E] (A : E →L[𝕜] E), (∀ x, RCLike.re ⟪A x, x⟫_𝕜 ≤ 0) →
      ∀ τ : ℝ, 0 ≤ τ → ∀ (n : ℕ) (x : E),
        ‖((aeval ((τ : 𝕜) • A) (p.map (algebraMap ℝ 𝕜)) *
              Ring.inverse (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜)))) ^ n) x -
            NormedSpace.exp (((n * τ : ℝ) : 𝕜) • A) x‖ ≤
          K * (n * τ) * τ ^ m * ‖(A ^ (m + 1)) x‖ := by
  sorry

end VonNeumann
