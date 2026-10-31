module

public import Solution.Defs
public import Feec.TimeStepping.Rational
public import Feec.TimeStepping.Theta

/-!
# The bridge from the challenge to `Feec`

The challenge is stated over Mathlib's polynomials and bounded operators, the vocabulary of
`Feec.ForMathlib.InnerProductSpace.VonNeumann`, which proves von Neumann's inequality and its
rational form directly, with suprema in `[0, ∞]`; `Feec` states the bounds with a real constant.
`enorm_le_iSup` and `enorm_pow_le_iSup_pow` pass from every real bound to the supremum (vacuous
when the supremum is infinite).

For the dissipative forms, a real rational function `p/q` without poles in the closed left
half-plane and bounded on the imaginary axis is a `Feec.TimeStepping.RationalScheme`
(`Feec.TimeStepping.RationalScheme.ofBounded`, whose `deg p ≤ deg q` follows from the bound along
the imaginary axis), with `sup_y |r(iy)| ≤ C`
(`Feec.TimeStepping.RationalScheme.supNorm_ofBounded_le`); its operator `r(L)` is
`p(L) q(L)⁻¹` by definition (`apply_ofBounded`), and `r(τA)` for an m-dissipative `A` is
`P(S) Q(S)⁻¹` at the resolvent `S = (1 - τA)⁻¹`
(`Feec.TimeStepping.RationalScheme.step_eq_resolventEval`, `resolventEval_map`).

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.11

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ENNReal
open Polynomial Feec.TimeStepping

@[expose] public noncomputable section

namespace VonNeumann

/-- **From real bounds to the supremum in `[0, ∞]`**: if every bound `C` of `‖f i‖` bounds
`‖a‖`, then `‖a‖ₑ ≤ sup_i ‖f i‖ₑ`. -/
theorem enorm_le_iSup {ι : Sort*} {M F : Type*} [SeminormedAddCommGroup M]
    [SeminormedAddCommGroup F] (a : M) (f : ι → F)
    (h : ∀ C : ℝ, (∀ i, ‖f i‖ ≤ C) → ‖a‖ ≤ C) : ‖a‖ₑ ≤ ⨆ i, ‖f i‖ₑ := by
  by_cases hs : (⨆ i, ‖f i‖ₑ) = ∞
  · rw [hs]; exact le_top
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hs]
  refine ENNReal.ofReal_le_ofReal (h _ fun i => ?_)
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono hs (le_iSup (fun i => ‖f i‖ₑ) i)

/-- **Powers**: if every bound `C` of `‖f i‖` bounds `‖a‖`, and `‖1‖ ≤ 1`, then
`‖aⁿ‖ₑ ≤ (sup_i ‖f i‖ₑ)ⁿ`. -/
theorem enorm_pow_le_iSup_pow {ι : Sort*} {M F : Type*} [SeminormedRing M]
    [SeminormedAddCommGroup F] (h1 : ‖(1 : M)‖ ≤ 1) (a : M) (f : ι → F)
    (h : ∀ C : ℝ, (∀ i, ‖f i‖ ≤ C) → ‖a‖ ≤ C) (n : ℕ) :
    ‖a ^ n‖ₑ ≤ (⨆ i, ‖f i‖ₑ) ^ n := by
  rcases n with _ | n
  · rw [pow_zero, pow_zero, ← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h1
  calc ‖a ^ (n + 1)‖ₑ ≤ ‖a‖ₑ ^ (n + 1) := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_pow_le' a n.succ_pos)
    _ ≤ (⨆ i, ‖f i‖ₑ) ^ (n + 1) := pow_le_pow_left' (enorm_le_iSup a f h) _

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `p(L) q(L)⁻¹` is the operator `r(L)` of the scheme `r = p/q`. -/
theorem apply_ofBounded {p q : ℝ[X]} (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {C : ℝ}
    (hC : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ C) (L : E →L[𝕜] E) :
    (RationalScheme.ofBounded p q hq hC).apply L =
      aeval L (p.map (algebraMap ℝ 𝕜)) * Ring.inverse (aeval L (q.map (algebraMap ℝ 𝕜))) :=
  rfl

/-- `P(S) = sᴺ p(1 - 1/s)` at `S`, as written in the challenge. -/
theorem resolventEval_map (N : ℕ) (p : ℝ[X]) (S : E →L[𝕜] E) :
    resolventEval N (p.map (algebraMap ℝ 𝕜)) S =
      ∑ k ∈ Finset.range (N + 1), (p.coeff k : 𝕜) • ((S - 1) ^ k * S ^ (N - k)) := by
  simp only [resolventEval, coeff_map, RCLike.algebraMap_eq_ofReal]

end VonNeumann
