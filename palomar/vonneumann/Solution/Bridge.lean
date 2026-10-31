module

public import Solution.Defs
public import Feec.TimeStepping.RationalSemigroup
public import Feec.Evolution.WellPosed

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

For the error bounds of m-dissipative operators, the semigroup of the challenge is the
Lumer–Phillips semigroup (`LinearPMap.IsMDissipative.semigroup`): its orbits from `D(A)` are
classical solutions (`Feec.C0Semigroup.isClassicalSolution_orbit` with
`LinearPMap.IsMDissipative.generator_semigroup`), and strong solutions of a dissipative `A` are
unique (`Feec.Evolution.IsStrongSolution.unique`); the challenge's `IsStrongSolution` is
`Feec.Evolution.IsStrongSolution` without forcing (`isStrongSolution_iff`).

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

section Semigroup

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E}

omit [IsScalarTower ℝ 𝕜 E] in
theorem isStrongSolution_iff {I : Set ℝ} {u : ℝ → E} :
    IsStrongSolution A I u ↔ Feec.Evolution.IsStrongSolution A I 0 u := by
  refine ⟨fun h => ⟨h.1, fun t ht => ?_⟩, fun h => ⟨h.continuousOn, fun t ht => ?_⟩⟩
  · obtain ⟨v, hv, hd⟩ := h.2 t ht
    exact ⟨v, hv, by simpa using hd⟩
  · obtain ⟨v, hv, hd⟩ := h.deriv t ht
    exact ⟨v, hv, by simpa using hd⟩

variable [CompleteSpace E]

/-- The orbits of the Lumer–Phillips semigroup from `D(A)` are strong solutions. -/
theorem isStrongSolution_semigroup (hA : A.IsMDissipative) (x : A.domain) (T : ℝ) :
    IsStrongSolution A (Set.Icc 0 T) fun t => hA.semigroup.S t x := by
  have h := hA.semigroup.isClassicalSolution_orbit (U₀ := x)
    (by rw [hA.generator_semigroup]; exact x.2) 0 T
  rw [hA.generator_semigroup] at h
  simp only [sub_zero] at h
  exact isStrongSolution_iff.2 h.toIsStrongSolution

/-- They are the only strong solutions. -/
theorem eqOn_semigroup_of_isStrongSolution (hA : A.IsMDissipative) (x : A.domain) (T : ℝ)
    (u : ℝ → E) (hu0 : u 0 = x) (hu : IsStrongSolution A (Set.Icc 0 T) u) :
    Set.EqOn u (fun t => hA.semigroup.S t x) (Set.Icc 0 T) :=
  (isStrongSolution_iff.1 hu).unique hA.dissipative
    (isStrongSolution_iff.1 (isStrongSolution_semigroup hA x T))
    (by rw [hu0, hA.semigroup.map_zero]; rfl)

end Semigroup

end VonNeumann
