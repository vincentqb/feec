module

public import Solution.Bridge

/-!
# Von Neumann's inequality and A-stable time stepping (solution)

The theorems of `Challenge.lean`, proved from `Feec`: von Neumann's inequality from
`ContinuousLinearMap.norm_aeval_le_of_norm_le_one`, its rational form from
`ContinuousLinearMap.norm_aeval_mul_inverse_le`, and the dissipative form from
`Feec.TimeStepping.RationalScheme.isUnit_aeval_den` and
`Feec.TimeStepping.RationalScheme.norm_apply_le` (von Neumann's inequality for the Cayley
transform of `τA`, through the complexification over `𝕜 = ℝ`) through the bridge
`Solution.Bridge`.

## References

* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3
* [M. Crouzeix, S. Larsson, S. Piskarev, V. Thomée, *The stability of rational approximations of analytic semigroups*][CrouzeixLarssonPiskarevThomee1993]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Polynomial Feec.TimeStepping

@[expose] public noncomputable section

namespace VonNeumann

/-- **Von Neumann's inequality** ([VonNeumann1951]). -/
theorem inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T : E →L[ℂ] E}
    (hT : ‖T‖ ≤ 1) (p : ℂ[X]) {C : ℝ} (hC : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖p.eval ζ‖ ≤ C) :
    ‖aeval T p‖ ≤ C :=
  ContinuousLinearMap.norm_aeval_le_of_norm_le_one hT hC

/-- **Von Neumann's inequality for rational functions** ([VonNeumann1951]). -/
theorem inequality_rational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) (p q : ℂ[X])
    (hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0) {C : ℝ}
    (hC : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖p.eval ζ / q.eval ζ‖ ≤ C) :
    IsUnit (aeval T q) ∧ ‖aeval T p * Ring.inverse (aeval T q)‖ ≤ C :=
  ContinuousLinearMap.norm_aeval_mul_inverse_le hT hq fun ζ hζ _ => hC ζ hζ

/-- **A-stable schemes are unconditionally stable** ([HairerWanner1996], §IV.3;
[CrouzeixLarssonPiskarevThomee1993]). -/
theorem inequality_dissipative {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →L[𝕜] E}
    (hA : ∀ x, RCLike.re ⟪A x, x⟫_𝕜 ≤ 0) (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    {C : ℝ} (hC : ∀ z : ℂ, z.re ≤ 0 → ‖aeval z p / aeval z q‖ ≤ C) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsUnit (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜))) ∧
      ‖aeval ((τ : 𝕜) • A) (p.map (algebraMap ℝ 𝕜)) *
        Ring.inverse (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜)))‖ ≤ C := by
  set r := RationalScheme.ofHalfPlane p q hq hC
  have hτA := RationalScheme.dissipative_smul hA hτ
  refine ⟨r.isUnit_aeval_den hτA, ?_⟩
  rw [← apply_ofHalfPlane hq hC]
  exact (r.norm_apply_le hτA).trans (RationalScheme.supNorm_ofHalfPlane_le hq hC)

end VonNeumann
