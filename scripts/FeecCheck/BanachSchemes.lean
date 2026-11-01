module

public import Feec.TimeStepping.RationalHillePhillipsReal

/-!
# Regression test: the `√n`-lossy error bound on complex Banach spaces

`Feec.TimeStepping.RationalHillePhillips` stated the `√n`-lossy error bound of a strongly A-stable
rational scheme on complex Banach spaces, with `R = (1 - τA)⁻¹` the Laplace transform of the
semigroup (`RationalScheme.norm_resolventStep_pow_sub_S_le_sqrt`). It is now stated over `ℝ` or
`ℂ`, for every `R` with `R (x - τ A x) = x` on `D(A)`
(`Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent`). The theorem
below states the old result verbatim and derives it at `𝕜 = ℂ` and `R` the Laplace transform.

This file is part of the `FeecCheck` library, not of `Feec`.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

public section

namespace FeecCheck.BanachSchemes

open Feec Feec.TimeStepping

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

/-- The earlier `RationalScheme.norm_resolventStep_pow_sub_S_le_sqrt` ([BrennerThomee1979] for
the stability bound), on complex Banach spaces with `R` the Laplace transform resolvent. -/
theorem norm_resolventStep_pow_sub_S_le_sqrt_old {r : RationalScheme} (hr : r.IsStronglyAStable)
    {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      M * (1 + r.stabilityConst * √n) *
        (M * (r.remainder p).hpMeasure.variation + M / (p + 1).factorial) * M * (n * τ) *
          τ ^ p * ‖u (p + 1)‖ :=
  RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent G hM hr hp hτ
    (fun _ _ h => G.laplaceResolvent_apply_sub hM hτ.le h) n hu

end FeecCheck.BanachSchemes
