module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Feec foundation §B: evolution problems

Strong solutions of `U' = L U + F`, the explicit well-posedness hypotheses standing in for
Thm 4.3 (Hille–Yosida / Stone, which Mathlib lacks), and the energy lemma behind every
uniqueness statement. No `axiom`: existence enters only as an explicit hypothesis. For
skew-adjoint generators the hypotheses are discharged downstream by Stone's theorem
(`Feec.stoneGroup` in `Feec.Ch4.Stone`; `Feec.IsSkewAdjoint.wellPosedHom` and
`Feec.IsSkewAdjoint.wellPosedExistence_thm43` in `Feec.Ch4.StoneApplications`).

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3), §4.4 (strong solutions, Thm 4.6, uniqueness by energy)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (the Hille–Yosida corollary the thesis cites for
  Thm 4.3; here only the hypothesis `WellPosedExistence`)
* [Pazy1983], §1.10 (Stone's theorem) and Ch. 4 (inhomogeneous problems): classical background
  for the existence hypothesis
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open Set

namespace Feec

/-! ## §B. Evolution problems: solutions and the well-posedness hypothesis -/

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong solution of `U' = L U + F` on `[0,T]` with `U 0 = U₀`.
Derivatives are within `Icc 0 T` (one-sided at the endpoints). Continuity of `U` in `E`
follows from `deriv`; graph-norm continuity is NOT part of the predicate (no module needs it).
See [QuennevilleBelair2015, Thm 4.3] and the definition of strong solution in §4.4. -/
structure IsStrongSolution (L : E →ₗ.[ℝ] E) (T : ℝ) (U₀ : E) (F U : ℝ → E) : Prop where
  mem : ∀ t ∈ Icc 0 T, U t ∈ L.domain
  deriv : ∀ t (ht : t ∈ Icc 0 T), HasDerivWithinAt U (L ⟨U t, mem t ht⟩ + F t) (Icc 0 T) t
  init : U 0 = U₀

/-- **Explicit hypothesis standing in for Thm 4.3 (Hille–Yosida / Stone), which Mathlib lacks.**
For every initial datum in `D(L)` and every admissible forcing there is a strong solution.
`Adm` abstracts the class "`C([0,T];X) ∩ (W^{1,1}(0,T;X) ∪ L¹(0,T;D(L)))`".
Never assumed as an `axiom`; always a theorem hypothesis. Uniqueness is *proved* (energy).
For skew-adjoint `L` it is a theorem, `Feec.IsSkewAdjoint.wellPosedExistence_thm43` (Stone),
with the forcing class `ForcingThm43`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9] and
[Pazy1983, §1.10, Ch. 4]. -/
def WellPosedExistence (L : E →ₗ.[ℝ] E) (T : ℝ) (Adm : (ℝ → E) → Prop) : Prop :=
  ∀ U₀ ∈ L.domain, ∀ F, Adm F → ∃ U, IsStrongSolution L T U₀ F U

/-- Homogeneous version (`F = 0`), the form used in Thm 4.6.
See [QuennevilleBelair2015, Thm 4.6]. -/
def WellPosedHom (L : E →ₗ.[ℝ] E) (T : ℝ) : Prop :=
  ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U

/-- Energy lemma: if `⟪e', e⟫ = 0` on `[0,T)` then `e(0) = 0` forces `e ≡ 0` on `[0,T]`.
The single engine behind every uniqueness statement (Thm 4.3/4.6/4.7, Cor 4.5, Ch 6).
Abstracts the energy argument for uniqueness of weak solutions in [QuennevilleBelair2015, §4.4]. -/
theorem energy_zero {e e' : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (horth : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ = 0) (h0 : e 0 = 0) :
    ∀ t ∈ Icc 0 T, e t = 0 := by
  have hc : ∀ t ∈ Icc (0:ℝ) T, ‖e t‖ ^ 2 = ‖e 0‖ ^ 2 := by
    refine constant_of_has_deriv_right_zero (f := fun t => ‖e t‖ ^ 2)
      (hcont.norm.pow 2) ?_
    intro t ht
    have := (hd t ht).norm_sq
    rw [real_inner_comm, horth t ht, mul_zero] at this; exact this
  intro t ht
  simpa [h0] using hc t ht

end Evolution

end Feec

/-! Sanity check that the API elaborates. -/
section Checks
open Feec
example {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : E →ₗ.[ℝ] E) (T : ℝ) :
    WellPosedHom L T ↔ ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U := Iff.rfl
end Checks
