module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Feec.Legacy.Operators
public import Feec.Evolution.Constrained

/-!
# Feec foundation §B: evolution problems

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

Strong solutions of `U' = L U + F`, the explicit well-posedness hypotheses standing in for
Thm 4.3 (Hille–Yosida / Stone, which Mathlib lacks), and the energy lemma behind every
uniqueness statement.

## Main results

* `norm_le_norm_zero_of_inner_deriv_nonpos`: the energy inequality `‖e t‖ ≤ ‖e 0‖` when
  `⟪e', e⟫ ≤ 0`; `energy_zero` is its equality case.
* `IsDissipative A`: `⟪A x, x⟫ ≤ 0` on `D(A)`; skew-symmetric operators are dissipative.
* `IsStrongSolution.norm_sub_le`, `IsStrongSolution.unique`: strong solutions for a dissipative
  generator depend `1`-Lipschitz on the initial datum, hence are unique. This is the only
  uniqueness argument; every other uniqueness statement is a corollary.
* `IsStrongSolution.mem_of_invariant`, `IsStrongSolution.mem_of_isReducing`: constraint
  propagation. If `P_K D(A) ⊆ D(A)` and `A (D(A) ∩ K) ⊆ K` (in particular if `K` reduces `A`),
  a strong solution with datum and forcing in `K` stays in `K`, for any dissipative `A`.
skew-adjoint generators the hypotheses are discharged downstream by Stone's theorem
(`Feec.Legacy.stoneGroup` in `Feec.Legacy.Stone`; `Feec.Legacy.IsSkewAdjoint.wellPosedHom` and
`LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution` in `Feec.Legacy.WaveGroup`).

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

namespace Feec.Legacy

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

/-- A strong solution in the sense of `Feec.Evolution.IsStrongSolution` (graph form, time set
`Icc 0 T`) together with its initial value. -/
theorem IsStrongSolution.toEvolution {L : E →ₗ.[ℝ] E} {T : ℝ} {U₀ : E}
    {F U : ℝ → E} (hU : IsStrongSolution L T U₀ F U) :
    Evolution.IsStrongSolution L (Icc 0 T) F U :=
  Evolution.IsStrongSolution.of_hasDerivWithinAt hU.mem hU.deriv

theorem IsStrongSolution.of_evolution {L : E →ₗ.[ℝ] E} {T : ℝ} {U₀ : E} {F U : ℝ → E}
    (hU : Evolution.IsStrongSolution L (Icc 0 T) F U) (h0 : U 0 = U₀) :
    IsStrongSolution L T U₀ F U :=
  ⟨fun _ => hU.mem_domain, fun _ => hU.hasDerivWithinAt, h0⟩

/-- Homogeneous version (`F = 0`), the form used in Thm 4.6.
See [QuennevilleBelair2015, Thm 4.6]. -/
def WellPosedHom (L : E →ₗ.[ℝ] E) (T : ℝ) : Prop :=
  ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U

/-! ### The energy inequality -/

/-- **Energy inequality**: if `e` is continuous on `[0,T]` with right derivative `e'` on `[0,T)`
and `⟪e', e⟫ ≤ 0`, then `‖e t‖ ≤ ‖e 0‖` on `[0,T]` (`‖e‖²` is non-increasing).
The engine behind every uniqueness and propagation statement (Thm 4.3/4.6/4.7, Cor 4.5, Ch 6).
Abstracts the energy argument of [QuennevilleBelair2015, §4.4]. -/
theorem norm_le_norm_zero_of_inner_deriv_nonpos {e e' : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (hneg : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ ≤ 0) : ∀ t ∈ Icc 0 T, ‖e t‖ ≤ ‖e 0‖ :=
  Evolution.Energy.norm_le_of_re_inner_deriv_nonpos (𝕜 := ℝ) hcont hd hneg

/-- Energy lemma: if `⟪e', e⟫ = 0` on `[0,T)` then `e(0) = 0` forces `e ≡ 0` on `[0,T]`.
The equality case of `norm_le_norm_zero_of_inner_deriv_nonpos`.
Abstracts the energy argument for uniqueness of weak solutions in [QuennevilleBelair2015, §4.4]. -/
theorem energy_zero {e e' : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (horth : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ = 0) (h0 : e 0 = 0) :
    ∀ t ∈ Icc 0 T, e t = 0 := by
  intro t ht
  have := norm_le_norm_zero_of_inner_deriv_nonpos hcont hd (fun s hs => (horth s hs).le) t ht
  rw [h0, norm_zero] at this
  exact norm_le_zero_iff.1 this

/-! ### Dissipative generators: uniqueness and constraint propagation -/

/-- `A` is **dissipative**: `⟪A x, x⟫ ≤ 0` for every `x ∈ D(A)`. Skew-symmetric operators
(`IsSkewSymm.isDissipative`), in particular skew-adjoint ones, are dissipative. -/
def IsDissipative (A : E →ₗ.[ℝ] E) : Prop := ∀ x : A.domain, ⟪A x, (x : E)⟫ ≤ 0

/-- A skew-symmetric operator is dissipative (`⟪A x, x⟫ = 0`). -/
theorem IsSkewSymm.isDissipative {A : E →ₗ.[ℝ] E} (hA : IsSkewSymm A) : IsDissipative A :=
  fun x => (hA.inner_self x).le

/-- **Stability of strong solutions** for a dissipative generator: two strong solutions of
`U' = A U + F` with the same forcing satisfy `‖U(t) - V(t)‖ ≤ ‖U(0) - V(0)‖` on `[0,T]`.
Energy method; no density, closedness, skew-adjointness or semigroup is needed.
See [QuennevilleBelair2015, Thm 4.3] (uniqueness half); cf. [Pazy1983, §1.4].
Shim over `Feec.Evolution.IsStrongSolution.norm_sub_le`. -/
theorem IsStrongSolution.norm_sub_le {A : E →ₗ.[ℝ] E} (hA : IsDissipative A) {T : ℝ}
    {U₀ V₀ : E} {F U V : ℝ → E} (hU : IsStrongSolution A T U₀ F U)
    (hV : IsStrongSolution A T V₀ F V) : ∀ t ∈ Icc 0 T, ‖U t - V t‖ ≤ ‖U₀ - V₀‖ := by
  simpa [hU.init, hV.init] using hU.toEvolution.norm_sub_le hA hV.toEvolution

/-- **Uniqueness of strong solutions** for a dissipative generator: strong solutions of
`U' = A U + F`, `U(0) = U₀` agree on `[0,T]`. Shim over `Feec.Evolution.IsStrongSolution.unique`.
See [QuennevilleBelair2015, Thm 4.3, Thm 4.6] (uniqueness). -/
theorem IsStrongSolution.unique {A : E →ₗ.[ℝ] E} (hA : IsDissipative A) {T : ℝ} {U₀ : E}
    {F U V : ℝ → E} (hU : IsStrongSolution A T U₀ F U) (hV : IsStrongSolution A T U₀ F V) :
    EqOn U V (Icc 0 T) :=
  hU.toEvolution.unique hA hV.toEvolution (hU.init.trans hV.init.symm)

/-- **Constraint propagation** for a dissipative generator: if `P_K D(A) ⊆ D(A)` and
`A (D(A) ∩ K) ⊆ K`, every strong solution of `U' = A U + F` with `U(0) ∈ K` and `K`-valued
forcing stays in `K` on `[0,T]`. Shim over `Feec.Evolution.IsStrongSolution.mem_of_invariant`.
Generalizes [QuennevilleBelair2015, Thm 4.4, Cor 4.5]. -/
theorem IsStrongSolution.mem_of_invariant {A : E →ₗ.[ℝ] E} (hA : IsDissipative A)
    {K : Submodule ℝ E} [K.HasOrthogonalProjection]
    (hP : ∀ x : A.domain, K.starProjection (x : E) ∈ A.domain)
    (hAK : ∀ x : A.domain, (x : E) ∈ K → A x ∈ K) {T : ℝ} {U₀ : E} {F U : ℝ → E}
    (hU : IsStrongSolution A T U₀ F U) (hU₀ : U₀ ∈ K) (hF : ∀ t ∈ Icc 0 T, F t ∈ K) :
    ∀ t ∈ Icc 0 T, U t ∈ K :=
  hU.toEvolution.mem_of_invariant hA hP hAK (hU.init ▸ hU₀) hF

end Evolution

end Feec.Legacy

/-! Sanity check that the API elaborates. -/
section Checks
open Feec.Legacy
example {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : E →ₗ.[ℝ] E) (T : ℝ) :
    WellPosedHom L T ↔ ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U := Iff.rfl
end Checks
