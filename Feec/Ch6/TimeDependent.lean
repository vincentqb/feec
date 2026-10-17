module

public import Feec.Foundation.BGG
public import Feec.HilbertComplex.BGG.TimeDependent

/-!
# Chapter 6: the time-dependent BGG construction (compatibility layer)

The content of this file moved to `Feec.HilbertComplex.BGG.TimeDependent`: the problems (6.1),
(6.2) (`Feec.BGG.WaveData`), the semi-discrete system (6.3) (`Feec.BGG.DiscreteSolution`), the
corrected Prop 6.2, the error equations of Prop 6.3 and the convergence theorem. The old names
below are aliases of the new declarations, with the same statements.

## References

* [QuennevilleBelair2015], Ch. 6 (§6.1 (6.1)/(6.2), Prop 6.1; §6.2 (6.3), Prop 6.2, Prop 6.3)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Ch6

alias hasDerivWithinAt_Ici_unique := Feec.BGG.hasDerivWithinAt_Ici_unique
alias hasDerivWithinAt_Ici_eq_zero := Feec.BGG.hasDerivWithinAt_Ici_eq_zero

/-- `‖x‖² = 0`-type extraction used repeatedly: `⟪x, x⟫ = 0 → x = 0`. -/
@[deprecated inner_self_eq_zero +typeChanged (since := "2026-10-16")]
lemma eq_zero_of_inner_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (h : ⟪x, x⟫ = 0) : x = 0 :=
  inner_self_eq_zero.mp h

/-- Continuous data of §6.1 (`Feec.BGG.WaveData`). See [QuennevilleBelair2015, §6.1]. -/
abbrev ContData := @Feec.BGG.WaveData

namespace ContData

/-- The Hilbert space `V⁰ × Ṽ⁰`. -/
abbrev X := @Feec.BGG.WaveData.X
/-- The constraint operator `B(τ, ψ) = dτ − Sψ`. -/
abbrev B := @Feec.BGG.WaveData.B
/-- `J λ = ⟨λ, d· − S·⟩`. -/
abbrev J := @Feec.BGG.WaveData.J
/-- The multiplier space `W̌¹`. See [QuennevilleBelair2015, §6.1]. -/
abbrev Wcheck := @Feec.BGG.WaveData.Wcheck
/-- The functional `ℓ(τ, ψ) = ⟪w, τ⟫ − ⟪v, dψ⟫`. -/
abbrev ell := @Feec.BGG.WaveData.ell
/-- Trajectories of (6.1)/(6.2). -/
abbrev Traj := @Feec.BGG.WaveData.Trajectory
/-- A solution of (6.1). See [QuennevilleBelair2015, §6.1, (6.1)]. -/
abbrev Sol61 := @Feec.BGG.WaveData.Solution
/-- A solution of (6.2). See [QuennevilleBelair2015, §6.1, (6.2)]. -/
abbrev Sol62 := @Feec.BGG.WaveData.MultiplierSolution

alias B_toLp := Feec.BGG.WaveData.B_toLp
alias J_apply := Feec.BGG.WaveData.J_apply
alias J_mem_Wcheck := Feec.BGG.WaveData.J_mem_Wcheck
alias Wcheck_vanish := Feec.BGG.WaveData.Wcheck_vanish
alias mem_Wcheck_of_vanish := Feec.BGG.WaveData.mem_Wcheck_of_vanish
alias Wcheck_eq_range_of_isClosed := Feec.BGG.WaveData.Wcheck_eq_range_of_isClosed
alias ell_toLp := Feec.BGG.WaveData.ell_toLp
alias continuous_ell := Feec.BGG.WaveData.continuous_ell
alias ext_X := Feec.BGG.WaveData.ext_X
alias Sol62.constraint := Feec.BGG.WaveData.MultiplierSolution.constraint
/-- Thesis Prop 6.1, first bullet. See [QuennevilleBelair2015, Prop 6.1]. -/
abbrev Sol62.toSol61 := @Feec.BGG.WaveData.MultiplierSolution.toSolution
alias Sol62.toSol61_toTraj := Feec.BGG.WaveData.MultiplierSolution.toSolution_toTrajectory
alias Sol62.Λ_eq := Feec.BGG.WaveData.MultiplierSolution.Λ_eq
alias prop_6_1_i := Feec.BGG.WaveData.Solution.exists_multiplierSolution
alias Sol62.continuousOn_Λ := Feec.BGG.WaveData.MultiplierSolution.continuousOn_Λ
alias prop_6_1_i_closedRange := Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_isClosed_range
alias prop_6_1_ii := Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense
/-- The energy `‖σ‖² + ‖u‖² + ‖M‖² + ‖ρ‖²`. -/
abbrev Traj.energy := @Feec.BGG.WaveData.Trajectory.energy
alias Sol61.hasDerivWithinAt_energy := Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy
alias Traj.continuousOn_energy := Feec.BGG.WaveData.Trajectory.continuousOn_energy
alias Sol61.energy_const := Feec.BGG.WaveData.Solution.energy_const
alias Sol62.energy_const := Feec.BGG.WaveData.MultiplierSolution.energy_const
/-- Difference of two solutions of (6.1). -/
abbrev Sol61.sub := @Feec.BGG.WaveData.Solution.sub
alias Sol61.unique := Feec.BGG.WaveData.Solution.unique
alias Sol62.unique := Feec.BGG.WaveData.MultiplierSolution.unique

end ContData

alias linear_ode_exists := Feec.BGG.exists_hasDerivAt_linearODE

/-- A solution of the discrete system (6.3). See [QuennevilleBelair2015, §6.2, (6.3)]. -/
abbrev Sol63 := @Feec.BGG.DiscreteSolution

alias Sol63.constraint := Feec.BGG.DiscreteSolution.constraint
alias Sol63.hidden_constraint := Feec.BGG.DiscreteSolution.hidden_constraint
alias no_solution_of_incompatible := Feec.BGG.not_exists_discreteSolution_of_ker
alias no_solution_of_incompatible_phi := Feec.BGG.not_exists_discreteSolution_phi_of_ker
alias prop_6_2_necessary := Feec.BGG.DiscreteSolution.compatible
alias Sol63.hasDerivWithinAt_energy := Feec.BGG.DiscreteSolution.hasDerivWithinAt_energy
alias Sol63.energy_const := Feec.BGG.DiscreteSolution.energy_const
alias Sol63.uniq := Feec.BGG.DiscreteSolution.eq_zero_of_initial_eq_zero
/-- Difference of two solutions of (6.3). -/
abbrev Sol63.sub := @Feec.BGG.DiscreteSolution.sub
alias Sol63.unique := Feec.BGG.DiscreteSolution.unique
/-- `Ψ φ = (S₀,ₕ φ, P_K(d* d φ))`. -/
abbrev psi := @Feec.BGG.psi
alias psi_apply := Feec.BGG.psi_apply
alias inner_psi_snd := Feec.BGG.inner_psi_snd
alias psi_bijective := Feec.BGG.psi_bijective
/-- `Φ(σ, w)`, the algebraic variable of (6.3). -/
abbrev phiMap := @Feec.BGG.phiMap
alias psi_phiMap := Feec.BGG.psi_phiMap
alias S0_phiMap := Feec.BGG.S0_phiMap
alias inner_phiMap := Feec.BGG.inner_phiMap
alias phiMap_eq := Feec.BGG.phiMap_eq
alias exists_adjoint_S0 := Feec.BGG.exists_adjoint_S0
alias adjoint_S0_injective := Feec.BGG.adjoint_S0_injective
alias prop_6_2_exists_regular := Feec.BGG.exists_discreteSolution_regular
alias prop_6_2_exists := Feec.BGG.exists_discreteSolution
alias prop_6_2 := Feec.BGG.exists_discreteSolution_iff
/-- A solution of (6.3) only sees the source on `[0,T)`. -/
abbrev Sol63.ofEqOn := @Feec.BGG.DiscreteSolution.ofEqOn
alias prop_6_2_exists_of_continuousOn := Feec.BGG.exists_discreteSolution_of_continuousOn

/-- `e₁ = (0, 1) ∈ ℝ²`. -/
abbrev cexE1 := Feec.BGG.Counterexample.kerVector
/-- Concrete discrete BGG data refuting Prop 6.2. -/
abbrev cexBGG := Feec.BGG.Counterexample.incompatibleSegment
alias cexBGG_hyps := Feec.BGG.Counterexample.incompatibleSegment_hyps
alias prop_6_2_false := Feec.BGG.Counterexample.not_forall_exists_discreteSolution

alias prop_6_3_a := Feec.BGG.errorEq_a
alias prop_6_3_b := Feec.BGG.errorEq_b
alias prop_6_3_c := Feec.BGG.errorEq_c
alias prop_6_3_c_split := Feec.BGG.errorEq_c_split
alias prop_6_3_d := Feec.BGG.errorEq_d
alias prop_6_3_e := Feec.BGG.errorEq_e

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Energy estimate, integral form: if `⟪ė, e⟫ = ⟪r, e⟫` (skew part dropped after testing with
`e`) and `‖r‖ ≤ g` with `g ≥ 0` continuous, then `‖e(t)‖ ≤ ‖e(0)‖ + ∫₀ᵗ g`.
Cf. [QuennevilleBelair2015, Lemma 4.12]. -/
theorem energy_estimate_integral {e e' r : ℝ → E} {g : ℝ → ℝ} {T : ℝ}
    (he : ContinuousOn e (Icc 0 T))
    (he' : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (heq : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ = ⟪r t, e t⟫)
    (hg : ContinuousOn g (Icc 0 T)) (hg0 : ∀ t, 0 ≤ g t) (hr : ∀ t ∈ Ico 0 T, ‖r t‖ ≤ g t) :
    ∀ t ∈ Icc 0 T, ‖e t‖ ≤ ‖e 0‖ + ∫ s in (0:ℝ)..t, g s :=
  Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := ℝ) he he' hg
    (fun t _ => hg0 t) fun t ht => by
      rw [RCLike.re_to_real, heq t ht]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hr t ht) (norm_nonneg _))

end Convergence

alias ch6_convergence := Feec.BGG.norm_sub_le_of_ellipticProjection
alias ch6_convergence_rate := Feec.BGG.norm_sub_le_mul_of_ellipticProjection
/-- The discrete skew form of (6.3). -/
abbrev a63 := @Feec.BGG.discreteSkewForm
alias a63_self := Feec.BGG.discreteSkewForm_self
alias ch6_convergence_Sol63 := Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection

end Feec.Ch6
