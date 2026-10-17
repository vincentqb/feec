module

public import Feec.Ch6.TimeDependent

/-!
# Repair of thesis Prop 6.2 (compatibility layer)

The content of this file moved to `Feec.HilbertComplex.BGG.TimeDependent`: the dynamic-data
form of the corrected Prop 6.2 (`Feec.BGG.exists_discreteSolution_iff_compatible_u`,
`Feec.BGG.exists_discreteSolution_unique`), admissibility of projected initial data
(`Feec.BGG.projected_compatible_u`, `Feec.BGG.projected_compatible_phi_iff`), convergence from
projected data (`Feec.BGG.exists_discreteSolution_norm_sub_le`) and the counterexample
(`Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi`). The old names are aliases.

See [QuennevilleBelair2015, §6.2, Prop 6.2].
-/

@[expose] public section

namespace Feec.Repair.C67

alias S1_dt0_of_ker := Feec.BGG.Segment.S1_dt0_eq_zero
alias sol63_C3 := Feec.BGG.DiscreteSolution.inner_dt0_phi_eq
alias sol63_phi_eq := Feec.BGG.DiscreteSolution.phi_eq
alias sol63_phi_zero := Feec.BGG.DiscreteSolution.phi_zero
alias prop_6_2_dynamic := Feec.BGG.exists_discreteSolution_iff_compatible_u
alias prop_6_2_wellposed := Feec.BGG.exists_discreteSolution_unique
alias projected_C2 := Feec.BGG.projected_compatible_u
alias projected_C3_iff := Feec.BGG.projected_compatible_phi_iff
alias ch6_convergence_projected := Feec.BGG.exists_discreteSolution_norm_sub_le

/-- The zero space. -/
abbrev E0 := Feec.Counterexamples.ConstrainedEvolution.E0
alias E0_eq_zero := Feec.Counterexamples.ConstrainedEvolution.E0_eq_zero
/-- BGG data with `Ṽ⁰ = Ṽ¹ = ℝ`, `d = id` on `Ṽ⁰`, all other spaces zero. -/
abbrev cexD := Feec.Counterexamples.ConstrainedEvolution.projSegment
/-- `ι(σ, u, M, ρ) = u`. -/
abbrev cexι := Feec.Counterexamples.ConstrainedEvolution.projι
/-- The form `Ah((x, z), (y, w)) = −x w + z y`. -/
abbrev cexAh := Feec.Counterexamples.ConstrainedEvolution.projAh
alias projected_Q0_counterexample := Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi
alias projected_Q0_counterexample_sol := Feec.Counterexamples.ConstrainedEvolution.exists_discreteSolution_projected_ne

end Feec.Repair.C67
