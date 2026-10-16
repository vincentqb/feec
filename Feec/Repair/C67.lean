module

public import Feec.Repair.C67Prop62
public import Feec.Repair.C67Minres

/-!
# Repair group "Prop 6.2; Ch. 7 MINRES"

* `Feec.Repair.C67Prop62`: thesis Prop 6.2 (well-posedness of the semi-discrete system (6.3))
  in its dynamic-data form (`prop_6_2_dynamic`, `prop_6_2_wellposed`: a solution exists iff
  `u₀ ⊥ d(ker S₀,ₕ)`, it is unique, and `φₕ(0) = Φ(σ₀, f(0))` is forced), and admissibility of
  the projected initial data used by the Ch. 6 convergence theorem (`projected_C2`,
  `projected_C3_iff`, `ch6_convergence_projected`).
* `Feec.Repair.C67Minres`: the Ch. 7 solver claim (MINRES on the CN matrices). The CN matrix
  `M + sK` is not symmetric (`cn_matrix_not_isSymm`, `cnSystem_not_isSymm_of_ne`); its
  `J`-symmetrization is symmetric, nonsingular and indefinite (`minres_symm`,
  `minres_matrix_isUnit`, `minres_matrix_not_posDef`, `minres_matrix_not_negDef`), and its
  unique solution is the coefficient vector of the CN iterate of (4.14) / (4.15)
  (`fullStep_iff_matrix`, `minres_solution_iff_cnStep`, `minres_solution_iff_redStep`).

See [QuennevilleBelair2015, §6.2, Prop 6.2] and [QuennevilleBelair2015, Ch. 7].
-/
