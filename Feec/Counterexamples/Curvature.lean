module

public import Feec.Geometry.AlgebraicCurvature

/-!
# Vacuum Einstein equations in dimension two

`G = 0 ⇔ Ric = 0` holds over every field in every dimension `n ≠ 2`
(`Feec.CurvatureTensor.einstein_eq_zero_iff`); in dimension `2` it fails, since
`G = Ric - ½ (tr_g Ric) g` vanishes identically when `Ric = g`
(`exists_einstein_eq_zero_ne_zero_two`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §2.4
* [R. M. Wald, *General Relativity*][Wald1984], §4.3
-/

open Finset Matrix

@[expose] public noncomputable section

namespace Feec.Counterexamples.Curvature

open Feec.CurvatureTensor

/-- In dimension `2` the equivalence `G = 0 ⇔ Ric = 0` fails (`g = gi = Ric = 1`).
[QuennevilleBelair2015], §2.4 -/
theorem exists_einstein_eq_zero_ne_zero_two {K : Type*} [Field K] [Invertible (2 : K)] :
    ∃ g gi Ric : Matrix (Fin 2) (Fin 2) K, gi * g = 1 ∧ einstein g gi Ric = 0 ∧ Ric ≠ 0 := by
  refine ⟨1, 1, 1, by simp, ?_, one_ne_zero⟩
  unfold einstein
  simp only [Matrix.one_mul, Matrix.trace_one, Fintype.card_fin]
  rw [show ((2 : ℕ) : K) = 2 by norm_num, invOf_mul_self, one_smul, sub_self]

end Feec.Counterexamples.Curvature

/-! ### Deprecated names -/

namespace Feec.CurvatureTensor

end Feec.CurvatureTensor
