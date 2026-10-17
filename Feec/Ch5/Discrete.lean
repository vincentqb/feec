module

public import Feec.Foundation.BGG
public import Feec.FiniteElement.Dof
public import Feec.HilbertComplex.BGG.Discrete

/-!
# Chapter 5.2: discretization of the weak-symmetry complex (compatibility layer)

The content of this file moved to `Feec.HilbertComplex.BGG.Discrete` (discrete BGG complex with
compatible cochain projections: thesis Props 5.3, 5.4, 5.6, Thm 5.5) and
`Feec.FiniteElement.Dof` (degrees of freedom, commuting interpolants: thesis Prop 5.7, over any
commutative ring). The old names below are aliases of the new declarations, with the same
statements.

## References

* [QuennevilleBelair2015], Ch. 5: §5.2 (Props 5.3, 5.4, 5.6, Thm 5.5), §5.3 (Prop 5.7)
-/

open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace Feec.Ch5.Discrete

/-- Minimum-norm principle: if `u ⊥ K` and `u' - u ∈ K` then `‖u‖ ≤ ‖u'‖`. -/
@[deprecated Submodule.norm_le_of_mem_orthogonal_of_sub_mem +typeChanged
  (since := "2026-10-16")]
theorem norm_le_of_sub_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Submodule ℝ E} {u u' : E} (hu : u ∈ Kᗮ) (h : u' - u ∈ K) : ‖u‖ ≤ ‖u'‖ :=
  Submodule.norm_le_of_mem_orthogonal_of_sub_mem hu h

alias minNorm_bound := Feec.BGG.norm_le_of_mem_orthogonal_ker
alias discrete_anticomm := Feec.BGG.anticomm_of_comm_proj
alias surj_of_54 := Feec.BGG.surjective_of_comp_eq
alias exact_55 := Feec.BGG.exists_of_exact_rows
alias prop54_unique := Feec.BGG.eq_zero_of_mixed_homogeneous
alias prop54_hB_necessary := Feec.BGG.exists_mixed_homogeneous_of_perp
alias prop54_counterexample_noTopExact := Feec.BGG.mixed_not_unique_of_not_exactTop
alias sys56_iff := Feec.BGG.isMixedSolution_iff

/-- The discrete system (5.6). See [QuennevilleBelair2015, §5.2, (5.6)]. -/
abbrev Sys56 := @Feec.BGG.IsMixedSolution

/-- The bilinear form of the discrete system (5.6). -/
abbrev sysForm := @Feec.BGG.mixedForm

alias sysForm_bijective := Feec.BGG.mixedForm_bijective
alias prop54_existsUnique := Feec.BGG.existsUnique_isMixedSolution
alias prop_5_6 := Feec.BGG.mixed_error_eq
alias thm55_lhs_identity := Feec.BGG.mixed_coercivity_eq
alias dof_commute := Feec.FiniteElement.comp_eq_of_dof
alias dof_hS_of_span := Feec.FiniteElement.dof_vanish_of_mem_span
alias dof_commute_of_span := Feec.FiniteElement.comp_eq_of_mem_span

/-- Squared graph norm `‖x‖² + ‖d x‖²`. -/
abbrev gr2 := @Feec.BGG.graphSq

/-- From `a² ≤ c²` and `c ≥ 0` to `a ≤ c`. -/
@[deprecated le_of_pow_le_pow_left₀ +typeChanged (since := "2026-10-16")]
theorem le_of_sq_le {a c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 ≤ c ^ 2) : a ≤ c :=
  le_of_pow_le_pow_left₀ two_ne_zero hc h

/-- Squaring preserves `≤` on nonnegative reals. -/
@[deprecated pow_le_pow_left₀ +typeChanged (since := "2026-10-16")]
theorem sq_le_of_le {a c : ℝ} (ha : 0 ≤ a) (h : a ≤ c) : a ^ 2 ≤ c ^ 2 :=
  pow_le_pow_left₀ ha h 2

/-- Young's inequality `xy ≤ x²/(2θ) + θy²/2`. -/
@[deprecated mul_le_sq_div_add_mul_sq_div (since := "2026-10-16")]
theorem young (x y : ℝ) {θ : ℝ} (hθ : 0 < θ) : x * y ≤ x ^ 2 / (2 * θ) + θ * y ^ 2 / 2 :=
  mul_le_sq_div_add_mul_sq_div x y hθ

/-- Absorption step of the proof of Thm 5.5: if `κN ≤ Σ Dᵢ Lᵢ` with `Lᵢ² ≤ K N`, then
`N ≤ (#terms + 1) K / κ² · Σ Dᵢ²`. -/
@[deprecated Finset.le_mul_sum_sq_of_mul_le_sum_mul (since := "2026-10-16")]
theorem absorb {ι : Type*} (s : Finset ι) (Dd L : ι → ℝ) {κ K N : ℝ} (hκ : 0 < κ) (hK : 0 < K)
    (hL : ∀ i ∈ s, L i ^ 2 ≤ K * N) (h : κ * N ≤ ∑ i ∈ s, Dd i * L i) :
    N ≤ (s.card + 1) * K / κ ^ 2 * ∑ i ∈ s, Dd i ^ 2 :=
  s.le_mul_sum_sq_of_mul_le_sum_mul Dd L hκ hK hL h

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
@[deprecated norm_add_sq_le_two_mul +typeChanged (since := "2026-10-16")]
theorem sq_norm_add_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 :=
  norm_add_sq_le_two_mul x y

/-- `‖x - y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
@[deprecated norm_sub_sq_le_two_mul +typeChanged (since := "2026-10-16")]
theorem sq_norm_sub_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 :=
  norm_sub_sq_le_two_mul x y

/-- `‖x + y + z‖² ≤ 3(‖x‖² + ‖y‖² + ‖z‖²)`. -/
@[deprecated norm_add₃_sq_le_three_mul +typeChanged (since := "2026-10-16")]
theorem sq_norm_add3_le {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) :=
  norm_add₃_sq_le_three_mul x y z

alias gr2_nonneg := Feec.BGG.graphSq_nonneg
alias gr2_sub_le := Feec.BGG.graphSq_sub_le
alias hodget1_of_poincare := Feec.BGG.hodge_bot_of_poincare

/-- Continuous hypotheses of Prop 5.3 (`Feec.BGG.Stability`).
See [QuennevilleBelair2015, Prop 5.3]. -/
abbrev ContHyp := @Feec.BGG.Stability

/-- Discretization of the BGG data (`Feec.BGG.Discrete`). See [QuennevilleBelair2015, §5.2]. -/
abbrev Disc := @Feec.BGG.Discrete

namespace Disc

/-- The compatibility condition (5.4). See [QuennevilleBelair2015, §5.2, (5.4)]. -/
abbrev Hyp54 := @Feec.BGG.Discrete.Compatible

/-- The `h`-dependent squared graph norm on `Ṽ¹`. -/
abbrev gn2 := @Feec.BGG.Discrete.gnSq

/-- Thesis Prop 5.3 constant (a). -/
abbrev Ca := @Feec.BGG.Discrete.Ca
/-- Thesis Prop 5.3 constant (b). -/
abbrev Cb := @Feec.BGG.Discrete.Cb
/-- `1 + C_a`. -/
abbrev Ca1 := @Feec.BGG.Discrete.Ca1
/-- The constant bounding the squared norms of the Thm 5.5 test functions. -/
abbrev KL := @Feec.BGG.Discrete.KL
/-- The constant of Thm 5.5. See [QuennevilleBelair2015, Thm 5.5]. -/
abbrev C55 := @Feec.BGG.Discrete.errorConst
/-- The identity discretization. -/
abbrev top := @Feec.BGG.Discrete.top

alias mem_Γh := Feec.BGG.Discrete.mem_Γh
alias S0h_apply := Feec.BGG.Discrete.S0h_apply
alias S1h_apply := Feec.BGG.Discrete.S1h_apply
alias S0h_mem := Feec.BGG.Discrete.S0h_mem
alias S1h_mem := Feec.BGG.Discrete.S1h_mem
alias anticomm_h := Feec.BGG.Discrete.anticomm_h
alias exact_t1 := Feec.BGG.Discrete.exact_bot_h
alias exact_1 := Feec.BGG.Discrete.exact_top_h
alias dt0_injective := Feec.BGG.Discrete.dt0_injective
alias exact_55_h := Feec.BGG.Discrete.exact_mid_h
alias cons_of_56c := Feec.BGG.Discrete.constraint_of_inner
alias complex_55 := Feec.BGG.Discrete.comp_eq_zero_h
alias Zh_eq_map := Feec.BGG.Discrete.Zh_eq_map
alias decomp_55 := Feec.BGG.Discrete.hodge_h
alias hB := Feec.BGG.Discrete.exists_sub_S0h_eq
alias prop_5_3_a := Feec.BGG.Discrete.poincare_Γh
alias preimage_bound := Feec.BGG.Discrete.preimage_bound
alias prop_5_3_b := Feec.BGG.Discrete.poincare_Zh
alias prop_5_4 := Feec.BGG.Discrete.existsUnique_mixed_h
alias gn2_sub_le := Feec.BGG.Discrete.gnSq_sub_le
alias gn2_nonneg := Feec.BGG.Discrete.gnSq_nonneg
alias KL_ge := Feec.BGG.Discrete.KL_ge
alias KL_ge' := Feec.BGG.Discrete.KL_ge'
alias KL_pos := Feec.BGG.Discrete.KL_pos
alias thm55_absorb_real := Feec.BGG.Discrete.errorEstimate_absorb
alias thm55_final_real := Feec.BGG.Discrete.errorEstimate_final
alias thm_5_5 := Feec.BGG.Discrete.error_estimate
alias top_bounded := Feec.BGG.Discrete.top_bounded
alias top_hyp54 := Feec.BGG.Discrete.top_compatible

end Disc

/-- A small BGG-type complex (`Feec.BGG.Discrete.exampleSegment`). -/
abbrev exampleBGG := Feec.BGG.Discrete.exampleSegment

alias nonvacuous := Feec.BGG.Discrete.exists_nonvacuous

end Feec.Ch5.Discrete
