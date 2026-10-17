module

public import Feec.Counterexamples.BallSymTSD

/-!
# Prop 4.19 on the unit ball (compatibility layer)

Moved to `Feec.Counterexamples.BallSymTSD`; the old names are deprecated aliases.

See [QuennevilleBelair2015, §4.11, Prop 4.19].
-/

@[expose] public section

namespace Feec.BoundedSymDual

@[deprecated (since := "2026-10-17")] alias rho :=
  Counterexamples.BallSymTSD.rho
@[deprecated (since := "2026-10-17")] alias differentiable_rho :=
  Counterexamples.BallSymTSD.differentiable_rho
@[deprecated (since := "2026-10-17")] alias contDiff_rho :=
  Counterexamples.BallSymTSD.contDiff_rho
@[deprecated (since := "2026-10-17")] alias pd_rho :=
  Counterexamples.BallSymTSD.pd_rho
@[deprecated (since := "2026-10-17")] alias pd_comp_rho :=
  Counterexamples.BallSymTSD.pd_comp_rho
@[deprecated (since := "2026-10-17")] alias continuous_rho :=
  Counterexamples.BallSymTSD.continuous_rho
@[deprecated (since := "2026-10-17")] alias rho_nonneg :=
  Counterexamples.BallSymTSD.rho_nonneg
@[deprecated (since := "2026-10-17")] alias sq_le_rho :=
  Counterexamples.BallSymTSD.sq_le_rho
@[deprecated (since := "2026-10-17")] alias abs_le_one_of_rho_le :=
  Counterexamples.BallSymTSD.abs_le_one_of_rho_le
@[deprecated (since := "2026-10-17")] alias norm_le_one_of_rho_le :=
  Counterexamples.BallSymTSD.norm_le_one_of_rho_le
@[deprecated (since := "2026-10-17")] alias ball3 :=
  Counterexamples.BallSymTSD.ball3
@[deprecated (since := "2026-10-17")] alias isOpen_ball3 :=
  Counterexamples.BallSymTSD.isOpen_ball3
@[deprecated (since := "2026-10-17")] alias isBounded_ball3 :=
  Counterexamples.BallSymTSD.isBounded_ball3
@[deprecated (since := "2026-10-17")] alias zero_mem_ball3 :=
  Counterexamples.BallSymTSD.zero_mem_ball3
@[deprecated (since := "2026-10-17")] alias ball3_nonempty :=
  Counterexamples.BallSymTSD.ball3_nonempty
@[deprecated (since := "2026-10-17")] alias eta :=
  Counterexamples.BallSymTSD.eta
@[deprecated (since := "2026-10-17")] alias chi :=
  Counterexamples.BallSymTSD.chi
@[deprecated (since := "2026-10-17")] alias contDiff_eta :=
  Counterexamples.BallSymTSD.contDiff_eta
@[deprecated (since := "2026-10-17")] alias differentiable_eta :=
  Counterexamples.BallSymTSD.differentiable_eta
@[deprecated (since := "2026-10-17")] alias differentiable_deriv_eta :=
  Counterexamples.BallSymTSD.differentiable_deriv_eta
@[deprecated (since := "2026-10-17")] alias deriv_eta :=
  Counterexamples.BallSymTSD.deriv_eta
@[deprecated (since := "2026-10-17")] alias two_le_mul :=
  Counterexamples.BallSymTSD.two_le_mul
@[deprecated (since := "2026-10-17")] alias eta_eq_one :=
  Counterexamples.BallSymTSD.eta_eq_one
@[deprecated (since := "2026-10-17")] alias eta_eq_zero :=
  Counterexamples.BallSymTSD.eta_eq_zero
@[deprecated (since := "2026-10-17")] alias deriv_eta_eq_zero :=
  Counterexamples.BallSymTSD.deriv_eta_eq_zero
@[deprecated (since := "2026-10-17")] alias eta_nonneg :=
  Counterexamples.BallSymTSD.eta_nonneg
@[deprecated (since := "2026-10-17")] alias eta_le_one :=
  Counterexamples.BallSymTSD.eta_le_one
@[deprecated (since := "2026-10-17")] alias abs_mul_deriv_eta_le :=
  Counterexamples.BallSymTSD.abs_mul_deriv_eta_le
@[deprecated (since := "2026-10-17")] alias contDiff_chi :=
  Counterexamples.BallSymTSD.contDiff_chi
@[deprecated (since := "2026-10-17")] alias differentiable_chi :=
  Counterexamples.BallSymTSD.differentiable_chi
@[deprecated (since := "2026-10-17")] alias isTest_chi :=
  Counterexamples.BallSymTSD.isTest_chi
@[deprecated (since := "2026-10-17")] alias pd_chi :=
  Counterexamples.BallSymTSD.pd_chi
@[deprecated (since := "2026-10-17")] alias eventually_eta_eq_one :=
  Counterexamples.BallSymTSD.eventually_eta_eq_one
@[deprecated (since := "2026-10-17")] alias tendsto_chi :=
  Counterexamples.BallSymTSD.tendsto_chi
@[deprecated (since := "2026-10-17")] alias tendsto_toLp_of_bound :=
  Counterexamples.BallSymTSD.tendsto_toLp_of_bound
@[deprecated (since := "2026-10-17")] alias linF :=
  Counterexamples.BallSymTSD.linF
@[deprecated (since := "2026-10-17")] alias contDiff_linF :=
  Counterexamples.BallSymTSD.contDiff_linF
@[deprecated (since := "2026-10-17")] alias differentiable_linF :=
  Counterexamples.BallSymTSD.differentiable_linF
@[deprecated (since := "2026-10-17")] alias pd_linF :=
  Counterexamples.BallSymTSD.pd_linF
@[deprecated (since := "2026-10-17")] alias ecoef :=
  Counterexamples.BallSymTSD.ecoef
@[deprecated (since := "2026-10-17")] alias eF :=
  Counterexamples.BallSymTSD.eF
@[deprecated (since := "2026-10-17")] alias eF_symm :=
  Counterexamples.BallSymTSD.eF_symm
@[deprecated (since := "2026-10-17")] alias eF_trace :=
  Counterexamples.BallSymTSD.eF_trace
@[deprecated (since := "2026-10-17")] alias sum_pd_eF :=
  Counterexamples.BallSymTSD.sum_pd_eF
@[deprecated (since := "2026-10-17")] alias Mc :=
  Counterexamples.BallSymTSD.Mc
@[deprecated (since := "2026-10-17")] alias curlM_eF :=
  Counterexamples.BallSymTSD.curlM_eF
@[deprecated (since := "2026-10-17")] alias pd_const_fun :=
  Counterexamples.BallSymTSD.pd_const_fun
@[deprecated (since := "2026-10-17")] alias pd_pd_chi :=
  Counterexamples.BallSymTSD.pd_pd_chi
@[deprecated (since := "2026-10-17")] alias pd_pd_chi_mul_linF :=
  Counterexamples.BallSymTSD.pd_pd_chi_mul_linF
@[deprecated (since := "2026-10-17")] alias divdivF_chi_eF :=
  Counterexamples.BallSymTSD.divdivF_chi_eF
@[deprecated (since := "2026-10-17")] alias isTest_chi_mul :=
  Counterexamples.BallSymTSD.isTest_chi_mul
@[deprecated (since := "2026-10-17")] alias pd_eF_diag :=
  Counterexamples.BallSymTSD.pd_eF_diag
@[deprecated (since := "2026-10-17")] alias abs_eF_le :=
  Counterexamples.BallSymTSD.abs_eF_le
@[deprecated (since := "2026-10-17")] alias contDiff_one_eF :=
  Counterexamples.BallSymTSD.contDiff_one_eF
@[deprecated (since := "2026-10-17")] alias E0 :=
  Counterexamples.BallSymTSD.E0
@[deprecated (since := "2026-10-17")] alias coe_E0 :=
  Counterexamples.BallSymTSD.coe_E0
@[deprecated (since := "2026-10-17")] alias E0_mem_TSDS :=
  Counterexamples.BallSymTSD.E0_mem_TSDS
@[deprecated (since := "2026-10-17")] alias E0_mem_d1 :=
  Counterexamples.BallSymTSD.E0_mem_d1
@[deprecated (since := "2026-10-17")] alias psiN :=
  Counterexamples.BallSymTSD.psiN
@[deprecated (since := "2026-10-17")] alias isTest_psiN :=
  Counterexamples.BallSymTSD.isTest_psiN
@[deprecated (since := "2026-10-17")] alias psiN_symm :=
  Counterexamples.BallSymTSD.psiN_symm
@[deprecated (since := "2026-10-17")] alias divdivTestField_psiN :=
  Counterexamples.BallSymTSD.divdivTestField_psiN
@[deprecated (since := "2026-10-17")] alias tendsto_testFieldS_psiN :=
  Counterexamples.BallSymTSD.tendsto_testFieldS_psiN
@[deprecated (since := "2026-10-17")] alias E0_mem_divdivD :=
  Counterexamples.BallSymTSD.E0_mem_divdivD
@[deprecated (since := "2026-10-17")] alias E0_mem_adjoint_d0 :=
  Counterexamples.BallSymTSD.E0_mem_adjoint_d0
@[deprecated (since := "2026-10-17")] alias x0 :=
  Counterexamples.BallSymTSD.x0
@[deprecated (since := "2026-10-17")] alias x0_mem_domL :=
  Counterexamples.BallSymTSD.x0_mem_domL
@[deprecated (since := "2026-10-17")] alias x0_mem_Kc :=
  Counterexamples.BallSymTSD.x0_mem_Kc
@[deprecated (since := "2026-10-17")] alias pF :=
  Counterexamples.BallSymTSD.pF
@[deprecated (since := "2026-10-17")] alias vF :=
  Counterexamples.BallSymTSD.vF
@[deprecated (since := "2026-10-17")] alias contDiff_pF :=
  Counterexamples.BallSymTSD.contDiff_pF
@[deprecated (since := "2026-10-17")] alias contDiff_vF :=
  Counterexamples.BallSymTSD.contDiff_vF
@[deprecated (since := "2026-10-17")] alias gExp :=
  Counterexamples.BallSymTSD.gExp
@[deprecated (since := "2026-10-17")] alias pd_vF :=
  Counterexamples.BallSymTSD.pd_vF
@[deprecated (since := "2026-10-17")] alias qExp :=
  Counterexamples.BallSymTSD.qExp
@[deprecated (since := "2026-10-17")] alias qExp_eq_symF :=
  Counterexamples.BallSymTSD.qExp_eq_symF
@[deprecated (since := "2026-10-17")] alias qExp_symm :=
  Counterexamples.BallSymTSD.qExp_symm
@[deprecated (since := "2026-10-17")] alias gExp_eq_pd :=
  Counterexamples.BallSymTSD.gExp_eq_pd
@[deprecated (since := "2026-10-17")] alias contDiff_gExp :=
  Counterexamples.BallSymTSD.contDiff_gExp
@[deprecated (since := "2026-10-17")] alias contDiff_qExp :=
  Counterexamples.BallSymTSD.contDiff_qExp
@[deprecated (since := "2026-10-17")] alias contDiff_one_qExp :=
  Counterexamples.BallSymTSD.contDiff_one_qExp
@[deprecated (since := "2026-10-17")] alias pd2_q01 :=
  Counterexamples.BallSymTSD.pd2_q01
@[deprecated (since := "2026-10-17")] alias pd2_q10 :=
  Counterexamples.BallSymTSD.pd2_q10
@[deprecated (since := "2026-10-17")] alias pd1_q02 :=
  Counterexamples.BallSymTSD.pd1_q02
@[deprecated (since := "2026-10-17")] alias pd1_q20 :=
  Counterexamples.BallSymTSD.pd1_q20
@[deprecated (since := "2026-10-17")] alias pd0_q12 :=
  Counterexamples.BallSymTSD.pd0_q12
@[deprecated (since := "2026-10-17")] alias pd0_q21 :=
  Counterexamples.BallSymTSD.pd0_q21
@[deprecated (since := "2026-10-17")] alias sum_Mc_curlM_qExp :=
  Counterexamples.BallSymTSD.sum_Mc_curlM_qExp
@[deprecated (since := "2026-10-17")] alias exists_bound_ball3 :=
  Counterexamples.BallSymTSD.exists_bound_ball3
@[deprecated (since := "2026-10-17")] alias tendsto_pd_chi_vF :=
  Counterexamples.BallSymTSD.tendsto_pd_chi_vF
@[deprecated (since := "2026-10-17")] alias sum_integral_mul_qExp_eq_zero :=
  Counterexamples.BallSymTSD.sum_integral_mul_qExp_eq_zero
@[deprecated (since := "2026-10-17")] alias integral_Ioi_radial :=
  Counterexamples.BallSymTSD.integral_Ioi_radial
@[deprecated (since := "2026-10-17")] alias integral_ball3_radial :=
  Counterexamples.BallSymTSD.integral_ball3_radial
@[deprecated (since := "2026-10-17")] alias volume_real_ball3 :=
  Counterexamples.BallSymTSD.volume_real_ball3
@[deprecated (since := "2026-10-17")] alias integral_rho_ball3 :=
  Counterexamples.BallSymTSD.integral_rho_ball3
@[deprecated (since := "2026-10-17")] alias integrable_ball3 :=
  Counterexamples.BallSymTSD.integrable_ball3
@[deprecated (since := "2026-10-17")] alias not_propagate_of_inner :=
  Counterexamples.BallSymTSD.not_propagate_of_inner
@[deprecated (since := "2026-10-17")] alias inner_negL_ini :=
  Counterexamples.BallSymTSD.inner_negL_ini
@[deprecated (since := "2026-10-17")] alias Qs :=
  Counterexamples.BallSymTSD.Qs
@[deprecated (since := "2026-10-17")] alias Qs_mem_d1 :=
  Counterexamples.BallSymTSD.Qs_mem_d1
@[deprecated (since := "2026-10-17")] alias Nvec :=
  Counterexamples.BallSymTSD.Nvec
@[deprecated (since := "2026-10-17")] alias inner_Qs_eq_zero :=
  Counterexamples.BallSymTSD.inner_Qs_eq_zero
@[deprecated (since := "2026-10-17")] alias inner_Nvec_eq_zero :=
  Counterexamples.BallSymTSD.inner_Nvec_eq_zero
@[deprecated (since := "2026-10-17")] alias inner_negL_x0 :=
  Counterexamples.BallSymTSD.inner_negL_x0
@[deprecated (since := "2026-10-17")] alias inner_curlE0_curlQ :=
  Counterexamples.BallSymTSD.inner_curlE0_curlQ
@[deprecated (since := "2026-10-17")] alias inner_negL_x0_lt :=
  Counterexamples.BallSymTSD.inner_negL_x0_lt
@[deprecated (since := "2026-10-17")] alias inner_negL_x0_ne_zero :=
  Counterexamples.BallSymTSD.inner_negL_x0_ne_zero
@[deprecated (since := "2026-10-17")] alias negL_x0_not_mem_closure :=
  Counterexamples.BallSymTSD.negL_x0_not_mem_closure
@[deprecated (since := "2026-10-17")] alias symComplexD_ball_not_propagate :=
  Counterexamples.BallSymTSD.tsd_not_propagates
@[deprecated (since := "2026-10-17")] alias symComplexD_ball_not_propagate_unconditional :=
  Counterexamples.BallSymTSD.not_propagates
@[deprecated (since := "2026-10-17")] alias symComplexD_ball_not_propagate_TSDSk :=
  Counterexamples.BallSymTSD.tsdSk_not_propagates
@[deprecated (since := "2026-10-17")] alias x0_not_mem_Kmax :=
  Counterexamples.BallSymTSD.x0_not_mem_Kmax
@[deprecated (since := "2026-10-17")] alias curlE0_not_mem_closure :=
  Counterexamples.BallSymTSD.curlE0_not_mem_closure

end Feec.BoundedSymDual
