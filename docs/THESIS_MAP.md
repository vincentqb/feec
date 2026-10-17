# Thesis map

Traceability from V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of
General Relativity* (PhD thesis, Minnesota, 2015) [QuennevilleBelair2015] to the Lean
declarations of `Feec`. Lean names carry no thesis numbers after the refactor
(`docs/REFACTOR_PLAN.md` §1); this file is the only place where they meet.

**Generated** by `scripts/ThesisMap.sh` from declaration names and docstrings; do not edit by
hand, rerun after renaming. A declaration is listed under a thesis id when

- **named**: its name encodes the id (`prop_4_17`, `prop417_density_gap`, `ch6_corrected`,
  `Sol61`; old names only, banned after the refactor);
- **tagged**: its docstring has a `Thesis: Prop 4.17 (corrected)` tag (the convention for new
  declarations);
- **cited**: its docstring cites the id inside `[QuennevilleBelair2015, ...]`.

Every backticked name in a list item below is checked by `scripts/MapCheck.sh`
(`#check @name` must elaborate).

Counts at generation: 40 numbered results (Thm/Prop/Cor/Lemma/Remark/Def), 64 equations/sections/chapters, 1279 distinct declarations (169 with a thesis-numbered name).

## Results

### Prop 2.1

- named: `Feec.Curvature.prop_2_1`, `Feec.Curvature.prop_2_1_jet`
- tagged: `Feec.CurvatureTensor.Bianchi1`, `Feec.CurvatureTensor.PairSkew`, `Feec.CurvatureTensor.lower_riemComp_isAlgCurv`, `Feec.CurvatureTensor.lower_riemComp_skew`, `Feec.CurvatureTensor.riemComp_bianchi`, `Feec.CurvatureTensor.riemComp_skew`, `Feec.CurvatureTensor.riemField_isAlgCurv`
- cited: `Feec.Bianchi1`, `Feec.Bivector.bianchi_iff`, `Feec.Curvature.lower_riemComp_skew`, `Feec.Curvature.prop_2_1`, `Feec.Curvature.prop_2_1_jet`, `Feec.Curvature.riemComp_bianchi`, `Feec.Curvature.riemComp_skew`, `Feec.DoubleForm.bianchi_iff_altPart`, `Feec.PairSkew`
- modules: Feec.Ch2.Curvature, Feec.Ch3.Bivector, Feec.Foundation.Tensor, Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Bivector, Feec.Geometry.Connection

### Thm 2.3

- tagged: `Feec.LinearizedGravity.HbarJet`, `Feec.LinearizedGravity.Hfun`, `Feec.LinearizedGravity.Hfun_eq_bar`, `Feec.LinearizedGravity.Hjet`, `Feec.LinearizedGravity.Hjet_eq_bar`, `Feec.LinearizedGravity.Hjet_eq_div`, `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.Hsym_eq`
- cited: `Feec.Linearized.Hfun_eq_bar`, `Feec.Linearized.Hjet_eq_bar`, `Feec.Linearized.Hjet_eq_div`, `Feec.Linearized.Hjet_eq_einstein`, `Feec.Linearized.Hsym_eq`
- modules: Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Prop 2.4

- named: `Feec.Linearized.thesis_prop_2_4b_false`
- tagged: `Feec.Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ`, `Feec.LinearizedGravity.Hfun_lorentz`, `Feec.LinearizedGravity.Hjet_lorentz`, `Feec.LinearizedGravity.Hsym_lorentz`, `Feec.LinearizedGravity.LorentzJet`, `Feec.LinearizedGravity.exists_lorentz_gauge`, `Feec.LinearizedGravity.not_Hjet_eq_neg_boxJ`
- cited: `Feec.Linearized.Hfun_lorentz`, `Feec.Linearized.Hjet_lorentz`, `Feec.Linearized.Hsym_lorentz`, `Feec.Linearized.exists_lorentz_gauge`, `Feec.Linearized.thesis_prop_2_4b_false`
- modules: Feec.Ch2.Linearized, Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Prop 2.5

- tagged: `Feec.LinearizedGravity.plane_wave`
- cited: `Feec.Linearized.plane_wave`
- modules: Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.PlaneWave

### Prop 2.6

- named: `Feec.Repair.C2.prop_2_6`, `Feec.Repair.C2.prop_2_6_metric`
- tagged: `Feec.LinearizedGravity.exists_ttGauge`, `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`, `Feec.LinearizedGravity.tt_gauge_fun`
- cited: `Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed`, `Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed_contra`, `Feec.Linearized.thesis_gauge_fails`, `Feec.Linearized.thesis_gauge_fails_contra`, `Feec.Linearized.tt_gauge`, `Feec.Linearized.tt_gauge_fun`, `Feec.LinearizedGravity.not_isTT_gaugeAmp_printed`, `Feec.LinearizedGravity.not_isTT_gaugeAmp_printed_contra`, `Feec.LinearizedGravity.tt_gauge`, `Feec.Repair.C2.prop_2_6`, `Feec.Repair.C2.prop_2_6_metric`
- modules: Feec.Ch2.Linearized, Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.PlaneWave, Feec.Repair.C2

### Prop 3.1

- named: `Feec.Bivector.prop_3_1`
- cited: `Feec.Bivector.prop_3_1`, `Feec.DoubleForm.electric_magnetic_props`
- modules: Feec.Ch3.Bivector, Feec.Geometry.WeylDecomposition

### Prop 3.2

- named: `Feec.Bivector.prop_3_2`
- cited: `Feec.Bivector.ldual_T`, `Feec.Bivector.ldual_rdual_T`, `Feec.Bivector.prop_3_2`, `Feec.Bivector.rdual_T`, `Feec.DoubleForm.blocks_eq_and_duals`, `Feec.DoubleForm.ldual_ofBlocks`, `Feec.DoubleForm.ldual_rdual_ofBlocks`, `Feec.DoubleForm.rdual_ofBlocks`
- modules: Feec.Ch3.Bivector, Feec.Geometry.Hodge2

### Prop 3.3

- cited: `Feec.Bivector.alt_iff`, `Feec.Bivector.bianchi_T_iff`, `Feec.Bivector.bianchi_iff`, `Feec.Bivector.interchange_iff`, `Feec.Bivector.tracefree_iff`, `Feec.Bivector.weyl_iff`, `Feec.DoubleForm.altPart_ofBlocks_iff`, `Feec.DoubleForm.bianchi_iff_altPart`, `Feec.DoubleForm.bianchi_ofBlocks_iff`, `Feec.DoubleForm.interchange_iff`, `Feec.DoubleForm.tracefree_iff`, `Feec.DoubleForm.weyl_iff`, `Feec.EB.dWeyl`, `Feec.EinsteinBianchi.dWeyl`
- modules: Feec.Ch3.Bivector, Feec.Ch3.EB, Feec.Geometry.Bivector, Feec.Geometry.WeylDecomposition, Feec.Physics.EinsteinBianchi.System

### Prop 3.4

- cited: `Feec.EB.EBJet`, `Feec.EB.EBJetSym_surjective`, `Feec.EB.linBianchi_field_iff`, `Feec.EB.linBianchi_iff`, `Feec.EB.linBianchi_iff_sym`, `Feec.EinsteinBianchi.EBJet`, `Feec.EinsteinBianchi.EBJetSym_surjective`, `Feec.EinsteinBianchi.linBianchi_field_iff`, `Feec.EinsteinBianchi.linBianchi_iff`, `Feec.EinsteinBianchi.linBianchi_iff_sym`
- modules: Feec.Ch3.EB, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.System

### Lemma 3.5

- tagged: `Feec.Fourier.GradCurl.curl_mem_tsd`, `Feec.Fourier.GradCurl.isFibreReducing`, `Feec.Fourier.SymCurl.curl_mem_trSub`, `Feec.Fourier.SymCurl.isFibreReducing`, `Feec.MatrixSymbol.axial_curl`, `Feec.MatrixSymbol.curl`, `Feec.MatrixSymbol.curlSymbol_mem_ttSub`, `Feec.MatrixSymbol.curl_isTSD`, `Feec.MatrixSymbol.div`, `Feec.MatrixSymbol.div_curl`, `Feec.MatrixSymbol.div_sub_transpose`, `Feec.MatrixSymbol.trace_curl`, `Feec.MatrixSymbol.trace_curl_eq_vskw`, `Feec.MatrixSymbol.trace_curl_of_transpose_eq`, `Feec.MatrixSymbol.transpose_curl_eq`, `Feec.MatrixSymbol.two_smul_vskw_curl`, `Feec.MatrixSymbol.vskw`, `Feec.Models.BoundedDomain.curl_symm_of_mem_tsd`
- cited: `Feec.BoundedDomain.curl_symm_of_mem_TSD`, `Feec.Constraints.curl_TSD`, `Feec.Constraints.curl_TSD_div`, `Feec.Constraints.div_curl`, `Feec.Constraints.trace_curl`, `Feec.Constraints.trace_curl_of_symm`, `Feec.Constraints.two_vskw_curl`, `Feec.EB.curl_TSD`, `Feec.EB.curl_TSD_field`, `Feec.EB.div_curl`, `Feec.EB.div_curl_field`, `Feec.EB.trace_curl`, `Feec.EB.two_vskw_curl`, `Feec.EinsteinBianchi.curl_TSD_field`, `Feec.EinsteinBianchi.div_curl_field`, `Feec.Torus.curlR_apply_eps3`, `Feec.Torus.curlR_mem_tsd`, `Feec.TorusSym.curlST_mem_L2TSDT`, `Feec.TorusSym.curlSym_mem_trSub`, `Feec.curl`, `Feec.div`, `Feec.vskw`
- modules: Feec.Algebra.MatrixSymbol, Feec.Ch3.EB, Feec.Ch4.BoundedDomain, Feec.Ch4.Constraints, Feec.Ch4.Torus, Feec.Ch4.TorusSym, Feec.Foundation.Tensor, Feec.Fourier.GradCurlSymbol, Feec.Fourier.SymCurlSymbol, Feec.Models.BoundedDomain.GradCurl, Feec.Physics.EinsteinBianchi.Fields

### Prop 3.6

- named: `Feec.EB.prop_3_6`, `Feec.EB.prop_3_6_hyps_nonvacuous`
- tagged: `Feec.Domain.FiniteSpeed.IsWeakSolution.ae_eq_zero_of_ball`, `Feec.EinsteinBianchi.tsd_propagates_classical`
- cited: `Feec.EB.curl_TSD`, `Feec.EB.curl_TSD_field`, `Feec.EB.div_propagation`, `Feec.EB.energy_flux`, `Feec.EB.prop_3_6`, `Feec.EB.violation_evolution`, `Feec.EinsteinBianchi.curl_TSD_field`, `Feec.EinsteinBianchi.div_propagation`, `Feec.EinsteinBianchi.energy_flux`, `Feec.EinsteinBianchi.tsd_propagates`, `Feec.EinsteinBianchi.violation_evolution`
- modules: Feec.Ch3.EB, Feec.Domain.FiniteSpeed, Feec.Physics.EinsteinBianchi.Constraints, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.Propagation, Feec.Physics.EinsteinBianchi.System

### Thm 4.1

- tagged: `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`, `Feec.HilbertComplex.hodge`, `Feec.HilbertComplex.hodge_domain`, `Feec.HilbertComplex.hodge_domainComplex`, `Feec.HilbertComplex.hodge_domain_of_closedRangeAt`, `Feec.HilbertComplex.hodge_of_closedRangeAt`
- cited: `Feec.BGG.Hilb.hodge_Vt1`, `Feec.Constraints.ker_adj0_orth_le`, `Feec.DomainComplex.hodge_V`, `Feec.DomainComplex.hodge_V_orthogonal_W`, `Feec.DomainComplex.hodge_V_unique`, `Feec.DomainComplex.hodge_V_zero`, `Feec.HilbertComplex2.closed_and_fredholm_of_compact`, `Feec.HilbertComplex2.hodge_W`, `Feec.HilbertComplex2.hodge_W0`, `Feec.HilbertComplex2.hodge_W0_of_closedRange`, `Feec.HilbertComplex2.hodge_W2`, `Feec.HilbertComplex2.hodge_W2_of_closedRange`, `Feec.HilbertComplex2.hodge_W_of_closedRange`, `Feec.TorusSym.symComplex_hodge`
- modules: Feec.Ch4.Adjoint, Feec.Ch4.Constraints, Feec.Ch4.Hodge, Feec.Ch4.HodgeW, Feec.Ch4.TorusSym, Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.Compactness, Feec.HilbertComplex.DomainComplex, Feec.HilbertComplex.Hodge

### Thm 4.2

- tagged: `Feec.Counterexamples.not_poincare_curl`, `Feec.Counterexamples.not_poincare_grad`, `Feec.HilbertComplex.closedRangeAt_iff_poincare`, `Feec.HilbertComplex.closedRangeAt_iff_poincare_adjoint`, `Feec.HilbertComplex.closedRangeAt_iff_poincare_of_rel`, `LinearPMap.exists_norm_le_of_isClosed_range`, `LinearPMap.isClosed_range_iff_exists_norm_le`
- cited: `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`, `Feec.DomainComplex.isClosedAt_iff_poincare_W`, `Feec.DomainComplex.isClosedAt_of_poincare`, `Feec.DomainComplex.poincare`, `Feec.DomainComplex.poincare_W`, `Feec.DomainComplex.poincare_iff`, `Feec.UHilbertComplex.isClosed_range_iff_poincare`, `Feec.isClosed_range_iff_poincare`, `Feec.poincare_graphNorm_of_isClosed_range`, `Feec.poincare_of_isClosed_range`
- modules: Feec.Ch4.Adjoint, Feec.Ch4.Hodge, Feec.Counterexamples.NonClosedRangeEuclidean, Feec.ForMathlib.LinearPMap.ClosedRange, Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.Hodge

### Thm 4.3

- named: `Feec.HilbertComplex2.thm_4_3_hodgeWave`, `Feec.HilbertComplex2.thm_4_3_hodgeWave_thm43`, `Feec.IsSkewAdjoint.wellPosedClassical_thm43`, `Feec.IsSkewAdjoint.wellPosedClassical_thm43Full`, `Feec.IsSkewAdjoint.wellPosedExistence_thm43`, `Feec.IsSkewAdjoint.wellPosedExistence_thm43Full`, `Feec.Torus.thm_4_3_torus`, `Feec.UnitaryGroupGenerator.wellPosedClassical_thm43`, `Feec.UnitaryGroupGenerator.wellPosedClassical_thm43Full`, `Feec.thm_4_3_full`, `Feec.thm_4_3_of_isSkewAdjoint`, `Feec.thm_4_3_unconditional`
- tagged: `Feec.C0Semigroup.isClassicalSolution_mild`, `Feec.Evolution.IsStrongSolution.norm_sub_le`, `Feec.Evolution.IsStrongSolution.unique`, `Feec.Examples.bounded_standing_hypotheses`, `Feec.Examples.rotGen_standing_hypotheses`, `Feec.Maxwell.gauss_existsUnique`, `LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup`
- cited: `Feec.Box.mirror_prop_4_17_exists`, `Feec.Box.mirror_prop_4_19_exists`, `Feec.Constraints.isStrongSolution_orbit`, `Feec.Constraints.prop_4_17_group_all_unconditional`, `Feec.Constraints.prop_4_17_group_unconditional`, `Feec.Constraints.strong_unique`, `Feec.Constraints.waveGroup_mem_Kc`, `Feec.Constraints.waveGroup_mem_Kc_of_nonneg`, `Feec.Evolution.ForcingClass.admissible`, `Feec.Evolution.IsClassicalSolution`, `Feec.ForcingClass.admissible`, `Feec.ForcingThm43Full`, `Feec.HilbertComplex2.thm_4_3_hodgeWave`, `Feec.HilbertComplex2.thm_4_3_hodgeWave_thm43`, `Feec.HilbertComplex2.thm_4_6`, `Feec.HilbertComplex2.thm_4_6_classical`, `Feec.HilbertComplex2.waveOp_isSkewAdjoint`, `Feec.HilbertComplex2.wellPosedClassical_neg_waveOp`, `Feec.IsClassicalSolution`, `Feec.IsSkewAdjoint.existsUnique_classicalSolution`, `Feec.IsSkewAdjoint.neg`, `Feec.IsSkewAdjoint.wellPosedClassical`, `Feec.IsSkewAdjoint.wellPosedClassical_W11`, `Feec.IsSkewAdjoint.wellPosedClassical_forcing`, `Feec.IsSkewAdjoint.wellPosedClassical_of_le`, `Feec.IsSkewAdjoint.wellPosedClassical_thm43`, `Feec.IsSkewAdjoint.wellPosedClassical_thm43Full`, `Feec.IsSkewAdjoint.wellPosedExistence`, `Feec.IsSkewAdjoint.wellPosedExistence_thm43`, `Feec.IsSkewAdjoint.wellPosedExistence_thm43Full`, `Feec.IsSkewAdjoint.wellPosedHom`, `Feec.IsStrongSolution`, `Feec.IsStrongSolution.norm_sub_le`, `Feec.IsStrongSolution.unique`, `Feec.Torus.periodicGroup`, `Feec.Torus.periodic_waveOp_isSkewAdjoint`, `Feec.Torus.prop_4_17_torus_classical`, `Feec.Torus.prop_4_17_torus_exists`, `Feec.Torus.prop_4_17_torus_group`, `Feec.Torus.thm_4_3_torus`, `Feec.Torus.wellPosedHom_periodic`, `Feec.TorusSym.prop_4_19_torus_exists`, `Feec.TorusSym.prop_4_19_torus_exists_real`, `Feec.TorusSym.prop_4_19_torus_group`, `Feec.TorusSym.prop_4_19_torus_real_space`, `Feec.TorusSym.symGroup`, `Feec.UnitaryGroupGenerator`, `Feec.UnitaryGroupGenerator.duhamel_L1`, `Feec.UnitaryGroupGenerator.duhamel_W11`, `Feec.UnitaryGroupGenerator.isSkewSymm`, `Feec.UnitaryGroupGenerator.wellPosedClassical`, `Feec.UnitaryGroupGenerator.wellPosedClassical_W11`, `Feec.UnitaryGroupGenerator.wellPosedClassical_admissible`, `Feec.UnitaryGroupGenerator.wellPosedClassical_forcing`, `Feec.UnitaryGroupGenerator.wellPosedClassical_thm43`, `Feec.UnitaryGroupGenerator.wellPosedClassical_thm43Full`, `Feec.UnitaryGroupGenerator.wellPosedHom`, `Feec.WellPosedClassical`, `Feec.WellPosedExistence`, `Feec.WellPosedExistence.exists_mem_ker`, `Feec.Whole.prop_4_17_whole_exists`, `Feec.Whole.prop_4_17_whole_group`, `Feec.WholeSym.prop_4_19_whole_exists`, `Feec.bddOp_standing_hypotheses`, `Feec.constraint_ker_exists`, `Feec.dense_bddOp_domain`, `Feec.exists_classical_solution_bddOp`, `Feec.isSkewAdjoint_bddOp`, `Feec.stoneGroup`, `Feec.strongSolution_unique`, `Feec.thm_4_3_full`, `Feec.thm_4_3_of_isSkewAdjoint`, `Feec.thm_4_3_unconditional`, `Feec.wellPosedClassical_bddOp`, `Feec.wellPosedExistence_bddOp`, `Feec.wellPosedHom_bddOp`
- modules: Feec.Ch4.BoxMirror, Feec.Ch4.Constraints, Feec.Ch4.Duhamel, Feec.Ch4.Existence, Feec.Ch4.HodgeWave, Feec.Ch4.Restriction, Feec.Ch4.Stone, Feec.Ch4.StoneApplications, Feec.Ch4.StoneDuhamel, Feec.Ch4.StoneForcing, Feec.Ch4.Torus, Feec.Ch4.TorusGroup, Feec.Ch4.TorusSym, Feec.Ch4.Unconditional, Feec.Ch4.Whole, Feec.Ch4.WholeSym, Feec.Evolution.Duhamel, Feec.Evolution.Forcing, Feec.Evolution.Solution, Feec.Examples.NonVacuity, Feec.Foundation.Evolution, Feec.Physics.Maxwell.Constraints, Feec.Semigroup.Stone

### Thm 4.4

- named: `Feec.thm_4_4`
- tagged: `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `Feec.IsSkewAdjoint.restrictTo`, `Feec.IsStrongSolution.mem_of_isReducing`, `LinearPMap.IsSkewAdjoint.restrict`
- cited: `Feec.Constraints.Kc_propagate`, `Feec.Constraints.projK_mem_domL`, `Feec.Constraints.projection_hyp_necessary`, `Feec.Constraints.propagate`, `Feec.Constraints.waveOp_mem_K`, `Feec.Constraints.waveOp_mem_Kc`, `Feec.IsSkewAdjoint.existsUnique_classicalSolution_mem`, `Feec.IsSkewAdjoint.existsUnique_classicalSolution_restrictTo`, `Feec.IsSkewAdjoint.restrictTo`, `Feec.IsStrongSolution.mem_of_invariant`, `Feec.commute_proj`, `Feec.cor_4_5_ambient_unconditional`, `Feec.cor_4_5_classical_unconditional`, `Feec.cor_4_5_hypotheses_bddOp_ker`, `Feec.cor_4_5_of_isSkewAdjoint`, `Feec.cor_4_5_unconditional`, `Feec.dense_inter_of_proj_mem`, `Feec.dense_restrictTo_domain`, `Feec.map_orthogonal_mem`, `Feec.restrictTo`, `Feec.skewAdjoint_restrict`, `Feec.thm_4_4`
- modules: Feec.Ch4.Constraints, Feec.Ch4.Restriction, Feec.Ch4.StoneApplications, Feec.Evolution.Constrained, Feec.ForMathlib.LinearPMap.Reducing, Feec.Foundation.Evolution, Feec.Foundation.Operators

### Cor 4.5

- named: `Feec.cor_4_5`, `Feec.cor_4_5_ambient`, `Feec.cor_4_5_ambient_unconditional`, `Feec.cor_4_5_classical`, `Feec.cor_4_5_classical_unconditional`, `Feec.cor_4_5_hypotheses_bddOp_ker`, `Feec.cor_4_5_of_isSkewAdjoint`, `Feec.cor_4_5_unconditional`
- tagged: `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `Feec.Examples.ker_standing_hypotheses`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.IsSkewAdjoint.exists_classicalSolution_restrictTo`, `Feec.IsSkewAdjoint.exists_strongSolution_restrictTo`, `Feec.IsStrongSolution.mem_of_isReducing`, `Feec.WellPosedExistence.exists_mem_of_isReducing`
- cited: `Feec.Constraints.Kc_propagate`, `Feec.Constraints.propagate`, `Feec.EB.div_propagation`, `Feec.EB.energy_flux`, `Feec.EB.prop_3_6`, `Feec.EB.violation_evolution`, `Feec.EinsteinBianchi.div_propagation`, `Feec.EinsteinBianchi.energy_flux`, `Feec.EinsteinBianchi.tsd_propagates`, `Feec.EinsteinBianchi.violation_evolution`, `Feec.IsSkewAdjoint.existsUnique_classicalSolution_mem`, `Feec.IsSkewAdjoint.existsUnique_classicalSolution_restrictTo`, `Feec.IsSkewAdjoint.exists_classicalSolution_restrictTo`, `Feec.IsSkewAdjoint.exists_strongSolution_restrictTo`, `Feec.IsStrongSolution.mem_of_invariant`, `Feec.WellPosedExistence.exists_mem_ker`, `Feec.WellPosedExistence.exists_mem_of_isReducing`, `Feec.bddOp_standing_hypotheses`, `Feec.constraint_ker`, `Feec.constraint_ker_exists`, `Feec.constraint_ker_exists_unconditional`, `Feec.constraint_propagation`, `Feec.cor_4_5`, `Feec.cor_4_5_ambient`, `Feec.cor_4_5_ambient_unconditional`, `Feec.cor_4_5_classical`, `Feec.cor_4_5_classical_unconditional`, `Feec.cor_4_5_hypotheses_bddOp_ker`, `Feec.cor_4_5_of_isSkewAdjoint`, `Feec.cor_4_5_unconditional`
- modules: Feec.Ch3.EB, Feec.Ch4.Constraints, Feec.Ch4.Existence, Feec.Ch4.Restriction, Feec.Ch4.StoneApplications, Feec.Ch4.Unconditional, Feec.Evolution.Constrained, Feec.Examples.NonVacuity, Feec.Foundation.Evolution, Feec.HilbertComplex.Reducing, Feec.Physics.EinsteinBianchi.Propagation, Feec.Physics.EinsteinBianchi.System

### Thm 4.5

- cited: `Feec.CrankNicolson.full_iter_reduces`
- modules: Feec.Ch7.CrankNicolson

### Thm 4.6

- named: `Feec.HilbertComplex2.thm_4_6`, `Feec.HilbertComplex2.thm_4_6_classical`, `Feec.HilbertComplex2.thm_4_6_classical_of_unitaryGroupGenerator`, `Feec.HilbertComplex2.thm_4_6_of_unitaryGroupGenerator`, `Feec.HilbertComplex2.thm_4_6_strong_unconditional`, `Feec.HilbertComplex2.thm_4_6_unconditional`
- tagged: `Feec.Evolution.IsStrongSolution.unique`, `Feec.Examples.idComplex_nonvacuous`, `Feec.HilbertComplex.HodgeWave.existsUnique`, `Feec.HilbertComplex.HodgeWave.existsUnique_hom`, `Feec.HilbertComplex.isSkewAdjoint_wave`, `Feec.HodgeWave.existsUnique`, `Feec.HodgeWave.existsUnique_hom`, `Feec.HodgeWave.norm_eq`, `Feec.ShortHilbertComplex.isSkewAdjoint_wave`
- cited: `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.Constraints.prop_4_16_exists`, `Feec.Constraints.prop_4_18`, `Feec.Constraints.strong_unique`, `Feec.Constraints.waveOp_isSkewSymm`, `Feec.Constraints.wellPosedHom_boundedComplex`, `Feec.HilbertComplex2.adjoint_waveOp_domain_le`, `Feec.HilbertComplex2.dense_domL`, `Feec.HilbertComplex2.dense_midDomain`, `Feec.HilbertComplex2.eqOn_waveGroup_of_isWeakSolution`, `Feec.HilbertComplex2.existsUnique_classicalSolution_neg_waveOp`, `Feec.HilbertComplex2.isStrongSolution_waveGroup`, `Feec.HilbertComplex2.neg_waveOp_isSkewAdjoint`, `Feec.HilbertComplex2.norm_eq_of_isStrongSolution`, `Feec.HilbertComplex2.orthogonal_ker_adjoint_d0_le`, `Feec.HilbertComplex2.orthogonal_ker_d1_le`, `Feec.HilbertComplex2.thm_4_6`, `Feec.HilbertComplex2.thm_4_6_classical`, `Feec.HilbertComplex2.thm_4_6_classical_of_unitaryGroupGenerator`, `Feec.HilbertComplex2.thm_4_6_of_unitaryGroupGenerator`, `Feec.HilbertComplex2.thm_4_6_strong_unconditional`, `Feec.HilbertComplex2.thm_4_6_unconditional`, `Feec.HilbertComplex2.waveOp_isSkewAdjoint`, `Feec.HilbertComplex2.waveOp_isSkewSymm`, `Feec.HodgeWaveExample.nonvacuous`, `Feec.IsStrongSolution.unique`, `Feec.Torus.periodicGroup`, `Feec.Torus.periodic_waveOp_isSkewAdjoint`, `Feec.Torus.prop_4_17_torus_classical`, `Feec.Torus.wellPosedHom_periodic`, `Feec.UnitaryGroupGenerator.wellPosedHom`, `Feec.WellPosedHom`, `Feec.adjoint_adjoint`, `Feec.wellPosedHom_bddOp`
- modules: Feec.Ch4.Adjoint, Feec.Ch4.Constraints, Feec.Ch4.ErrorEstimateDL, Feec.Ch4.Existence, Feec.Ch4.HodgeWave, Feec.Ch4.StoneApplications, Feec.Ch4.TorusGroup, Feec.Ch4.Unconditional, Feec.Evolution.Solution, Feec.Examples.NonVacuity, Feec.Foundation.Evolution, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.Dirac, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.Short

### Thm 4.7

- named: `Feec.HilbertComplex2.thm_4_7`, `Feec.HilbertComplex2.thm_4_7_classical`, `Feec.HilbertComplex2.thm_4_7_classical_unconditional`, `Feec.HilbertComplex2.thm_4_7_unconditional`
- tagged: `Feec.Examples.idComplex_nonvacuous`, `Feec.HilbertComplex.HodgeWave.classicalWeak_iff_classical`, `Feec.HilbertComplex.HodgeWave.weak_iff_strong`, `Feec.HodgeWave.IsWeakSolution.isClassicalSolution`, `Feec.HodgeWave.classicalWeak_iff_classical`, `Feec.HodgeWave.isClassicalWeakSolution_of_isClassicalSolution`, `Feec.HodgeWave.isWeakSolution_of_isStrongSolution`, `Feec.HodgeWave.weak_iff_strong`
- cited: `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.HilbertComplex2.eqOn_waveGroup_of_isWeakSolution`, `Feec.HilbertComplex2.existsUnique_classicalWeakSolution`, `Feec.HilbertComplex2.exists_classicalWeakSolution_unconditional`, `Feec.HilbertComplex2.isClassicalSolution_iff_isClassicalWeakSolution`, `Feec.HilbertComplex2.isClassicalSolution_of_isWeakSolution`, `Feec.HilbertComplex2.isClassicalWeakSolution_of_isClassicalSolution`, `Feec.HilbertComplex2.isStrongSolution_iff_isWeakSolution`, `Feec.HilbertComplex2.isWeakSolution_of_isStrongSolution`, `Feec.HilbertComplex2.norm_embed`, `Feec.HilbertComplex2.norm_toV_le`, `Feec.HilbertComplex2.thm_4_7`, `Feec.HilbertComplex2.thm_4_7_classical`, `Feec.HilbertComplex2.thm_4_7_classical_unconditional`, `Feec.HilbertComplex2.thm_4_7_unconditional`, `Feec.HilbertComplex2.weak_identity`, `Feec.HilbertComplex2.weak_identity_neg`, `Feec.HilbertComplex2.weak_imp_classical`, `Feec.HilbertComplex2.weak_imp_strong`, `Feec.HilbertComplex2.weak_imp_strong_unconditional`, `Feec.HodgeWaveExample.nonvacuous`
- modules: Feec.Ch4.ErrorEstimateDL, Feec.Ch4.HodgeWave, Feec.Ch4.StoneApplications, Feec.Ch4.Unconditional, Feec.Examples.NonVacuity, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.HodgeWave

### Thm 4.8

- tagged: `Feec.Variational.existsUnique_of_coercive`, `Feec.Variational.infSup_of_coercive`
- cited: `Feec.Galerkin.lax_milgram`, `Feec.Galerkin.lax_milgram_bound`
- modules: Feec.Ch4.Galerkin, Feec.Variational.BabuskaNecas

### Thm 4.9

- tagged: `Feec.Counterexamples.surjective_not_infSup`, `Feec.Variational.InfSup.surjective`, `Feec.Variational.babuskaNecas_iff`, `Feec.Variational.babuskaNecas_iff_inner`, `Feec.Variational.existsUnique_apply_eq`, `Feec.Variational.existsUnique_inner`, `Feec.Variational.exists_infSup_of_bijective`, `Feec.Variational.infSup_iff_mul_norm_symm_le`
- cited: `Feec.Complex3.ellProj_existsUnique`, `Feec.Complex3.infSup_of_tst_mem`, `Feec.Complex3.norm_ellProjFun_le`, `Feec.Complex3.prop_4_13_infSup`, `Feec.Galerkin.babuska_necas_iff`, `Feec.Galerkin.existsUnique_solution`, `Feec.Galerkin.infSup_const_iff`, `Feec.Galerkin.surjective_not_infSup`
- modules: Feec.Ch4.ErrorEstimate, Feec.Ch4.Galerkin, Feec.Counterexamples.Ell2, Feec.Variational.BabuskaNecas

### Thm 4.10

- named: `Feec.Galerkin.thm_4_10`
- tagged: `Feec.Variational.InfSup.norm_le_of_restrict_eq`, `Feec.Variational.InfSup.norm_sub_le_infDist`, `Feec.Variational.InfSup.norm_sub_le_infDist_sharp`, `Feec.Variational.InfSup.norm_sub_le_of_orthogonal`, `Feec.Variational.InfSup.norm_sub_le_of_orthogonal_sharp`, `Feec.Variational.existsUnique_galerkin`, `Feec.Variational.existsUnique_galerkin_sesq`
- cited: `Feec.Complex3.DensityHyp.ellProj_tendsto`, `Feec.Complex3.ellProj_quasiopt`, `Feec.Complex3.ellProj_quasiopt_infDist`, `Feec.Galerkin.discrete_existsUnique`, `Feec.Galerkin.quasi_opt`, `Feec.Galerkin.thm_4_10`
- modules: Feec.Ch4.ErrorEstimate, Feec.Ch4.Galerkin, Feec.Variational.BabuskaNecas, Feec.Variational.Galerkin

### Thm 4.11

- named: `Feec.Galerkin.thm_4_11`
- tagged: `Feec.BGG.brezzi_wellPosed_real`, `Feec.Variational.IsSaddleSolution`, `Feec.Variational.IsSaddleSolution.norm_fst_le`, `Feec.Variational.IsSaddleSolution.norm_snd_le`, `Feec.Variational.IsSaddleSolution.unique`, `Feec.Variational.brezzi_iff`, `Feec.Variational.existsUnique_discrete_isSaddleSolution`, `Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.exists_lift`
- cited: `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.infSup_a`, `Feec.BGG.Hilb.infSup_b`, `Feec.BGG.Hilb.saddle_wellPosed`, `Feec.BGG.brezzi_wellPosed_real`, `Feec.Galerkin.brezzi`, `Feec.Galerkin.brezzi_stability`, `Feec.Galerkin.brezzi_unique`, `Feec.Galerkin.brezzi_wellPosed`, `Feec.Galerkin.not_infSup_first_of_ker_ne_bot`, `Feec.Galerkin.thm_4_11`
- modules: Feec.Ch4.Galerkin, Feec.HilbertComplex.BGG.WeakSymmetry, Feec.Variational.Fortin, Feec.Variational.SaddlePoint

### Lemma 4.12

- named: `Feec.lemma_4_12`, `Feec.lemma_4_12_integral`, `Feec.lemma_4_12_sharp`
- tagged: `Feec.Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le`, `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`, `le_add_half_integral_of_sq_deriv_le_mul`, `le_add_half_sub_of_sq_deriv_le_mul`, `norm_le_add_integral_of_re_inner_deriv_le`, `norm_le_of_re_inner_deriv_le`
- cited: `Feec.Ch6.energy_estimate_integral`, `Feec.lemma_4_12`, `Feec.lemma_4_12_integral`, `Feec.lemma_4_12_sharp`
- modules: Feec.Ch4.ErrorEstimate, Feec.Ch6.TimeDependent, Feec.Evolution.Energy, Feec.ForMathlib.Analysis.Gronwall

### Prop 4.13

- named: `Feec.Complex3.prop_4_13`, `Feec.Complex3.prop_4_13_V`, `Feec.Complex3.prop_4_13_infSup`, `Feec.Complex3.prop_4_13_lower`, `Feec.Complex3.prop_4_13_test_norm`
- tagged: `Feec.Variational.InfSup.of_testMap`, `Feec.Variational.InfSup.restrict_of_testMap`
- cited: `Feec.Complex3.Sub.infSup`, `Feec.Complex3.Sub.tst_mem`, `Feec.Complex3.infSup_of_tst_mem`, `Feec.Complex3.prop_4_13`, `Feec.Complex3.prop_4_13_infSup`, `Feec.Complex3.tst`
- modules: Feec.Ch4.ErrorEstimate, Feec.Variational.InfSup

### Thm 4.14

- named: `Feec.Complex3.thm_4_14`, `Feec.Complex3.thm_4_14_pointwise`
- tagged: `Feec.Counterexamples.ClassicalRegularity.exists_datum_not_C1`, `Feec.Counterexamples.ClassicalRegularity.not_C1_graphSpace`, `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, `Feec.Variational.GalerkinEvolution.error_bound`, `Feec.Variational.GalerkinEvolution.error_bound_refined`, `Feec.Variational.norm_sub_le_of_projected_error`, `Feec.Variational.norm_sub_le_of_projected_error_decay`
- cited: `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.Complex3.IsWeakSol`, `Feec.Complex3.abs_bigA_le`, `Feec.Complex3.convergence`, `Feec.Complex3.thm_4_14`, `Feec.Complex3.thm_4_14_pointwise`, `Feec.FredholmCE.cxK1_convergence_without_C1`, `Feec.FredholmCE.cxK1_exists_not_isWeakSol`, `Feec.HilbertComplex2.convergence_W`, `Feec.HilbertComplex2.convergence_domL`, `Feec.HilbertComplex2.convergence_domL_classicalWeak_exists`, `Feec.HilbertComplex2.convergence_domL_weakSolution`, `Feec.HilbertComplex2.convergence_unconditional`, `Feec.HilbertComplex2.embW_deriv_zero_of_isWeakSol`, `Feec.HilbertComplex2.error_bound_W`, `Feec.HilbertComplex2.error_bound_W'`, `Feec.HilbertComplex2.exists_isWeakSol_of_waveOp_mem`, `Feec.HilbertComplex2.exists_isWeakSol_unconditional`, `Feec.HilbertComplex2.tendstoUniformlyOn_discreteSol`, `Feec.error_bound_core`, `Feec.norm_le_norm_zero_add_integral`, `Feec.projected_error_bound`
- modules: Feec.Ch4.ErrorEstimate, Feec.Ch4.ErrorEstimateDL, Feec.Ch4.Unconditional, Feec.Counterexamples.ClassicalRegularity, Feec.HilbertComplex.Approximation.SemidiscreteWave, Feec.HilbertComplex.BGG.TimeDependent, Feec.Variational.GalerkinEvolution

### Prop 4.16

- named: `Feec.BoundedSym.symComplexB_prop_4_16`, `Feec.BoundedSym.symComplexD_prop_4_16`, `Feec.Ch6.Bounded.bggComplex_prop_4_16`, `Feec.Constraints.prop_4_16`, `Feec.Constraints.prop_4_16'`, `Feec.Constraints.prop_4_16_classical_unconditional`, `Feec.Constraints.prop_4_16_exists`, `Feec.Constraints.prop_4_16_exists_unconditional`
- tagged: `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.Maxwell.euclidean_gauss_propagates`, `Feec.Maxwell.gauss_existsUnique`, `Feec.Maxwell.gauss_propagates`, `Feec.Maxwell.pec_gauss_propagates`, `Feec.Maxwell.pmc_gauss_propagates`, `Feec.Maxwell.torus_gauss_propagates`, `Feec.Maxwell.waveGroup_mem`, `Feec.ShortHilbertComplex.divFreeSub`, `Feec.ShortHilbertComplex.divFree_propagates`, `Feec.ShortHilbertComplex.divFree_propagates_neg`, `Feec.ShortHilbertComplex.reducingSubcomplex_divFreeSub`
- cited: `Feec.BoundedSym.symComplexB_prop_4_16`, `Feec.Constraints.K`, `Feec.Constraints.existsUnique_classicalSolution_mem_K`, `Feec.Constraints.prop_4_16`, `Feec.Constraints.prop_4_16'`, `Feec.Constraints.prop_4_16_classical_unconditional`, `Feec.Constraints.prop_4_16_exists`, `Feec.Constraints.prop_4_16_exists_unconditional`, `Feec.proj_orth_mem_of_le`
- modules: Feec.Ch4.BoundedSym, Feec.Ch4.Constraints, Feec.Ch4.Restriction, Feec.Ch4.StoneApplications, Feec.HilbertComplex.Reducing, Feec.Physics.Maxwell.Constraints

### Prop 4.17

- named: `Feec.BoundedDomain.prop417_density_gap`, `Feec.BoundedDomain.thesisComplex_prop_4_17_max`, `Feec.Box.mirror_prop_4_17`, `Feec.Box.mirror_prop_4_17_exists`, `Feec.Box.prop_4_17_hyps_res`, `Feec.Box.prop_4_17_res`, `Feec.Box.prop_4_17_res_exists`, `Feec.Ch6.Bounded.bggComplex_prop_4_17_max`, `Feec.Ch6.Whole.prop_4_17_bggWhole`, `Feec.Constraints.le_max_of_prop_4_17_hyps`, `Feec.Constraints.prop_4_17`, `Feec.Constraints.prop_4_17_exists_unconditional`, `Feec.Constraints.prop_4_17_group_all_unconditional`, `Feec.Constraints.prop_4_17_group_unconditional`, `Feec.Constraints.prop_4_17_iff`, `Feec.Constraints.prop_4_17_iff_unconditional`, `Feec.Constraints.prop_4_17_max`, `Feec.Constraints.prop_4_17_max_unconditional`, `Feec.Constraints.prop_4_17_necessary`, `Feec.Constraints.prop_4_17_necessary_unconditional`, `Feec.Repair.C417.mirrorCxCube_prop_4_17_exists`, `Feec.Repair.C417.mirrorCxQ_prop_4_17_exists`, `Feec.Repair.C417.piCube_mirror_prop_4_17_exists`, `Feec.Repair.C417.prop_4_17_compr_exists`, `Feec.Repair.C417.prop_4_17_corrected`, `Feec.Repair.C417.prop_4_17_corrected_cube`, `Feec.Repair.C417.prop_4_17_hyps_compr`, `Feec.Repair.C417.prop_4_17_hyps_scale`, `Feec.Repair.C417.prop_4_17_hyps_scale2`, `Feec.Repair.C417.unitCube_mirror_prop_4_17_exists`, `Feec.Torus.prop_4_17_torus`, `Feec.Torus.prop_4_17_torus_backward`, `Feec.Torus.prop_4_17_torus_classical`, `Feec.Torus.prop_4_17_torus_exists`, `Feec.Torus.prop_4_17_torus_exists_of_Hcurl`, `Feec.Torus.prop_4_17_torus_group`, `Feec.Torus.prop_4_17_torus_group_all`, `Feec.Torus.prop_4_17_torus_group_periodic`, `Feec.Whole.prop_4_17_whole`, `Feec.Whole.prop_4_17_whole_exists`, `Feec.Whole.prop_4_17_whole_group`, `Feec.WholeReal.real_prop_4_17_whole`, `Feec.WholeReal.real_prop_4_17_whole_exists`
- tagged: `Feec.Counterexamples.BoundedDomainTSD.exists_projTSD_not_mem_domain`, `Feec.Counterexamples.BoundedDomainTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedDomainTSD.not_mem_closure_wave_domain_inter`, `Feec.Counterexamples.BoundedDomainTSD.obstruction_ne_bot`, `Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`, `Feec.Counterexamples.CubeStationary.forward_iff_stationary`, `Feec.Counterexamples.CubeStationary.mem_invariantCore_tsd_iff`, `Feec.Counterexamples.CubeStationary.tsd_not_propagates`, `Feec.EinsteinBianchi.boundedDomain_tsd_not_propagates`, `Feec.EinsteinBianchi.cube_tsd_propagates`, `Feec.EinsteinBianchi.euclidean_tsd_propagates`, `Feec.EinsteinBianchi.torus_tsd_propagates`, `Feec.Fourier.FibreReducing.existsUnique_mem`, `Feec.Fourier.FibreReducing.propagates`, `Feec.Fourier.GradCurl.isFibreReducing`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.HilbertComplex.isReducing_iff_waveGroup_invariant`, `Feec.Models.BoundedDomain.closure_eq_tsd₀`, `Feec.Models.BoundedDomain.exists_projTSD_not_mem_domain`, `Feec.Models.BoundedDomain.integral_eq_zero_of_mem_tsd`, `Feec.Models.BoundedDomain.not_isReducing_wave_tsd`, `Feec.Models.BoundedDomain.not_propagates`, `Feec.Models.BoundedDomain.obstruction_ne_bot`, `Feec.Models.BoundedDomain.sum_integral_mul_pd_eq_zero`, `Feec.Models.BoundedDomain.tsd`, `Feec.Models.BoundedDomain.tsd₀`, `Feec.Models.BoundedDomain.tsd₀_le_closure`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Models.Cube.Ident.mem_invariantCore_iff`, `Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.Mirror.existsUnique_memQ`, `Feec.Models.Cube.Mirror.exists_nonstationary`, `Feec.Models.Cube.Mirror.exists_nonstationaryCube`, `Feec.Models.Cube.Mirror.exists_nonstationaryQ`, `Feec.Models.Cube.Mirror.invariantCore_eq`, `Feec.Models.Cube.Mirror.invariantCore_eqCube`, `Feec.Models.Cube.Mirror.invariantCore_eqQ`, `Feec.Models.Cube.Mirror.propagates`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Cube.Mirror.propagatesQ`, `Feec.Models.Cube.Mirror.reducingSubcomplex`, `Feec.Models.Cube.Mirror.reducingSubcomplexCube`, `Feec.Models.Cube.Mirror.reducingSubcomplexQ`, `Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ`, `Feec.Models.Cube.Parity.exists_linearIndependent_invariantCore`, `Feec.Models.Cube.Parity.forward_iff`, `Feec.Models.Cube.Parity.forward_torus_iff`, `Feec.Models.Cube.Parity.forward_tsd_iff`, `Feec.Models.Cube.Parity.invariantCore_ne_bot`, `Feec.Models.Cube.Parity.mem_invariantCore_iff`, `Feec.Models.Cube.Parity.mem_invariantCore_torus_iff`, `Feec.Models.Cube.Parity.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.reducingSubcomplex_tsd_torus`, `Feec.Models.Cube.reducingSubcomplex_tsd_torusBGG`, `Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.real_tsd_propagates`, `Feec.Models.Euclidean.GradCurl.reducingSubcomplex`, `Feec.Models.Euclidean.GradCurl.tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.tsd_propagates`, `Feec.Models.Euclidean.GradCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.GradCurl.waveGroup_mem`, `Feec.Models.Torus.GradCurl.real_tsd_existsUnique`, `Feec.Models.Torus.GradCurl.real_tsd_propagates`, `Feec.Models.Torus.GradCurl.reducingSubcomplex`, `Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.GradCurl.tsd_propagates`, `Feec.Models.Torus.GradCurl.tsd_propagates_neg`, `Feec.Models.Torus.GradCurl.waveGroup_mem`
- cited: `Feec.BoundedDomain.HcurlM_not_projection`, `Feec.BoundedDomain.HcurlM_not_projection_bochner`, `Feec.BoundedDomain.adjoint_mem_TSD0_of_propagate`, `Feec.BoundedDomain.closure_TSD_inter_HcurlM_eq`, `Feec.BoundedDomain.closure_TSD_inter_HcurlM_inter_HdivM_eq`, `Feec.BoundedDomain.closure_TSD_inter_HcurlZero_subset`, `Feec.BoundedDomain.dense_domain_d1_inter_ker_adj0`, `Feec.BoundedDomain.density_dichotomy`, `Feec.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.BoundedDomain.exists_data_not_propagate`, `Feec.BoundedDomain.exists_orbit_not_propagate`, `Feec.BoundedDomain.exists_orbit_not_propagate_unconditional`, `Feec.BoundedDomain.exists_projTSD_not_mem_HcurlZero`, `Feec.BoundedDomain.exists_tsd_not_propagates`, `Feec.BoundedDomain.integral_eq_zero_bochner`, `Feec.BoundedDomain.integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`, `Feec.BoundedDomain.not_dense_TSD_inter_HcurlZero`, `Feec.BoundedDomain.not_dense_domL_inter_Kc`, `Feec.BoundedDomain.not_finiteDimensional_obstr`, `Feec.BoundedDomain.not_finiteDimensional_orth_closure_TSD_inter_HcurlZero`, `Feec.BoundedDomain.not_projection_hyp`, `Feec.BoundedDomain.not_projection_hyp_S2`, `Feec.BoundedDomain.not_projection_hyp_adjoint`, `Feec.BoundedDomain.not_propagate_of_adjoint`, `Feec.BoundedDomain.projTSD_not_mem_HcurlZero`, `Feec.BoundedDomain.projection_unbounded`, `Feec.BoundedDomain.prop417_density_gap`, `Feec.BoundedDomain.starProjection_grad`, `Feec.BoundedDomain.sum_integral_mul_pd_eq_zero`, `Feec.BoundedDomain.thesisComplex_adjoint_mem_TSD0`, `Feec.BoundedDomain.thesisComplex_beta_violation_boundary_layer`, `Feec.BoundedDomain.thesisComplex_dense_literal`, `Feec.BoundedDomain.thesisComplex_not_projection_hyp`, `Feec.BoundedDomain.thesisComplex_not_projection_hyp2`, `Feec.BoundedDomain.thesisComplex_not_propagate`, `Feec.BoundedDomain.thesisComplex_orbit_not_propagate`, `Feec.BoundedDomain.thesisComplex_orbit_not_propagate_unconditional`, `Feec.BoundedDomain.thesisComplex_prop_4_17_max`, `Feec.BoundedDomain.thesisComplex_tsd_not_propagates`, `Feec.BoundedDomain.thesisComplex_violation_boundary_layer`, `Feec.BoundedDomain.thesisComplex_waveGroup_not_invariant`, `Feec.Box.forward_boxTSD_iff`, `Feec.Box.mem_Kmax_boxTSD_iff`, `Feec.Box.mirror_prop_4_17`, `Feec.Box.mirror_prop_4_17_exists`, `Feec.Box.offB_mem_Kmax`, `Feec.Box.staticB_mem_Kmax`, `Feec.Box.thesisBox_mem_Kmax_iff`, `Feec.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Constraints.projKc_mem_domL_of_propagates`, `Feec.Constraints.prop_4_17`, `Feec.Constraints.prop_4_17_exists_unconditional`, `Feec.Constraints.prop_4_17_group_all_unconditional`, `Feec.Constraints.prop_4_17_group_unconditional`, `Feec.Constraints.prop_4_17_iff`, `Feec.Constraints.prop_4_17_iff_unconditional`, `Feec.Constraints.prop_4_17_max`, `Feec.Constraints.prop_4_17_max_unconditional`, `Feec.Constraints.prop_4_17_necessary`, `Feec.Constraints.prop_4_17_necessary_unconditional`, `Feec.Constraints.propagates_iff_projKc_mem_domL`, `Feec.Constraints.waveGroup_mem_Kc`, `Feec.Constraints.waveGroup_mem_Kc_of_nonneg`, `Feec.Models.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.Repair.C417.mirrorCxCube_prop_4_17_exists`, `Feec.Repair.C417.mirrorCxQ_prop_4_17_exists`, `Feec.Torus.projKc_mem_domL`, `Feec.Torus.prop_4_17_torus`, `Feec.Torus.prop_4_17_torus_backward`, `Feec.Torus.prop_4_17_torus_classical`, `Feec.Torus.prop_4_17_torus_exists`, `Feec.Torus.prop_4_17_torus_group`, `Feec.Torus.prop_4_17_torus_group_all`, `Feec.Whole.projKc_mem_domL`, `Feec.Whole.prop_4_17_whole`, `Feec.Whole.prop_4_17_whole_exists`, `Feec.Whole.prop_4_17_whole_group`, `Feec.WholeReal.real_prop_4_17_whole`, `Feec.WholeReal.real_prop_4_17_whole_exists`
- modules: Feec.Ch4.BoundedDensity, Feec.Ch4.BoundedDomain, Feec.Ch4.BoundedDomainExt, Feec.Ch4.BoundedInterior, Feec.Ch4.BoundedSalvage, Feec.Ch4.BoundedSalvageDim, Feec.Ch4.BoundedSalvageMax, Feec.Ch4.Box, Feec.Ch4.BoxIdent, Feec.Ch4.BoxMirror, Feec.Ch4.BoxStatic, Feec.Ch4.BoxThesis, Feec.Ch4.Constraints, Feec.Ch4.StoneApplications, Feec.Ch4.Torus, Feec.Ch4.TorusGroup, Feec.Ch4.Unconditional, Feec.Ch4.Whole, Feec.Ch4.WholeReal, Feec.Ch6.Bounded, Feec.Counterexamples.BoundedDomainTSD, Feec.Counterexamples.CubeStationary, Feec.Fourier.FibreReducing, Feec.Fourier.GradCurlSymbol, Feec.HilbertComplex.Reducing, Feec.HilbertComplex.Transport, Feec.Models.BoundedDomain.Density, Feec.Models.BoundedDomain.GradCurl, Feec.Models.Cube.Ident, Feec.Models.Cube.Mirror, Feec.Models.Cube.MirrorBGG, Feec.Models.Cube.Parity, Feec.Models.Cube.Static, Feec.Models.Euclidean.GradCurl, Feec.Models.Torus.GradCurl, Feec.Physics.EinsteinBianchi.Constraints, Feec.Repair.C417, Feec.Repair.C417Cube, Feec.Repair.C417Pi

### Prop 4.18

- named: `Feec.BoundedSym.symComplexB_prop_4_18`, `Feec.Constraints.prop_4_18`, `Feec.Constraints.prop_4_18_i`, `Feec.Constraints.prop_4_18_ii`, `Feec.Constraints.prop_4_18_unconditional`
- tagged: `Feec.TimeStepping.IsCNStep.mem_of_isReducing`, `Feec.TimeStepping.mem_of_forall_isCNStep`
- cited: `Feec.BoundedSym.symComplexB_prop_4_18`, `Feec.Constraints.existsUnique_reducedSolution`, `Feec.Constraints.prop_4_18`, `Feec.Constraints.prop_4_18_i`, `Feec.Constraints.prop_4_18_ii`, `Feec.Constraints.prop_4_18_unconditional`, `Feec.Constraints.reduced_mem_ker`, `Feec.Constraints.reduced_unique`, `Feec.CrankNicolson.cn_iterates_agree`, `Feec.CrankNicolson.full_iter_reduces`, `Feec.CrankNicolson.red_to_full`, `Feec.CrankNicolson.red_to_full_necessary`, `Feec.proj_orth_mem_of_le`
- modules: Feec.Ch4.BoundedSym, Feec.Ch4.Constraints, Feec.Ch4.Restriction, Feec.Ch4.StoneApplications, Feec.Ch7.CrankNicolson, Feec.TimeStepping.Cayley

### Prop 4.19

- named: `Feec.BoundedSym.symComplexB_prop_4_19_max`, `Feec.BoundedSym.symComplexD_prop_4_19_max`, `Feec.Box.mirror_prop_4_19`, `Feec.Box.mirror_prop_4_19_exists`, `Feec.Repair.C417.mirrorSymCxCube_prop_4_19_exists`, `Feec.Repair.C417.mirrorSymCxQ_prop_4_19_exists`, `Feec.Repair.C417.prop_4_19_corrected`, `Feec.Repair.C417.prop_4_19_corrected_cube`, `Feec.TorusSym.prop_4_19_torus`, `Feec.TorusSym.prop_4_19_torus_exists`, `Feec.TorusSym.prop_4_19_torus_exists_real`, `Feec.TorusSym.prop_4_19_torus_group`, `Feec.TorusSym.prop_4_19_torus_iff`, `Feec.TorusSym.prop_4_19_torus_real_space`, `Feec.TorusSym.prop_4_19_torus_symGroup`, `Feec.WholeSym.prop_4_19_whole`, `Feec.WholeSym.prop_4_19_whole_exists`, `Feec.WholeSym.prop_4_19_whole_group`
- tagged: `Feec.Counterexamples.BoundedSymTSD.exists_projTSD_not_mem_domain`, `Feec.Counterexamples.BoundedSymTSD.not_dense_tsdS_inter`, `Feec.Counterexamples.BoundedSymTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedSymTSD.tsd_not_propagates`, `Feec.Fourier.FibreReducing.existsUnique_mem`, `Feec.Fourier.FibreReducing.propagates`, `Feec.Fourier.SymCurl.isFibreReducing`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.Models.BoundedDomain.hessCurl`, `Feec.Models.BoundedDomain.not_propagates_sym`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memQ`, `Feec.Models.Cube.MirrorSym.exists_nonstationaryCube`, `Feec.Models.Cube.MirrorSym.exists_nonstationaryQ`, `Feec.Models.Cube.MirrorSym.invariantCore_eq`, `Feec.Models.Cube.MirrorSym.invariantCore_eqCube`, `Feec.Models.Cube.MirrorSym.invariantCore_eqQ`, `Feec.Models.Cube.MirrorSym.propagates`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Cube.MirrorSym.propagatesQ`, `Feec.Models.Cube.MirrorSym.reducingSubcomplex`, `Feec.Models.Cube.MirrorSym.reducingSubcomplexCube`, `Feec.Models.Cube.MirrorSym.reducingSubcomplexQ`, `Feec.Models.Cube.reducingSubcomplex_tsd_torusSym`, `Feec.Models.Euclidean.SymCurl.real_tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.real_tsd_propagates`, `Feec.Models.Euclidean.SymCurl.reducingSubcomplex`, `Feec.Models.Euclidean.SymCurl.tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.tsd_propagates`, `Feec.Models.Euclidean.SymCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.SymCurl.waveGroup_mem`, `Feec.Models.Torus.SymCurl.real_tsd_existsUnique`, `Feec.Models.Torus.SymCurl.real_tsd_propagates`, `Feec.Models.Torus.SymCurl.reducingSubcomplex`, `Feec.Models.Torus.SymCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_propagates`, `Feec.Models.Torus.SymCurl.tsd_propagates_neg`, `Feec.Models.Torus.SymCurl.waveGroup_mem`
- cited: `Feec.BoundedDomain.not_propagate_of_adjoint`, `Feec.BoundedSym.adjoint_curlS_mem_TSDS`, `Feec.BoundedSym.curlS_mem_TSDT`, `Feec.BoundedSym.not_dense_TSDS_inter_domain`, `Feec.BoundedSym.not_finiteDimensional_obstrS`, `Feec.BoundedSym.not_projection_hyp_adjoint_curlS`, `Feec.BoundedSym.symComplexB_diagnosis`, `Feec.BoundedSym.symComplexB_mem_TSD0_of_propagate`, `Feec.BoundedSym.symComplexB_not_projection_hyp`, `Feec.BoundedSym.symComplexB_not_projection_hyp2`, `Feec.BoundedSym.symComplexB_not_propagate`, `Feec.BoundedSym.symComplexB_not_propagate_unconditional`, `Feec.BoundedSym.symComplexB_prop_4_19_max`, `Feec.BoundedSym.symComplexD_diagnosis`, `Feec.BoundedSym.symComplexD_not_projection_hyp`, `Feec.Box.mirror_prop_4_19`, `Feec.Box.mirror_prop_4_19_exists`, `Feec.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Constraints.projKc_mem_domL_of_propagates`, `Feec.Constraints.prop_4_17`, `Feec.Constraints.prop_4_17_exists_unconditional`, `Feec.Constraints.prop_4_17_group_all_unconditional`, `Feec.Constraints.prop_4_17_group_unconditional`, `Feec.Constraints.prop_4_17_iff`, `Feec.Constraints.prop_4_17_iff_unconditional`, `Feec.Constraints.prop_4_17_max`, `Feec.Constraints.prop_4_17_necessary`, `Feec.Constraints.prop_4_17_necessary_unconditional`, `Feec.Constraints.propagates_iff_projKc_mem_domL`, `Feec.Constraints.waveGroup_mem_Kc`, `Feec.Constraints.waveGroup_mem_Kc_of_nonneg`, `Feec.Counterexamples.BallSymTSD.not_propagates`, `Feec.Repair.C417.mirrorSymCxCube_prop_4_19_exists`, `Feec.Repair.C417.mirrorSymCxQ_prop_4_19_exists`, `Feec.TorusSym.projKc_mem_domL`, `Feec.TorusSym.prop_4_19_torus`, `Feec.TorusSym.prop_4_19_torus_exists`, `Feec.TorusSym.prop_4_19_torus_exists_real`, `Feec.TorusSym.prop_4_19_torus_group`, `Feec.TorusSym.prop_4_19_torus_real_space`, `Feec.WholeSym.projKc_mem_domL`, `Feec.WholeSym.prop_4_19_whole`, `Feec.WholeSym.prop_4_19_whole_exists`
- modules: Feec.Ch4.BoundedSalvage, Feec.Ch4.BoundedSalvageMax, Feec.Ch4.BoundedSym, Feec.Ch4.BoundedSymDual, Feec.Ch4.BoundedSymExt, Feec.Ch4.BoxMirror, Feec.Ch4.Constraints, Feec.Ch4.StoneApplications, Feec.Ch4.TorusSym, Feec.Ch4.Unconditional, Feec.Ch4.WholeSym, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Fourier.FibreReducing, Feec.Fourier.SymCurlSymbol, Feec.HilbertComplex.Reducing, Feec.Models.BoundedDomain.SymCurl, Feec.Models.Cube.MirrorSym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl, Feec.Repair.C417, Feec.Repair.C419Cube, Feec.Repair.C419Pi

### Prop 5.1

- named: `Feec.Ch5.BGG.BGGHilb.prop_5_1`
- tagged: `Feec.BGG.Hilb.isClosed_closedRange_exact`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Hilb.toHilbertComplex_closedRangeAt_one`, `Feec.BGG.Hilb.toHilbertComplex_closedRangeAt_two`, `Feec.BGG.Hilb.toHilbertComplex_cycles_one`, `Feec.BGG.Hilb.toHilbertComplex_cycles_zero`, `Feec.BGG.Hilb.toShort`, `Feec.BGG.Hilb.toShort_closedRange_exact`, `Feec.BGG.Segment.D1_D0`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.range_D0`, `Feec.BGG.Segment.range_D1`, `Feec.BGG.isClosed_range_prod`
- cited: `Feec.BGG.Hilb.D0op_isClosed`, `Feec.BGG.Hilb.D1op_isClosed`, `Feec.BGG.Hilb.D1op_isClosed_range`, `Feec.BGG.Hilb.Hyps`, `Feec.BGG.Hilb.exact_D0op_D1op`, `Feec.BGG.Hilb.isClosed_closedRange_exact`, `Feec.BGG.Hilb.isClosed_range_T`, `Feec.BGG.Hilb.isClosed_Γ`, `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Hilb.toShort`, `Feec.BGG.Hilb.toShort_closedRange_exact`, `Feec.BGG.Segment.range_D0`, `Feec.BGG.Stability`, `Feec.BGG.isClosed_range_prod`, `Feec.Ch5.BGG.BGGHilb.prop_5_1`, `Feec.Ch5.BGG.isClosed_range_prod`, `Feec.Ch5.BGG.range_D0`
- modules: Feec.Ch5.BGG, Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.ToComplex

### Prop 5.2

- named: `Feec.Ch5.BGG.BGGHilb.prop_5_2`, `Feec.Ch5.BGG.BGGHilb.prop_5_2_wellPosed`
- tagged: `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.infSup_a`, `Feec.BGG.Hilb.nondeg_a`, `Feec.BGG.Hilb.saddle_wellPosed`
- cited: `Feec.BGG.Hilb.Wcheck`, `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.hodge_Vt1`, `Feec.BGG.Hilb.infSup_a`, `Feec.BGG.Hilb.infSup_b`, `Feec.BGG.Hilb.jW_spec`, `Feec.BGG.Hilb.nondeg_a`, `Feec.BGG.Hilb.saddle_wellPosed`, `Feec.BGG.Hilb.tripleNorm_definite`, `Feec.BGG.Hilb.tripleNorm_spec`, `Feec.Ch5.BGG.BGGHilb.prop_5_2`, `Feec.Ch5.BGG.BGGHilb.prop_5_2_wellPosed`
- modules: Feec.Ch5.BGG, Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.BGG.WeakSymmetry

### Prop 5.3

- named: `Feec.Ch5.Discrete.Disc.prop_5_3_a`, `Feec.Ch5.Discrete.Disc.prop_5_3_b`
- tagged: `Feec.BGG.Discrete.poincare_Zh`, `Feec.BGG.Discrete.poincare_Γh`
- cited: `Feec.BGG.Discrete.exact_bot_h`, `Feec.BGG.Discrete.exact_top_h`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.poincare_Zh`, `Feec.BGG.Discrete.poincare_Γh`, `Feec.BGG.Discrete.preimage_bound`, `Feec.BGG.Stability`, `Feec.BGG.mixed_not_unique_of_not_exactTop`, `Feec.Ch5.Discrete.ContHyp`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`
- modules: Feec.Ch5.Discrete, Feec.Counterexamples.DiscreteBGG, Feec.HilbertComplex.BGG.Discrete

### Prop 5.4

- named: `Feec.Ch5.Discrete.Disc.prop_5_4`, `Feec.Ch5.Discrete.prop54_counterexample_noTopExact`, `Feec.Ch5.Discrete.prop54_existsUnique`, `Feec.Ch5.Discrete.prop54_hB_necessary`, `Feec.Ch5.Discrete.prop54_unique`
- tagged: `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.BGG.eq_zero_of_mixed_homogeneous`, `Feec.BGG.existsUnique_isMixedSolution`
- cited: `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.exists_sub_S0h_eq`, `Feec.BGG.Discrete.hodge_h`, `Feec.BGG.eq_zero_of_mixed_homogeneous`, `Feec.BGG.existsUnique_isMixedSolution`, `Feec.BGG.exists_mixed_homogeneous_of_perp`, `Feec.BGG.mixed_not_unique_of_not_exactTop`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`
- modules: Feec.Counterexamples.DiscreteBGG, Feec.HilbertComplex.BGG.Discrete

### Thm 5.5

- named: `Feec.Ch5.Discrete.Disc.thm55_absorb_real`, `Feec.Ch5.Discrete.Disc.thm55_final_real`, `Feec.Ch5.Discrete.Disc.thm_5_5`, `Feec.Ch5.Discrete.thm55_lhs_identity`
- tagged: `Feec.BGG.Discrete.error_estimate`
- cited: `Feec.BGG.Discrete.errorConst`, `Feec.BGG.Discrete.error_estimate`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.hodge_h`, `Feec.BGG.mixed_coercivity_eq`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection`, `Feec.Ch5.Discrete.Disc.C55`
- modules: Feec.Ch5.Discrete, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent

### Prop 5.6

- named: `Feec.Ch5.Discrete.prop_5_6`
- tagged: `Feec.BGG.mixed_error_eq`
- cited: `Feec.BGG.Discrete.error_estimate`, `Feec.BGG.errorEq_a`, `Feec.BGG.mixed_error_eq`
- modules: Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent

### Prop 5.7

- tagged: `Feec.FiniteElement.comp_eq_of_dof`, `Feec.FiniteElement.interp_comp_eq`
- cited: `Feec.BGG.Discrete.Compatible`, `Feec.FiniteElement.comp_eq_of_dof`, `Feec.FiniteElement.comp_eq_of_mem_span`, `Feec.FiniteElement.dof_vanish_of_mem_span`, `Feec.FiniteElement.interp_comp_eq`
- modules: Feec.FiniteElement.Dof, Feec.HilbertComplex.BGG.Discrete

### Prop 6.1

- named: `Feec.Ch6.ContData.prop_6_1_i`, `Feec.Ch6.ContData.prop_6_1_i_closedRange`, `Feec.Ch6.ContData.prop_6_1_ii`
- tagged: `Feec.BGG.WaveData.MultiplierSolution.toSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution`
- cited: `Feec.BGG.WaveData.MultiplierSolution.toSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.BGG.WaveData.mem_Wcheck_of_vanish`, `Feec.Ch6.ContData.Sol62.toSol61`
- modules: Feec.Ch6.TimeDependent, Feec.HilbertComplex.BGG.TimeDependent

### Prop 6.2

- named: `Feec.Ch6.prop_6_2`, `Feec.Ch6.prop_6_2_exists`, `Feec.Ch6.prop_6_2_exists_of_continuousOn`, `Feec.Ch6.prop_6_2_exists_regular`, `Feec.Ch6.prop_6_2_false`, `Feec.Ch6.prop_6_2_necessary`, `Feec.Repair.C67.prop_6_2_dynamic`, `Feec.Repair.C67.prop_6_2_wellposed`
- tagged: `Feec.BGG.Counterexample.not_forall_exists_discreteSolution`, `Feec.BGG.DiscreteSolution.compatible`, `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`
- cited: `Feec.BGG.Counterexample.not_forall_exists_discreteSolution`, `Feec.BGG.DiscreteSolution.compatible`, `Feec.BGG.DiscreteSolution.eq_zero_of_initial_eq_zero`, `Feec.BGG.DiscreteSolution.phi_eq`, `Feec.BGG.DiscreteSolution.phi_zero`, `Feec.BGG.DiscreteSolution.unique`, `Feec.BGG.exists_discreteSolution`, `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.BGG.not_exists_discreteSolution_of_ker`, `Feec.BGG.not_exists_discreteSolution_phi_of_ker`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`
- modules: Feec.Counterexamples.ConstrainedEvolution, Feec.HilbertComplex.BGG.TimeDependent, Feec.Repair.C67, Feec.Repair.C67Prop62

### Prop 6.3

- named: `Feec.Ch6.prop_6_3_a`, `Feec.Ch6.prop_6_3_b`, `Feec.Ch6.prop_6_3_c`, `Feec.Ch6.prop_6_3_c_split`, `Feec.Ch6.prop_6_3_d`, `Feec.Ch6.prop_6_3_e`
- tagged: `Feec.BGG.errorEq_a`, `Feec.BGG.errorEq_e`
- cited: `Feec.BGG.errorEq_a`, `Feec.BGG.errorEq_b`, `Feec.BGG.errorEq_c`, `Feec.BGG.errorEq_c_split`, `Feec.BGG.errorEq_d`, `Feec.BGG.errorEq_e`
- modules: Feec.HilbertComplex.BGG.TimeDependent

## Equations, sections and chapters

### Eq (2.2)

- tagged: `Feec.CurvatureTensor.riemComp`, `Feec.CurvatureTensor.riemField`
- cited: `Feec.Curvature.riemComp`
- modules: Feec.Ch2.Curvature, Feec.Geometry.Connection

### Eq (2.3)

- tagged: `Feec.CurvatureTensor.deviation`, `Feec.CurvatureTensor.deviationForm`, `Feec.CurvatureTensor.deviation_eq_zero_iff`, `Feec.CurvatureTensor.eq_zero_of_deviationForm`, `Feec.CurvatureTensor.eq_zero_of_symm_bd`
- cited: `Feec.Curvature.deviation_eq_zero_iff`, `Feec.Curvature.eq_zero_of_deviation`
- modules: Feec.Ch2.Curvature, Feec.Geometry.AlgebraicCurvature

### Eq (2.5)

- tagged: `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`, `Feec.Metric.eq_trRev_sub`, `Feec.Metric.trRev`, `Feec.Metric.trRev_add_sym`, `Feec.Metric.trRev_trRev`, `Feec.Metric.trace_trRev`
- cited: `Feec.Linearized.trRev_gauge`, `Feec.Linearized.trRev_trRev`, `Feec.Linearized.trRev_trace`, `Feec.Repair.C2.prop_2_6_metric`
- modules: Feec.Algebra.Metric, Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.PlaneWave, Feec.Repair.C2

### Eq (2.6)

- tagged: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.Rjet`, `Feec.LinearizedGravity.Rjet_bianchi1`, `Feec.LinearizedGravity.Rjet_pairSkew`
- cited: `Feec.Linearized.Hjet_eq_einstein`, `Feec.Linearized.Rjet`
- modules: Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.Einstein

### Eq (2.7)

- tagged: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.RicJ`
- cited: `Feec.Linearized.Hjet_eq_einstein`
- modules: Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.Einstein

### Eq (2.8)

- tagged: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.scalJ`
- cited: `Feec.Linearized.Hjet_eq_einstein`
- modules: Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.Einstein

### Eq (2.11)

- tagged: `Feec.LinearizedGravity.Hfun_lorentz_eq_iff`, `Feec.LinearizedGravity.Hjet_lorentz_eq_iff`
- cited: `Feec.Linearized.Hsym_lorentz_eq_iff`, `Feec.Linearized.lorentz_eq_iff`, `Feec.Linearized.lorentz_fun_iff`
- modules: Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Eq (2.12)

- tagged: `Feec.TT.ttSub`
- cited: `Feec.Linearized.IsTT`, `Feec.Linearized.isTT_iff`, `Feec.Linearized.mem_ttSpace_iff`, `Feec.LinearizedGravity.IsTT`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.mem_ttSpace_iff`
- modules: Feec.Algebra.TransverseTraceless, Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.13)

- cited: `Feec.Linearized.finrank_ttSpace`, `Feec.Linearized.finrank_ttSub`, `Feec.Linearized.isTT_iff`, `Feec.Linearized.mem_ttSpace_iff`, `Feec.LinearizedGravity.finrank_ttSpace`, `Feec.LinearizedGravity.finrank_ttSub`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.mem_ttSpace_iff`
- modules: Feec.Ch2.Linearized, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.15)

- tagged: `Feec.Counterexamples.LinearizedGravity.not_accel_printed`, `Feec.LinearizedGravity.not_accel_printed`, `Feec.LinearizedGravity.tt_accel_fun`
- cited: `Feec.Linearized.Rjet_tt`, `Feec.Linearized.Rjet_ttWave`, `Feec.Linearized.Rjet_tt_support`, `Feec.Linearized.thesis_accel_fails`, `Feec.Linearized.tt_accel`, `Feec.Linearized.tt_accel_fun`, `Feec.LinearizedGravity.Rjet_tt`, `Feec.LinearizedGravity.Rjet_ttWave`, `Feec.LinearizedGravity.Rjet_tt_support`, `Feec.LinearizedGravity.tt_accel`
- modules: Feec.Ch2.Linearized, Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (3.2)

- cited: `Feec.Bivector.weyl_reconstruct`, `Feec.Bivector.weyl_reconstruct_unit`, `Feec.DoubleForm.weyl_reconstruct`, `Feec.DoubleForm.weyl_reconstruct_unit`
- modules: Feec.Ch3.Bivector, Feec.Geometry.WeylDecomposition

### Eq (4.1)

- tagged: `Feec.HilbertComplex.orthogonal_boundaries`, `Feec.HilbertComplex.orthogonal_cycles`
- cited: `Feec.Constraints.ker_adj0_eq`, `Feec.Constraints.ker_adj1_eq`, `Feec.orth_range_eq_ker_adjoint`, `Feec.orthogonal_ker`, `Feec.orthogonal_ker_adjoint`, `Feec.orthogonal_range_adjoint`, `Feec.range_eq_orthogonal_ker_adjoint`
- modules: Feec.Ch4.Adjoint, Feec.Ch4.Constraints, Feec.Foundation.Operators, Feec.HilbertComplex.Hodge

### Eq (4.4)

- cited: `Feec.HilbertComplex2.neg_waveOp_isSkewAdjoint`, `Feec.IsSkewAdjoint.neg`
- modules: Feec.Ch4.HodgeWave

### Eq (4.5)

- tagged: `Feec.HilbertComplex.wave`, `Feec.ShortHilbertComplex.wave`
- cited: `Feec.Constraints.tot_waveOp`, `Feec.HilbertComplex2.dense_domL`, `Feec.HilbertComplex2.domL`, `Feec.HilbertComplex2.neg_waveOp_isSkewAdjoint`, `Feec.HilbertComplex2.waveGroup`, `Feec.HilbertComplex2.waveOp`
- modules: Feec.Ch4.Constraints, Feec.Ch4.HodgeWave, Feec.Ch4.StoneApplications, Feec.Foundation.Complex, Feec.HilbertComplex.Dirac, Feec.HilbertComplex.Short

### Eq (4.7)

- tagged: `Feec.HilbertComplex.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsWeakSolution`
- cited: `Feec.Complex3.a`, `Feec.Complex3.aL`, `Feec.HilbertComplex2.IsClassicalWeakSolution`, `Feec.HilbertComplex2.IsWeakSolution`, `Feec.HilbertComplex2.existsUnique_classicalWeakSolution`, `Feec.HilbertComplex2.exists_classicalWeakSolution_unconditional`, `Feec.HilbertComplex2.toComplex3`, `Feec.HilbertComplex2.weak_identity_neg`
- modules: Feec.Ch4.ErrorEstimate, Feec.Ch4.ErrorEstimateDL, Feec.Ch4.HodgeWave, Feec.Ch4.Unconditional, Feec.Foundation.Complex, Feec.HilbertComplex.HodgeWave

### Eq (4.8)

- tagged: `Feec.HilbertComplex.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsWeakSolution.unique`
- cited: `Feec.Complex3.IsWeakSol`, `Feec.Complex3.a`, `Feec.HilbertComplex2.IsClassicalWeakSolution`, `Feec.HilbertComplex2.IsWeakSolution`, `Feec.HilbertComplex2.a_self`, `Feec.HilbertComplex2.existsUnique_classicalWeakSolution`, `Feec.HilbertComplex2.exists_classicalWeakSolution_unconditional`, `Feec.HilbertComplex2.weak_identity_neg`, `Feec.HilbertComplex2.weak_unique`
- modules: Feec.Ch4.ErrorEstimate, Feec.Ch4.ErrorEstimateDL, Feec.Ch4.HodgeWave, Feec.Ch4.Unconditional, Feec.Foundation.Complex, Feec.HilbertComplex.HodgeWave

### Eq (4.10)

- cited: `Feec.Complex3.IsDiscreteSol`, `Feec.Complex3.opMh`
- modules: Feec.Ch4.ErrorEstimate

### Eq (4.11)

- tagged: `Feec.HodgeWave.ellipticProjection`, `Feec.HodgeWave.shiftedForm_ellipticProjection`
- cited: `Feec.Complex3.ellProj`, `Feec.Complex3.ellProj_existsUnique`
- modules: Feec.Ch4.ErrorEstimate, Feec.HilbertComplex.Approximation.SemidiscreteWave

### Eq (4.12)

- cited: `Feec.Constraints.IsMixedWeak3`
- modules: Feec.Ch4.Constraints

### Eq (4.14)

- cited: `Feec.Constraints.revT`, `Feec.Constraints.waveOp_revT`, `Feec.CrankNicolson.FullStep`, `Feec.CrankNicolson.cn_invertible`
- modules: Feec.Ch4.Constraints, Feec.Ch7.CrankNicolson

### Eq (4.15)

- cited: `Feec.Constraints.IsReducedSolution`, `Feec.CrankNicolson.RedStep`, `Feec.CrankNicolson.red_step_energy`
- modules: Feec.Ch4.Constraints, Feec.Ch7.CrankNicolson

### Eq (4.16)

- cited: `Feec.TorusSym.curlSym_mem_trSub`, `Feec.TorusSym.symComplex`, `Feec.WholeSym.symWComplex`
- modules: Feec.Ch4.TorusSym, Feec.Ch4.WholeSym

### Eq (4.17)

- cited: `Feec.TorusSym.adjoint_curlS`, `Feec.TorusSym.adjoint_hessS`
- modules: Feec.Ch4.TorusSym

### Eq (4.18)

- cited: `Feec.TorusSym.symComplex_closedRange`, `Feec.TorusSym.symGroup`
- modules: Feec.Ch4.TorusSym

### Eq (5.1)

- tagged: `Feec.BGG.Hilb.toHilbertComplex`
- cited: `Feec.BGG.Hilb.D0op`, `Feec.BGG.Hilb.D1op`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Segment.D0`, `Feec.BGG.Segment.D1`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.Γ`
- modules: Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.ToComplex

### Eq (5.2)

- cited: `Feec.BGG.Hilb.IsReduced`, `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`
- modules: Feec.HilbertComplex.BGG.WeakSymmetry

### Eq (5.3)

- cited: `Feec.BGG.Hilb.IsSaddleW1`, `Feec.BGG.Hilb.aForm`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`
- modules: Feec.HilbertComplex.BGG.WeakSymmetry

### Eq (5.4)

- cited: `Feec.BGG.Discrete.Compatible`, `Feec.BGG.surjective_of_comp_eq`, `Feec.Ch5.Discrete.Disc.Hyp54`
- modules: Feec.Ch5.Discrete, Feec.HilbertComplex.BGG.Discrete

### Eq (5.5)

- cited: `Feec.BGG.Discrete.exact_mid_h`, `Feec.BGG.exists_of_exact_rows`
- modules: Feec.HilbertComplex.BGG.Discrete

### Eq (5.6)

- cited: `Feec.BGG.IsMixedSolution`, `Feec.Ch5.Discrete.Sys56`
- modules: Feec.Ch5.Discrete, Feec.HilbertComplex.BGG.Discrete

### Eq (5.8)

- cited: `Feec.FiniteElement.dof_vanish_of_mem_span`
- modules: Feec.FiniteElement.Dof

### Eq (6.1)

- cited: `Feec.BGG.WaveData.Solution`, `Feec.Ch6.ContData.Sol61`
- modules: Feec.Ch6.TimeDependent, Feec.HilbertComplex.BGG.TimeDependent

### Eq (6.2)

- cited: `Feec.BGG.WaveData.MultiplierSolution`, `Feec.Ch6.ContData.Sol62`
- modules: Feec.Ch6.TimeDependent, Feec.HilbertComplex.BGG.TimeDependent

### Eq (6.3)

- cited: `Feec.BGG.DiscreteSolution`, `Feec.Ch6.Sol63`
- modules: Feec.Ch6.TimeDependent, Feec.HilbertComplex.BGG.TimeDependent

### Eq (6.4)

- cited: `Feec.BGG.exists_discreteSolution_norm_sub_le`
- modules: Feec.HilbertComplex.BGG.TimeDependent

### Sec §2.2

- tagged: `Feec.LinearizedGravity.η4`, `Feec.Metric.minkowski`, `Feec.Metric.minkowski4`, `Feec.Metric.minkowskiMatrix`
- cited: `Feec.η`
- modules: Feec.Algebra.Metric, Feec.Foundation.Tensor, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §2.3

- tagged: `Feec.CurvatureTensor.Interchange`, `Feec.CurvatureTensor.algCurvEquiv`, `Feec.CurvatureTensor.bianchi_iff`, `Feec.CurvatureTensor.deviation_eq_zero_iff`, `Feec.CurvatureTensor.einstein`, `Feec.CurvatureTensor.einstein_isSymm`, `Feec.CurvatureTensor.eq_zero_of_deviationForm`, `Feec.CurvatureTensor.finrank_algCurv_four`, `Feec.CurvatureTensor.interchange_of_bianchi`, `Feec.CurvatureTensor.ricci`, `Feec.CurvatureTensor.ricci_isSymm`, `Feec.CurvatureTensor.ricci_isSymm_of_inv`, `Feec.CurvatureTensor.ricci_riemField_isSymm`
- cited: `Feec.Curvature.algCurvEquiv`, `Feec.Curvature.bianchi_iff`, `Feec.Curvature.deviation_eq_zero_iff`, `Feec.Curvature.einstein`, `Feec.Curvature.einstein_symm`, `Feec.Curvature.eq_zero_of_deviation`, `Feec.Curvature.eq_zero_of_symm_bd`, `Feec.Curvature.finrank_algCurv_four`, `Feec.Curvature.interchange_of_bianchi`, `Feec.Curvature.ricci_field_symm`, `Feec.Curvature.ricci_symm`, `Feec.Curvature.ricci_symm_of_inv`, `Feec.Curvature.riemComp`, `Feec.Interchange`, `Feec.T4`
- modules: Feec.Ch2.Curvature, Feec.Foundation.Tensor, Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Connection

### Sec §2.4

- tagged: `Feec.Counterexamples.Curvature.exists_einstein_eq_zero_ne_zero_two`, `Feec.CurvatureTensor.einstein_eq_zero_iff`, `Feec.CurvatureTensor.exists_einstein_eq_zero_ne_zero_two`, `Feec.LinearizedGravity.einstein_const_bounds`
- cited: `Feec.Curvature.einstein_zero_iff`, `Feec.Curvature.einstein_zero_iff_fails_two`, `Feec.Linearized.einstein_const_bounds`
- modules: Feec.Ch2.Curvature, Feec.Ch2.Linearized, Feec.Counterexamples.Curvature, Feec.Geometry.AlgebraicCurvature, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §2.7

- tagged: `Feec.LinearizedGravity.Hfun_bianchi`, `Feec.LinearizedGravity.Hfun_gauge`, `Feec.LinearizedGravity.Hjet_bianchi`, `Feec.LinearizedGravity.Hjet_gauge`, `Feec.LinearizedGravity.Hsym_div`, `Feec.LinearizedGravity.Hsym_gauge`, `Feec.LinearizedGravity.jet2_isSymJet2`, `Feec.Metric.trRev`, `Feec.Metric.trace`
- cited: `Feec.Linearized.Hfun_bianchi`, `Feec.Linearized.Hfun_gauge`, `Feec.Linearized.Hjet_bianchi`, `Feec.Linearized.Hjet_gauge`, `Feec.Linearized.jet2_isSymJet2`, `Feec.Linearized.trRev_gauge`, `Feec.Linearized.trRev_trRev`, `Feec.Linearized.trRev_trace`, `Feec.η`
- modules: Feec.Algebra.Metric, Feec.Ch2.Linearized, Feec.Foundation.Tensor, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Sec §2.8

- tagged: `Feec.Counterexamples.LinearizedGravity.not_accel_printed`, `Feec.LinearizedGravity.not_accel_printed`, `Feec.TT.ttProj`, `Feec.TT.ttProj_mem`
- cited: `Feec.Linearized.IsTT`, `Feec.Linearized.isTT_iff`, `Feec.Linearized.thesis_accel_fails`, `Feec.Linearized.tt_accel`, `Feec.LinearizedGravity.IsTT`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.tt_accel`
- modules: Feec.Algebra.TransverseTraceless, Feec.Ch2.Linearized, Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §3.1

- tagged: `Feec.leviCivita`, `Feec.leviCivita3`, `Feec.leviCivita4`
- cited: `Feec.Bivector.hodge2_hodge2`, `Feec.DoubleForm.hodge2_hodge2`, `Feec.eps3`, `Feec.eps4`
- modules: Feec.Algebra.LeviCivita, Feec.Ch3.Bivector, Feec.Foundation.Tensor, Feec.Geometry.Hodge2

### Sec §3.2

- cited: `Feec.Bivector.IsWeylLike`, `Feec.Bivector.finrank_weylSpace`, `Feec.Bivector.ldual_eq_rdual`, `Feec.Bivector.ldual_eq_rdual_swap`, `Feec.Bivector.rdual_rdual`, `Feec.DoubleForm.IsWeyl`, `Feec.DoubleForm.finrank_weylSpace`, `Feec.DoubleForm.ldual_eq_rdual`, `Feec.DoubleForm.ldual_eq_rdual_swap`, `Feec.DoubleForm.rdual_rdual`, `Feec.T4`
- modules: Feec.Ch3.Bivector, Feec.Foundation.Tensor, Feec.Geometry.Hodge2, Feec.Geometry.WeylDecomposition

### Sec §3.4

- tagged: `Feec.TT.ttProj`, `Feec.TT.ttProj_mem`, `Feec.TT.ttSub`
- cited: `Feec.BoundedDomain.curl_symm_of_mem_TSD`, `Feec.Constraints.curl_TSD`, `Feec.Constraints.curl_TSD_div`, `Feec.Constraints.div_curl`, `Feec.Constraints.trace_curl`, `Feec.Constraints.trace_curl_of_symm`, `Feec.Constraints.two_vskw_curl`, `Feec.EB.EBJet`, `Feec.EB.EBJetSym_surjective`, `Feec.EB.linBianchi_iff_sym`, `Feec.EinsteinBianchi.EBJet`, `Feec.EinsteinBianchi.EBJetSym_surjective`, `Feec.EinsteinBianchi.linBianchi_iff_sym`, `Feec.Torus.curlR_mem_tsd`, `Feec.TorusSym.curlST_mem_L2TSDT`, `Feec.TorusSym.curlSym_mem_trSub`
- modules: Feec.Algebra.TransverseTraceless, Feec.Ch3.EB, Feec.Ch4.BoundedDomain, Feec.Ch4.Constraints, Feec.Ch4.Torus, Feec.Ch4.TorusSym, Feec.Physics.EinsteinBianchi.System

### Sec §3.5

- cited: `Feec.CrankNicolson.E0`, `Feec.CrankNicolson.planeWave`, `Feec.CrankNicolson.planeWave_solves`, `Feec.EB.planeWave_EB`, `Feec.EB.planeWave_weyl`, `Feec.EinsteinBianchi.planeWave_EB`, `Feec.EinsteinBianchi.planeWave_weyl`
- modules: Feec.Ch3.EB, Feec.Ch7.CrankNicolson, Feec.Physics.EinsteinBianchi.Fields

### Sec §4.1

- cited: `Feec.Constraints.isClosed_ker`, `Feec.Constraints.ker_adj0_eq`, `Feec.Constraints.ker_adj1_eq`, `Feec.DomainComplex.norm_sq_eq`, `Feec.IsSkewAdjoint`, `Feec.IsSkewAdjoint.isSkewSymm`, `Feec.IsSkewAdjoint.isSkewSymmetric`, `Feec.IsSkewSymm`, `Feec.adjoint_adjoint`, `Feec.closure_graph`, `Feec.dense_adjoint_domain`, `Feec.graph_eq_orthogonal`, `Feec.graph_orthogonal`, `Feec.isSelfAdjoint_iff`, `Feec.isSelfAdjoint_iff_le_adjoint`, `Feec.isSkewAdjoint_bddOp`, `Feec.isSkewAdjoint_iff`, `Feec.isSkewAdjoint_iff_neg_le_adjoint`, `Feec.isSkewSymm_iff_neg_le_adjoint`, `Feec.isSymm_iff_le_adjoint`, `Feec.orth_range_eq_ker_adjoint`
- modules: Feec.Ch4.Adjoint, Feec.Ch4.Constraints, Feec.Ch4.Existence, Feec.Ch4.Hodge, Feec.Foundation.Operators

### Sec §4.2

- tagged: `Feec.Counterexamples.deRham_not_closedRange`, `Feec.Counterexamples.euclidean_not_closedRange`, `Feec.Counterexamples.fredholm_not_closedRange`, `Feec.Counterexamples.hasCompactProperty_infiniteDimensional`, `Feec.Counterexamples.not_forall_closedRangeAt_of_finiteDimensional_harmonic`, `Feec.Counterexamples.periodic_not_closedRange`, `Feec.HilbertComplex`, `Feec.HilbertComplex.ClosedRangeAt`, `Feec.HilbertComplex.HasCompactProperty`, `Feec.HilbertComplex.HasCompactProperty.isCompactOperator_resolvent_wave`, `Feec.HilbertComplex.HasCompactPropertyAt`, `Feec.HilbertComplex.HasCompactPropertyAt.closedRangeAt`, `Feec.HilbertComplex.HasCompactPropertyAt.closedRangeAt_of_rel`, `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`, `Feec.HilbertComplex.HasCompactPropertyAt.finiteDimensional_harmonic`, `Feec.HilbertComplex.HasCompactPropertyAt.isClosed_range`, `Feec.HilbertComplex.boundaries`, `Feec.HilbertComplex.boundaries_sup_harmonic`, `Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`, `Feec.HilbertComplex.closure_boundaries_sup_harmonic`, `Feec.HilbertComplex.cohomology`, `Feec.HilbertComplex.cohomologyEquivHarmonic`, `Feec.HilbertComplex.cycles`, `Feec.HilbertComplex.domainComplex`, `Feec.HilbertComplex.domainComplex_closedRangeAt_iff`, `Feec.HilbertComplex.domainSpace`, `Feec.HilbertComplex.dual`, `Feec.HilbertComplex.dual_closedRangeAt_iff`, `Feec.HilbertComplex.exact_iff_harmonic_eq_bot`, `Feec.HilbertComplex.harmonic`, `Feec.HilbertComplex.harmonicToCohomology_surjective_iff`, `Feec.HilbertComplex.harmonic_eq`, `Feec.HilbertComplex.map_domainIncl_harmonic`
- cited: `Feec.Constraints.range_d0_le_ker_d1`, `Feec.DomainComplex`, `Feec.DomainComplex.B`, `Feec.DomainComplex.B_sup_H`, `Feec.DomainComplex.H`, `Feec.DomainComplex.IsClosedAt`, `Feec.DomainComplex.Z`, `Feec.DomainComplex.closed_and_fredholm_of_isCompactOperator`, `Feec.DomainComplex.exact_iff_H_eq_bot`, `Feec.DomainComplex.finiteDimensional_H_of_isCompactOperator`, `Feec.DomainComplex.harmonicEquivCohomology`, `Feec.DomainComplex.inner_of_mem_Z`, `Feec.DomainComplex.isClosedAt_iff_isClosed_image`, `Feec.DomainComplex.isClosedAt_of_finiteDimensional_cohomology`, `Feec.DomainComplex.isClosedAt_of_isCompactOperator`, `Feec.DomainComplex.mem_H_iff`, `Feec.DomainComplex.norm_sq_eq`, `Feec.FredholmCE.hasCompactEmbedding_infiniteDimensional`, `Feec.HilbertComplex2`, `Feec.HilbertComplex2.ClosedRange`, `Feec.HilbertComplex2.HasCompactEmbedding`, `Feec.HilbertComplex2.HasCompactEmbedding0`, `Feec.HilbertComplex2.HasCompactEmbedding2`, `Feec.HilbertComplex2.closedRange_dual_iff`, `Feec.HilbertComplex2.closedRange_iff_isClosedAt`, `Feec.HilbertComplex2.closedRange_of_compact`, `Feec.HilbertComplex2.closed_and_fredholm_V`, `Feec.HilbertComplex2.closed_and_fredholm_of_compact`, `Feec.HilbertComplex2.dual`, `Feec.HilbertComplex2.dual_dual`, `Feec.HilbertComplex2.finiteDimensional_harmonic_of_compact`, `Feec.HilbertComplex2.finiteDimensional_ker_adjoint_d1_of_compact2`, `Feec.HilbertComplex2.finiteDimensional_ker_d0_of_compact0`, `Feec.HilbertComplex2.harmonic`, `Feec.HilbertComplex2.harmonic_eq_ker_inf_orthogonal_range`, `Feec.HilbertComplex2.hasCompactEmbedding_of_finiteDimensional`, `Feec.HilbertComplex2.isClosed_range_d0_of_compact`, `Feec.HilbertComplex2.isClosed_range_d0_of_compact0`, `Feec.HilbertComplex2.isClosed_range_d0_of_finiteDimensional_cohomology`, `Feec.HilbertComplex2.isClosed_range_d1_of_compact`, `Feec.HilbertComplex2.isClosed_range_d1_of_compact2`, `Feec.HilbertComplex2.ofBounded`, `Feec.HilbertComplex2.range_adjoint_d0_eq`, `Feec.HilbertComplex2.range_adjoint_d1_eq`, `Feec.HilbertComplex2.toHilbertComplex`, `Feec.HilbertComplex2.toU`, `Feec.UHilbertComplex`, `Feec.UHilbertComplex.closed_and_fredholm_of_compact`, `Feec.UHilbertComplex.cohomologyEquiv`, `Feec.UHilbertComplex.isClosed_range_of_finiteDimensional_cohomology`, `Feec.UHilbertComplex.isCompactOperator_H`, `Feec.UHilbertComplex.isCompactOperator_orthogonal_Z`, `Feec.UHilbertComplex.isCompactOperator_orthogonal_Z_zero`, `Feec.UHilbertComplex.map_H_eq_harmonic`, `Feec.UHilbertComplex.toHilbertComplex`, `Feec.UHilbertComplex.toHilbertComplex_isClosedAt_iff`, `Feec.exists_bounded_inverse`, `Feec.fredholm_not_closed`, `Feec.fredholm_not_closed_V`, `Feec.fredholm_not_closed_W`, `Feec.fredholm_not_closed_fin`, `Feec.isClosed_ker`, `Feec.isClosed_range_adjoint_iff`, `Feec.range_adjoint_eq_orthogonal_ker`, `Feec.range_eq_orthogonal_ker_adjoint`
- modules: Feec.Ch4.Adjoint, Feec.Ch4.Constraints, Feec.Ch4.Hodge, Feec.Ch4.HodgeW, Feec.Counterexamples.Fredholm, Feec.Counterexamples.NonClosedRangeEuclidean, Feec.Foundation.Complex, Feec.Foundation.Operators, Feec.HilbertComplex.Basic, Feec.HilbertComplex.Compactness, Feec.HilbertComplex.DomainComplex, Feec.HilbertComplex.Dual, Feec.HilbertComplex.Hodge

### Sec §4.3

- tagged: `Feec.Counterexamples.exists_dense_not_isClosed_ker`, `Feec.Counterexamples.not_forall_isClosed_ker`, `Feec.WellPosedExistence.exists_mem_ker`
- cited: `Feec.CrankNicolson.full_iter_reduces`, `Feec.WellPosedExistence.exists_mem_ker`, `Feec.bddOp_standing_hypotheses`, `Feec.constraint_ker`, `Feec.constraint_ker_exists`, `Feec.constraint_ker_exists_unconditional`, `Feec.exists_not_isClosed_ker`, `Feec.isClosed_ker`, `Feec.isClosed_ker_of_isClosed`, `Feec.rotGen_standing_hypotheses`
- modules: Feec.Ch4.Adjoint, Feec.Ch4.Constraints, Feec.Ch4.Existence, Feec.Ch4.HodgeWave, Feec.Ch4.Restriction, Feec.Ch4.Unconditional, Feec.Ch7.CrankNicolson, Feec.Counterexamples.Ell2, Feec.Foundation.Operators

### Sec §4.4

- tagged: `Feec.HodgeWave.IsClassicalWeakSolution`, `Feec.HodgeWave.IsWeakSolution.unique`, `Feec.ShortHilbertComplex`
- cited: `Feec.BGG.WaveData.Solution`, `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.Complex3`, `Feec.Complex3.IsWeakSol`, `Feec.Complex3.VSp`, `Feec.Complex3.a`, `Feec.Complex3.a_self`, `Feec.Complex3.isWeakSol_unique`, `Feec.Complex3.nV2`, `Feec.Constraints.tot_waveOp`, `Feec.CrankNicolson.full_step_energy`, `Feec.CrankNicolson.full_step_unique`, `Feec.Evolution.IsStrongSolution`, `Feec.HilbertComplex2`, `Feec.HilbertComplex2.IsClassicalWeakSolution`, `Feec.HilbertComplex2.IsWeakSolution`, `Feec.HilbertComplex2.Tot`, `Feec.HilbertComplex2.a_self`, `Feec.HilbertComplex2.convergence_domL_classicalWeak_exists`, `Feec.HilbertComplex2.dense_domL`, `Feec.HilbertComplex2.domL`, `Feec.HilbertComplex2.existsUnique_classicalWeakSolution`, `Feec.HilbertComplex2.exists_classicalWeakSolution_unconditional`, `Feec.HilbertComplex2.midDomain`, `Feec.HilbertComplex2.neg_waveOp_isSkewAdjoint`, `Feec.HilbertComplex2.thm_4_3_hodgeWave`, `Feec.HilbertComplex2.thm_4_3_hodgeWave_thm43`, `Feec.HilbertComplex2.toComplex3`, `Feec.HilbertComplex2.toComplex3_a`, `Feec.HilbertComplex2.toU`, `Feec.HilbertComplex2.waveGroup`, `Feec.HilbertComplex2.waveOp`, `Feec.HilbertComplex2.weak_unique`, `Feec.energy_zero`, `Feec.norm_le_norm_zero_of_inner_deriv_nonpos`
- modules: Feec.Ch4.Constraints, Feec.Ch4.ErrorEstimate, Feec.Ch4.ErrorEstimateDL, Feec.Ch4.HodgeW, Feec.Ch4.HodgeWave, Feec.Ch4.StoneApplications, Feec.Ch4.Unconditional, Feec.Ch7.CrankNicolson, Feec.Evolution.Solution, Feec.Foundation.Complex, Feec.Foundation.Evolution, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.Short

### Sec §4.5

- tagged: `Feec.Variational.InfSup`, `Feec.Variational.SeparatingRight`, `Feec.Variational.infSup_iff_forall_exists_norm_le_one`
- cited: `Feec.Complex3.AL_self_eq_zero`, `Feec.Complex3.VSp`, `Feec.Galerkin.DenseRangeCond`, `Feec.Galerkin.InfSupCond`, `Feec.Galerkin.brezzi_wellPosed`, `Feec.Galerkin.infSupCond_iff_attained`
- modules: Feec.Ch4.ErrorEstimate, Feec.Ch4.Galerkin, Feec.Variational.BabuskaNecas, Feec.Variational.InfSup

### Sec §4.6

- tagged: `Feec.HilbertComplex.Subcomplex`, `Feec.HilbertComplex.Subcomplex.toHilbertComplex`
- cited: `Feec.Complex3`, `Feec.Complex3.AL`, `Feec.Complex3.DensityHyp`, `Feec.Complex3.DensityHyp.ellProj_tendsto`, `Feec.Complex3.IsDiscreteSol.norm_toW_sub_le`, `Feec.Complex3.Sub`, `Feec.Complex3.Sub.toV`, `Feec.Complex3.VSp`, `Feec.Complex3.abs_bigA_le`, `Feec.Complex3.bigA`, `Feec.Complex3.bigAL`, `Feec.Complex3.convergence`, `Feec.Complex3.discrete_solution_exists`, `Feec.Complex3.discrete_solution_unique`, `Feec.Complex3.discrete_stability`, `Feec.Complex3.ellProj_quasiopt`, `Feec.Complex3.isWeakSol_unique`, `Feec.Complex3.nV2`, `Feec.Complex3.norm_ellProjFun_le`, `Feec.Complex3.vInner`, `Feec.DomainComplex.CochainProjection`, `Feec.DomainComplex.Subcomplex`, `Feec.FredholmCE.cxK1Sub_densityHyp`, `Feec.HilbertComplex2.convergence_W`, `Feec.HilbertComplex2.convergence_domL`, `Feec.HilbertComplex2.convergence_domL_classicalWeak_exists`, `Feec.HilbertComplex2.convergence_domL_weakSolution`, `Feec.HilbertComplex2.convergence_unconditional`, `Feec.HilbertComplex2.exists_isWeakSol_of_waveOp_mem`, `Feec.HilbertComplex2.exists_isWeakSol_unconditional`, `Feec.HilbertComplex2.tendstoUniformlyOn_discreteSol`
- modules: Feec.Ch4.ErrorEstimate, Feec.Ch4.ErrorEstimateDL, Feec.Ch4.Unconditional, Feec.Foundation.Complex, Feec.HilbertComplex.Approximation.Subcomplex

### Sec §4.7

- tagged: `Feec.Koszul.eq_koszul_add_extDeriv`, `Feec.Koszul.eq_zero_of_eq_koszul_of_eq_extDeriv`, `Feec.Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero`, `Feec.Koszul.exists_koszul_eq_of_koszul_eq_zero`, `Feec.Koszul.extDeriv`, `Feec.Koszul.extDeriv_extDeriv`, `Feec.Koszul.extDeriv_koszul_add_koszul_extDeriv`, `Feec.Koszul.extDeriv_koszul_add_koszul_extDeriv_of_isHomogeneous`, `Feec.Koszul.extDeriv_mem_homForm`, `Feec.Koszul.extDeriv_mem_polyForm`, `Feec.Koszul.extDeriv_mem_polyFormMinus`, `Feec.Koszul.extDeriv_mem_polyForm_of_mem_polyFormMinus`, `Feec.Koszul.homForm`, `Feec.Koszul.homForm_le_sup`, `Feec.Koszul.koszul`, `Feec.Koszul.koszul_koszul`, `Feec.Koszul.koszul_mem_homForm`, `Feec.Koszul.koszul_mem_polyForm`, `Feec.Koszul.polyForm`, `Feec.Koszul.polyFormMinus`, `Feec.Koszul.polyFormMinus_le_polyForm`
- cited: `Feec.Constraints.PminusLambda1`, `Feec.Constraints.koszul_decomp`, `Feec.Constraints.koszul_direct`, `Feec.Constraints.koszul_homotopy_core`
- modules: Feec.Algebra.Koszul, Feec.Algebra.PolynomialForm, Feec.Ch4.Constraints

### Sec §4.8

- cited: `Feec.Constraints.IsMixedWeak`, `Feec.Constraints.IsSecondOrderWeak`, `Feec.Constraints.mixed_imp_secondOrder`, `Feec.Constraints.secondOrder_imp_mixed`, `Feec.Constraints.secondOrder_not_mixed`
- modules: Feec.Ch4.Constraints, Feec.Ch4.HodgeWave

### Sec §4.9

- cited: `Feec.Constraints.IsMixedWeak3`, `Feec.Constraints.K`, `Feec.Constraints.mixed3_eliminate`, `Feec.Constraints.mixed3_eliminate_of_reg`, `Feec.Constraints.prop_4_16`
- modules: Feec.Ch4.Constraints

### Sec §4.10

- tagged: `Feec.Counterexamples.PolynomialForms.extDeriv_not_mem_polyFormMinus`, `Feec.Counterexamples.PolynomialForms.grad_sq_not_whitney`, `Feec.Counterexamples.PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus`, `Feec.Koszul.Proxy3.koszul_empty`, `Feec.Koszul.Proxy3.vec1_extDeriv`, `Feec.Koszul.Proxy3.vec1_koszul`, `Feec.Koszul.Proxy3.vec2_extDeriv`, `Feec.Koszul.Proxy3.vec2_koszul`, `Feec.Koszul.Proxy3.vol_extDeriv`, `Feec.Koszul.extDeriv_mem_polyFormMinus`, `Feec.Koszul.polyFormMinus`, `Feec.Models.Cube.Mirror.complex`, `Feec.Models.Cube.Parity.complex`
- cited: `Feec.BoundedDomain.HcurlM_not_projection`, `Feec.BoundedDomain.HcurlM_not_projection_bochner`, `Feec.BoundedDomain.adjoint_mem_TSD0_of_propagate`, `Feec.BoundedDomain.closure_TSD_inter_HcurlZero_subset`, `Feec.BoundedDomain.dense_HcurlM_inter_HdivZero`, `Feec.BoundedDomain.dense_domain_d1_inter_ker_adj0`, `Feec.BoundedDomain.density_dichotomy`, `Feec.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.BoundedDomain.exists_data_not_propagate`, `Feec.BoundedDomain.exists_orbit_not_propagate`, `Feec.BoundedDomain.exists_orbit_not_propagate_unconditional`, `Feec.BoundedDomain.exists_projTSD_not_mem_HcurlZero`, `Feec.BoundedDomain.exists_tsd_not_propagates`, `Feec.BoundedDomain.integral_eq_zero_bochner`, `Feec.BoundedDomain.integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`, `Feec.BoundedDomain.not_dense_TSD_inter_HcurlZero`, `Feec.BoundedDomain.not_dense_domL_inter_Kc`, `Feec.BoundedDomain.not_finiteDimensional_obstr`, `Feec.BoundedDomain.not_finiteDimensional_orth_closure_TSD_inter_HcurlZero`, `Feec.BoundedDomain.not_projection_hyp`, `Feec.BoundedDomain.not_projection_hyp_S2`, `Feec.BoundedDomain.not_projection_hyp_adjoint`, `Feec.BoundedDomain.not_propagate_of_adjoint`, `Feec.BoundedDomain.projTSD_not_mem_HcurlZero`, `Feec.BoundedDomain.projection_unbounded`, `Feec.BoundedDomain.prop417_density_gap`, `Feec.BoundedDomain.starProjection_grad`, `Feec.BoundedDomain.sum_integral_mul_pd_eq_zero`, `Feec.BoundedDomain.thesisComplex_adjoint_mem_TSD0`, `Feec.BoundedDomain.thesisComplex_beta_violation_boundary_layer`, `Feec.BoundedDomain.thesisComplex_dense_literal`, `Feec.BoundedDomain.thesisComplex_not_projection_hyp`, `Feec.BoundedDomain.thesisComplex_not_projection_hyp2`, `Feec.BoundedDomain.thesisComplex_not_propagate`, `Feec.BoundedDomain.thesisComplex_orbit_not_propagate`, `Feec.BoundedDomain.thesisComplex_orbit_not_propagate_unconditional`, `Feec.BoundedDomain.thesisComplex_prop_4_17_max`, `Feec.BoundedDomain.thesisComplex_tsd_not_propagates`, `Feec.BoundedDomain.thesisComplex_violation_boundary_layer`, `Feec.BoundedDomain.thesisComplex_waveGroup_not_invariant`, `Feec.BoundedSym.symComplexB_prop_4_16`, `Feec.BoundedSym.symComplexB_prop_4_18`, `Feec.Box.forward_boxTSD_iff`, `Feec.Box.mem_Kmax_boxTSD_iff`, `Feec.Box.mirror_prop_4_17`, `Feec.Box.mirror_prop_4_17_exists`, `Feec.Box.offB_mem_Kmax`, `Feec.Box.staticB_mem_Kmax`, `Feec.Box.thesisBox_mem_Kmax_iff`, `Feec.Ch6.Bounded.bggComplex_verdict`, `Feec.Constraints.IsReducedSolution`, `Feec.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Constraints.grad_sq_not_whitney`, `Feec.Constraints.pgrad_mem_PminusLambda1`, `Feec.Constraints.pgrad_not_mem_PminusLambda1`, `Feec.Constraints.prop_4_17`, `Feec.Constraints.prop_4_17_exists_unconditional`, `Feec.Constraints.prop_4_17_max`, `Feec.Constraints.prop_4_17_max_unconditional`, `Feec.Constraints.prop_4_18`, `Feec.Constraints.prop_4_18_i`, `Feec.Constraints.prop_4_18_ii`, `Feec.Constraints.reduced_mem_ker`, `Feec.Constraints.reduced_unique`, `Feec.Constraints.revT`, `Feec.Constraints.waveOp_revT`, `Feec.CrankNicolson.FullStep`, `Feec.CrankNicolson.RedStep`, `Feec.CrankNicolson.cn_invertible`, `Feec.CrankNicolson.red_step_energy`, `Feec.Models.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.Repair.C417.mirrorCxCube_prop_4_17_exists`, `Feec.Repair.C417.mirrorCxQ_prop_4_17_exists`, `Feec.Torus.projKc_mem_domL`, `Feec.Torus.prop_4_17_torus`, `Feec.Torus.prop_4_17_torus_backward`, `Feec.Torus.prop_4_17_torus_classical`, `Feec.Torus.prop_4_17_torus_exists`, `Feec.Torus.prop_4_17_torus_group_all`, `Feec.Whole.projKc_mem_domL`, `Feec.Whole.prop_4_17_whole`, `Feec.Whole.prop_4_17_whole_exists`, `Feec.WholeReal.real_prop_4_17_whole`, `Feec.WholeReal.real_prop_4_17_whole_exists`
- modules: Feec.Algebra.PolynomialForm, Feec.Algebra.Proxy3, Feec.Ch4.BoundedDensity, Feec.Ch4.BoundedDomain, Feec.Ch4.BoundedDomainExt, Feec.Ch4.BoundedInterior, Feec.Ch4.BoundedSalvage, Feec.Ch4.BoundedSalvageDim, Feec.Ch4.BoundedSalvageMax, Feec.Ch4.BoundedSym, Feec.Ch4.Box, Feec.Ch4.BoxIdent, Feec.Ch4.BoxMirror, Feec.Ch4.BoxStatic, Feec.Ch4.BoxThesis, Feec.Ch4.Constraints, Feec.Ch4.StoneApplications, Feec.Ch4.Torus, Feec.Ch4.TorusGroup, Feec.Ch4.TorusWeak, Feec.Ch4.Unconditional, Feec.Ch4.Whole, Feec.Ch4.WholeReal, Feec.Ch6.Bounded, Feec.Ch7.CrankNicolson, Feec.Counterexamples.PolynomialForms, Feec.Models.BoundedDomain.GradCurl, Feec.Models.Cube.Mirror, Feec.Models.Cube.Parity, Feec.Repair.C410, Feec.Repair.C417, Feec.Repair.C417Cube, Feec.Repair.C417Pi

### Sec §4.11

- tagged: `Feec.Models.Cube.MirrorSym.complex`
- cited: `Feec.BoundedDomain.not_propagate_of_adjoint`, `Feec.BoundedSym.adjoint_curlS_mem_TSDS`, `Feec.BoundedSym.curlS_mem_TSDT`, `Feec.BoundedSym.not_dense_TSDS_inter_domain`, `Feec.BoundedSym.not_finiteDimensional_obstrS`, `Feec.BoundedSym.not_projection_hyp_adjoint_curlS`, `Feec.BoundedSym.symComplexB_diagnosis`, `Feec.BoundedSym.symComplexB_mem_TSD0_of_propagate`, `Feec.BoundedSym.symComplexB_not_projection_hyp`, `Feec.BoundedSym.symComplexB_not_projection_hyp2`, `Feec.BoundedSym.symComplexB_not_propagate`, `Feec.BoundedSym.symComplexB_not_propagate_unconditional`, `Feec.BoundedSym.symComplexB_prop_4_16`, `Feec.BoundedSym.symComplexB_prop_4_19_max`, `Feec.BoundedSym.symComplexD_diagnosis`, `Feec.BoundedSym.symComplexD_not_projection_hyp`, `Feec.Box.mirror_prop_4_19`, `Feec.Box.mirror_prop_4_19_exists`, `Feec.Ch6.Bounded.bggComplex_verdict`, `Feec.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Constraints.prop_4_17`, `Feec.Constraints.prop_4_17_exists_unconditional`, `Feec.Constraints.prop_4_17_max`, `Feec.Counterexamples.BallSymTSD.not_propagates`, `Feec.Repair.C417.mirrorSymCxCube_prop_4_19_exists`, `Feec.Repair.C417.mirrorSymCxQ_prop_4_19_exists`, `Feec.TorusSym.adjoint_curlS`, `Feec.TorusSym.adjoint_hessS`, `Feec.TorusSym.curlSym_mem_trSub`, `Feec.TorusSym.projKc_mem_domL`, `Feec.TorusSym.prop_4_19_torus`, `Feec.TorusSym.prop_4_19_torus_exists`, `Feec.TorusSym.prop_4_19_torus_exists_real`, `Feec.TorusSym.prop_4_19_torus_real_space`, `Feec.TorusSym.symComplex`, `Feec.TorusSym.symComplex_closedRange`, `Feec.TorusSym.symComplex_hodge`, `Feec.TorusSym.symGroup`, `Feec.WholeSym.projKc_mem_domL`, `Feec.WholeSym.prop_4_19_whole`, `Feec.WholeSym.prop_4_19_whole_exists`, `Feec.WholeSym.symWComplex`
- modules: Feec.Ch4.BoundedSalvage, Feec.Ch4.BoundedSalvageMax, Feec.Ch4.BoundedSym, Feec.Ch4.BoundedSymDual, Feec.Ch4.BoundedSymExt, Feec.Ch4.BoxMirror, Feec.Ch4.Constraints, Feec.Ch4.Torus, Feec.Ch4.TorusSym, Feec.Ch4.Unconditional, Feec.Ch4.Whole, Feec.Ch4.WholeSym, Feec.Ch6.Bounded, Feec.Counterexamples.BallSymTSD, Feec.Models.Cube.MirrorSym, Feec.Repair.C417, Feec.Repair.C419Cube, Feec.Repair.C419Pi

### Sec §5.1

- tagged: `Feec.BGG.HilbertData.twistComplex`, `Feec.BGG.Segment`, `Feec.BGG.Segment.D1_D0`
- cited: `Feec.BGG.Data`, `Feec.BGG.Hilb`, `Feec.BGG.Hilb.Hyps`, `Feec.BGG.Hilb.Wcheck`, `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`, `Feec.BGG.Hilb.jW_spec`, `Feec.BGG.Hilb.mem_Z1_iff`, `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`, `Feec.BGG.Hilb.tripleNorm_definite`, `Feec.BGG.Hilb.tripleNorm_spec`, `Feec.BGG.HilbertData`, `Feec.BGG.HilbertData.twistComplex`, `Feec.BGG.Segment`, `Feec.BGG.Segment.D0`, `Feec.BGG.Segment.D1`, `Feec.BGG.Segment.D1_D0`, `Feec.BGG.Segment.ExactBot`, `Feec.BGG.Segment.ExactTop`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.Γ`, `Feec.BGG.Stability`, `Feec.BGG.WaveData.Wcheck`, `Feec.BGGData`, `Feec.BGGData.D1_D0`, `Feec.Ch5.BGG.BGGHilb`, `Feec.Ch5.BGG.BGGHilb.mem_Z1_iff`, `Feec.Ch5.BGG.exact_mid`
- modules: Feec.Ch5.BGG, Feec.Foundation.BGG, Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.BGG.Twisted, Feec.HilbertComplex.BGG.WeakSymmetry

### Sec §5.2

- cited: `Feec.BGG.Discrete`, `Feec.BGG.Discrete.Compatible`, `Feec.BGG.Discrete.exact_mid_h`, `Feec.BGG.Discrete.exists_sub_S0h_eq`, `Feec.BGG.IsMixedSolution`, `Feec.BGG.anticomm_of_comm_proj`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.exists_of_exact_rows`, `Feec.BGG.mixedForm_bijective`, `Feec.BGG.surjective_of_comp_eq`, `Feec.Ch5.Discrete.Disc`, `Feec.Ch5.Discrete.Disc.Hyp54`, `Feec.Ch5.Discrete.Sys56`
- modules: Feec.Ch5.Discrete, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent

### Sec §5.3

- tagged: `Feec.FiniteElement.comp_eq_of_dof`
- cited: `Feec.FiniteElement.comp_eq_of_dof`
- modules: Feec.FiniteElement.Dof

### Sec §6.1

- cited: `Feec.BGG.WaveData.MultiplierSolution`, `Feec.BGG.WaveData.MultiplierSolution.unique`, `Feec.BGG.WaveData.Solution`, `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.BGG.WaveData.Solution.unique`, `Feec.BGG.WaveData.Wcheck`, `Feec.Ch6.Bounded.bggComplex_verdict`, `Feec.Ch6.ContData`, `Feec.Ch6.ContData.Sol61`, `Feec.Ch6.ContData.Sol62`, `Feec.Ch6.ContData.Wcheck`, `Feec.Repair.C417.bggCxQ_verdict`
- modules: Feec.Ch6.Bounded, Feec.Ch6.TimeDependent, Feec.Ch6.Whole, Feec.HilbertComplex.BGG.TimeDependent, Feec.Repair.C417, Feec.Repair.C417BggCube, Feec.Repair.C417BggTorus

### Sec §6.2

- cited: `Feec.BGG.Counterexample.not_projected_compatible_phi`, `Feec.BGG.DiscreteSolution`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection`, `Feec.BGG.discreteSkewForm`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.BGG.projected_compatible_phi_iff`, `Feec.BGG.projected_compatible_u`, `Feec.Ch6.Sol63`, `Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi`
- modules: Feec.Ch6.TimeDependent, Feec.Counterexamples.ConstrainedEvolution, Feec.HilbertComplex.BGG.TimeDependent, Feec.Repair.C67, Feec.Repair.C67Prop62

### Sec §6.3

- tagged: `Feec.Models.Euclidean.BGG.reducingSubcomplex`, `Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Euclidean.BGG.tsd_propagates`, `Feec.Models.Euclidean.BGG.tsd_propagates_neg`, `Feec.Models.Euclidean.BGG.waveGroup_mem`, `Feec.Models.Torus.BGG.closedRangeAt`, `Feec.Models.Torus.BGG.hodge`, `Feec.Models.Torus.BGG.reducingSubcomplex`, `Feec.Models.Torus.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_propagates`, `Feec.Models.Torus.BGG.tsd_propagates_neg`, `Feec.Models.Torus.BGG.waveGroup_mem`
- cited: `Feec.Ch6.Bounded.bggComplex_verdict`, `Feec.Repair.C417.bggCxQ_verdict`
- modules: Feec.Ch6.Bounded, Feec.Ch6.Whole, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG, Feec.Repair.C417, Feec.Repair.C417BggCube, Feec.Repair.C417BggTorus

### Ch 5

- named: `Feec.Ch5.Discrete.Disc.C55`, `Feec.Ch5.Discrete.Disc.Hyp54`, `Feec.Ch5.Discrete.Sys56`

### Ch 6

- named: `Feec.Ch6.ContData.Sol61`, `Feec.Ch6.ContData.Sol62`, `Feec.Ch6.Sol63`, `Feec.Ch6.ch6_convergence`, `Feec.Ch6.ch6_convergence_Sol63`, `Feec.Ch6.ch6_convergence_rate`, `Feec.Repair.C417.ch6_corrected`, `Feec.Repair.C67.ch6_convergence_projected`

### Ch 7

- cited: `Feec.CrankNicolson.E0`, `Feec.CrankNicolson.FullStep`, `Feec.CrankNicolson.RedStep`, `Feec.CrankNicolson.cellCount_table`, `Feec.CrankNicolson.cn_invertible`, `Feec.CrankNicolson.cn_iterates_agree`, `Feec.CrankNicolson.cn_matrix_det_ne_zero`, `Feec.CrankNicolson.cn_matrix_energy`, `Feec.CrankNicolson.div_B_invariant_full`, `Feec.CrankNicolson.final_time_table`, `Feec.CrankNicolson.fullLHS_bijective`, `Feec.CrankNicolson.full_step_energy`, `Feec.CrankNicolson.full_step_unique`, `Feec.CrankNicolson.minres_symm`, `Feec.CrankNicolson.planeWave`, `Feec.CrankNicolson.planeWave_solves`, `Feec.CrankNicolson.red_step_energy`, `Feec.CrankNicolson.red_to_full`, `Feec.CrankNicolson.stepCount_table`, `Feec.Repair.C67.cnSystem_not_isSymm_of_ne`, `Feec.Repair.C67.cn_matrix_not_isSymm`, `Feec.Repair.C67.cn_schur_iff`, `Feec.Repair.C67.minres_cn_existsUnique`, `Feec.Repair.C67.minres_matrix_indefinite`, `Feec.Repair.C67.minres_matrix_isUnit`, `Feec.Repair.C67.minres_matrix_not_posDef`, `Feec.Repair.C67.minres_solution_iff_cnStep`, `Feec.Repair.C67.minres_solution_iff_redStep`, `Feec.Repair.C67.schurE_posDef`
- modules: Feec.Ch7.CrankNicolson, Feec.Repair.C67, Feec.Repair.C67Minres
