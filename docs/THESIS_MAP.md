# Thesis map

Traceability from V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of
General Relativity* (PhD thesis, Minnesota, 2015) [QuennevilleBelair2015] to the Lean
declarations of `Feec`. Lean names carry no thesis numbers after the refactor
(`docs/REFACTOR_PLAN.md` §1); this file is the only place where they meet.

**Generated** by `scripts/ThesisMap.sh` from declaration names and docstrings; do not edit by
hand, rerun after renaming. A declaration is listed under a thesis id when

- **named**: it is a current home (`docs/migration/map.tsv`) of a pre-refactor declaration whose
  name encoded the id (`prop_4_17`, `prop417_density_gap`, `ch6_corrected`, `Sol61`); those old
  names are listed, unchecked, under **old**;
- **tagged**: its docstring has a `Thesis: Prop 4.17 (corrected)` tag (the convention for new
  declarations);
- **cited**: its docstring cites the id, as `[QuennevilleBelair2015], Prop. 4.17` or inside
  `[QuennevilleBelair2015, ...]`.

Every backticked name in a list item below is checked by `scripts/MapCheck.sh`
(`#check @name` must elaborate).

Counts at generation: 40 numbered results (Thm/Prop/Cor/Lemma/Remark/Def), 73 equations/sections/chapters, 888 distinct declarations (136 current homes of thesis-numbered old names).

## Results

### Prop 2.1

- named: `Feec.CurvatureTensor.interchange_of_bianchi`, `Feec.CurvatureTensor.lower_riemComp_isAlgCurv`, `Feec.CurvatureTensor.riemField_isAlgCurv`
- old: Feec.Curvature.prop_2_1, Feec.Curvature.prop_2_1_jet
- tagged: `Feec.CurvatureTensor.Bianchi1`, `Feec.CurvatureTensor.PairSkew`, `Feec.CurvatureTensor.lower_riemComp_isAlgCurv`, `Feec.CurvatureTensor.lower_riemComp_skew`, `Feec.CurvatureTensor.riemComp_bianchi`, `Feec.CurvatureTensor.riemComp_skew`, `Feec.CurvatureTensor.riemField_isAlgCurv`
- cited: `Feec.DoubleForm.bianchi_iff_altPart`
- modules: Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Bivector, Feec.Geometry.Connection, Feec.Legacy.Tensor

### Thm 2.3

- tagged: `Feec.LinearizedGravity.HbarJet`, `Feec.LinearizedGravity.Hfun`, `Feec.LinearizedGravity.Hfun_eq_bar`, `Feec.LinearizedGravity.Hjet`, `Feec.LinearizedGravity.Hjet_eq_bar`, `Feec.LinearizedGravity.Hjet_eq_div`, `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.Hsym_eq`
- modules: Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Prop 2.4

- named: `Feec.Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ`
- old: Feec.Linearized.thesis_prop_2_4b_false
- tagged: `Feec.Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ`, `Feec.LinearizedGravity.Hfun_lorentz`, `Feec.LinearizedGravity.Hjet_lorentz`, `Feec.LinearizedGravity.Hsym_lorentz`, `Feec.LinearizedGravity.LorentzJet`, `Feec.LinearizedGravity.exists_lorentz_gauge`
- modules: Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge, Feec.Physics.LinearizedGravity.PlaneWave

### Prop 2.5

- tagged: `Feec.LinearizedGravity.plane_wave`
- modules: Feec.Physics.LinearizedGravity.PlaneWave

### Prop 2.6

- named: `Feec.LinearizedGravity.exists_ttGauge`, `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`
- old: Feec.Repair.C2.prop_2_6, Feec.Repair.C2.prop_2_6_metric
- tagged: `Feec.LinearizedGravity.exists_ttGauge`, `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`, `Feec.LinearizedGravity.tt_gauge_fun`
- cited: `Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed`, `Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed_contra`, `Feec.LinearizedGravity.tt_gauge`
- modules: Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.PlaneWave

### Prop 3.1

- named: `Feec.DoubleForm.electric_magnetic_props`
- old: Feec.Bivector.prop_3_1
- cited: `Feec.DoubleForm.electric_magnetic_props`
- modules: Feec.Geometry.WeylDecomposition

### Prop 3.2

- named: `Feec.DoubleForm.blocks_eq_and_duals`
- old: Feec.Bivector.prop_3_2
- cited: `Feec.DoubleForm.blocks_eq_and_duals`, `Feec.DoubleForm.ldual_ofBlocks`, `Feec.DoubleForm.ldual_rdual_ofBlocks`, `Feec.DoubleForm.rdual_ofBlocks`
- modules: Feec.Geometry.Hodge2

### Prop 3.3

- cited: `Feec.DoubleForm.altPart_ofBlocks_iff`, `Feec.DoubleForm.bianchi_iff_altPart`, `Feec.DoubleForm.bianchi_ofBlocks_iff`, `Feec.DoubleForm.interchange_iff`, `Feec.DoubleForm.tracefree_iff`, `Feec.DoubleForm.weyl_iff`, `Feec.EinsteinBianchi.dWeyl`
- modules: Feec.Geometry.Bivector, Feec.Geometry.WeylDecomposition, Feec.Physics.EinsteinBianchi.System

### Prop 3.4

- cited: `Feec.EinsteinBianchi.EBJet`, `Feec.EinsteinBianchi.EBJetSym_surjective`, `Feec.EinsteinBianchi.linBianchi_field_iff`, `Feec.EinsteinBianchi.linBianchi_iff`, `Feec.EinsteinBianchi.linBianchi_iff_sym`
- modules: Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.System

### Lemma 3.5

- tagged: `Feec.Fourier.GradCurl.curl_mem_tsd`, `Feec.Fourier.GradCurl.isFibreReducing`, `Feec.Fourier.SymCurl.curl_mem_trSub`, `Feec.Fourier.SymCurl.isFibreReducing`, `Feec.MatrixSymbol.axial_curl`, `Feec.MatrixSymbol.curl`, `Feec.MatrixSymbol.curlSymbol_mem_ttSub`, `Feec.MatrixSymbol.curl_isTSD`, `Feec.MatrixSymbol.div`, `Feec.MatrixSymbol.div_curl`, `Feec.MatrixSymbol.div_sub_transpose`, `Feec.MatrixSymbol.trace_curl`, `Feec.MatrixSymbol.trace_curl_eq_vskw`, `Feec.MatrixSymbol.trace_curl_of_transpose_eq`, `Feec.MatrixSymbol.transpose_curl_eq`, `Feec.MatrixSymbol.two_smul_vskw_curl`, `Feec.MatrixSymbol.vskw`, `Feec.Models.BoundedDomain.curl_symm_of_mem_tsd`
- cited: `Feec.EinsteinBianchi.curl_TSD_field`, `Feec.EinsteinBianchi.div_curl_field`, `Feec.Legacy.BoundedDomain.curl_symm_of_mem_TSD`, `Feec.Legacy.Constraints.curl_TSD`, `Feec.Legacy.Constraints.curl_TSD_div`, `Feec.Legacy.Constraints.div_curl`, `Feec.Legacy.Constraints.trace_curl`, `Feec.Legacy.Constraints.trace_curl_of_symm`, `Feec.Legacy.Constraints.two_vskw_curl`, `Feec.Legacy.Torus.curlR_apply_eps3`, `Feec.Legacy.Torus.curlR_mem_tsd`, `Feec.Legacy.TorusSym.curlST_mem_L2TSDT`, `Feec.Legacy.TorusSym.curlSym_mem_trSub`, `Feec.Legacy.curl`, `Feec.Legacy.div`, `Feec.Legacy.vskw`
- modules: Feec.Algebra.MatrixSymbol, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedDomainTSD, Feec.Fourier.BGGSymbol, Feec.Fourier.GradCurlSymbol, Feec.Fourier.SymCurlSymbol, Feec.Legacy.BoundedDomain.Basic, Feec.Legacy.BoundedDomain.Interior, Feec.Legacy.BoundedDomain.Salvage, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.BoundedDomain.SymExt, Feec.Legacy.Box.Basic, Feec.Legacy.Constraints, Feec.Legacy.MirrorCube.BggTorus, Feec.Legacy.Tensor, Feec.Legacy.Torus.Basic, Feec.Legacy.Torus.Sym, Feec.Legacy.Whole.Basic, Feec.Models.BoundedDomain.GradCurl, Feec.Models.Torus.BGG, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.System

### Prop 3.6

- named: `Feec.EinsteinBianchi.propagation_hyps_nonvacuous`, `Feec.EinsteinBianchi.tsd_propagates`
- old: Feec.EB.prop_3_6, Feec.EB.prop_3_6_hyps_nonvacuous
- tagged: `Feec.Domain.FiniteSpeed.IsWeakSolution.ae_eq_zero_of_ball`, `Feec.EinsteinBianchi.tsd_propagates_classical`
- cited: `Feec.EinsteinBianchi.curl_TSD_field`, `Feec.EinsteinBianchi.div_propagation`, `Feec.EinsteinBianchi.energy_flux`, `Feec.EinsteinBianchi.tsd_propagates`, `Feec.EinsteinBianchi.violation_evolution`
- modules: Feec.Domain.FiniteSpeed, Feec.Legacy.BoundedDomain.Interior, Feec.Physics.EinsteinBianchi.Constraints, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.Propagation, Feec.Physics.EinsteinBianchi.System

### Thm 4.1

- tagged: `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`, `Feec.HilbertComplex.hodge`, `Feec.HilbertComplex.hodge_domain`, `Feec.HilbertComplex.hodge_domainComplex`, `Feec.HilbertComplex.hodge_domain_of_closedRangeAt`, `Feec.HilbertComplex.hodge_of_closedRangeAt`
- cited: `Feec.BGG.Hilb.hodge_Vt1`, `Feec.Legacy.Constraints.ker_adj0_orth_le`, `Feec.Legacy.HilbertComplex2.hodge_W`, `Feec.Legacy.HilbertComplex2.hodge_W_of_closedRange`, `Feec.Legacy.TorusSym.symComplex_hodge`
- modules: Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.Compactness, Feec.HilbertComplex.DomainComplex, Feec.HilbertComplex.Hodge, Feec.Legacy.Adjoint, Feec.Legacy.Constraints, Feec.Legacy.Hodge, Feec.Legacy.Torus.Sym

### Thm 4.2

- tagged: `Feec.Counterexamples.not_poincare_curl`, `Feec.Counterexamples.not_poincare_grad`, `Feec.HilbertComplex.closedRangeAt_iff_poincare`, `Feec.HilbertComplex.closedRangeAt_iff_poincare_adjoint`, `Feec.HilbertComplex.closedRangeAt_iff_poincare_of_rel`, `LinearPMap.exists_norm_le_of_isClosed_range`, `LinearPMap.isClosed_range_iff_exists_norm_le`
- cited: `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`
- modules: Feec.Counterexamples.NonClosedRangeEuclidean, Feec.ForMathlib.LinearPMap.ClosedRange, Feec.Fourier.ClosedRange, Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.DomainComplex, Feec.HilbertComplex.Hodge, Feec.Legacy.Hodge

### Thm 4.3

- named: `Feec.C0Semigroup.existsUnique_classicalSolution`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.isSkewAdjoint_wave`, `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`
- old: Feec.HilbertComplex2.thm_4_3_hodgeWave, Feec.HilbertComplex2.thm_4_3_hodgeWave_thm43, Feec.IsSkewAdjoint.wellPosedClassical_thm43, Feec.IsSkewAdjoint.wellPosedClassical_thm43Full, Feec.IsSkewAdjoint.wellPosedExistence_thm43, Feec.IsSkewAdjoint.wellPosedExistence_thm43Full, Feec.Torus.thm_4_3_torus, Feec.UnitaryGroupGenerator.wellPosedClassical_thm43, Feec.UnitaryGroupGenerator.wellPosedClassical_thm43Full, Feec.thm_4_3_full, Feec.thm_4_3_of_isSkewAdjoint, Feec.thm_4_3_unconditional
- tagged: `Feec.C0Semigroup.isClassicalSolution_mild`, `Feec.Evolution.IsStrongSolution.norm_sub_le`, `Feec.Evolution.IsStrongSolution.unique`, `Feec.Examples.bounded_standing_hypotheses`, `Feec.Examples.rotGen_standing_hypotheses`, `Feec.Maxwell.gauss_existsUnique`, `LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup`
- cited: `Feec.Evolution.ForcingClass.admissible`, `Feec.Evolution.IsClassicalSolution`, `Feec.ForcingClass.admissible`, `Feec.ForcingThm43Full`, `Feec.Legacy.Constraints.isStrongSolution_orbit`, `Feec.Legacy.Constraints.strong_unique`, `Feec.Legacy.HilbertComplex2.existsUnique_classical_of_wellPosed`, `Feec.Legacy.HilbertComplex2.waveOp_isSkewAdjoint`, `Feec.Legacy.IsClassicalSolution`, `Feec.Legacy.IsSkewAdjoint.neg`, `Feec.Legacy.IsSkewAdjoint.wellPosedClassical`, `Feec.Legacy.IsSkewAdjoint.wellPosedHom`, `Feec.Legacy.IsStrongSolution`, `Feec.Legacy.IsStrongSolution.norm_sub_le`, `Feec.Legacy.IsStrongSolution.unique`, `Feec.Legacy.Torus.periodicGroup`, `Feec.Legacy.UnitaryGroupGenerator`, `Feec.Legacy.UnitaryGroupGenerator.isSkewSymm`, `Feec.Legacy.UnitaryGroupGenerator.wellPosedClassical`, `Feec.Legacy.UnitaryGroupGenerator.wellPosedHom`, `Feec.Legacy.WellPosedClassical`, `Feec.Legacy.stoneGroup`, `Feec.Legacy.strongSolution_unique`
- modules: Feec.Evolution.Duhamel, Feec.Evolution.Forcing, Feec.Evolution.Solution, Feec.Evolution.WellPosed, Feec.Examples.NonVacuity, Feec.Legacy.Constraints, Feec.Legacy.Evolution, Feec.Legacy.Existence, Feec.Legacy.HodgeWave, Feec.Legacy.Restriction, Feec.Legacy.Stone, Feec.Legacy.Torus.Group, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution, Feec.Legacy.Whole.Basic, Feec.Physics.Maxwell.Constraints, Feec.Semigroup.Stone

### Thm 4.4

- named: `LinearPMap.IsSkewAdjoint.restrict`
- old: Feec.thm_4_4
- tagged: `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `LinearPMap.IsSkewAdjoint.restrict`
- cited: `Feec.Legacy.Constraints.Kc_propagate`, `Feec.Legacy.Constraints.projK_mem_domL`, `Feec.Legacy.Constraints.propagate`, `Feec.Legacy.Constraints.waveOp_mem_K`, `Feec.Legacy.Constraints.waveOp_mem_Kc`, `Feec.Legacy.IsStrongSolution.mem_of_invariant`
- modules: Feec.Evolution.Constrained, Feec.ForMathlib.LinearPMap.Reducing, Feec.HilbertComplex.Reducing, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.Constraints, Feec.Legacy.Evolution, Feec.Legacy.Existence, Feec.Legacy.Operators, Feec.Legacy.Restriction, Feec.Legacy.WaveGroup

### Cor 4.5

- named: `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `Feec.Examples.ker_standing_hypotheses`, `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`, `LinearPMap.IsSkewAdjoint.restrict`
- old: Feec.cor_4_5, Feec.cor_4_5_ambient, Feec.cor_4_5_ambient_unconditional, Feec.cor_4_5_classical, Feec.cor_4_5_classical_unconditional, Feec.cor_4_5_hypotheses_bddOp_ker, Feec.cor_4_5_of_isSkewAdjoint, Feec.cor_4_5_unconditional
- tagged: `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `Feec.Examples.ker_standing_hypotheses`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`
- cited: `Feec.EinsteinBianchi.div_propagation`, `Feec.EinsteinBianchi.energy_flux`, `Feec.EinsteinBianchi.tsd_propagates`, `Feec.EinsteinBianchi.violation_evolution`, `Feec.Legacy.Constraints.Kc_propagate`, `Feec.Legacy.Constraints.propagate`, `Feec.Legacy.IsStrongSolution.mem_of_invariant`
- modules: Feec.Evolution.Constrained, Feec.Examples.NonVacuity, Feec.HilbertComplex.Reducing, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.Constraints, Feec.Legacy.Evolution, Feec.Legacy.Existence, Feec.Legacy.Restriction, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution, Feec.Physics.EinsteinBianchi.Propagation, Feec.Physics.EinsteinBianchi.System

### Thm 4.5

- modules: Feec.Legacy.BoundedDomain.Basic

### Thm 4.6

- named: `Feec.HilbertComplex.HodgeWave.existsUnique_hom`, `Feec.HodgeWave.existsUnique`, `Feec.HodgeWave.existsUnique_hom`, `Feec.Legacy.HilbertComplex2.existsUnique_classicalSolution_neg_waveOp`
- old: Feec.HilbertComplex2.thm_4_6, Feec.HilbertComplex2.thm_4_6_classical, Feec.HilbertComplex2.thm_4_6_classical_of_unitaryGroupGenerator, Feec.HilbertComplex2.thm_4_6_of_unitaryGroupGenerator, Feec.HilbertComplex2.thm_4_6_strong_unconditional, Feec.HilbertComplex2.thm_4_6_unconditional
- tagged: `Feec.Evolution.IsStrongSolution.unique`, `Feec.Examples.idComplex_nonvacuous`, `Feec.HilbertComplex.HodgeWave.existsUnique`, `Feec.HilbertComplex.HodgeWave.existsUnique_hom`, `Feec.HilbertComplex.isSkewAdjoint_wave`, `Feec.HodgeWave.existsUnique`, `Feec.HodgeWave.existsUnique_hom`, `Feec.HodgeWave.norm_eq`, `Feec.ShortHilbertComplex.isSkewAdjoint_wave`
- cited: `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.Legacy.Constraints.reducedSolution_of_wellPosedHom`, `Feec.Legacy.Constraints.strong_unique`, `Feec.Legacy.Constraints.waveOp_isSkewSymm`, `Feec.Legacy.Constraints.wellPosedHom_boundedComplex`, `Feec.Legacy.HilbertComplex2.adjoint_waveOp_domain_le`, `Feec.Legacy.HilbertComplex2.dense_domL`, `Feec.Legacy.HilbertComplex2.dense_midDomain`, `Feec.Legacy.HilbertComplex2.eqOn_waveGroup_of_isWeakSolution`, `Feec.Legacy.HilbertComplex2.existsUnique_classicalSolution_neg_waveOp`, `Feec.Legacy.HilbertComplex2.existsUnique_classical_of_unitaryGroupGenerator`, `Feec.Legacy.HilbertComplex2.existsUnique_classical_of_wellPosed`, `Feec.Legacy.HilbertComplex2.existsUnique_strongSolution_neg_waveOp`, `Feec.Legacy.HilbertComplex2.isStrongSolution_waveGroup`, `Feec.Legacy.HilbertComplex2.neg_waveOp_isSkewAdjoint`, `Feec.Legacy.HilbertComplex2.orthogonal_ker_adjoint_d0_le`, `Feec.Legacy.HilbertComplex2.orthogonal_ker_d1_le`, `Feec.Legacy.HilbertComplex2.waveOp_isSkewAdjoint`, `Feec.Legacy.IsStrongSolution.unique`, `Feec.Legacy.Torus.periodicGroup`, `Feec.Legacy.UnitaryGroupGenerator.wellPosedHom`, `Feec.Legacy.WellPosedHom`, `Feec.Legacy.adjoint_adjoint`
- modules: Feec.Counterexamples.ClassicalRegularity, Feec.Evolution.Solution, Feec.Examples.NonVacuity, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.Dirac, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.Short, Feec.Legacy.Adjoint, Feec.Legacy.Constraints, Feec.Legacy.ErrorEstimateDomain, Feec.Legacy.Evolution, Feec.Legacy.Existence, Feec.Legacy.HodgeWave, Feec.Legacy.Stone, Feec.Legacy.Torus.Group, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution

### Thm 4.7

- named: `Feec.HilbertComplex.HodgeWave.classicalWeak_iff_classical`, `Feec.HilbertComplex.HodgeWave.weak_iff_strong`, `Feec.HodgeWave.classicalWeak_iff_classical`, `Feec.HodgeWave.weak_iff_strong`
- old: Feec.HilbertComplex2.thm_4_7, Feec.HilbertComplex2.thm_4_7_classical, Feec.HilbertComplex2.thm_4_7_classical_unconditional, Feec.HilbertComplex2.thm_4_7_unconditional
- tagged: `Feec.Examples.idComplex_nonvacuous`, `Feec.HilbertComplex.HodgeWave.classicalWeak_iff_classical`, `Feec.HilbertComplex.HodgeWave.weak_iff_strong`, `Feec.HodgeWave.IsWeakSolution.isClassicalSolution`, `Feec.HodgeWave.classicalWeak_iff_classical`, `Feec.HodgeWave.isClassicalWeakSolution_of_isClassicalSolution`, `Feec.HodgeWave.isWeakSolution_of_isStrongSolution`, `Feec.HodgeWave.weak_iff_strong`
- cited: `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.Legacy.HilbertComplex2.eqOn_waveGroup_of_isWeakSolution`, `Feec.Legacy.HilbertComplex2.existsUnique_classicalWeakSolution`, `Feec.Legacy.HilbertComplex2.isClassicalSolution_of_isWeakSolution`, `Feec.Legacy.HilbertComplex2.isClassicalWeakSolution_of_isClassicalSolution`, `Feec.Legacy.HilbertComplex2.isStrongSolution_of_isWeakSolution`, `Feec.Legacy.HilbertComplex2.isWeakSolution_of_isStrongSolution`, `Feec.Legacy.HilbertComplex2.norm_embed`, `Feec.Legacy.HilbertComplex2.norm_toV_le`, `Feec.Legacy.HilbertComplex2.weak_identity`, `Feec.Legacy.HilbertComplex2.weak_identity_neg`, `Feec.Legacy.HilbertComplex2.weak_imp_classical`
- modules: Feec.Examples.NonVacuity, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.HodgeWave, Feec.Legacy.ErrorEstimateDomain, Feec.Legacy.HodgeWave, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution

### Thm 4.8

- tagged: `Feec.Variational.existsUnique_of_coercive`, `Feec.Variational.infSup_of_coercive`
- modules: Feec.Legacy.Galerkin, Feec.Variational.BabuskaNecas

### Thm 4.9

- tagged: `Feec.Counterexamples.surjective_not_infSup`, `Feec.Variational.InfSup.surjective`, `Feec.Variational.babuskaNecas_iff`, `Feec.Variational.babuskaNecas_iff_inner`, `Feec.Variational.existsUnique_apply_eq`, `Feec.Variational.existsUnique_inner`, `Feec.Variational.exists_infSup_of_bijective`, `Feec.Variational.infSup_iff_mul_norm_symm_le`
- cited: `Feec.Legacy.AlgSegment.ellProj_existsUnique`, `Feec.Legacy.AlgSegment.infSup_of_testMap_mem`, `Feec.Legacy.AlgSegment.norm_ellProjFun_le`
- modules: Feec.Counterexamples.Ell2, Feec.Legacy.ErrorEstimate, Feec.Variational.BabuskaNecas

### Thm 4.10

- named: `Feec.Variational.InfSup.norm_sub_le_infDist`, `Feec.Variational.InfSup.norm_sub_le_infDist_sharp`
- old: Feec.Galerkin.thm_4_10
- tagged: `Feec.Variational.InfSup.norm_le_of_restrict_eq`, `Feec.Variational.InfSup.norm_sub_le_infDist`, `Feec.Variational.InfSup.norm_sub_le_infDist_sharp`, `Feec.Variational.InfSup.norm_sub_le_of_orthogonal`, `Feec.Variational.InfSup.norm_sub_le_of_orthogonal_sharp`, `Feec.Variational.existsUnique_galerkin`, `Feec.Variational.existsUnique_galerkin_sesq`
- cited: `Feec.Legacy.AlgSegment.DensityHyp.ellProj_tendsto`, `Feec.Legacy.AlgSegment.ellProj_quasiopt`, `Feec.Legacy.Galerkin.discrete_existsUnique`, `Feec.Legacy.Galerkin.quasi_opt`
- modules: Feec.Legacy.ErrorEstimate, Feec.Legacy.Galerkin, Feec.Variational.BabuskaNecas, Feec.Variational.Galerkin

### Thm 4.11

- named: `Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.isSaddleSolution_rieszOp_iff`
- old: Feec.Galerkin.thm_4_11
- tagged: `Feec.BGG.brezzi_wellPosed_real`, `Feec.Variational.IsSaddleSolution`, `Feec.Variational.IsSaddleSolution.norm_fst_le`, `Feec.Variational.IsSaddleSolution.norm_snd_le`, `Feec.Variational.IsSaddleSolution.unique`, `Feec.Variational.brezzi_iff`, `Feec.Variational.existsUnique_discrete_isSaddleSolution`, `Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.exists_lift`
- cited: `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.infSup_a`, `Feec.BGG.Hilb.infSup_b`, `Feec.BGG.Hilb.saddle_wellPosed`, `Feec.BGG.brezzi_wellPosed_real`
- modules: Feec.HilbertComplex.BGG.WeakSymmetry, Feec.Variational.Fortin, Feec.Variational.SaddlePoint

### Lemma 4.12

- named: `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`, `Feec.Legacy.le_add_half_integral_sharp`, `le_add_half_integral_of_sq_deriv_le_mul`, `le_add_half_sub_of_sq_deriv_le_mul`
- old: Feec.lemma_4_12, Feec.lemma_4_12_integral, Feec.lemma_4_12_sharp
- tagged: `Feec.Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le`, `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`, `le_add_half_integral_of_sq_deriv_le_mul`, `le_add_half_sub_of_sq_deriv_le_mul`, `norm_le_add_integral_of_re_inner_deriv_le`, `norm_le_of_re_inner_deriv_le`
- cited: `Feec.Legacy.le_add_half_integral_of_sq_deriv_le`, `Feec.Legacy.le_add_half_integral_sharp`, `Feec.Legacy.le_add_half_sub_of_sq_deriv_le`
- modules: Feec.Evolution.Energy, Feec.ForMathlib.Analysis.Gronwall, Feec.Legacy.ErrorEstimate

### Prop 4.13

- named: `Feec.Variational.InfSup.of_testMap`
- old: Feec.Complex3.prop_4_13, Feec.Complex3.prop_4_13_V, Feec.Complex3.prop_4_13_infSup, Feec.Complex3.prop_4_13_lower, Feec.Complex3.prop_4_13_test_norm
- tagged: `Feec.Variational.InfSup.of_testMap`, `Feec.Variational.InfSup.restrict_of_testMap`
- cited: `Feec.Legacy.AlgSegment.Sub.infSup`, `Feec.Legacy.AlgSegment.Sub.testMap_mem`, `Feec.Legacy.AlgSegment.formA_test_lower`, `Feec.Legacy.AlgSegment.infSup_of_testMap_mem`, `Feec.Legacy.AlgSegment.testMap`
- modules: Feec.HilbertComplex.Mixed, Feec.Legacy.ErrorEstimate, Feec.Variational.InfSup

### Thm 4.14

- named: `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, `Feec.Variational.GalerkinEvolution.error_bound_refined`
- old: Feec.Complex3.thm_4_14, Feec.Complex3.thm_4_14_pointwise
- tagged: `Feec.Counterexamples.ClassicalRegularity.exists_datum_not_C1`, `Feec.Counterexamples.ClassicalRegularity.not_C1_graphSpace`, `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, `Feec.Variational.GalerkinEvolution.error_bound`, `Feec.Variational.GalerkinEvolution.error_bound_refined`, `Feec.Variational.norm_sub_le_of_projected_error`, `Feec.Variational.norm_sub_le_of_projected_error_decay`
- cited: `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.Legacy.AlgSegment.IsWeakSol`, `Feec.Legacy.AlgSegment.abs_formA_le`, `Feec.Legacy.AlgSegment.convergence`, `Feec.Legacy.AlgSegment.semidiscrete_error_bound`, `Feec.Legacy.AlgSegment.semidiscrete_error_bound_pointwise`, `Feec.Legacy.FredholmCE.cxK1_convergence_without_C1`, `Feec.Legacy.FredholmCE.cxK1_exists_not_isWeakSol`, `Feec.Legacy.HilbertComplex2.convergence_W`, `Feec.Legacy.HilbertComplex2.convergence_domL`, `Feec.Legacy.HilbertComplex2.convergence_domL_classicalWeak_exists`, `Feec.Legacy.HilbertComplex2.convergence_domL_weakSolution`, `Feec.Legacy.HilbertComplex2.embW_deriv_zero_of_isWeakSol`, `Feec.Legacy.HilbertComplex2.error_bound_W`, `Feec.Legacy.HilbertComplex2.error_bound_W'`, `Feec.Legacy.HilbertComplex2.exists_isWeakSol_of_waveOp_mem`, `Feec.Legacy.HilbertComplex2.tendstoUniformlyOn_discreteSol`, `Feec.Legacy.error_bound_core`, `Feec.Legacy.norm_le_norm_zero_add_integral`, `Feec.Legacy.projected_error_bound`
- modules: Feec.Counterexamples.ClassicalRegularity, Feec.HilbertComplex.Approximation.SemidiscreteWave, Feec.HilbertComplex.BGG.TimeDependent, Feec.Legacy.ErrorEstimate, Feec.Legacy.ErrorEstimateDomain, Feec.Legacy.WeakSolution, Feec.Variational.GalerkinEvolution

### Prop 4.16

- named: `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.HilbertComplex.ReducingSubcomplex.propagates_neg`, `Feec.Legacy.BoundedBGG.bggComplex_divFree_propagates`, `Feec.Legacy.BoundedSym.symComplexB_divFree_propagates`, `Feec.Legacy.BoundedSym.symComplexD_divFree_propagates`, `Feec.Legacy.Constraints.existsUnique_classicalSolution_mem_K`, `Feec.ShortHilbertComplex.divFree_propagates`, `Feec.ShortHilbertComplex.divFree_propagates_neg`
- old: Feec.BoundedSym.symComplexB_prop_4_16, Feec.BoundedSym.symComplexD_prop_4_16, Feec.Ch6.Bounded.bggComplex_prop_4_16, Feec.Constraints.prop_4_16, Feec.Constraints.prop_4_16', Feec.Constraints.prop_4_16_classical_unconditional, Feec.Constraints.prop_4_16_exists, Feec.Constraints.prop_4_16_exists_unconditional
- tagged: `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.Maxwell.euclidean_gauss_propagates`, `Feec.Maxwell.gauss_existsUnique`, `Feec.Maxwell.gauss_propagates`, `Feec.Maxwell.pec_gauss_propagates`, `Feec.Maxwell.pmc_gauss_propagates`, `Feec.Maxwell.torus_gauss_propagates`, `Feec.Maxwell.waveGroup_mem`, `Feec.ShortHilbertComplex.divFreeSub`, `Feec.ShortHilbertComplex.divFree_propagates`, `Feec.ShortHilbertComplex.divFree_propagates_neg`, `Feec.ShortHilbertComplex.reducingSubcomplex_divFreeSub`
- cited: `Feec.Legacy.BoundedSym.symComplexB_divFree_propagates`, `Feec.Legacy.Constraints.K`, `Feec.Legacy.Constraints.divFree_propagates`, `Feec.Legacy.Constraints.existsUnique_classicalSolution_mem_K`, `Feec.Legacy.Constraints.existsUnique_divFree_mem`
- modules: Feec.HilbertComplex.Reducing, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.BoundedDomain.SymExt, Feec.Legacy.Constraints, Feec.Legacy.WaveGroup, Feec.Physics.Maxwell.Constraints

### Prop 4.17

- named: `Feec.C0Group.IsIsometric.isReducing_of_forward_invariant`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates_neg`, `Feec.HilbertComplex.ReducingSubcomplex.waveGroup_mem`, `Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.HilbertComplex.isReducing_iff_waveGroup_invariant`, `Feec.HilbertComplex.isReducing_invariantCore_waveGroup`, `Feec.HilbertComplex.le_invariantCore_waveGroup`, `Feec.Legacy.BoundedBGG.bggComplex_Kmax_propagates`, `Feec.Legacy.BoundedDomain.density_gap`, `Feec.Legacy.BoundedDomain.thesisComplex_Kmax_eq`, `Feec.Legacy.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Legacy.Constraints.propagates_iff_projKc_mem_domL`, `Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.Mirror.existsUnique_memQ`, `Feec.Models.Cube.Mirror.propagates`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Euclidean.BGG.tsd_propagates_neg`, `Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.real_tsd_propagates`, `Feec.Models.Euclidean.GradCurl.tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.GradCurl.waveGroup_mem`, `Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.GradCurl.tsd_propagates_neg`, `Feec.Models.Torus.GradCurl.waveGroup_mem`
- old: Feec.BoundedDomain.prop417_density_gap, Feec.BoundedDomain.thesisComplex_prop_4_17_max, Feec.Box.mirror_prop_4_17, Feec.Box.mirror_prop_4_17_exists, Feec.Box.prop_4_17_hyps_res, Feec.Box.prop_4_17_res, Feec.Box.prop_4_17_res_exists, Feec.Ch6.Bounded.bggComplex_prop_4_17_max, Feec.Ch6.Whole.prop_4_17_bggWhole, Feec.Constraints.le_max_of_prop_4_17_hyps, Feec.Constraints.prop_4_17, Feec.Constraints.prop_4_17_exists_unconditional, Feec.Constraints.prop_4_17_group_all_unconditional, Feec.Constraints.prop_4_17_group_unconditional, Feec.Constraints.prop_4_17_iff, Feec.Constraints.prop_4_17_iff_unconditional, Feec.Constraints.prop_4_17_max, Feec.Constraints.prop_4_17_max_unconditional, Feec.Constraints.prop_4_17_necessary, Feec.Constraints.prop_4_17_necessary_unconditional, Feec.Repair.C417.mirrorCxCube_prop_4_17_exists, Feec.Repair.C417.mirrorCxQ_prop_4_17_exists, Feec.Repair.C417.piCube_mirror_prop_4_17_exists, Feec.Repair.C417.prop_4_17_compr_exists, Feec.Repair.C417.prop_4_17_corrected, Feec.Repair.C417.prop_4_17_corrected_cube, Feec.Repair.C417.prop_4_17_hyps_compr, Feec.Repair.C417.prop_4_17_hyps_scale, Feec.Repair.C417.prop_4_17_hyps_scale2, Feec.Repair.C417.unitCube_mirror_prop_4_17_exists, Feec.Torus.prop_4_17_torus, Feec.Torus.prop_4_17_torus_backward, Feec.Torus.prop_4_17_torus_classical, Feec.Torus.prop_4_17_torus_exists, Feec.Torus.prop_4_17_torus_exists_of_Hcurl, Feec.Torus.prop_4_17_torus_group, Feec.Torus.prop_4_17_torus_group_all, Feec.Torus.prop_4_17_torus_group_periodic, Feec.Whole.prop_4_17_whole, Feec.Whole.prop_4_17_whole_exists, Feec.Whole.prop_4_17_whole_group, Feec.WholeReal.real_prop_4_17_whole, Feec.WholeReal.real_prop_4_17_whole_exists
- tagged: `Feec.Counterexamples.BoundedDomainTSD.exists_projTSD_not_mem_domain`, `Feec.Counterexamples.BoundedDomainTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedDomainTSD.not_mem_closure_wave_domain_inter`, `Feec.Counterexamples.BoundedDomainTSD.obstruction_ne_bot`, `Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`, `Feec.Counterexamples.CubeStationary.forward_iff_stationary`, `Feec.Counterexamples.CubeStationary.mem_invariantCore_tsd_iff`, `Feec.Counterexamples.CubeStationary.tsd_not_propagates`, `Feec.EinsteinBianchi.cube_tsd_propagates`, `Feec.EinsteinBianchi.euclidean_tsd_propagates`, `Feec.EinsteinBianchi.torus_tsd_propagates`, `Feec.Fourier.FibreReducing.existsUnique_mem`, `Feec.Fourier.FibreReducing.propagates`, `Feec.Fourier.GradCurl.isFibreReducing`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.HilbertComplex.isReducing_iff_waveGroup_invariant`, `Feec.Models.BoundedDomain.closure_eq_tsd₀`, `Feec.Models.BoundedDomain.integral_eq_zero_of_mem_tsd`, `Feec.Models.BoundedDomain.sum_integral_mul_pd_eq_zero`, `Feec.Models.BoundedDomain.tsd`, `Feec.Models.BoundedDomain.tsd₀`, `Feec.Models.BoundedDomain.tsd₀_le_closure`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Models.Cube.Ident.mem_invariantCore_iff`, `Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.Mirror.existsUnique_memQ`, `Feec.Models.Cube.Mirror.exists_nonstationary`, `Feec.Models.Cube.Mirror.exists_nonstationaryCube`, `Feec.Models.Cube.Mirror.exists_nonstationaryQ`, `Feec.Models.Cube.Mirror.invariantCore_eq`, `Feec.Models.Cube.Mirror.invariantCore_eqCube`, `Feec.Models.Cube.Mirror.invariantCore_eqQ`, `Feec.Models.Cube.Mirror.propagates`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Cube.Mirror.propagatesQ`, `Feec.Models.Cube.Mirror.reducingSubcomplex`, `Feec.Models.Cube.Mirror.reducingSubcomplexCube`, `Feec.Models.Cube.Mirror.reducingSubcomplexQ`, `Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ`, `Feec.Models.Cube.Parity.exists_linearIndependent_invariantCore`, `Feec.Models.Cube.Parity.forward_iff`, `Feec.Models.Cube.Parity.forward_torus_iff`, `Feec.Models.Cube.Parity.forward_tsd_iff`, `Feec.Models.Cube.Parity.invariantCore_ne_bot`, `Feec.Models.Cube.Parity.mem_invariantCore_iff`, `Feec.Models.Cube.Parity.mem_invariantCore_torus_iff`, `Feec.Models.Cube.Parity.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.reducingSubcomplex_tsd_torus`, `Feec.Models.Cube.reducingSubcomplex_tsd_torusBGG`, `Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.real_tsd_propagates`, `Feec.Models.Euclidean.GradCurl.reducingSubcomplex`, `Feec.Models.Euclidean.GradCurl.tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.tsd_propagates`, `Feec.Models.Euclidean.GradCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.GradCurl.waveGroup_mem`, `Feec.Models.Torus.GradCurl.real_tsd_existsUnique`, `Feec.Models.Torus.GradCurl.real_tsd_propagates`, `Feec.Models.Torus.GradCurl.reducingSubcomplex`, `Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.GradCurl.tsd_propagates`, `Feec.Models.Torus.GradCurl.tsd_propagates_neg`, `Feec.Models.Torus.GradCurl.waveGroup_mem`
- cited: `Feec.Legacy.BoundedDomain.HcurlM_not_projection`, `Feec.Legacy.BoundedDomain.HcurlM_not_projection_bochner`, `Feec.Legacy.BoundedDomain.adjoint_mem_TSD0_of_propagate`, `Feec.Legacy.BoundedDomain.closure_TSD_inter_HcurlM_eq`, `Feec.Legacy.BoundedDomain.closure_TSD_inter_HcurlM_inter_HdivM_eq`, `Feec.Legacy.BoundedDomain.closure_TSD_inter_HcurlZero_subset`, `Feec.Legacy.BoundedDomain.dense_domain_d1_inter_ker_adj0`, `Feec.Legacy.BoundedDomain.density_dichotomy`, `Feec.Legacy.BoundedDomain.density_gap`, `Feec.Legacy.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.Legacy.BoundedDomain.exists_data_not_propagate`, `Feec.Legacy.BoundedDomain.exists_orbit_not_propagate`, `Feec.Legacy.BoundedDomain.exists_projTSD_not_mem_HcurlZero`, `Feec.Legacy.BoundedDomain.exists_tsd_not_propagates`, `Feec.Legacy.BoundedDomain.integral_eq_zero_bochner`, `Feec.Legacy.BoundedDomain.integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`, `Feec.Legacy.BoundedDomain.not_dense_TSD_inter_HcurlZero`, `Feec.Legacy.BoundedDomain.not_dense_domL_inter_Kc`, `Feec.Legacy.BoundedDomain.not_finiteDimensional_obstr`, `Feec.Legacy.BoundedDomain.not_finiteDimensional_orth_closure_TSD_inter_HcurlZero`, `Feec.Legacy.BoundedDomain.not_projection_hyp`, `Feec.Legacy.BoundedDomain.not_projection_hyp_S2`, `Feec.Legacy.BoundedDomain.not_projection_hyp_adjoint`, `Feec.Legacy.BoundedDomain.not_propagate_of_adjoint`, `Feec.Legacy.BoundedDomain.projTSD_not_mem_HcurlZero`, `Feec.Legacy.BoundedDomain.projection_unbounded`, `Feec.Legacy.BoundedDomain.starProjection_grad`, `Feec.Legacy.BoundedDomain.sum_integral_mul_pd_eq_zero`, `Feec.Legacy.BoundedDomain.thesisComplex_Kmax_eq`, `Feec.Legacy.BoundedDomain.thesisComplex_adjoint_mem_TSD0`, `Feec.Legacy.BoundedDomain.thesisComplex_beta_violation_boundary_layer`, `Feec.Legacy.BoundedDomain.thesisComplex_dense_literal`, `Feec.Legacy.BoundedDomain.thesisComplex_not_projection_hyp`, `Feec.Legacy.BoundedDomain.thesisComplex_not_projection_hyp2`, `Feec.Legacy.BoundedDomain.thesisComplex_not_propagate`, `Feec.Legacy.BoundedDomain.thesisComplex_orbit_not_propagate`, `Feec.Legacy.BoundedDomain.thesisComplex_tsd_not_propagates`, `Feec.Legacy.BoundedDomain.thesisComplex_violation_boundary_layer`, `Feec.Legacy.Box.mem_Kmax_boxTSD_iff`, `Feec.Legacy.Box.offB_mem_Kmax`, `Feec.Legacy.Box.thesisBox_mem_Kmax_iff`, `Feec.Legacy.Constraints.Kc_propagates`, `Feec.Legacy.Constraints.Kc_propagates_iff`, `Feec.Legacy.Constraints.Kmax_propagates`, `Feec.Legacy.Constraints.existsUnique_Kmax`, `Feec.Legacy.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Legacy.Constraints.projKc_mem_domL_of_Kc_propagates`, `Feec.Legacy.Constraints.propagates_iff_projKc_mem_domL`, `Feec.Legacy.Torus.projKc_mem_domL`, `Feec.Legacy.Whole.projKc_mem_domL`, `Feec.Legacy.Whole.whole_Kc_propagates`, `Feec.Models.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.Models.Cube.MirrorTorus.existsUnique_mem`, `Feec.Models.Cube.MirrorTorus.propagates`, `Feec.Models.Euclidean.GradCurl.fourier_mem_constraint_iff`
- modules: Feec.Algebra.MatrixSymbol, Feec.Counterexamples.BoundedDomainTSD, Feec.Counterexamples.CubeStationary, Feec.Domain.Mollify, Feec.Domain.Obstruction, Feec.Fourier.Euclidean, Feec.Fourier.FibreReducing, Feec.Fourier.GradCurlSymbol, Feec.Fourier.Reality, Feec.Fourier.Weak, Feec.HilbertComplex.Equivariant, Feec.HilbertComplex.Reducing, Feec.HilbertComplex.Transport, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.BoundedDomain.Basic, Feec.Legacy.BoundedDomain.Density, Feec.Legacy.BoundedDomain.Ext, Feec.Legacy.BoundedDomain.Interior, Feec.Legacy.BoundedDomain.Kstar, Feec.Legacy.BoundedDomain.Salvage, Feec.Legacy.BoundedDomain.SalvageDim, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.Box.Basic, Feec.Legacy.Box.Forward, Feec.Legacy.Box.Mirror, Feec.Legacy.Box.Reduce, Feec.Legacy.Box.RowWise, Feec.Legacy.Box.Static, Feec.Legacy.Constraints, Feec.Legacy.MirrorCube.Compress, Feec.Legacy.MirrorCube.Cube, Feec.Legacy.MirrorCube.Pi, Feec.Legacy.Torus.Basic, Feec.Legacy.Torus.Group, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution, Feec.Legacy.Whole.Basic, Feec.Legacy.Whole.Ident, Feec.Models.BoundedDomain.Density, Feec.Models.BoundedDomain.GradCurl, Feec.Models.Cube.Basic, Feec.Models.Cube.Ident, Feec.Models.Cube.Mirror, Feec.Models.Cube.MirrorBGG, Feec.Models.Cube.MirrorDirichlet, Feec.Models.Cube.Parity, Feec.Models.Cube.Reflection, Feec.Models.Cube.Static, Feec.Models.Euclidean.GradCurl, Feec.Models.Torus.GradCurl, Feec.Physics.EinsteinBianchi.Constraints, Feec.Semigroup.Spectral

### Prop 4.18

- named: `Feec.Legacy.BoundedSym.symComplexB_existsUnique_reducedSolution`, `Feec.Legacy.Constraints.existsUnique_reducedSolution`, `Feec.Legacy.Constraints.isStrongSolution_of_isReducedSolution`, `Feec.Legacy.Constraints.reducedSolution_of_wellPosedHom`, `Feec.ShortHilbertComplex.divFree_propagates_neg`
- old: Feec.BoundedSym.symComplexB_prop_4_18, Feec.Constraints.prop_4_18, Feec.Constraints.prop_4_18_i, Feec.Constraints.prop_4_18_ii, Feec.Constraints.prop_4_18_unconditional
- tagged: `Feec.TimeStepping.IsCNStep.mem_of_isReducing`, `Feec.TimeStepping.mem_of_forall_isCNStep`
- cited: `Feec.Legacy.BoundedSym.symComplexB_existsUnique_reducedSolution`, `Feec.Legacy.Constraints.existsUnique_reducedSolution`, `Feec.Legacy.Constraints.isStrongSolution_of_isReducedSolution`, `Feec.Legacy.Constraints.reducedSolution_divFree`, `Feec.Legacy.Constraints.reducedSolution_of_wellPosedHom`, `Feec.Legacy.Constraints.reduced_mem_ker`, `Feec.Legacy.Constraints.reduced_unique`, `Feec.Legacy.CrankNicolson.red_to_full`, `Feec.Legacy.CrankNicolson.red_to_full_necessary`
- modules: Feec.Legacy.BoundedDomain.Interior, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.Constraints, Feec.Legacy.CrankNicolson, Feec.Legacy.WaveGroup, Feec.TimeStepping.Cayley

### Prop 4.19

- named: `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.Legacy.BoundedSym.symComplexB_Kmax_eq`, `Feec.Legacy.BoundedSym.symComplexD_Kmax_eq`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memQ`, `Feec.Models.Cube.MirrorSym.propagates`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Euclidean.SymCurl.tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.SymCurl.waveGroup_mem`, `Feec.Models.Torus.SymCurl.real_tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_propagates_neg`, `Feec.Models.Torus.SymCurl.waveGroup_mem`
- old: Feec.BoundedSym.symComplexB_prop_4_19_max, Feec.BoundedSym.symComplexD_prop_4_19_max, Feec.Box.mirror_prop_4_19, Feec.Box.mirror_prop_4_19_exists, Feec.Repair.C417.mirrorSymCxCube_prop_4_19_exists, Feec.Repair.C417.mirrorSymCxQ_prop_4_19_exists, Feec.Repair.C417.prop_4_19_corrected, Feec.Repair.C417.prop_4_19_corrected_cube, Feec.TorusSym.prop_4_19_torus, Feec.TorusSym.prop_4_19_torus_exists, Feec.TorusSym.prop_4_19_torus_exists_real, Feec.TorusSym.prop_4_19_torus_group, Feec.TorusSym.prop_4_19_torus_iff, Feec.TorusSym.prop_4_19_torus_real_space, Feec.TorusSym.prop_4_19_torus_symGroup, Feec.WholeSym.prop_4_19_whole, Feec.WholeSym.prop_4_19_whole_exists, Feec.WholeSym.prop_4_19_whole_group
- tagged: `Feec.Counterexamples.BoundedSymTSD.exists_projTSD_not_mem_domain`, `Feec.Counterexamples.BoundedSymTSD.not_dense_tsdS_inter`, `Feec.Counterexamples.BoundedSymTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedSymTSD.tsd_not_propagates`, `Feec.Fourier.FibreReducing.existsUnique_mem`, `Feec.Fourier.FibreReducing.propagates`, `Feec.Fourier.SymCurl.isFibreReducing`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.Models.BoundedDomain.hessCurl`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memQ`, `Feec.Models.Cube.MirrorSym.exists_nonstationaryCube`, `Feec.Models.Cube.MirrorSym.exists_nonstationaryQ`, `Feec.Models.Cube.MirrorSym.invariantCore_eq`, `Feec.Models.Cube.MirrorSym.invariantCore_eqCube`, `Feec.Models.Cube.MirrorSym.invariantCore_eqQ`, `Feec.Models.Cube.MirrorSym.propagates`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Cube.MirrorSym.propagatesQ`, `Feec.Models.Cube.MirrorSym.reducingSubcomplex`, `Feec.Models.Cube.MirrorSym.reducingSubcomplexCube`, `Feec.Models.Cube.MirrorSym.reducingSubcomplexQ`, `Feec.Models.Cube.reducingSubcomplex_tsd_torusSym`, `Feec.Models.Euclidean.SymCurl.real_tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.real_tsd_propagates`, `Feec.Models.Euclidean.SymCurl.reducingSubcomplex`, `Feec.Models.Euclidean.SymCurl.tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.tsd_propagates`, `Feec.Models.Euclidean.SymCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.SymCurl.waveGroup_mem`, `Feec.Models.Torus.SymCurl.real_tsd_existsUnique`, `Feec.Models.Torus.SymCurl.real_tsd_propagates`, `Feec.Models.Torus.SymCurl.reducingSubcomplex`, `Feec.Models.Torus.SymCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_propagates`, `Feec.Models.Torus.SymCurl.tsd_propagates_neg`, `Feec.Models.Torus.SymCurl.waveGroup_mem`
- cited: `Feec.Counterexamples.BallSymTSD.not_propagates`, `Feec.Legacy.BoundedDomain.not_propagate_of_adjoint`, `Feec.Legacy.BoundedSym.adjoint_curlS_mem_TSDS`, `Feec.Legacy.BoundedSym.curlS_mem_TSDT`, `Feec.Legacy.BoundedSym.not_finiteDimensional_obstrS`, `Feec.Legacy.BoundedSym.not_projection_hyp_adjoint_curlS`, `Feec.Legacy.BoundedSym.symComplexB_Kmax_eq`, `Feec.Legacy.BoundedSym.symComplexB_diagnosis`, `Feec.Legacy.BoundedSym.symComplexB_mem_TSD0_of_propagate`, `Feec.Legacy.BoundedSym.symComplexB_not_projection_hyp`, `Feec.Legacy.BoundedSym.symComplexB_not_projection_hyp2`, `Feec.Legacy.BoundedSym.symComplexB_not_propagate`, `Feec.Legacy.BoundedSym.symComplexB_tsd_not_propagates`, `Feec.Legacy.BoundedSym.symComplexD_diagnosis`, `Feec.Legacy.BoundedSym.symComplexD_not_projection_hyp`, `Feec.Legacy.Constraints.Kc_propagates`, `Feec.Legacy.Constraints.Kc_propagates_iff`, `Feec.Legacy.Constraints.Kmax_propagates`, `Feec.Legacy.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Legacy.Constraints.projKc_mem_domL_of_Kc_propagates`, `Feec.Legacy.Constraints.propagates_iff_projKc_mem_domL`, `Feec.Legacy.TorusSym.projKc_mem_domL`, `Feec.Models.Torus.SymCurl.tsd_propagates`
- modules: Feec.Algebra.MatrixSymbol, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Fourier.Euclidean, Feec.Fourier.FibreReducing, Feec.Fourier.SymCurlSymbol, Feec.HilbertComplex.Reducing, Feec.Legacy.BoundedDomain.Kstar, Feec.Legacy.BoundedDomain.Salvage, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.BoundedDomain.SymExt, Feec.Legacy.Box.Mirror, Feec.Legacy.Box.Reduce, Feec.Legacy.Constraints, Feec.Legacy.MirrorCube.SymCube, Feec.Legacy.MirrorCube.SymPi, Feec.Legacy.Torus.Sym, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution, Feec.Models.BoundedDomain.SymCurl, Feec.Models.Cube.MirrorSym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Prop 5.1

- named: `Feec.BGG.Hilb.isClosed_closedRange_exact`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Hilb.toHilbertComplex_closedRangeAt_one`, `Feec.BGG.Hilb.toHilbertComplex_cycles_one`, `Feec.BGG.Hilb.toShort_closedRange_exact`
- old: Feec.Ch5.BGG.BGGHilb.prop_5_1
- tagged: `Feec.BGG.Hilb.isClosed_closedRange_exact`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Hilb.toHilbertComplex_closedRangeAt_one`, `Feec.BGG.Hilb.toHilbertComplex_closedRangeAt_two`, `Feec.BGG.Hilb.toHilbertComplex_cycles_one`, `Feec.BGG.Hilb.toHilbertComplex_cycles_zero`, `Feec.BGG.Hilb.toShort`, `Feec.BGG.Hilb.toShort_closedRange_exact`, `Feec.BGG.Segment.D1_D0`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.range_D0`, `Feec.BGG.Segment.range_D1`, `Feec.BGG.isClosed_range_prod`
- cited: `Feec.BGG.Hilb.D0op_isClosed`, `Feec.BGG.Hilb.D1op_isClosed`, `Feec.BGG.Hilb.D1op_isClosed_range`, `Feec.BGG.Hilb.Hyps`, `Feec.BGG.Hilb.exact_D0op_D1op`, `Feec.BGG.Hilb.isClosed_closedRange_exact`, `Feec.BGG.Hilb.isClosed_range_T`, `Feec.BGG.Hilb.isClosed_Γ`, `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Hilb.toShort`, `Feec.BGG.Hilb.toShort_closedRange_exact`, `Feec.BGG.Segment.range_D0`, `Feec.BGG.Stability`, `Feec.BGG.isClosed_range_prod`
- modules: Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.ToComplex, Feec.Legacy.BoundedDomain.BGG

### Prop 5.2

- named: `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.saddle_wellPosed`
- old: Feec.Ch5.BGG.BGGHilb.prop_5_2, Feec.Ch5.BGG.BGGHilb.prop_5_2_wellPosed
- tagged: `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.infSup_a`, `Feec.BGG.Hilb.nondeg_a`, `Feec.BGG.Hilb.saddle_wellPosed`
- cited: `Feec.BGG.Hilb.Wcheck`, `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.hodge_Vt1`, `Feec.BGG.Hilb.infSup_a`, `Feec.BGG.Hilb.infSup_b`, `Feec.BGG.Hilb.jW_spec`, `Feec.BGG.Hilb.nondeg_a`, `Feec.BGG.Hilb.saddle_wellPosed`, `Feec.BGG.Hilb.tripleNorm_definite`, `Feec.BGG.Hilb.tripleNorm_spec`
- modules: Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.BGG.WeakSymmetry

### Prop 5.3

- named: `Feec.BGG.Discrete.poincare_Zh`, `Feec.BGG.Discrete.poincare_Γh`
- old: Feec.Ch5.Discrete.Disc.prop_5_3_a, Feec.Ch5.Discrete.Disc.prop_5_3_b
- tagged: `Feec.BGG.Discrete.poincare_Zh`, `Feec.BGG.Discrete.poincare_Γh`
- cited: `Feec.BGG.Discrete.exact_bot_h`, `Feec.BGG.Discrete.exact_top_h`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.poincare_Zh`, `Feec.BGG.Discrete.poincare_Γh`, `Feec.BGG.Discrete.preimage_bound`, `Feec.BGG.Stability`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`
- modules: Feec.Counterexamples.DiscreteBGG, Feec.HilbertComplex.BGG.Discrete

### Prop 5.4

- named: `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.BGG.eq_zero_of_mixed_homogeneous`, `Feec.BGG.existsUnique_isMixedSolution`, `Feec.BGG.exists_mixed_homogeneous_of_perp`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`
- old: Feec.Ch5.Discrete.Disc.prop_5_4, Feec.Ch5.Discrete.prop54_counterexample_noTopExact, Feec.Ch5.Discrete.prop54_existsUnique, Feec.Ch5.Discrete.prop54_hB_necessary, Feec.Ch5.Discrete.prop54_unique
- tagged: `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.BGG.eq_zero_of_mixed_homogeneous`, `Feec.BGG.existsUnique_isMixedSolution`
- cited: `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.exists_sub_S0h_eq`, `Feec.BGG.Discrete.hodge_h`, `Feec.BGG.eq_zero_of_mixed_homogeneous`, `Feec.BGG.existsUnique_isMixedSolution`, `Feec.BGG.exists_mixed_homogeneous_of_perp`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`
- modules: Feec.Counterexamples.DiscreteBGG, Feec.HilbertComplex.BGG.Discrete

### Thm 5.5

- named: `Feec.BGG.Discrete.errorEstimate_absorb`, `Feec.BGG.Discrete.errorEstimate_final`, `Feec.BGG.Discrete.error_estimate`, `Feec.BGG.mixed_coercivity_eq`
- old: Feec.Ch5.Discrete.Disc.thm55_absorb_real, Feec.Ch5.Discrete.Disc.thm55_final_real, Feec.Ch5.Discrete.Disc.thm_5_5, Feec.Ch5.Discrete.thm55_lhs_identity
- tagged: `Feec.BGG.Discrete.error_estimate`
- cited: `Feec.BGG.Discrete.errorConst`, `Feec.BGG.Discrete.error_estimate`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.hodge_h`, `Feec.BGG.mixed_coercivity_eq`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection`
- modules: Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent

### Prop 5.6

- named: `Feec.BGG.mixed_error_eq`
- old: Feec.Ch5.Discrete.prop_5_6
- tagged: `Feec.BGG.mixed_error_eq`
- cited: `Feec.BGG.Discrete.error_estimate`, `Feec.BGG.errorEq_a`, `Feec.BGG.mixed_error_eq`
- modules: Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent

### Prop 5.7

- tagged: `Feec.FiniteElement.comp_eq_of_dof`, `Feec.FiniteElement.interp_comp_eq`
- cited: `Feec.BGG.Discrete.Compatible`, `Feec.FiniteElement.comp_eq_of_dof`, `Feec.FiniteElement.comp_eq_of_mem_span`, `Feec.FiniteElement.dof_vanish_of_mem_span`, `Feec.FiniteElement.interp_comp_eq`
- modules: Feec.FiniteElement.Dof, Feec.HilbertComplex.BGG.Discrete

### Prop 6.1

- named: `Feec.BGG.WaveData.Solution.exists_multiplierSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_isClosed_range`
- old: Feec.Ch6.ContData.prop_6_1_i, Feec.Ch6.ContData.prop_6_1_i_closedRange, Feec.Ch6.ContData.prop_6_1_ii
- tagged: `Feec.BGG.WaveData.MultiplierSolution.toSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution`
- cited: `Feec.BGG.WaveData.MultiplierSolution.toSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.BGG.WaveData.mem_Wcheck_of_vanish`
- modules: Feec.HilbertComplex.BGG.TimeDependent

### Prop 6.2

- named: `Feec.BGG.DiscreteSolution.compatible`, `Feec.BGG.exists_discreteSolution`, `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_of_continuousOn`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`
- old: Feec.Ch6.prop_6_2, Feec.Ch6.prop_6_2_exists, Feec.Ch6.prop_6_2_exists_of_continuousOn, Feec.Ch6.prop_6_2_exists_regular, Feec.Ch6.prop_6_2_false, Feec.Ch6.prop_6_2_necessary, Feec.Repair.C67.prop_6_2_dynamic, Feec.Repair.C67.prop_6_2_wellposed
- tagged: `Feec.BGG.DiscreteSolution.compatible`, `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`
- cited: `Feec.BGG.DiscreteSolution.compatible`, `Feec.BGG.DiscreteSolution.eq_zero_of_initial_eq_zero`, `Feec.BGG.DiscreteSolution.phi_eq`, `Feec.BGG.DiscreteSolution.phi_zero`, `Feec.BGG.DiscreteSolution.unique`, `Feec.BGG.exists_discreteSolution`, `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.BGG.not_exists_discreteSolution_of_ker`, `Feec.BGG.not_exists_discreteSolution_phi_of_ker`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`
- modules: Feec.Counterexamples.ConstrainedEvolution, Feec.HilbertComplex.BGG.TimeDependent

### Prop 6.3

- named: `Feec.BGG.errorEq_a`, `Feec.BGG.errorEq_b`, `Feec.BGG.errorEq_c`, `Feec.BGG.errorEq_c_split`, `Feec.BGG.errorEq_d`, `Feec.BGG.errorEq_e`
- old: Feec.Ch6.prop_6_3_a, Feec.Ch6.prop_6_3_b, Feec.Ch6.prop_6_3_c, Feec.Ch6.prop_6_3_c_split, Feec.Ch6.prop_6_3_d, Feec.Ch6.prop_6_3_e
- tagged: `Feec.BGG.errorEq_a`, `Feec.BGG.errorEq_e`
- cited: `Feec.BGG.errorEq_a`, `Feec.BGG.errorEq_b`, `Feec.BGG.errorEq_c`, `Feec.BGG.errorEq_c_split`, `Feec.BGG.errorEq_d`, `Feec.BGG.errorEq_e`
- modules: Feec.HilbertComplex.BGG.TimeDependent

## Equations, sections and chapters

### Eq (2.2)

- tagged: `Feec.CurvatureTensor.riemComp`, `Feec.CurvatureTensor.riemField`
- modules: Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Connection

### Eq (2.3)

- tagged: `Feec.CurvatureTensor.deviation`, `Feec.CurvatureTensor.deviationForm`, `Feec.CurvatureTensor.deviation_eq_zero_iff`, `Feec.CurvatureTensor.eq_zero_of_deviationForm`, `Feec.CurvatureTensor.eq_zero_of_symm_bd`
- modules: Feec.Geometry.AlgebraicCurvature

### Eq (2.4)

- modules: Feec.Geometry.AlgebraicCurvature

### Eq (2.5)

- tagged: `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`, `Feec.Metric.eq_trRev_sub`, `Feec.Metric.trRev`, `Feec.Metric.trRev_add_sym`, `Feec.Metric.trRev_trRev`, `Feec.Metric.trace_trRev`
- modules: Feec.Algebra.Metric, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.6)

- tagged: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.Rjet`, `Feec.LinearizedGravity.Rjet_bianchi1`, `Feec.LinearizedGravity.Rjet_pairSkew`
- modules: Feec.Physics.LinearizedGravity.Einstein

### Eq (2.7)

- tagged: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.RicJ`
- modules: Feec.Physics.LinearizedGravity.Einstein

### Eq (2.8)

- tagged: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.scalJ`
- modules: Feec.Physics.LinearizedGravity.Einstein

### Eq (2.9)

- modules: Feec.Physics.LinearizedGravity.Einstein

### Eq (2.10)

- modules: Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Eq (2.11)

- tagged: `Feec.LinearizedGravity.Hfun_lorentz_eq_iff`, `Feec.LinearizedGravity.Hjet_lorentz_eq_iff`
- modules: Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Eq (2.12)

- tagged: `Feec.TT.ttSub`
- cited: `Feec.LinearizedGravity.IsTT`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.mem_ttSpace_iff`
- modules: Feec.Algebra.TransverseTraceless, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.13)

- cited: `Feec.LinearizedGravity.finrank_ttSpace`, `Feec.LinearizedGravity.finrank_ttSub`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.mem_ttSpace_iff`
- modules: Feec.Algebra.TransverseTraceless, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.14)

- modules: Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.15)

- tagged: `Feec.Counterexamples.LinearizedGravity.not_accel_printed`, `Feec.LinearizedGravity.tt_accel_fun`
- cited: `Feec.LinearizedGravity.Rjet_tt`, `Feec.LinearizedGravity.Rjet_ttWave`, `Feec.LinearizedGravity.Rjet_tt_support`, `Feec.LinearizedGravity.tt_accel`
- modules: Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (3.2)

- cited: `Feec.DoubleForm.weyl_reconstruct`, `Feec.DoubleForm.weyl_reconstruct_unit`
- modules: Feec.Geometry.WeylDecomposition

### Eq (4.1)

- tagged: `Feec.HilbertComplex.orthogonal_boundaries`, `Feec.HilbertComplex.orthogonal_cycles`
- cited: `Feec.Legacy.Constraints.ker_adj0_eq`, `Feec.Legacy.Constraints.ker_adj1_eq`, `Feec.Legacy.orth_range_eq_ker_adjoint`, `Feec.Legacy.orthogonal_range_adjoint`
- modules: Feec.ForMathlib.LinearPMap.ClosedRange, Feec.HilbertComplex.Hodge, Feec.Legacy.Adjoint, Feec.Legacy.Constraints, Feec.Legacy.Operators

### Eq (4.2)

- modules: Feec.Fourier.Torus, Feec.Legacy.Torus.Weak

### Eq (4.4)

- cited: `Feec.Legacy.HilbertComplex2.neg_waveOp_isSkewAdjoint`, `Feec.Legacy.IsSkewAdjoint.neg`
- modules: Feec.HilbertComplex.HodgeWave, Feec.Legacy.HodgeWave

### Eq (4.5)

- tagged: `Feec.HilbertComplex.wave`, `Feec.ShortHilbertComplex.wave`
- cited: `Feec.Legacy.Constraints.tot_waveOp`, `Feec.Legacy.HilbertComplex2.dense_domL`, `Feec.Legacy.HilbertComplex2.domL`, `Feec.Legacy.HilbertComplex2.neg_waveOp_isSkewAdjoint`, `Feec.Legacy.HilbertComplex2.waveGroup`, `Feec.Legacy.HilbertComplex2.waveOp`
- modules: Feec.HilbertComplex.Dirac, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.Short, Feec.Legacy.Constraints, Feec.Legacy.HodgeWave, Feec.Legacy.ShortComplex, Feec.Legacy.Torus.Group, Feec.Legacy.WaveGroup, Feec.Models.Cube.Bridge

### Eq (4.6)

- modules: Feec.HilbertComplex.HodgeWave

### Eq (4.7)

- tagged: `Feec.HilbertComplex.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsWeakSolution`
- cited: `Feec.Legacy.AlgSegment.a`, `Feec.Legacy.AlgSegment.aL`, `Feec.Legacy.HilbertComplex2.IsClassicalWeakSolution`, `Feec.Legacy.HilbertComplex2.IsWeakSolution`, `Feec.Legacy.HilbertComplex2.existsUnique_classicalWeakSolution`, `Feec.Legacy.HilbertComplex2.toAlgSegment`, `Feec.Legacy.HilbertComplex2.weak_identity_neg`
- modules: Feec.HilbertComplex.HodgeWave, Feec.Legacy.ErrorEstimate, Feec.Legacy.ErrorEstimateDomain, Feec.Legacy.HodgeWave, Feec.Legacy.ShortComplex, Feec.Legacy.WeakSolution

### Eq (4.8)

- tagged: `Feec.HilbertComplex.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsWeakSolution.unique`
- cited: `Feec.Legacy.AlgSegment.IsWeakSol`, `Feec.Legacy.AlgSegment.a`, `Feec.Legacy.HilbertComplex2.IsClassicalWeakSolution`, `Feec.Legacy.HilbertComplex2.IsWeakSolution`, `Feec.Legacy.HilbertComplex2.a_self`, `Feec.Legacy.HilbertComplex2.existsUnique_classicalWeakSolution`, `Feec.Legacy.HilbertComplex2.weak_identity_neg`, `Feec.Legacy.HilbertComplex2.weak_unique`
- modules: Feec.HilbertComplex.HodgeWave, Feec.Legacy.ErrorEstimate, Feec.Legacy.ErrorEstimateDomain, Feec.Legacy.HodgeWave, Feec.Legacy.ShortComplex, Feec.Legacy.WeakSolution

### Eq (4.10)

- cited: `Feec.Legacy.AlgSegment.IsDiscreteSol`, `Feec.Legacy.AlgSegment.semidiscreteOp`
- modules: Feec.HilbertComplex.Approximation.SemidiscreteWave, Feec.Legacy.ErrorEstimate

### Eq (4.11)

- tagged: `Feec.HodgeWave.ellipticProjection`, `Feec.HodgeWave.shiftedForm_ellipticProjection`
- cited: `Feec.Legacy.AlgSegment.ellProj`, `Feec.Legacy.AlgSegment.ellProj_existsUnique`
- modules: Feec.HilbertComplex.Approximation.SemidiscreteWave, Feec.Legacy.ErrorEstimate

### Eq (4.12)

- cited: `Feec.Legacy.Constraints.IsMixedWeak3`
- modules: Feec.Legacy.Constraints

### Eq (4.14)

- cited: `Feec.Legacy.Constraints.revT`, `Feec.Legacy.Constraints.waveOp_revT`, `Feec.Legacy.CrankNicolson.FullStep`, `Feec.Legacy.CrankNicolson.cn_invertible`
- modules: Feec.Fourier.GradCurlSymbol, Feec.Legacy.BoundedDomain.Basic, Feec.Legacy.BoundedDomain.Ext, Feec.Legacy.BoundedDomain.Interior, Feec.Legacy.BoundedDomain.Salvage, Feec.Legacy.Box.Basic, Feec.Legacy.Constraints, Feec.Legacy.CrankNicolson, Feec.Legacy.MirrorCube.Cube, Feec.Legacy.Torus.Basic, Feec.Legacy.Torus.Group, Feec.Legacy.Whole.Basic, Feec.Models.Euclidean.GradCurl, Feec.Models.Torus.GradCurl

### Eq (4.15)

- cited: `Feec.Legacy.Constraints.IsReducedSolution`, `Feec.Legacy.CrankNicolson.RedStep`, `Feec.Models.Torus.BGG.verdict`
- modules: Feec.Legacy.Constraints, Feec.Legacy.CrankNicolson, Feec.Legacy.MirrorCube.Cube, Feec.Legacy.Torus.Basic, Feec.Legacy.Whole.Basic, Feec.Models.Torus.BGG, Feec.Models.Torus.GradCurl

### Eq (4.16)

- cited: `Feec.Legacy.TorusSym.curlSym_mem_trSub`, `Feec.Legacy.TorusSym.symComplex`, `Feec.Models.Torus.SymCurl.closedRangeAt`, `Feec.Models.Torus.SymCurl.complex`
- modules: Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Fourier.SymCurlSymbol, Feec.Fourier.Torus, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.Box.Mirror, Feec.Legacy.MirrorCube.SymCube, Feec.Legacy.Torus.Sym, Feec.Models.BoundedDomain.SymCurl, Feec.Models.Cube.MirrorSym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Eq (4.17)

- cited: `Feec.Legacy.TorusSym.adjoint_curlS`, `Feec.Legacy.TorusSym.adjoint_hessS`, `Feec.Models.Torus.SymCurl.adjoint_d`, `Feec.Models.Torus.SymCurl.closedRangeAt`, `Feec.Models.Torus.SymCurl.dual_closedRangeAt`
- modules: Feec.Counterexamples.BallSymTSD, Feec.Fourier.SymCurlSymbol, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.MirrorCube.SymCube, Feec.Legacy.Torus.Sym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Eq (4.18)

- cited: `Feec.Legacy.TorusSym.symComplex_closedRange`, `Feec.Models.Torus.SymCurl.closedRangeAt`, `Feec.Models.Torus.SymCurl.tsd_propagates`
- modules: Feec.Counterexamples.BallSymTSD, Feec.Fourier.SymCurlSymbol, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.MirrorCube.SymCube, Feec.Legacy.Torus.Sym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Eq (5.1)

- tagged: `Feec.BGG.Hilb.toHilbertComplex`
- cited: `Feec.BGG.Hilb.D0op`, `Feec.BGG.Hilb.D1op`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Segment.D0`, `Feec.BGG.Segment.D1`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.Γ`
- modules: Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.ToComplex, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.MirrorCube.BggTorus, Feec.Legacy.Whole.BGG, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG

### Eq (5.2)

- cited: `Feec.BGG.Hilb.IsReduced`, `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`
- modules: Feec.HilbertComplex.BGG.WeakSymmetry

### Eq (5.3)

- cited: `Feec.BGG.Hilb.IsSaddleW1`, `Feec.BGG.Hilb.aForm`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`
- modules: Feec.HilbertComplex.BGG.WeakSymmetry

### Eq (5.4)

- cited: `Feec.BGG.Discrete.Compatible`, `Feec.BGG.surjective_of_comp_eq`
- modules: Feec.HilbertComplex.BGG.Discrete

### Eq (5.5)

- cited: `Feec.BGG.Discrete.exact_mid_h`, `Feec.BGG.exists_of_exact_rows`
- modules: Feec.HilbertComplex.BGG.Discrete

### Eq (5.6)

- cited: `Feec.BGG.IsMixedSolution`
- modules: Feec.HilbertComplex.BGG.Discrete

### Eq (5.8)

- cited: `Feec.FiniteElement.dof_vanish_of_mem_span`
- modules: Feec.FiniteElement.Dof

### Eq (6.1)

- cited: `Feec.BGG.WaveData.Solution`
- modules: Feec.HilbertComplex.BGG.TimeDependent, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.Whole.BGG

### Eq (6.2)

- cited: `Feec.BGG.WaveData.MultiplierSolution`
- modules: Feec.HilbertComplex.BGG.TimeDependent, Feec.Legacy.BoundedDomain.BGG

### Eq (6.3)

- cited: `Feec.BGG.DiscreteSolution`
- modules: Feec.Counterexamples.ConstrainedEvolution, Feec.HilbertComplex.BGG.TimeDependent

### Eq (6.4)

- cited: `Feec.BGG.exists_discreteSolution_norm_sub_le`
- modules: Feec.HilbertComplex.BGG.TimeDependent

### Sec §2.2

- tagged: `Feec.LinearizedGravity.η4`, `Feec.Metric.minkowski`, `Feec.Metric.minkowski4`, `Feec.Metric.minkowskiMatrix`
- modules: Feec.Algebra.Metric, Feec.Legacy.Tensor, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §2.3

- tagged: `Feec.CurvatureTensor.Interchange`, `Feec.CurvatureTensor.algCurvEquiv`, `Feec.CurvatureTensor.bianchi_iff`, `Feec.CurvatureTensor.deviation_eq_zero_iff`, `Feec.CurvatureTensor.einstein`, `Feec.CurvatureTensor.einstein_isSymm`, `Feec.CurvatureTensor.eq_zero_of_deviationForm`, `Feec.CurvatureTensor.finrank_algCurv_four`, `Feec.CurvatureTensor.interchange_of_bianchi`, `Feec.CurvatureTensor.ricci`, `Feec.CurvatureTensor.ricci_isSymm`, `Feec.CurvatureTensor.ricci_isSymm_of_inv`, `Feec.CurvatureTensor.ricci_riemField_isSymm`
- modules: Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Connection, Feec.Legacy.Tensor

### Sec §2.4

- tagged: `Feec.Counterexamples.Curvature.exists_einstein_eq_zero_ne_zero_two`, `Feec.CurvatureTensor.einstein_eq_zero_iff`, `Feec.LinearizedGravity.einstein_const_bounds`
- modules: Feec.Counterexamples.Curvature, Feec.Geometry.AlgebraicCurvature, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §2.7

- tagged: `Feec.LinearizedGravity.Hfun_bianchi`, `Feec.LinearizedGravity.Hfun_gauge`, `Feec.LinearizedGravity.Hjet_bianchi`, `Feec.LinearizedGravity.Hjet_gauge`, `Feec.LinearizedGravity.Hsym_div`, `Feec.LinearizedGravity.Hsym_gauge`, `Feec.LinearizedGravity.jet2_isSymJet2`, `Feec.Metric.trRev`, `Feec.Metric.trace`
- modules: Feec.Algebra.Metric, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Sec §2.8

- tagged: `Feec.Counterexamples.LinearizedGravity.not_accel_printed`, `Feec.TT.ttProj`, `Feec.TT.ttProj_mem`
- cited: `Feec.LinearizedGravity.IsTT`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.tt_accel`
- modules: Feec.Algebra.TransverseTraceless, Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §3.1

- tagged: `Feec.leviCivita`, `Feec.leviCivita3`, `Feec.leviCivita4`
- cited: `Feec.DoubleForm.hodge2_hodge2`, `Feec.Legacy.eps3`
- modules: Feec.Algebra.LeviCivita, Feec.Geometry.Hodge2, Feec.Legacy.Tensor

### Sec §3.2

- cited: `Feec.DoubleForm.IsWeyl`, `Feec.DoubleForm.finrank_weylSpace`, `Feec.DoubleForm.ldual_eq_rdual`, `Feec.DoubleForm.ldual_eq_rdual_swap`, `Feec.DoubleForm.rdual_rdual`
- modules: Feec.Geometry.Bivector, Feec.Geometry.Hodge2, Feec.Geometry.WeylDecomposition

### Sec §3.3

- modules: Feec.Geometry.Bivector, Feec.Geometry.WeylDecomposition, Feec.Physics.EinsteinBianchi.System

### Sec §3.4

- tagged: `Feec.TT.ttProj`, `Feec.TT.ttProj_mem`, `Feec.TT.ttSub`
- cited: `Feec.EinsteinBianchi.EBJet`, `Feec.EinsteinBianchi.EBJetSym_surjective`, `Feec.EinsteinBianchi.linBianchi_iff_sym`, `Feec.Legacy.BoundedDomain.curl_symm_of_mem_TSD`, `Feec.Legacy.Constraints.curl_TSD`, `Feec.Legacy.Constraints.curl_TSD_div`, `Feec.Legacy.Constraints.div_curl`, `Feec.Legacy.Constraints.trace_curl`, `Feec.Legacy.Constraints.trace_curl_of_symm`, `Feec.Legacy.Constraints.two_vskw_curl`, `Feec.Legacy.Torus.curlR_mem_tsd`, `Feec.Legacy.TorusSym.curlST_mem_L2TSDT`, `Feec.Legacy.TorusSym.curlSym_mem_trSub`, `Feec.Models.Euclidean.GradCurl.fourier_mem_constraint_iff`
- modules: Feec.Algebra.MatrixSymbol, Feec.Algebra.TransverseTraceless, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedDomainTSD, Feec.Fourier.BGGSymbol, Feec.Fourier.GradCurlSymbol, Feec.Fourier.SymCurlSymbol, Feec.Legacy.BoundedDomain.Basic, Feec.Legacy.BoundedDomain.Interior, Feec.Legacy.BoundedDomain.Salvage, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.BoundedDomain.SymExt, Feec.Legacy.Box.Basic, Feec.Legacy.Box.Restrict, Feec.Legacy.Constraints, Feec.Legacy.MirrorCube.BggTorus, Feec.Legacy.Torus.Basic, Feec.Legacy.Torus.Sym, Feec.Legacy.Whole.Basic, Feec.Legacy.Whole.Ident, Feec.Legacy.Whole.Weak, Feec.Models.BoundedDomain.GradCurl, Feec.Models.Euclidean.GradCurl, Feec.Models.Torus.BGG, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.System

### Sec §3.5

- cited: `Feec.EinsteinBianchi.planeWave_EB`, `Feec.EinsteinBianchi.planeWave_weyl`
- modules: Feec.Domain.FiniteSpeed, Feec.Numerics.CrankNicolsonTable, Feec.Physics.EinsteinBianchi.Fields

### Sec §4.1

- cited: `Feec.Legacy.Constraints.isClosed_ker`, `Feec.Legacy.Constraints.ker_adj0_eq`, `Feec.Legacy.Constraints.ker_adj1_eq`, `Feec.Legacy.IsSkewAdjoint`, `Feec.Legacy.IsSkewAdjoint.isSkewSymm`, `Feec.Legacy.IsSkewAdjoint.isSkewSymmetric`, `Feec.Legacy.IsSkewSymm`, `Feec.Legacy.adjoint_adjoint`, `Feec.Legacy.dense_adjoint_domain`, `Feec.Legacy.isSkewAdjoint_iff`, `Feec.Legacy.orth_range_eq_ker_adjoint`
- modules: Feec.ForMathlib.LinearPMap.ClosedRange, Feec.ForMathlib.LinearPMap.GraphSpace, Feec.ForMathlib.LinearPMap.Skew, Feec.Legacy.Adjoint, Feec.Legacy.Constraints, Feec.Legacy.Existence, Feec.Legacy.Operators

### Sec §4.2

- tagged: `Feec.Counterexamples.deRham_not_closedRange`, `Feec.Counterexamples.euclidean_not_closedRange`, `Feec.Counterexamples.fredholm_not_closedRange`, `Feec.Counterexamples.hasCompactProperty_infiniteDimensional`, `Feec.Counterexamples.not_forall_closedRangeAt_of_finiteDimensional_harmonic`, `Feec.Counterexamples.periodic_not_closedRange`, `Feec.HilbertComplex`, `Feec.HilbertComplex.ClosedRangeAt`, `Feec.HilbertComplex.HasCompactProperty`, `Feec.HilbertComplex.HasCompactProperty.isCompactOperator_resolvent_wave`, `Feec.HilbertComplex.HasCompactPropertyAt`, `Feec.HilbertComplex.HasCompactPropertyAt.closedRangeAt`, `Feec.HilbertComplex.HasCompactPropertyAt.closedRangeAt_of_rel`, `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`, `Feec.HilbertComplex.HasCompactPropertyAt.finiteDimensional_harmonic`, `Feec.HilbertComplex.HasCompactPropertyAt.isClosed_range`, `Feec.HilbertComplex.boundaries`, `Feec.HilbertComplex.boundaries_sup_harmonic`, `Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`, `Feec.HilbertComplex.closure_boundaries_sup_harmonic`, `Feec.HilbertComplex.cohomology`, `Feec.HilbertComplex.cohomologyEquivHarmonic`, `Feec.HilbertComplex.cycles`, `Feec.HilbertComplex.domainComplex`, `Feec.HilbertComplex.domainComplex_closedRangeAt_iff`, `Feec.HilbertComplex.domainSpace`, `Feec.HilbertComplex.dual`, `Feec.HilbertComplex.dual_closedRangeAt_iff`, `Feec.HilbertComplex.exact_iff_harmonic_eq_bot`, `Feec.HilbertComplex.harmonic`, `Feec.HilbertComplex.harmonicToCohomology_surjective_iff`, `Feec.HilbertComplex.harmonic_eq`, `Feec.HilbertComplex.map_domainIncl_harmonic`
- cited: `Feec.Legacy.Constraints.range_d0_le_ker_d1`, `Feec.Legacy.DomainComplex`, `Feec.Legacy.DomainComplex.Z`, `Feec.Legacy.HilbertComplex2`, `Feec.Legacy.HilbertComplex2.ClosedRange`, `Feec.Legacy.HilbertComplex2.dual`, `Feec.Legacy.HilbertComplex2.harmonic`, `Feec.Legacy.HilbertComplex2.ofBounded`, `Feec.Legacy.HilbertComplex2.range_adjoint_d1_eq`, `Feec.Legacy.UHilbertComplex`, `Feec.Legacy.isClosed_ker`, `Feec.Legacy.isClosed_range_adjoint_iff`, `Feec.Legacy.range_adjoint_eq_orthogonal_ker`
- modules: Feec.Counterexamples.Fredholm, Feec.Counterexamples.NonClosedRangeEuclidean, Feec.Fourier.ClosedRange, Feec.Fourier.ExteriorSymbol, Feec.HilbertComplex.Basic, Feec.HilbertComplex.Compactness, Feec.HilbertComplex.DomainComplex, Feec.HilbertComplex.Dual, Feec.HilbertComplex.Hodge, Feec.Legacy.Adjoint, Feec.Legacy.BoundedDomain.SymExt, Feec.Legacy.Box.Reduce, Feec.Legacy.Constraints, Feec.Legacy.Hodge, Feec.Legacy.HodgeW, Feec.Legacy.MirrorCube.Compress, Feec.Legacy.Operators, Feec.Legacy.ShortComplex, Feec.Legacy.Torus.Weak, Feec.Models.Euclidean.DeRham, Feec.Models.Torus.DeRham, Feec.Operator.Adjoint

### Sec §4.3

- tagged: `Feec.Counterexamples.exists_dense_not_isClosed_ker`, `Feec.Counterexamples.not_forall_isClosed_ker`
- cited: `Feec.Legacy.isClosed_ker`
- modules: Feec.Counterexamples.Ell2, Feec.Evolution.Constrained, Feec.Evolution.Duhamel, Feec.Evolution.Forcing, Feec.Evolution.Solution, Feec.Evolution.WellPosed, Feec.Examples.NonVacuity, Feec.HilbertComplex.Reducing, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.Constraints, Feec.Legacy.Evolution, Feec.Legacy.Existence, Feec.Legacy.HodgeWave, Feec.Legacy.Operators, Feec.Legacy.Restriction, Feec.Legacy.Stone, Feec.Legacy.Torus.Group, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution, Feec.Legacy.Whole.Basic

### Sec §4.4

- tagged: `Feec.HodgeWave.IsClassicalWeakSolution`, `Feec.HodgeWave.IsWeakSolution.unique`, `Feec.ShortHilbertComplex`
- cited: `Feec.BGG.WaveData.Solution`, `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.Evolution.IsStrongSolution`, `Feec.Legacy.AlgSegment`, `Feec.Legacy.AlgSegment.IsWeakSol`, `Feec.Legacy.AlgSegment.VSp`, `Feec.Legacy.AlgSegment.a`, `Feec.Legacy.AlgSegment.a_self`, `Feec.Legacy.AlgSegment.isWeakSol_unique`, `Feec.Legacy.AlgSegment.normVSq`, `Feec.Legacy.Constraints.tot_waveOp`, `Feec.Legacy.CrankNicolson.full_step_energy`, `Feec.Legacy.CrankNicolson.full_step_unique`, `Feec.Legacy.HilbertComplex2`, `Feec.Legacy.HilbertComplex2.IsClassicalWeakSolution`, `Feec.Legacy.HilbertComplex2.IsWeakSolution`, `Feec.Legacy.HilbertComplex2.Tot`, `Feec.Legacy.HilbertComplex2.a_self`, `Feec.Legacy.HilbertComplex2.convergence_domL_classicalWeak_exists`, `Feec.Legacy.HilbertComplex2.dense_domL`, `Feec.Legacy.HilbertComplex2.domL`, `Feec.Legacy.HilbertComplex2.existsUnique_classicalWeakSolution`, `Feec.Legacy.HilbertComplex2.midDomain`, `Feec.Legacy.HilbertComplex2.neg_waveOp_isSkewAdjoint`, `Feec.Legacy.HilbertComplex2.toAlgSegment`, `Feec.Legacy.HilbertComplex2.toAlgSegment_a`, `Feec.Legacy.HilbertComplex2.waveGroup`, `Feec.Legacy.HilbertComplex2.waveOp`, `Feec.Legacy.HilbertComplex2.weak_unique`, `Feec.Legacy.energy_zero`, `Feec.Legacy.norm_le_norm_zero_of_inner_deriv_nonpos`
- modules: Feec.Counterexamples.ClassicalRegularity, Feec.Evolution.Solution, Feec.Examples.NonVacuity, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.Dirac, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.Short, Feec.HilbertComplex.Window, Feec.Legacy.Constraints, Feec.Legacy.CrankNicolson, Feec.Legacy.ErrorEstimate, Feec.Legacy.ErrorEstimateDomain, Feec.Legacy.Evolution, Feec.Legacy.HodgeWave, Feec.Legacy.ShortComplex, Feec.Legacy.Stone, Feec.Legacy.Torus.Group, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution, Feec.Models.Cube.Bridge

### Sec §4.5

- tagged: `Feec.Variational.InfSup`, `Feec.Variational.SeparatingRight`, `Feec.Variational.infSup_iff_forall_exists_norm_le_one`
- cited: `Feec.Legacy.AlgSegment.AL_self_eq_zero`, `Feec.Legacy.AlgSegment.VSp`
- modules: Feec.Legacy.ErrorEstimate, Feec.Legacy.Galerkin, Feec.Variational.BabuskaNecas, Feec.Variational.InfSup

### Sec §4.6

- tagged: `Feec.HilbertComplex.Subcomplex`, `Feec.HilbertComplex.Subcomplex.toHilbertComplex`
- cited: `Feec.Legacy.AlgSegment`, `Feec.Legacy.AlgSegment.AL`, `Feec.Legacy.AlgSegment.DensityHyp`, `Feec.Legacy.AlgSegment.DensityHyp.ellProj_tendsto`, `Feec.Legacy.AlgSegment.IsDiscreteSol.norm_toW_sub_le`, `Feec.Legacy.AlgSegment.Sub`, `Feec.Legacy.AlgSegment.Sub.toV`, `Feec.Legacy.AlgSegment.VSp`, `Feec.Legacy.AlgSegment.abs_formA_le`, `Feec.Legacy.AlgSegment.convergence`, `Feec.Legacy.AlgSegment.discrete_solution_exists`, `Feec.Legacy.AlgSegment.discrete_solution_unique`, `Feec.Legacy.AlgSegment.discrete_stability`, `Feec.Legacy.AlgSegment.ellProj_quasiopt`, `Feec.Legacy.AlgSegment.formA`, `Feec.Legacy.AlgSegment.formAV`, `Feec.Legacy.AlgSegment.isWeakSol_unique`, `Feec.Legacy.AlgSegment.normVSq`, `Feec.Legacy.AlgSegment.norm_ellProjFun_le`, `Feec.Legacy.AlgSegment.vInner`, `Feec.Legacy.FredholmCE.cxK1Sub_densityHyp`, `Feec.Legacy.HilbertComplex2.convergence_W`, `Feec.Legacy.HilbertComplex2.convergence_domL`, `Feec.Legacy.HilbertComplex2.convergence_domL_classicalWeak_exists`, `Feec.Legacy.HilbertComplex2.convergence_domL_weakSolution`, `Feec.Legacy.HilbertComplex2.exists_isWeakSol_of_waveOp_mem`, `Feec.Legacy.HilbertComplex2.tendstoUniformlyOn_discreteSol`
- modules: Feec.Counterexamples.ClassicalRegularity, Feec.HilbertComplex.Approximation.SemidiscreteWave, Feec.HilbertComplex.Approximation.Subcomplex, Feec.Legacy.ErrorEstimate, Feec.Legacy.ErrorEstimateDomain, Feec.Legacy.ShortComplex, Feec.Legacy.WeakSolution

### Sec §4.7

- tagged: `Feec.Koszul.eq_koszul_add_extDeriv`, `Feec.Koszul.eq_zero_of_eq_koszul_of_eq_extDeriv`, `Feec.Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero`, `Feec.Koszul.exists_koszul_eq_of_koszul_eq_zero`, `Feec.Koszul.extDeriv`, `Feec.Koszul.extDeriv_extDeriv`, `Feec.Koszul.extDeriv_koszul_add_koszul_extDeriv`, `Feec.Koszul.extDeriv_koszul_add_koszul_extDeriv_of_isHomogeneous`, `Feec.Koszul.extDeriv_mem_homForm`, `Feec.Koszul.extDeriv_mem_polyForm`, `Feec.Koszul.extDeriv_mem_polyFormMinus`, `Feec.Koszul.extDeriv_mem_polyForm_of_mem_polyFormMinus`, `Feec.Koszul.homForm`, `Feec.Koszul.homForm_le_sup`, `Feec.Koszul.koszul`, `Feec.Koszul.koszul_koszul`, `Feec.Koszul.koszul_mem_homForm`, `Feec.Koszul.koszul_mem_polyForm`, `Feec.Koszul.polyForm`, `Feec.Koszul.polyFormMinus`, `Feec.Koszul.polyFormMinus_le_polyForm`
- cited: `Feec.Legacy.Constraints.PminusLambda1`, `Feec.Legacy.Constraints.koszul_decomp`, `Feec.Legacy.Constraints.koszul_direct`, `Feec.Legacy.Constraints.koszul_homotopy_core`
- modules: Feec.Algebra.Koszul, Feec.Algebra.PolynomialForm, Feec.Algebra.Proxy3, Feec.Legacy.Constraints

### Sec §4.8

- cited: `Feec.Legacy.Constraints.IsMixedWeak`, `Feec.Legacy.Constraints.IsSecondOrderWeak`, `Feec.Legacy.Constraints.mixed_imp_secondOrder`, `Feec.Legacy.Constraints.secondOrder_imp_mixed`, `Feec.Legacy.Constraints.secondOrder_not_mixed`
- modules: Feec.Legacy.Constraints, Feec.Legacy.HodgeWave

### Sec §4.9

- cited: `Feec.Legacy.Constraints.IsMixedWeak3`, `Feec.Legacy.Constraints.K`, `Feec.Legacy.Constraints.divFree_propagates`, `Feec.Legacy.Constraints.mixed3_eliminate`, `Feec.Legacy.Constraints.mixed3_eliminate_of_reg`
- modules: Feec.HilbertComplex.Reducing, Feec.Legacy.Constraints, Feec.Physics.Maxwell.Constraints

### Sec §4.10

- tagged: `Feec.Counterexamples.PolynomialForms.extDeriv_not_mem_polyFormMinus`, `Feec.Counterexamples.PolynomialForms.grad_sq_not_whitney`, `Feec.Counterexamples.PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus`, `Feec.Koszul.Proxy3.koszul_empty`, `Feec.Koszul.Proxy3.vec1_extDeriv`, `Feec.Koszul.Proxy3.vec1_koszul`, `Feec.Koszul.Proxy3.vec2_extDeriv`, `Feec.Koszul.Proxy3.vec2_koszul`, `Feec.Koszul.Proxy3.vol_extDeriv`, `Feec.Koszul.extDeriv_mem_polyFormMinus`, `Feec.Koszul.polyFormMinus`, `Feec.Models.Cube.Mirror.complex`, `Feec.Models.Cube.Parity.complex`
- cited: `Feec.Legacy.BoundedBGG.bggComplex_verdict`, `Feec.Legacy.BoundedDomain.HcurlM_not_projection`, `Feec.Legacy.BoundedDomain.HcurlM_not_projection_bochner`, `Feec.Legacy.BoundedDomain.adjoint_mem_TSD0_of_propagate`, `Feec.Legacy.BoundedDomain.closure_TSD_inter_HcurlZero_subset`, `Feec.Legacy.BoundedDomain.dense_HcurlM_inter_HdivZero`, `Feec.Legacy.BoundedDomain.dense_domain_d1_inter_ker_adj0`, `Feec.Legacy.BoundedDomain.density_dichotomy`, `Feec.Legacy.BoundedDomain.density_gap`, `Feec.Legacy.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.Legacy.BoundedDomain.exists_data_not_propagate`, `Feec.Legacy.BoundedDomain.exists_orbit_not_propagate`, `Feec.Legacy.BoundedDomain.exists_projTSD_not_mem_HcurlZero`, `Feec.Legacy.BoundedDomain.exists_tsd_not_propagates`, `Feec.Legacy.BoundedDomain.integral_eq_zero_bochner`, `Feec.Legacy.BoundedDomain.integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`, `Feec.Legacy.BoundedDomain.not_dense_TSD_inter_HcurlZero`, `Feec.Legacy.BoundedDomain.not_dense_domL_inter_Kc`, `Feec.Legacy.BoundedDomain.not_finiteDimensional_obstr`, `Feec.Legacy.BoundedDomain.not_finiteDimensional_orth_closure_TSD_inter_HcurlZero`, `Feec.Legacy.BoundedDomain.not_projection_hyp`, `Feec.Legacy.BoundedDomain.not_projection_hyp_S2`, `Feec.Legacy.BoundedDomain.not_projection_hyp_adjoint`, `Feec.Legacy.BoundedDomain.not_propagate_of_adjoint`, `Feec.Legacy.BoundedDomain.projTSD_not_mem_HcurlZero`, `Feec.Legacy.BoundedDomain.projection_unbounded`, `Feec.Legacy.BoundedDomain.starProjection_grad`, `Feec.Legacy.BoundedDomain.sum_integral_mul_pd_eq_zero`, `Feec.Legacy.BoundedDomain.thesisComplex_Kmax_eq`, `Feec.Legacy.BoundedDomain.thesisComplex_adjoint_mem_TSD0`, `Feec.Legacy.BoundedDomain.thesisComplex_beta_violation_boundary_layer`, `Feec.Legacy.BoundedDomain.thesisComplex_dense_literal`, `Feec.Legacy.BoundedDomain.thesisComplex_not_projection_hyp`, `Feec.Legacy.BoundedDomain.thesisComplex_not_projection_hyp2`, `Feec.Legacy.BoundedDomain.thesisComplex_not_propagate`, `Feec.Legacy.BoundedDomain.thesisComplex_orbit_not_propagate`, `Feec.Legacy.BoundedDomain.thesisComplex_tsd_not_propagates`, `Feec.Legacy.BoundedDomain.thesisComplex_violation_boundary_layer`, `Feec.Legacy.BoundedSym.symComplexB_divFree_propagates`, `Feec.Legacy.BoundedSym.symComplexB_existsUnique_reducedSolution`, `Feec.Legacy.Box.mem_Kmax_boxTSD_iff`, `Feec.Legacy.Box.offB_mem_Kmax`, `Feec.Legacy.Box.thesisBox_mem_Kmax_iff`, `Feec.Legacy.Constraints.IsReducedSolution`, `Feec.Legacy.Constraints.Kc_propagates`, `Feec.Legacy.Constraints.Kmax_propagates`, `Feec.Legacy.Constraints.existsUnique_Kmax`, `Feec.Legacy.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Legacy.Constraints.isStrongSolution_of_isReducedSolution`, `Feec.Legacy.Constraints.pgrad_mem_PminusLambda1`, `Feec.Legacy.Constraints.pgrad_not_mem_PminusLambda1`, `Feec.Legacy.Constraints.reducedSolution_divFree`, `Feec.Legacy.Constraints.reducedSolution_of_wellPosedHom`, `Feec.Legacy.Constraints.reduced_mem_ker`, `Feec.Legacy.Constraints.reduced_unique`, `Feec.Legacy.Constraints.revT`, `Feec.Legacy.Constraints.waveOp_revT`, `Feec.Legacy.CrankNicolson.FullStep`, `Feec.Legacy.CrankNicolson.RedStep`, `Feec.Legacy.CrankNicolson.cn_invertible`, `Feec.Legacy.Torus.projKc_mem_domL`, `Feec.Legacy.Whole.projKc_mem_domL`, `Feec.Legacy.Whole.whole_Kc_propagates`, `Feec.Models.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.Models.Cube.MirrorTorus.existsUnique_mem`, `Feec.Models.Cube.MirrorTorus.propagates`, `Feec.Models.Euclidean.GradCurl.fourier_mem_constraint_iff`, `Feec.Models.Torus.BGG.verdict`
- modules: Feec.Algebra.MatrixSymbol, Feec.Algebra.PolynomialForm, Feec.Algebra.Proxy3, Feec.Counterexamples.BoundedDomainTSD, Feec.Counterexamples.CubeStationary, Feec.Counterexamples.NonClosedRangeEuclidean, Feec.Counterexamples.PolynomialForms, Feec.Domain.Affine, Feec.Domain.ConstCoeffOp, Feec.Domain.FiniteSpeed, Feec.Domain.Mollify, Feec.Domain.Obstruction, Feec.Fourier.Euclidean, Feec.Fourier.FibreReducing, Feec.Fourier.GradCurlSymbol, Feec.Fourier.Reality, Feec.Fourier.SymbolComplex, Feec.Fourier.Torus, Feec.Fourier.TorusWeak, Feec.Fourier.Weak, Feec.HilbertComplex.Equivariant, Feec.HilbertComplex.Reality, Feec.HilbertComplex.Reducing, Feec.HilbertComplex.RestrictScalars, Feec.HilbertComplex.Transport, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.BoundedDomain.Basic, Feec.Legacy.BoundedDomain.Density, Feec.Legacy.BoundedDomain.Ext, Feec.Legacy.BoundedDomain.Interior, Feec.Legacy.BoundedDomain.Kstar, Feec.Legacy.BoundedDomain.Salvage, Feec.Legacy.BoundedDomain.SalvageDim, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.BoundedDomain.SymExt, Feec.Legacy.Box.Basic, Feec.Legacy.Box.Forward, Feec.Legacy.Box.Ident, Feec.Legacy.Box.Mirror, Feec.Legacy.Box.Reduce, Feec.Legacy.Box.Restrict, Feec.Legacy.Box.RowWise, Feec.Legacy.Box.Static, Feec.Legacy.Constraints, Feec.Legacy.CrankNicolson, Feec.Legacy.MirrorCube.Compress, Feec.Legacy.MirrorCube.Cube, Feec.Legacy.MirrorCube.CubeDense, Feec.Legacy.MirrorCube.Ext, Feec.Legacy.MirrorCube.Pi, Feec.Legacy.PolynomialSubcomplex, Feec.Legacy.Torus.Basic, Feec.Legacy.Torus.Group, Feec.Legacy.Torus.Sym, Feec.Legacy.Torus.Weak, Feec.Legacy.WaveGroup, Feec.Legacy.WeakSolution, Feec.Legacy.Whole.Basic, Feec.Legacy.Whole.Ident, Feec.Legacy.Whole.Mul, Feec.Legacy.Whole.Weak, Feec.Models.BoundedDomain.Density, Feec.Models.BoundedDomain.GradCurl, Feec.Models.Cube.Basic, Feec.Models.Cube.Ident, Feec.Models.Cube.Mirror, Feec.Models.Cube.MirrorDirichlet, Feec.Models.Cube.Parity, Feec.Models.Cube.Reflection, Feec.Models.Cube.Static, Feec.Models.Euclidean.GradCurl, Feec.Models.Torus.BGG, Feec.Models.Torus.GradCurl, Feec.Physics.EinsteinBianchi.Constraints, Feec.Semigroup.Spectral

### Sec §4.11

- tagged: `Feec.Models.Cube.MirrorSym.complex`
- cited: `Feec.Counterexamples.BallSymTSD.not_propagates`, `Feec.Legacy.BoundedBGG.bggComplex_verdict`, `Feec.Legacy.BoundedDomain.not_propagate_of_adjoint`, `Feec.Legacy.BoundedSym.adjoint_curlS_mem_TSDS`, `Feec.Legacy.BoundedSym.curlS_mem_TSDT`, `Feec.Legacy.BoundedSym.not_finiteDimensional_obstrS`, `Feec.Legacy.BoundedSym.not_projection_hyp_adjoint_curlS`, `Feec.Legacy.BoundedSym.symComplexB_Kmax_eq`, `Feec.Legacy.BoundedSym.symComplexB_diagnosis`, `Feec.Legacy.BoundedSym.symComplexB_divFree_propagates`, `Feec.Legacy.BoundedSym.symComplexB_mem_TSD0_of_propagate`, `Feec.Legacy.BoundedSym.symComplexB_not_projection_hyp`, `Feec.Legacy.BoundedSym.symComplexB_not_projection_hyp2`, `Feec.Legacy.BoundedSym.symComplexB_not_propagate`, `Feec.Legacy.BoundedSym.symComplexB_tsd_not_propagates`, `Feec.Legacy.BoundedSym.symComplexD_diagnosis`, `Feec.Legacy.BoundedSym.symComplexD_not_projection_hyp`, `Feec.Legacy.Constraints.Kc_propagates`, `Feec.Legacy.Constraints.Kmax_propagates`, `Feec.Legacy.Constraints.existsUnique_classicalSolution_mem_Kc`, `Feec.Legacy.TorusSym.adjoint_curlS`, `Feec.Legacy.TorusSym.adjoint_hessS`, `Feec.Legacy.TorusSym.curlSym_mem_trSub`, `Feec.Legacy.TorusSym.projKc_mem_domL`, `Feec.Legacy.TorusSym.symComplex`, `Feec.Legacy.TorusSym.symComplex_closedRange`, `Feec.Legacy.TorusSym.symComplex_hodge`, `Feec.Models.Torus.SymCurl.adjoint_d`, `Feec.Models.Torus.SymCurl.closedRangeAt`, `Feec.Models.Torus.SymCurl.complex`, `Feec.Models.Torus.SymCurl.dual_closedRangeAt`, `Feec.Models.Torus.SymCurl.tsd_propagates`
- modules: Feec.Algebra.MatrixSymbol, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Fourier.Euclidean, Feec.Fourier.FibreReducing, Feec.Fourier.SymCurlSymbol, Feec.Fourier.SymbolComplex, Feec.Fourier.Torus, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.BoundedDomain.Kstar, Feec.Legacy.BoundedDomain.Salvage, Feec.Legacy.BoundedDomain.SalvageMax, Feec.Legacy.BoundedDomain.Sym, Feec.Legacy.BoundedDomain.SymExt, Feec.Legacy.Box.Mirror, Feec.Legacy.Box.Reduce, Feec.Legacy.Constraints, Feec.Legacy.MirrorCube.SymCube, Feec.Legacy.MirrorCube.SymPi, Feec.Legacy.Torus.Basic, Feec.Legacy.Torus.Sym, Feec.Legacy.WeakSolution, Feec.Legacy.Whole.Basic, Feec.Models.BoundedDomain.SymCurl, Feec.Models.Cube.MirrorSym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Sec §4.12

- modules: Feec.Fourier.SpectralGalerkin

### Sec §4.13

- modules: Feec.Fourier.SpectralGalerkin

### Sec §5.1

- tagged: `Feec.BGG.HilbertData.twistComplex`, `Feec.BGG.Segment`, `Feec.BGG.Segment.D1_D0`
- cited: `Feec.BGG.Data`, `Feec.BGG.Hilb`, `Feec.BGG.Hilb.Hyps`, `Feec.BGG.Hilb.Wcheck`, `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`, `Feec.BGG.Hilb.jW_spec`, `Feec.BGG.Hilb.mem_Z1_iff`, `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`, `Feec.BGG.Hilb.tripleNorm_definite`, `Feec.BGG.Hilb.tripleNorm_spec`, `Feec.BGG.HilbertData`, `Feec.BGG.HilbertData.twistComplex`, `Feec.BGG.Segment`, `Feec.BGG.Segment.D0`, `Feec.BGG.Segment.D1`, `Feec.BGG.Segment.D1_D0`, `Feec.BGG.Segment.ExactBot`, `Feec.BGG.Segment.ExactTop`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.Γ`, `Feec.BGG.Stability`, `Feec.BGG.WaveData.Wcheck`
- modules: Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.BGG.Twisted, Feec.HilbertComplex.BGG.WeakSymmetry, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.MirrorCube.BggCube, Feec.Legacy.MirrorCube.BggTorus, Feec.Legacy.Whole.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG

### Sec §5.2

- cited: `Feec.BGG.Discrete`, `Feec.BGG.Discrete.Compatible`, `Feec.BGG.Discrete.exact_mid_h`, `Feec.BGG.Discrete.exists_sub_S0h_eq`, `Feec.BGG.IsMixedSolution`, `Feec.BGG.anticomm_of_comm_proj`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.exists_of_exact_rows`, `Feec.BGG.mixedForm_bijective`, `Feec.BGG.surjective_of_comp_eq`
- modules: Feec.Counterexamples.DiscreteBGG, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent

### Sec §5.3

- tagged: `Feec.FiniteElement.comp_eq_of_dof`
- cited: `Feec.FiniteElement.comp_eq_of_dof`
- modules: Feec.FiniteElement.Dof, Feec.HilbertComplex.BGG.Discrete

### Sec §6.1

- cited: `Feec.BGG.WaveData.MultiplierSolution`, `Feec.BGG.WaveData.MultiplierSolution.unique`, `Feec.BGG.WaveData.Solution`, `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.BGG.WaveData.Solution.unique`, `Feec.BGG.WaveData.Wcheck`, `Feec.Legacy.BoundedBGG.bggComplex_verdict`
- modules: Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.TimeDependent, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.MirrorCube.BggCube, Feec.Legacy.MirrorCube.BggTorus, Feec.Legacy.Whole.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG

### Sec §6.2

- cited: `Feec.BGG.DiscreteSolution`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection`, `Feec.BGG.discreteSkewForm`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.BGG.projected_compatible_phi_iff`, `Feec.BGG.projected_compatible_u`, `Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi`
- modules: Feec.Counterexamples.ConstrainedEvolution, Feec.HilbertComplex.BGG.TimeDependent

### Sec §6.3

- tagged: `Feec.Models.Euclidean.BGG.reducingSubcomplex`, `Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Euclidean.BGG.tsd_propagates`, `Feec.Models.Euclidean.BGG.tsd_propagates_neg`, `Feec.Models.Euclidean.BGG.waveGroup_mem`, `Feec.Models.Torus.BGG.closedRangeAt`, `Feec.Models.Torus.BGG.hodge`, `Feec.Models.Torus.BGG.reducingSubcomplex`, `Feec.Models.Torus.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_propagates`, `Feec.Models.Torus.BGG.tsd_propagates_neg`, `Feec.Models.Torus.BGG.waveGroup_mem`
- cited: `Feec.Legacy.BoundedBGG.bggComplex_verdict`, `Feec.Models.Torus.BGG.verdict`
- modules: Feec.Fourier.BGGSymbol, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.MirrorCube.BggCube, Feec.Legacy.MirrorCube.BggTorus, Feec.Legacy.Whole.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG

### Ch 5

- named: `Feec.BGG.Discrete.Compatible`, `Feec.BGG.Discrete.errorConst`, `Feec.BGG.IsMixedSolution`
- old: Feec.Ch5.Discrete.Disc.C55, Feec.Ch5.Discrete.Disc.Hyp54, Feec.Ch5.Discrete.Sys56
- modules: Feec.Fourier.BGGSymbol, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.MirrorCube.BggCube, Feec.Legacy.MirrorCube.BggTorus, Feec.Legacy.Whole.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG

### Ch 6

- named: `Feec.BGG.DiscreteSolution`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection`, `Feec.BGG.WaveData.MultiplierSolution`, `Feec.BGG.WaveData.Solution`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.Models.Cube.MirrorBGG.propagatesQ`, `Feec.Variational.norm_sub_le_of_projected_error`
- old: Feec.Ch6.ContData.Sol61, Feec.Ch6.ContData.Sol62, Feec.Ch6.Sol63, Feec.Ch6.ch6_convergence, Feec.Ch6.ch6_convergence_Sol63, Feec.Ch6.ch6_convergence_rate, Feec.Repair.C417.ch6_corrected, Feec.Repair.C67.ch6_convergence_projected
- tagged: `Feec.Models.Cube.MirrorBGG.existsUnique_memQ`, `Feec.Models.Cube.MirrorBGG.exists_nonstationaryQ`, `Feec.Models.Cube.MirrorBGG.invariantCore_eqQ`, `Feec.Models.Cube.MirrorBGG.propagatesQ`, `Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ`, `Feec.Models.Cube.reducingSubcomplex_tsd_torusBGG`
- modules: Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.TimeDependent, Feec.Legacy.BoundedDomain.BGG, Feec.Legacy.BoundedDomain.Salvage, Feec.Legacy.MirrorCube.BggCube, Feec.Legacy.MirrorCube.BggTorus, Feec.Legacy.Whole.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG

### Ch 7

- tagged: `Feec.Numerics.CrankNicolson.amplitudeB`, `Feec.Numerics.CrankNicolson.amplitudeE`, `Feec.Numerics.CrankNicolson.cellCount_table`, `Feec.Numerics.CrankNicolson.dt`, `Feec.Numerics.CrankNicolson.finalTime_table`, `Feec.Numerics.CrankNicolson.planeWave_amplitudes`, `Feec.Numerics.CrankNicolson.planeWave_solves`, `Feec.Numerics.CrankNicolson.stepCount_table`, `Feec.TimeStepping.IsCNStep`, `Feec.TimeStepping.IsCNStep.norm_eq`, `Feec.TimeStepping.IsCNStep.unique`, `Feec.TimeStepping.IsCNStep.unique_of_isSkewSymmetric`, `Feec.TimeStepping.isCNStep_cayley`, `Feec.TimeStepping.isSymm_diagonal_mul_add_smul`, `Feec.TimeStepping.mulVec_diagonal_mul_iff`, `Feec.TimeStepping.norm_cayley_apply`, `Feec.TimeStepping.norm_cayley_pow_apply`, `Feec.TimeStepping.norm_eq_of_forall_isCNStep`, `LinearPMap.IsSkewAdjoint.isCNStep_cayley`
- cited: `Feec.Legacy.CrankNicolson.FullStep`, `Feec.Legacy.CrankNicolson.RedStep`, `Feec.Legacy.CrankNicolson.cn_invertible`, `Feec.Legacy.CrankNicolson.cn_matrix_det_ne_zero`, `Feec.Legacy.CrankNicolson.cn_matrix_energy`, `Feec.Legacy.CrankNicolson.div_B_invariant_full`, `Feec.Legacy.CrankNicolson.fullLHS_bijective`, `Feec.Legacy.CrankNicolson.full_step_energy`, `Feec.Legacy.CrankNicolson.full_step_unique`, `Feec.Legacy.CrankNicolson.minres_symm`, `Feec.Legacy.CrankNicolson.red_to_full`, `Feec.Legacy.Minres.cnSystem_not_isSymm_of_ne`, `Feec.Legacy.Minres.cn_matrix_not_isSymm`, `Feec.Legacy.Minres.cn_schur_iff`, `Feec.Legacy.Minres.minres_cn_existsUnique`, `Feec.Legacy.Minres.minres_matrix_indefinite`, `Feec.Legacy.Minres.minres_matrix_isUnit`, `Feec.Legacy.Minres.minres_matrix_not_posDef`, `Feec.Legacy.Minres.minres_solution_iff_cnStep`, `Feec.Legacy.Minres.minres_solution_iff_redStep`, `Feec.Legacy.Minres.schurE_posDef`
- modules: Feec.Legacy.CrankNicolson, Feec.Legacy.Minres, Feec.Legacy.MirrorCube.Pi, Feec.Numerics.CrankNicolsonTable, Feec.TimeStepping.BlockMatrix, Feec.TimeStepping.Cayley
