# Thesis map

Traceability from V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of
General Relativity* (PhD thesis, Minnesota, 2015) [QuennevilleBelair2015] to the Lean
declarations of `Feec`. Lean names carry no thesis numbers after the refactor
(`docs/REFACTOR_PLAN.md` §1); this file is the only place where they meet.

**Generated** by `lake exe feec-thesismap` from declaration names and docstrings; do not edit
by hand, rerun after renaming (`lake exe feec-gate` fails while this file is out of date). A
declaration is listed under a thesis id when

- **named**: it is a current home (`docs/migration/map.tsv`) of a pre-refactor declaration whose
  name encoded the id (`prop_4_17`, `prop417_density_gap`, `ch6_corrected`, `Sol61`); those old
  names are listed, unchecked, under **old**;
- **cited**: its docstring cites the id, as `[QuennevilleBelair2015], Prop. 4.17 (corrected)`
  (the citation convention of `docs/REFACTOR_PLAN.md`);
- **modules**: the module cites the id anywhere in its source (module docstring,
  `## References`, comments).

Every backticked name in a list item below is checked by `lake exe feec-mapcheck`
(the declaration must exist).

Counts at generation: 42 numbered results (Thm/Prop/Cor/Lemma/Remark/Def), 80 equations/sections/chapters, 1012 distinct declarations (133 current homes of thesis-numbered old names).

## Results

### Prop 2.1

- named: `Feec.CurvatureTensor.interchange_of_bianchi`, `Feec.CurvatureTensor.lower_riemComp_isAlgCurv`, `Feec.CurvatureTensor.riemField_isAlgCurv`
- old: Feec.Curvature.prop_2_1, Feec.Curvature.prop_2_1_jet
- cited: `Feec.CurvatureTensor.Bianchi1`, `Feec.CurvatureTensor.PairSkew`, `Feec.CurvatureTensor.lower_riemComp_isAlgCurv`, `Feec.CurvatureTensor.lower_riemComp_skew`, `Feec.CurvatureTensor.riemComp_bianchi`, `Feec.CurvatureTensor.riemComp_skew`, `Feec.CurvatureTensor.riemField_isAlgCurv`, `Feec.CurvatureTensor.riemLowField_bianchi1`, `Feec.CurvatureTensor.riemLowField_interchange`, `Feec.CurvatureTensor.riemLowField_pairSkew`, `Feec.DoubleForm.bianchi_iff_altPart`
- modules: Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Bianchi, Feec.Geometry.Bivector, Feec.Geometry.Connection

### Thm 2.3

- cited: `Feec.LinearizedGravity.HbarJet`, `Feec.LinearizedGravity.Hfun`, `Feec.LinearizedGravity.Hfun_eq_bar`, `Feec.LinearizedGravity.Hjet`, `Feec.LinearizedGravity.Hjet_eq_bar`, `Feec.LinearizedGravity.Hjet_eq_div`, `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.Hsym_eq`
- modules: Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Prop 2.4

- named: `Feec.Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ`
- old: Feec.Linearized.thesis_prop_2_4b_false
- cited: `Feec.Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ`, `Feec.LinearizedGravity.Hfun_lorentz`, `Feec.LinearizedGravity.Hjet_lorentz`, `Feec.LinearizedGravity.Hsym_lorentz`, `Feec.LinearizedGravity.LorentzJet`, `Feec.LinearizedGravity.exists_lorentz_gauge`
- modules: Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge, Feec.Physics.LinearizedGravity.PlaneWave

### Prop 2.5

- cited: `Feec.LinearizedGravity.plane_wave`
- modules: Feec.Physics.LinearizedGravity.PlaneWave

### Prop 2.6

- named: `Feec.LinearizedGravity.exists_ttGauge`, `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`
- old: Feec.Repair.C2.prop_2_6, Feec.Repair.C2.prop_2_6_metric
- cited: `Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed`, `Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed_contra`, `Feec.LinearizedGravity.exists_ttGauge`, `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`, `Feec.LinearizedGravity.tt_gauge`, `Feec.LinearizedGravity.tt_gauge_fun`
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
- modules: Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.Nonlinear, Feec.Physics.EinsteinBianchi.System

### Lemma 3.5

- cited: `Feec.Counterexamples.BoundedSymTSD.hessCurlMax_d₁_mem_tsdT`, `Feec.EinsteinBianchi.curl_TSD_field`, `Feec.EinsteinBianchi.div_curl_field`, `Feec.Fourier.GradCurl.curl_mem_tsd`, `Feec.Fourier.GradCurl.isFibreReducing`, `Feec.Fourier.SymCurl.curl_mem_trSub`, `Feec.Fourier.SymCurl.isFibreReducing`, `Feec.MatrixSymbol.axial_curl`, `Feec.MatrixSymbol.curl`, `Feec.MatrixSymbol.curlSymbol_mem_ttSub`, `Feec.MatrixSymbol.curl_isTSD`, `Feec.MatrixSymbol.div`, `Feec.MatrixSymbol.div_curl`, `Feec.MatrixSymbol.div_sub_transpose`, `Feec.MatrixSymbol.trace_curl`, `Feec.MatrixSymbol.trace_curl_eq_vskw`, `Feec.MatrixSymbol.trace_curl_of_transpose_eq`, `Feec.MatrixSymbol.transpose_curl_eq`, `Feec.MatrixSymbol.two_smul_vskw_curl`, `Feec.MatrixSymbol.vskw`, `Feec.Models.BoundedDomain.adjoint_hessCurl_d₁_mem_tsdS`, `Feec.Models.BoundedDomain.curl_symm_of_mem_tsd`, `Feec.Models.BoundedDomain.hessCurl_d₁_mem_tsdT`, `Feec.Models.BoundedDomain.minimal_curl_mem_tsd`, `Feec.Models.BoundedDomain.symm_of_weakCurl_tsd`, `Feec.Models.BoundedDomain.trace_minimal_curl_eq_zero`
- modules: Feec.Algebra.MatrixSymbol, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedDomainTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Counterexamples.EveryBallSymTSD, Feec.Fourier.BGGSymbol, Feec.Fourier.GradCurlSymbol, Feec.Fourier.SymCurlSymbol, Feec.Models.BoundedDomain.GradCurl, Feec.Models.BoundedDomain.Interior, Feec.Models.BoundedDomain.InvariantCore, Feec.Models.BoundedDomain.SymCurl, Feec.Models.Cube.AbsorbingTSD, Feec.Models.Torus.BGG, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.System

### Prop 3.6

- named: `Feec.EinsteinBianchi.propagation_hyps_nonvacuous`, `Feec.EinsteinBianchi.tsd_propagates`
- old: Feec.EB.prop_3_6, Feec.EB.prop_3_6_hyps_nonvacuous
- cited: `Feec.Domain.FiniteSpeed.IsWeakSolution.ae_eq_zero_of_ball`, `Feec.EinsteinBianchi.curl_TSD_field`, `Feec.EinsteinBianchi.div_propagation`, `Feec.EinsteinBianchi.energy_flux`, `Feec.EinsteinBianchi.tsd_propagates`, `Feec.EinsteinBianchi.tsd_propagates_classical`, `Feec.EinsteinBianchi.violation_evolution`
- modules: Feec.Domain.FiniteSpeed, Feec.Models.BoundedDomain.Interior, Feec.Physics.EinsteinBianchi.Constraints, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.Propagation, Feec.Physics.EinsteinBianchi.System

### Thm 4.1

- cited: `Feec.BGG.Hilb.hodge_Vt1`, `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`, `Feec.HilbertComplex.hodge`, `Feec.HilbertComplex.hodge_domain`, `Feec.HilbertComplex.hodge_domainComplex`, `Feec.HilbertComplex.hodge_domain_of_closedRangeAt`, `Feec.HilbertComplex.hodge_of_closedRangeAt`
- modules: Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.Compactness, Feec.HilbertComplex.DomainComplex, Feec.HilbertComplex.Hodge

### Thm 4.2

- cited: `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`, `Feec.Counterexamples.not_poincare_curl`, `Feec.Counterexamples.not_poincare_grad`, `Feec.HilbertComplex.closedRangeAt_iff_poincare`, `Feec.HilbertComplex.closedRangeAt_iff_poincare_adjoint`, `Feec.HilbertComplex.closedRangeAt_iff_poincare_of_rel`, `LinearPMap.exists_norm_le_of_isClosed_range`, `LinearPMap.isClosed_range_iff_exists_norm_le`
- modules: Feec.Counterexamples.NonClosedRangeEuclidean, Feec.ForMathlib.LinearPMap.ClosedRange, Feec.Fourier.ClosedRange, Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.DomainComplex, Feec.HilbertComplex.Hodge

### Thm 4.3

- named: `Feec.C0Semigroup.existsUnique_classicalSolution`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.isSkewAdjoint_wave`, `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`
- old: Feec.HilbertComplex2.thm_4_3_hodgeWave, Feec.HilbertComplex2.thm_4_3_hodgeWave_thm43, Feec.IsSkewAdjoint.wellPosedClassical_thm43, Feec.IsSkewAdjoint.wellPosedClassical_thm43Full, Feec.IsSkewAdjoint.wellPosedExistence_thm43, Feec.IsSkewAdjoint.wellPosedExistence_thm43Full, Feec.Torus.thm_4_3_torus, Feec.UnitaryGroupGenerator.wellPosedClassical_thm43, Feec.UnitaryGroupGenerator.wellPosedClassical_thm43Full, Feec.thm_4_3_full, Feec.thm_4_3_of_isSkewAdjoint, Feec.thm_4_3_unconditional
- cited: `Feec.C0Semigroup.isClassicalSolution_mild`, `Feec.Evolution.ForcingClass.admissible`, `Feec.Evolution.IsClassicalSolution`, `Feec.Evolution.IsStrongSolution.norm_sub_le`, `Feec.Evolution.IsStrongSolution.unique`, `Feec.Evolution.existsUnique_isBoundarySolution`, `Feec.Examples.bounded_standing_hypotheses`, `Feec.Examples.rotGen_standing_hypotheses`, `Feec.ForcingClass.admissible`, `Feec.ForcingDLOrW11`, `Feec.Maxwell.Medium.ohmic_existsUnique`, `Feec.Maxwell.gauss_existsUnique`, `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`, `LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup`
- modules: Feec.Evolution.BoundaryLifting, Feec.Evolution.Duhamel, Feec.Evolution.Forcing, Feec.Evolution.Solution, Feec.Evolution.WellPosed, Feec.Examples.NonVacuity, Feec.Physics.Maxwell.Constraints, Feec.Physics.Maxwell.Ohmic, Feec.Semigroup.Stone

### Thm 4.4

- named: `LinearPMap.IsSkewAdjoint.restrict`
- old: Feec.thm_4_4
- cited: `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `LinearPMap.IsSkewAdjoint.restrict`
- modules: Feec.Evolution.Constrained, Feec.ForMathlib.LinearPMap.Reducing, Feec.HilbertComplex.InvariantCore, Feec.HilbertComplex.Reducing

### Cor 4.5

- named: `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `Feec.Examples.ker_standing_hypotheses`, `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`, `LinearPMap.IsSkewAdjoint.restrict`
- old: Feec.cor_4_5, Feec.cor_4_5_ambient, Feec.cor_4_5_ambient_unconditional, Feec.cor_4_5_classical, Feec.cor_4_5_classical_unconditional, Feec.cor_4_5_hypotheses_bddOp_ker, Feec.cor_4_5_of_isSkewAdjoint, Feec.cor_4_5_unconditional
- cited: `Feec.EinsteinBianchi.div_propagation`, `Feec.EinsteinBianchi.energy_flux`, `Feec.EinsteinBianchi.tsd_propagates`, `Feec.EinsteinBianchi.violation_evolution`, `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `Feec.Examples.ker_standing_hypotheses`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`
- modules: Feec.Evolution.Constrained, Feec.Examples.NonVacuity, Feec.HilbertComplex.Reducing, Feec.Physics.EinsteinBianchi.Propagation, Feec.Physics.EinsteinBianchi.System

### Thm 4.6

- named: `Feec.HilbertComplex.HodgeWave.existsUnique`, `Feec.HilbertComplex.HodgeWave.existsUnique_hom`, `Feec.HodgeWave.existsUnique`, `Feec.HodgeWave.existsUnique_hom`
- old: Feec.HilbertComplex2.thm_4_6, Feec.HilbertComplex2.thm_4_6_classical, Feec.HilbertComplex2.thm_4_6_classical_of_unitaryGroupGenerator, Feec.HilbertComplex2.thm_4_6_of_unitaryGroupGenerator, Feec.HilbertComplex2.thm_4_6_strong_unconditional, Feec.HilbertComplex2.thm_4_6_unconditional
- cited: `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.EinsteinBianchi.WaveFEM.bgg_wave_existsUnique`, `Feec.EinsteinBianchi.WaveFEM.bgg_wave_existsUnique_cube`, `Feec.Evolution.IsStrongSolution.unique`, `Feec.Examples.idComplex_nonvacuous`, `Feec.HilbertComplex.ConformingFamily.Verdict.constrained`, `Feec.HilbertComplex.ConformingFamily.feec`, `Feec.HilbertComplex.ConstrainedFEEC.Verdict`, `Feec.HilbertComplex.HodgeWave.existsUnique`, `Feec.HilbertComplex.HodgeWave.existsUnique_hom`, `Feec.HilbertComplex.approxFEEC`, `Feec.HilbertComplex.constrainedFEEC`, `Feec.HilbertComplex.constrainedFEEC_wellPosed`, `Feec.HilbertComplex.isSkewAdjoint_wave`, `Feec.HilbertComplex.skewFEEC`, `Feec.HodgeWave.eqOn_waveGroup_of_isWeakSolution`, `Feec.HodgeWave.existsUnique`, `Feec.HodgeWave.existsUnique_hom`, `Feec.HodgeWave.exists_isClassicalWeakSolution_tendstoUniformlyOn`, `Feec.HodgeWave.norm_eq`, `Feec.HodgeWave.waveGroup`, `Feec.Instances.Corollaries.acoustic`, `Feec.Instances.Maxwell.Verdict`, `Feec.Instances.Maxwell.maxwellFEEC`, `Feec.Instances.Maxwell.medium_maxwellFEEC`, `Feec.ShortHilbertComplex.isSkewAdjoint_wave`
- modules: Feec.Counterexamples.ClassicalRegularity, Feec.Evolution.Solution, Feec.Examples.NonVacuity, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ApproxFEEC, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.Approximation.Crown, Feec.HilbertComplex.Approximation.DissipFEEC, Feec.HilbertComplex.Approximation.SkewFEEC, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.Dirac, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.ReducedSystem, Feec.HilbertComplex.Short, Feec.Instances.Corollaries, Feec.Instances.Maxwell, Feec.Instances.MaxwellMedia, Feec.Physics.EinsteinBianchi.Unconditional, Feec.Physics.EinsteinBianchi.WaveFEM

### Thm 4.7

- named: `Feec.HilbertComplex.HodgeWave.classicalWeak_iff_classical`, `Feec.HilbertComplex.HodgeWave.weak_iff_strong`, `Feec.HodgeWave.classicalWeak_iff_classical`, `Feec.HodgeWave.weak_iff_strong`
- old: Feec.HilbertComplex2.thm_4_7, Feec.HilbertComplex2.thm_4_7_classical, Feec.HilbertComplex2.thm_4_7_classical_unconditional, Feec.HilbertComplex2.thm_4_7_unconditional
- cited: `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.Examples.idComplex_nonvacuous`, `Feec.HilbertComplex.ConformingFamily.Verdict.constrained`, `Feec.HilbertComplex.ConformingFamily.feec`, `Feec.HilbertComplex.ConstrainedFEEC.Verdict`, `Feec.HilbertComplex.HodgeWave.classicalWeak_iff_classical`, `Feec.HilbertComplex.HodgeWave.weak_iff_strong`, `Feec.HilbertComplex.approxFEEC`, `Feec.HilbertComplex.approxFEEC_unique_weak`, `Feec.HilbertComplex.constrainedFEEC`, `Feec.HilbertComplex.constrainedFEEC_wellPosed`, `Feec.HilbertComplex.skewFEEC`, `Feec.HodgeWave.IsWeakSolution.isClassicalSolution`, `Feec.HodgeWave.classicalWeak_iff_classical`, `Feec.HodgeWave.eqOn_waveGroup_of_isWeakSolution`, `Feec.HodgeWave.exists_isClassicalWeakSolution_tendstoUniformlyOn`, `Feec.HodgeWave.isClassicalWeakSolution_of_isClassicalSolution`, `Feec.HodgeWave.isWeakSolution_of_isStrongSolution`, `Feec.HodgeWave.weak_iff_strong`, `Feec.Instances.Corollaries.acoustic`, `Feec.Instances.Maxwell.Verdict`, `Feec.Instances.Maxwell.maxwellFEEC`, `Feec.Instances.Maxwell.medium_maxwellFEEC`
- modules: Feec.Examples.NonVacuity, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ApproxFEEC, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.Approximation.Crown, Feec.HilbertComplex.Approximation.DissipFEEC, Feec.HilbertComplex.Approximation.SkewFEEC, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.HodgeWave, Feec.Instances.Corollaries, Feec.Instances.Maxwell, Feec.Instances.MaxwellMedia

### Thm 4.8

- cited: `Feec.Variational.existsUnique_of_coercive`, `Feec.Variational.infSup_of_coercive`
- modules: Feec.Variational.BabuskaNecas

### Thm 4.9

- cited: `Feec.Counterexamples.surjective_not_infSup`, `Feec.Variational.InfSup.surjective`, `Feec.Variational.babuskaNecas_iff`, `Feec.Variational.babuskaNecas_iff_inner`, `Feec.Variational.existsUnique_apply_eq`, `Feec.Variational.existsUnique_inner`, `Feec.Variational.exists_infSup_of_bijective`, `Feec.Variational.infSup_iff_mul_norm_symm_le`
- modules: Feec.Counterexamples.Ell2, Feec.Variational.BabuskaNecas

### Thm 4.10

- named: `Feec.Variational.InfSup.norm_sub_le_infDist`, `Feec.Variational.InfSup.norm_sub_le_infDist_sharp`
- old: Feec.Galerkin.thm_4_10
- cited: `Feec.Variational.InfSup.norm_le_of_restrict_eq`, `Feec.Variational.InfSup.norm_sub_le_infDist`, `Feec.Variational.InfSup.norm_sub_le_infDist_sharp`, `Feec.Variational.InfSup.norm_sub_le_of_orthogonal`, `Feec.Variational.InfSup.norm_sub_le_of_orthogonal_sharp`, `Feec.Variational.existsUnique_galerkin`, `Feec.Variational.existsUnique_galerkin_sesq`
- modules: Feec.Variational.BabuskaNecas, Feec.Variational.Galerkin

### Thm 4.11

- named: `Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.isSaddleSolution_rieszOp_iff`
- old: Feec.Galerkin.thm_4_11
- cited: `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.infSup_a`, `Feec.BGG.Hilb.infSup_b`, `Feec.BGG.Hilb.saddle_wellPosed`, `Feec.BGG.brezzi_wellPosed_real`, `Feec.Variational.IsSaddleSolution`, `Feec.Variational.IsSaddleSolution.norm_fst_le`, `Feec.Variational.IsSaddleSolution.norm_snd_le`, `Feec.Variational.IsSaddleSolution.unique`, `Feec.Variational.brezzi_iff`, `Feec.Variational.existsUnique_discrete_isSaddleSolution`, `Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.exists_lift`, `Feec.Variational.isSaddleSolution_rieszOp_iff`
- modules: Feec.HilbertComplex.BGG.WeakSymmetry, Feec.Variational.Fortin, Feec.Variational.SaddlePoint

### Lemma 4.12

- named: `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`, `le_add_half_integral_of_sq_deriv_le_mul`, `le_add_half_integral_of_sq_deriv_le_mul_sharp`, `le_add_half_sub_of_sq_deriv_le_mul`
- old: Feec.lemma_4_12, Feec.lemma_4_12_integral, Feec.lemma_4_12_sharp
- cited: `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le`, `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`, `le_add_half_integral_of_sq_deriv_le_mul`, `le_add_half_integral_of_sq_deriv_le_mul_sharp`, `le_add_half_sub_of_sq_deriv_le_mul`, `norm_le_add_integral_of_re_inner_deriv_le`, `norm_le_of_re_inner_deriv_le`
- modules: Feec.Evolution.Energy, Feec.ForMathlib.Analysis.Gronwall, Feec.HilbertComplex.BGG.TimeDependent

### Prop 4.13

- named: `Feec.Variational.InfSup.of_testMap`
- old: Feec.Complex3.prop_4_13, Feec.Complex3.prop_4_13_V, Feec.Complex3.prop_4_13_infSup, Feec.Complex3.prop_4_13_lower, Feec.Complex3.prop_4_13_test_norm
- cited: `Feec.BGG.Discrete.infSup_shiftedForm_h`, `Feec.HilbertComplex.ConstrainedFEEC.isApproximating`, `Feec.HilbertComplex.HasCompactPropertyAt`, `Feec.HilbertComplex.constrainedFEEC_rate`, `Feec.HilbertComplex.ellipticConst`, `Feec.HodgeWave.infSup_shiftedForm`, `Feec.HodgeWave.norm_ellipticProjection_le`, `Feec.Variational.InfSup.of_testMap`, `Feec.Variational.InfSup.restrict_of_testMap`
- modules: Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.BGG.EllipticProjection, Feec.HilbertComplex.Compactness, Feec.HilbertComplex.Mixed, Feec.Variational.InfSup

### Thm 4.14

- named: `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, `Feec.Variational.GalerkinEvolution.error_bound_refined`
- old: Feec.Complex3.thm_4_14, Feec.Complex3.thm_4_14_pointwise
- cited: `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection`, `Feec.BGG.ExactWave.exists_discreteSolution_rate`, `Feec.BGG.ExactWave.exists_discreteSolution_rate_harm`, `Feec.BGG.HarmonicStability.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection_L2`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection_L2`, `Feec.Counterexamples.ClassicalRegularity.exists_datum_not_C1`, `Feec.Counterexamples.ClassicalRegularity.not_C1_graphSpace`, `Feec.Counterexamples.ClassicalRegularity.tendstoUniformlyOn_truncSub_datum`, `Feec.HilbertComplex.ConformingFamily.Verdict.Rated.rate_wave`, `Feec.HilbertComplex.ConformingFamily.Verdict.constrained`, `Feec.HilbertComplex.ConformingFamily.feec`, `Feec.HilbertComplex.ConformingFamily.feec_rated`, `Feec.HilbertComplex.ConstrainedFEEC.RateClass`, `Feec.HilbertComplex.ConstrainedFEEC.RateClass.ofDegreewise`, `Feec.HilbertComplex.ConstrainedFEEC.RateClass.ofJackson`, `Feec.HilbertComplex.ConstrainedFEEC.Verdict`, `Feec.HilbertComplex.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection`, `Feec.HilbertComplex.Subcomplex.norm_sub_le_of_approx`, `Feec.HilbertComplex.constrainedFEEC`, `Feec.HilbertComplex.constrainedFEEC_rate`, `Feec.HodgeWave.IsGraphSolution`, `Feec.HodgeWave.IsGraphSolution.norm_sub_le`, `Feec.HodgeWave.exists_isClassicalWeakSolution_tendstoUniformlyOn`, `Feec.HodgeWave.exists_isGraphSolution`, `Feec.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection`, `Feec.HodgeWave.exists_tendstoUniformlyOn_of_tendsto`, `Feec.HodgeWave.norm_sub_ellipticProjection_le`, `Feec.HodgeWave.norm_sub_le_of_comparison`, `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, `Feec.HodgeWave.tendstoUniformlyOn_ellipticProjection`, `Feec.HodgeWave.tendstoUniformlyOn_of_isGraphSolution`, `Feec.HodgeWave.tendstoUniformlyOn_of_isWeakSolution`, `Feec.HodgeWave.tendstoUniformlyOn_of_tendsto`, `Feec.HodgeWave.tendstoUniformlyOn_semidiscrete`, `Feec.Instances.Corollaries.acoustic`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_approxFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_constrainedFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_constrainedFEEC_sobolev`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_approxFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_constrainedFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_constrainedFEEC_sobolev`, `Feec.Instances.Maxwell.Verdict`, `Feec.Instances.Maxwell.maxwellFEEC`, `Feec.Instances.Maxwell.medium_maxwellFEEC`, `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_sub_le_window_sobolevQ`, `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_sub_le_window_sobolevQ_high`, `Feec.Models.Cube.FEM.exists_tendstoUniformlyOn_window`, `Feec.Models.Cube.FEM.exists_tendstoUniformlyOn_windowMin_whitney`, `Feec.Models.Cube.FEM.exists_tendstoUniformlyOn_window_poly`, `Feec.Models.Cube.FEM.exists_tendstoUniformlyOn_window_whitney`, `Feec.Models.Cube.FEM.norm_sub_le_meshSize_window`, `Feec.Models.Cube.FEM.norm_sub_le_meshSize_windowMin_smooth`, `Feec.Models.Cube.FEM.norm_sub_le_meshSize_window_smooth`, `Feec.Models.Cube.FEM.norm_sub_le_windowMin_lagrangeP2`, `Feec.Models.Cube.FEM.norm_sub_le_windowTr_lagrangeP2`, `Feec.Models.Cube.FEM.norm_sub_le_window_poly_smooth_of_polyOrderAt`, `Feec.Models.Parallelepiped.exists_tendstoUniformlyOn_window_poly`, `Feec.Models.Parallelepiped.exists_tendstoUniformlyOn_window_whitney`, `Feec.Models.Parallelepiped.norm_sub_le_meshSize_window_smooth`, `Feec.Models.StarShaped.MeshFamily.exists_tendstoUniformlyOn_window`, `Feec.Models.StarShaped.MeshFamily.exists_tendstoUniformlyOn_windowMin`, `Feec.Models.StarShaped.MeshFamily.exists_tendstoUniformlyOn_window_poly`, `Feec.Models.StarShaped.MeshFamily.norm_sub_le_window_poly_smooth_of_polyOrderAt`, `Feec.Variational.GalerkinEvolution.error_bound`, `Feec.Variational.GalerkinEvolution.error_bound_refined`, `Feec.Variational.norm_sub_le_of_projected_error`, `Feec.Variational.norm_sub_le_of_projected_error_decay`
- modules: Feec.Counterexamples.ClassicalRegularity, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.Approximation.Crown, Feec.HilbertComplex.Approximation.SemidiscreteWave, Feec.HilbertComplex.BGG.DiscreteWave, Feec.HilbertComplex.BGG.Harmonic, Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.Corollaries, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiSpectral, Feec.Instances.Maxwell, Feec.Instances.MaxwellMedia, Feec.Models.Cube.FiniteElementConvergence, Feec.Models.Cube.FiniteElementMethod, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.PolyFiniteElementConvergence, Feec.Models.Cube.PolyRate, Feec.Models.Cube.SobolevRate, Feec.Models.Cube.SobolevRateHigh, Feec.Models.Cube.TangentialRate, Feec.Models.Cube.WeakSymmetryWave, Feec.Models.Cube.WhitneyApprox, Feec.Models.Cube.WhitneyRate, Feec.Models.Parallelepiped.FiniteElement, Feec.Models.StarShaped.FiniteElement, Feec.Models.StarShaped.PolyFiniteElement, Feec.Variational.GalerkinEvolution

### Thm 4.15

- cited: `Feec.HilbertComplex.ConstrainedFEEC.RateClass`, `Feec.HilbertComplex.Subcomplex.CochainProjection`
- modules: Feec.FiniteElement.Dof, Feec.HilbertComplex.Approximation.CochainProjection, Feec.HilbertComplex.Approximation.ConstrainedFEEC

### Prop 4.16

- named: `Feec.Counterexamples.BoundedSymTSD.hessCurlMax_divFree_propagates`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.HilbertComplex.ReducingSubcomplex.propagates_neg`, `Feec.Models.BoundedDomain.bggComplex_divFree_propagates`, `Feec.Models.BoundedDomain.hessCurl_divFree_propagates`, `Feec.ShortHilbertComplex.divFree_propagates`, `Feec.ShortHilbertComplex.divFree_propagates_neg`
- old: Feec.BoundedSym.symComplexB_prop_4_16, Feec.BoundedSym.symComplexD_prop_4_16, Feec.Ch6.Bounded.bggComplex_prop_4_16, Feec.Constraints.prop_4_16, Feec.Constraints.prop_4_16', Feec.Constraints.prop_4_16_classical_unconditional, Feec.Constraints.prop_4_16_exists, Feec.Constraints.prop_4_16_exists_unconditional
- cited: `Feec.Counterexamples.BoundedSymTSD.hessCurlMax_divFree_propagates`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.Instances.EuclideanBand.maxwellApprox_isReducing`, `Feec.Instances.EuclideanBand.maxwell_euclidean_band`, `Feec.Instances.Maxwell.Verdict`, `Feec.Instances.Maxwell.discreteGauss_propagates`, `Feec.Instances.Maxwell.gaussFam`, `Feec.Instances.Maxwell.isReducing_gauss`, `Feec.Instances.Maxwell.isReducing_windowGauss`, `Feec.Instances.Maxwell.maxwellFEEC`, `Feec.Instances.Maxwell.medium_maxwellFEEC`, `Feec.Instances.Maxwell.reducingSubcomplex_gaussFam`, `Feec.Instances.Maxwell.windowGauss_propagates`, `Feec.Instances.Maxwell.windowGauss_propagates_strong`, `Feec.Maxwell.euclidean_gauss_propagates`, `Feec.Maxwell.gauss_existsUnique`, `Feec.Maxwell.gauss_propagates`, `Feec.Maxwell.pec_gauss_propagates`, `Feec.Maxwell.pmc_gauss_propagates`, `Feec.Maxwell.torus_gauss_propagates`, `Feec.Maxwell.waveGroup_mem`, `Feec.Models.BoundedDomain.bggComplex_divFree_propagates`, `Feec.Models.BoundedDomain.hessCurl_divFree_propagates`, `Feec.ShortHilbertComplex.divFreeSub`, `Feec.ShortHilbertComplex.divFree_propagates`, `Feec.ShortHilbertComplex.divFree_propagates_neg`, `Feec.ShortHilbertComplex.reducingSubcomplex_divFreeSub`
- modules: Feec.Counterexamples.BoundedSymTSD, Feec.HilbertComplex.InvariantCore, Feec.HilbertComplex.InvariantCoreSpectral, Feec.HilbertComplex.Reducing, Feec.Instances.EuclideanBand, Feec.Instances.Maxwell, Feec.Instances.MaxwellMedia, Feec.Models.BoundedDomain.BGG, Feec.Models.BoundedDomain.SymCurl, Feec.Physics.Maxwell.Constraints, Feec.Physics.Maxwell.Forms, Feec.Physics.Maxwell.Media

### Prop 4.17

- named: `Feec.C0Group.IsIsometric.isReducing_of_forward_invariant`, `Feec.Counterexamples.BoundedBGG.bggComplex_invariantCore_propagates`, `Feec.Counterexamples.BoundedDomainTSD.density_gap`, `Feec.Counterexamples.BoundedDomainTSD.invariantCore_tsd`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates_neg`, `Feec.HilbertComplex.ReducingSubcomplex.waveGroup_mem`, `Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.HilbertComplex.isReducing_iff_waveGroup_invariant`, `Feec.HilbertComplex.isReducing_invariantCore_waveGroup`, `Feec.HilbertComplex.le_invariantCore_waveGroup`, `Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.Mirror.existsUnique_memQ`, `Feec.Models.Cube.Mirror.propagates`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Euclidean.BGG.tsd_propagates_neg`, `Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.real_tsd_propagates`, `Feec.Models.Euclidean.GradCurl.tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.GradCurl.waveGroup_mem`, `Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.GradCurl.tsd_propagates_neg`, `Feec.Models.Torus.GradCurl.waveGroup_mem`
- old: Feec.BoundedDomain.prop417_density_gap, Feec.BoundedDomain.thesisComplex_prop_4_17_max, Feec.Box.mirror_prop_4_17, Feec.Box.mirror_prop_4_17_exists, Feec.Box.prop_4_17_hyps_res, Feec.Box.prop_4_17_res, Feec.Box.prop_4_17_res_exists, Feec.Ch6.Bounded.bggComplex_prop_4_17_max, Feec.Ch6.Whole.prop_4_17_bggWhole, Feec.Constraints.le_max_of_prop_4_17_hyps, Feec.Constraints.prop_4_17, Feec.Constraints.prop_4_17_exists_unconditional, Feec.Constraints.prop_4_17_group_all_unconditional, Feec.Constraints.prop_4_17_group_unconditional, Feec.Constraints.prop_4_17_iff, Feec.Constraints.prop_4_17_iff_unconditional, Feec.Constraints.prop_4_17_max, Feec.Constraints.prop_4_17_max_unconditional, Feec.Constraints.prop_4_17_necessary, Feec.Constraints.prop_4_17_necessary_unconditional, Feec.Repair.C417.mirrorCxCube_prop_4_17_exists, Feec.Repair.C417.mirrorCxQ_prop_4_17_exists, Feec.Repair.C417.piCube_mirror_prop_4_17_exists, Feec.Repair.C417.prop_4_17_compr_exists, Feec.Repair.C417.prop_4_17_corrected, Feec.Repair.C417.prop_4_17_corrected_cube, Feec.Repair.C417.prop_4_17_hyps_compr, Feec.Repair.C417.prop_4_17_hyps_scale, Feec.Repair.C417.prop_4_17_hyps_scale2, Feec.Repair.C417.unitCube_mirror_prop_4_17_exists, Feec.Torus.prop_4_17_torus, Feec.Torus.prop_4_17_torus_backward, Feec.Torus.prop_4_17_torus_classical, Feec.Torus.prop_4_17_torus_exists, Feec.Torus.prop_4_17_torus_exists_of_Hcurl, Feec.Torus.prop_4_17_torus_group, Feec.Torus.prop_4_17_torus_group_all, Feec.Torus.prop_4_17_torus_group_periodic, Feec.Whole.prop_4_17_whole, Feec.Whole.prop_4_17_whole_exists, Feec.Whole.prop_4_17_whole_group, Feec.WholeReal.real_prop_4_17_whole, Feec.WholeReal.real_prop_4_17_whole_exists
- cited: `Feec.Counterexamples.BallEigenDense.coreSub_le_stationary_ball3_iff`, `Feec.Counterexamples.BoundedBGG.bggComplex_invariantCore_propagates`, `Feec.Counterexamples.BoundedDomainTSD.betaL2_not_propagates`, `Feec.Counterexamples.BoundedDomainTSD.beta_violation_boundary_layer`, `Feec.Counterexamples.BoundedDomainTSD.density_dichotomy`, `Feec.Counterexamples.BoundedDomainTSD.density_gap`, `Feec.Counterexamples.BoundedDomainTSD.exists_isStrongSolution_tsd_not_propagates`, `Feec.Counterexamples.BoundedDomainTSD.exists_projTSD_not_mem_domain`, `Feec.Counterexamples.BoundedDomainTSD.invariantCore_tsd`, `Feec.Counterexamples.BoundedDomainTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedDomainTSD.not_mem_closure_wave_domain_inter`, `Feec.Counterexamples.BoundedDomainTSD.not_projection_magnetic`, `Feec.Counterexamples.BoundedDomainTSD.not_starProjection_mem_adjoint_domain`, `Feec.Counterexamples.BoundedDomainTSD.not_starProjection_mem_curl_maximal`, `Feec.Counterexamples.BoundedDomainTSD.not_starProjection_mem_curl_maximal_bochner`, `Feec.Counterexamples.BoundedDomainTSD.obstruction_ne_bot`, `Feec.Counterexamples.BoundedDomainTSD.projection_unbounded`, `Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`, `Feec.Counterexamples.BoundedDomainTSD.violation_boundary_layer`, `Feec.Counterexamples.BoxStationary.forward_iff_stationary_box`, `Feec.Counterexamples.BoxStationary.mem_invariantCore_tsd_iff_box`, `Feec.Counterexamples.BoxStationary.not_exists_tsd_eigenfield_box`, `Feec.Counterexamples.BoxStationary.tsd_not_propagates_box`, `Feec.Counterexamples.CubeStationary.forward_iff_stationary`, `Feec.Counterexamples.CubeStationary.mem_invariantCore_tsd_iff`, `Feec.Counterexamples.CubeStationary.tsd_not_propagates`, `Feec.EinsteinBianchi.cube_tsd_existsUnique`, `Feec.EinsteinBianchi.cube_tsd_propagates`, `Feec.EinsteinBianchi.euclidean_tsd_propagates`, `Feec.EinsteinBianchi.torus_tsd_propagates`, `Feec.Fourier.FibreReducing.existsUnique_mem`, `Feec.Fourier.FibreReducing.propagates`, `Feec.Fourier.GradCurl.isFibreReducing`, `Feec.HilbertComplex.ConformingFamily.Verdict.constrained`, `Feec.HilbertComplex.ConformingFamily.feec`, `Feec.HilbertComplex.ConstrainedFEEC.Verdict`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`, `Feec.HilbertComplex.approxFEEC`, `Feec.HilbertComplex.approxFEEC_isReducing_iff_keeps`, `Feec.HilbertComplex.constrainedFEEC`, `Feec.HilbertComplex.constrainedFEEC_propagates`, `Feec.HilbertComplex.constrainedFEEC_propagates_iff`, `Feec.HilbertComplex.constrainedFEEC_propagates_iff_domain`, `Feec.HilbertComplex.constrainedFEEC_propagates_iff_of_grading`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.HilbertComplex.isReducing_iff_waveGroup_invariant`, `Feec.HilbertComplex.mem_closure_domain_inter_ker_adjoint`, `Feec.HilbertComplex.skewFEEC`, `Feec.HilbertComplex.skewFEEC_isReducing_iff_invariant`, `Feec.Instances.EinsteinBianchi.FEM.isReducing_tsdQℝ`, `Feec.Instances.EinsteinBianchi.StandardCubeVerdict`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_approxFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_constrainedFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_thesisCube`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_approxFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_constrainedFEEC`, `Feec.Instances.EinsteinBianchi.exists_mem_thesisTSD_not_mem_closure`, `Feec.Instances.EinsteinBianchi.mirrorFEEC_isReducing`, `Feec.Instances.EinsteinBianchi.not_isReducing_thesisCube`, `Feec.Instances.EinsteinBianchi.not_isReducing_thesisTSD`, `Feec.Instances.EinsteinBianchi.thesisTSD`, `Feec.Instances.EinsteinBianchi.torusFEEC_isReducing`, `Feec.Instances.Maxwell.Verdict`, `Feec.Instances.Maxwell.maxwellFEEC`, `Feec.Instances.Maxwell.windowGauss_propagates`, `Feec.Models.BoundedDomain.WeakEB.mem_tsd_univ`, `Feec.Models.BoundedDomain.closure_eq_tsd₀`, `Feec.Models.BoundedDomain.closure_tsd_inf_curl_maximal`, `Feec.Models.BoundedDomain.dense_curl_inter_divFree`, `Feec.Models.BoundedDomain.dense_curl_maximal_inter_divFree`, `Feec.Models.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.Models.BoundedDomain.integral_eq_zero_of_mem_tsd`, `Feec.Models.BoundedDomain.not_finiteDimensional_obstruction`, `Feec.Models.BoundedDomain.not_tsd_le_closure_sup_finiteDimensional`, `Feec.Models.BoundedDomain.sum_integral_mul_pd_eq_zero`, `Feec.Models.BoundedDomain.tsd`, `Feec.Models.BoundedDomain.tsd_cone`, `Feec.Models.BoundedDomain.tsd_depDomain`, `Feec.Models.BoundedDomain.tsd₀`, `Feec.Models.BoundedDomain.tsd₀_le_closure`, `Feec.Models.Box.Mirror.existsUnique_memBox`, `Feec.Models.Box.Mirror.exists_nonstationaryBox`, `Feec.Models.Box.Mirror.invariantCore_eqBox`, `Feec.Models.Box.Mirror.propagatesBox`, `Feec.Models.Box.Mirror.reducingSubcomplexBox`, `Feec.Models.Box.forward_iff`, `Feec.Models.Box.mem_invariantCore_iff`, `Feec.Models.Box.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Models.Cube.Ident.forward_iff_pi`, `Feec.Models.Cube.Ident.mem_invariantCore_iff`, `Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff_pi`, `Feec.Models.Cube.Inhomogeneous.constraint`, `Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.Mirror.existsUnique_memCube_pi`, `Feec.Models.Cube.Mirror.existsUnique_memCube_trace`, `Feec.Models.Cube.Mirror.existsUnique_memCube_unit`, `Feec.Models.Cube.Mirror.existsUnique_memQ`, `Feec.Models.Cube.Mirror.existsUnique_memQ_trace`, `Feec.Models.Cube.Mirror.exists_nonstationary`, `Feec.Models.Cube.Mirror.exists_nonstationaryCube`, `Feec.Models.Cube.Mirror.exists_nonstationaryQ`, `Feec.Models.Cube.Mirror.invariantCore_eq`, `Feec.Models.Cube.Mirror.invariantCore_eqCube`, `Feec.Models.Cube.Mirror.invariantCore_eqQ`, `Feec.Models.Cube.Mirror.propagates`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Cube.Mirror.propagatesQ`, `Feec.Models.Cube.Mirror.reducingSubcomplex`, `Feec.Models.Cube.Mirror.reducingSubcomplexCube`, `Feec.Models.Cube.Mirror.reducingSubcomplexQ`, `Feec.Models.Cube.Parity.exists_linearIndependent_invariantCore`, `Feec.Models.Cube.Parity.forward_iff`, `Feec.Models.Cube.Parity.forward_torus_iff`, `Feec.Models.Cube.Parity.forward_tsd_iff`, `Feec.Models.Cube.Parity.invariantCore_ne_bot`, `Feec.Models.Cube.Parity.mem_invariantCore_iff`, `Feec.Models.Cube.Parity.mem_invariantCore_torus_iff`, `Feec.Models.Cube.Parity.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Parity.not_finiteDimensional_invariantCore`, `Feec.Models.Cube.RowWise.forward_iff`, `Feec.Models.Cube.RowWise.mem_invariantCore_iff`, `Feec.Models.Cube.RowWise.mem_invariantCore_tsd_iff`, `Feec.Models.Euclidean.GradCurl.fourier_mem_constraint_iff`, `Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.real_tsd_propagates`, `Feec.Models.Euclidean.GradCurl.reducingSubcomplex`, `Feec.Models.Euclidean.GradCurl.tsd_existsUnique`, `Feec.Models.Euclidean.GradCurl.tsd_propagates`, `Feec.Models.Euclidean.GradCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.GradCurl.waveGroup_mem`, `Feec.Models.Torus.GradCurl.real_tsd_existsUnique`, `Feec.Models.Torus.GradCurl.real_tsd_propagates`, `Feec.Models.Torus.GradCurl.reducingSubcomplex`, `Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.GradCurl.tsd_propagates`, `Feec.Models.Torus.GradCurl.tsd_propagates_neg`, `Feec.Models.Torus.GradCurl.waveGroup_mem`, `Feec.ShortHilbertComplex.mem_closure_domain_inter_ker_adjoint`
- modules: Feec.Algebra.MatrixSymbol, Feec.Counterexamples.BallEigenDense, Feec.Counterexamples.BallEigenfields, Feec.Counterexamples.BoundedBGG, Feec.Counterexamples.BoundedDomainTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Counterexamples.BoxStationary, Feec.Counterexamples.CubeStationary, Feec.Domain.Mollify, Feec.Domain.Obstruction, Feec.Fourier.Euclidean, Feec.Fourier.FibreReducing, Feec.Fourier.GradCurlSymbol, Feec.Fourier.Reality, Feec.Fourier.TorusSpectral, Feec.Fourier.Weak, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ApproxFEEC, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Crown, Feec.HilbertComplex.Approximation.DissipFEEC, Feec.HilbertComplex.Approximation.SkewFEEC, Feec.HilbertComplex.Density, Feec.HilbertComplex.Equivariant, Feec.HilbertComplex.InvariantCore, Feec.HilbertComplex.InvariantCoreSpectral, Feec.HilbertComplex.Reducing, Feec.HilbertComplex.Transport, Feec.Instances.Corollaries, Feec.Instances.CrownNonVacuity, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiFEM, Feec.Instances.EinsteinBianchiFEMCube, Feec.Instances.EinsteinBianchiFEMMirror, Feec.Instances.EinsteinBianchiSpectral, Feec.Instances.Maxwell, Feec.Models.BoundedDomain.Density, Feec.Models.BoundedDomain.GradCurl, Feec.Models.BoundedDomain.Interior, Feec.Models.BoundedDomain.InvariantCore, Feec.Models.BoundedDomain.MovingTSD, Feec.Models.Box.EigenDense, Feec.Models.Box.Mirror, Feec.Models.Cube.AbsorbingTSD, Feec.Models.Cube.Basic, Feec.Models.Cube.EigenDense, Feec.Models.Cube.Ident, Feec.Models.Cube.Inhomogeneous, Feec.Models.Cube.Mirror, Feec.Models.Cube.MirrorDirichlet, Feec.Models.Cube.MirrorTrace, Feec.Models.Cube.Parity, Feec.Models.Cube.Reflection, Feec.Models.Cube.RowWiseIdent, Feec.Models.Cube.Static, Feec.Models.Euclidean.GradCurl, Feec.Models.Torus.GradCurl, Feec.Numerics.PlaneWaveCube, Feec.Physics.EinsteinBianchi.Constraints, Feec.Semigroup.Spectral

### Prop 4.18

- named: `Feec.Models.BoundedDomain.hessCurl_existsUnique_reducedSolution`, `Feec.ShortHilbertComplex.divFree_propagates_neg`, `Feec.ShortHilbertComplex.existsUnique_reducedSolution_divFree`, `Feec.ShortHilbertComplex.isStrongSolution_of_isReducedSolution`, `Feec.ShortHilbertComplex.reducedSolution_of_exists`
- old: Feec.BoundedSym.symComplexB_prop_4_18, Feec.Constraints.prop_4_18, Feec.Constraints.prop_4_18_i, Feec.Constraints.prop_4_18_ii, Feec.Constraints.prop_4_18_unconditional
- cited: `Feec.HilbertComplex.DissipFEEC.crankNicolson_pow_mem`, `Feec.HilbertComplex.DissipFEEC.rationalScheme_pow_mem`, `Feec.HilbertComplex.DissipFEEC.thetaScheme_pow_mem`, `Feec.Models.BoundedDomain.hessCurl_existsUnique_reducedSolution`, `Feec.ShortHilbertComplex.IsReducedSolution.mem_ker_adjoint`, `Feec.ShortHilbertComplex.existsUnique_reducedSolution`, `Feec.ShortHilbertComplex.existsUnique_reducedSolution_divFree`, `Feec.ShortHilbertComplex.isReducedSolution_of_isStrongSolution`, `Feec.ShortHilbertComplex.isStrongSolution_of_isReducedSolution`, `Feec.ShortHilbertComplex.reducedSolution_of_exists`, `Feec.TimeStepping.IsCNStep.mem_of_isReducing`, `Feec.TimeStepping.IsReducedCNStep.adjoint_eq_zero_of_isFullCNStep`, `Feec.TimeStepping.IsReducedCNStep.isFullCNStep_zero`, `Feec.TimeStepping.RationalScheme.apply_mem_of_mapsTo`, `Feec.TimeStepping.mem_of_forall_isCNStep`, `Feec.TimeStepping.thetaStep_mem_of_isReducing`, `Feec.TimeStepping.thetaStep_mem_of_keeps`, `Feec.TimeStepping.thetaStep_mem_of_mapsTo`
- modules: Feec.HilbertComplex.Approximation.FullyDiscrete, Feec.HilbertComplex.Approximation.RationalScheme, Feec.HilbertComplex.InvariantCore, Feec.HilbertComplex.InvariantCoreSpectral, Feec.HilbertComplex.ReducedSystem, Feec.HilbertComplex.Reducing, Feec.Models.BoundedDomain.Interior, Feec.Models.BoundedDomain.SymCurl, Feec.TimeStepping.Cayley, Feec.TimeStepping.Convergence, Feec.TimeStepping.Rational, Feec.TimeStepping.Theta

### Prop 4.19

- named: `Feec.Counterexamples.BoundedSymTSD.invariantCore_tsd`, `Feec.Counterexamples.BoundedSymTSD.invariantCore_tsdSKer`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memQ`, `Feec.Models.Cube.MirrorSym.propagates`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Euclidean.SymCurl.tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.SymCurl.waveGroup_mem`, `Feec.Models.Torus.SymCurl.real_tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_propagates_neg`, `Feec.Models.Torus.SymCurl.waveGroup_mem`
- old: Feec.BoundedSym.symComplexB_prop_4_19_max, Feec.BoundedSym.symComplexD_prop_4_19_max, Feec.Box.mirror_prop_4_19, Feec.Box.mirror_prop_4_19_exists, Feec.Repair.C417.mirrorSymCxCube_prop_4_19_exists, Feec.Repair.C417.mirrorSymCxQ_prop_4_19_exists, Feec.Repair.C417.prop_4_19_corrected, Feec.Repair.C417.prop_4_19_corrected_cube, Feec.TorusSym.prop_4_19_torus, Feec.TorusSym.prop_4_19_torus_exists, Feec.TorusSym.prop_4_19_torus_exists_real, Feec.TorusSym.prop_4_19_torus_group, Feec.TorusSym.prop_4_19_torus_iff, Feec.TorusSym.prop_4_19_torus_real_space, Feec.TorusSym.prop_4_19_torus_symGroup, Feec.WholeSym.prop_4_19_whole, Feec.WholeSym.prop_4_19_whole_exists, Feec.WholeSym.prop_4_19_whole_group
- cited: `Feec.Counterexamples.BallSymTSD.not_propagates`, `Feec.Counterexamples.BallSymTSD.tsd_not_propagates`, `Feec.Counterexamples.BoundedSymTSD.diagnosis`, `Feec.Counterexamples.BoundedSymTSD.diagnosis_hessCurlMax`, `Feec.Counterexamples.BoundedSymTSD.exists_projTSD_not_mem_domain`, `Feec.Counterexamples.BoundedSymTSD.hessCurlMax_d₁_mem_tsdT`, `Feec.Counterexamples.BoundedSymTSD.invariantCore_tsd`, `Feec.Counterexamples.BoundedSymTSD.invariantCore_tsdSKer`, `Feec.Counterexamples.BoundedSymTSD.not_dense_hessCurlMax`, `Feec.Counterexamples.BoundedSymTSD.not_dense_tsdS_inter`, `Feec.Counterexamples.BoundedSymTSD.not_finiteDimensional_obstruction`, `Feec.Counterexamples.BoundedSymTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedSymTSD.not_projection_magnetic`, `Feec.Counterexamples.BoundedSymTSD.not_starProjection_mem_adjoint_domain`, `Feec.Counterexamples.BoundedSymTSD.not_starProjection_mem_wave_domain_hessCurlMax`, `Feec.Counterexamples.BoundedSymTSD.tsd_not_propagates`, `Feec.Counterexamples.EveryBallSymTSD.tsd_not_propagates`, `Feec.Fourier.FibreReducing.existsUnique_mem`, `Feec.Fourier.FibreReducing.propagates`, `Feec.Fourier.SymCurl.isFibreReducing`, `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`, `Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.Models.BoundedDomain.adjoint_hessCurl_d₁_mem_tsdS`, `Feec.Models.BoundedDomain.hessCurl`, `Feec.Models.BoundedDomain.hessCurlMax`, `Feec.Models.BoundedDomain.hessCurl_d₁_mem_tsdT`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memQ`, `Feec.Models.Cube.MirrorSym.exists_nonstationary`, `Feec.Models.Cube.MirrorSym.exists_nonstationaryCube`, `Feec.Models.Cube.MirrorSym.exists_nonstationaryQ`, `Feec.Models.Cube.MirrorSym.invariantCore_eq`, `Feec.Models.Cube.MirrorSym.invariantCore_eqCube`, `Feec.Models.Cube.MirrorSym.invariantCore_eqQ`, `Feec.Models.Cube.MirrorSym.propagates`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Cube.MirrorSym.propagatesQ`, `Feec.Models.Cube.MirrorSym.reducingSubcomplex`, `Feec.Models.Cube.MirrorSym.reducingSubcomplexCube`, `Feec.Models.Cube.MirrorSym.reducingSubcomplexQ`, `Feec.Models.Euclidean.SymCurl.real_tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.real_tsd_propagates`, `Feec.Models.Euclidean.SymCurl.reducingSubcomplex`, `Feec.Models.Euclidean.SymCurl.tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.tsd_propagates`, `Feec.Models.Euclidean.SymCurl.tsd_propagates_neg`, `Feec.Models.Euclidean.SymCurl.waveGroup_mem`, `Feec.Models.Torus.SymCurl.real_tsd_existsUnique`, `Feec.Models.Torus.SymCurl.real_tsd_propagates`, `Feec.Models.Torus.SymCurl.reducingSubcomplex`, `Feec.Models.Torus.SymCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_propagates`, `Feec.Models.Torus.SymCurl.tsd_propagates_neg`, `Feec.Models.Torus.SymCurl.waveGroup_mem`
- modules: Feec.Algebra.MatrixSymbol, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Counterexamples.EveryBallSymTSD, Feec.Fourier.Euclidean, Feec.Fourier.FibreReducing, Feec.Fourier.SymCurlSymbol, Feec.HilbertComplex.InvariantCore, Feec.HilbertComplex.InvariantCoreSpectral, Feec.HilbertComplex.Reducing, Feec.Models.BoundedDomain.SymCurl, Feec.Models.BoundedDomain.SymDualGeneral, Feec.Models.Cube.MirrorSym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Prop 5.1

- named: `Feec.BGG.Hilb.isClosed_closedRange_exact`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Hilb.toHilbertComplex_closedRangeAt_one`, `Feec.BGG.Hilb.toHilbertComplex_cycles_one`, `Feec.BGG.Hilb.toShort_closedRange_exact`
- old: Feec.Ch5.BGG.BGGHilb.prop_5_1
- cited: `Feec.BGG.Hilb.D0op_isClosed`, `Feec.BGG.Hilb.D1op_isClosed`, `Feec.BGG.Hilb.D1op_isClosed_range`, `Feec.BGG.Hilb.Hyps`, `Feec.BGG.Hilb.exact_D0op_D1op`, `Feec.BGG.Hilb.isClosed_closedRange_exact`, `Feec.BGG.Hilb.isClosed_range_T`, `Feec.BGG.Hilb.isClosed_Γ`, `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Hilb.toHilbertComplex_closedRangeAt_one`, `Feec.BGG.Hilb.toHilbertComplex_closedRangeAt_two`, `Feec.BGG.Hilb.toHilbertComplex_cycles_one`, `Feec.BGG.Hilb.toHilbertComplex_cycles_zero`, `Feec.BGG.Hilb.toShort`, `Feec.BGG.Hilb.toShort_closedRange_exact`, `Feec.BGG.Segment.D1_D0`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.range_D0`, `Feec.BGG.Segment.range_D1`, `Feec.BGG.Segment.sup_range_eq_top`, `Feec.BGG.Stability`, `Feec.BGG.isClosed_range_prod`, `Feec.Models.Cube.WeakSymmetry.bggShort_closedRange_exact'`
- modules: Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.Derived, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.ToComplex, Feec.Instances.EinsteinBianchiGauss, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryComplex

### Prop 5.2

- named: `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.saddle_wellPosed`
- old: Feec.Ch5.BGG.BGGHilb.prop_5_2, Feec.Ch5.BGG.BGGHilb.prop_5_2_wellPosed
- cited: `Feec.BGG.Hilb.Wcheck`, `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.existsUnique_isSaddle`, `Feec.BGG.Hilb.hodge_Vt1`, `Feec.BGG.Hilb.infSup_a`, `Feec.BGG.Hilb.infSup_b`, `Feec.BGG.Hilb.jW_spec`, `Feec.BGG.Hilb.nondeg_a`, `Feec.BGG.Hilb.saddle_wellPosed`, `Feec.BGG.Hilb.tripleNorm`, `Feec.BGG.Hilb.tripleNorm_definite`, `Feec.BGG.Hilb.tripleNorm_spec`, `Feec.EinsteinBianchi.StaticFEM.staticFEM`, `Feec.EinsteinBianchi.StaticFEM.staticFEM_cube`, `Feec.Models.Cube.WeakSymmetry.bgg_existsUnique_isSaddle'`
- modules: Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.BGG.WeakSymmetry, Feec.Models.Cube.RegularDecomposition, Feec.Physics.EinsteinBianchi.StaticFEM, Feec.Physics.EinsteinBianchi.Unconditional

### Prop 5.3

- named: `Feec.BGG.Discrete.poincare_Zh`, `Feec.BGG.Discrete.poincare_Γh`
- old: Feec.Ch5.Discrete.Disc.prop_5_3_a, Feec.Ch5.Discrete.Disc.prop_5_3_b
- cited: `Feec.BGG.Discrete.exact_bot_h`, `Feec.BGG.Discrete.exact_top_h`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.poincare_Zh`, `Feec.BGG.Discrete.poincare_Γh`, `Feec.BGG.Discrete.preimage_bound`, `Feec.BGG.HarmonicStability`, `Feec.BGG.Stability`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`, `Feec.Models.Cube.WeakSymmetry.bggStability'`, `Feec.Models.Cube.WeakSymmetry.bggStability_curlPotentialConst`
- modules: Feec.Counterexamples.DiscreteBGG, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.Harmonic, Feec.Models.Cube.MirrorWeakSymmetryComplex, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryComplex

### Prop 5.4

- named: `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.BGG.eq_zero_of_mixed_homogeneous`, `Feec.BGG.existsUnique_isMixedSolution`, `Feec.BGG.exists_mixed_homogeneous_of_perp`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`
- old: Feec.Ch5.Discrete.Disc.prop_5_4, Feec.Ch5.Discrete.prop54_counterexample_noTopExact, Feec.Ch5.Discrete.prop54_existsUnique, Feec.Ch5.Discrete.prop54_hB_necessary, Feec.Ch5.Discrete.prop54_unique
- cited: `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.exists_sub_S0h_eq`, `Feec.BGG.Discrete.hodge_h`, `Feec.BGG.eq_zero_of_mixed_homogeneous`, `Feec.BGG.existsUnique_isMixedSolution`, `Feec.BGG.exists_mixed_homogeneous_of_perp`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`, `Feec.EinsteinBianchi.StaticFEM.staticFEM`, `Feec.EinsteinBianchi.StaticFEM.staticFEM_cube`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_existsUnique'`
- modules: Feec.Counterexamples.DiscreteBGG, Feec.HilbertComplex.BGG.Discrete, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryFEM, Feec.Physics.EinsteinBianchi.StaticFEM, Feec.Physics.EinsteinBianchi.Unconditional

### Thm 5.5

- named: `Feec.BGG.Discrete.errorEstimate_absorb`, `Feec.BGG.Discrete.errorEstimate_final`, `Feec.BGG.Discrete.error_estimate`, `Feec.BGG.mixed_coercivity_eq`
- old: Feec.Ch5.Discrete.Disc.thm55_absorb_real, Feec.Ch5.Discrete.Disc.thm55_final_real, Feec.Ch5.Discrete.Disc.thm_5_5, Feec.Ch5.Discrete.thm55_lhs_identity
- cited: `Feec.BGG.Discrete.errorConst`, `Feec.BGG.Discrete.error_estimate`, `Feec.BGG.Discrete.error_estimate_of_regularPotential`, `Feec.BGG.Discrete.error_estimate_of_weakConsistency`, `Feec.BGG.Discrete.exists_nonvacuous`, `Feec.BGG.Discrete.hodge_h`, `Feec.BGG.Discrete.weakConsistency_of_regularPotential`, `Feec.BGG.HarmonicStability.weakConsistency_of_regularPotential_of_bound`, `Feec.BGG.mixed_coercivity_eq`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection`, `Feec.EinsteinBianchi.StaticFEM.staticFEM`, `Feec.EinsteinBianchi.StaticFEM.staticFEM_cube`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_rate'`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_rate_C2'`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_rate_tr'`, `Feec.Models.Cube.WeakSymmetry.staticFEM_rate_sobolev`, `Feec.Models.Cube.WeakSymmetry.staticFEM_rate_sobolev_of_one_le`
- modules: Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.EllipticProjection, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.BGG.WeakConsistency, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryFEM, Feec.Models.Cube.WeakSymmetrySobolevRate, Feec.Models.Cube.WeakSymmetryTangentialRate, Feec.Physics.EinsteinBianchi.StaticFEM, Feec.Physics.EinsteinBianchi.Unconditional, Feec.Physics.EinsteinBianchi.WaveFEMRegularity, Feec.Physics.EinsteinBianchi.WaveFEMTangential, Feec.Physics.EinsteinBianchi.WaveFEMTangentialCube

### Prop 5.6

- named: `Feec.BGG.mixed_error_eq`
- old: Feec.Ch5.Discrete.prop_5_6
- cited: `Feec.BGG.Discrete.error_estimate`, `Feec.BGG.errorEq_a`, `Feec.BGG.mixed_error_eq`
- modules: Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.BGG.WeakConsistency

### Prop 5.7

- cited: `Feec.BGG.Discrete.Compatible`, `Feec.FiniteElement.PolySeq.dof_comp_coordWedgeC_mem_span`, `Feec.FiniteElement.comp_eq_of_dof`, `Feec.FiniteElement.comp_eq_of_mem_span`, `Feec.FiniteElement.dof_vanish_of_mem_span`, `Feec.FiniteElement.interp_comp_eq`
- modules: Feec.FiniteElement.Dof, Feec.FiniteElement.WeakSymmetryMaps, Feec.HilbertComplex.BGG.Discrete, Feec.Models.Cube.WeakSymmetryFEM, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.StaticFEM

### Prop 5.8

- cited: `Feec.FiniteElement.PolySeq.exists_local_formL2Sq_equiv`, `Feec.FiniteElement.exists_local_formL2Sq_equiv_of_le_polySpace`, `Feec.FiniteElement.exists_local_formL2Sq_equiv_polySpace`, `Feec.Models.Cube.WeakSymmetry.norm_glue_bggS0h_le`, `Feec.Models.Cube.WeakSymmetry.norm_glue_bggS1h_le`
- modules: Feec.FiniteElement.PolyInterpolation, Feec.FiniteElement.PolyInverseEstimate, Feec.Models.Cube.WeakSymmetryEstimates, Feec.Models.Cube.WeakSymmetryFEM, Feec.Physics.EinsteinBianchi.StaticFEM

### Prop 5.9

- cited: `Feec.BGG.Discrete.RegularPotential`, `Feec.BGG.Discrete.consistency_S0_of_approx`, `Feec.BGG.Discrete.consistency_S1_of_regularPotential`, `Feec.BGG.Discrete.error_estimate_of_regularPotential`, `Feec.BGG.Discrete.error_estimate_of_weakConsistency`, `Feec.BGG.Discrete.strang_rate_of_regularPotential`, `Feec.BGG.Discrete.weakConsistency_of_regularPotential`, `Feec.BGG.HarmonicStability.weakConsistency_of_regularPotential_of_bound`, `Feec.FiniteElement.exists_formL2Sq_le_formGradL2Sq`, `Feec.FiniteElement.exists_formL2Sq_sub_polyMinusInterp_le_formGradL2Sq`, `Feec.FiniteElement.exists_local_kernel_bound`, `Feec.HilbertComplex.DissipFEEC.Comparison`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorFEM_happ0`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_ellipticProjection_rate_trS1`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_happ0`, `Feec.Models.Cube.WeakSymmetry.exists_bestApproxError_ge`, `Feec.Models.Cube.WeakSymmetry.exists_interpolationError_ge`, `Feec.Models.Cube.WeakSymmetry.norm_sub_glue_bggS0h_le`, `Feec.Models.Cube.WeakSymmetry.not_exists_bestApprox_bound`, `Feec.Models.Cube.WeakSymmetry.not_exists_interpolationError_bound`, `Feec.Models.Cube.WeakSymmetry.vN_mem_polySpace`
- modules: Feec.FiniteElement.PolyInterpolation, Feec.FiniteElement.PolyInverseEstimate, Feec.HilbertComplex.Approximation.DissipFEEC, Feec.HilbertComplex.BGG.EllipticProjection, Feec.HilbertComplex.BGG.WeakConsistency, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetryEstimates, Feec.Models.Cube.WeakSymmetryFEM, Feec.Models.Cube.WeakSymmetryTangentialRate, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.StaticFEM

### Prop 6.1

- named: `Feec.BGG.WaveData.Solution.exists_multiplierSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_isClosed_range`
- old: Feec.Ch6.ContData.prop_6_1_i, Feec.Ch6.ContData.prop_6_1_i_closedRange, Feec.Ch6.ContData.prop_6_1_ii
- cited: `Feec.BGG.WaveData.MultiplierSolution.toSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.BGG.WaveData.mem_Wcheck_of_vanish`
- modules: Feec.HilbertComplex.BGG.TimeDependent, Feec.Physics.EinsteinBianchi.WaveFEM

### Prop 6.2

- named: `Feec.BGG.DiscreteSolution.compatible`, `Feec.BGG.exists_discreteSolution`, `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_of_continuousOn`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`
- old: Feec.Ch6.prop_6_2, Feec.Ch6.prop_6_2_exists, Feec.Ch6.prop_6_2_exists_of_continuousOn, Feec.Ch6.prop_6_2_exists_regular, Feec.Ch6.prop_6_2_false, Feec.Ch6.prop_6_2_necessary, Feec.Repair.C67.prop_6_2_dynamic, Feec.Repair.C67.prop_6_2_wellposed
- cited: `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.DiscreteSolution.compatible`, `Feec.BGG.DiscreteSolution.eq_zero_of_initial_eq_zero`, `Feec.BGG.DiscreteSolution.phi_eq`, `Feec.BGG.DiscreteSolution.phi_zero`, `Feec.BGG.DiscreteSolution.unique`, `Feec.BGG.ExactWave.exists_discreteSolution_rate`, `Feec.BGG.ExactWave.exists_discreteSolution_rate_harm`, `Feec.BGG.HarmonicStability.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.eq_zero_of_isEllipticProjection`, `Feec.BGG.exists_discreteSolution`, `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.exists_discreteSolution_norm_sub_le_L2`, `Feec.BGG.exists_discreteSolution_norm_sub_le_ellipticProjection`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.BGG.not_exists_discreteSolution_of_ker`, `Feec.BGG.not_exists_discreteSolution_phi_of_ker`, `Feec.BGG.projected_compatible_u_L2`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_converges`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_rate`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr`
- modules: Feec.Counterexamples.ConstrainedEvolution, Feec.HilbertComplex.BGG.DiscreteWave, Feec.HilbertComplex.BGG.EllipticProjection, Feec.HilbertComplex.BGG.Harmonic, Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.EinsteinBianchiFEMElliptic, Feec.Instances.EinsteinBianchiFEMGenerator, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.MirrorWeakSymmetryFEM, Feec.Models.Cube.WeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetryTangentialRate, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure, Feec.Physics.EinsteinBianchi.WaveFEM, Feec.Physics.EinsteinBianchi.WaveFEMTangential

### Prop 6.3

- named: `Feec.BGG.errorEq_a`, `Feec.BGG.errorEq_b`, `Feec.BGG.errorEq_c`, `Feec.BGG.errorEq_c_split`, `Feec.BGG.errorEq_d`, `Feec.BGG.errorEq_e`
- old: Feec.Ch6.prop_6_3_a, Feec.Ch6.prop_6_3_b, Feec.Ch6.prop_6_3_c, Feec.Ch6.prop_6_3_c_split, Feec.Ch6.prop_6_3_d, Feec.Ch6.prop_6_3_e
- cited: `Feec.BGG.Discrete.strang_shiftedForm_h`, `Feec.BGG.errorEq_a`, `Feec.BGG.errorEq_b`, `Feec.BGG.errorEq_c`, `Feec.BGG.errorEq_c_split`, `Feec.BGG.errorEq_d`, `Feec.BGG.errorEq_e`
- modules: Feec.HilbertComplex.BGG.DiscreteWave, Feec.HilbertComplex.BGG.EllipticProjection, Feec.HilbertComplex.BGG.TimeDependent

## Equations, sections and chapters

### Eq (2.2)

- cited: `Feec.CurvatureTensor.riemComp`, `Feec.CurvatureTensor.riemField`
- modules: Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Bianchi, Feec.Geometry.Connection

### Eq (2.3)

- cited: `Feec.CurvatureTensor.deviation`, `Feec.CurvatureTensor.deviationForm`, `Feec.CurvatureTensor.deviation_eq_zero_iff`, `Feec.CurvatureTensor.eq_zero_of_deviationForm`, `Feec.CurvatureTensor.eq_zero_of_symm_bd`
- modules: Feec.Geometry.AlgebraicCurvature

### Eq (2.4)

- cited: `Feec.CurvatureTensor.cov13_riem_cyclic`
- modules: Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Bianchi

### Eq (2.5)

- cited: `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`, `Feec.Metric.eq_trRev_sub`, `Feec.Metric.trRev`, `Feec.Metric.trRev_add_sym`, `Feec.Metric.trRev_trRev`, `Feec.Metric.trace_trRev`
- modules: Feec.Algebra.Metric, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.6)

- cited: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.Rjet`, `Feec.LinearizedGravity.Rjet_bianchi1`, `Feec.LinearizedGravity.Rjet_pairSkew`
- modules: Feec.Physics.LinearizedGravity.Einstein

### Eq (2.7)

- cited: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.RicJ`
- modules: Feec.Physics.LinearizedGravity.Einstein

### Eq (2.8)

- cited: `Feec.LinearizedGravity.Hjet_eq_einstein`, `Feec.LinearizedGravity.scalJ`
- modules: Feec.Physics.LinearizedGravity.Einstein

### Eq (2.9)

- modules: Feec.Physics.LinearizedGravity.Einstein

### Eq (2.10)

- modules: Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Eq (2.11)

- cited: `Feec.LinearizedGravity.Hfun_lorentz_eq_iff`, `Feec.LinearizedGravity.Hjet_lorentz_eq_iff`
- modules: Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Eq (2.12)

- cited: `Feec.LinearizedGravity.IsTT`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.mem_ttSpace_iff`, `Feec.TT.ttSub`
- modules: Feec.Algebra.TransverseTraceless, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.13)

- cited: `Feec.LinearizedGravity.finrank_ttSpace`, `Feec.LinearizedGravity.finrank_ttSub`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.mem_ttSpace_iff`
- modules: Feec.Algebra.TransverseTraceless, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.14)

- modules: Feec.Physics.LinearizedGravity.PlaneWave

### Eq (2.15)

- cited: `Feec.Counterexamples.LinearizedGravity.not_accel_printed`, `Feec.LinearizedGravity.Rjet_tt`, `Feec.LinearizedGravity.Rjet_ttWave`, `Feec.LinearizedGravity.Rjet_tt_support`, `Feec.LinearizedGravity.tt_accel`, `Feec.LinearizedGravity.tt_accel_fun`
- modules: Feec.Counterexamples.LinearizedGravity, Feec.Physics.LinearizedGravity.PlaneWave

### Eq (3.2)

- cited: `Feec.DoubleForm.weyl_reconstruct`, `Feec.DoubleForm.weyl_reconstruct_unit`
- modules: Feec.Geometry.WeylDecomposition

### Eq (4.1)

- cited: `Feec.HilbertComplex.orthogonal_boundaries`, `Feec.HilbertComplex.orthogonal_cycles`, `LinearPMap.orthogonal_range_eq_ker_adjoint`
- modules: Feec.ForMathlib.LinearPMap.ClosedRange, Feec.HilbertComplex.Hodge

### Eq (4.2)

- modules: Feec.Fourier.Torus

### Eq (4.4)

- cited: `Feec.HodgeWave.waveGroup`
- modules: Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.HodgeWave

### Eq (4.5)

- cited: `Feec.HilbertComplex.wave`, `Feec.ShortHilbertComplex.wave`
- modules: Feec.HilbertComplex.Dirac, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.Short

### Eq (4.6)

- modules: Feec.HilbertComplex.HodgeWave

### Eq (4.7)

- cited: `Feec.HilbertComplex.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsWeakSolution`
- modules: Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.HodgeWave

### Eq (4.8)

- cited: `Feec.HilbertComplex.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsGraphSolution`, `Feec.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.IsWeakSolution.unique`
- modules: Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.HodgeWave

### Eq (4.10)

- cited: `Feec.HilbertComplex.ConstrainedFEEC.discrete`, `Feec.HilbertComplex.ConstrainedFEEC.discreteWave`, `Feec.HodgeWave.IsSemidiscreteSolution`, `Feec.HodgeWave.exists_isSemidiscreteSolution`
- modules: Feec.HilbertComplex.Approximation.ApproxComplex, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.Approximation.SemidiscreteWave

### Eq (4.11)

- cited: `Feec.HilbertComplex.ApproxComplex.Family.ellProj`, `Feec.HilbertComplex.ConstrainedFEEC.toXh_ellProj_waveLift`, `Feec.HilbertComplex.ConstrainedFEEC.waveRitz`, `Feec.HodgeWave.ellipticProjection`, `Feec.HodgeWave.norm_ellipticProjection_le`, `Feec.HodgeWave.shiftedForm_ellipticProjection`
- modules: Feec.HilbertComplex.Approximation.ApproxComplex, Feec.HilbertComplex.Approximation.ApproxComplexCrime, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.Approximation.SemidiscreteWave

### Eq (4.12)

- cited: `Feec.HodgeWave.IsMixedWeak3`
- modules: Feec.HilbertComplex.SecondOrder

### Eq (4.14)

- cited: `Feec.Counterexamples.BoundedBGG.thesisComplex_B_not_symm`, `Feec.ShortHilbertComplex.existsUnique_reducedSolution_divFree`, `Feec.ShortHilbertComplex.isReducedSolution_of_isStrongSolution`, `Feec.ShortHilbertComplex.isStrongSolution_of_isReducedSolution`, `Feec.TimeStepping.IsFullCNStep`, `Feec.TimeStepping.isFullCNStep_iff_mulVec`, `Feec.TimeStepping.isUnit_blockMass_add_smul`
- modules: Feec.Counterexamples.BoundedBGG, Feec.Fourier.GradCurlSymbol, Feec.HilbertComplex.ReducedSystem, Feec.Models.BoundedDomain.Interior, Feec.Models.Box.Mirror, Feec.Models.Cube.Inhomogeneous, Feec.Models.Cube.InhomogeneousError, Feec.Models.Cube.Mirror, Feec.Models.Euclidean.GradCurl, Feec.Models.Torus.GradCurl, Feec.TimeStepping.BlockMatrix, Feec.TimeStepping.Cayley

### Eq (4.15)

- cited: `Feec.Counterexamples.BoundedBGG.thesisComplex_reduced_B_not_symm`, `Feec.Models.Torus.BGG.verdict`, `Feec.ShortHilbertComplex.IsReducedSolution`, `Feec.ShortHilbertComplex.existsUnique_reducedSolution_divFree`, `Feec.TimeStepping.IsReducedCNStep`, `Feec.TimeStepping.isReducedCNStep_iff_mulVec`
- modules: Feec.Counterexamples.BoundedBGG, Feec.HilbertComplex.ReducedSystem, Feec.Models.Box.Mirror, Feec.Models.Cube.Mirror, Feec.Models.Torus.BGG, Feec.Models.Torus.GradCurl, Feec.TimeStepping.BlockMatrix, Feec.TimeStepping.Cayley

### Eq (4.16)

- cited: `Feec.EinsteinBianchi.WaveFEM.bgg_wave_existsUnique`, `Feec.EinsteinBianchi.WaveFEM.bgg_wave_existsUnique_cube`, `Feec.Models.Cube.WeakSymmetry.bgg_existsUnique_isSaddle'`, `Feec.Models.Torus.SymCurl.closedRangeAt`, `Feec.Models.Torus.SymCurl.complex`
- modules: Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Counterexamples.EveryBallSymTSD, Feec.Fourier.SymCurlSymbol, Feec.Fourier.Torus, Feec.Models.BoundedDomain.SymCurl, Feec.Models.BoundedDomain.SymDualGeneral, Feec.Models.Cube.MirrorSym, Feec.Models.Cube.MirrorWeakSymmetryComplex, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryComplex, Feec.Models.Cube.WeakSymmetryWave, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl, Feec.Physics.EinsteinBianchi.Unconditional, Feec.Physics.EinsteinBianchi.WaveFEM

### Eq (4.17)

- cited: `Feec.Models.BoundedDomain.symCurlDivDiv`, `Feec.Models.Torus.SymCurl.adjoint_d`, `Feec.Models.Torus.SymCurl.closedRangeAt`, `Feec.Models.Torus.SymCurl.dual_closedRangeAt`
- modules: Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.EveryBallSymTSD, Feec.Fourier.SymCurlSymbol, Feec.Models.BoundedDomain.SymCurl, Feec.Models.BoundedDomain.SymDualGeneral, Feec.Models.Cube.MirrorSym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Eq (4.18)

- cited: `Feec.Counterexamples.BoundedBGG.symComplexB_B_not_symm`, `Feec.Models.Torus.SymCurl.closedRangeAt`, `Feec.Models.Torus.SymCurl.tsd_propagates`
- modules: Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedBGG, Feec.Counterexamples.EveryBallSymTSD, Feec.Fourier.SymCurlSymbol, Feec.Models.BoundedDomain.SymDualGeneral, Feec.Models.Cube.MirrorSym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Eq (5.1)

- cited: `Feec.BGG.Hilb.D0op`, `Feec.BGG.Hilb.D1op`, `Feec.BGG.Hilb.toHilbertComplex`, `Feec.BGG.Segment.D0`, `Feec.BGG.Segment.D1`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.Γ`, `Feec.Models.BoundedDomain.bggComplex`, `Feec.Models.Cube.WeakSymmetry.bggShort_closedRange_exact'`
- modules: Feec.Counterexamples.BoundedBGG, Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.Derived, Feec.HilbertComplex.BGG.ToComplex, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiGauss, Feec.Models.BoundedDomain.BGG, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Cube.RegularDecomposition, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG, Feec.Physics.EinsteinBianchi.MatrixModel

### Eq (5.2)

- cited: `Feec.BGG.Hilb.IsReduced`, `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.existsUnique_multiplier`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`
- modules: Feec.HilbertComplex.BGG.WeakSymmetry

### Eq (5.3)

- cited: `Feec.BGG.Hilb.IsSaddleW1`, `Feec.BGG.Hilb.aForm`, `Feec.BGG.Hilb.existsUnique_multiplier`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`, `Feec.Models.Cube.WeakSymmetry.bgg_existsUnique_isSaddle'`, `Feec.Models.Cube.WeakSymmetry.staticFEM_rate_sobolev`
- modules: Feec.HilbertComplex.BGG.WeakSymmetry, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetrySobolevRate, Feec.Physics.EinsteinBianchi.StaticFEM

### Eq (5.4)

- cited: `Feec.BGG.Discrete.Compatible`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.surjective_of_comp_eq`
- modules: Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.EinsteinBianchiGauss, Feec.Models.Cube.WeakSymmetryFEM, Feec.Physics.EinsteinBianchi.Unconditional

### Eq (5.5)

- cited: `Feec.BGG.Discrete.exact_mid_h`, `Feec.BGG.exists_of_exact_rows`
- modules: Feec.HilbertComplex.BGG.Discrete

### Eq (5.6)

- cited: `Feec.BGG.IsMixedSolution`
- modules: Feec.HilbertComplex.BGG.Discrete, Feec.Models.Cube.WeakSymmetrySobolevRate, Feec.Physics.EinsteinBianchi.StaticFEM

### Eq (5.7)

- cited: `Feec.FiniteElement.PolySeq.bggS0h`, `Feec.FiniteElement.PolySeq.bggS1h`
- modules: Feec.FiniteElement.WeakSymmetryMaps, Feec.Models.Cube.WeakSymmetryFEM, Feec.Physics.EinsteinBianchi.StaticFEM

### Eq (5.8)

- cited: `Feec.FiniteElement.dof_vanish_of_mem_span`
- modules: Feec.FiniteElement.Dof

### Eq (6.1)

- cited: `Feec.BGG.WaveData.Solution`, `Feec.ShortHilbertComplex.weakEqs_of_isStrongSolution`
- modules: Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.ShortDual, Feec.Models.BoundedDomain.BGG, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure, Feec.Physics.EinsteinBianchi.MatrixModel, Feec.Physics.EinsteinBianchi.WaveFEM, Feec.Physics.EinsteinBianchi.WaveFEMRegularity

### Eq (6.2)

- cited: `Feec.BGG.ExactWave`, `Feec.BGG.WaveData.MultiplierSolution`, `Feec.Instances.EinsteinBianchi.FEM.cochainDefectForm_eq`, `Feec.Models.Cube.MirrorWeakSymmetry.TSDDatum.exactWave`
- modules: Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.EinsteinBianchiFEMDefect, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure, Feec.Physics.EinsteinBianchi.WaveFEM, Feec.Physics.EinsteinBianchi.WaveFEMRegularity

### Eq (6.3)

- cited: `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.DiscreteSolution`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection_L2`, `Feec.BGG.ExactWave.exists_discreteSolution_rate`, `Feec.BGG.ExactWave.exists_discreteSolution_rate_harm`, `Feec.BGG.HarmonicStability.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.exists_discreteSolution_norm_sub_le_ellipticProjection`, `Feec.BGG.projected_compatible_phi_iff`, `Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi`
- modules: Feec.Counterexamples.ConstrainedEvolution, Feec.HilbertComplex.BGG.DiscreteWave, Feec.HilbertComplex.BGG.EllipticProjection, Feec.HilbertComplex.BGG.Harmonic, Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.EinsteinBianchiFEMComplex, Feec.Instances.EinsteinBianchiFEMElliptic, Feec.Instances.EinsteinBianchiFEMGenerator, Feec.Instances.EinsteinBianchiFEMMirror, Feec.Instances.EinsteinBianchiGauss, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure

### Eq (6.4)

- cited: `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.Discrete.strang_of_isEllipticProjection`, `Feec.BGG.Discrete.strang_rate_of_regularPotential`, `Feec.BGG.Discrete.strang_shiftedForm_h`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection_L2`, `Feec.BGG.ExactWave.exists_discreteSolution_rate`, `Feec.BGG.ExactWave.exists_discreteSolution_rate_harm`, `Feec.BGG.HarmonicStability.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.HarmonicStability.strang_shiftedForm_h`, `Feec.BGG.IsEllipticProjection`, `Feec.BGG.IsEllipticProjection.galerkin`, `Feec.BGG.ellipticProjection`, `Feec.BGG.existsUnique_isEllipticProjection`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.exists_discreteSolution_norm_sub_le_L2`, `Feec.BGG.exists_discreteSolution_norm_sub_le_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection_L2`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_of_mem_domain`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_of_mem_domain_of_orbit`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_converges`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_rate`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_ellipticProjection_rate_tr`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_ellipticProjection_rate_trS1`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr`
- modules: Feec.HilbertComplex.Approximation.ApproxComplexCrime, Feec.HilbertComplex.BGG.DiscreteWave, Feec.HilbertComplex.BGG.EllipticProjection, Feec.HilbertComplex.BGG.Harmonic, Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.EinsteinBianchiFEMComplex, Feec.Instances.EinsteinBianchiFEMCubeEll, Feec.Instances.EinsteinBianchiFEMDefect, Feec.Instances.EinsteinBianchiFEMElliptic, Feec.Instances.EinsteinBianchiFEMMirror, Feec.Instances.EinsteinBianchiFEMMirrorEll, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Cube.WeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetrySobolevRate, Feec.Models.Cube.WeakSymmetryTangentialRate, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure, Feec.Physics.EinsteinBianchi.WaveFEMRegularity, Feec.Physics.EinsteinBianchi.WaveFEMTangential

### Eq (6.5)

- cited: `Feec.EinsteinBianchi.BoundedConvergence.tendsto_of_isStrongSolution`, `Feec.EinsteinBianchi.BoundedConvergence.tendsto_of_mem_wave_domain`, `Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`, `Feec.EinsteinBianchi.BoundedFailure.waveFEM_converges_to_non_tsd_of_isRateApproximable`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_of_mem_domain`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_of_mem_domain_of_orbit`, `Feec.HilbertComplex.DissipFEEC.Comparison`, `Feec.Instances.EinsteinBianchi.FEM.cochainDefectForm_eq`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_waveFEM`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_waveFEM_rate`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_waveFEM_rate_sobolev`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_thesisCube`, `Feec.Instances.EinsteinBianchi.mirrorFEMApprox_verdict`, `Feec.Instances.EinsteinBianchi.standardCubeApprox_verdict`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_converges`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_rate`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`, `Feec.Models.Cube.WeakSymmetry.cubeWave_converges`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_sobolev`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr`
- modules: Feec.HilbertComplex.Approximation.DissipFEEC, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiFEM, Feec.Instances.EinsteinBianchiFEMComplex, Feec.Instances.EinsteinBianchiFEMCube, Feec.Instances.EinsteinBianchiFEMCubeEll, Feec.Instances.EinsteinBianchiFEMDefect, Feec.Instances.EinsteinBianchiFEMMirror, Feec.Instances.EinsteinBianchiFEMMirrorEll, Feec.Instances.EinsteinBianchiGauss, Feec.Models.Cube.DeRhamPartialFEM, Feec.Models.Cube.MirrorWaveRegularity, Feec.Models.Cube.MirrorWeakSymmetryComplex, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.MirrorWeakSymmetryFEM, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetrySobolevRate, Feec.Models.Cube.WeakSymmetryTangentialRate, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure, Feec.Physics.EinsteinBianchi.Unconditional, Feec.Physics.EinsteinBianchi.WaveFEM, Feec.Physics.EinsteinBianchi.WaveFEMRegularity, Feec.Physics.EinsteinBianchi.WaveFEMTangential

### Sec §1.1

- modules: Feec.Geometry.WeylDecomposition

### Sec §2.2

- cited: `Feec.LinearizedGravity.η4`, `Feec.Metric.minkowski`, `Feec.Metric.minkowski4`, `Feec.Metric.minkowskiMatrix`
- modules: Feec.Algebra.Metric, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §2.3

- cited: `Feec.CurvatureTensor.Interchange`, `Feec.CurvatureTensor.algCurvEquiv`, `Feec.CurvatureTensor.bianchi_iff`, `Feec.CurvatureTensor.deviation_eq_zero_iff`, `Feec.CurvatureTensor.einstein`, `Feec.CurvatureTensor.einstein_isSymm`, `Feec.CurvatureTensor.eq_zero_of_deviationForm`, `Feec.CurvatureTensor.finrank_algCurv_four`, `Feec.CurvatureTensor.interchange_of_bianchi`, `Feec.CurvatureTensor.ricci`, `Feec.CurvatureTensor.ricci_isSymm`, `Feec.CurvatureTensor.ricci_isSymm_of_inv`, `Feec.CurvatureTensor.ricci_riemField_isSymm`
- modules: Feec.Geometry.AlgebraicCurvature, Feec.Geometry.Bianchi, Feec.Geometry.Connection

### Sec §2.4

- cited: `Feec.Counterexamples.Curvature.exists_einstein_eq_zero_ne_zero_two`, `Feec.CurvatureTensor.einstein_eq_zero_iff`, `Feec.LinearizedGravity.einstein_const_bounds`
- modules: Feec.Counterexamples.Curvature, Feec.Geometry.AlgebraicCurvature, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §2.7

- cited: `Feec.LinearizedGravity.Hfun_bianchi`, `Feec.LinearizedGravity.Hfun_gauge`, `Feec.LinearizedGravity.Hjet_bianchi`, `Feec.LinearizedGravity.Hjet_gauge`, `Feec.LinearizedGravity.Hsym_div`, `Feec.LinearizedGravity.Hsym_gauge`, `Feec.LinearizedGravity.jet2_isSymJet2`, `Feec.Metric.trRev`, `Feec.Metric.trace`
- modules: Feec.Algebra.Metric, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge

### Sec §2.8

- cited: `Feec.Counterexamples.LinearizedGravity.not_accel_printed`, `Feec.EinsteinBianchi.planeWave_EB`, `Feec.EinsteinBianchi.planeWave_weyl`, `Feec.LinearizedGravity.IsTT`, `Feec.LinearizedGravity.isTT_iff`, `Feec.LinearizedGravity.tt_accel`, `Feec.TT.ttProj`, `Feec.TT.ttProj_mem`
- modules: Feec.Algebra.TransverseTraceless, Feec.Counterexamples.LinearizedGravity, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.LinearizedGravity.Einstein, Feec.Physics.LinearizedGravity.Gauge, Feec.Physics.LinearizedGravity.PlaneWave

### Sec §3.1

- cited: `Feec.DoubleForm.hodge2`, `Feec.DoubleForm.hodge2_hodge2`, `Feec.DoubleForm.ldual`, `Feec.DoubleForm.rdual`, `Feec.leviCivita`, `Feec.leviCivita3`, `Feec.leviCivita4`
- modules: Feec.Algebra.LeviCivita, Feec.Geometry.Hodge2

### Sec §3.2

- cited: `Feec.DoubleForm.IsWeyl`, `Feec.DoubleForm.finrank_weylSpace`, `Feec.DoubleForm.ldual_eq_rdual`, `Feec.DoubleForm.ldual_eq_rdual_swap`, `Feec.DoubleForm.rdual_rdual`
- modules: Feec.Geometry.Bivector, Feec.Geometry.Hodge2, Feec.Geometry.WeylDecomposition, Feec.Physics.EinsteinBianchi.Nonlinear

### Sec §3.3

- cited: `Feec.DoubleForm.blkE`, `Feec.DoubleForm.eq_ofBlocks_blocks`, `Feec.DoubleForm.ofBlocks`, `Feec.DoubleForm.toMat`
- modules: Feec.Geometry.Bivector, Feec.Geometry.WeylDecomposition, Feec.Physics.EinsteinBianchi.Nonlinear, Feec.Physics.EinsteinBianchi.System

### Sec §3.4

- cited: `Feec.EinsteinBianchi.EBJet`, `Feec.EinsteinBianchi.EBJetSym_surjective`, `Feec.EinsteinBianchi.crossCross`, `Feec.EinsteinBianchi.crossDot`, `Feec.EinsteinBianchi.linBianchi_iff_sym`, `Feec.Models.BoundedDomain.minimal_curl_mem_tsd`, `Feec.Models.BoundedDomain.symm_of_weakCurl_tsd`, `Feec.Models.BoundedDomain.trace_minimal_curl_eq_zero`, `Feec.Models.Euclidean.GradCurl.fourier_mem_constraint_iff`, `Feec.TT.ttProj`, `Feec.TT.ttProj_mem`, `Feec.TT.ttSub`
- modules: Feec.Algebra.MatrixSymbol, Feec.Algebra.TransverseTraceless, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedDomainTSD, Feec.Counterexamples.EveryBallSymTSD, Feec.Fourier.BGGSymbol, Feec.Fourier.GradCurlSymbol, Feec.Fourier.SymCurlSymbol, Feec.Geometry.Bianchi, Feec.Instances.EinsteinBianchiAbsorbing, Feec.Models.BoundedDomain.GradCurl, Feec.Models.BoundedDomain.Interior, Feec.Models.BoundedDomain.SymCurl, Feec.Models.Cube.Absorbing, Feec.Models.Cube.AbsorbingFiniteSpeed, Feec.Models.Cube.AbsorbingTSD, Feec.Models.Euclidean.GradCurl, Feec.Models.Torus.BGG, Feec.Physics.EinsteinBianchi.Fields, Feec.Physics.EinsteinBianchi.Nonlinear, Feec.Physics.EinsteinBianchi.System

### Sec §3.5

- cited: `Feec.EinsteinBianchi.planeWave_EB`, `Feec.EinsteinBianchi.planeWave_weyl`
- modules: Feec.Domain.FiniteSpeed, Feec.Numerics.CrankNicolsonTable, Feec.Physics.EinsteinBianchi.Fields

### Sec §4.1

- cited: `LinearPMap.IsSkewAdjoint`, `LinearPMap.IsSkewAdjoint.isSkewSymmetric`, `LinearPMap.IsSkewSymmetric`, `LinearPMap.adjoint_adjoint`, `LinearPMap.dense_adjoint_domain`, `LinearPMap.isClosed_ker`, `LinearPMap.isSkewAdjoint_iff`, `LinearPMap.mem_graph_iff_of_isClosed`, `LinearPMap.orthogonal_range_eq_ker_adjoint`
- modules: Feec.ForMathlib.LinearPMap.ClosedRange, Feec.ForMathlib.LinearPMap.GraphSpace, Feec.ForMathlib.LinearPMap.Skew

### Sec §4.2

- cited: `Feec.Counterexamples.Fredholm.periodic_not_staticVerdict`, `Feec.Counterexamples.deRham_not_closedRange`, `Feec.Counterexamples.deRham_not_staticVerdict`, `Feec.Counterexamples.euclidean_not_closedRange`, `Feec.Counterexamples.fredholm_not_closedRange`, `Feec.Counterexamples.hasCompactProperty_infiniteDimensional`, `Feec.Counterexamples.not_forall_closedRangeAt_of_finiteDimensional_harmonic`, `Feec.Counterexamples.periodic_not_closedRange`, `Feec.HilbertComplex`, `Feec.HilbertComplex.ClosedRangeAt`, `Feec.HilbertComplex.HasCompactProperty`, `Feec.HilbertComplex.HasCompactProperty.isCompactOperator_resolvent_wave`, `Feec.HilbertComplex.HasCompactPropertyAt`, `Feec.HilbertComplex.HasCompactPropertyAt.closedRangeAt`, `Feec.HilbertComplex.HasCompactPropertyAt.closedRangeAt_of_rel`, `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`, `Feec.HilbertComplex.HasCompactPropertyAt.finiteDimensional_harmonic`, `Feec.HilbertComplex.HasCompactPropertyAt.isClosed_range`, `Feec.HilbertComplex.boundaries`, `Feec.HilbertComplex.boundaries_sup_harmonic`, `Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`, `Feec.HilbertComplex.closure_boundaries_sup_harmonic`, `Feec.HilbertComplex.cohomology`, `Feec.HilbertComplex.cohomologyEquivHarmonic`, `Feec.HilbertComplex.cycles`, `Feec.HilbertComplex.domainComplex`, `Feec.HilbertComplex.domainComplex_closedRangeAt_iff`, `Feec.HilbertComplex.domainSpace`, `Feec.HilbertComplex.dual`, `Feec.HilbertComplex.dual_closedRangeAt_iff`, `Feec.HilbertComplex.exact_iff_harmonic_eq_bot`, `Feec.HilbertComplex.harmonic`, `Feec.HilbertComplex.harmonicToCohomology_surjective_iff`, `Feec.HilbertComplex.harmonic_eq`, `Feec.HilbertComplex.map_domainIncl_harmonic`, `Feec.ShortHilbertComplex.dual`, `Feec.ShortHilbertComplex.ofBounded`
- modules: Feec.Counterexamples.Fredholm, Feec.Counterexamples.NonClosedRangeEuclidean, Feec.Counterexamples.PeriodicFamily, Feec.Counterexamples.Sharpness, Feec.Fourier.ClosedRange, Feec.Fourier.ExteriorSymbol, Feec.HilbertComplex.Basic, Feec.HilbertComplex.Compactness, Feec.HilbertComplex.CompressCompact, Feec.HilbertComplex.DomainComplex, Feec.HilbertComplex.Dual, Feec.HilbertComplex.Hodge, Feec.HilbertComplex.Homology, Feec.HilbertComplex.Short, Feec.HilbertComplex.ShortDual, Feec.Models.Cube.DeRham, Feec.Models.Cube.DeRhamIdentPoincare, Feec.Models.Euclidean.DeRham, Feec.Models.Torus.DeRham, Feec.Operator.Adjoint

### Sec §4.3

- cited: `Feec.Counterexamples.exists_dense_not_isClosed_ker`, `Feec.Counterexamples.not_forall_isClosed_ker`
- modules: Feec.Counterexamples.Ell2, Feec.Evolution.BoundaryLifting, Feec.Evolution.Constrained, Feec.Evolution.Duhamel, Feec.Evolution.Forcing, Feec.Evolution.Solution, Feec.Evolution.WellPosed, Feec.Examples.NonVacuity, Feec.HilbertComplex.InvariantCore, Feec.HilbertComplex.Reducing

### Sec §4.4

- cited: `Feec.BGG.WaveData.Solution`, `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.Evolution.IsStrongSolution`, `Feec.HodgeWave.IsClassicalWeakSolution`, `Feec.HodgeWave.IsWeakSolution.unique`, `Feec.ShortHilbertComplex`
- modules: Feec.Counterexamples.ClassicalRegularity, Feec.Evolution.Solution, Feec.Examples.NonVacuity, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ApproxFEEC, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.Approximation.Crown, Feec.HilbertComplex.Approximation.DissipFEEC, Feec.HilbertComplex.Approximation.SkewFEEC, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.Dirac, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.Short, Feec.HilbertComplex.Window, Feec.Instances.CrownNonVacuity, Feec.Instances.EinsteinBianchi, Feec.Instances.Maxwell

### Sec §4.5

- cited: `Feec.Variational.InfSup`, `Feec.Variational.SeparatingRight`, `Feec.Variational.infSup_iff_forall_exists_norm_le_one`
- modules: Feec.Variational.BabuskaNecas, Feec.Variational.InfSup

### Sec §4.6

- cited: `Feec.HilbertComplex.ConformingFamily`, `Feec.HilbertComplex.ConstrainedFEEC`, `Feec.HilbertComplex.HasCompactPropertyAt`, `Feec.HilbertComplex.Subcomplex`, `Feec.HilbertComplex.Subcomplex.CochainProjection.infSup_mixedForm`, `Feec.HilbertComplex.Subcomplex.graphSub`, `Feec.HilbertComplex.Subcomplex.toHilbertComplex`, `Feec.HilbertComplex.infSup_mixedForm`, `Feec.HodgeWave.IsApproximating`, `Feec.HodgeWave.IsSemidiscreteSolution`, `Feec.HodgeWave.IsSemidiscreteSolution.norm_sub_le`, `Feec.HodgeWave.exists_isSemidiscreteSolution`, `Feec.HodgeWave.norm_sub_ellipticProjection_le`, `Feec.Koszul.IsSubcomplex`
- modules: Feec.Algebra.PolynomialForm, Feec.Counterexamples.ClassicalRegularity, Feec.Counterexamples.Sharpness, Feec.HilbertComplex.Approximation.ApproxComplex, Feec.HilbertComplex.Approximation.ApproxComplexCrime, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ConformingFamily, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Convergence, Feec.HilbertComplex.Approximation.Crown, Feec.HilbertComplex.Approximation.GraphApprox, Feec.HilbertComplex.Approximation.MixedError, Feec.HilbertComplex.Approximation.SemidiscreteWave, Feec.HilbertComplex.Approximation.Spectral, Feec.HilbertComplex.Approximation.Subcomplex, Feec.HilbertComplex.Compactness, Feec.HilbertComplex.Mixed, Feec.Instances.CrownNonVacuity, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiSpectral, Feec.Instances.Maxwell, Feec.Models.Cube.WhitneyApprox

### Sec §4.7

- cited: `Feec.FiniteElement.IsUnisolvent`, `Feec.FiniteElement.comp_eq_of_dof`, `Feec.FiniteElement.interp`, `Feec.FiniteElement.interp_comp_eq`, `Feec.FiniteElement.isUnisolvent_iff_forall_eq_zero`, `Feec.HilbertComplex.ConstrainedFEEC`, `Feec.HilbertComplex.Subcomplex.CochainProjection`, `Feec.Koszul.eq_koszul_add_extDeriv`, `Feec.Koszul.eq_zero_of_eq_koszul_of_eq_extDeriv`, `Feec.Koszul.exists_extDeriv_eq_of_extDeriv_eq_zero`, `Feec.Koszul.exists_koszul_eq_of_koszul_eq_zero`, `Feec.Koszul.extDeriv`, `Feec.Koszul.extDeriv_extDeriv`, `Feec.Koszul.extDeriv_koszul_add_koszul_extDeriv`, `Feec.Koszul.extDeriv_koszul_add_koszul_extDeriv_of_isHomogeneous`, `Feec.Koszul.extDeriv_mem_homForm`, `Feec.Koszul.extDeriv_mem_polyForm`, `Feec.Koszul.extDeriv_mem_polyFormMinus`, `Feec.Koszul.extDeriv_mem_polyFormMinus_of_mem_polyFormMinus`, `Feec.Koszul.extDeriv_mem_polyForm_of_mem_polyFormMinus`, `Feec.Koszul.extDeriv_mem_polyForm_sub_one_of_mem_polyFormMinus`, `Feec.Koszul.homForm`, `Feec.Koszul.homForm_le_sup`, `Feec.Koszul.koszul`, `Feec.Koszul.koszul_koszul`, `Feec.Koszul.koszul_mem_homForm`, `Feec.Koszul.koszul_mem_polyForm`, `Feec.Koszul.polyForm`, `Feec.Koszul.polyFormMinus`, `Feec.Koszul.polyFormMinus_le_polyForm`
- modules: Feec.Algebra.Koszul, Feec.Algebra.PolynomialForm, Feec.Algebra.Proxy3, Feec.FiniteElement.Dof, Feec.HilbertComplex.Approximation.CochainProjection, Feec.HilbertComplex.Approximation.ConstrainedFEEC

### Sec §4.8

- cited: `Feec.Counterexamples.MixedWave.not_isMixedWeak`, `Feec.HodgeWave.IsMixedWeak`, `Feec.HodgeWave.IsMixedWeak.isSecondOrderWeak`, `Feec.HodgeWave.IsSecondOrderWeak`, `Feec.HodgeWave.IsSecondOrderWeak.exists_isMixedWeak`, `Feec.HodgeWave.IsWeakSolution`, `Feec.HodgeWave.not_isMixedWeak_of_inner_ne_zero`
- modules: Feec.Counterexamples.MixedWave, Feec.HilbertComplex.HodgeWave, Feec.HilbertComplex.SecondOrder

### Sec §4.9

- cited: `Feec.HodgeWave.IsMixedWeak3`, `Feec.HodgeWave.IsMixedWeak3.eliminate`, `Feec.HodgeWave.IsMixedWeak3.eliminate_of_hasDerivWithinAt`, `Feec.Instances.EuclideanBand.maxwell_euclidean_band`
- modules: Feec.HilbertComplex.Reducing, Feec.HilbertComplex.SecondOrder, Feec.Instances.EuclideanBand, Feec.Instances.Maxwell, Feec.Instances.MaxwellMedia, Feec.Physics.Maxwell.Constraints, Feec.Physics.Maxwell.Forms, Feec.Physics.Maxwell.Media

### Sec §4.10

- cited: `Feec.Counterexamples.BallEigenDense.coreSub_le_stationary_ball3_iff`, `Feec.Counterexamples.PolynomialForms.extDeriv_not_mem_polyFormMinus`, `Feec.Counterexamples.PolynomialForms.grad_sq_not_whitney`, `Feec.Counterexamples.PolynomialForms.not_isTensorSubcomplex_printed`, `Feec.Counterexamples.PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus`, `Feec.Koszul.IsSubcomplex`, `Feec.Koszul.Proxy3.koszul_empty`, `Feec.Koszul.Proxy3.vec1_extDeriv`, `Feec.Koszul.Proxy3.vec1_koszul`, `Feec.Koszul.Proxy3.vec2_extDeriv`, `Feec.Koszul.Proxy3.vec2_koszul`, `Feec.Koszul.Proxy3.vol_extDeriv`, `Feec.Koszul.extDeriv_mem_polyFormMinus`, `Feec.Koszul.extDeriv_mem_polyFormMinus_of_mem_polyForm`, `Feec.Koszul.extDeriv_mem_polyFormMinus_of_mem_polyFormMinus`, `Feec.Koszul.extDeriv_mem_tensorForm_reduced`, `Feec.Koszul.extDeriv_not_mem_polyFormMinus_of_koszul_eq_zero`, `Feec.Koszul.isSubcomplex_polyForm`, `Feec.Koszul.isTensorSubcomplex_alt`, `Feec.Koszul.isTensorSubcomplex_polyForm`, `Feec.Koszul.map_extDeriv_polyForm_le_polyFormMinus_iff`, `Feec.Koszul.map_extDeriv_polyForm_le_polyForm_iff`, `Feec.Koszul.polyFormMinus`, `Feec.Koszul.polyFormMinus_lt_polyForm_one`, `Feec.Koszul.polyForm_lt_polyFormMinus`, `Feec.Koszul.tensorForm_reduced_iff`, `Feec.Models.BoundedDomain.eq_zero_of_symm_of_trace_of_cross`, `Feec.Models.Box.Mirror.existsUnique_memBox`, `Feec.Models.Box.Mirror.exists_nonstationaryBox`, `Feec.Models.Box.Mirror.invariantCore_eqBox`, `Feec.Models.Box.Mirror.propagatesBox`, `Feec.Models.Box.Mirror.reducingSubcomplexBox`, `Feec.Models.Box.forward_iff`, `Feec.Models.Box.mem_invariantCore_iff`, `Feec.Models.Box.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Models.Cube.Ident.forward_iff_pi`, `Feec.Models.Cube.Ident.mem_invariantCore_iff`, `Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff_pi`, `Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.Mirror.existsUnique_memCube_pi`, `Feec.Models.Cube.Mirror.existsUnique_memCube_trace`, `Feec.Models.Cube.Mirror.existsUnique_memCube_unit`, `Feec.Models.Cube.Mirror.existsUnique_memQ`, `Feec.Models.Cube.Mirror.existsUnique_memQ_trace`, `Feec.Models.Cube.Mirror.exists_nonstationary`, `Feec.Models.Cube.Mirror.exists_nonstationaryCube`, `Feec.Models.Cube.Mirror.exists_nonstationaryQ`, `Feec.Models.Cube.Mirror.invariantCore_eq`, `Feec.Models.Cube.Mirror.invariantCore_eqCube`, `Feec.Models.Cube.Mirror.invariantCore_eqQ`, `Feec.Models.Cube.Mirror.propagates`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Cube.Mirror.propagatesQ`, `Feec.Models.Cube.Mirror.reducingSubcomplex`, `Feec.Models.Cube.Mirror.reducingSubcomplexCube`, `Feec.Models.Cube.Mirror.reducingSubcomplexQ`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev`, `Feec.Models.Cube.Parity.complex`, `Feec.Models.Cube.Parity.exists_linearIndependent_invariantCore`, `Feec.Models.Cube.Parity.forward_iff`, `Feec.Models.Cube.Parity.forward_torus_iff`, `Feec.Models.Cube.Parity.forward_tsd_iff`, `Feec.Models.Cube.Parity.invariantCore_ne_bot`, `Feec.Models.Cube.Parity.mem_invariantCore_iff`, `Feec.Models.Cube.Parity.mem_invariantCore_torus_iff`, `Feec.Models.Cube.Parity.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Parity.not_finiteDimensional_invariantCore`, `Feec.Models.Cube.RowWise.forward_iff`, `Feec.Models.Cube.RowWise.mem_invariantCore_iff`, `Feec.Models.Cube.RowWise.mem_invariantCore_tsd_iff`, `Feec.Models.Euclidean.GradCurl.fourier_mem_constraint_iff`, `Feec.Models.Torus.BGG.verdict`, `Feec.ShortHilbertComplex.IsReducedSolution`, `Feec.ShortHilbertComplex.IsReducedSolution.mem_ker_adjoint`, `Feec.ShortHilbertComplex.existsUnique_reducedSolution`, `Feec.ShortHilbertComplex.existsUnique_reducedSolution_divFree`, `Feec.ShortHilbertComplex.isReducedSolution_of_isStrongSolution`, `Feec.ShortHilbertComplex.isStrongSolution_of_isReducedSolution`, `Feec.ShortHilbertComplex.reducedSolution_of_exists`
- modules: Feec.Algebra.MatrixSymbol, Feec.Algebra.PolynomialForm, Feec.Algebra.Proxy3, Feec.Counterexamples.BallEigenDense, Feec.Counterexamples.BallEigenfields, Feec.Counterexamples.BoundedBGG, Feec.Counterexamples.BoundedDomainTSD, Feec.Counterexamples.BoundedSymTSD, Feec.Counterexamples.BoxStationary, Feec.Counterexamples.CubeStationary, Feec.Counterexamples.NonClosedRangeEuclidean, Feec.Counterexamples.PolynomialForms, Feec.Counterexamples.Sharpness, Feec.Domain.Affine, Feec.Domain.ConstCoeffOp, Feec.Domain.DiagonalPullback, Feec.Domain.FiniteSpeed, Feec.Domain.Mollify, Feec.Domain.Obstruction, Feec.Fourier.Euclidean, Feec.Fourier.FibreReducing, Feec.Fourier.GradCurlSymbol, Feec.Fourier.Reality, Feec.Fourier.SymbolComplex, Feec.Fourier.Torus, Feec.Fourier.TorusSpectral, Feec.Fourier.TorusWeak, Feec.Fourier.Weak, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.ApproxFEEC, Feec.HilbertComplex.Approximation.ConstrainedFEEC, Feec.HilbertComplex.Approximation.Crown, Feec.HilbertComplex.Approximation.DissipFEEC, Feec.HilbertComplex.Approximation.SkewFEEC, Feec.HilbertComplex.CompressCompact, Feec.HilbertComplex.Density, Feec.HilbertComplex.Equivariant, Feec.HilbertComplex.InvariantCore, Feec.HilbertComplex.InvariantCoreSpectral, Feec.HilbertComplex.Reality, Feec.HilbertComplex.ReducedSystem, Feec.HilbertComplex.Reducing, Feec.HilbertComplex.RestrictScalars, Feec.HilbertComplex.Transport, Feec.Instances.CrownNonVacuity, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiAbsorbing, Feec.Instances.Maxwell, Feec.Models.BoundedDomain.Compactness, Feec.Models.BoundedDomain.Density, Feec.Models.BoundedDomain.GradCurl, Feec.Models.BoundedDomain.Interior, Feec.Models.BoundedDomain.InvariantCore, Feec.Models.BoundedDomain.MovingTSD, Feec.Models.Box.EigenDense, Feec.Models.Box.Mirror, Feec.Models.Box.RowWise, Feec.Models.Cube.Absorbing, Feec.Models.Cube.AbsorbingTSD, Feec.Models.Cube.AbsorbingTrace, Feec.Models.Cube.Basic, Feec.Models.Cube.DeRham, Feec.Models.Cube.DeRhamIdent, Feec.Models.Cube.DeRhamIdentExt, Feec.Models.Cube.DeRhamIdentForms, Feec.Models.Cube.DeRhamIdentTrunc, Feec.Models.Cube.EigenDense, Feec.Models.Cube.Ident, Feec.Models.Cube.Inhomogeneous, Feec.Models.Cube.InhomogeneousError, Feec.Models.Cube.Mirror, Feec.Models.Cube.MirrorBase, Feec.Models.Cube.MirrorDirichlet, Feec.Models.Cube.MirrorExt, Feec.Models.Cube.MirrorTrace, Feec.Models.Cube.MirrorWaveRegularity, Feec.Models.Cube.Parity, Feec.Models.Cube.Reflection, Feec.Models.Cube.RowWiseIdent, Feec.Models.Cube.Smoothing, Feec.Models.Cube.Sobolev, Feec.Models.Cube.Static, Feec.Models.Euclidean.GradCurl, Feec.Models.StarShaped.EigenDense, Feec.Models.Torus.BGG, Feec.Models.Torus.GradCurl, Feec.Numerics.PlaneWaveCube, Feec.Physics.EinsteinBianchi.Constraints, Feec.Semigroup.Spectral

### Sec §4.11

- cited: `Feec.Counterexamples.BallSymTSD.not_propagates`, `Feec.Counterexamples.BallSymTSD.tsd_not_propagates`, `Feec.Counterexamples.BoundedSymTSD.diagnosis`, `Feec.Counterexamples.BoundedSymTSD.diagnosis_hessCurlMax`, `Feec.Counterexamples.BoundedSymTSD.not_dense_hessCurlMax`, `Feec.Counterexamples.BoundedSymTSD.not_finiteDimensional_obstruction`, `Feec.Counterexamples.BoundedSymTSD.not_projection_magnetic`, `Feec.Counterexamples.BoundedSymTSD.not_starProjection_mem_adjoint_domain`, `Feec.Counterexamples.BoundedSymTSD.not_starProjection_mem_wave_domain_hessCurlMax`, `Feec.Counterexamples.EveryBallSymTSD.tsd_not_propagates`, `Feec.Models.BoundedDomain.hessCurlMax`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memQ`, `Feec.Models.Cube.MirrorSym.exists_nonstationary`, `Feec.Models.Cube.MirrorSym.exists_nonstationaryCube`, `Feec.Models.Cube.MirrorSym.exists_nonstationaryQ`, `Feec.Models.Cube.MirrorSym.invariantCore_eq`, `Feec.Models.Cube.MirrorSym.invariantCore_eqCube`, `Feec.Models.Cube.MirrorSym.invariantCore_eqQ`, `Feec.Models.Cube.MirrorSym.propagates`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Cube.MirrorSym.propagatesQ`, `Feec.Models.Cube.MirrorSym.reducingSubcomplex`, `Feec.Models.Cube.MirrorSym.reducingSubcomplexCube`, `Feec.Models.Cube.MirrorSym.reducingSubcomplexQ`, `Feec.Models.Torus.SymCurl.adjoint_d`, `Feec.Models.Torus.SymCurl.closedRangeAt`, `Feec.Models.Torus.SymCurl.complex`, `Feec.Models.Torus.SymCurl.dual_closedRangeAt`, `Feec.Models.Torus.SymCurl.tsd_propagates`
- modules: Feec.Algebra.MatrixSymbol, Feec.Counterexamples.BallSymTSD, Feec.Counterexamples.BoundedBGG, Feec.Counterexamples.BoundedSymTSD, Feec.Counterexamples.EveryBallSymTSD, Feec.Counterexamples.Sharpness, Feec.Fourier.Euclidean, Feec.Fourier.FibreReducing, Feec.Fourier.SymCurlSymbol, Feec.Fourier.SymbolComplex, Feec.Fourier.Torus, Feec.HilbertComplex.InvariantCore, Feec.HilbertComplex.InvariantCoreSpectral, Feec.HilbertComplex.Reducing, Feec.Models.BoundedDomain.SymCurl, Feec.Models.BoundedDomain.SymDualGeneral, Feec.Models.Cube.MirrorSym, Feec.Models.Euclidean.SymCurl, Feec.Models.Torus.SymCurl

### Sec §4.12

- cited: `Feec.HilbertComplex.ReducingFamily.feec`, `Feec.HilbertComplex.SpectralFamily`, `Feec.Instances.EinsteinBianchi.mirrorFEEC`, `Feec.Instances.EinsteinBianchi.torusFEEC`, `Feec.Instances.EuclideanBand.einsteinBianchi_euclidean_band`, `Feec.Instances.EuclideanBand.maxwell_euclidean_band`
- modules: Feec.Fourier.SpectralGalerkin, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.Spectral, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiSobolev, Feec.Instances.EinsteinBianchiSpectral, Feec.Instances.EuclideanBand

### Sec §4.13

- cited: `Feec.HilbertComplex.ReducingFamily.feec`, `Feec.HilbertComplex.SpectralFamily`, `Feec.Instances.EuclideanBand.einsteinBianchi_euclidean_band`, `Feec.Instances.EuclideanBand.maxwell_euclidean_band`
- modules: Feec.Fourier.SpectralGalerkin, Feec.HilbertComplex.Approximation.ApproxConforming, Feec.HilbertComplex.Approximation.Spectral, Feec.Instances.EinsteinBianchiSobolev, Feec.Instances.EinsteinBianchiSpectral, Feec.Instances.EuclideanBand

### Sec §5.1

- cited: `Feec.BGG.Data`, `Feec.BGG.Data.Γ_eq_segment_Γ`, `Feec.BGG.Hilb`, `Feec.BGG.Hilb.Hyps`, `Feec.BGG.Hilb.Wcheck`, `Feec.BGG.Hilb.existsUnique_isReduced`, `Feec.BGG.Hilb.existsUnique_multiplier`, `Feec.BGG.Hilb.isSaddle_iff_isReduced`, `Feec.BGG.Hilb.jW_spec`, `Feec.BGG.Hilb.mem_Z1_iff`, `Feec.BGG.Hilb.poincare_T`, `Feec.BGG.Hilb.poincare_Γ`, `Feec.BGG.Hilb.tripleNorm`, `Feec.BGG.Hilb.tripleNorm_definite`, `Feec.BGG.Hilb.tripleNorm_spec`, `Feec.BGG.HilbertData`, `Feec.BGG.HilbertData.twistComplex`, `Feec.BGG.Segment`, `Feec.BGG.Segment.D0`, `Feec.BGG.Segment.D1`, `Feec.BGG.Segment.D1_D0`, `Feec.BGG.Segment.ExactBot`, `Feec.BGG.Segment.ExactTop`, `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.Γ`, `Feec.BGG.Stability`, `Feec.BGG.WaveData.Wcheck`, `Feec.EinsteinBianchi.WaveFEM.negNorm_le_tripleNorm`, `Feec.Models.Cube.WeakSymmetry.bggHilb_hyps`, `Feec.Models.Cube.WeakSymmetry.bggHyps`
- modules: Feec.Counterexamples.BoundedBGG, Feec.Domain.BGG, Feec.Domain.HessianBGG, Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.Basic, Feec.HilbertComplex.BGG.Derived, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.BGG.ToComplex, Feec.HilbertComplex.BGG.Twisted, Feec.HilbertComplex.BGG.WeakSymmetry, Feec.Instances.EinsteinBianchiGauss, Feec.Models.BoundedDomain.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Cube.MirrorWeakSymmetryComplex, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryComplex, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG, Feec.Physics.EinsteinBianchi.WaveFEM

### Sec §5.2

- cited: `Feec.BGG.Discrete`, `Feec.BGG.Discrete.Compatible`, `Feec.BGG.Discrete.exact_mid_h`, `Feec.BGG.Discrete.exists_sub_S0h_eq`, `Feec.BGG.IsMixedSolution`, `Feec.BGG.anticomm_of_comm_proj`, `Feec.BGG.exists_discreteSolution_regular`, `Feec.BGG.exists_of_exact_rows`, `Feec.BGG.mixedForm_bijective`, `Feec.BGG.surjective_of_comp_eq`
- modules: Feec.Counterexamples.DiscreteBGG, Feec.HilbertComplex.BGG.Discrete, Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.EinsteinBianchiGauss

### Sec §5.3

- cited: `Feec.EinsteinBianchi.StaticFEM.staticFEM`, `Feec.EinsteinBianchi.StaticFEM.staticFEM_cube`, `Feec.FiniteElement.PolySeq.bggS0h`, `Feec.FiniteElement.PolySeq.bggS1h`, `Feec.FiniteElement.PolySeq.lagrangeP2`, `Feec.FiniteElement.PolySeq.lowestOrder`, `Feec.FiniteElement.PolySeq.wsGlobal₀_surjective`, `Feec.FiniteElement.PolySeq.wsPiecewise`, `Feec.FiniteElement.comp_eq_of_dof`, `Feec.FiniteElement.coordWedgeField`, `Feec.FiniteElement.extDeriv_coordWedgeField`, `Feec.Models.Cube.FEM.tableRows_common_smoother`, `Feec.Models.Cube.WeakSymmetry.CurlPotential`, `Feec.Models.Cube.WeakSymmetry.eq_zero_of_dPiecewise_tensor_eq_zero`
- modules: Feec.FiniteElement.Dof, Feec.FiniteElement.PolyComplex, Feec.FiniteElement.TensorElement, Feec.FiniteElement.WeakSymmetryMaps, Feec.HilbertComplex.BGG.Discrete, Feec.Models.Cube.MirrorWeakSymmetryComplex, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.PolyFiniteElementConvergence, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryComplex, Feec.Models.Cube.WeakSymmetryEstimates, Feec.Models.Cube.WeakSymmetryFEM, Feec.Models.Cube.WeakSymmetryTangentialRate, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.StaticFEM, Feec.Physics.EinsteinBianchi.Unconditional, Feec.Physics.EinsteinBianchi.WaveFEMTangential, Feec.Physics.EinsteinBianchi.WaveFEMTangentialCube

### Sec §6.1

- cited: `Feec.BGG.ExactWave`, `Feec.BGG.WaveData.MultiplierSolution`, `Feec.BGG.WaveData.MultiplierSolution.unique`, `Feec.BGG.WaveData.Solution`, `Feec.BGG.WaveData.Solution.hasDerivWithinAt_energy`, `Feec.BGG.WaveData.Solution.unique`, `Feec.BGG.WaveData.Wcheck`, `Feec.Counterexamples.BoundedBGG.bggComplex_verdict`, `Feec.Instances.EinsteinBianchi.thesisTSD`, `Feec.Models.BoundedDomain.bggComplex_weakEqs_of_isStrongSolution`, `Feec.Models.Cube.MirrorWeakSymmetry.TSDDatum.exactWave`
- modules: Feec.Counterexamples.BoundedBGG, Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.TimeDependent, Feec.HilbertComplex.ShortDual, Feec.Instances.EinsteinBianchi, Feec.Models.BoundedDomain.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Cube.WeakSymmetryWave, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure, Feec.Physics.EinsteinBianchi.MatrixModel, Feec.Physics.EinsteinBianchi.WaveFEM, Feec.Physics.EinsteinBianchi.WaveFEMRegularity

### Sec §6.2

- cited: `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.Discrete.infSup_shiftedForm_h`, `Feec.BGG.Discrete.strang_of_isEllipticProjection`, `Feec.BGG.Discrete.strang_rate_of_regularPotential`, `Feec.BGG.Discrete.strang_shiftedForm_h`, `Feec.BGG.DiscreteSolution`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection_L2`, `Feec.BGG.ExactWave.exists_discreteSolution_rate`, `Feec.BGG.ExactWave.exists_discreteSolution_rate_harm`, `Feec.BGG.HarmonicStability.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.HarmonicStability.strang_shiftedForm_h`, `Feec.BGG.IsEllipticProjection`, `Feec.BGG.IsEllipticProjection.galerkin`, `Feec.BGG.discreteSkewForm`, `Feec.BGG.ellipticProjection`, `Feec.BGG.eq_zero_of_isEllipticProjection`, `Feec.BGG.existsUnique_isEllipticProjection`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.exists_discreteSolution_norm_sub_le_L2`, `Feec.BGG.exists_discreteSolution_norm_sub_le_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection_L2`, `Feec.BGG.projected_compatible_phi_iff`, `Feec.BGG.projected_compatible_u`, `Feec.BGG.projected_compatible_u_L2`, `Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_converges`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_rate`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_ellipticProjection_rate_tr`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_ellipticProjection_rate_trS1`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr`
- modules: Feec.Counterexamples.ConstrainedEvolution, Feec.HilbertComplex.Approximation.ApproxComplexCrime, Feec.HilbertComplex.BGG.DiscreteWave, Feec.HilbertComplex.BGG.EllipticProjection, Feec.HilbertComplex.BGG.Harmonic, Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiFEMComplex, Feec.Instances.EinsteinBianchiFEMCubeEll, Feec.Instances.EinsteinBianchiFEMDefect, Feec.Instances.EinsteinBianchiFEMElliptic, Feec.Instances.EinsteinBianchiFEMGenerator, Feec.Instances.EinsteinBianchiFEMMirror, Feec.Instances.EinsteinBianchiFEMMirrorEll, Feec.Instances.EinsteinBianchiGauss, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.MirrorWeakSymmetryFEM, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Cube.WeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetryTangentialRate, Feec.Models.Cube.WeakSymmetryWave, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure, Feec.Physics.EinsteinBianchi.WaveFEM, Feec.Physics.EinsteinBianchi.WaveFEMTangential

### Sec §6.3

- cited: `Feec.BGG.ExactWave`, `Feec.Counterexamples.BoundedBGG.bggComplex_B_not_symm`, `Feec.Counterexamples.BoundedBGG.bggComplex_not_propagate`, `Feec.Counterexamples.BoundedBGG.bggComplex_verdict`, `Feec.EinsteinBianchi.BoundedConvergence.tendsto_of_isStrongSolution`, `Feec.EinsteinBianchi.BoundedConvergence.tendsto_of_mem_wave_domain`, `Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`, `Feec.EinsteinBianchi.BoundedFailure.waveFEM_converges_to_non_tsd_of_isRateApproximable`, `Feec.EinsteinBianchi.WaveFEM.bgg_wave_existsUnique`, `Feec.EinsteinBianchi.WaveFEM.gamma_equiv_hessMin`, `Feec.EinsteinBianchi.WaveFEM.negNorm_le_tripleNorm`, `Feec.EinsteinBianchi.WaveFEM.not_isClosed_range_B`, `Feec.EinsteinBianchi.WaveFEM.waveFEM`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_cube`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_of_mem_domain`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_of_mem_domain_of_orbit`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_tr`, `Feec.FiniteElement.LocalElement.dPiecewise_mem_globalSpacePartial_bcFacets`, `Feec.FiniteElement.PolySeq.lagrangeP2`, `Feec.FiniteElement.PolySeq.lagrangeP2_VPartial_bcFacets_ne_bot`, `Feec.FiniteElement.PolySeq.lowestOrder`, `Feec.Instances.EinsteinBianchi.MirrorFEMApprox.Verdict`, `Feec.Instances.EinsteinBianchi.StandardCubeApprox.Verdict`, `Feec.Instances.EinsteinBianchi.StandardCubeVerdict`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_waveFEM`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_waveFEM_rate`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_waveFEM_rate_sobolev`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_thesisCube`, `Feec.Instances.EinsteinBianchi.mirrorFEMApprox_verdict`, `Feec.Instances.EinsteinBianchi.not_isReducing_thesisCube`, `Feec.Instances.EinsteinBianchi.not_isReducing_thesisTSD`, `Feec.Instances.EinsteinBianchi.standardCubeApprox_verdict`, `Feec.Instances.EuclideanBand.ebApprox_isReducing`, `Feec.Models.BoundedDomain.bggComplex`, `Feec.Models.BoundedDomain.bggComplex_divFree_propagates`, `Feec.Models.Cube.FEM.tableRows_common_smoother`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_converges`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_rate`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`, `Feec.Models.Cube.WeakSymmetry.cubeWave_converges`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate'`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_sobolev`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_sobolev_of_one_le`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr`, `Feec.Models.Euclidean.BGG.reducingSubcomplex`, `Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Euclidean.BGG.tsd_propagates`, `Feec.Models.Euclidean.BGG.tsd_propagates_neg`, `Feec.Models.Euclidean.BGG.waveGroup_mem`, `Feec.Models.Torus.BGG.closedRangeAt`, `Feec.Models.Torus.BGG.hodge`, `Feec.Models.Torus.BGG.reducingSubcomplex`, `Feec.Models.Torus.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_propagates`, `Feec.Models.Torus.BGG.tsd_propagates_neg`, `Feec.Models.Torus.BGG.verdict`, `Feec.Models.Torus.BGG.waveGroup_mem`
- modules: Feec.Counterexamples.BoundedBGG, Feec.FiniteElement.PolyComplex, Feec.FiniteElement.PolyElementMixed, Feec.Fourier.BGGSymbol, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiFEM, Feec.Instances.EinsteinBianchiFEMComplex, Feec.Instances.EinsteinBianchiFEMCube, Feec.Instances.EinsteinBianchiFEMCubeEll, Feec.Instances.EinsteinBianchiFEMDefect, Feec.Instances.EinsteinBianchiFEMMirror, Feec.Instances.EinsteinBianchiFEMMirrorEll, Feec.Instances.EinsteinBianchiGauss, Feec.Instances.EuclideanBand, Feec.Models.BoundedDomain.BGG, Feec.Models.BoundedDomain.Hessian, Feec.Models.Cube.DeRhamPartialFEM, Feec.Models.Cube.MirrorBGG, Feec.Models.Cube.MirrorWaveRegularity, Feec.Models.Cube.MirrorWeakSymmetryComplex, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.MirrorWeakSymmetryFEM, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Cube.PolyFiniteElementConvergence, Feec.Models.Cube.RegularDecomposition, Feec.Models.Cube.WeakSymmetryConvergence, Feec.Models.Cube.WeakSymmetrySobolevRate, Feec.Models.Cube.WeakSymmetryTangentialRate, Feec.Models.Cube.WeakSymmetryWave, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG, Feec.Physics.EinsteinBianchi.BoundedConvergence, Feec.Physics.EinsteinBianchi.BoundedFailure, Feec.Physics.EinsteinBianchi.MatrixModel, Feec.Physics.EinsteinBianchi.Unconditional, Feec.Physics.EinsteinBianchi.WaveFEM, Feec.Physics.EinsteinBianchi.WaveFEMRegularity, Feec.Physics.EinsteinBianchi.WaveFEMTangential

### Ch 1

- modules: Feec.Algebra.PolynomialForm

### Ch 2

- modules: Feec.Algebra.Metric, Feec.Geometry.AlgebraicCurvature

### Ch 3

- cited: `Feec.EinsteinBianchi.EBJet`, `Feec.EinsteinBianchi.dWeyl`
- modules: Feec.Physics.EinsteinBianchi.System

### Ch 4

- cited: `Feec.Instances.EinsteinBianchi.einsteinBianchi_constrainedFEEC_summary`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_summary`
- modules: Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiFEM

### Ch 5

- named: `Feec.BGG.Discrete.Compatible`, `Feec.BGG.Discrete.errorConst`, `Feec.BGG.IsMixedSolution`
- old: Feec.Ch5.Discrete.Disc.C55, Feec.Ch5.Discrete.Disc.Hyp54, Feec.Ch5.Discrete.Sys56
- modules: Feec.Counterexamples.BoundedBGG, Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.WeakSymmetry, Feec.Instances.EinsteinBianchi, Feec.Models.BoundedDomain.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG

### Ch 6

- named: `Feec.BGG.DiscreteSolution`, `Feec.BGG.DiscreteSolution.norm_sub_le_of_ellipticProjection`, `Feec.BGG.WaveData.MultiplierSolution`, `Feec.BGG.WaveData.Solution`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.BGG.norm_sub_le_mul_of_ellipticProjection`, `Feec.BGG.norm_sub_le_of_ellipticProjection`, `Feec.Models.Cube.MirrorBGG.propagatesQ`, `Feec.Variational.norm_sub_le_of_projected_error`
- old: Feec.Ch6.ContData.Sol61, Feec.Ch6.ContData.Sol62, Feec.Ch6.Sol63, Feec.Ch6.ch6_convergence, Feec.Ch6.ch6_convergence_Sol63, Feec.Ch6.ch6_convergence_rate, Feec.Repair.C417.ch6_corrected, Feec.Repair.C67.ch6_convergence_projected
- cited: `Feec.Counterexamples.BoundedBGG.bggComplex_invariantCore_propagates`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_approxFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_constrainedFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_mirror_constrainedFEEC_sobolev`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_approxFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_constrainedFEEC`, `Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_constrainedFEEC_sobolev`, `Feec.Instances.EinsteinBianchi.mirrorFEEC`, `Feec.Instances.EinsteinBianchi.torusFEEC`, `Feec.Instances.EuclideanBand.einsteinBianchi_euclidean_band`, `Feec.Models.Cube.MirrorBGG.existsUnique_mem`, `Feec.Models.Cube.MirrorBGG.existsUnique_memQ`, `Feec.Models.Cube.MirrorBGG.exists_nonstationary`, `Feec.Models.Cube.MirrorBGG.exists_nonstationaryQ`, `Feec.Models.Cube.MirrorBGG.invariantCore_eq`, `Feec.Models.Cube.MirrorBGG.invariantCore_eqQ`, `Feec.Models.Cube.MirrorBGG.propagates`, `Feec.Models.Cube.MirrorBGG.propagatesQ`, `Feec.Models.Cube.MirrorBGG.reducingSubcomplex`, `Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ`, `Feec.Models.Cube.MirrorBGG.tsd_of_mem_tsdQ`, `Feec.Models.Cube.MirrorWeakSymmetry.TSDDatum.exactWave`, `Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_rate_tsd`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`
- modules: Feec.Counterexamples.BoundedBGG, Feec.Fourier.BGGSymbol, Feec.HilbertComplex.BGG.TimeDependent, Feec.Instances.EinsteinBianchi, Feec.Instances.EinsteinBianchiSobolev, Feec.Instances.EinsteinBianchiSpectral, Feec.Instances.EuclideanBand, Feec.Models.BoundedDomain.BGG, Feec.Models.Cube.MirrorBGG, Feec.Models.Cube.MirrorWaveRegularity, Feec.Models.Cube.MirrorWeakSymmetryConvergence, Feec.Models.Cube.MirrorWeakSymmetryTSD, Feec.Models.Euclidean.BGG, Feec.Models.Torus.BGG

### Ch 7

- cited: `Feec.Counterexamples.BoundedBGG.thesisComplex_B_not_symm`, `Feec.Counterexamples.BoundedBGG.thesisComplex_reduced_B_not_symm`, `Feec.HilbertComplex.DissipFEEC.crankNicolson`, `Feec.HilbertComplex.SkewFEEC.norm_crankNicolson_pow_apply`, `Feec.Instances.Corollaries.maxwell_fullyDiscrete`, `Feec.Instances.FullyDiscrete.einsteinBianchi_mirror_crankNicolson`, `Feec.Instances.FullyDiscrete.einsteinBianchi_mirror_crankNicolson_rate`, `Feec.Instances.FullyDiscrete.maxwell_cubePEC_crankNicolson`, `Feec.Instances.FullyDiscrete.maxwell_cubePMC_crankNicolson`, `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD`, `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.Smooth.whitney_cn_error_monitors_le`, `Feec.Models.Cube.Inhomogeneous.whitney_cn_error_le`, `Feec.Models.Cube.Inhomogeneous.whitney_cn_monitors_le`, `Feec.Models.Cube.Mirror.existsUnique_memCube_unit`, `Feec.Numerics.CrankNicolson.amplitudeB`, `Feec.Numerics.CrankNicolson.amplitudeE`, `Feec.Numerics.CrankNicolson.cellCount_table`, `Feec.Numerics.CrankNicolson.dt`, `Feec.Numerics.CrankNicolson.finalTime_table`, `Feec.Numerics.CrankNicolson.planeWave_amplitudes`, `Feec.Numerics.CrankNicolson.planeWave_solves`, `Feec.Numerics.CrankNicolson.stepCount_table`, `Feec.TimeStepping.IsCNStep`, `Feec.TimeStepping.IsCNStep.norm_eq`, `Feec.TimeStepping.IsCNStep.unique`, `Feec.TimeStepping.IsCNStep.unique_of_isSkewSymmetric`, `Feec.TimeStepping.IsFullCNStep`, `Feec.TimeStepping.IsFullCNStep.apply_eq_of_comp_eq_zero`, `Feec.TimeStepping.IsFullCNStep.norm_sq_add`, `Feec.TimeStepping.IsFullCNStep.unique`, `Feec.TimeStepping.IsReducedCNStep`, `Feec.TimeStepping.IsReducedCNStep.adjoint_eq_zero_of_isFullCNStep`, `Feec.TimeStepping.IsReducedCNStep.isFullCNStep_zero`, `Feec.TimeStepping.bijective_cnLHS`, `Feec.TimeStepping.blockMass_add_smul_mulVec_eq_iff_schur`, `Feec.TimeStepping.blockSign_mul_mulVec_iff_fullCNStep`, `Feec.TimeStepping.blockSign_mul_mulVec_iff_reducedCNStep`, `Feec.TimeStepping.det_add_smul_ne_zero`, `Feec.TimeStepping.dotProduct_mulVec_eq_of_cn`, `Feec.TimeStepping.existsUnique_blockSign_mul_mulVec`, `Feec.TimeStepping.existsUnique_isFullCNStep`, `Feec.TimeStepping.existsUnique_isReducedCNStep`, `Feec.TimeStepping.isCNStep_cayley`, `Feec.TimeStepping.isFullCNStep_iff_mulVec`, `Feec.TimeStepping.isReducedCNStep_iff_mulVec`, `Feec.TimeStepping.isSymm_blockSign_mul`, `Feec.TimeStepping.isSymm_diagonal_mul_add_smul`, `Feec.TimeStepping.isSymm_isUnit_indefinite_blockSign_mul`, `Feec.TimeStepping.isUnit_blockMass_add_smul`, `Feec.TimeStepping.mulVec_diagonal_mul_iff`, `Feec.TimeStepping.norm_cayley_apply`, `Feec.TimeStepping.norm_cayley_pow_apply`, `Feec.TimeStepping.norm_eq_of_forall_isCNStep`, `Feec.TimeStepping.not_isSymm_assembled`, `Feec.TimeStepping.not_isSymm_blockMass_add_smul`, `Feec.TimeStepping.posDef_schurComplement`, `LinearPMap.IsSkewAdjoint.isCNStep_cayley`
- modules: Feec.Counterexamples.BoundedBGG, Feec.Evolution.BoundaryLifting, Feec.HilbertComplex.Approximation.Crown, Feec.HilbertComplex.Approximation.FullyDiscrete, Feec.Instances.Corollaries, Feec.Instances.FullyDiscrete, Feec.Models.Cube.Inhomogeneous, Feec.Models.Cube.InhomogeneousError, Feec.Models.Cube.Mirror, Feec.Numerics.CrankNicolsonTable, Feec.Numerics.PlaneWaveCube, Feec.Numerics.PlaneWaveCubeError, Feec.TimeStepping.BlockMatrix, Feec.TimeStepping.Cayley
