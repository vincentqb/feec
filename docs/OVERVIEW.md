# Overview

Module map, corrections to the thesis, the proved repaired statements, and the scope of the
formalization. Declarations are named in full. `docs/THESIS_MAP.md` lists, for every result,
equation and section of the thesis, the declarations that formalize it, and
`docs/migration/map.tsv` gives the current home of every declaration of the pre-refactor tree
(the chapter-ordered modules `Feec.Ch2`–`Feec.Ch7`, `Feec.Repair`, `Feec.Foundation`, and the
real-scalar layer `Feec.Legacy` that remained of them; see [The pre-refactor tree](#the-pre-refactor-tree)).

## Module map

The library is organized by mathematics. A layer imports only the layers above it in this table.

| Layer | Content | Thesis |
|---|---|---|
| `Feec.ForMathlib` | Unbounded operators over `ℝ` or `ℂ`: skew-symmetric, skew-adjoint and dissipative operators, the graph space and `T†† = T`, reducing subspaces and restriction, the closed range theorem; `ℓᵖ` and `Lᵖ` identifications; a square-root Gronwall inequality; partial derivatives | §4.1, (4.1a–d), Thm 4.4, Lemma 4.12 |
| `Feec.Operator` | Adjoints of composable pairs, multiplication operators on `L²(μ; E)`, resolvents | §4.1–4.2 |
| `Feec.Semigroup` | Strongly continuous groups and semigroups; Stone's theorem; invariant cores; bounded perturbations (Dyson–Phillips); pure point spectrum, and eigenbases from a compact resolvent | Thm 4.3; `K*` in Props 4.17, 4.19 |
| `Feec.Evolution` | Strong and classical solutions of `U' = AU + F` on any interval, energy estimates, forcing classes, Duhamel's formula, existence and uniqueness for generators, constraint propagation through reducing subspaces | Thm 4.3, Cor 4.5, Lemma 4.12 |
| `Feec.Variational` | The inf-sup condition, Babuška–Nečas and Lax–Milgram, Petrov–Galerkin quasi-optimality, Brezzi's theorem, Fortin operators, the Galerkin error bound for evolution problems (all over `ℝ` and `ℂ`) | Thms 4.8–4.11, Thm 4.14 |
| `Feec.TimeStepping` | Crank–Nicolson as a Cayley transform; signed symmetrization of the block systems for MINRES | Ch. 7 |
| `Feec.HilbertComplex` | Hilbert complexes over any `ComplexShape` (any length, every index), short complexes, windows, the dual and domain complexes; Hodge decomposition, Poincaré ⇔ closed range, the compactness property; the Dirac and wave operators, the Hodge and mixed Hodge Laplacians, the Hodge wave equation and its weak form; reducing subcomplexes and constraint propagation; scaled embeddings, equivariance, reality; approximation (subcomplexes, cochain projections, discrete Hodge decomposition, mixed error, semi-discrete wave equation); BGG complexes (twisted complex, weak symmetry, discretization, time-dependent problem) | §4.2–4.6, Thms 4.1, 4.2, 4.6, 4.7, Props 4.13, 4.16–4.19, Ch. 5–6 |
| `Feec.Fourier` | Symbol complexes of multiplication operators, fibrewise reducing subspaces, closed range from spectral gaps, the torus and `ℝᵈ`, weak derivatives, real fields, spectral Galerkin; the symbols of de Rham, grad–curl, (4.16) and the BGG complex (5.1) | §4.10–4.11, Ch. 6 |
| `Feec.Domain` | `L²` fields on an open `Ω ⊆ ℝⁿ`, mollification, constant-coefficient operators with their minimal and maximal realizations and adjoints, complexes of them, boundary obstructions, finite speed of propagation for symmetric hyperbolic systems | §4.10, Prop 3.6 |
| `Feec.Algebra`, `Feec.Geometry` | Levi-Civita symbol, constant metrics, the exterior algebra, matrix calculus on jets and symbols, transverse–traceless matrices, the Koszul complex and polynomial forms in any dimension; algebraic curvature tensors, the Riemann tensor of a connection, Hodge duality on 2-forms, the Weyl decomposition | Ch. 2–3, §4.7–4.10 |
| `Feec.FiniteElement` | Degrees of freedom, unisolvence, commuting interpolants | §5.2 |
| `Feec.Models` | Instances: de Rham, grad–curl, (4.16) and BGG on `𝕋ᵈ`/`𝕋³` and `ℝᵈ`/`ℝ³`; de Rham, grad–curl and (4.16) on bounded domains, with the density of `L²(TSD) ∩ H̊(curl)`; cubes: the method of images, the identification with the bounded-domain complex, static data, mirror boundary conditions for grad–curl, (4.16) and BGG | §4.10–4.11, Ch. 6 |
| `Feec.Physics` | Linearized gravity (Einstein operator, gauge, plane waves), the linearized Einstein–Bianchi system (jets, fields, propagation of its constraints), Maxwell's Gauss laws | Ch. 2–3 |
| `Feec.Counterexamples`, `Feec.Examples`, `Feec.Numerics` | The refutations listed below; non-vacuity witnesses; the plane-wave check and Table 7.1 of Ch. 7 | |

## Corrections to the thesis

The most significant errors and gaps found during formalization, each with the declaration that
refutes or corrects it; module docstrings list the rest.

- **Prop 2.4(b)**: `H = −□h̄` is false; it is `H = −½□h̄` (`Feec.Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ`).
- **Prop 2.6**: the gauge vector `B` has the wrong sign and does not reach TT gauge (`Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed`); with the sign fixed it does (`Feec.LinearizedGravity.tt_gauge`, `Feec.LinearizedGravity.exists_ttGauge`).
- **(2.15)**: the geodesic-deviation accelerations have the wrong sign and `f` in place of `f''` (`Feec.Counterexamples.LinearizedGravity.not_accel_printed`, `Feec.LinearizedGravity.tt_accel_fun`).
- **§2.4**: `8πG/c⁴ ≈ 2.08·10⁻⁴³`, not `5·10⁻⁴⁴` (`Feec.LinearizedGravity.einstein_const_bounds`); `G = 0 ⇔ Ric = 0` needs `n ≠ 2` (`Feec.Counterexamples.Curvature.exists_einstein_eq_zero_ne_zero_two`).
- **§4.3**: the kernel of an unbounded operator need not be closed, even for a densely defined one (`Feec.Counterexamples.exists_dense_not_isClosed_ker`).
- **§4.2**: "Fredholm ⇒ closed" is false (`Feec.Counterexamples.periodic_not_closedRange`); the compactness property does imply it (`Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`).
- **Thm 4.6**: closed range is unnecessary: the wave operator of every Hilbert complex, of any length, is skew-adjoint (`Feec.HilbertComplex.isSkewAdjoint_wave`), and the Hodge wave equation is well posed with the thesis's forcing class (`Feec.HilbertComplex.HodgeWave.existsUnique`).
- **Thm 4.9**: the converse needs a *unique* solution; the backward shift is a counterexample (`Feec.Counterexamples.surjective_not_infSup`).
- **Thm 4.11 (Brezzi)**: the inf-sup condition on `b` is quantified over the wrong argument, which forces injectivity (`Feec.Variational.InfSup.injective`) and fails as soon as `Z ≠ 0`; the thesis gives no proof. Stated correctly and proved (`Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.brezzi_iff`).
- **Lemma 4.12**: `Q ∈ C¹` fails where the lemma is applied; only `Q²` needs to be differentiable (`le_add_half_sub_of_sq_deriv_le_mul`, `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`).
- **Thm 4.14**: it needs `ξ ∈ C¹(V)`, and the `(1 + T)` factor is sharpened (`Feec.Variational.GalerkinEvolution.error_bound_refined`, `Feec.HodgeWave.norm_sub_le_of_semidiscrete`). `ξ₀ ∈ D(L)` does not give `C¹(V)` (`Feec.Counterexamples.ClassicalRegularity.exists_datum_not_C1`), but the convergence claimed after the theorem holds for every `ξ₀ ∈ D(L)`, without a rate (`Feec.HodgeWave.tendstoUniformlyOn_of_isWeakSolution`, `Feec.HodgeWave.tendstoUniformlyOn_of_tendsto`).
- **§4.10**: two of the four proposed discretizations are not subcomplexes, in any dimension (`Feec.Counterexamples.PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus`, `Feec.Counterexamples.PolynomialForms.not_isTensorSubcomplex_printed`); replacing `P_{r+1}Λ⁰` by `P_rΛ⁰` in them fixes this (`Feec.Koszul.isTensorSubcomplex_corrected`).
- **Props 4.17, 4.19**: for every Hilbert complex and every constraint subspace, the density conjectures are unnecessary and the projection hypothesis is necessary and sufficient for propagation (`Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`). Without a boundary the projection hypothesis holds and Props 4.17 and 4.19 hold with existence and uniqueness, on `𝕋³` (`Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_existsUnique`) and on `ℝ³` (`Feec.Models.Euclidean.GradCurl.tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.tsd_existsUnique`, and for real fields `Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`). On every nonempty bounded open `Ω ⊆ ℝ³` the projection hypotheses fail, for every complex whose `d₁` lies in the minimal curl (`Feec.Counterexamples.BoundedDomainTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedSymTSD.not_isReducing_tsd`) and with the maximal curl (`Feec.Counterexamples.BoundedDomainTSD.not_projection_magnetic`), and so do the conclusions: explicit TSD data have strong solutions that leave the constraint set (`Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`, `Feec.Counterexamples.BoundedSymTSD.tsd_not_propagates`). The density conjectures themselves are true on every bounded domain (`Feec.Models.BoundedDomain.dense_curl_inter_divFree`, `Feec.Models.BoundedDomain.dense_curl_maximal_inter_divFree`); the invalid step is the inference that `H̊(curl) ∩ L²(TSD)` is dense in `L²(TSD)`: its closure has infinite codimension (`Feec.Counterexamples.BoundedDomainTSD.not_dense_tsd_inter`, `Feec.Models.BoundedDomain.not_tsd_le_closure_sup_finiteDimensional`), and on domains star-shaped with respect to a ball it is `L²(TSD₀)` (`Feec.Models.BoundedDomain.closure_eq_tsd₀`, `Feec.Counterexamples.BoundedDomainTSD.density_gap`). The failure starts at the boundary: TSD propagates in the interior at unit speed, and for the datum `(0, 0, β)` the violation sits in the boundary layer (`Feec.Models.BoundedDomain.tsd_depDomain`, `Feec.Counterexamples.BoundedDomainTSD.beta_violation_boundary_layer`). What survives on bounded domains: Props 4.16 and 4.18, and Props 4.17/4.19 on the largest invariant constraint space `K* ⊊ K` (`Feec.Counterexamples.BoundedDomainTSD.invariantCore_tsd`, `Feec.Counterexamples.BoundedSymTSD.invariantCore_tsd`). On every open cube, `(0, π)³` included, with the boundary conditions of Prop 4.17, `K*` consists of the stationary data, and forward invariance alone already forces this (`Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Counterexamples.CubeStationary.forward_iff_stationary`; proved in a parity model, `Feec.Models.Cube.Parity.mem_invariantCore_iff`, `Feec.Models.Cube.Parity.forward_iff`). With tensorial mirror conditions Props 4.17 and 4.19 hold, in the parity model (`Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`), for `L²` fields on `(0, ½)³` (`Feec.Models.Cube.Mirror.existsUnique_memQ`) and on every open cube (`Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`). For the boundary conditions as printed in Prop 4.19 (`Feec.Models.BoundedDomain.hessCurlMax`), the projection hypothesis and the density fail (`Feec.Counterexamples.BoundedSymTSD.not_starProjection_mem_wave_domain_hessCurlMax`, `Feec.Counterexamples.BoundedSymTSD.not_dense_hessCurlMax`), and on the unit ball so does the conclusion (`Feec.Counterexamples.BallSymTSD.not_propagates`).
- **(5.1)**: exactness at `Ṽ¹` is used but never proved (`Feec.BGG.Segment.ker_D1_eq_range_D0`).
- **Prop 5.4**: exactness at `V_h¹` cannot be dropped (`Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`).
- **Prop 6.2**: false as stated (`Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`); it holds exactly under compatibility conditions (C1)–(C3) (`Feec.BGG.exists_discreteSolution_iff`), of which only (C2) constrains the dynamic data (`Feec.BGG.exists_discreteSolution_iff_compatible_u`).
- **Ch. 6**: on bounded domains with the boundary conditions of §6.3, the weak-symmetry method inherits the failure: from the TSD datum `(0, 0, (0, β))` the unique solution has `u(t) ∉ L²(TSD)` and `B(t)` non-symmetric for some `t` in every `[0, T]` (`Feec.Counterexamples.BoundedBGG.bggComplex_verdict`). On `ℝ³` and `𝕋³` the same system propagates TSD (`Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_existsUnique`), and so it does on `(0, ½)³` with mirror conditions (`Feec.Models.Cube.MirrorBGG.existsUnique_memQ`).
- **Ch. 7**: MINRES does not apply to the unsymmetrized Crank–Nicolson matrix (`Feec.TimeStepping.not_isSymm_blockMass_add_smul`); a sign change symmetrizes it, for complexes of any length (`Feec.TimeStepping.isSymm_diagonal_mul_add_smul`). The thesis does not say which matrix MINRES is applied to; for the Schur complement of block elimination the claim holds as stated (`Feec.TimeStepping.posDef_schurComplement`).

## Repaired statements

Every correction above comes with a proved corrected statement: the strongest true form of what
the thesis claims and uses downstream that is formalized here. All are kernel-checked and depend
only on `propext`, `Classical.choice` and `Quot.sound`. The last paragraph of this section lists
what the repairs do not cover.

| Thesis | Claim | Defect | Proved corrected statement | Lean |
|---|---|---|---|---|
| Prop 2.4(b), (2.11) | In Lorentz gauge `H_bd = −□h̄_bd`, so `□h̄ = −16πT` | Factor `½` missing | For every C² symmetric `h` with `∂^a h̄_ab = 0`: `H_bd = −½□h̄_bd`, hence `H = 8πT ⇔ □h̄ = −16πT` | `Feec.LinearizedGravity.Hfun_lorentz`, `Feec.LinearizedGravity.Hjet_lorentz`, `Feec.LinearizedGravity.Hfun_lorentz_eq_iff`, `Feec.Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ` |
| Prop 2.6 | `ξ_a = B_a g(k·x)` with the printed `B` brings a plane wave to TT gauge | Printed `B` fails under both index readings | For `κ ≠ 0`, `A` symmetric with `Ak = 0`, `f ∈ C²`: there is a C³ gauge vector (`B` = minus the printed one, `g = ∫₀ f`) with `h̄ − (2∂_(aξ_b) − η_ab∂·ξ) = A' f(k·x)`, `A' = ttAmp((A₁₁−A₂₂)/2, A₁₂)` TT, again a vacuum plane wave; `□ξ = 0` | `Feec.LinearizedGravity.exists_ttGauge`, `Feec.LinearizedGravity.trRev_sub_gauge_eq_ttAmp`, `Feec.LinearizedGravity.box_ttGaugeVec`, `Feec.LinearizedGravity.tt_gauge`, `Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed` |
| (2.15) | `a¹ = −(κ²/2)(A₊v¹ + Aₓv²) f`, `a² = −(κ²/2)(Aₓv¹ − A₊v²) f` | Wrong sign, `f` in place of `f''` | `a¹ = (κ²/2)(A₊v¹ + Aₓv²) f''(k·x)`, `a² = (κ²/2)(Aₓv¹ − A₊v²) f''(k·x)`, `a⁰ = a³ = 0`; the printed Riemann components hold for every TT jet | `Feec.LinearizedGravity.tt_accel_fun`, `Feec.LinearizedGravity.tt_accel`, `Feec.LinearizedGravity.Rjet_tt`, `Feec.LinearizedGravity.Rjet_tt_support`, `Feec.Counterexamples.LinearizedGravity.not_accel_printed` |
| §2.4 | `8πG/c⁴ ≈ 5·10⁻⁴⁴`; `G = 0 ⇔ Ric = 0` | The value is `2πG/c⁴`; the equivalence needs `n ≠ 2` | `8πG/c⁴ ∈ (2.07, 2.09)·10⁻⁴³`; for every `n ≠ 2`, `Ric − ½ tr(g⁻¹Ric) g = 0 ⇔ Ric = 0`, false for `n = 2` | `Feec.LinearizedGravity.einstein_const_bounds`, `Feec.CurvatureTensor.einstein_eq_zero_iff`, `Feec.Counterexamples.Curvature.exists_einstein_eq_zero_ne_zero_two` |
| §4.3 | The kernel of any linear operator is closed, so `MU = 0` on `[0,T]` | False for non-closed operators | `ker M` is closed for closed `M`; for a constraint subspace that reduces the generator every strong solution stays in it, with existence for skew-adjoint generators; `ker d₀†` is closed since adjoints are closed | `LinearPMap.isClosed_ker`, `Feec.Evolution.IsStrongSolution.mem_of_invariant`, `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`, `Feec.Counterexamples.exists_dense_not_isClosed_ker` |
| §4.2 | Compactness ⇒ Fredholm ⇒ closed | "Fredholm ⇒ closed" false with finite-dimensional harmonic forms | Finite-dimensional cohomology ⇒ closed range; the compactness property ⇒ closed range at both ends, finite-dimensional harmonic forms and the Hodge decomposition without closures, at every index of every Hilbert complex | `Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`, `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`, `Feec.Counterexamples.periodic_not_closedRange` |
| Thm 4.6 | Under closed range, `L` is skew-adjoint and data in `D(L)` have unique solutions | Closed range unneeded; density of `D(L)` and existence not shown | For every Hilbert complex of closed densely defined operators, of any length: `L` skew-adjoint, a unique solution in `C⁰(D(L)) ∩ C¹(W)` for `ξ₀ ∈ D(L)` and forcing in the thesis's class, unique also among weak solutions, energy conserved | `Feec.HilbertComplex.isSkewAdjoint_wave`, `Feec.HilbertComplex.HodgeWave.existsUnique`, `Feec.HilbertComplex.HodgeWave.existsUnique_hom` |
| Thm 4.9 | Inf-sup and dense range ⇔ `a(u,·) = f` solvable for every `f` | Needs a unique solution; the backward shift is a counterexample | (Inf-sup ∧ dense range in the second slot) ⇔ `∀ f, ∃! u, a(u,·) = f`, over `ℝ` and `ℂ`; `γ` admissible ⇔ `γ‖L⁻¹‖ ≤ 1` | `Feec.Variational.babuskaNecas_iff`, `Feec.Variational.babuskaNecas_iff_inner`, `Feec.Variational.infSup_iff_mul_norm_symm_le`, `Feec.Counterexamples.surjective_not_infSup` |
| Thm 4.11 | Brezzi well-posedness, inf-sup on `b` over `u`; no proof | The printed inf-sup is unsatisfiable when `Z ≠ 0` | With the inf over `q ∈ Y`, inf-sup and dense range of `a` on `Z`: a unique `(u,p)` with `‖u‖ + ‖p‖ ≤ C(‖F‖ + ‖G‖)`, explicit `C(‖a‖, γ, β)`, and the converse | `Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.brezzi_iff`, `Feec.Variational.IsSaddleSolution.norm_fst_le`, `Feec.Variational.IsSaddleSolution.norm_snd_le`, `Feec.Variational.InfSup.injective` |
| Lemma 4.12 | `Q ∈ C¹`, `(Q²)' ≤ FQ` ⇒ `Q(t) ≤ Q(0) + ½∫₀ᵗF` | Applied to `‖ε_h‖`, which is not C¹ | `Q ≥ 0` continuous with `Q²` right-differentiable and `(Q²)' ≤ FQ` ⇒ the same bound, on any interval, with a decay rate in the energy form; sharp | `le_add_half_sub_of_sq_deriv_le_mul`, `le_add_half_integral_of_sq_deriv_le_mul`, `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`, `le_add_half_integral_of_sq_deriv_le_mul_sharp` |
| Thm 4.14 | Error bound for `ξ ∈ C⁰(V) ∩ C¹(W)`; convergence under compactness | Needs `ξ ∈ C¹(V)`, which `ξ₀ ∈ D(L)` does not give | Pointwise bound with `t − t₀` in place of `T` for `ξ ∈ C¹(V)`, for any accretive form over `ℝ` or `ℂ`; `C¹(V)` solutions exist for `ξ₀ ∈ D(L²)`; convergence (no rate) for every `ξ₀ ∈ D(L)`, and every `ξ₀ ∈ W`, from density alone | `Feec.Variational.GalerkinEvolution.error_bound_refined`, `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, `Feec.HodgeWave.exists_isGraphSolution`, `Feec.HodgeWave.tendstoUniformlyOn_of_isWeakSolution`, `Feec.HodgeWave.tendstoUniformlyOn_of_tendsto`, `Feec.Counterexamples.ClassicalRegularity.exists_datum_not_C1` |
| §4.10 | Four discretizations of (4.14), four of (4.15) | `P_{r+1}Λ⁰ × P_r⁻Λ¹` is not a subcomplex | With `P_rΛ⁰` paired with `P_r⁻Λ¹`, all four (4.14) choices are subcomplexes (row-wise `⊗V`); the (4.15) list is correct as printed; the 0-form degree is maximal; the failure holds in every dimension | `Feec.Koszul.isTensorSubcomplex_corrected`, `Feec.Counterexamples.PolynomialForms.not_isTensorSubcomplex_printed`, `Feec.Koszul.extDeriv_mem_tensorForm_reduced`, `Feec.Koszul.tensorForm_reduced_iff`, `Feec.Koszul.isTensorSubcomplex_alt`, `Feec.Koszul.map_extDeriv_polyForm_le_polyFormMinus_iff`, `Feec.Counterexamples.PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus` |
| Props 4.17, 4.19 | On bounded `Ω`, under projection and density conjectures, TSD data propagate | Hypotheses false and conclusions fail on every bounded `Ω` with the stated conditions; the density inference is invalid | Propagation ⇔ the constraint reduces the complex, for every complex; hold on `𝕋³` and `ℝ³` for all TSD data, with existence and uniqueness; with the thesis's conditions only on `K*`, stationary on cubes (4.17); with tensorial mirror conditions on every open cube, `(0,1)³` and `(0,π)³` included, with `K* = K` and moving data | `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.Ident.forward_iff` |
| (5.1) | Exactness at `Ṽ¹` (used in Props 5.2, 5.4) | Never proved | `N(S₁) ∩ N(d̃¹) = R(0 d)` from exactness of the two complexes; used in Prop 5.2 | `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.range_D0`, `Feec.BGG.Hilb.mem_Z1_iff` |
| Prop 5.4 | The discrete system (5.6) is invertible | The proof never uses exactness at `V_h¹`, which is necessary | With exactness at `V_h¹` and `Ṽ_h¹`, `d̃` injective and `V_h¹ = dV_h⁰ + S₀Ṽ_h⁰` (weaker than `S₀` onto): unique solution for all data; derived from the continuous hypotheses | `Feec.BGG.existsUnique_isMixedSolution`, `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`, `Feec.BGG.exists_mixed_homogeneous_of_perp` |
| Prop 6.2 | (6.3) has a unique solution for every initial datum with `(σ₀, φ₀) ∈ Γ_h` | False | Solvable ⇔ (C1)–(C3), uniquely; for dynamic data `(σ₀, u₀, M₀, ρ₀)` ⇔ `(u₀, dψ) = 0` for `ψ ∈ ker S₀,h`, with `φ_h(0)` forced; projected data give a solution and the error bound | `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`, `Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi` |
| Ch. 6 | The weak-symmetry method with the §6.3 conditions propagates TSD | Fails on every bounded domain | Propagates TSD on `ℝ³`, on `𝕋³`, and on `(0, ½)³` with mirror conditions: unique solution, `σ ≡ 0`, `u` TSD, `M ≡ 0`, `B` TSD and symmetric | `Feec.Models.Cube.MirrorBGG.propagatesQ`, `Feec.Models.Cube.MirrorBGG.existsUnique_memQ`, `Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_existsUnique`, `Feec.Counterexamples.BoundedBGG.bggComplex_verdict` |
| Ch. 7 | "Other matrices are inverted with MINRES" | The Crank–Nicolson matrix is not symmetric | `J(M + sK)` is symmetric (for any number of blocks), nonsingular, indefinite, and its system is solved exactly by the CN update (assembled from Gram, `grad`, `curl` matrices); the Schur complement of block elimination is SPD | `Feec.TimeStepping.isSymm_diagonal_mul_add_smul`, `Feec.TimeStepping.mulVec_diagonal_mul_iff`, `Feec.TimeStepping.not_isSymm_blockMass_add_smul`, `Feec.TimeStepping.isSymm_isUnit_indefinite_blockSign_mul`, `Feec.TimeStepping.existsUnique_blockSign_mul_mulVec`, `Feec.TimeStepping.blockSign_mul_mulVec_iff_fullCNStep`, `Feec.TimeStepping.blockMass_add_smul_mulVec_eq_iff_schur`, `Feec.TimeStepping.posDef_schurComplement` |

Limits of the repairs. Props 4.17, 4.19 and the Ch. 6 claim are repaired on domains without
boundary and on axis-parallel cubes only: on a curved bounded domain no boundary condition is
proved to propagate non-stationary TSD data (the mirror conditions do not form a complex there),
and the Ch. 6 system with mirror conditions is proved only on `(0, ½)³`, since it is not
dilation-invariant. The mirror conditions hold in the reflection sense, not as trace conditions;
on cubes other than `(0, ½)³` the operators of (4.16) are dilation conjugates, not identified with
the weak Hessian and curl. The §4.10 repair is at the level of polynomial shape functions, without
a mesh or cochain projections. Prop 6.2 keeps the §6.3 finite element facts (`S₀,h` onto,
`grad` injective on `P₂Λ⁰ ⊗ V`, the elliptic projection) as hypotheses. For Ch. 7, which matrix
the thesis applies MINRES to is undetermined; both readings are treated. The Ch. 7 plane-wave
test solution satisfies no homogeneous boundary condition and is outside every proved statement.

## The pre-refactor tree

The chapter-ordered tree (`Feec.Ch2`–`Feec.Ch7`, `Feec.Repair`, `Feec.Foundation`) and the
real-scalar layer that remained of it (`Feec.Legacy`, built on a short complex
`Feec.Legacy.HilbertComplex2` with concrete ℝ³ models of the torus, the box, the mirror cubes and
bounded domains) are gone. Every declaration of the old tree was re-derived in the general layers
or deleted as a helper, and `docs/migration/map.tsv` records where each one went
(`scripts/MapCheck.sh --strict` checks that every old declaration is covered and every new name
elaborates). Thesis-numbered names, `_unconditional` variants, strangler shims and deprecated
aliases are gone with it. The cube models are built from the Fourier models of `𝕋³`
(`Feec.Models.Torus`, `Feec.Fourier`) and the bounded-domain complexes
(`Feec.Models.BoundedDomain`) alone.

## Scope

Stone's theorem is proved over `ℝ` and `ℂ` (`LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup`),
so existence for every skew-adjoint generator, the Hodge wave operator of every Hilbert complex
included, is a theorem and never a hypothesis: `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`
covers the thesis's full forcing class `C([0,T];X) ∩ (W^{1,1}(0,T;X) ∪ L¹(0,T;D(L)))`, with
`W^{1,1}` in integral form; its equivalence with "absolutely continuous with an integrable
derivative" is not formalized. Bounded perturbations (Dyson–Phillips) are covered; the
Lumer–Phillips theorem is not. Semi-discrete convergence holds for every datum in `W`, and in the
thesis's form for `ξ₀ ∈ D(L)`; the error bound of Thm 4.14 needs `C¹(V)` solutions, which exist
for `ξ₀ ∈ D(L²)`, and no rate is formalized for `D(L)` or `W` data.

Mathlib has no Sobolev spaces with traces and no finite element spaces. Abstract results therefore
take concrete complexes as instances of abstract structures, with their analytic facts (closed
range, bounded cochain projections, density, regular decompositions) as hypotheses. The concrete
models are:
* `𝕋ᵈ` and `ℝᵈ` (`Feec.Models.Torus`, `Feec.Models.Euclidean`, built on `Feec.Fourier`): symbol
  complexes of Fourier multipliers, for de Rham in every dimension and degree, grad–curl, (4.16)
  and the BGG complex (5.1); the Fourier spaces are identified with the weak-derivative spaces
  (`Feec.Fourier.Weak`), and real fields are the fixed points of a conjugation
  (`Feec.Fourier.Reality`).
* Bounded open sets of `ℝⁿ` (`Feec.Domain`, `Feec.Models.BoundedDomain`): `L²` fields,
  constant-coefficient operators and their minimal and maximal realizations, with the adjoint of
  one being the other. Density of `L²(TSD) ∩ H̊(curl)` in `L²(TSD₀)` is proved for domains
  star-shaped with respect to a ball, not for Lipschitz domains. Finite speed of propagation is
  proved for symmetric hyperbolic systems (`Feec.Domain.FiniteSpeed`); Prop 3.6 holds in its
  interior form at unit speed, and on `ℝ³` for solutions of the weak equations, which are assumed,
  not constructed.
* Cubes (`Feec.Models.Cube`): complexes on the box `(0, ½)³` obtained from the `𝕋³` model by the
  method of images, encoding the thesis's boundary conditions or tensorial mirror conditions,
  identified with the bounded-domain complexes on `(0, ½)³` and carried to every open cube by
  `x ↦ a x + b`; the mirror boundary conditions hold in the reflection sense and are not
  characterized by traces.

The thesis states its Ch. 4 results with boundary conditions on a bounded `Ω` (§4.10, §6.3), so
the bounded-domain models are the faithful setting; `𝕋³` and `ℝ³` have no boundary and serve as
a contrast. For the boundary conditions printed in Prop 4.19, the hypotheses fail, and the
conclusion fails on the unit ball; other domains, and whether `K*` is nonzero there, are not
decided. On a general bounded domain no non-stationary element of `K*` is known;
`Feec.Models.BoundedDomain.gradCurl_coreSub_spectral` reduces the question to the existence of a nonzero TSD
eigenfield of `curl* curl`, which needs pure point spectrum; that is derived from a compact
resolvent (`Feec.C0Group.eigenDense_of_compactResolvent`) and proved on `𝕋³`, but for no bounded
domain (it needs Rellich–Kondrachov and Maxwell compactness). Not formalized for Ch. 6: the
multiplier form (6.2), the transfer of the bounded-domain failure to the semi-discrete scheme
(6.5), and its bearing on Ch. 7, which states no boundary conditions and whose plane-wave exact
solution does not satisfy the homogeneous ones.

Pseudo-Riemannian geometry is done in components at the jet level. Out of scope: the nonlinear
Einstein–Bianchi system (§3.4), the concrete finite element computations of §5.3 (Props 5.7–5.9
beyond the abstract core of Prop 5.7), and the numerical results of Ch. 7 beyond the plane-wave
check. All cited works are collected in [`references.bib`](references.bib).
