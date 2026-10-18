# Overview

Module map, corrections to the thesis, the proved repaired statements, and the scope of the
formalization. Declarations are named in full. `docs/THESIS_MAP.md` lists, for every result,
equation and section of the thesis, the declarations that formalize it, and
`docs/migration/map.tsv` gives the current home of every declaration of the pre-refactor tree
(the chapter-ordered modules `Feec.Ch2`–`Feec.Ch7`, `Feec.Repair`, `Feec.Foundation`, and the
real-scalar layer `Feec.Legacy` that remained of them; see [The pre-refactor tree](#the-pre-refactor-tree)).
[`docs/THESIS_REFERENCES.md`](THESIS_REFERENCES.md) lists, for each entry [1]–[28] of the thesis
bibliography, where the thesis and the code cite it.

## Module map

The library is organized by mathematics. A layer imports only the layers above it in this table.

| Layer | Content | Thesis |
|---|---|---|
| `Feec.ForMathlib` | Unbounded operators over `ℝ` or `ℂ`: skew-symmetric, skew-adjoint and dissipative operators, the graph space and `T†† = T`, reducing subspaces and restriction, the closed range theorem; `ℓᵖ` and `Lᵖ` identifications; a square-root Gronwall inequality; partial derivatives, interval integrals, Hille's theorem (closed operators commute with Bochner integrals), restriction of scalars | §4.1, (4.1a–d), Thm 4.4, Lemma 4.12 |
| `Feec.Operator` | Adjoints of composable pairs, multiplication operators on `L²(μ; E)`, resolvents | §4.1–4.2 |
| `Feec.Semigroup` | Strongly continuous groups and semigroups and the calculus of their orbits; Stone's theorem; the Lumer–Phillips theorem (m-dissipative ⇔ generator of a contraction semigroup, with uniqueness); invariant cores; bounded perturbations (Dyson–Phillips); pure point spectrum, and eigenbases from a compact resolvent | Thm 4.3; `K*` in Props 4.17, 4.19 |
| `Feec.Evolution` | Strong and classical solutions of `U' = AU + F` on any interval, energy estimates, forcing classes, Duhamel's formula, existence and uniqueness for generators, constraint propagation through reducing subspaces, inhomogeneous essential boundary data by a lifting (`U − G ∈ D(A)`) | Thm 4.3, Cor 4.5, Lemma 4.12, Ch. 7 |
| `Feec.Variational` | The inf-sup condition, Babuška–Nečas and Lax–Milgram, Petrov–Galerkin quasi-optimality, Brezzi's theorem, Fortin operators, the Galerkin error bound for evolution problems (all over `ℝ` and `ℂ`) | Thms 4.8–4.11, Thm 4.14 |
| `Feec.TimeStepping` | Crank–Nicolson as a Cayley transform, also with prescribed boundary DOFs; its amplification factor and phase; signed symmetrization of the block systems for MINRES | Ch. 7 |
| `Feec.HilbertComplex` | Hilbert complexes over any `ComplexShape` (any length, every index), short complexes, windows, the dual and domain complexes; Hodge decomposition, Poincaré ⇔ closed range, the compactness property; the Dirac and wave operators, the Hodge and mixed Hodge Laplacians, the solution operator `K` with its bounds by Poincaré constants, the Hodge wave and Hodge heat equations; reducing subcomplexes and constraint propagation, with compactness, closed range and eigenbases passing to compressions; scaled embeddings, reweighting by bounded isomorphisms, equivariance, reality; approximation (subcomplexes, cochain projections, discrete Hodge decomposition, mixed error, quasi-optimal and improved error estimates of the mixed method, semi-discrete wave equation); BGG complexes (twisted complex, weak symmetry, discretization, time-dependent problem) | §4.2–4.6, Thms 4.1, 4.2, 4.6, 4.7, Props 4.13, 4.16–4.19, Ch. 5–6 |
| `Feec.Algebra`, `Feec.Geometry` | Levi-Civita symbol, constant metrics, the exterior algebra, matrix calculus on jets and symbols, transverse–traceless matrices, the Koszul complex and polynomial forms in any dimension (direct sums, dimensions of `P_rΛᵏ` and `P_r⁻Λᵏ`, exactness), the wedge product; algebraic curvature tensors, the Riemann tensor of a connection, Hodge duality on 2-forms, the Weyl decomposition; the second Bianchi identity and its contractions (`∇^a G_ab = 0`, vacuum `∇^a C_abcd = 0`) for metrics of any signature, Christoffel symbols, frame components and torsion in a frame | Ch. 2–3, §4.7–4.10 |
| `Feec.Fourier` | Symbol complexes of multiplication operators, fibrewise reducing subspaces, closed range from spectral gaps, the torus and `ℝᵈ`, weak derivatives, real fields, spectral Galerkin; the symbols of de Rham, grad–curl, (4.16) and the BGG complex (5.1) | §4.10–4.11, Ch. 6 |
| `Feec.Domain` | `L²` fields on an open `Ω ⊆ ℝⁿ`, mollification, constant-coefficient operators with their minimal and maximal realizations and adjoints, complexes of them (also with constrained values), the `L²` de Rham complex of `k`-forms on any open `Ω ⊆ ℝⁿ` with both boundary-condition families and their duality, the Hessian, div-div and elasticity complexes on open `Ω ⊆ ℝ³`, minimal = maximal on `ℝⁿ`, smoothers commuting with `d` on domains star-shaped with respect to a ball, boundary obstructions, finite speed of propagation for symmetric hyperbolic systems | §4.10, Prop 3.6 |
| `Feec.Mesh` | Conforming simplicial meshes of `Ω ⊆ ℝⁿ`, Kuhn simplices and Freudenthal meshes of boxes (face-to-face, uniform refinement), shape regularity | |
| `Feec.FiniteElement` | Abstract degrees of freedom and commuting interpolants; smooth forms, integration over simplices, Stokes' and the divergence theorem on simplices and meshes; the local spaces `P_rΛᵏ(T)`, `P_r⁻Λᵏ(T)` with unisolvent DOFs and commuting interpolants; Whitney forms; assembly of global spaces and conformity; the Whitney complex on any mesh; Bramble–Hilbert (classical form) and interpolation error on shape-regular meshes; smoothed projections | §5.2 |
| `Feec.Models` | Instances: de Rham, grad–curl, (4.16) and BGG on `𝕋ᵈ`/`𝕋³` and `ℝᵈ`/`ℝ³`; de Rham, grad–curl and (4.16) on bounded domains, with the density of `L²(TSD) ∩ H̊(curl)`; cubes: the method of images, the identification with the bounded-domain complex, static data, mirror boundary conditions for grad–curl, (4.16) and BGG, characterized on every open cube by Green's formulas (weak trace conditions), eigenbases on every open cube, the de Rham complex of `(0, ½)ⁿ` (relative and absolute classes: compactness, Poincaré, harmonic forms), smoothing by even Fourier multipliers, Whitney complexes on Freudenthal meshes and the finite element method under explicit smoothing estimates; inhomogeneous boundary data from whole-space TSD solutions on bounded domains and the fully discrete `fem4gr` scheme on Whitney spaces; on bounded domains, eigenfield obstructions to moving `K*` data and (4.16) under affine maps; spectral Galerkin for the torus de Rham complex | §4.10–4.11, Ch. 6–7 |
| `Feec.Physics` | Linearized gravity (Einstein operator, gauge, plane waves), the linearized Einstein–Bianchi system (jets, fields, propagation of its constraints), the nonlinear Einstein–Bianchi system in an orthonormal frame (satisfied by every vacuum metric, linearizing to the linearized system), Maxwell's equations (Gauss laws, linear media by reweighting with isotropic and anisotropic coefficient fields, Ohmic loss, `k`-form Maxwell on open `Ω ⊆ ℝⁿ`) | Ch. 2–3, §3.4 |
| `Feec.Counterexamples`, `Feec.Examples`, `Feec.Numerics` | The refutations listed below; non-vacuity witnesses; the plane-wave check, Table 7.1 and the plane-wave runs of Ch. 7 (Dirichlet data on the cube, periodic on `𝕋³`) | Ch. 7 |

## Corrections to the thesis

The most significant errors and gaps found during formalization, each with the declaration that
refutes or corrects it; module docstrings list the rest.

- **Prop 2.4(b)**: `H = −□h̄` is false; it is `H = −½□h̄` (`Feec.Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ`).
- **Prop 2.6**: the gauge vector `B` has the wrong sign and does not reach TT gauge (`Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed`); with the sign fixed it does (`Feec.LinearizedGravity.tt_gauge`, `Feec.LinearizedGravity.exists_ttGauge`).
- **(2.15)**: the geodesic-deviation accelerations have the wrong sign and `f` in place of `f''` (`Feec.Counterexamples.LinearizedGravity.not_accel_printed`, `Feec.LinearizedGravity.tt_accel_fun`).
- **§2.4**: `8πG/c⁴ ≈ 2.08·10⁻⁴³`, not `5·10⁻⁴⁴` (`Feec.LinearizedGravity.einstein_const_bounds`); `G = 0 ⇔ Ric = 0` needs `n ≠ 2` (`Feec.Counterexamples.Curvature.exists_einstein_eq_zero_ne_zero_two`).
- **§3.4**: in the nonlinear Einstein–Bianchi system the `B`-constraint has `+ E ×· K` and the `B`-evolution equation has `− sym curl E` and `− 2 sym(a × E)`; the printed `B`-equation `Ḃ + sym curl E + L² = 0` disagrees with Prop 3.4 already at `K = a = 0` (argued in the docstring of `Feec.Physics.EinsteinBianchi.Nonlinear`, not stated as a Lean refutation). The corrected system holds for every vacuum metric (`Feec.EinsteinBianchi.nonlinearEB_iff_extrinsicEB`, `Feec.EinsteinBianchi.vacuum_extrinsicEB`).
- **§4.3**: the kernel of an unbounded operator need not be closed, even for a densely defined one (`Feec.Counterexamples.exists_dense_not_isClosed_ker`).
- **§4.2**: "Fredholm ⇒ closed" is false (`Feec.Counterexamples.periodic_not_closedRange`); the compactness property does imply it (`Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`).
- **Thm 4.6**: closed range is unnecessary: the wave operator of every Hilbert complex, of any length, is skew-adjoint (`Feec.HilbertComplex.isSkewAdjoint_wave`), and the Hodge wave equation is well posed with the thesis's forcing class (`Feec.HilbertComplex.HodgeWave.existsUnique`).
- **Thm 4.9**: the converse needs a *unique* solution; the backward shift is a counterexample (`Feec.Counterexamples.surjective_not_infSup`).
- **Thm 4.11 (Brezzi)**: the inf-sup condition on `b` is quantified over the wrong argument, which forces injectivity (`Feec.Variational.InfSup.injective`) and fails as soon as `Z ≠ 0`; the thesis gives no proof. Stated correctly and proved (`Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.brezzi_iff`).
- **Lemma 4.12**: `Q ∈ C¹` fails where the lemma is applied; only `Q²` needs to be differentiable (`le_add_half_sub_of_sq_deriv_le_mul`, `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`).
- **Thm 4.14**: it needs `ξ ∈ C¹(V)`, and the `(1 + T)` factor is sharpened (`Feec.Variational.GalerkinEvolution.error_bound_refined`, `Feec.HodgeWave.norm_sub_le_of_semidiscrete`). `ξ₀ ∈ D(L)` does not give `C¹(V)` (`Feec.Counterexamples.ClassicalRegularity.exists_datum_not_C1`), but the convergence claimed after the theorem holds for every `ξ₀ ∈ D(L)`, without a rate (`Feec.HodgeWave.tendstoUniformlyOn_of_isWeakSolution`, `Feec.HodgeWave.tendstoUniformlyOn_of_tendsto`).
- **§4.10**: two of the four proposed discretizations are not subcomplexes, in any dimension (`Feec.Counterexamples.PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus`, `Feec.Counterexamples.PolynomialForms.not_isTensorSubcomplex_printed`); replacing `P_{r+1}Λ⁰` by `P_rΛ⁰` in them fixes this (`Feec.Koszul.isTensorSubcomplex_polyForm`).
- **Props 4.17, 4.19**: for every Hilbert complex and every constraint subspace, the density conjectures are unnecessary and the projection hypothesis is necessary and sufficient for propagation (`Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`). Without a boundary the projection hypothesis holds and Props 4.17 and 4.19 hold with existence and uniqueness, on `𝕋³` (`Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_existsUnique`) and on `ℝ³` (`Feec.Models.Euclidean.GradCurl.tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.tsd_existsUnique`, and for real fields `Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`). On every nonempty bounded open `Ω ⊆ ℝ³` the projection hypotheses fail, for every complex whose `d₁` lies in the minimal curl (`Feec.Counterexamples.BoundedDomainTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedSymTSD.not_isReducing_tsd`) and with the maximal curl (`Feec.Counterexamples.BoundedDomainTSD.not_projection_magnetic`), and so do the conclusions: explicit TSD data have strong solutions that leave the constraint set (`Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`, `Feec.Counterexamples.BoundedSymTSD.tsd_not_propagates`). The density conjectures themselves are true on every bounded domain (`Feec.Models.BoundedDomain.dense_curl_inter_divFree`, `Feec.Models.BoundedDomain.dense_curl_maximal_inter_divFree`); the invalid step is the inference that `H̊(curl) ∩ L²(TSD)` is dense in `L²(TSD)`: its closure has infinite codimension (`Feec.Counterexamples.BoundedDomainTSD.not_dense_tsd_inter`, `Feec.Models.BoundedDomain.not_tsd_le_closure_sup_finiteDimensional`), and on domains star-shaped with respect to a ball it is `L²(TSD₀)` (`Feec.Models.BoundedDomain.closure_eq_tsd₀`, `Feec.Counterexamples.BoundedDomainTSD.density_gap`). The failure starts at the boundary: TSD propagates in the interior at unit speed, and for the datum `(0, 0, β)` the violation sits in the boundary layer (`Feec.Models.BoundedDomain.tsd_depDomain`, `Feec.Counterexamples.BoundedDomainTSD.beta_violation_boundary_layer`). What survives on bounded domains: Props 4.16 and 4.18, and Props 4.17/4.19 on the largest invariant constraint space `K* ⊊ K` (`Feec.Counterexamples.BoundedDomainTSD.invariantCore_tsd`, `Feec.Counterexamples.BoundedSymTSD.invariantCore_tsd`). On every open cube, `(0, π)³` included, with the boundary conditions of Prop 4.17, `K*` consists of the stationary data, and forward invariance alone already forces this (`Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Counterexamples.CubeStationary.forward_iff_stationary`; proved in a parity model, `Feec.Models.Cube.Parity.mem_invariantCore_iff`, `Feec.Models.Cube.Parity.forward_iff`). With tensorial mirror conditions Props 4.17 and 4.19 hold, in the parity model (`Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`), for `L²` fields on `(0, ½)³` (`Feec.Models.Cube.Mirror.existsUnique_memQ`) and on every open cube (`Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`). For the boundary conditions as printed in Prop 4.19 (`Feec.Models.BoundedDomain.hessCurlMax`), the projection hypothesis and the density fail (`Feec.Counterexamples.BoundedSymTSD.not_starProjection_mem_wave_domain_hessCurlMax`, `Feec.Counterexamples.BoundedSymTSD.not_dense_hessCurlMax`), and on every ball `{|x − c| < R}` so do the conclusion and the density hypothesis, the latter read with the boundary condition of the printed data space `H̊(sym curl, T)` (`Feec.Counterexamples.BallSymTSD.not_propagates`, `Feec.Counterexamples.EveryBallSymTSD.tsd_not_propagates`, `Feec.Counterexamples.EveryBallSymTSD.not_dense_tsdT`). The mirror conditions are weak trace conditions: on every open cube `D(L)` is characterized by Green's formulas against `C¹` functions vanishing on the faces where the parity is odd (read as `σ·n = 0`, `E_{nτ} = E_{τn} = 0`, `B_{ττ} = 0`), and Prop 4.17 holds with them (`Feec.Models.Cube.Mirror.mem_wave_domain_cube_iff_trace`, `Feec.Models.Cube.Mirror.existsUnique_memCube_trace`). On every bounded domain, an eigenfield `curl* curl u = ξ²u`, `ξ ≠ 0`, with `u, curl u ∈ H̊(curl)` vanishes (`Feec.Models.BoundedDomain.eq_zero_of_isEigenfield_of_mem_minimal`), so under pure point spectrum `K*` has a moving datum exactly when some TSD eigenfield has `curl u ∉ H̊(curl)` (`Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff`).
- **(5.1)**: exactness at `Ṽ¹` is used but never proved (`Feec.BGG.Segment.ker_D1_eq_range_D0`).
- **Prop 5.4**: exactness at `V_h¹` cannot be dropped (`Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`).
- **Prop 6.2**: false as stated (`Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`); it holds exactly under compatibility conditions (C1)–(C3) (`Feec.BGG.exists_discreteSolution_iff`), of which only (C2) constrains the dynamic data (`Feec.BGG.exists_discreteSolution_iff_compatible_u`).
- **Ch. 6**: on bounded domains with the boundary conditions of §6.3, the weak-symmetry method inherits the failure: from the TSD datum `(0, 0, (0, β))` the unique solution has `u(t) ∉ L²(TSD)` and `B(t)` non-symmetric for some `t` in every `[0, T]` (`Feec.Counterexamples.BoundedBGG.bggComplex_verdict`). On `ℝ³` and `𝕋³` the same system propagates TSD (`Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_existsUnique`), and so it does on `(0, ½)³` with mirror conditions (`Feec.Models.Cube.MirrorBGG.existsUnique_memQ`).
- **Ch. 7 (inhomogeneous data)**: the runs prescribe boundary data from the exact plane wave, so they are outside the homogeneous theory of Ch. 4. With these data the plane wave is the unique solution and stays TSD, but a TSD perturbation of its initial value leaves `L²(TSD)` (`Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.restrict_unique`, `Feec.Numerics.PlaneWaveCube.exists_not_propagates`).
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
| §3.4 | Nonlinear vacuum EB system: constraints `div E − B ×· K = 0`, `div B − E ×· K = 0`, evolution `Ė + sym curl B + L¹ = 0`, `Ḃ + sym curl E + L² = 0` | Signs of the `B`-constraint and of `sym curl E` in the `B`-equation wrong; the sign of `2 sym(a × E)` in `L²` wrong; `a × B` undefined | In an orthonormal frame of a metric with Levi-Civita connection on `ℝ⁴`: the frame second Bianchi identity for `W = [[E, B], [B, −E]]` ⇔ the frame EB system; every vacuum metric satisfies it; its linearization at Minkowski is the linearized system of Prop 3.4; for symmetric `K` (no normal component in the triad brackets) it is the thesis' system with `div B + E ×· K = 0`, `L_n B − sym curl E + L² = 0`, `L¹` as printed; Minkowski satisfies all hypotheses | `Feec.EinsteinBianchi.frameBianchi_iff`, `Feec.EinsteinBianchi.vacuum_nonlinearEB`, `Feec.EinsteinBianchi.linearization_nonlinearEB`, `Feec.EinsteinBianchi.nonlinearEB_iff_extrinsicEB`, `Feec.EinsteinBianchi.vacuum_extrinsicEB`, `Feec.EinsteinBianchi.extrinsic_symm_iff_bracket`, `Feec.EinsteinBianchi.minkowski_extrinsicEB`, `Feec.CurvatureTensor.frameRiemField_cyclic` |
| §4.3 | The kernel of any linear operator is closed, so `MU = 0` on `[0,T]` | False for non-closed operators | `ker M` is closed for closed `M`; for a constraint subspace that reduces the generator every strong solution stays in it, with existence for skew-adjoint generators; `ker d₀†` is closed since adjoints are closed | `LinearPMap.isClosed_ker`, `Feec.Evolution.IsStrongSolution.mem_of_invariant`, `Feec.Evolution.IsStrongSolution.mem_of_isReducing`, `LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution`, `Feec.Counterexamples.exists_dense_not_isClosed_ker` |
| §4.2 | Compactness ⇒ Fredholm ⇒ closed | "Fredholm ⇒ closed" false with finite-dimensional harmonic forms | Finite-dimensional cohomology ⇒ closed range; the compactness property ⇒ closed range at both ends, finite-dimensional harmonic forms and the Hodge decomposition without closures, at every index of every Hilbert complex | `Feec.HilbertComplex.closedRangeAt_of_finiteDimensional_cohomology`, `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm`, `Feec.Counterexamples.periodic_not_closedRange` |
| Thm 4.6 | Under closed range, `L` is skew-adjoint and data in `D(L)` have unique solutions | Closed range unneeded; density of `D(L)` and existence not shown | For every Hilbert complex of closed densely defined operators, of any length: `L` skew-adjoint, a unique solution in `C⁰(D(L)) ∩ C¹(W)` for `ξ₀ ∈ D(L)` and forcing in the thesis's class, unique also among weak solutions, energy conserved | `Feec.HilbertComplex.isSkewAdjoint_wave`, `Feec.HilbertComplex.HodgeWave.existsUnique`, `Feec.HilbertComplex.HodgeWave.existsUnique_hom` |
| Thm 4.9 | Inf-sup and dense range ⇔ `a(u,·) = f` solvable for every `f` | Needs a unique solution; the backward shift is a counterexample | (Inf-sup ∧ dense range in the second slot) ⇔ `∀ f, ∃! u, a(u,·) = f`, over `ℝ` and `ℂ`; `γ` admissible ⇔ `γ‖L⁻¹‖ ≤ 1` | `Feec.Variational.babuskaNecas_iff`, `Feec.Variational.babuskaNecas_iff_inner`, `Feec.Variational.infSup_iff_mul_norm_symm_le`, `Feec.Counterexamples.surjective_not_infSup` |
| Thm 4.11 | Brezzi well-posedness, inf-sup on `b` over `u`; no proof | The printed inf-sup is unsatisfiable when `Z ≠ 0` | With the inf over `q ∈ Y`, inf-sup and dense range of `a` on `Z`: a unique `(u,p)` with `‖u‖ + ‖p‖ ≤ C(‖F‖ + ‖G‖)`, explicit `C(‖a‖, γ, β)`, and the converse | `Feec.Variational.existsUnique_isSaddleSolution`, `Feec.Variational.brezzi_iff`, `Feec.Variational.IsSaddleSolution.norm_fst_le`, `Feec.Variational.IsSaddleSolution.norm_snd_le`, `Feec.Variational.InfSup.injective` |
| Lemma 4.12 | `Q ∈ C¹`, `(Q²)' ≤ FQ` ⇒ `Q(t) ≤ Q(0) + ½∫₀ᵗF` | Applied to `‖ε_h‖`, which is not C¹ | `Q ≥ 0` continuous with `Q²` right-differentiable and `(Q²)' ≤ FQ` ⇒ the same bound, on any interval, with a decay rate in the energy form; sharp | `le_add_half_sub_of_sq_deriv_le_mul`, `le_add_half_integral_of_sq_deriv_le_mul`, `Feec.Evolution.Energy.norm_le_of_re_inner_deriv_le`, `le_add_half_integral_of_sq_deriv_le_mul_sharp` |
| Thm 4.14 | Error bound for `ξ ∈ C⁰(V) ∩ C¹(W)`; convergence under compactness | Needs `ξ ∈ C¹(V)`, which `ξ₀ ∈ D(L)` does not give | Pointwise bound with `t − t₀` in place of `T` for `ξ ∈ C¹(V)`, for any accretive form over `ℝ` or `ℂ`; `C¹(V)` solutions exist for `ξ₀ ∈ D(L²)`; convergence (no rate) for every `ξ₀ ∈ D(L)`, and every `ξ₀ ∈ W`, from density alone | `Feec.Variational.GalerkinEvolution.error_bound_refined`, `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, `Feec.HodgeWave.exists_isGraphSolution`, `Feec.HodgeWave.tendstoUniformlyOn_of_isWeakSolution`, `Feec.HodgeWave.tendstoUniformlyOn_of_tendsto`, `Feec.Counterexamples.ClassicalRegularity.exists_datum_not_C1` |
| §4.10 | Four discretizations of (4.14), four of (4.15) | `P_{r+1}Λ⁰ × P_r⁻Λ¹` is not a subcomplex | With `P_rΛ⁰` paired with `P_r⁻Λ¹`, all four (4.14) choices are subcomplexes (row-wise `⊗V`); the (4.15) list is correct as printed; the 0-form degree is maximal; the failure holds in every dimension | `Feec.Koszul.isTensorSubcomplex_polyForm`, `Feec.Counterexamples.PolynomialForms.not_isTensorSubcomplex_printed`, `Feec.Koszul.extDeriv_mem_tensorForm_reduced`, `Feec.Koszul.tensorForm_reduced_iff`, `Feec.Koszul.isTensorSubcomplex_alt`, `Feec.Koszul.map_extDeriv_polyForm_le_polyFormMinus_iff`, `Feec.Counterexamples.PolynomialForms.not_map_extDeriv_polyForm_le_polyFormMinus` |
| Props 4.17, 4.19 | On bounded `Ω`, under projection and density conjectures, TSD data propagate | Hypotheses false and conclusions fail on every bounded `Ω` with the stated conditions; the density inference is invalid; for Prop 4.19 the conclusion and the density fail on every ball | Propagation ⇔ the constraint reduces the complex, for every complex; hold on `𝕋³` and `ℝ³` for all TSD data, with existence and uniqueness; with the thesis's conditions only on `K*`, stationary on cubes (4.17), and on every bounded `Ω` a moving element of `K*` needs a TSD eigenfield with `curl u ∉ H̊(curl)`; with tensorial mirror conditions on every open cube, `(0,1)³` and `(0,π)³` included, with `K* = K` and moving data, the conditions of 4.17 characterized by Green's formulas (weak traces) | `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.Mirror.existsUnique_memCube_trace`, `Feec.Models.Cube.Mirror.mem_wave_domain_cube_iff_trace`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff`, `Feec.Counterexamples.EveryBallSymTSD.tsd_not_propagates`, `Feec.Counterexamples.EveryBallSymTSD.not_dense_tsdT` |
| (5.1) | Exactness at `Ṽ¹` (used in Props 5.2, 5.4) | Never proved | `N(S₁) ∩ N(d̃¹) = R(0 d)` from exactness of the two complexes; used in Prop 5.2 | `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.range_D0`, `Feec.BGG.Hilb.mem_Z1_iff` |
| Prop 5.4 | The discrete system (5.6) is invertible | The proof never uses exactness at `V_h¹`, which is necessary | With exactness at `V_h¹` and `Ṽ_h¹`, `d̃` injective and `V_h¹ = dV_h⁰ + S₀Ṽ_h⁰` (weaker than `S₀` onto): unique solution for all data; derived from the continuous hypotheses | `Feec.BGG.existsUnique_isMixedSolution`, `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`, `Feec.BGG.exists_mixed_homogeneous_of_perp` |
| Prop 6.2 | (6.3) has a unique solution for every initial datum with `(σ₀, φ₀) ∈ Γ_h` | False | Solvable ⇔ (C1)–(C3), uniquely; for dynamic data `(σ₀, u₀, M₀, ρ₀)` ⇔ `(u₀, dψ) = 0` for `ψ ∈ ker S₀,h`, with `φ_h(0)` forced; projected data give a solution and the error bound | `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`, `Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi` |
| Ch. 6 | The weak-symmetry method with the §6.3 conditions propagates TSD | Fails on every bounded domain | Propagates TSD on `ℝ³`, on `𝕋³`, and on `(0, ½)³` with mirror conditions: unique solution, `σ ≡ 0`, `u` TSD, `M ≡ 0`, `B` TSD and symmetric | `Feec.Models.Cube.MirrorBGG.propagatesQ`, `Feec.Models.Cube.MirrorBGG.existsUnique_memQ`, `Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_existsUnique`, `Feec.Counterexamples.BoundedBGG.bggComplex_verdict` |
| Ch. 7 | "Other matrices are inverted with MINRES" | The Crank–Nicolson matrix is not symmetric | `J(M + sK)` is symmetric (for any number of blocks), nonsingular, indefinite, and its system is solved exactly by the CN update (assembled from Gram, `grad`, `curl` matrices); the Schur complement of block elimination is SPD | `Feec.TimeStepping.isSymm_diagonal_mul_add_smul`, `Feec.TimeStepping.mulVec_diagonal_mul_iff`, `Feec.TimeStepping.not_isSymm_blockMass_add_smul`, `Feec.TimeStepping.isSymm_isUnit_indefinite_blockSign_mul`, `Feec.TimeStepping.existsUnique_blockSign_mul_mulVec`, `Feec.TimeStepping.blockSign_mul_mulVec_iff_fullCNStep`, `Feec.TimeStepping.blockMass_add_smul_mulVec_eq_iff_schur`, `Feec.TimeStepping.posDef_schurComplement` |
| Ch. 7 (as run) | The plane-wave runs with boundary data from the exact solution preserve the constraints | Inhomogeneous boundary data are outside every homogeneous statement; not every TSD datum propagates with them | With a lifting `G`, `U' = L_max U + F`, `U − G ∈ D(L)` is uniquely solvable (skew-adjoint `L`) with energy bounds; on every bounded `Ω` the restriction `R` of a whole-space TSD solution (the plane wave) is the unique solution with its data and stays TSD, and from `U₀` it is `R + e^{tL}(U₀ − R(0))`, TSD iff the homogeneous part is (e.g. `U₀ − R(0) ∈ K*`); the fully discrete CN scheme on the three-row Whitney spaces of the cube is well posed for every `Δt`, with every `fem4gr` monitor bounded by the comparison residual, the initial error and the summed consistency errors; on `𝕋³` the CN iterates conserve energy and stay TSD, with phase `2 arctan(sω) ≠ 2sω` | `Feec.Evolution.isBoundarySolution_iff`, `Feec.Evolution.existsUnique_isBoundarySolution`, `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.restrict_unique`, `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.eq_add_waveGroup`, `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.mem_iff`, `Feec.Models.Cube.Inhomogeneous.whitney_existsUnique_cnStep3`, `Feec.Models.Cube.Inhomogeneous.whitney_norm_residuals_le`, `Feec.Numerics.PlaneWaveCube.exists_not_propagates`, `Feec.Numerics.PlaneWaveCube.cnTorusPlaneWave_props`, `Feec.Numerics.PlaneWaveCube.amp_eq_exp_phase` |

Limits of the repairs. Props 4.17, 4.19 and the Ch. 6 claim are repaired on domains without
boundary and on axis-parallel cubes only: on a curved bounded domain no boundary condition is
proved to propagate non-stationary TSD data (the mirror conditions do not form a complex there),
and the Ch. 6 system with mirror conditions is proved only on `(0, ½)³`, since it is not
dilation-invariant. The mirror conditions of Prop 4.17 are characterized on every open cube by
Green's formulas against `C¹` test functions (weak trace conditions); reading them as pointwise
traces `σ·n = 0`, `E_{nτ} = E_{τn} = 0`, `B_{ττ} = 0` is an interpretation, since traces of `L²`
fields are not formalized, and Prop 4.19 (`MirrorSym`, whose first operator is second order) is
not characterized this way. On cubes other than `(0, ½)³` the operators of (4.16) are dilation
conjugates, not identified with the weak Hessian and curl. The §4.10 repair is at the level of polynomial shape functions, without
a mesh or cochain projections. Prop 6.2 keeps the §6.3 finite element facts (`S₀,h` onto,
`grad` injective on `P₂Λ⁰ ⊗ V`, the elliptic projection) as hypotheses. For Ch. 7, which matrix
the thesis applies MINRES to is undetermined; both readings are treated. The Ch. 7 runs with
inhomogeneous data are covered through a lifting, the continuous problem on every bounded domain
and the discrete scheme on the Freudenthal meshes of `(0, ½)³` (its dilation to the unit cube of
`fem4gr` is not formalized); for the discrete scheme the consistency errors are inputs, with no
bound in `h` and `Δt`, and the interior spaces `V̊ₕ` are not shown nonzero. The §3.4 repair is
pointwise in a given frame on a global chart of `ℝ⁴`: no existence of solutions or of the `3 + 1`
frame, no local version on an open set, and no non-vacuum system.

## FEEC book coverage

Topics of [Arnold2018] (by its outline; chapter numbers are not checked against the book) and of
[AFW2006]/[AFW2010]. *Covered*: proved in the generality of the book. *Partial*: proved, but with
a named analytic input as an explicit hypothesis, or only for some instances. *Not*: absent.

| Book topic | Status | Lean modules / main theorems |
|---|---|---|
| Hilbert complexes: closed range ⇔ Poincaré, Hodge decomposition, cohomology ≅ harmonic forms, dual complex, compactness property | covered | `HilbertComplex.{Basic,Dual,Hodge,Compactness,CompressCompact}`: `Feec.HilbertComplex.hodge`, `Feec.HilbertComplex.closedRangeAt_iff_poincare`, `Feec.HilbertComplex.cohomologyEquivHarmonic`, `Feec.HilbertComplex.HasCompactPropertyAt.closed_and_fredholm` |
| Abstract Hodge Laplacian, solution operator `K` and its bounds | covered | `HilbertComplex.{HodgeLaplacian,HodgeSolution}`: `Feec.HilbertComplex.isSelfAdjoint_hodgeLaplacian`, `Feec.HilbertComplex.mem_ker_hodgeLaplacian_iff`, `Feec.HilbertComplex.hodgeLaplacian_solutionOp`, `Feec.HilbertComplex.norm_solutionOp_le`, `Feec.HilbertComplex.isCompactOperator_solutionOp` |
| Mixed formulation and its well-posedness | covered | `HilbertComplex.Mixed`: `Feec.HilbertComplex.infSup_mixedForm`, `Feec.HilbertComplex.existsUnique_mixed` |
| Variational theory: Lax–Milgram, Babuška–Nečas, Céa, Brezzi, Fortin | covered | `Variational.*`: `Feec.Variational.babuskaNecas_iff`, `Feec.Variational.InfSup.norm_sub_le_infDist`, `Feec.Variational.brezzi_iff` |
| Approximation of Hilbert complexes: subcomplexes, bounded cochain projections, discrete Poincaré and Hodge decomposition, harmonic gap | covered | `HilbertComplex.Approximation.{Subcomplex,CochainProjection,DiscreteHodge,MixedError}`, `Feec.HilbertComplex.Subcomplex.CochainProjection.existsUnique_mixed` |
| Quasi-optimal error estimate of the mixed method ([AFW2010], Thm 3.9) | covered | `Feec.HilbertComplex.Subcomplex.CochainProjection.norm_sub_le_infDist`, `Feec.HilbertComplex.Subcomplex.CochainProjection.norm_sub_le_infDist_domainSub` |
| Improved (duality) error estimates ([AFW2010], Thm 3.11) | partial | `Feec.HilbertComplex.Subcomplex.CochainProjection.norm_sub_u_le_improved`, with `η`, `δ`, `μ` defined (`improvedEta`, `improvedDelta`, `harmonicGap`) and bounded; that `η, δ → 0` (elliptic regularity) is shown for no concrete family |
| Eigenvalue problem: compact resolvent ⇒ eigenbasis | partial | `Feec.C0Group.eigenDense_of_compactResolvent`; instances `Feec.Models.Cube.DeRham.eigenDense`, `Feec.Models.Cube.Ident.eigenDense_gradCurl_cube`; convergence of discrete eigenvalues: not |
| Evolution: Hodge wave equation, semi-discrete convergence and rate | covered | `HilbertComplex.HodgeWave`, `Approximation.{SemidiscreteWave,Convergence}`: `Feec.HodgeWave.norm_sub_le_of_semidiscrete` |
| Evolution: Lumer–Phillips, Hodge heat equation | covered | `Semigroup.LumerPhillips`, `HilbertComplex.HodgeHeat`: `LinearPMap.isMDissipative_iff_exists_contraction`, `Feec.HilbertComplex.existsUnique_classicalSolution_heat`, `Feec.HilbertComplex.norm_heatSemigroup_sub_starProjection_le` |
| Exterior algebra and polynomial forms: Koszul complex, `P_rΛᵏ`, `P_r⁻Λᵏ`, direct sums, dimensions, exactness | covered | `Algebra.{ExteriorFibre,Koszul,PolynomialForm,PolynomialFormDim,Wedge}`: `Feec.Koszul.finrank_polyForm`, `Feec.Koszul.finrank_polyFormMinus`, `Feec.ExteriorFibre.wedgeForm_assoc` |
| Smooth forms, pullback, integration over simplices, Stokes' theorem | covered | `FiniteElement.{SmoothForm,SimplexIntegral,Stokes,MeshDivergence}`: `Feec.FiniteElement.simplexIntegral_extDeriv`, `Feec.FiniteElement.setIntegral_image_simplexMap_divergence` |
| `L²` de Rham complex on a domain: `HΛ`, `H̊Λ`, duality | covered | `Feec.Domain.deRham`, `Feec.Domain.deRham_dual_minimalComplex_d`, `Feec.Domain.deRham_minimalComplex_univ_eq_maximalComplex_univ` (any open `Ω ⊆ ℝⁿ`) |
| Closed range, compactness and harmonic forms of the de Rham complex | partial | proved on `𝕋ⁿ` (`Models.Torus.DeRham`: `Feec.Models.Torus.DeRham.window_hasCompactProperty`, `H^k ≅ Λᵏ`) and on `(0, ½)ⁿ` in the parity model (`Feec.Models.Cube.DeRham.hasCompactProperty`, `Feec.Models.Cube.DeRham.finrank_relative_harmonic_top`); not on Lipschitz domains (no Rellich, Gaffney or traces) |
| Simplicial meshes, shape regularity | covered | `Mesh.{Basic,Kuhn,Freudenthal,ShapeRegular}`: `Feec.Mesh.SimplicialMesh`, `Feec.Mesh.freudenthalMesh`, `Feec.Mesh.IsShapeRegular` |
| Degrees of freedom of `P_rΛᵏ(T)`, `P_r⁻Λᵏ(T)`: unisolvence, trace determination, commuting interpolants | covered | `FiniteElement.{Dof,LocalSpace,LocalDof}`: `Feec.FiniteElement.isUnisolvent_localDof`, `Feec.FiniteElement.isUnisolvent_localDofMinus`, `Feec.FiniteElement.polyInterp_extDeriv`, `Feec.FiniteElement.polyMinusInterp_extDeriv` |
| Global finite element spaces, conformity | partial | `FiniteElement.{Assembly,Conformity}`: assembly and conformity for any element family (`Feec.FiniteElement.LocalElement`, `Feec.FiniteElement.pieceL2_mem_maximal_domain`); the global family is instantiated only for Whitney forms, not for `P_r`, `P_r⁻` with `r ≥ 2` |
| Whitney forms and the lowest-order complex | covered | `FiniteElement.{Whitney,WhitneyComplex}`: `Feec.FiniteElement.whitneySubcomplex`, `Feec.FiniteElement.whitneySubcomplexMin`, `Feec.FiniteElement.finrank_whitney_globalSpace` |
| Bramble–Hilbert, interpolation error | partial | `FiniteElement.{BrambleHilbert,InterpolationError}`: `Feec.FiniteElement.norm_iteratedFDeriv_sub_taylorPoly_le`, `Feec.FiniteElement.norm_sub_transportInterp_le_of_isShapeRegular`; classical `C^{r+1}` form only (no Sobolev seminorms), and the reference-interpolant hypothesis is not instantiated for Whitney forms |
| Smoothed (bounded commuting) projections | partial | `FiniteElement.SmoothedProjection`, `Domain.StarShapedSmoothing`, `Models.Cube.Smoothing`: `Feec.HilbertComplex.Subcomplex.CommutingMap.toCochainProjection`, `Feec.FiniteElement.LocalElement.smoothedCommutingMap`; the estimate `‖v − Qv‖ ≤ ½‖v‖` on `Vₕ` is the hypothesis `Feec.Models.Cube.FEM.SmoothingEstimates` |
| Convergence of the finite element method | partial | on Freudenthal meshes of the cube, under `SmoothingEstimates`, the Poincaré inequality of `HΛ(Q)` and approximation by the Whitney spaces: `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_infDist`, `Feec.Models.Cube.FEM.SmoothingEstimates.norm_sub_le_meshSize`, `Feec.Models.Cube.FEM.maxwell_exists_tendstoUniformlyOn`; unconditionally only for spectral Galerkin on `𝕋ⁿ` (`Feec.Models.Torus.DeRham.tendsto_bandGalerkin`) |
| Other complexes: elasticity, Hessian, div-div, BGG | partial | `Feec.Domain.elasticityComplex`, `Feec.Domain.hessianComplex`, `Feec.Domain.divDivComplex` on open `Ω ⊆ ℝ³` with duality; abstract BGG (`HilbertComplex.BGG`); closed range on bounded domains and their finite elements: not |
| Maxwell's equations | covered | `Physics.Maxwell.*`: `Feec.Maxwell.pecForms_three_gauss_propagates`, `Feec.Maxwell.Medium.exists_anisotropic`, `Feec.Maxwell.Medium.ohmic_existsUnique`, `Feec.Maxwell.Medium.ohmic_magnetic_gauss_propagates` |
| Sobolev spaces, traces, elliptic regularity, Lipschitz domains | not | |

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
derivative" is not formalized. Bounded perturbations (Dyson–Phillips) and the Lumer–Phillips theorem
(`LinearPMap.isMDissipative_iff_exists_contraction`) are covered; the latter gives the Hodge heat
equation of every Hilbert complex (`Feec.HilbertComplex.heatSemigroup`). Semi-discrete convergence holds for every datum in `W`, and in the
thesis's form for `ξ₀ ∈ D(L)`; the error bound of Thm 4.14 needs `C¹(V)` solutions, which exist
for `ξ₀ ∈ D(L²)`, and no rate is formalized for `D(L)` or `W` data.

Mathlib has no Sobolev spaces with traces. Meshes, finite element spaces and Whitney complexes are
built here (`Feec.Mesh`, `Feec.FiniteElement`), but abstract results still take concrete complexes
as instances of abstract structures, with their analytic facts (closed range on general domains,
the estimates behind bounded cochain projections, density, regular decompositions) as hypotheses. The concrete
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
  `x ↦ a x + b`; for grad–curl the mirror boundary conditions are characterized on every open
  cube by Green's formulas against `C¹` test functions vanishing on the odd faces
  (`Feec.Models.Cube.Mirror.mem_wave_domain_cube_iff_trace`), for (4.16) and BGG only in the
  reflection sense.
  The de Rham complex of `(0, ½)ⁿ` in every dimension and degree is the parity model
  (`Feec.Models.Cube.DeRham`): fixed complexes of the reflections of the torus complex, with the
  compactness property, Poincaré constant `(2π)⁻¹` and the harmonic forms of both classes; its
  identification with `HΛ((0, ½)ⁿ)` and `H̊Λ((0, ½)ⁿ)` of `Feec.Domain.DeRham` is not formalized.
* Finite elements (`Feec.Mesh`, `Feec.FiniteElement`, `Feec.Models.Cube.FiniteElementMethod`):
  the Whitney complex on every conforming simplicial mesh is a subcomplex of `HΛ(Ω)` (of `H̊Λ(Ω)`
  with vanishing boundary DOFs, for strictly star-shaped `Ω`), and the smoothed interpolant
  `Π_h R` is a commuting map into it. The estimates of [AFW2010] §5.4 that make `J⁻¹ Π_h R` a
  uniformly bounded cochain projection (`‖v − Π_h R v‖ ≤ ½‖v‖` on `Vₕ`, from inverse estimates)
  are the explicit hypothesis `Feec.Models.Cube.FEM.SmoothingEstimates`; everything downstream
  (stability, quasi-optimality, `O(h)` rates, harmonic gap → 0, semi-discrete Maxwell) is proved
  from it.

The thesis states its Ch. 4 results with boundary conditions on a bounded `Ω` (§4.10, §6.3), so
the bounded-domain models are the faithful setting; `𝕋³` and `ℝ³` have no boundary and serve as
a contrast. For the boundary conditions printed in Prop 4.19, the hypotheses fail, and the
conclusion and the density fail on every ball (transported from the unit ball by affine maps,
`Feec.Models.BoundedDomain.SymDualGeneral`); other domains, and whether `K*` is nonzero there,
are not decided (on domains of revolution the sign of a boundary pairing decides, and it is not
formalized). On a general bounded domain no non-stationary element of `K*` is known;
`Feec.Models.BoundedDomain.gradCurl_coreSub_spectral` reduces the question to the existence of a nonzero TSD
eigenfield of `curl* curl`, and `Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff` narrows
it to one with `curl u ∉ H̊(curl)` (eigenfields with `u, curl u ∈ H̊(curl)` vanish on every bounded
domain, by a Pohozaev identity; the expectation that `K*` is stationary when every boundary
component is a sphere is not formalized). Both need pure point spectrum; that is derived from a compact
resolvent (`Feec.C0Group.eigenDense_of_compactResolvent`) and proved on `𝕋³` and on every open
cube (`Feec.Models.Cube.Ident.eigenDense_gradCurl_cube`, by compression of the torus), but on no
other bounded domain (it needs Rellich–Kondrachov and Maxwell compactness). Not formalized for Ch. 6: the
multiplier form (6.2) and the transfer of the bounded-domain failure to the semi-discrete scheme
(6.5). Ch. 7 states no boundary conditions; its runs (read from `fem4gr`) prescribe `σ`, `E × n`
and `B · n` from the exact plane wave. These inhomogeneous data are formalized by a lifting
(`Feec.Evolution.BoundaryLifting`, `Feec.Models.Cube.Inhomogeneous`): the plane wave is the unique
solution with its own data and stays TSD on every bounded domain, a TSD perturbation of its
initial value does not (`Feec.Numerics.PlaneWaveCube.exists_not_propagates`), and the fully
discrete scheme on the Whitney spaces of the cube is well posed with its constraint monitors
bounded by the consistency error. Not formalized for Ch. 7: bounds of the consistency error in
`h` and `Δt`, the discrete-divergence monitor on Whitney spaces, `B · n` (a remark: it is not a
condition of the continuous problem), the dilation to the unit cube and periodic Whitney spaces.

Pseudo-Riemannian geometry is done in components, at the jet level and for fields on a global
chart of `ℝⁿ` (metrics of any signature, Christoffel symbols of a `C³` metric, the second Bianchi
identity and its contractions, `Feec.Geometry.Bianchi`). The nonlinear Einstein–Bianchi system
(§3.4) is derived in an orthonormal frame for every vacuum metric on `ℝ⁴`
(`Feec.Physics.EinsteinBianchi.Nonlinear`), with the frame and its connection coefficients as
given data; not formalized: existence of solutions or of the `3 + 1` frame (the Frobenius
theorem enters only through `Feec.EinsteinBianchi.extrinsic_symm_iff_bracket`), local versions
on an open set (so charts such as Schwarzschild's are not covered as stated), the non-vacuum
system of [ACBY1997], and a vacuum example with `E, B ≠ 0`. Out of scope: the concrete finite
element computations of §5.3 (Props 5.7–5.9 beyond the abstract core of Prop 5.7), which need
`P₂` and second-kind Nédélec/BDM spaces as global families, and the numerical results of Ch. 7
beyond the plane-wave runs (error tables and convergence rates). All cited works are collected in [`references.bib`](references.bib).
