# Final refactor plan for `Feec`: organize by mathematics, not by thesis chapter

I edited and committed nothing in the repo. The scratch files are under `/tmp/feec_refactor_design/`:

| File | What it checks | Result |
|---|---|---|
| `Core.lean` | operator, semigroup, evolution and complex structures | compiles, no `sorry` |
| `Complex.lean` | dual complex, `Fin 3` window, Fourier and inf-sup layers | compiles; `dual` has 4 `sorry` fields on purpose (their proofs move over from `Ch4/Adjoint`) |
| `Snapshot.lean` | dumps every old theorem | ran correctly on `Feec.Foundation.Operators` |
| `AxiomAudit.lean` | flags non-standard axioms | ran correctly; reported clean |

I ran each with `lake env lean` against the pinned Mathlib (rev `6e2a148e`).

**Inventory today:** 77 files, 59,669 lines, about 3,660 `theorem`/`lemma`, 1,098 definitions/structures, and 164 thesis-numbered theorems (`thm_*`, `prop_*`, `cor_*`, `lemma_*`, `ch6_*`).


> **Docstring citations (user decision, 2026-10-17).** Thesis numbering is banned only in Lean
> *identifiers* (declaration, module and namespace names). Docstrings should keep, and may add,
> references to the corresponding thesis chapter, section, theorem, proposition, equation and
> page, e.g. `Thesis: Prop 4.17 (§4.10, p. 66), corrected` or `[QuennevilleBelair2015, Thm 4.6]`.
> Naming greps (`prop_[0-9]`, `Ch[0-9]`, …) apply to identifiers only, never to comments or
> docstrings; do not strip thesis references from documentation.


> **Citation convention (user decision, 2026-10-17; Mathlib/doc-gen4 style).**
> * Every cited work has a BibTeX entry in `docs/references.bib` (key *AuthorYear*, DOI when one
>   exists, verified against Crossref). No citation without an entry.
> * Inline citations are bare links `[Key]`, with the location *outside* the brackets:
>   `[QuennevilleBelair2015], Prop. 4.17 (§4.10, p. 66)`, `see [AFW2010], Thm 3.5`.
>   Never `[Key, Thm 4.6]` (doc-gen4 would read the whole bracket as the key).
> * Each module docstring declares its bibliography on a line of its own (user decision,
>   2026-10-21), `Bibliography: [references.bib](<relative path>/docs/references.bib)`, so that
>   `leantex` (and doc-gen4) compile the references from the bib file; checked by
>   `lake exe feec-citations`.
> * Each module docstring ends with `## References` listing
>   `* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]`
>   (author(s), italic title, then `[Key]`).
> * Thesis traceability uses the same convention (`[QuennevilleBelair2015], Prop. 4.17, corrected`);
>   the separate `Thesis:` tag is retired, and `lake exe feec-thesismap` reads these citations.
> * Wave W6 rewrites existing citations to this form (mechanically where possible) and adds
>   a citation check, now `lake exe feec-citations` (every `[Key]` in `Feec/` exists in `references.bib`; no
>   `[Key, …]` forms; every module has a `## References` section) to the verification gate.

> **Status (2026-10-22): minimality pass.** `lake exe feec-deps` (`scripts/FeecCheck/Deps.lean`)
> measures what nothing kept uses (seeds: the `main` rows of `map.tsv`, the declarations named in
> the docs, cited docstrings, metaprograms and coercions) and lists wrappers, duplicate statements
> and name twins; `--strip FILE OUT` deletes the dead groups of a file. Eight parallel tasks and a
> merge deleted the dead groups, collapsed wrappers and duplicates and proved twins once, with no
> main statement weakened. Before → after: 329 → 327 modules (`ForMathlib.LinearPMap.CompPartial`
> and `Models.BoundedDomain.DeRham`, left without declarations, are deleted; `deRham3` is the case
> `n = 3` of `Feec.Domain.deRham`), 220,777 → 198,824 lines in `Feec/**/*.lean`, 17,556 → 15,658
> user declarations (13,891 → 12,133 theorems), dead groups 2,422 (20,714 lines) → 408 (3,541
> lines with the final docs as seeds; all kept on purpose: `rfl` simp lemmas that bare `simp`
> uses, the second Bianchi identity, the dualities of the Hessian, div-div and elasticity
> complexes, isotropic media, non-vacuity witnesses, and the results a module docstring states in
> **bold**, see below), wrappers 412 → 282,
> duplicate sets 92 → 44, name-twin sets 93 → 76 (10,283 → 7,061 lines). The gate passes;
> `map.tsv` marks the deleted declarations `deleted-helper` (none `main`).
>
> A review of the pass found that `feec-deps` does not seed from module docstrings, so it had
> deleted results the docstrings advertised in bold (and their docstring mentions). These are
> restored from `ca5b417` with the helpers they need (+4.4k lines, 2 modules): the tangential-class
> rates `mixed_rate_polyTr(_of_polyOrderAt)`, `mixed_rate_lagrangeP2Tr`,
> `norm_sub_le_windowTr_poly_smooth`, `IsCsFormTr.d_eq` (`Cube.TangentialRate`); uniqueness and
> the growth bound of the bounded perturbation theorem (`Feec.Evolution.Perturbation`:
> `C0Semigroup.eqOn_perturb`, `existsUnique_generator_eq_vadd`, `eqOn_of_generator_eq`;
> `C0Semigroup.norm_perturb_le` in `Feec.Semigroup.Perturbation`); the mirror complex between
> the minimal and maximal realizations (`Feec.Models.Cube.MirrorDirichlet`);
> `HilbertComplex.hodge_unique` and the real Hodge decomposition (`HilbertComplex.Conj.hodge_real`,
> `SymCurl.hodge_real`);
> `Domain.ConstCoeffComplex.dual_maximalComplex_d`, `deRham_dual_maximalComplex_d`; the harmonic
> forms of the parity and mixed models (`Cube.DeRham`, `Cube.DeRhamPartial`) and the Hodge star
> exchange; `LumerPhillips.existsUnique_normalized_contraction`,
> `IsSkewAdjoint.eqOn_group_semigroup`, `isSelfAdjoint_S_of_isSymmetric`;
> `SpectralGalerkin.norm_waveGroup_sub_waveGroup_band`; the cube corollaries
> `gradCurl_coreSub_spectral_Q/_cube` (`Cube.EigenDense`); `mirror_exists_iff(_compatible_u)`,
> `cubeWave_exists_iff`; and the non-vacuity witnesses `waveFEM_nonvacuous(_cube)`,
> `staticFEM_nonvacuous(_coupled)(_cube)` (with the manufactured and coupled solutions of
> `Cube.WeakSymmetryFEM`/`WeakSymmetryWave`), `waveFEM_rate_of_mem_domain_nonvacuous`,
> `cubeWave_rate_sobolev_nonvacuous`. The rows of `map.tsv` whose old target is back are
> restored. Not restored: `planeWave_unique` (`Inhomogeneous.WholeSpaceTSD.restrict_unique`
> covers it on every bounded domain) and `mirror_waveFEM_rate` (`C²` hypothesis; superseded by
> the `D(L³)` rate of `Cube.MirrorWaveRegularity`).

> **Status (2026-10-21): the gate is in Lean.** The checks of §5 run as `lake exe feec-gate`
> (library `FeecCheck`, `scripts/FeecCheck/`; Lean only, no shell or Python): `feec-citations`
> (citation convention), `feec-layering` (import order of §1), `feec-axioms` (axiom audit),
> `feec-naming` (banned identifiers), `feec-thesismap` (`--check`: `docs/THESIS_MAP.md` up to
> date; without it, regenerate) and `feec-mapcheck --strict` (migration coverage), plus
> `feec-snapshot OUT` (the one-time declaration snapshot). They replace `scripts/{AxiomAudit.lean,
> MapCheck.sh, CheckCitations.sh, ThesisMap.sh, DocDump.lean, Snapshot.sh, Snapshot.lean}`, whose
> results they reproduce on the tree of 2026-10-21 (identical `THESIS_MAP.md` up to its header, an
> identical snapshot, the same errors on planted violations). The naming check is new as a
> program: it found three thesis-numbered names that the old greps (`prop_[0-9]`) missed,
> `exists_counterexample_prop59_two{,_bestApprox}` and `not_exists_prop59_two_bound`, now
> `Feec.Models.Cube.WeakSymmetry.{exists_interpolationError_ge, exists_bestApproxError_ge,
> not_exists_interpolationError_bound}`; of the process suffixes of §1 it does not check `_res`
> and `_max`, which are ordinary vocabulary (`Feec.Stone.res`, `mul_le_max_one`). A review then
> found that camelCase and equation numbers got through (`ForcingThm43`, `bggComplex_eq61`): the
> check now also bans `Thm`/`Prop`/`Cor`/`Lemma` followed by a digit at any camelCase boundary
> and `eq`/`Eq` followed by two digits (`eq61`, `eq_6_1`; one digit, as in `eq1 : Fin 3 ≃ …`,
> and Lean's equation lemmas `f.eq_1` are allowed). `ForcingThm43` is now
> `Feec.ForcingDLOrW11` (with `.admissible`), the alias `ForcingThm43Full` of
> `ForcingClass.admissible` is deleted, and `bggComplex_{eq61, of_eq61}` are now
> `Feec.Models.BoundedDomain.bggComplex_{weakEqs_of_isStrongSolution,
> isStrongSolution_of_weakEqs}`. The status notes below name the old scripts as they were at the
> time.

> **Status (2026-10-17): waves W0–W6 are done.** `Feec/Legacy` (57 modules) and
> `Feec/Models/Cube/Bridge.lean` are deleted; the cube models are built on `Feec.Models.Torus`,
> `Feec.Fourier` and `Feec.Models.BoundedDomain` alone, and every module of `Feec/` is imported by
> `Feec.lean`. The layer order of §1 holds for every import (siblings of one tier, e.g.
> `Fourier`/`Geometry` → `Algebra` and `Counterexamples` → `Physics`, import each other acyclically);
> in particular `Semigroup` no longer imports `Evolution`: the orbit calculus is
> `Feec.Semigroup.Orbit`, Hille's theorem is `Feec.ForMathlib.LinearPMap.Integral`, and the
> uniqueness half of the bounded perturbation theorem (via Duhamel) is `Feec.Evolution.Perturbation`.
> Every declaration of the pre-refactor tree has a row in
> `docs/migration/map.tsv` pointing at a current name or marked `deleted-helper` (non-main rows
> only); `scripts/MapCheck.sh --strict` passes (5131/5131 old declarations, main 269/269).
> `scripts/CheckCitations.sh` implements the citation gate above and passes: every `[Key]` is in
> `references.bib`, no `[Key, …]` form, no `Thesis:` tag (all 431 rewritten to
> `[QuennevilleBelair2015], …`), and every module's `## References` lists each key it cites as
> `* [Author(s), *Title*][Key]` (authors and title as in `references.bib`), then the location. The verification gate
> is: `lake build` (no errors, no warnings), `lake env lean scripts/AxiomAudit.lean`,
> `scripts/MapCheck.sh --strict`, `scripts/CheckCitations.sh`, `scripts/ThesisMap.sh` (regenerate
> `docs/THESIS_MAP.md`), and the naming greps of §5. W7 (§6) is open.

> **Status (2026-10-18): W7 and W8 gated.** 42 new modules (Lumer–Phillips and the Hodge heat
> equation; the solution operator `K`, the quasi-optimal and improved estimates of the mixed
> method; reweighting, Maxwell media, Ohmic loss and `k`-form Maxwell; the `L²` de Rham complex
> of `k`-forms on any open `Ω ⊆ ℝⁿ`, Hessian, div-div and elasticity complexes, minimal = maximal
> on `ℝⁿ`; dimensions of `P_rΛᵏ`, `P_r⁻Λᵏ` and the wedge product; the new layer `Feec.Mesh`
> (simplicial, Kuhn and Freudenthal meshes, shape regularity); in `Feec.FiniteElement` Stokes on
> simplices, the local spaces with unisolvent DOFs and commuting interpolants, Whitney forms,
> assembly, conformity, Bramble–Hilbert, interpolation error and smoothed projections; on cubes
> the de Rham parity model, eigenbases on every open cube, even Fourier smoothers and the finite
> element method on Freudenthal meshes) are imported by `Feec.lean`, and the full gate passes
> (clean build with no warnings, AxiomAudit, `MapCheck.sh --strict`, `CheckCitations.sh`,
> `ThesisMap.sh`, naming and layering greps). `Feec.Mesh` imports only Mathlib and sits beside
> `Algebra`/`Geometry`, below `FiniteElement`. What each book topic proves, and what is still a
> hypothesis, is the table "FEEC book coverage" of `docs/OVERVIEW.md`; §6 below records the
> status per rank.

> **Status (2026-10-18): thesis-rest gated.** 9 new modules (`Feec.Geometry.Bianchi`,
> `Feec.Physics.EinsteinBianchi.Nonlinear`: the second Bianchi identity and the nonlinear EB
> system of §3.4; `Feec.Evolution.BoundaryLifting`, `Feec.Models.Cube.Inhomogeneous`,
> `Feec.Numerics.PlaneWaveCube`: the Ch. 7 runs with inhomogeneous data; `Feec.Models.Cube.MirrorTrace`,
> `Feec.Models.BoundedDomain.{MovingTSD, SymDualGeneral}`, `Feec.Counterexamples.EveryBallSymTSD`:
> Props 4.17/4.19 with trace conditions on cubes, on every ball and on general bounded domains)
> are imported by `Feec.lean`, and the full gate passes. `ThesisEB` was renamed `ExtrinsicEB`
> (with `nonlinearEB_iff_extrinsicEB`, `vacuum_extrinsicEB`, `minkowski_extrinsicEB`) for the
> naming grep.

> **Status (2026-10-18): finite element hypotheses gated.** 16 new modules discharge the three
> hypotheses of `Feec.Models.Cube.FiniteElementMethod` on the Freudenthal meshes of `(0, ½)ⁿ`:
> the smoothed-projection estimates (`Feec.FiniteElement.InverseEstimate`,
> `Feec.Models.Cube.SmoothingEstimates`), the Poincaré inequalities of `HΛ` and `H̊Λ` through the
> identification of the parity model with `Feec.Domain.DeRham` on the cube
> (`Feec.Models.Cube.DeRhamIdent` and
> `Feec.Models.Cube.DeRhamIdent{Ext,Cutoff,Forms,Trunc,Poincare,FEM,Rate}`), and the Whitney
> interpolation error (`Feec.FiniteElement.WhitneyInterpolation`,
> `Feec.HilbertComplex.Approximation.GraphApprox`, `Feec.Models.Cube.{WhitneyApprox,WhitneyRate}`).
> `Feec.Models.Cube.FiniteElementConvergence` and the Maxwell instances (now in
> `Feec.Instances.Maxwell`) state the results with no hypothesis. All are imported by `Feec.lean` and the full gate passes.

> **Status (2026-10-19): thesis-fem gated.** 19 new modules give the higher-order and the BGG
> finite elements on the Freudenthal meshes of `(0, ½)³` and the Ch. 5–6 finite element claims:
> the global families `P_rΛᵏ`, `P_r⁻Λᵏ` of every admissible sequence with their inverse and
> interpolation estimates and partial boundary conditions
> (`Feec.FiniteElement.{PolyElement,PolyComplex,PolyElementMixed,PolyInverseEstimate,PolyInterpolation}`),
> vector-valued spaces and the weak-symmetry maps (`Feec.FiniteElement.{TensorElement,WeakSymmetryMaps}`),
> their smoothed projections, convergence and rates (`Feec.Models.Cube.{PolySmoothingEstimates,
> PolyFiniteElementConvergence,PolyRate}`), the BGG data (4.16) on the cube and Props 5.7–5.9
> (`Feec.Models.Cube.{WeakSymmetryComplex,WeakSymmetryEstimates}`), Thm 5.5 with weak consistency
> (`Feec.HilbertComplex.BGG.WeakConsistency`, `Feec.Models.Cube.WeakSymmetryFEM`,
> `Feec.Physics.EinsteinBianchi.StaticFEM`), the elliptic projection (6.4) and the convergence of
> (6.3) (`Feec.HilbertComplex.BGG.{EllipticProjection,DiscreteWave}`), and the scheme (6.5) of
> Table 6.1: well posed ⇔ (C2), energy-stable, `O(h)` convergent (`Feec.Models.Cube.WeakSymmetryWave`,
> `Feec.Physics.EinsteinBianchi.WaveFEM`). The rates keep the regular decomposition
> `Feec.Models.Cube.WeakSymmetry.CurlPotential` as the one hypothesis. `Γ ≅ H̊²(Q)` with the first
> space of the matrix model `Feec.Models.BoundedDomain.bggComplex`
> (`Feec.EinsteinBianchi.WaveFEM.gamma_equiv_hessMin`). The mirror scheme
> (`Feec.Models.Cube.MirrorWeakSymmetryFEM`): BGG elements with the mirror parities, `S₀,ₕ` onto,
> `grad` injective, well posed ⇔ (C2), energy-stable, constant mode decoupled. Not built: the
> convergence of the mirror scheme (continuous complexes with boundary conditions on part of `∂Q`,
> partial-boundary conformity, mixed smoothed projections) and the identification of the second
> space with the matrix model. All are imported by `Feec.lean` and the full gate passes.

> **Status (2026-10-19): gaps gated.** 35 new modules close or narrow the open items of the
> thesis-fem status above. (G1) The regular decomposition `CurlPotential` is a theorem
> (`Feec.Models.Cube.{TorusHelmholtz,ShellExtension,RegularDecomposition}`,
> `Feec.Physics.EinsteinBianchi.Unconditional`), and the Ch. 5–6 rates hold for solutions `C²` up
> to `∂Q` with vanishing tangential traces instead of flat ones
> (`Feec.Models.Cube.{TangentialRate,WeakSymmetryTangentialRate}`,
> `Feec.Physics.EinsteinBianchi.{WaveFEMTangential,WaveFEMTangentialCube}`). (G2) The de Rham
> complexes `HΛ_J(Q)` with conditions on part of `∂Q`, their conforming finite elements and parity
> smoothers (`Feec.Models.Cube.{DeRhamPartial,DeRhamPartialIdent,DeRhamPartialFEM,ParitySmoother,
> ParitySmoothingEstimates}`), BGG convergence modulo harmonic forms
> (`Feec.HilbertComplex.BGG.Harmonic`), and the convergence of the mirror scheme (6.5) to the TSD
> solution (`Feec.Models.Cube.{MirrorWeakSymmetryComplex,MirrorWeakSymmetryConvergence,
> MirrorWeakSymmetryTSD}`). (G3) Sobolev spaces on the cube and rates `h^{min(s,1)}`
> (`Feec.Models.Cube.{Sobolev,SobolevRate}`). (G4) The forms model is the matrix model, and (6.5)
> converges for every datum in `D(L)`, to a solution that leaves TSD
> (`Feec.Physics.EinsteinBianchi.{MatrixModel,BoundedFailure,BoundedConvergence}`,
> `Feec.Models.Cube.WeakSymmetryConvergence`). (G5) `O(h + Δt²)` error of the Ch. 7 scheme and its
> dilation to the unit cube (`Feec.Models.Cube.InhomogeneousError`,
> `Feec.Numerics.PlaneWaveCubeError`). (G6) Boxes with unequal sides
> (`Feec.Domain.DiagonalPullback`, `Feec.Models.Box.{RowWise,EigenDense,Mirror}`,
> `Feec.Counterexamples.BoxStationary`); general bounded domains stay open. (G7) Parallelepipeds and
> domains star-shaped with respect to a ball (`Feec.Domain.FormPullback`,
> `Feec.FiniteElement.{ShapeRegularInverse,ShapeRegularSmoothing}`,
> `Feec.Models.{Parallelepiped,StarShaped}.FiniteElement`; the Poincaré inequality is the one
> hypothesis on star-shaped domains). What remains is listed in `docs/OVERVIEW.md` (limits of the
> repairs, FEEC coverage, scope). All are imported by `Feec.lean` and the full gate passes.

> **Status (2026-10-20): open items narrowed, gated.** 15 further modules. Compactness and
> eigenbases: compactness off the kernel (`Feec.HilbertComplex.EigenDenseKernel`), Rellich on
> bounded open sets (`Feec.Domain.Rellich`, `Feec.Models.BoundedDomain.Compactness`), bi-Lipschitz
> pullbacks (`Feec.Domain.LipschitzPullback`) and Weber compactness, hence `EigenDense`, on domains
> star-shaped with respect to a ball (`Feec.Models.StarShaped.EigenDense`); on the unit ball no
> TSD eigenfield is `C²` up to the boundary (`Feec.Counterexamples.{BallEigenfields,BallEigenDense}`;
> stationarity of `K*` there reduces to `MaxwellEigenfieldRegularity`). Approximation: the `L²`
> Bramble–Hilbert lemma (`Feec.FiniteElement.BrambleHilbertL2`), `Hᵐ` by weak derivatives and rates
> `h^{min(s, r_eff)}` on the cube (`Feec.Models.Cube.{SobolevWeak,SobolevRateHigh}`), higher-order
> families on star-shaped domains and on every mesh family of a parallelepiped
> (`Feec.Models.StarShaped.{PolySmoothing,PolyFiniteElement}`). BGG rates: Sobolev data with the
> thesis' conditions (`Feec.Models.Cube.WeakSymmetrySobolevRate`), `D(L³)` data under multiplier
> bounds (`Feec.Physics.EinsteinBianchi.WaveFEMRegularity`) and, with mirror conditions, with no
> hypothesis (`Feec.Models.Cube.MirrorWaveRegularity`). `docs/OVERVIEW.md` lists what remains.
> All are imported by `Feec.lean` and the full gate passes.

> **Status (2026-10-30): the FEEC theorem (crown), instance verdicts.** The verdicts of the
> Einstein–Bianchi rows are structures: `TorusVerdict`, `MirrorVerdict`
> (`Feec.Instances.EinsteinBianchi`) extend `ConstrainedFEEC.Verdict` of `torusFEEC`, `mirrorFEEC`
> by the one field `isReducing` (propagation and the residual bounds follow from the parent,
> `ConstrainedFEEC.Verdict.residual_rate`); `TorusSobolevVerdict`, `MirrorSobolevVerdict` extend
> them (`mem_domain_sobolev`, `rate_sobolev`, `tsd_residual_rate_sobolev`);
> `AbsorbingVerdict` (`Feec.Instances.EinsteinBianchiAbsorbing`) extends `DissipFEEC.Verdict` of
> `absorbingGalerkin`; `MirrorFEMVerdict`, `StandardCubeVerdict` (model theorems, no layer theorem
> upstream) have named fields. `FeecCheck.InstanceVerdicts` keeps the old conjunctions.

> **Status (2026-10-27): analytic BGG on `L²`, open item.** The Hessian, elasticity and div-div
> verdicts (`Feec.Domain.BGGRealization`) assume only the regular decompositions after `J`
> (`HilbertData.RegularDecomposition`) and finite-dimensional cohomology of the `L²` de Rham rows
> `deRhamVec 1`, `deRhamVec 3`. Neither is discharged on any nonempty `Ω`: the cube regular
> decomposition (`Feec.Models.Cube.WeakSymmetry.curlPotential`) is for `H̊(curl)` (minimal
> complex, form proxies), `H(div)` has none, and `deRhamVec m` is not identified with `deRham 3`
> (whose cube cohomology is known, `Feec.Models.Cube.DeRhamIdentFEM`).

> **Status (2026-10-27): open items after the five crown extensions.** Proved: the fully discrete
> error `O(hᵅ + τ^{p/(p+2)})` uniformly in `h` for every one-step `TimeScheme` and every rate-class
> datum in `D(A)` (`Feec.HilbertComplex.DissipFEEC.TimeScheme.norm_S_sub_sol_le_uniform`, crown
> fields `rate_uniform_iterates`, `wave_uniform`, `heat_uniform`); the cubical `Q_b⁻Λ` conforming
> family with Jackson rates (`Feec.Models.Cube.FEM.qMinusFamily`); a nonzero velocity in `ker 𝐝†`
> for slip Stokes on the cube (`Feec.Instances.Corollaries.Cube.FEM.slipStokes`); A-stable rational
> schemes and implicit Runge–Kutta methods as `TimeScheme`s by von Neumann's inequality
> (`Feec.HilbertComplex.DissipFEEC.rationalScheme`). Open: the sharp uniform order `τᵖ` on all
> Jackson data, parabolic nonsmooth-data smoothing; `Q_b⁻Λ` in `H̊Λ` (PEC), serendipity elements, a
> non-vacuity witness for `qMinusJackson`; a closed-form slip velocity in `D(Δ)`; explicit
> Runge–Kutta under a CFL condition, trajectory consistency of general rational schemes.

> **Status (2026-10-28): physics bridges to the crown.** The strong-symmetry EB systems (4.14),
> (4.16) are read through the FEEC theorem on `𝕋³`, `ℝ³`, mirror cubes and boxes
> (`Feec.Instances.EinsteinBianchiGradCurl`), with the TT plane waves of linearized gravity as exact
> eigenmodes (`GradCurl.planeWave_verdict`: amplitudes, Fourier image and exact discrete solutions)
> and Prop 3.6 for the first variation of the nonlinear system
> (`Feec.EinsteinBianchi.tsd_propagates_variation`, consumed by no verdict); for every
> discretization of the thesis' complex on bounded domains the data with vanishing TSD residuals
> are `K*` (`Feec.Instances.EinsteinBianchiBounded`); Maxwell for forms, every discretization
> (`Feec.Instances.MaxwellForms`); Sobolev rates on the cube (`Corollaries.Cube.FEM.feec_sobolev`).
> Open: a conforming family of the thesis' complex and of `pecForms` (both verdicts are
> conditional until one exists); the identification of the strong solutions of (4.14) with values
> in `K` with the (weak) solutions of the EB system; the real plane-wave fields as elements of
> `L²(𝕋³)`; the forms system on `Q` as the `H̊Λ` window of `cubePEC` (index casts `k + ↑i`); a
> nonzero family of vacuum metrics for `tsd_propagates_variation`; a route through the crown for
> the `O(h)` rates of scheme (6.5) (`Feec.EinsteinBianchi.WaveFEM`, not a `ConstrainedFEEC`).

> **Status (2026-10-28): discrete BGG tied to the crown.** Stacked conforming families
> (`Feec.BGG.HilbertData.StackedFamily`: families of the two rows with `S Ṽₕ ⊆ Vₕ`, `πₕ S = S π̃ₕ`)
> give conforming families of the derived complex of the domain complexes
> (`Feec.BGG.BoundedData.StackedFamily.derived`, through `Feec.HilbertComplex.ConformingFamily.domain`)
> and of the `L²` twisted complex (`Feec.BGG.HilbertData.StackedFamily.twist`), so the crown applies
> (`Feec.BGG.HilbertData.StackedFamily.bggVerdict`; `Feec.Domain.hessianFEEC`,
> `Feec.Domain.elasticityFEEC`, `Feec.Domain.divDivFEEC`). Open: the regular decompositions and the
> cohomology of `deRhamVec m` (as above), the `L²` realization of the derived complex (the verdicts
> are in graph norms), a finite element stacked family (only the full families, `πₕ = id`, are
> constructed), and the weak-symmetry elements
> (`Feec.HilbertComplex.BGG.Discrete`, discrete connecting maps `Πₕ S`), hence elastodynamics with them.

> **Status (2026-10-28): every result tied to the crown.** After the perturbation, reweighting,
> sharpness, physics-bridge, lifting and discrete-BGG rounds, 14 of 392 modules feed nothing that
> reaches `Crown.lean` through imports (96 of 377 before); the README lists them. Open across the
> rounds: rates for perturbed and forced problems; a discretization of the thesis' complex on
> bounded domains and of `pecForms`; a finite element stacked BGG family and the weak-symmetry
> bridge (scheme (6.5)); real anisotropic medium factors; the identification of the Ch. 7
> compression with the crown's `Lₕ`; finite speed of propagation for damped absorbing problems.

> **Status (2026-10-28): the crown over approximating families.** `ApproxComplexCrime.feec`
> (`Crown.lean`) is the FEEC theorem for Holst–Stern families with an inner-product and a cochain
> defect; conforming families are its zero-defect case (`ConstrainedFEEC.toCrime`, the last
> field `crime` of `ConformingFamily.Verdict`; `FeecCheck.Crown.crown_old_verdict` keeps the old
> verdict). The weak-symmetry scheme (6.5) is an instance under both boundary conditions with
> rates (`Feec.Instances.EinsteinBianchiFEMCrown`), which ties
> `Instances.EinsteinBianchi{FEMDefect, Gauss}`, `Models.Cube.WeakSymmetrySobolevRate` and
> `EinsteinBianchi.{Unconditional, WaveFEMRegularity}` to the crown. Open: a non-stationary datum in
> the Sobolev rate class of the thesis' boundary conditions.

> **Status (2026-10-28): every module on the crown's tree.** With the crime crown, the signed
> Crank–Nicolson systems (`FullVerdict.crankNicolson_signed`, from `TimeStepping.BlockMatrix`),
> the discrete inf-sup by Fortin operators (`StaticVerdict.infSup`), the vector-proxy Maxwell
> verdict (`Instances.Maxwell.vec_maxwellFEEC`, from `Algebra.Proxy3`) and the by-reference
> `crownCorrections`, 0 of 394 modules are off the tree (14 of 392 before). Open: a basis adapted
> to the parity grading in an instance; the three-block `IsFullCNStep` against `Lₕ`; the PEC side
> of the proxies; a bridge from the wave-group orbits to `IsMixedWeak`.

## 0. Decisions

Design 2 is the base: all three judges picked it. The grafts below come from Designs 0 and 1.

| Question | Decision | Why |
|---|---|---|
| Where thesis numbering lives | **No thesis layer in Lean.** Traceability goes in `docs/THESIS_MAP.md` plus a `Thesis: Prop 4.17 (corrected)` tag in docstrings (superseded 2026-10-17 by the citation `[QuennevilleBelair2015], Prop 4.17 (corrected)`; see the citation convention above). | You asked not to call things "chapter 4"; that overrides Designs 0 and 1, which kept a `Feec/Thesis` layer. |
| Indexing | `HilbertComplex (c : ComplexShape ι) W` with `d i j` and a `shape` field. Concrete complexes use `ComplexShape.up ℤ` or a finite window. | Checked in Lean: the dual is `c.symm` with the same spaces, so it needs no casts. |
| Short complexes | `ShortHilbertComplex` (the old `HilbertComplex2`) embeds as a window on `ComplexShape.fin3`. | Checked: `ComplexShape.up (Fin 3)` is wrong because it wraps 2 → 0. The `match`-defined `W3` family resolves its instances and `W3 … 1 = W₁` holds by `rfl`. |
| Total space for Dirac and wave operators | `PiLp 2` over a finite window, not `lp` over all of ℤ. Zero padding uses `PUnit`. | Checked: `InnerProductSpace` and `CompleteSpace` are found for the window. `PUnit` has an `InnerProductSpace` instance (`InnerProductSpace/Defs.lean:609`). |
| Scalars | `RCLike 𝕜` in every abstract layer. Time derivatives need `[NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]`. | Checked: the generator domain fails to typecheck without them. Mathlib's Lax–Milgram is ℝ-only, so the ℂ version is derived from Babuška–Nečas. |
| Reality condition | Its own lemma (`HilbertComplex/Reality`, `Fourier/Reality`), **not** a `ReducingSubcomplex`. | Conjugation is antilinear, so its fixed set is not a ℂ-submodule. Designs 0 and 1 got this wrong. |
| Graph space | `GraphSpace T := ↥T.graphL2`. | Checked: avoids a norm diamond with the subtype norm. |
| Transport between complexes | One `ScaledEmbedding` structure. `map`, `smul`, `compress` and `pullbackAffine` are instances of it. | Graft from Design 0. Checked in Lean, including the chain-rule factors `dScale`. |
| Order of semigroup theory | Stone → Dyson–Phillips perturbation → Lumer–Phillips. | Perturbation already covers Ohmic Maxwell and lower-order terms; it is much cheaper than Lumer–Phillips. |
| Compact resolvent ⇒ eigenbasis | Short and scheduled early. | Checked: Mathlib already has the compact self-adjoint spectral theorem (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`, `Spectrum.lean:442`). Design 1 said it was missing. |
| Window of a longer complex | Its wave operator is the wave of the **truncated** complex, not a restriction of the full one. | The adjoints change at the window ends. |

## 1. Module tree, namespaces, naming

```
Feec/
├── ForMathlib/                       -- imports only Mathlib; Mathlib namespaces (LinearPMap, MeasureTheory.Lp, …)
│   ├── LinearPMap/{Skew,GraphSpace,Reducing,Intertwines,ClosedRange,Bounded}.lean
│   ├── Lp/{CountEquiv,ProdEquiv}.lean          -- lp ≃ₗᵢ Lp count (ae_count_iff); Lp(E×F) ≃ Lp E × Lp F
│   ├── Analysis/{Gronwall,Inequalities}.lean   -- decay-rate Gronwall; young/absorb/sq_norm_add3_le
│   ├── Calculus/{Partial,TimeSlice}.lean
│   └── Homology/Subcomplex.lean               -- subcomplex/quotient of modules; exact pieces are quasi-isos
├── Operator/{Adjoint,Multiplication,Resolvent}.lean                         -- Feec.Operator
├── Semigroup/{Basic,Stone,Perturbation,LumerPhillips,Invariance,Spectral}.lean  -- Feec.C0Group / Feec.C0Semigroup
├── Evolution/{Solution,Energy,Forcing,Duhamel,WellPosed,Tangent,Constrained}.lean -- Feec.Evolution
├── Variational/{InfSup,BabuskaNecas,Galerkin,SaddlePoint,Fortin,GalerkinEvolution}.lean -- Feec.Variational
├── TimeStepping/{Cayley,BlockMatrix,Theta,Convergence,Trajectory,Leapfrog}.lean -- Feec.TimeStepping
├── HilbertComplex/                                                          -- Feec.HilbertComplex
│   ├── Basic.lean  Short.lean  Window.lean  Dual.lean  DomainComplex.lean
│   ├── Hodge.lean (cohomology, harmonic, Hodge, Poincaré)  Compactness.lean
│   ├── Homology.lean (cohomology = Mathlib homology of the complex of domains)
│   ├── Dirac.lean (dirac = d+d†, wave = d−d†)  HodgeLaplacian.lean  Mixed.lean  HodgeWave.lean
│   ├── Reducing.lean  Transport.lean  Equivariant.lean  Reality.lean
│   ├── Total.lean (the total complex ⊕ Wⁱ →𝐝 ⊕ Wⁱ on one point; the Green operator of Δ)
│   ├── Approximation/{Subcomplex,CochainProjection,DiscreteHodge,DiscreteCohomology,MixedError,SemidiscreteWave}.lean
│   │   Approximation/ConformingFamily.lean -- AFW §3.3 data: subcomplexes, bounded cochain projections, windows, Jackson estimates
│   │   Approximation/StaticFEEC.lean -- the static FEEC theorem staticFEEC (StaticVerdict: AFW Thm 3.4–3.9), rates, uniform projections
│   │   Approximation/{DissipFEEC,SkewFEEC,ApproxFEEC}.lean -- the tower dissipFEEC → skewFEEC → approxFEEC
│   │   Approximation/FullyDiscrete.lean -- the tower × one-step schemes (fully discrete verdict)
│   │   Approximation/{Ritz,RitzResolvent}.lean -- Ritz projections → cores, rate classes (regularity scales)
│   │   Approximation/HeatFEEC.lean -- the Hodge heat equation: toHeat, the heat Ritz projection, heatFEEC, rate_heat
│   │   Approximation/Crown.lean -- the FEEC theorem feec (Verdict: static, wave, heat, fully discrete on every window) and feec_rated
│   │   Approximation/Spectral.lean -- reducing families (ReducingFamily.feec: exact on the bands, error = truncation error), spectral families (ofSpectral)
│   │   Approximation/{ConstrainedFEEC,ApproxConforming,ApproxOrthogonal,ApproxFEECWitness,DissipGalerkin}.lean
│   │   Approximation/{ApproxComplex,ApproxComplexWitness,ApproxComplexCrime,ApproxComplexCrimeWitness}.lean
│   │                                 -- constrainedFEEC; approxFEEC (variational crimes), its conforming case,
│   │                                 -- ofComplex, ofComplexCrime (cochain defect), complex-level rates
│   └── BGG/{Basic,Derived,DomainData,ToComplex,WeakSymmetry,Discrete}.lean -- Derived: BGG complex, any length
│       BGG/Analytic.lean -- bounded BGG data: the derived complex as a Hilbert complex; closed range, dim H ≤ rows
│       BGG/Conforming.lean -- stacked conforming families: conforming families of the derived complex, the crown
├── Fourier/{SymbolComplex,FibreReducing,ClosedRange,Torus,Euclidean,Weak,Reality,SpectralGalerkin}.lean
├── Domain/{L2Field,Mollify,ConstCoeffOp,Complexes,Obstruction,FiniteSpeed}.lean   -- open Ω ⊆ ℝⁿ, no traces
│   Domain/{BGG,HessianBGG,ElasticityBGG,DivDivBGG}.lean -- BGG data of constant-coefficient operators;
│                                 -- the Hessian, elasticity, div-div complexes as bgg 0, 1, 2 of stacked de Rham
│   Domain/BGGRealization.lean -- their L² (maximal) realizations as HilbertData; the analytic BGG verdicts on Ω
│                                 -- (only the regular decompositions after J assumed)
│   Domain/BGGFEEC.lean -- the FEEC theorem for discrete Hessian, elasticity, div-div complexes
├── Algebra/{LeviCivita,Metric,ExteriorFibre,MatrixSymbol,TransverseTraceless,Koszul,PolynomialForm,Proxy3,CubicalForm}.lean
├── Geometry/{AlgebraicCurvature,Bivector,Hodge2,WeylDecomposition}.lean
├── Mesh/{Basic,Kuhn,Freudenthal,ShapeRegular}.lean   -- simplicial meshes; imports only Mathlib (added in W8)
├── FiniteElement/{Dof,SmoothForm,SimplexIntegral,Stokes,MeshDivergence,LocalSpace,LocalDof,Whitney,
│                  Assembly,Conformity,WhitneyComplex,BrambleHilbert,InterpolationError,SmoothedProjection,
│                  WhitneyInterpolation,InverseEstimate,CubeDof,CubeMesh,CubeConformity,CubeInterpolation}.lean
├── Models/                           -- INSTANCES ONLY; nothing generic may import Models
│   ├── Torus/{DeRham,GradCurl,SymCurl,BGG}.lean     Euclidean/{DeRham,GradCurl,SymCurl,BGG}.lean
│   ├── Cube/{Parity,Mirror,MirrorSym,MirrorBGG,Static}.lean        -- equivariant compressions of the torus
│   ├── BoundedDomain/{GradCurl,SymCurl,Hessian,BGG,Interior}.lean  -- minimal/maximal realizations
│   └── ConformingFamilies.lean   -- Whitney and every PolySeq family (cube, parallelepiped, star-shaped) as conforming families; their discrete cohomology
├── Physics/{Maxwell,LinearizedGravity,EinsteinBianchi}/*.lean -- headline physical statements, no analysis (elasticity: Domain/Elasticity)
├── Counterexamples/{Ell2,Fredholm,NonClosedRangeEuclidean,BoundedDomainTSD,BoundedSymTSD,
│                   BallSymTSD,CubeStationary,ConstrainedEvolution,ClassicalRegularity}.lean
├── Examples/NonVacuity.lean          -- bddOp, rotGen, idComplex witnesses
├── Numerics/CrankNicolsonTable.lean  -- plane-wave check and the step-count table (descriptive names)
└── Instances/{Maxwell,EuclideanBand,EinsteinBianchi*,FullyDiscrete,Corollaries}.lean  -- Feec.Instances: models as instances of approxFEEC;
                                      -- top layer, imported only by Feec.lean, adds no names to lower namespaces
docs/THESIS_MAP.md  docs/migration/{old_theorems.tsv,map.tsv}  scripts/FeecCheck/*.lean (the gate, `lake exe feec-gate`)
```

**Import rules.** The layers form a partial order (a DAG), not a chain: a layer imports only
itself and the layers below it along the edges below (the reflexive-transitive closure), and
layers that no path joins are independent and may not import each other.
`lake exe feec-layering` enforces this; the edges are the table `FeecCheck.Layering.layerDeps`, which must
match this list.

| layer | imports directly (and, through them, everything they import) |
|---|---|
| `ForMathlib`, `Mesh` | only Mathlib |
| `Algebra` | `ForMathlib` |
| `Geometry` | `Algebra` |
| `Operator` | `ForMathlib` |
| `Semigroup` | `Operator` |
| `Evolution` | `Semigroup` |
| `Variational` | `Evolution` (the Galerkin error bound for evolution problems uses the energy method) |
| `TimeStepping` | `Semigroup` (one-step schemes approximate semigroups) |
| `HilbertComplex` | `Variational`, `TimeStepping` (the fully discrete FEEC theorem) |
| `Fourier`, `Domain` | `HilbertComplex`, `Algebra` |
| `FiniteElement` | `Domain`, `Mesh` |
| `Models` | `FiniteElement`, `Fourier`, `Geometry`, `TimeStepping` |
| `Physics`, `Counterexamples` | `Models`, and each other (siblings; Lean keeps the modules acyclic) |
| `Examples`, `Numerics` | `Physics`, `Counterexamples` |
| `Instances` | `Examples`, `Numerics` (so every layer); imported only by `Feec.lean` |

So `Fourier` and `Domain` are independent of each other and both sit above `Algebra`, which with
`Geometry` sits beside the analytic chain `Operator` → `Semigroup` → `Evolution` → `Variational` →
`HilbertComplex`; `TimeStepping` sits beside `Evolution` and `Variational` (no path joins them),
below `HilbertComplex`; `Examples`
and `Numerics` are independent. Hard rules, which `feec-layering` also checks on the table itself:
the graph has no cycle (sibling groups contracted); `ForMathlib` and `Mesh` import no other part
of `Feec`; nothing below the top tier (`Models`, `Physics`, `Counterexamples`, `Examples`,
`Numerics`, `Instances`) imports a layer of it; only `Feec.lean` imports `Instances`, and it
imports every module.

This fixed the inversion of the pre-refactor tree, where `Ch4/StoneApplications` imported the
torus group (`Ch4/TorusGroup`) and the bounded-domain models (`Ch4/BoundedDomain`).

**Naming:**
- Mathlib style: `IsX` for predicates, lower camel case for defs, and theorem names that describe the conclusion (`isSkewAdjoint_wave`, `IsStrongSolution.mem_of_isReducing`).
- Namespaces name objects, never chapters.
- **Banned everywhere:**
  - thesis numbers: `prop_4_17`, `ForcingThm43`, `eq61` (two-digit equation numbers), `Sol61`, `Hyp54`, `C55`, `Sys56`;
  - process suffixes: `_unconditional`, `_of_isSkewAdjoint`, `_thm43`, `_ambient`, `_literal`, `_corrected`, `_res`, `_compr`, `_max`;
  - thesis typography: `bigAL`, `tst`, `nV2`, `opMh`, `Bthesis`, `Complex3`.
- Counterexamples use `not_`/`_false` names in `Feec.Counterexamples`. Global names such as `E0`, `x0` and `betaField` move into that namespace.
- Fixed letters: `𝕜 E F W H A G K Ω n ξ`. `Fin 3` appears only for curl, cross product, `vskw` and `mskw`.
- During migration, a renamed declaration gets `@[deprecated (since := "2026-10-xx")] alias`; aliases are deleted in wave 6.

## 2. Core abstractions (checked ones are copied from the scratch files)

```lean
-- ForMathlib/LinearPMap/Skew.lean   [checked, Core.lean]
variable {𝕜 E F} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] …
def LinearPMap.IsSkewSymmetric (A : E →ₗ.[𝕜] E) : Prop := ∀ x y : A.domain, ⟪A x, (y:E)⟫ = -⟪(x:E), A y⟫
def LinearPMap.IsSkewAdjoint (A : E →ₗ.[𝕜] E) : Prop := A† = -A
def LinearPMap.IsDissipative (A : E →ₗ.[𝕜] E) : Prop := ∀ x : A.domain, RCLike.re ⟪A x, (x:E)⟫ ≤ 0
structure LinearPMap.IsMDissipative (A : E →ₗ.[𝕜] E) : Prop where
  dissipative : A.IsDissipative
  surj : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y

-- ForMathlib/LinearPMap/Reducing.lean   [checked]
structure LinearPMap.IsReducingPair (T : E →ₗ.[𝕜] F) (K : Submodule 𝕜 E) (L : Submodule 𝕜 F)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] : Prop where
  proj_mem : ∀ x : T.domain, K.starProjection (x : E) ∈ T.domain
  comm : ∀ x : T.domain, T ⟨_, proj_mem x⟩ = L.starProjection (T x)
abbrev LinearPMap.IsReducing (A : E →ₗ.[𝕜] E) K [K.HasOrthogonalProjection] := A.IsReducingPair K K
-- design-only: IsReducingPair.adjoint (hd : Dense) : T†.IsReducingPair L K ; .orthogonal ;
--   restrict ; adjoint_restrict ; IsSkewSymmetric.isReducing_iff (= the old (h1,h3) pair)

-- GraphSpace / Intertwines   [checked]
def LinearPMap.graphL2 (T : E →ₗ.[𝕜] F) : Submodule 𝕜 (WithLp 2 (E × F)) :=
  T.graph.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
abbrev LinearPMap.GraphSpace (T : E →ₗ.[𝕜] F) := ↥(T.graphL2)
structure LinearPMap.Intertwines (J : E →L[𝕜] F) (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) : Prop where
  mapsTo : ∀ x : A.domain, J x ∈ B.domain
  comm : ∀ x : A.domain, B ⟨J x, mapsTo x⟩ = J (A x)
-- design-only: closedRange_tfae (hc : T.IsClosed) (hd : Dense) :
--   [IsClosed range T, IsClosed range T†, Poincaré on (ker T)ᗮ, range T† = (ker T)ᗮ].TFAE

-- Semigroup/Basic.lean   [checked; needs [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]]
structure Feec.C0Group (𝕜 E) where
  S : ℝ → E →L[𝕜] E; map_zero : S 0 = 1; map_add : ∀ s t, S (s+t) = S s * S t
  strongCont : ∀ x, Continuous fun t => S t x
structure Feec.C0Semigroup (𝕜 E) where
  S : ℝ → E →L[𝕜] E; map_zero : S 0 = 1; map_add : ∀ s t, 0 ≤ s → 0 ≤ t → S (s+t) = S s * S t
  strongCont : ∀ x, ContinuousOn (fun t => S t x) (Ici 0)
def C0Semigroup.generatorDomain (G) : Submodule 𝕜 E   -- {x | ∃ y, HasDerivWithinAt (G.S · x) y (Ici 0) 0}
def C0Group.invariantCore (G : C0Group 𝕜 E) (K : Submodule 𝕜 E) : Submodule 𝕜 E := ⨅ t, K.comap (G.S t).toLinearMap
-- design-only:
theorem LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup :
  A.IsSkewAdjoint ↔ ∃! G : C0Group 𝕜 E, G.IsIsometric ∧ G.generator = A            -- Stone
noncomputable def LinearPMap.IsSkewAdjoint.group (hA : A.IsSkewAdjoint) : C0Group 𝕜 E
theorem C0Semigroup.perturb (G) (B : E →L[𝕜] E) : ∃! G', G'.generator = G.generator + B.toPMap
theorem LinearPMap.IsMDissipative.existsUnique_contraction  -- as built: unique on `Ici 0`, since
  -- `C0Semigroup.S` is unconstrained for t < 0 (the literal `∃!` is false)
  : ∃ G : C0Semigroup 𝕜 E, G.IsContraction ∧ G.generator = A ∧ ∀ G', … → EqOn G'.S G.S (Ici 0)
theorem C0Group.isReducing_iff_invariant (hG : G.IsIsometric) : G.generator.IsReducing K ↔ ∀ t, K.map (G.S t) ≤ K
theorem eigenDense_of_compactResolvent (hA : A.IsSkewAdjoint) (hK : IsCompactOperator (resolvent A 1)) : EigenDense hA.group

-- Evolution/Solution.lean   [checked]  — stated through the graph, on any time set I
structure Evolution.IsStrongSolution (A : E →ₗ.[𝕜] E) (I : Set ℝ) (F U : ℝ → E) : Prop where
  continuousOn : ContinuousOn U I
  deriv : ∀ t ∈ I, ∃ v, (U t, v) ∈ A.graph ∧ HasDerivWithinAt U (v + F t) I t
structure Evolution.IsClassicalSolution (A) (I) (F U) : Prop extends IsStrongSolution A I F U where
  deriv_cont : ∃ V : ℝ → E, ContinuousOn V I ∧ ∀ t ∈ I, (U t, V t) ∈ A.graph
-- headline statements (shapes checked as Props in Core.lean):
theorem IsStrongSolution.unique (hA : A.IsDissipative) (hU hV : …) (h0 : U a = V a) : EqOn U V (Icc a b)
theorem IsStrongSolution.mem_of_isReducing (hA : A.IsDissipative) (hK : A.IsReducing K)
  (hU : IsStrongSolution A (Icc a b) F U) (h0 : U a ∈ K) (hF : ∀ t ∈ Icc a b, F t ∈ K) : ∀ t ∈ Icc a b, U t ∈ K
theorem C0Semigroup.existsUnique_classicalSolution (G) (hU₀ : U₀ ∈ G.generatorDomain)
  (hF : ForcingClass.admissible G.generator (Icc a b) F) : ∃! U, U a = U₀ ∧ IsClassicalSolution G.generator (Icc a b) F U

-- HilbertComplex/Basic.lean   [checked]
structure Feec.HilbertComplex {ι} (c : ComplexShape ι) (W : ι → Type u)
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] where
  d : ∀ i j, W i →ₗ.[𝕜] W j
  shape : ∀ i j, ¬ c.Rel i j → d i j = 0
  dense : ∀ i j, Dense ((d i j).domain : Set (W i))
  closed : ∀ i j, (d i j).IsClosed
  mapsTo : ∀ i j k (x : (d i j).domain), (d i j x : W j) ∈ (d j k).domain
  d_comp_d : ∀ i j k (x : (d i j).domain), d j k ⟨_, mapsTo i j k x⟩ = 0
def dual (H) : HilbertComplex c.symm W where d i j := (H.d j i)†   -- [typechecks; proofs migrate from Ch4/Adjoint]
def cycles i := (H.d i (c.next i)).ker ; def boundaries i := range (H.d (c.prev i) i)
def harmonic i := H.cycles i ⊓ ((H.d (c.prev i) i)†).ker ; def ClosedRangeAt i := IsClosed (boundaries i)
structure ReducingSubcomplex (S : ∀ i, Submodule 𝕜 (W i)) [∀ i, (S i).HasOrthogonalProjection] : Prop where
  reduces : ∀ i j, (H.d i j).IsReducingPair (S i) (S j)
structure ScaledEmbedding (H' : HilbertComplex c W') where
  J : ∀ i, W i →L[𝕜] W' i; scale : ι → ℝ; scale_pos : ∀ i, 0 < scale i
  inner_J : ∀ i x y, ⟪J i x, J i y⟫ = (scale i : 𝕜) * ⟪x, y⟫
  dScale : ι → ι → 𝕜                                  -- chain-rule factors (old scaleComplex2's (2s)⁻¹, (2s)⁻²)
  intertwines : ∀ i j (x : (H.d i j).domain), ∃ h, H'.d i j ⟨J i x, h⟩ = dScale i j • J j (H.d i j x)
def ComplexShape.fin3 : ComplexShape (Fin 3) where Rel i j := i.val + 1 = j.val …
structure ShortHilbertComplex (W₀ W₁ W₂) where d₀ d₁ dense₀ dense₁ closed₀ closed₁ mapsTo comp
abbrev Tot3 := PiLp 2 (fun i : Fin 3 => W3 W₀ W₁ W₂ i)       -- window total space [instances checked]
-- design-only: wave/dirac on window totals; isSkewAdjoint_wave; isSelfAdjoint_dirac;
--   ReducingSubcomplex.isReducing_wave; hodge; closedRangeAt_iff_poincare; HasCompactProperty.*;
--   hodgeLaplacian (via (1−D)(1+D) = 1−D², D = wave, Stone resolvents); Mixed.wellPosed

-- HilbertComplex/Approximation/{DissipFEEC,SkewFEEC,ApproxFEEC}.lean   [checked]
-- the generator is the one parameter; its m-dissipativity / skew-adjointness are Prop fields, so
-- a projection `F.X h` carries `A` once (not `A` and a proof term repeating `A` and `E`'s instances)
structure DissipFEEC (A : E →ₗ.[𝕜] E) (κ : Type*) where
  isMDissipative : A.IsMDissipative
  K : Submodule 𝕜 E; isClosed_K; l : Filter κ; X : κ → Type u; [instances]
  L : ∀ h, X h →L[𝕜] X h; dissipative : ∀ h x, re ⟪L h x, x⟫ ≤ 0
  incl : ∀ h, X h →L[𝕜] E; proj : ∀ h, E →L[𝕜] X h; proj_incl; bound
structure SkewFEEC (A : E →ₗ.[𝕜] E) (κ) extends DissipFEEC A κ where   -- [CompleteSpace E]
  isSkewAdjoint : A.IsSkewAdjoint; skew : ∀ h x y, ⟪L h x, y⟫ = -⟪x, L h y⟫
  isMDissipative := isSkewAdjoint.isMDissipative; dissipative h x := …   -- derived
abbrev ApproxFEEC (H : HilbertComplex 𝕜 c W) (κ) := SkewFEEC H.wave κ
-- verdicts: structure DissipFEEC.Verdict (Z : F.Core) : Prop; SkewFEEC.Verdict extends it;
--   ApproxFEEC.Verdict extends that; theorems dissipFEEC, skewFEEC, approxFEEC

-- Fourier/SymbolComplex.lean   [checked]
structure SymbolComplex (μ : Measure α) (c : ComplexShape ι) (E : ι → Type*) [… FiniteDimensional, CompleteSpace] where
  m : ∀ i j, α → E i →L[𝕜] E j; shape : ∀ i j, ¬ c.Rel i j → m i j = 0
  comp : ∀ i j k a, (m j k a).comp (m i j a) = 0; meas : ∀ i j, AEStronglyMeasurable (m i j) μ
structure FibreReducing (S : SymbolComplex μ c E) (K : ∀ i, α → Submodule 𝕜 (E i)) : Prop where
  map : ∀ i j a, (K i a).map (S.m i j a) ≤ K j a
  map_adj : ∀ i j a, (K j a).map (S.m i j a)† ≤ K i a
  meas : ∀ i, AEStronglyMeasurable (fun a => (K i a).starProjection) μ
-- design-only: toHilbertComplex, adjoint_d (= adjoint symbols), FibreReducing.toReducingSubcomplex,
--   closedRange_of_gap, not_closedRange_of_homogeneous, expGroup (explicit Stone group)

-- Variational/InfSup.lean   [checked]
structure InfSup (B : X →L[𝕜] Y →L⋆[𝕜] 𝕜) (γ : ℝ) : Prop where pos : 0 < γ; le : ∀ x, γ * ‖x‖ ≤ ‖B x‖
-- design-only: InfSup.of_testMap (T) (hT : c‖x‖² ≤ re B x (T x)) (hK : T K ⊆ K) : InfSup (B.restrict K K) (c/‖T‖);
--   babuskaNecas_iff ; norm_sub_galerkinProj_le (‖B‖/γ) ; brezzi_iff ; discreteBrezzi_of_fortin ;
--   GalerkinEvolution (accretive a) .unique/.stability/.error_bound ; TimeStepping.cayley_isContraction

-- Domain/ConstCoeffOp.lean   [design-only]
structure ConstCoeffOp (n) (V W) where coeff : (Fin n →₀ ℕ) →₀ (V →L[ℝ] W)
def minimal (A) (Ω : Opens (EuclideanSpace ℝ (Fin n))) ; def maximal (A) Ω
theorem adjoint_minimal : (A.minimal Ω)† = A.formalAdj.maximal Ω ; theorem adjoint_maximal
def minimalComplex / maximalComplex ; theorem dual_minimalComplex
```

**Argued on paper, not checked in Lean:**
- that `FibreReducing` implies all four old projection hypotheses;
- the converse "wave reduces ⇒ `ReducingSubcomplex`", which needs a core argument on `D(d) ∩ D(d†)`;
- that compactness transfers along the cube compression;
- a linearized second-Bianchi identity on 3-jets for every gauge;
- the sign identity `L = J ∘ wave ∘ J` with `J = diag(1,1,−1)`.

## 3. Generalized theorems and what each one subsumes

| New theorem | Subsumes |
|---|---|
| `LinearPMap.IsSkewAdjoint.dense_domain` (once) | the two duplicates in `Ch4/Adjoint` and `Ch4/Stone`; every `hD : Dense` argument next to skew-adjointness |
| `LinearPMap.closedRange_tfae` | `orth_range_eq_ker_adjoint`, `orthogonal_range_adjoint`, `orthogonal_ker(_adjoint)`, `poincare_of_isClosed_range`, `isClosed_range_of_poincare`, `isClosed_range_iff_poincare`, `range_adjoint_eq_orthogonal_ker`, `isClosed_range_adjoint_iff`, `range_eq_orthogonal_ker_adjoint` (thesis (4.1a–d)) |
| `IsReducingPair.adjoint`, `.adjoint_restrict`, `IsSkewAdjoint.restrict` | `commute_proj`, `skewAdjoint_restrict`, `thm_4_4`, `restrictTo`, `dense_restrictTo_domain`, `map_orthogonal_mem`, the `(h1,h3)` pair in about 15 signatures |
| Stone `isSkewAdjoint_iff_existsUnique_isometricGroup` with `.group` | `stoneGroup`, `stoneS`, `UnitaryGroupGenerator` (with `.transport`), `waveGroup`, `mulGroup`/`mulExp`, `symGroup`, `periodicGroup` |
| `C0Semigroup.existsUnique_classicalSolution`, plus its skew-adjoint and dissipative corollaries | `thm_4_3_full`, `thm_4_3_of_isSkewAdjoint`, `thm_4_3_unconditional`, `thm_4_3_hodgeWave(_thm43)`, `thm_4_3_torus`, `wellPosedClassical_thm43Full`, `IsSkewAdjoint.wellPosed*`, `exists_classical_solution_bddOp`, `WellPosed{Existence,Hom,Classical}` (deleted as hypotheses) |
| `IsStrongSolution.unique` (dissipative) | `strongSolution_unique`, `energy_zero`, `energy_zero_of_exists`, `weak_unique`, `isWeakSol_unique`, `discrete_solution_unique` |
| `IsStrongSolution.mem_of_isReducing` | `constraint_propagation`, `Constraints.propagate`, `cor_4_5`, `cor_4_5_ambient`, `cor_4_5_classical`, all 4 `cor_4_5_*_unconditional`, `constraint_ker(_exists)` |
| `ForcingClass.{contDomain,w11,l1Domain,admissible}` with inclusion lemmas | `ForcingDL`, `ForcingW11`, `ForcingThm43`, `ForcingThm43Full`, `IsW11`, `IsL1D`, `forcingThm43Full_of_*` |
| `Evolution.mild` with `integral_mem_domain` (once) | `duhamel`, `duhamelSol`, `duhamel_of_domain`, `duhamel_W11`, `duhamel_L1`, the four `integral_mem_domain*` |
| `deriv_mem_of_eventually_mem_closed` (Tangent) | five tangent-cone restatements (`*_necessary` helpers) |
| `C0Group.invariantCore` with `_isReducing`, `_maximal`, `isReducing_iff_invariant` | `Kmax`, `mem_Kmax`, `le_Kmax`, `isClosed_Kmax`, `mem_Kmax_iff_propagate`, `revT_mem_Kmax`, `Kmax_compr_eq` |
| `Semigroup.Spectral.mem_of_forward_invariant` and `eigenDense_of_compactResolvent` | `BoundedKstar` mean-ergodic results (generalized); the Cesàro argument in `BoxForward` (deleted); the `EigenDense` assumption (now derived) |
| `HilbertComplex.hodge`, `closedRangeAt_iff_poincare`, `dual_dual`, `cohomologyEquivHarmonic` (every index, any length) | `hodge_V*` and `poincare*` (thesis Thms 4.1–4.2), `harmonicEquivCohomology`, `closedRange_dual_iff`, `isClosedAt_iff_*` |
| `HasCompactProperty.{closedRange,finiteDimensional_harmonic,compactResolvent}` | `HasCompactEmbedding{,0,2}`, `closedRange_of_compact`, `isClosed_range_d{0,1}_of_compact*`, `closed_and_fredholm_of_*` |
| `isSkewAdjoint_wave`, `HodgeWave.existsUnique`, `HodgeWave.weak_iff_strong` | `waveOp_isSkewAdjoint`, `neg_waveOp_isSkewAdjoint`, `thm_4_6*` (4), `thm_4_7*` (2), `thm_4_6_unconditional`, `thm_4_6_strong_unconditional`, `thm_4_7*_unconditional`, `weak_imp_strong/classical` |
| `ReducingSubcomplex.propagates`, `isReducing_iff_waveGroup_invariant` | `prop_4_16(_exists, ')`, `prop_4_17`, `prop_4_17_necessary`, `prop_4_17_iff`, `prop_4_18(_i,_ii)` and all their `_unconditional` copies; the general `S₀` case is new |
| `ScaledEmbedding.reducingSubcomplex_comap` and `.invariantCore_eq` | `prop_4_17_hyps_res`, `_hyps_compr`, `_hyps_scale`, `_hyps_scale2`, `prop_4_17_res(_exists)`, `prop_4_17_compr_exists`, `totJ_group`, `totJ_waveOp`, `adjoint_compr_*` |
| `FibreReducing.toReducingSubcomplex` | per-model `projKc_mem_domL` (×6), `L2TSD_le_ker`, `curl*_mem_L2TSD`, `adjoint_curl*_mem_L2TSD` |
| `Fourier.closedRange_of_gap`, `not_closedRange_of_homogeneous` | the torus closed-range lemmas, `WholeRange` |
| `InfSup.of_testMap` | `prop_4_13(_lower,_V,_infSup,_test_norm)`, plus a new well-posedness result for the mixed Hodge Laplacian, continuous and discrete |
| `norm_sub_galerkinProj_le`, `babuskaNecas_iff`, `brezzi_iff` (RCLike) | `thm_4_10`, `quasi_opt*`, `babuska_necas_iff(_dual)`, `lax_milgram*`, `thm_4_11`, `brezzi*`, `InfSupCond`, `DenseRangeCond` (→ `SeparatingRight`) |
| `Energy.norm_le_of_re_inner_deriv_le` (decay rate λ) | `lemma_4_12`, `lemma_4_12_integral`, `lemma_4_12_sharp`, `energy_estimate_integral` |
| `GalerkinEvolution.error_bound` (accretive, optional multiplier) | `thm_4_14`, `thm_4_14_pointwise`, `ch6_convergence`, `ch6_convergence_rate`, `ch6_convergence_Sol63`, `ch6_convergence_projected` |
| `TimeStepping.cayley_*` | `FullStep`, `RedStep`, `cnStep`, `fullLHS` |
| `BGG.toHilbertComplex`, `BGG.closedRange`, `WeakSymmetry.wellPosed` | `prop_5_1` (an 8-tuple), `prop_5_2(_wellPosed)`, `BGGData`, `BGGHilb`, `ContData` |
| `BGG.Discrete` (pair of cochain projections, compatibility `ΠS = S_h Π'`) | `prop_5_3_a/b`, `prop_5_4`, `prop_5_6`, `thm_5_5`, `Disc`, `Hyp54`, `Sys56` |
| `Domain.adjoint_minimal`, `adjoint_maximal` | the 7 hand-built graph closures and their `closure_*_identity` / `mem_adjoint_*_iff` lemmas |
| `Domain.FiniteSpeed` (symmetric hyperbolic systems) | `prop_3_6` and `thesisComplex_TSD_depDomain` (BoundedInterior), which become instances; Maxwell, acoustics and elastodynamics come for free |
| `Algebra.tt n ξ` and `MatrixSymbol` identities over any `CommRing` | about 12 TSD definitions, 4 curls, 3 `vskw`, 2 Hessian symbols, and the 4 copies of thesis Lemma 3.5 |

## 4. Migration map (all 77 files)

| Current file | Destination(s) |
|---|---|
| Foundation.lean | deleted (umbrella import) |
| Foundation/Operators | ForMathlib/LinearPMap/{Skew,Reducing}; Operator/Adjoint |
| Foundation/Complex | HilbertComplex/{Basic,Short,Window,Dirac,DomainComplex} |
| Foundation/Evolution | Evolution/{Solution,Energy} |
| Foundation/BGG | HilbertComplex/BGG/Basic |
| Foundation/Tensor | Algebra/{LeviCivita,MatrixSymbol}; Geometry/AlgebraicCurvature |
| Ch2/Curvature | Geometry/{AlgebraicCurvature,WeylDecomposition} |
| Ch2/Linearized | Physics/LinearizedGravity/{Einstein,Gauge,PlaneWave} (any metric; only `trRev_trRev` needs n = 4) |
| Ch3/Bivector | Geometry/{Bivector,Hodge2} |
| Ch3/EB | Physics/EinsteinBianchi/System; jets → Algebra/MatrixSymbol; `prop_3_6` → Domain/FiniteSpeed instance |
| Ch4/Adjoint | ForMathlib/LinearPMap/{ClosedRange,GraphSpace}; HilbertComplex/Dual; `finSupp` → Counterexamples/Ell2 |
| Ch4/Hodge | HilbertComplex/{Hodge,Compactness}; ℓ² examples (`A`, `D`, `Dfin`) → Counterexamples/{Ell2,Fredholm} |
| Ch4/HodgeW | HilbertComplex/{Hodge,Compactness}; `ofBounded` → Basic; `cxW`, `cxK*` → Counterexamples/Fredholm |
| Ch4/HodgeWave | HilbertComplex/{Dirac,HodgeWave}; `idComplex` → Examples/NonVacuity |
| Ch4/Restriction | Evolution/{Solution,Invariance}; ForMathlib/LinearPMap/Reducing |
| Ch4/Existence | Semigroup/Basic (`ofBounded`); Examples/NonVacuity (`bddOp`, `rotGen`) |
| Ch4/Stone | Semigroup/Stone; Operator/Resolvent |
| Ch4/Duhamel, StoneDuhamel, StoneForcing | Evolution/{Forcing,Duhamel,WellPosed} |
| Ch4/StoneApplications, Unconditional | deleted; each statement becomes an instance of the headline theorems (§3) |
| Ch4/Galerkin | Variational/{InfSup,BabuskaNecas,Galerkin,SaddlePoint}; `shift` → Counterexamples/Ell2 |
| Ch4/ErrorEstimate | Variational/GalerkinEvolution; Evolution/Energy; HilbertComplex/Approximation/SemidiscreteWave |
| Ch4/ErrorEstimateDL | GalerkinEvolution (domain-data corollary); `trunc` → Fourier/SpectralGalerkin; C¹ failure → Counterexamples/ClassicalRegularity |
| Ch4/Constraints | Koszul/Nédélec → Algebra/{Koszul,PolynomialForm}; Lemma 3.5 → Algebra/MatrixSymbol; propagation → HilbertComplex/Reducing; weak forms → HilbertComplex/HodgeWave |
| Ch4/Torus, TorusGroup | Fourier/{SymbolComplex,Torus}, Operator/Multiplication; Models/Torus/GradCurl |
| Ch4/TorusSym | Models/Torus/SymCurl; Algebra/{TransverseTraceless,MatrixSymbol} |
| Ch4/TorusWeak | Fourier/Weak |
| Ch4/WholeMul | Operator/Multiplication; Fourier/{SymbolComplex,Euclidean} |
| Ch4/Whole, WholeIdent, WholeWeak | Models/Euclidean/GradCurl; Fourier/Weak |
| Ch4/WholeSym | Models/Euclidean/SymCurl |
| Ch4/WholeReal | Fourier/Reality; HilbertComplex/Reality |
| Ch4/WholeRange | Fourier/ClosedRange; Counterexamples/NonClosedRangeEuclidean |
| Ch4/BoundedDomain, BoundedDomainExt | Domain/{L2Field,ConstCoeffOp,Complexes}; Models/BoundedDomain/GradCurl; Counterexamples/BoundedDomainTSD |
| Ch4/BoundedDensity | Domain/Mollify; Counterexamples/BoundedDomainTSD (the density gap) |
| Ch4/BoundedInterior | Domain/FiniteSpeed; Models/BoundedDomain/Interior |
| Ch4/BoundedKstar | Semigroup/Spectral; model part → Models/BoundedDomain/GradCurl |
| Ch4/BoundedSalvage, BoundedSalvageDim | Domain/Obstruction |
| Ch4/BoundedSalvageMax | Semigroup/Invariance (`invariantCore`); Models/BoundedDomain/GradCurl |
| Ch4/BoundedSym, BoundedSymExt | Models/BoundedDomain/SymCurl; Counterexamples/BoundedSymTSD |
| Ch4/BoundedSymDual | Counterexamples/BallSymTSD |
| Ch4/Box, BoxRestrict, BoxReduce | HilbertComplex/{Equivariant,Transport}; Models/Cube/Parity |
| Ch4/BoxStatic, BoxThesis, BoxForward | Models/Cube/Static; Counterexamples/CubeStationary (`BoxForward`'s Cesàro proof is deleted) |
| Ch4/BoxIdent | Models/Cube/Parity (identification with the bounded-domain complex) |
| Ch4/BoxMirror | Models/Cube/{Mirror,MirrorSym} |
| Ch5/BGG | HilbertComplex/BGG/{ToComplex,WeakSymmetry}; Physics/Elasticity/WeakSymmetry |
| Ch5/Discrete | HilbertComplex/BGG/Discrete; FiniteElement/Dof (`dof_commute*`); inequalities → ForMathlib/Analysis/Inequalities |
| Ch6/TimeDependent | Evolution/Constrained; Variational/GalerkinEvolution; `prop_6_2_false` → Counterexamples/ConstrainedEvolution |
| Ch6/Whole, Ch6/Bounded | Models/{Euclidean,BoundedDomain}/BGG; Physics/Elasticity |
| Ch7/CrankNicolson | TimeStepping/{Cayley,BlockMatrix}; Numerics/CrankNicolsonTable |
| Repair/C2 | Physics/LinearizedGravity/Gauge |
| Repair/C410 | Algebra/PolynomialForm (any n) |
| Repair/C417Compress | HilbertComplex/Transport (`ScaledEmbedding`) |
| Repair/C417Ext, C417Cube, C417CubeDense, C417Pi | Models/Cube/Mirror |
| Repair/C419Cube, C419Pi | Models/Cube/MirrorSym; `Compr.restrict` → Transport |
| Repair/C417BggTorus, C417BggCube | Models/{Torus/BGG,Cube/MirrorBGG}; `Compr.prod` → Transport |
| Repair/C417 | deleted; its bundles become rows of `docs/THESIS_MAP.md` |
| Repair/C67, C67Prop62, C67Minres | Evolution/Constrained; Counterexamples/ConstrainedEvolution; TimeStepping/BlockMatrix |

**Key declarations, old → new:**
- `Feec.IsSkewAdjoint` → `LinearPMap.IsSkewAdjoint`; `IsSkewSymm` → `LinearPMap.IsSkewSymmetric`; `restrictTo` → `LinearPMap.restrict`; `graphL2` → `LinearPMap.graphL2`/`GraphSpace`.
- `HilbertComplex2` → `ShortHilbertComplex`; `UHilbertComplex` → `HilbertComplex (ComplexShape.up ℤ)`; the bounded `HilbertComplex V W` and `Complex3` → `HilbertComplex.domainComplex`; `ClosedRange` → `ClosedRangeAt`; `waveOp`/`totL`/`domL`/`midDomain` → `wave` on `Window`; `Kc`/`projKc` → `ReducingSubcomplex` with `S 0 = ⊥`.
- `UnitaryGroupGenerator` → `C0Group` + `IsIsometric`; `stoneGroup`/`waveGroup` → `IsSkewAdjoint.group`.
- `IsStrongSolution` → `Evolution.IsStrongSolution` (graph form, set `I`); `IsClassicalSolution` → `Evolution.IsClassicalSolution`; `Sol61`/`Sol62`/`Sol63` → `Evolution.IsConstrainedSolution` (with `.regular`).
- `Kmax` → `C0Group.invariantCore`; `S1max`/`S2max` → components of `invariantCore`; `Per`/`Stat`/`PurePoint`/`EigenDense` → `Semigroup.Spectral.*`.
- `Refl3`, `resComplex`, `Compr`, `comprComplex`, `totJ`, `scaleComplex`, `scaleComplex2`, `mirrorComplex` → `ScaledEmbedding` / `Equivariant.fixed`; `realRefl`/`realComplex` → `Reality`.
- `Torus.mulOp`, `Whole.mulOp`, `fibreSub` → `Fourier.mulOp μ`, `Fourier.fibreSub`.
- `InfSupCond` → `InfSup`; `DenseRangeCond` → `SeparatingRight`; `bigAL`/`tst`/`ellProjFun` → `galerkinOperator`/`testMap`/`galerkinProj`; `Disc`/`Hyp54`/`Sys56` → `BGG.Discrete`; `FullStep`/`RedStep` → `TimeStepping.cayley`.
- Model results (`prop_4_17_torus*`, `prop_4_17_whole*`, `prop_4_19_torus*`, `prop_4_19_whole*`, `prop_4_17_bggWhole`, `mirror*_prop_4_1x_exists`, `piCube_*`, `thesisComplex_prop_4_17_max`) become corollaries named per model, e.g. `Models.Torus.GradCurl.tsd_propagates` or `Models.Cube.Mirror.tsd_propagates`. Each is one application of `ReducingSubcomplex.propagates`.
- Refutations get descriptive names, for example:
  - `thesisComplex_not_projection_hyp` → `Counterexamples.BoundedDomainTSD.not_reducing_tsd`
  - `symComplexD_ball_not_propagate_unconditional` → `Counterexamples.BallSymTSD.not_propagates`
  - `prop_6_2_false` → `Counterexamples.ConstrainedEvolution.not_wellPosed_regularData`

## 5. Execution waves

Each task owns the files listed and nothing else. Tasks inside a wave are independent. Every wave ends with a green build.

**Freeze first.** New `Repair/*` work stops before W1, or goes straight into W5 targets. Otherwise the cube results get rewritten twice.

- **W0 — tooling (1 agent).**
  - `scripts/Snapshot.lean` (checked prototype) imports `Feec` at HEAD and writes `docs/migration/old_theorems.tsv` (name, type).
  - `scripts/AxiomAudit.lean` (checked prototype).
  - Create `docs/migration/map.tsv` with columns `old`, `new`, `kind ∈ {rename, generalize, corollary, dedup, counterexample, deleted-helper}`.
  - Create `docs/THESIS_MAP.md`.
- **W1 — deduplicate in place, no directory moves (3 agents).**
  - (a) Operators: one `dense_domain`, one `isClosed_ker`, and `IsReducing` replacing `(h1,h3)`. Owns `Foundation/Operators`, `Ch4/{Adjoint,Restriction,Stone}`.
  - (b) Evolution: one uniqueness lemma, one propagation lemma, the `ForcingClass` predicates; delete the `_unconditional` towers by re-proving them as one-liners. Owns `Ch4/{StoneApplications,Unconditional,StoneForcing,StoneDuhamel,Duhamel,Existence}`, `Foundation/Evolution`.
  - (c) Copies of the energy proofs and inequalities. Owns `Ch4/ErrorEstimate*`, `Ch5/Discrete`, `Ch6/TimeDependent`.
- **W2 — ForMathlib and Operator, switched to RCLike (2 agents).** (a) `ForMathlib/LinearPMap/*`, `Operator/Adjoint`. (b) `ForMathlib/Lp/*`, `ForMathlib/Analysis/*`, `Operator/{Multiplication,Resolvent}`.
- **W3 — semigroups and evolution (2 agents).** (a) `Semigroup/{Basic,Stone,Invariance,Spectral}`, including `eigenDense_of_compactResolvent`. (b) `Evolution/*`. `Perturbation` (Dyson–Phillips) goes to whichever agent finishes first.
- **W4 — the Hilbert-complex core (1 agent, then 2).**
  - First prototype `Basic`, `Short`, `Window`, `Dual` and `Dirac`.
  - Then (a) `Hodge`, `Compactness`, `DomainComplex`; (b) `Reducing`, `HodgeWave`, `Transport`, `Equivariant`, `Reality`.
- **W5 — consumers, in parallel (6 agents).**
  1. Fourier and the torus/ℝⁿ models: `Fourier/*`, `Models/{Torus,Euclidean}/*`.
  2. Cube models: `Models/Cube/*` (from `Ch4/Box*` and `Repair/C41*`).
  3. Variational and approximation: `Variational/*`, `HilbertComplex/{Approximation/*,Mixed,HodgeLaplacian}`, `TimeStepping/*`.
  4. BGG: `HilbertComplex/BGG/*`, `Physics/Elasticity/*`, `FiniteElement/Dof`.
  5. Bounded domains: `Domain/*`, `Models/BoundedDomain/*`.
  6. Algebra, geometry and gravity: `Algebra/*`, `Geometry/*`, `Physics/{LinearizedGravity,EinsteinBianchi,Maxwell}/*`.
- **W6 — cleanup (2 agents).**
  - (a) Move `Counterexamples/*`, `Examples/*` and `Numerics/*`.
  - (b) Delete `Ch*/`, `Repair/`, `Foundation/` and the `@[deprecated]` aliases; finish `THESIS_MAP.md`; update `docs/OVERVIEW.md`.
- **W7 — new coverage**, in the order of §6.

**Verification gate, run after every wave:**
1. `lake build` is clean from scratch, with no `sorry` and no new warnings.
2. The axiom audit (`lake exe feec-axioms`) reports only `propext`, `Classical.choice` and `Quot.sound` for every `Feec.*` declaration.
3. **Strangler shim.** While an old module still exists, each of its main theorems is re-proved *with its old statement* as a thin theorem calling the new result. This is the semantic proof that the new theorem subsumes the old one. Shims are deleted only in W6.
4. **Coverage.** `lake exe feec-mapcheck --strict` checks that every row of `old_theorems.tsv` appears in `map.tsv`. Theorems that are thesis-numbered or named in `OVERVIEW.md` (the "main" set, roughly 400) may not be `deleted-helper`. Every `new` name and every `THESIS_MAP.md` entry must be a declaration of `Feec` (originally a generated `#check @Feec.X` file). Every thesis result cited as `[QuennevilleBelair2015], Prop 4.17` must also appear in `THESIS_MAP.md` (the `Thesis:` tags of the original plan are retired).
5. `lake exe feec-naming` finds no `prop_[0-9]`, `thm_[0-9]`, `prop59`-style, `Ch[0-9]`, `_unconditional`, `Repair` or `Thesis` identifiers (nor the other bans of §1, see `FeecCheck.Naming.rules`) in the declaration and module names of `Feec`, and `lake exe feec-layering` finds no import outside the relation of §1 (in particular none from
   `Models/` in lower layers).
6. `docs/THESIS_MAP.md` is up to date (`lake exe feec-thesismap --check`).
7. Every Lean name in backticks in `README.md` and `docs/*.md` exists (`lake exe feec-docnames`); the historical regions (dated status notes, the pre-refactor tree) may also name pre-refactor declarations, and the proposals written before the refactor (§0, §2–§4 of this plan, `docs/BLUEPRINT.md`) are not checked.

Items 2 and 4–7 and the citation check run as one command, `lake exe feec-gate` (one import of `Feec` and `FeecCheck`; nonzero exit on any failure, each violation printed as `path:line: message`).

## 6. FEEC-book coverage newly in reach, ranked by value/cost

I could not check the book's chapter numbers: `references.bib` has only the citation (CBMS-NSF 93, SIAM 2018) and I had no copy of the book. Topics follow its outline. Status codes:
- **C**: covered by migrating existing proofs;
- **R**: reachable with new work, roughly 300–1500 lines each (an estimate, not a measurement);
- **F**: far, blocked by missing Mathlib infrastructure.

| Rank | Target (book topic) | Status | Cost |
|---|---|---|---|
| 1 | Hilbert complexes at every index and length: dual, cohomology ≅ harmonic, Hodge decomposition, Poincaré ⇔ closed range, compactness property | C | falls out of W4 |
| 2 | Abstract Hodge Laplacian (self-adjoint, ≥ 0, kernel = harmonic forms, solution operator K), via `(1−D)(1+D)` and Stone resolvents | R | low |
| 3 | Mixed Hodge Laplacian well-posedness via `InfSup.of_testMap` | R | low (same trick as the existing thesis Prop 4.13 proof) |
| 4 | Compact resolvent ⇒ eigenbasis (`EigenDense` derived, not assumed) | R | low (Mathlib `Spectrum.lean:442`) |
| 5 | Approximation of complexes: subcomplex, V-bounded cochain projection, discrete Poincaré `c_P‖π_h‖`, discrete Hodge decomposition, harmonic gap, quasi-optimality of the discrete mixed problem | R | medium; non-vacuous instance via Fourier truncation on 𝕋ⁿ and the mirror cubes |
| 6 | Lax–Milgram, Babuška–Nečas, Céa, Brezzi over RCLike; Petrov–Galerkin; sharp `‖B‖/γ`; discrete Brezzi via Fortin | C/R | low |
| 7 | Maxwell with div constraints on 𝕋ⁿ, ℝⁿ and cubes (PEC = minimal complex), media through reweighting, Ohmic loss through Dyson–Phillips | R | low–medium |
| 8 | L² de Rham complexes on any open Ω, with both boundary-condition families and their duality; Hessian and div-div; elasticity complex (sym grad → inc → div) via second-order `ConstCoeffOp` | R | medium |
| 9 | De Rham on 𝕋ⁿ for k-forms: closed range, `H^k ≅ Λ^k`, Poincaré constant 1/(2π), via the Cartan identity on `ExteriorFibre` | R | medium |
| 10 | Finite propagation speed for any symmetric hyperbolic system; vacuum linearized gravity → EB for every solution, not only plane waves | R | medium (the second needs the 3-jet Bianchi identity) |
| 11 | Koszul complex, `P_rΛᵏ`, `P_r⁻Λᵏ` for any n: homotopy formula, exactness, direct sum | R | medium; dimension formulas are long |
| 12 | Hodge heat equation, impedance boundary conditions (Lumer–Phillips) | R | high (largest new theory) |
| 13 | Improved (duality) error estimates | R | medium, under an explicit regularity hypothesis |
| 14 | Abstract DOFs and unisolvence; Whitney `P₁⁻Λᵏ` on one simplex | C/R | low / stretch goal |
| 15 | Triangulations, global FE spaces, smoothed projections, Sobolev traces, Rellich/Gaffney on Lipschitz domains | F | no simplicial complexes or traces in Mathlib |

**Status after the W7/W8 gate (2026-10-18).** Ranks 1–4, 6, 9, 10 (finite speed), 11, 14:
done as planned (14 well beyond: all `P_rΛᵏ`, `P_r⁻Λᵏ` local elements, not only Whitney `P₁⁻Λᵏ`). Rank 5: done, including quasi-optimality ([AFW2010], Thm 3.9) and a
non-vacuous instance (spectral Galerkin on `𝕋ⁿ`, `C = 1`, `μ = 0`). Rank 7: done (isotropic
and anisotropic media, Ohmic loss with the magnetic Gauss law for every `σ`, `k`-form Maxwell on
open `Ω ⊆ ℝⁿ`). Rank 8: done for the complexes and their dualities on every open set; closed
range on bounded domains is not. Rank 10, second half (vacuum linearized gravity ⇒ EB for every
solution): no new work in W7/W8. Rank 12: Lumer–Phillips and the Hodge heat equation done; impedance boundary conditions not. Rank 13: the estimates are proved for the defined `η, δ, μ`; that they tend to
zero is shown for no concrete family. Rank 15 (formerly F): meshes, global Whitney spaces,
conformity, Stokes and smoothed projections are built; on the Freudenthal meshes of `(0, ½)ⁿ` the
inverse estimates and the smoothed-projection bounds (`Feec.Models.Cube.FEM.smoothingEstimates_pMax`,
`Feec.Models.Cube.FEM.smoothingEstimatesMin_pMin`) are proved, and with the identification of
`HΛ`, `H̊Λ` on the cube with the parity model and the Whitney interpolation error, the finite
element method converges with no hypothesis (`Feec.Models.Cube.FiniteElementConvergence`).
Sobolev traces and Rellich/Gaffney on Lipschitz domains remain out of reach; compactness and
eigenbases are proved on cubes instead. After the thesis-fem gate (2026-10-19) the higher-order global
families, their smoothed projections and rates, and the BGG elements of Tables 5.1/6.1 on the
cube are built as well (status note above).

**Main risks:**
- The RCLike conversion of about 60k lines of real-only proofs is the largest mechanical cost. Do it in W2, before anything is built on top.
- `ComplexShape` elaboration cost. Fallback: ℕ indexing, where `k+1+1 ≡ k+2` holds by definition.
- The unchecked paper arguments listed at the end of §2.