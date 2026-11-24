# Overview

Module map, corrections to the thesis, the proved repaired statements, and the scope of the
formalization. Declarations are named in full. `docs/THESIS_MAP.md` lists, for every result,
equation and section of the thesis, the declarations that formalize it, and
`docs/migration/map.tsv` gives the current home of every declaration of the pre-refactor tree
(the chapter-ordered modules and the real-scalar layer that remained of them; see
[The pre-refactor tree](#the-pre-refactor-tree)).
[`docs/THESIS_REFERENCES.md`](THESIS_REFERENCES.md) lists, for each entry [1]–[28] of the thesis
bibliography, where the thesis and the code cite it. Every module feeds the crown
`Feec.HilbertComplex.ConformingFamily.feec` through imports (README).

## Module map

The library is organized by mathematics. A layer imports only layers above it in this table, and
only along the import relation of `docs/REFACTOR_PLAN.md` §1, a partial order checked by
`lake exe feec-layering` (so, e.g., `Feec.Fourier` and `Feec.Domain` do not import each other).

| Layer | Content | Thesis |
|---|---|---|
| `Feec.ForMathlib` | Unbounded operators over `ℝ` or `ℂ`: skew-symmetric, skew-adjoint and dissipative operators, the graph space and `T†† = T`, reducing subspaces and restriction, the closed range theorem; `ℓᵖ` and `Lᵖ` identifications; a square-root Gronwall inequality; partial derivatives, interval integrals, Hille's theorem (closed operators commute with Bochner integrals), restriction of scalars | §4.1, (4.1a–d), Thm 4.4, Lemma 4.12 |
| `Feec.Operator` | Adjoints of composable pairs, multiplication operators on `L²(μ; E)`, resolvents | §4.1–4.2 |
| `Feec.Semigroup` | Strongly continuous groups and semigroups and the calculus of their orbits; Stone's theorem; the Lumer–Phillips theorem (m-dissipative ⇔ generator of a contraction semigroup, with uniqueness); invariant cores; invariance criteria for m-dissipative generators (resolvent invariance, the part in `K`, reducing subspaces); impedance operators of energy triples; bounded perturbations (Dyson–Phillips); pure point spectrum, and eigenbases from a compact resolvent | Thm 4.3; `K*` in Props 4.17, 4.19 |
| `Feec.Evolution` | Strong and classical solutions of `U' = AU + F` on any interval, energy estimates, forcing classes, Duhamel's formula, existence and uniqueness for generators, constraint propagation through reducing subspaces, inhomogeneous essential boundary data by a lifting (`U − G ∈ D(A)`) | Thm 4.3, Cor 4.5, Lemma 4.12, Ch. 7 |
| `Feec.Variational` | The inf-sup condition, Babuška–Nečas and Lax–Milgram, Petrov–Galerkin quasi-optimality, Brezzi's theorem, Fortin operators, the Galerkin error bound for evolution problems (all over `ℝ` and `ℂ`) | Thms 4.8–4.11, Thm 4.14 |
| `Feec.TimeStepping` | Crank–Nicolson as a Cayley transform, also with prescribed boundary DOFs; its amplification factor and phase; A-stable rational schemes and Runge–Kutta methods (Gauss–Legendre, Radau IIA, SDIRK), contractive by von Neumann's inequality, and on Banach spaces stable by Hille–Yosida (backward Euler) and Brenner–Thomée (`√n`), with the sharp smooth-data error; time schemes for families of bounded generators (`TimeStepping.TimeScheme`); signed symmetrization of the block systems for MINRES | Ch. 7 |
| `Feec.HilbertComplex` | Hilbert complexes over any `ComplexShape` (any length, every index), short complexes, windows, the dual and domain complexes; Hodge decomposition, Poincaré ⇔ closed range, the compactness property; the Dirac and wave operators, the Hodge and mixed Hodge Laplacians, the solution operator `K` with its bounds by Poincaré constants, the Hodge wave and Hodge heat equations; reducing subcomplexes and constraint propagation, with compactness, closed range and eigenbases passing to compressions; eigenbases from compactness off the kernel of the wave operator (compactness in degrees `0` and `1` of a three-term complex suffices) and Weber's lemma with a coefficient, in abstract form; scaled embeddings, reweighting by bounded isomorphisms, equivariance, reality; approximation (subcomplexes, cochain projections, conforming families, discrete Hodge decomposition, discrete cohomology, mixed error, quasi-optimal and improved error estimates of the mixed method, graph-norm approximation with a rate, semi-discrete wave equation, the constrained FEEC theorem, the approximating FEEC theorem with variational crimes and its dissipative extension (Trotter–Kato cores, conforming Galerkin schemes for impedance triples), with its front ends for discrete Hilbert complexes with cochain maps and for discrete differential spaces with a cochain defect, and rates from complex-level estimates); BGG complexes (twisted complex, the derived complex of any length and its cohomology, weak symmetry, discretization, weak consistency, time-dependent problem, the elliptic projection (6.4) with its Strang bound and the convergence of (6.3), also modulo finite-dimensional harmonic forms) | §4.2–4.6, Thms 4.1, 4.2, 4.6, 4.7, Props 4.13, 4.16–4.19, Ch. 5–6 |
| `Feec.Algebra`, `Feec.Geometry` | Levi-Civita symbol, constant metrics, the exterior algebra, matrix calculus on jets and symbols, transverse–traceless matrices, the Koszul complex and polynomial forms in any dimension (direct sums, dimensions of `P_rΛᵏ` and `P_r⁻Λᵏ`, exactness), the wedge product; algebraic curvature tensors, the Riemann tensor of a connection, Hodge duality on 2-forms, the Weyl decomposition; the second Bianchi identity and its contractions (`∇^a G_ab = 0`, vacuum `∇^a C_abcd = 0`) for metrics of any signature, Christoffel symbols, frame components and torsion in a frame | Ch. 2–3, §4.7–4.10 |
| `Feec.Fourier` | Symbol complexes of multiplication operators, fibrewise reducing subspaces, closed range from spectral gaps, the torus and `ℝᵈ`, weak derivatives, real fields, spectral Galerkin; the symbols of de Rham, grad–curl, (4.16) and the BGG complex (5.1) | §4.10–4.11, Ch. 6 |
| `Feec.Domain` | `L²` fields on an open `Ω ⊆ ℝⁿ`, mollification, constant-coefficient operators with their minimal and maximal realizations and adjoints, complexes of them (also with constrained values), the `L²` de Rham complex of `k`-forms on any open `Ω ⊆ ℝⁿ` with both boundary-condition families and their duality, the Hessian, div-div and elasticity complexes on open `Ω ⊆ ℝ³`, minimal = maximal on `ℝⁿ`, smoothers commuting with `d` on domains star-shaped with respect to a ball, diagonal changes of variables and the pullback of `L²` forms along invertible affine maps, Rellich compactness of minimal domains passing to open subsets and affine images, pullbacks along bi-Lipschitz homeomorphisms of `ℝ³` (change of variables, `H̊(curl)` pullback, Piola transform of `H(div)`), boundary obstructions, finite speed of propagation for symmetric hyperbolic systems | §4.10, Prop 3.6 |
| `Feec.Mesh` | Conforming simplicial meshes of `Ω ⊆ ℝⁿ`, Kuhn simplices and Freudenthal meshes of boxes (face-to-face, uniform refinement), shape regularity | |
| `Feec.FiniteElement` | Abstract degrees of freedom and commuting interpolants; smooth forms, integration over simplices, Stokes' and the divergence theorem on simplices and meshes; the local spaces `P_rΛᵏ(T)`, `P_r⁻Λᵏ(T)` with unisolvent DOFs and commuting interpolants; Whitney forms; assembly of global spaces and conformity; the Whitney complex on any mesh; Bramble–Hilbert (classical form, and the `L²` form by averaged Taylor polynomials with the Sobolev embedding and `L²` interpolation errors of `P_rΛᵏ`, `P_r⁻Λᵏ`) and interpolation error on shape-regular meshes; the Whitney interpolation error with explicit constants and the Whitney interpolant as a reference interpolant; local DOF and inverse estimates for Whitney forms on homothetic simplices, and on shape-regular simplices for every affine-invariant polynomial space; the mesh geometry of smoothed projections on shape-regular meshes (barycentric Lipschitz bounds, the pseudo-manifold property, bounded overlap); smoothed projections; the global families `P_rΛᵏ`, `P_r⁻Λᵏ` of every admissible sequence (moment DOFs, subcomplexes, dimensions, partial boundary conditions), their inverse and interpolation estimates; vector-valued spaces `Vₕ ⊗ ℝᵐ`; the weak-symmetry maps `S⁰ = I`, `S¹ = 2 vskw` and `S_h = Π'S` (Prop 5.7) | §5.2–5.3, Tables 5.1, 6.1 |
| `Feec.Models` | Instances: de Rham, grad–curl, (4.16) and BGG on `𝕋ᵈ`/`𝕋³` and `ℝᵈ`/`ℝ³`; de Rham, grad–curl and (4.16) on bounded domains, with the density of `L²(TSD) ∩ H̊(curl)`; cubes: the method of images, the identification with the bounded-domain complex, static data, mirror boundary conditions for grad–curl, (4.16) and BGG, characterized on every open cube by Green's formulas (weak trace conditions), eigenbases on every open cube and, by Rellich on bounded open sets and Weber compactness transported along bi-Lipschitz radial maps, on every domain star-shaped with respect to a ball (balls and bounded convex sets included), the de Rham complex of `(0, ½)ⁿ` (parity model, identified with `H̊Λ` and `HΛ` of `(0, ½)ⁿ`: compactness, Poincaré `(2π)⁻¹`, harmonic forms, cohomology), Whitney complexes on Freudenthal meshes, the smoothed-projection estimates and Whitney approximation on them, and the finite element method with no hypothesis (stability, quasi-optimality, `O(h)` rates, semi-discrete Hodge wave), also for the higher-order families with rates `h^{s+1}`; the BGG data (4.16) on `(0, ½)³` and their finite elements of Tables 5.1/6.1 (compatibility (5.4), Props 5.7–5.9, the static error estimate, the semi-discrete wave scheme (6.5)), with the regular decomposition `CurlPotential` proved (a Helmholtz decomposition on a larger torus cell and a Hestenes extension from a shell), rates for solutions `C²` up to `∂Q` with vanishing tangential traces and convergence of (6.5) without rate; the de Rham complexes `HΛ_J(Q)` with boundary conditions on the faces normal to `J` (Hodge theory, identification with a parity model, conforming finite element subcomplexes) and parity smoothers (reflection and mollification, no dilation) giving uniformly bounded cochain projections onto them; the scheme (6.5) with the mirror boundary conditions (well posed, with a decoupled constant mode, convergent to the TSD solution, at rate `O(h)` for data in `D(L³)` and `O(hˢ)` for `H^{2+s}` data); Sobolev spaces `Hˢ` on `(0, ½)ⁿ` (integer orders by weak derivatives) with finite element rates `h^{min(s, r_eff)}`, and `h^{min(s,1)}` for the BGG elements of Tables 5.1/6.1 with the thesis' conditions; boxes with unequal sides (eigenbases, `K*`, mirror conditions); the finite element method, Whitney and higher-order families, on parallelepipeds (every quasi-uniform shape-regular mesh family) and on domains star-shaped with respect to a ball; inhomogeneous boundary data from whole-space TSD solutions on bounded domains and the fully discrete `fem4gr` scheme on Whitney spaces with its `O(h + Δt²)` error; on bounded domains, eigenfield obstructions to moving `K*` data and (4.16) under affine maps; spectral Galerkin for the torus de Rham complex; absorbing boundary conditions for the row-wise Einstein–Bianchi system on `(0, ½)³` (tangential traces and Green's formula, m-dissipativity and radiation, non-invariance of TSD, finite speed, the Galerkin scheme with boundary term) | §4.10–4.11, Ch. 6–7 |
| `Feec.Physics` | Linearized gravity (Einstein operator, gauge, plane waves), the linearized Einstein–Bianchi system (jets, fields, propagation of its constraints), the nonlinear Einstein–Bianchi system in an orthonormal frame (satisfied by every vacuum metric, linearizing to the linearized system), Maxwell's equations (Gauss laws, linear media by reweighting with isotropic and anisotropic coefficient fields, Ohmic loss, `k`-form Maxwell on open `Ω ⊆ ℝⁿ`, Whitney finite elements for PMC and PEC on the cube); the linearized Einstein–Bianchi system with weak symmetries on the cube: the static problem (5.3) and the wave problem (6.2) with the finite elements of Tables 5.1/6.1 (well-posedness, error estimates, `O(h)` rates, with no hypothesis), the forms model identified with the matrix model, convergence of (6.5) for every datum in `D(L)`, and to a solution that leaves TSD; powers `D(Lᵏ)` of the forms-model Hodge wave operator and an `O(h)` rate of (6.5) from `D(L³)` under multiplier bounds | Ch. 2–3, §3.4, §5.3, §6.3 |
| `Feec.Counterexamples`, `Feec.Examples`, `Feec.Numerics` | The refutations listed below; on the unit ball, a complete set of eigenvectors and the absence of TSD eigenfields `C²` up to the boundary; non-vacuity witnesses; the plane-wave check, Table 7.1 and the plane-wave runs of Ch. 7 (Dirichlet data on the cube, periodic on `𝕋³`), with `O(h + Δt²)` error bounds on `(0, ½)³` and on the unit cube of `fem4gr` | Ch. 7 |
| `Feec.Instances` | The approximating FEEC theorem on the concrete models (top layer: nothing else imports it, and it adds no names to lower namespaces): Maxwell's equations (Gauss laws as a reducing constraint of every window; spectral Galerkin on `𝕋ᵈ`; Whitney forms and every admissible `P_rΛ`/`P_r⁻Λ` sequence for PMC and PEC on cubes, parallelepipeds and domains star-shaped with respect to a ball, through conforming families (`Feec.Instances.Maxwell.feec`), as instances of the FEEC theorem (`Feec.Instances.Maxwell.maxwellFEEC`; `O(h)` and `O(h^{s+1})` rates from the Jackson estimates of the models) with discrete Poincaré inequalities; through the discrete complex, exactly preserved discrete Gauss laws; the non-reducing constraint `E = 0`, `B = 0`); frequency truncation `\|ξ\| ≤ N` on `ℝᵈ` (Maxwell) and `ℝ³` (linearized Einstein–Bianchi), with exact constraint preservation and Fourier-side `Hˢ` rates, sharp on `ℝ³`; the linearized Einstein–Bianchi system with the TSD constraint (Fourier spectral on `𝕋³` and cosine–sine spectral on the mirror cube, with time-uniform `Hˢ` rates; the scheme (6.5) with mirror boundary conditions and with the thesis' boundary conditions, with the elliptic projection (6.4) as comparison, with exactly preserved discrete Gauss constraints and `O(h)`, `O(hˢ)` rates; Maxwell on the cube through the discrete complex, with exactly preserved discrete Gauss laws); the cube with absorbing boundary conditions, through the dissipative FEEC theorem; the strong-symmetry EB systems (4.14) and (4.16) on `𝕋³`, `ℝ³` and, with mirror conditions, on cubes and boxes (spectral and cosine–sine spectral families of every symbol complex on `ℤᵈ` and every mirror complex), the TT gravitational plane waves as exact eigenmodes of the torus discretization, and, for every discretization of the thesis' complex on bounded domains, the data whose TSD residuals vanish (`K*`; the stationary data on cubes and boxes); Maxwell's equations for `k`-forms with PEC on every open `Ω`; Sobolev-data rates `h^{min(s, p+1)}` of the FEEC theorem on the cube | §4.10, §4.12–4.13, Ch. 6 |

## The approximating FEEC theorem

`Feec.HilbertComplex.approxFEEC` (`Feec.HilbertComplex.Approximation.ApproxFEEC`, statement
`Feec.HilbertComplex.ApproxFEEC.Verdict`) is the headline theorem of the library; `README.md`
states it in plain language and lists its instances. It is the top of a tower of three theorems,
each stated as a structure of named conclusions extending the one below and proved from it:

1. `Feec.HilbertComplex.dissipFEEC` (`Feec.HilbertComplex.Approximation.DissipFEEC`, statement
   `Feec.HilbertComplex.DissipFEEC.Verdict`) for `Feec.HilbertComplex.DissipFEEC`: a generator
   `A` on a Hilbert space (the parameter), m-dissipative (a field, so that the projections of a
   discretization carry `A` once), a closed constraint `K`, Hilbert spaces `Xₕ`
   with their own inner products and dissipative bounded generators `Lₕ`, and uniformly bounded
   reading maps `ιₕ : Xₕ → E` with uniformly bounded left inverses `πₕ` (variational crimes in the
   sense of [HolstStern2012] are allowed). The exact flow is the Lumer–Phillips semigroup
   `Feec.HilbertComplex.DissipFEEC.S`. Consistency is a hypothesis on a core,
   `Feec.HilbertComplex.DissipFEEC.Core`: comparison trajectories that approximate the exact orbits
   through `ιₕ` with consistency defects tending to `0`, uniformly on `[0, T]`; rates are over
   `Feec.HilbertComplex.DissipFEEC.RateClass`. The abstract estimate is
   `Feec.HilbertComplex.norm_sub_le_of_defect_of_dissipative` (best approximation plus integrated
   consistency defect, by the energy method). The verdict: well-posedness and the energy identity
   (`Feec.HilbertComplex.dissipFEEC_wellPosed`), the propagation criteria
   (`Feec.HilbertComplex.dissipFEEC_propagates_iff`, for `Feec.HilbertComplex.DissipFEEC.Keeps`),
   convergence on the closure of the core for every convergent family of initial values
   (`Feec.HilbertComplex.dissipFEEC_converges`, with `ιₕ πₕ → 1` derived,
   `Feec.HilbertComplex.DissipFEEC.tendsto_incl_proj`), rates
   (`Feec.HilbertComplex.dissipFEEC_rate`), the constraint residual measured through `ιₕ`
   (`Feec.HilbertComplex.dissipFEEC_residual`, `Feec.HilbertComplex.dissipFEEC_tendsto_infDist`)
   and the departures from sets that are not kept (`Feec.HilbertComplex.dissipFEEC_leaves`,
   `Feec.HilbertComplex.dissipFEEC_leaves_smooth`).
2. `Feec.HilbertComplex.skewFEEC` (`Feec.HilbertComplex.Approximation.SkewFEEC`, statement
   `Feec.HilbertComplex.SkewFEEC.Verdict`) for `Feec.HilbertComplex.SkewFEEC`, a `DissipFEEC` of a
   skew-adjoint generator (the field `isSkewAdjoint`, from which m-dissipativity is derived) with
   skew discrete generators (cores and rate classes are those of the base): adds Stone's isometric
   group `Feec.HilbertComplex.SkewFEEC.U`, equal to the semigroup for `t ≥ 0`, conservation of the
   norm, reducing iff invariant for all `t ∈ ℝ`
   (`Feec.HilbertComplex.skewFEEC_isReducing_iff_invariant`) and the departure in both time
   directions (`Feec.HilbertComplex.skewFEEC_leaves_smooth_symm`).
3. `Feec.HilbertComplex.approxFEEC` for `Feec.HilbertComplex.ApproxFEEC`, the `SkewFEEC` of the Hodge
   wave operator `L = 𝐝 - 𝐝†` (`ApproxFEEC H κ = SkewFEEC H.wave κ`) of a Hilbert complex on any
   finite window of any `ComplexShape` (its group is the wave group): adds unique weak solutions
   (`Feec.HilbertComplex.approxFEEC_unique_weak`) and, on graded complexes, reducing iff kept forward
   in time (`Feec.HilbertComplex.approxFEEC_isReducing_iff_keeps`).

**Fully discrete, on Banach spaces first.** `Feec.TimeStepping.banachFEEC`
(`Feec.TimeStepping.BanachFEEC`, statement `Feec.TimeStepping.BanachFEEC.Verdict`)
for `Feec.TimeStepping.BanachFEEC`: a strongly continuous semigroup on a real or complex Banach
space, Banach spaces `Xₕ` with bounded generators `Lₕ`, the exact and discrete semigroups bounded
by one `M`, uniformly bounded reading maps with uniformly bounded left inverses. For every time
scheme (`Feec.TimeStepping.TimeScheme`): stability, temporal error, the error as semidiscrete plus
temporal error, and convergence wherever the semidiscrete solutions converge; backward Euler is
stable by the Hille–Yosida estimates; every A-stable rational scheme satisfies Brenner–Thomée's
stability bound `M (1 + C' √n)` and the sharp smooth-data error `C M nτ τᵖ ‖·^{p+1}‖`, discrete
(constants independent of `h`) and exact. Every `DissipFEEC` is a `BanachFEEC` with `M = 1`
(`Feec.HilbertComplex.DissipFEEC.toBanachFEEC`), its time schemes are those of the Banach one, and
the fully discrete theorem `Feec.HilbertComplex.dissipFEEC_fullyDiscrete` derives `rate_iterates`
and `converges_iterates` from `banachFEEC`, its temporal errors and `rate_uniform_iterates` from
the Banach-space bounds of `Feec.TimeStepping.TimeScheme` (`rate_smooth_iterates`, the forced and
lifted iterates are Hilbert-side); the crown carries the Banach verdicts of its wave, heat,
perturbed and crime discretizations. On these (dissipative, Hilbert) discretizations they are
Banach-route constants, not new rates; the Banach theorems give new content only for estimates
in norms in which the family is not Hilbert-contractive (e.g. the maximum norm), and the crown
states none. The maximum-norm heat equation (`Feec.Models.Cube.MaxNormHeat.maxNormHeat`:
lumped-mass `P₁` elements on the Freudenthal meshes of a cube, a `Feec.TimeStepping.StableFamily`
with `M = 1` by the discrete maximum principle; its generators are also `ℓ²`-dissipative, but the
direct Hilbert route reaches the maximum norm with a factor `h^{-n/2}`) gives such estimates in the
maximum norm at the nodes, with constants independent of `h`: `O(h²)`, `O(τ + h²)` for backward
Euler and `O(h²) + C_r tₙ τᵖ ‖Lₕ^{p+1} v‖_∞` for every A-stable rational scheme, collected with a
nonzero classical solution (the first eigenmode, `Feec.Models.Cube.MaxNormHeat.sineSolution`) in
the companion `Feec.Instances.CrownNonVacuity` (field `maxNorm`). The scheme is the
lumped-mass Galerkin method on `P̊₁⁻Λ⁰`, the `P₁` (Whitney `0`-form) functions with vanishing
boundary DOFs (the interior nodal values are a linear isomorphism onto it;
`Feec.FiniteElement.P1Global`), and the errors hold in `L^∞(Q)` for the finite element function
(plus `n² D₂ h² / 2`). The classical `(2n + 1)`-point finite difference scheme is the same scheme
(`Feec.Models.Cube.FiniteDifferenceHeat.finiteDifferenceHeat`, field `finiteDifference` of the
companion: its Laplacian is the lumped-mass one, so the iterates and the estimates coincide). With
natural boundary conditions (`Feec.Models.Cube.MaxNormNeumann.maxNormNeumann`) the maximum
principle holds and the errors are `O(h)` (semidiscrete), `O(τ + h)` for backward Euler and
`O(h) + C_r tₙ τᵖ ‖Lₕ^{p+1} v‖_∞` for every A-stable rational scheme, in the maximum norm at the
nodes and in `L^∞(Q)`; `O(h²)` is not proved for Neumann. Both meshes are families of non-obtuse
meshes (`Feec.FiniteElement.NonobtuseMeshes`: any domain, Dirichlet data at the vertices that are
not nodes), whose maximum-norm theorem (`Feec.FiniteElement.NonobtuseMeshes.maxNormHeat`) gives
the stability of both and the Dirichlet error estimates: its semidiscrete, backward Euler and
rational errors are stated in terms of a bound `ε` of the nodal consistency error
`‖Iₕ uₜ - Lₕ Iₕ u‖_∞` (`t ε` added to the initial error), which on general non-obtuse meshes need
not tend to `0`; the rates in `h` come from the cube's uniform stencil (Dirichlet) and the barrier
(Neumann). Limitations: for rational schemes `‖Lₕ^{p+1} v‖_∞` is not bounded uniformly in `h`,
and the uniform route loses `√k`.

The regression tests of `scripts/FeecCheck/Verdicts.lean` derive the earlier conjunctions of
`dissipFEEC` and `approxFEEC` (convergence on the core from the comparison initial values, the
departures with their positive residual limits) from the verdicts.

**The conforming special case.** `Feec.HilbertComplex.constrainedFEEC`
(`Feec.HilbertComplex.Approximation.ConstrainedFEEC`) covers every conforming family
(`Feec.HilbertComplex.ConformingFamily`: finite-dimensional subcomplexes `Vₕ` of any Hilbert
complex, with uniformly bounded commuting cochain projections and the approximation property in
`W`) with a closed constraint (`Feec.HilbertComplex.ConformingFamily.withConstraint`), on every
window (`Feec.HilbertComplex.ConformingFamily.window`). Its verdict
`Feec.HilbertComplex.ConstrainedFEEC.Verdict` also has the field `cohomology`: wherever `H` has
closed range and finite-dimensional harmonic forms, `πₕ` eventually induces isomorphisms
`Hⁱ(H) ≅ Hⁱ(Vₕ)` (`Feec.HilbertComplex.ConformingFamily.eventually_bijective_cohomologyMap`).
Whitney forms and every admissible `P_rΛ`/`P_r⁻Λ` sequence on the cube, parallelepipeds and
star-shaped domains are conforming families (`Feec.Models.ConformingFamilies`).
`Feec.HilbertComplex.ConstrainedFEEC.toApprox` and `toCore` (`Feec.HilbertComplex.Approximation.ApproxConforming`)
make it an approximating discretization with `ιₕ` the inclusion, and
`Feec.HilbertComplex.ConstrainedFEEC.constrainedFEEC_of_approxFEEC` derives the statement of
`constrainedFEEC` from `approxFEEC`. Non-vacuity (`Feec.HilbertComplex.Approximation.ApproxFEECWitness`):
`Feec.HilbertComplex.ApproxFEEC.perturbed_nonvacuous` (scalar non-isometric `ιₙ`, nonzero
defect, inexact scheme, both residual branches) and
`Feec.HilbertComplex.ApproxFEEC.projPerturbed_nonvacuous` (`ιₙ = 1 + hₙP` not a multiple of the
identity, nonzero commutator defect, graded branch with the half bound);
`Feec.HilbertComplex.constrainedFEEC_nonvacuous` for the conforming case.

**The complex-level front end.** `Feec.HilbertComplex.ApproxFEEC.ofComplex`
(`Feec.HilbertComplex.Approximation.ApproxComplex`) takes an approximating family of discrete
Hilbert complexes in the sense of [HolstStern2012] (`Feec.HilbertComplex.ApproxComplex`):
finite-dimensional complexes `Vₕ` with their own inner products, injective bounded cochain maps
`iₕ : Vₕ → W` with left inverses `πₕ`, the inner-product defect `‖1 − iₕ*iₕ‖ → 0`, and the
graph-norm approximation property (from `L²` approximation and a commutation defect of `πₕ` on a
dense set, `Feec.HilbertComplex.ApproxComplex.Family.graphApprox_of_commute`). The discrete
generator is the Hodge wave operator of `Vₕ` in its own inner product. The comparison is the
modified elliptic projection `Rₕ = (1 − Lₕ)⁻¹ Gₕ` (on `D(L)`, `Gₕ = iₕ*(1 − L)`), and every hypothesis of
`ApproxFEEC.Core.ofOperator` is derived: a Strang lemma
(`Feec.HilbertComplex.ApproxComplex.Family.norm_graphFst_sub_inclL_ellProj_le`, best
approximation plus inner-product defect) and the defect bound
`Feec.HilbertComplex.ApproxComplex.Family.norm_defectOp_apply_le`. No adjoint-consistency
hypothesis is needed: `iₕ*` intertwines the adjoints exactly, `iₕ* 𝐝* = 𝐝ₕ* iₕ*`. Since `iₕ` is
an injective cochain map, `iₕVₕ` is a subcomplex and `𝐝ₕ = iₕ⁻¹𝐝iₕ`: the crimes covered are the
inner product of `Vₕ` and a non-cochain left inverse `πₕ`. `Feec.HilbertComplex.approxFEEC_ofComplex` adds the
discrete constraints to the four conclusions: a subspace of `Vₕ` is preserved iff it reduces the
discrete wave operator, reducing subcomplexes of `Vₕ` are preserved exactly, and their
`𝐝ₕ`-closed components are read in `W` as `𝐝`-closed. The conforming case is
`Feec.HilbertComplex.ConstrainedFEEC.toComplex` (zero inner-product defect, the same discrete
solutions as the subcomplex scheme, `Feec.HilbertComplex.ConstrainedFEEC.toComplex_sol`, and on
`D(L)` the elliptic projection (4.11) as comparison,
`Feec.HilbertComplex.ConstrainedFEEC.toXh_ellProj_waveLift`). On the
cube, `Feec.Instances.Maxwell.cubePMC_ofComplex` preserves the discrete Gauss laws
`{0} × N(𝐝ₕ₀*) × (Vₕ² ∩ N(d))` exactly. The non-conforming witness
`Feec.HilbertComplex.ApproxComplex.scaled_nonvacuous` (in `ApproxComplexWitness.lean`) has the
cochain reading map `diag(cₙ, 1, 1)` (an inner-product crime), a positive inner-product defect, a
nonzero consistency defect and an inexact scheme.

**The front end with a cochain defect.** `Feec.HilbertComplex.ApproxFEEC.ofComplexCrime`
(`Feec.HilbertComplex.Approximation.ApproxComplexCrime`) drops the cochain condition: an
approximating family of discrete differential spaces (`Feec.HilbertComplex.ApproxComplexCrime`)
has finite-dimensional `Xₕ` with a differential `𝐝ₕ` (`𝐝ₕ𝐝ₕ = 0`, no relation to `𝐝`), reading
maps `iₕ` and left inverses `πₕ`; the generator is `Lₕ = 𝐝ₕ − 𝐝ₕ*`. The **cochain defect**
`κₕ(y) = 𝐝ₕ* iₕ* y − iₕ* 𝐝* y` (`⟪κₕ(y), v⟫ = ⟪y, (iₕ𝐝ₕ − 𝐝iₕ) v⟫` when `iₕ v ∈ D(𝐝)`) is measured in
the dual discrete graph norm. The comparison is the exact-load elliptic projection
`Rₕ = (1 − Lₕ)⁻¹ iₕ* (1 − L)` on `D(L)`; since it needs `L y`, the Trotter–Kato bridge is restated on
pairs `(y, L y)` (`Feec.HilbertComplex.ApproxFEEC.ofComplexCrimeCore`) with its hypotheses
derived. The hypothesis is consistent approximation on a set of admissible states: approximants
with `‖y − iₕwₕ‖ → 0` and discrete residual `⟪(1 − Lₕ)wₕ, v⟫ − ⟪(1 − L)y, iₕv⟫ → 0` (dual discrete graph
norm), with the inner-product defect in the graph norm of `𝐝ₕ` tending to `0`
(`Feec.HilbertComplex.ApproxComplexCrime.Family.graphDefect`, the norm `‖1 − Jₕ‖_{Vₕ}` of `1 − Jₕ`
on the graph space `Vₕ` of `𝐝ₕ`, at most `‖1 − Jₕ‖`). Since `Rₕy` is itself an approximant with
residual `0`, consistent approximation at `y` is equivalent to `iₕRₕy → y`
(`Feec.HilbertComplex.ApproxComplexCrime.consistent_iff_tendsto_incl_load`): the hypothesis is the
pointwise convergence of the projection, and the content is in the ways to check it. The residual splits exactly
(`Feec.HilbertComplex.ApproxComplexCrime.Family.inner_residual_eq`) into the inner-product defect,
the graph-norm best-approximation error and the cochain defect
(`Feec.HilbertComplex.ApproxComplexCrime.ofCochainDefect`), or vanishes for a Galerkin projection
(`Feec.HilbertComplex.ApproxComplexCrime.ofGalerkinCore`: orthogonal reading maps and an existing
core whose comparison satisfies `(1 − Lₕ) pₕ(t) = iₕ* (1 − L) e^{tL} x`; a bridge that re-reads the
core, not a new convergence proof). `ofComplex` is the special case with
zero cochain defect (`Feec.HilbertComplex.ApproxComplex.toCrime`,
`Feec.HilbertComplex.ApproxFEEC.ofComplexCrime_toCrime`, by `rfl`, with the same comparison on
`D(L²)`). `Feec.HilbertComplex.approxFEEC_ofComplexCrime` gives the verdict, the Strang bound, the
residual splitting, the defect bound, and exact preservation of `Lₕ`-invariant subspaces of `Xₕ`.
**Rates**: `Feec.HilbertComplex.ApproxComplexCrime.rateClass` builds a `DissipFEEC.RateClass` from
approximants along the trajectory with approximation, `‖(1 − Jₕ)wₕ‖` and residual `O(m(h)ᵅ)`, so
`‖e^{tL}x − iₕ e^{tLₕ} Rₕ x‖ ≤ (C + C_ι C' t) m(h)ᵅ ‖x‖_c`
(`Feec.HilbertComplex.ApproxComplexCrime.error_le_of_rateClass`); the split rates (graph-norm best
approximation `O(hᵅ)`, inner-product defect `O(h^β)`, cochain defect `O(h^γ)`) give a rate class
of order `min(α, β, γ)` with explicit constants
(`Feec.HilbertComplex.ApproxComplexCrime.rateClass_of_split`, `error_le_of_split`; through
`Feec.HilbertComplex.ApproxComplexCrime.Family.rateData_of_split` and
`Feec.HilbertComplex.add_rpow_le_rpow_min`), exercised with distinct orders `(2, 1, 2)` by the
witness `Feec.HilbertComplex.ApproxComplexCrime.mixed_nonvacuous` (inner-product defect `O(h)`,
cochain defect exactly `h²`, rate `O(h)`). Instances: the conforming rate classes through
`ofComplex` (`Feec.HilbertComplex.ConstrainedFEEC.RateClass.toCrimeRate`,
`Feec.HilbertComplex.ConstrainedFEEC.RateClass.norm_sub_ofComplex_le`, factor `C + C_ι C' t`; for
Whitney Maxwell on the cube, `O(h)`); the witness
`scaled` at the rate of its inner-product defect `cₙ² − 1`
(`Feec.HilbertComplex.ApproxComplexCrime.scaled_rate`); a witness with a **nonzero cochain defect**,
`Feec.HilbertComplex.ApproxComplexCrime.shifted_nonvacuous` (`𝐝ₙ = cₙ·d` read by the identity:
isometric, not a cochain map, `⟪κₙ(0, 1, 0), (1, 0, 0)⟫ = cₙ − 1 ≠ 0`, rate `O(cₙ − 1)`); and the scheme
(6.5) with both boundary conditions (below).

**Static and heat theory with crimes.** `Feec.HilbertComplex.ApproxComplexCrime.Family.staticFEEC`
(`Feec.HilbertComplex.Approximation.StaticCrime`) is the elliptic theory of these families: the
discrete differential space `(Xₕ, 𝐝ₕ)` is a Hilbert complex on `ComplexShape.loop`
(`Feec.HilbertComplex.diffComplex`), and its mixed Hodge Laplacian with the load `iₕ* f` is well
posed for every `h` and, under a uniform discrete Poincaré inequality
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsPoincare`; it follows from bounded left inverses
of `iₕ` mapping `ker 𝐝` into `ker 𝐝ₕ` when `‖𝐝 iₕ v‖ ≤ C' ‖𝐝ₕ v‖`,
`Feec.HilbertComplex.ApproxComplexCrime.Family.isPoincare_of_proj`), uniformly stable. Against the
mixed solution of the total complex, the error is at most best approximation plus `80 C c_P²` times
the residual of any discrete triple
(`Feec.HilbertComplex.ApproxComplexCrime.Family.staticError_le`), and the residual splits into the
inner-product defect in the graph norm `‖1 − Jₕ‖_{Vₕ}` (`1 − Jₕ` acts only on discrete forms whose
graph norm the estimates control), the read error, the cochain defects of `u = G f` and `𝐝 u`, and
the harmonic defect `sup |⟪iₕ q, u⟫| / ‖q‖` over the discrete harmonic forms
(`Feec.HilbertComplex.ApproxComplexCrime.Family.norm_staticResidual_le`,
`Feec.HilbertComplex.ApproxComplexCrime.Family.staticError_le_of_split`). Consistent approximation
is again equivalent to convergence
(`Feec.HilbertComplex.ApproxComplexCrime.Family.staticConsistent_iff_tendsto`), and on a dense set
of data it gives convergence for every datum
(`Feec.HilbertComplex.ApproxComplexCrime.Family.tendsto_staticError_of_dense`). The heat theorem
(`Feec.HilbertComplex.ApproxComplexCrime.HeatFamily.heatFEEC`,
`Feec.HilbertComplex.Approximation.HeatCrime`; it uses only the family, the constraint, the filter
and the inner-product defect in the graph norm, `Feec.HilbertComplex.ApproxComplexCrime.HeatFamily`)
follows the conforming route with `iₕ*` in place of the orthogonal projection: the heat Ritz
projection `P_ℌₕ iₕ* y − Gₕ iₕ* z` gives a core when the static errors tend to `0` (the
inner-product defect enters its consistency defect; in the crown, from static consistency on a
dense set), and a static rate `e(f) ≤ K L mᵅ` with `‖1 − Jₕ‖_{Vₕ} ≤ K mᵅ` gives the heat rate
`(2K + C (3C + 16 c_P² C) K t) L mᵅ`
(`Feec.HilbertComplex.ApproxComplexCrime.HeatFamily.rate_heat_of_static`). These are the fields
`static`, `heat`, `heat_rate` of `Feec.HilbertComplex.ApproxComplexCrime.Verdict`. The shifted
family satisfies every hypothesis, converges for every datum and is inexact
(`Feec.HilbertComplex.ApproxComplexCrime.shifted_static_nonvacuous`,
`Feec.HilbertComplex.ApproxComplexCrime.shifted_heat`). **The cochain case** of [HolstStern2012],
§3 (`Feec.HilbertComplex.Approximation.StaticCochain`): reading maps that are cochain maps
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain`, not necessarily isometric) with
cochain projections bounded in the graph norm of `D(𝐝)`, the `V`-bounds of §3.3
(`Feec.HilbertComplex.ApproxComplexCrime.Family.CochainProj`; bounded in `W`,
`CochainProj.ofNormLe`)
have no cochain defect, the discrete Poincaré inequality `(c₀ + 1) C_π C`
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.isPoincare`, Thm 3.5), a harmonic defect
bounded by `C ‖b − iₕ πₕ b‖ + C_π ‖1 − Jₕ‖_{Vₕ} ‖u‖`, `b = P_𝔷 u`
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.norm_inner_incl_harmonic_le`), the gap
`‖p − iₕ P_ℌₕ πₕ p‖ ≤ (1 + C²) ‖p − iₕ πₕ p‖ + C C_π ‖1 − Jₕ‖_{Vₕ} ‖p‖` on `ℌ`
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.norm_sub_incl_harmonic_le`), the error
estimate with no assumed defect
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.staticError_le`; with the factor
`μ = sup ‖(1 − iₕ πₕ) r‖` over the unit harmonic forms of Cor 3.11, through the gap bound
`‖(1 − P_ℌ) iₕ q‖ ≤ (C μ + C_π ‖1 − Jₕ‖_{Vₕ}) ‖q‖` on `ℌₕ`,
`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.norm_incl_sub_harmonicProj_le`,
`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.staticError_le_of_harmonic`; in the
infimum form `μ inf_v ‖P_𝔅 u − iₕ v‖_V` of Cor 3.11, from the quasi-optimality
`‖x − iₕ πₕ x‖ ≤ (1 + C C_π) (‖x − iₕ v‖ + ‖𝐝 x − iₕ 𝐝ₕ v‖)` on `D(𝐝)`,
`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.norm_sub_incl_π_le`,
`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.staticError_le_of_harmonic_inf`),
convergence for every datum from `‖1 − Jₕ‖_{Vₕ} → 0` and `iₕ πₕ → 1`
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.tendsto_staticError`), and the
isomorphism on cohomology under the strict gap on `ℌ`
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.cohomologyEquiv`, Thm 3.3, Cor 3.4).
The conforming windows are instances: under closed range they satisfy the discrete Poincaré
inequality and the static method with crimes converges for every datum
(`Feec.HilbertComplex.ConformingFamily.windowCrime_isPoincare`,
`Feec.HilbertComplex.ConformingFamily.windowCrime_tendsto_staticError`), and with
finite-dimensional harmonic forms the cochain projections eventually induce isomorphisms on
cohomology
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.eventually_bijective_cohomologyMap`,
`Feec.HilbertComplex.ConformingFamily.windowCrime_eventually_bijective_cohomologyMap`; the fields
`crime_static`, `crime_cohomology` of `Feec.HilbertComplex.ConformingFamily.Verdict`). **Rates
with crimes**: Jackson-type approximation of `σ, u, p, P_𝔷 u` in the graph norm and
`‖1 − Jₕ‖_{Vₕ} ‖X‖` within `ε` give `e(f) ≤ K ε`
(`Feec.HilbertComplex.ApproxComplexCrime.Family.IsCochain.staticError_le_of_approx`, at the
projected approximants `staticError_le_projError`); so the conforming windows with a Jackson
estimate have the static and heat rates `O(L hᵒʳᵈ⁽ˢ⁾)` read with crimes
(`Feec.HilbertComplex.ConformingFamily.windowCrime_rate_static`, `windowCrime_rate_heat`, the
fields `rate_crime_static`, `rate_crime_heat` of `ConformingFamily.Verdict.Rated`), the static-rate
hypothesis of `rate_heat_of_static` discharged. With
nonzero harmonic forms and reading maps that are not isometric, the shear family of
`𝕜 --id--> 𝕜 --0--> 𝕜` (`iₙ = 1 + hₙ N`, `N² = 0`) exercises these results: static convergence
for every datum, a positive static error and a positive harmonic gap at `(0, 0, 1)` (whose reading
is not harmonic), and the eventual isomorphism on a nonzero cohomology
(`Feec.HilbertComplex.ApproxComplexCrime.shear_nonvacuous`,
`Feec.HilbertComplex.Approximation.StaticCochainWitness`); its static error is
`O(‖f‖ hₙ)` and its heat error `O(L hₙ)`, carried by the inner-product defect alone
(`Feec.HilbertComplex.ApproxComplexCrime.shear_staticError_le`, `shear_rate_heat`). Not
formalized: cohomology for reading maps that are not cochain maps.

**Instances.** Every row of the README table is proved through `approxFEEC`; the theorems the
README names (and others such as `Feec.Instances.Maxwell.maxwellFEEC` and
`Feec.Instances.EinsteinBianchi.einsteinBianchi_torus_constrainedFEEC`) depend on it. The
scheme (6.5) (`Feec.Instances.EinsteinBianchiFEM`) is not a discretization by subcomplexes
(`S₀,ₕ = π¹S⁰`, in general different from `S⁰`) and enters through its own reading maps, with the elliptic projection (6.4)
of the exact solution as comparison (`Feec.Instances.EinsteinBianchi.FEM.mirrorEllCore`,
`Feec.Instances.EinsteinBianchi.FEM.standardCubeEllCore`), without the model convergence theorems
of (6.5). The model verdict of the mirror scheme is a corollary
(`Feec.Instances.EinsteinBianchi.mirrorFEMVerdict_of_approxFEEC`). The scheme is one crime front,
through the front end with a cochain defect (`Feec.Instances.EinsteinBianchiFEMComplex`): the
generator of (6.5) is `𝐝ₕ − 𝐝ₕ*` for the discrete BGG differential
`𝐝ₕ(σ, u, M, ρ) = (0, −d̃Φ(σ, 0), S₁,ₕu, d̃u)` on the hidden space
(`Feec.Instances.EinsteinBianchi.FEM.waveGen_eq_diffWave`,
`Feec.Instances.EinsteinBianchi.FEM.diffGen_diffGen`), and the elliptic projection (6.4) is a
Galerkin projection (`Feec.Instances.EinsteinBianchi.FEM.mEll_galerkin`,
`Feec.Instances.EinsteinBianchi.FEM.cEll_galerkin`, from `inner_ellDefect` and the identification
of the continuous forms state by polarization), so `ofGalerkinCore` applies to the elliptic cores.
The verdicts are structures extending the verdict of the approximating FEEC theorem for
`ofComplexCrime` of these families by the instance-only fields:
`Feec.Instances.EinsteinBianchi.MirrorFEMApprox.Verdict` (mirror BCs: the closure `tsdQℝ` of the
core, which reduces `L`; the discrete solutions are (6.5); the discrete Gauss constraint is
preserved; the `O(h)` and `O(hˢ)` rates from the initialization (6.4), linear in `t`) and
`Feec.Instances.EinsteinBianchi.StandardCubeApprox.Verdict` (thesis' BCs: dense core, (6.5), the
preserved discrete Gauss constraint, and from `(0, 0, (0, β)) ∈ thesisTSD` TSD residuals tending
to a positive limit). With `𝐝ₕ` identified the discrete Gauss (divergence) constraint `σₕ = 0`,
`uₕ ⊥ d̃Φ(Vₕ⁰, 0)`, a discrete analogue of part of TSD,
(`Feec.Instances.EinsteinBianchi.FEM.hiddenGauss`) is invariant under `Lₕ` and preserved exactly by
the discrete solutions of both instances
(`Feec.Instances.EinsteinBianchi.FEM.mirrorFEM_preserves_hiddenGauss`,
`Feec.Instances.EinsteinBianchi.FEM.standardCube_preserves_hiddenGauss`).
The cochain defect of (6.5) is computed in `Feec.Instances.EinsteinBianchiFEMDefect`: along a
source-free classical solution of (6.2) it pairs with a hidden state `v` as
`-ℓ((I − π¹)S⁰ Φ(σᵥ, 0)) − ⟪M, (I − π²)S¹ uᵥ⟫`
(`Feec.Instances.EinsteinBianchi.FEM.cochainDefectForm_eq`), the two consistency functionals of
the Strang bound of (6.4). For the thesis' boundary conditions this is the family's cochain
defect (`Feec.Instances.EinsteinBianchi.FEM.inner_standardCube_cochainDefect`); it is `O(h)` in the
dual discrete graph norm when `ℓ(t)` is an `L²` functional and `M(t) ∈ D(d₁*)`
(`Feec.Instances.EinsteinBianchi.FEM.exists_standardCube_cochainDefect_le_mesh`, regularity
assumed) and tends to `0` for every datum of `D(L²)`. For mirror boundary conditions it vanishes
at every TSD state of `D(L)` (`Feec.Instances.EinsteinBianchi.FEM.mirrorFamily_cochainDefect_eq_zero`,
`Feec.Instances.EinsteinBianchi.FEM.mirrorComplex_cochainDefect_eq_zero`). That the cochain
defect is nonzero for some mesh and datum is not proved.

Limits.
- `ApproxFEEC` itself is a semigroup-form abstraction: discrete constraints are stated only
  through `ofComplex` (reducing subcomplexes) and `ofComplexCrime` (`Lₕ`-invariant subspaces of
  the total discrete space; no grading). In `ofComplex` `iₕ` must be an exact cochain map;
  (6.5), whose discrete differential uses `S₀,ₕ = π¹S⁰` (different from `S⁰` in general; its
  reading maps are not shown to be cochain maps), is formalized through `ofComplexCrime`, not as an
  instance of `ofComplex`. The discrete spaces are
  finite-dimensional; the inner-product defect is in operator norm; the cochain defect is
  measured in the dual discrete graph norm at admissible states (pointwise, not uniformly).
- For (6.5) the consistent-approximation hypothesis is discharged with the elliptic projection
  (6.4) as approximant (`ofGalerkinCore`): its residual vanishes by the Galerkin identity, and its
  approximation is the Strang bound of (6.4) with the weak consistency constants `K₀`, `K₁`. The
  cochain defect of (6.5) is computed and bounded separately
  (`Feec.Instances.EinsteinBianchiFEMDefect`; the `O(h)` bound for the thesis' boundary conditions
  assumes `ℓ(t) ∈ L²` and `M(t) ∈ D(d₁*)`), and for mirror boundary conditions it vanishes on TSD
  states; that it is nonzero for some mesh and datum is not proved, so a nonzero cochain defect
  is exercised only by the witness `shifted`. The rates of (6.5) through `ofComplexCrime` have larger constants than
  the elliptic rate classes (`(4K + 8Kt) h`), with the same orders. The only non-conforming
  instance of `ofComplex` is the abstract witness, whose crime is the inner product alone; a
  nonzero commutation defect of `πₕ` is exercised by no instance (remark, not formalized: in
  finite dimension the approximation property forces `πₕ = iₕ⁻¹` eventually); the Maxwell
  instance of `ofComplex` is the conforming one.
- The split rate `rateClass_of_split` (order `min(α, β, γ)`, measure `0 ≤ m ≤ 1`) is exercised
  only by the witness `mixed`. The rates of (6.5) go through
  `Feec.HilbertComplex.galerkinRateClass`, with the elliptic projection (6.4) as approximant
  (residual `0`), not through the split.
- Rate classes and cores are hypotheses on the data that each instance must supply. The
  conforming rate carries `(1 + C_P)(1 + t)²`, where the model theorems have `(1 + t)`; through
  `ofComplex` (`ConstrainedFEEC.RateClass.toCrimeRate`) it is `C + C_ι C' t`.
- Without a grading, the converse with data in `D(L) ∩ K` is stated for `t ∈ [-T, T]`, and its
  discrete residual is not stated. Forward invariance alone does not give a reducing subspace (the
  de Rham counterexample in the `ConstrainedFEEC` docstring, not formalized).
- For the thesis' boundary conditions `D(L) ∩ thesisTSD` is not dense in `thesisTSD` (the density
  gap of Prop 4.17, `Feec.Instances.EinsteinBianchi.exists_mem_thesisTSD_not_mem_closure`), so the
  `D(L) ∩ K` clauses of the verdict say nothing there; the converse comes from the per-datum clause
  at `(0, 0, (0, β))` and the `K`-or-`K^⊥` clause. The componentwise discrete failure
  (`Eₕ ∉ L²(TSD)`, `Bₕ` not symmetric) is the model statement
  `Feec.Instances.EinsteinBianchi.standardCubeVerdict`, not derived from the instance, and there
  is no rate class for these boundary conditions.
- On (6.5) both reading maps are isometric, and that the consistency defect is nonzero is not
  proved for any datum (for mirror TSD data the Strang consistency terms vanish). Non-isometric
  reading maps and nonzero defects are exercised only by the abstract witnesses; one of them,
  `Feec.HilbertComplex.ApproxComplex.scaled_nonvacuous`, goes through
  `Feec.HilbertComplex.ApproxFEEC.Core.ofOperator` (as `ofComplexCore`) with a nonzero defect.
  That the exactly preserved discrete Gauss constraint `hiddenGauss`, read in `W`, lies in `tsdQℝ`
  or in `thesisTSD` is not shown, so the residual-`0` clause for `Lₕ`-invariant subspaces is not
  used on (6.5).
- On `ℝᵈ` and `ℝ³` the truncation is conforming (`ιₙ` is the inclusion, zero defect), the
  Sobolev classes are defined on the Fourier side, and it is a semi-discretization in frequency.
- The Maxwell rate classes require `C²` orbits on `[0, T]`, and their only witness is the zero
  datum. The non-reducing Maxwell constraint is exhibited on the torus and on `ℝᵈ`.

## The dissipative FEEC theorem and absorbing boundary conditions

`Feec.HilbertComplex.dissipFEEC` (`Feec.HilbertComplex.Approximation.DissipFEEC`, statement
`Feec.HilbertComplex.DissipFEEC.Verdict`) is the base of the tower: m-dissipative generators `A`
(Lumer–Phillips contraction semigroups) and dissipative bounded discrete generators `Lₕ`; an
approximating FEEC discretization is one by definition (`ApproxFEEC` is a `SkewFEEC`, which
extends `DissipFEEC`), and the verdict of `approxFEEC` extends the verdict of `dissipFEEC`. It
bundles well-posedness with the energy identity, the propagation criteria (invariance of `K` iff
resolvent invariance iff solvability of the stationary problem in `D(A) ∩ K`, from
`Feec.Semigroup.DissipativeInvariance`; reducing iff `K` and `Kᗮ` invariant), convergence on the
closure of a core, rates, the residual and the departures. The resolvent form of the
Trotter–Kato theorem gives cores from consistent discrete resolvents
(`Feec.HilbertComplex.DissipFEEC.Core.ofResolvent`). Impedance triples (`Feec.ImpedanceTriple`:
energy space, field, differential, boundary trace) give m-dissipative impedance operators, and
their conforming Galerkin schemes carry the boundary term in the bilinear form, a dissipative
discrete generator and the discrete energy identity, with the full verdict under the approximation
property (`Feec.ImpedanceTriple.GalerkinData.galerkin_verdict`).

On the cube `(0, ½)³` the row-wise linearized Einstein–Bianchi system with the absorbing condition
`n × Eᵢ + (Bᵢ)_τ = 0` (`Feec.Models.Cube.Absorbing`) is such an impedance operator; the headline is
`Feec.Instances.EinsteinBianchi.absorbingVerdict`. It is m-dissipative, radiates
(`‖S(t) u₀‖² = ‖u₀‖² - 2 ∫₀ᵗ ‖E_τ‖²`), propagates the Gauss laws from TSD data, keeps TSD on the domain of
dependence and has finite speed of propagation
(`Feec.Models.Cube.Absorbing.absorbingSemigroup_eq_depDomain`), but **TSD is not invariant**
(`Feec.Models.Cube.Absorbing.not_invariant_tsdPair`): on TSD states of the domain the condition
forces the weak normal–normal trace of `E` to vanish on the face `{x₀ = ½}`, which the constant TSD field
`diag(1, -½, -½)` violates. The semi-discrete Galerkin scheme converges for every datum; from some
TSD datum the solution leaves TSD, and the discrete residuals have a positive limit
(`Feec.Models.Cube.Absorbing.absorbingGalerkin_residual_not_invariant`).

Limits:
- No constraint-preserving absorbing condition is formalized (e.g. the modified systems or
  derivative boundary conditions of [FriedrichNagy1999], [KreissWinicour2006], [CPRST2003]); the
  ball is not treated.
- The energy space is the closure of smooth triples; that it equals the space of triples satisfying
  Green's formula (`greenTriples`; density of smooth fields in `H_imp(curl)`) is not proved, nor
  that smooth states with the boundary condition form a core or that smooth states of the domain
  satisfy the condition. Tangential traces of smooth fields are not shown to be dense in `L²(∂Q)`.
- The approximating Galerkin spaces of the instance are dense-sequence spaces
  (`Feec.ImpedanceTriple.GalerkinData.ofDenseSeq`), not finite element spaces: conformity of the
  Whitney or BGG elements on the Freudenthal meshes in the energy space and their approximation in
  the energy norm (with the boundary term) are not proved, and no rate class is constructed.
- Finite speed compares with weak solutions in `Q`; no weak solution other than the absorbing
  orbits is constructed (for instance restrictions of whole-space solutions), and the statement is
  non-trivial only for `t < ¼`.

## Highlights

- Stone's theorem over `ℝ` and `ℂ` (`LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup`): the Hodge wave equation of every Hilbert complex is well posed, with the thesis's full forcing class (Thms 4.3, 4.6–4.7).
- Constraint propagation (Props 4.16–4.19) for every Hilbert complex: a constraint propagates iff it is a reducing subcomplex. Props 4.17/4.19 hold on 𝕋³ and ℝ³; on every bounded domain their hypotheses and conclusions fail, and on cubes with the thesis's boundary conditions only stationary data propagate. With tensorial mirror boundary conditions, characterized by Green's formulas (weak trace conditions), they hold on every open cube. The Ch. 6 method inherits the bounded-domain failure: its semi-discrete scheme (6.5) converges, with no hypothesis, to a solution that leaves TSD; with mirror conditions it converges to the TSD solution, at rate `O(h)` for data in `D(L³)` with no regularity hypothesis.
- Brezzi theory and Babuška–Nečas over `ℝ` and `ℂ`, the semi-discrete error estimate (Thm 4.14), and the BGG weak-symmetry construction (Ch. 5–6) with the finite elements of Tables 5.1/6.1 on the cube, convergent with no hypothesis (the regular decomposition is proved).
- FEEC beyond the thesis: Lumer–Phillips and the Hodge heat equation, the Hodge solution operator and the quasi-optimal error estimate of the mixed method (AFW 2010, Thm 3.9), unisolvent `P_rΛᵏ`/`P_r⁻Λᵏ` elements in any dimension, and Whitney complexes on Freudenthal meshes of the cube `(0, ½)ⁿ` with the finite element method proved with no hypothesis: smoothed-projection estimates from inverse estimates, the Poincaré inequality of `HΛ`/`H̊Λ` via the parity model, Whitney interpolation error; hence stability, quasi-optimality, `O(h)` rates for `C²` solutions, and semi-discrete Hodge wave and Maxwell (PMC, PEC) convergence; the same on parallelepipeds, and on domains star-shaped with respect to a ball under the Poincaré inequality ([coverage table](#feec-book-coverage)).
- The nonlinear Einstein–Bianchi system (§3.4) in an orthonormal frame: every vacuum metric satisfies it, it linearizes to the system of Prop 3.4, and in the thesis' `K`/`a` form the printed signs of the `B`-constraint and the `B`-evolution equation are corrected. The second Bianchi identity and its contractions are proved for metrics of any signature.
- The Ch. 7 runs as implemented, with boundary data from the exact plane wave: well posed via a lifting, the plane wave stays TSD while a TSD perturbation of its data does not, and the fully discrete Crank–Nicolson scheme on Whitney spaces is well posed, with error and constraint monitors `O(h + Δt²)` for smooth solutions.
- Twenty corrections to the thesis, each pinned to a Lean declaration (most in `Feec.Counterexamples`), e.g. Prop 2.4(b) is off by a factor ½, "Fredholm ⇒ closed" is false, Prop 6.2 needs compatibility conditions.
- Every correction comes with a proved repaired statement (the table in [`docs/OVERVIEW.md`](#repaired-statements)). For Props 4.17/4.19 and Ch. 6 the repair covers domains without boundary, cubes and (Prop 4.17) boxes, not curved domains.

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
- **Props 4.17, 4.19**: for every Hilbert complex and every constraint subspace, the density conjectures are unnecessary and the projection hypothesis is necessary and sufficient for propagation (`Feec.HilbertComplex.ReducingSubcomplex.propagates`, `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`). Without a boundary the projection hypothesis holds and Props 4.17 and 4.19 hold with existence and uniqueness, on `𝕋³` (`Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.tsd_existsUnique`) and on `ℝ³` (`Feec.Models.Euclidean.GradCurl.tsd_existsUnique`, `Feec.Models.Euclidean.SymCurl.tsd_existsUnique`, and for real fields `Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`). On every nonempty bounded open `Ω ⊆ ℝ³` the projection hypotheses fail, for every short complex with `D(d₁) ⊆ H̊(curl)`, resp. `D(d₁) ⊆ H̊(curl, S)` for the sym-curl complex (`Feec.Counterexamples.BoundedDomainTSD.not_isReducing_tsd`, `Feec.Counterexamples.BoundedSymTSD.not_isReducing_tsd`) and with the maximal curl (`Feec.Counterexamples.BoundedDomainTSD.not_projection_magnetic`), and so do the conclusions: explicit TSD data have strong solutions that leave the constraint set (`Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`, `Feec.Counterexamples.BoundedSymTSD.tsd_not_propagates`). The density conjectures themselves are true on every bounded domain (`Feec.Models.BoundedDomain.dense_curl_inter_divFree`, `Feec.Models.BoundedDomain.dense_curl_maximal_inter_divFree`); the invalid step is the inference that `H̊(curl) ∩ L²(TSD)` is dense in `L²(TSD)`: its closure has infinite codimension (`Feec.Counterexamples.BoundedDomainTSD.not_dense_tsd_inter`, `Feec.Models.BoundedDomain.not_tsd_le_closure_sup_finiteDimensional`), and on domains star-shaped with respect to a ball it is `L²(TSD₀)` (`Feec.Models.BoundedDomain.closure_eq_tsd₀`, `Feec.Counterexamples.BoundedDomainTSD.density_gap`). The failure starts at the boundary: TSD propagates in the interior at unit speed, and for the datum `(0, 0, β)` the violation sits in the boundary layer (`Feec.Models.BoundedDomain.tsd_depDomain`, `Feec.Counterexamples.BoundedDomainTSD.beta_violation_boundary_layer`). What survives on bounded domains: Props 4.16 and 4.18, and Props 4.17/4.19 on the largest invariant constraint space `K* ⊊ K` (`Feec.Counterexamples.BoundedDomainTSD.invariantCore_tsd`, `Feec.Counterexamples.BoundedSymTSD.invariantCore_tsd`). On every open cube, `(0, π)³` included, with the boundary conditions of Prop 4.17, `K*` consists of the stationary data, and forward invariance alone already forces this (`Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Counterexamples.CubeStationary.forward_iff_stationary`; proved in a parity model, `Feec.Models.Cube.Parity.mem_invariantCore_iff`, `Feec.Models.Cube.Parity.forward_iff`). With tensorial mirror conditions Props 4.17 and 4.19 hold, in the parity model (`Feec.Models.Cube.Mirror.existsUnique_mem`, `Feec.Models.Cube.MirrorSym.existsUnique_mem`), for `L²` fields on `(0, ½)³` (`Feec.Models.Cube.Mirror.existsUnique_memQ`) and on every open cube (`Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`). For the boundary conditions as printed in Prop 4.19 (`Feec.Models.BoundedDomain.hessCurlMax`), the projection hypothesis and the density fail (`Feec.Counterexamples.BoundedSymTSD.not_starProjection_mem_wave_domain_hessCurlMax`, `Feec.Counterexamples.BoundedSymTSD.not_dense_hessCurlMax`), and on every ball `{|x − c| < R}` so do the conclusion and the density hypothesis, the latter read with the boundary condition of the printed data space `H̊(sym curl, T)` (`Feec.Counterexamples.BallSymTSD.not_propagates`, `Feec.Counterexamples.EveryBallSymTSD.tsd_not_propagates`, `Feec.Counterexamples.EveryBallSymTSD.not_dense_tsdT`). The mirror conditions are weak trace conditions: on every open cube `D(L)` is characterized by Green's formulas against `C¹` functions vanishing on the faces where the parity is odd (read as `σ·n = 0`, `E_{nτ} = E_{τn} = 0`, `B_{ττ} = 0`), and Prop 4.17 holds with them (`Feec.Models.Cube.Mirror.mem_wave_domain_cube_iff_trace`, `Feec.Models.Cube.Mirror.existsUnique_memCube_trace`). On every bounded domain, an eigenfield `curl* curl u = ξ²u`, `ξ ≠ 0`, with `u, curl u ∈ H̊(curl)` vanishes (`Feec.Models.BoundedDomain.eq_zero_of_isEigenfield_of_mem_minimal`), so under pure point spectrum `K*` has a moving datum exactly when some TSD eigenfield has `curl u ∉ H̊(curl)` (`Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff`). Pure point spectrum is proved on every domain star-shaped with respect to a ball, so on every ball this criterion holds with no hypothesis (`Feec.Models.StarShaped.coreSub_le_stationary_ball_iff`), and on the unit ball no TSD eigenfield is `C²` up to the boundary (`Feec.Counterexamples.BallEigenfields.eq_zero_of_isEigenfield_of_contDiff_ball`); that `K*` is stationary on the ball is reduced to the boundary regularity of Maxwell eigenfields (`Feec.Counterexamples.BallEigenDense.coreSub_le_stationary_ball3_of_maxwellRegularity`).
- **(5.1)**: exactness at `Ṽ¹` is used but never proved (`Feec.BGG.Segment.ker_D1_eq_range_D0`).
- **Prop 5.4**: exactness at `V_h¹` cannot be dropped (`Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`).
- **Prop 5.7**: the proof's density step is invalid for canonical interpolants, and the identity needs moment DOFs for `P₂Λ⁰`; with them it holds on continuous fields (`Feec.FiniteElement.PolySeq.wsGlobal_tensorInterp`), and (5.4) holds for the smoothed projections of Table 5.1 (`Feec.Models.Cube.WeakSymmetry.cubeFEM_compatible`).
- **Prop 5.8**: the global `ℓ¹` DOF sums of the proof are not uniformly equivalent to `L²` norms; local `ℓ²` scaling gives the bounds (`Feec.Models.Cube.WeakSymmetry.norm_glue_bggS0h_le`, `Feec.Models.Cube.WeakSymmetry.norm_glue_bggS1h_le`).
- **Prop 5.9(2)**: false, for the canonical projection and for every projection onto the Raviart–Thomas spaces (`Feec.Models.Cube.WeakSymmetry.exists_interpolationError_ge`, `Feec.Models.Cube.WeakSymmetry.not_exists_bestApprox_bound`); Thm 5.5 holds with a weak-consistency bound from regular potentials instead (`Feec.BGG.Discrete.error_estimate_of_weakConsistency`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_rate_C2`).
- **(6.4)**: as printed the elliptic projection is ill-formed and its constraint inhomogeneous; corrected, it is uniquely solvable with a Strang bound and an `O(h)` rate (`Feec.BGG.existsUnique_isEllipticProjection`, `Feec.BGG.Discrete.strang_rate_of_regularPotential`), and it gives the convergence of (6.3) that the thesis does not state (`Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`), on the cube with the elements of Table 6.1 (`Feec.Models.Cube.WeakSymmetry.cubeWave_rate`).
- **Prop 6.2**: false as stated (`Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`); it holds exactly under compatibility conditions (C1)–(C3) (`Feec.BGG.exists_discreteSolution_iff`), of which only (C2) constrains the dynamic data (`Feec.BGG.exists_discreteSolution_iff_compatible_u`).
- **Ch. 6**: on bounded domains with the boundary conditions of §6.3, the weak-symmetry method inherits the failure: from the TSD datum `(0, 0, (0, β))` the unique solution has `u(t) ∉ L²(TSD)` and `B(t)` non-symmetric for some `t` in every `[0, T]` (`Feec.Counterexamples.BoundedBGG.bggComplex_verdict`). On `ℝ³` and `𝕋³` the same system propagates TSD (`Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_existsUnique`), and so it does on `(0, ½)³` with mirror conditions (`Feec.Models.Cube.MirrorBGG.existsUnique_memQ`). With the mirror conditions the semi-discrete scheme (6.5) is built on the Freudenthal meshes of `(0, ½)³` (componentwise vanishing DOFs on the faces normal to `eₐ`, canonical `S_h = Π'S`) and is well posed: existence ⇔ (C2), uniqueness, energy stability, the constant mode of `σ` decoupled (`Feec.Models.Cube.MirrorWeakSymmetry.mirror_exists_unique`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_constantMode`). With `S_h = πS` for parity-smoothed projections it converges to the TSD solution from every TSD datum in `D(L²)`, with `σₕ`, `Mₕ` → 0 and `Bₕ` asymptotically symmetric (`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`), and with no regularity to the real part of the solution from every point of the constraint (`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_of_mem_tsd`), at rate `O(h)` for every TSD datum in `D(L³)` and `O(hˢ)`, `0 ≤ s ≤ 1`, for TSD data in `H^{2+s}`, with no regularity assumed (`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`). With the §6.3 conditions the scheme converges, with no hypothesis, to the solution from the TSD datum `(0, 0, (0, β))`, which leaves TSD, and for large `N` the discrete fields leave TSD too (`Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`, through the identification of the forms and matrix models, `Feec.EinsteinBianchi.MatrixModel.matrixComplex_eq_map`).
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
| Props 4.17, 4.19 | On bounded `Ω`, under projection and density conjectures, TSD data propagate | Hypotheses false and conclusions fail on every bounded `Ω` with the stated conditions; the density inference is invalid; for Prop 4.19 the conclusion and the density fail on every ball | Propagation ⇔ the constraint reduces the complex, for every complex; hold on `𝕋³` and `ℝ³` for all TSD data, with existence and uniqueness; with the thesis's conditions only on `K*`, stationary on cubes (4.17), and on every bounded `Ω` a moving element of `K*` needs a TSD eigenfield with `curl u ∉ H̊(curl)` (an equivalence on every ball, with no hypothesis; on the unit ball no TSD eigenfield is `C²` up to the boundary); with tensorial mirror conditions on every open cube, `(0,1)³` and `(0,π)³` included, with `K* = K` and moving data, the conditions of 4.17 characterized by Green's formulas (weak traces); on every box with unequal sides, only stationary data propagate with the thesis's conditions and `K* = K` with the mirror conditions | `Feec.HilbertComplex.isReducing_iff_forall_isStrongSolution`, `Feec.Models.Cube.Mirror.propagatesCube`, `Feec.Models.Cube.Mirror.existsUnique_memCube`, `Feec.Models.Cube.Mirror.existsUnique_memCube_trace`, `Feec.Models.Cube.Mirror.mem_wave_domain_cube_iff_trace`, `Feec.Models.Cube.MirrorSym.propagatesCube`, `Feec.Models.Cube.MirrorSym.existsUnique_memCube`, `Feec.Models.Cube.Ident.forward_iff`, `Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff`, `Feec.Models.StarShaped.coreSub_le_stationary_ball_iff`, `Feec.Counterexamples.BallEigenfields.eq_zero_of_isEigenfield_of_contDiff_ball`, `Feec.Counterexamples.EveryBallSymTSD.tsd_not_propagates`, `Feec.Counterexamples.EveryBallSymTSD.not_dense_tsdT`, `Feec.Counterexamples.BoxStationary.forward_iff_stationary_box`, `Feec.Models.Box.Mirror.invariantCore_eqBox` |
| (5.1) | Exactness at `Ṽ¹` (used in Props 5.2, 5.4) | Never proved | `N(S₁) ∩ N(d̃¹) = R(0 d)` from exactness of the two complexes; used in Prop 5.2 | `Feec.BGG.Segment.ker_D1_eq_range_D0`, `Feec.BGG.Segment.range_D0`, `Feec.BGG.Hilb.mem_Z1_iff` |
| Prop 5.4 | The discrete system (5.6) is invertible | The proof never uses exactness at `V_h¹`, which is necessary | With exactness at `V_h¹` and `Ṽ_h¹`, `d̃` injective and `V_h¹ = dV_h⁰ + S₀Ṽ_h⁰` (weaker than `S₀` onto): unique solution for all data; derived from the continuous hypotheses | `Feec.BGG.existsUnique_isMixedSolution`, `Feec.BGG.Discrete.existsUnique_mixed_h`, `Feec.Counterexamples.DiscreteBGG.mixed_not_unique_of_not_exactTop`, `Feec.BGG.exists_mixed_homogeneous_of_perp` |
| Prop 5.7 | (5.4) `S₀,ₕΠ̃⁰ = Π¹S₀` for the elements of §5.3, by density | The density step is invalid (canonical interpolants are not `L²`-continuous); the identity depends on moment DOFs for `P₂Λ⁰` | With moment DOFs: `Π¹S⁰Π̃⁰ = Π¹S⁰` (and `Π²S¹Π̃¹ = Π²S¹`) on continuous fields, `S₀,ₕ` onto `P₁⁻Λ̊¹`; transferred to the smoothed projections of one smoother, (5.4) holds for the discretization of Table 5.1 on every Freudenthal mesh of `(0, ½)³` | `Feec.FiniteElement.PolySeq.wsGlobal_tensorInterp`, `Feec.FiniteElement.PolySeq.bggS0h_tensorInterp`, `Feec.FiniteElement.PolySeq.bggS0h₀_surjective`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_compatible` |
| Prop 5.8 | `S₀,ₕ`, `S₁,ₕ` uniformly `L²`-bounded | The proof's global `ℓ¹` DOF sums are not uniformly equivalent to `L²` norms | `‖S₀,ₕψ‖ ≤ C‖ψ‖`, `‖S₁,ₕv‖ ≤ C‖v‖` on the Freudenthal meshes of `(0, ½)³`, `C` independent of `h`, by local `ℓ²`/`L²` scaling; `S₁ = 2 vskw` | `Feec.Models.Cube.WeakSymmetry.norm_glue_bggS0h_le`, `Feec.Models.Cube.WeakSymmetry.norm_glue_bggS1h_le` |
| Prop 5.9 | (1) `‖(I − Π¹)S₀ψ‖ ≤ Ch‖ψ‖_V`; (2) `‖(I − Π²)S₁v‖ ≤ Ch‖v‖_V` | (2) is false, for every projection onto the Raviart–Thomas spaces | (1) on `P₂Λ⁰ ⊗ ℝ³`, for the canonical `Π¹` and for the smoothed `π¹`; (2) refuted on every mesh (and for best approximation); Thm 5.5 uses weak consistency instead | `Feec.Models.Cube.WeakSymmetry.norm_sub_glue_bggS0h_le`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_happ0`, `Feec.Models.Cube.WeakSymmetry.exists_interpolationError_ge`, `Feec.Models.Cube.WeakSymmetry.not_exists_bestApprox_bound` |
| Thm 5.5 | Error estimate for (5.6) under Prop 5.9 | Rests on the false Prop 5.9(2); needs `λ ∈ W¹`; `‖·‖_{Γ_h}` misnamed | With the weak consistency `|⟪S¹u, (S₁ − S₁,ₕ)v⟫| ≤ Ch‖v‖_V` (from regular potentials) in place of 5.9(2), and `λ ∈ L²`: on the cube with the elements of Table 5.1, `‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h)²` for solutions `C²` up to `∂Q` (restrictions of `C²` fields on `ℝ³`) with vanishing tangential traces, the class of `S¹u` derived from that of `u`; no hypothesis: the regular decomposition `curl H̊(curl) = curl S⁰ H̊¹(Q; ℝ³)` (`CurlPotential`) is proved; for relative-class `Hˢ` data the rate `h^{min(s,1)}`, with `‖λ‖` and a pairing bound on `S¹u` as hypotheses | `Feec.BGG.Discrete.error_estimate_of_weakConsistency`, `Feec.BGG.Discrete.weakConsistency_of_regularPotential`, `Feec.Models.Cube.WeakSymmetry.curlPotential`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_rate_C2'`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_rate_tr'`, `Feec.EinsteinBianchi.StaticFEM.staticFEM_cube`, `Feec.EinsteinBianchi.StaticFEM.staticFEM_rate_tr_cube`, `Feec.Models.Cube.WeakSymmetry.staticFEM_rate_sobolev_cube` |
| (6.4) | The elliptic projection of the exact solution (used for the Ch. 6 error analysis) | Ill-formed (argument lists, inhomogeneous constraint); solvability and approximation never shown | With the homogeneous constraint and the continuous forms on the exact state: unique solvability, Galerkin orthogonality, a Strang bound and an `O(h)` rate (on the cube for states `C²` up to `∂Q` with vanishing tangential traces); convergence of (6.3) from its projected data, also modulo finite-dimensional harmonic forms | `Feec.BGG.existsUnique_isEllipticProjection`, `Feec.BGG.IsEllipticProjection.galerkin`, `Feec.BGG.Discrete.strang_of_isEllipticProjection`, `Feec.BGG.Discrete.strang_rate_of_regularPotential`, `Feec.BGG.exists_discreteSolution_norm_sub_le_ellipticProjection`, `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`, `Feec.BGG.HarmonicStability.exists_discreteSolution_norm_sub_le_rate`, `Feec.Models.Cube.WeakSymmetry.cubeFEM_ellipticProjection_rate_tr'` |
| §6.3 | "The hypotheses of the abstract framework hold for this method" ((6.5), Table 6.1) | Not checked; (5.4) and `S₀,ₕ` onto fail to be stated for bounded projections; no convergence result | For the elements of Table 6.1 with `S_h = πS` on the Freudenthal meshes of `(0, ½)³`: (5.4), uniform bounds, `grad` injective, `S₀,ₕ` onto, (6.5) well posed ⇔ (C2), energy-stable, `O(h)` convergent from the elliptic projection of the exact data for classical solutions of (6.2) whose states `σ, φ, u, M, ρ` and time derivatives are `C²` up to `∂Q` with vanishing tangential traces, with `L²` multiplier, and convergent without rate for every datum in `D(L)` (data of the scheme converging at `t = 0`); no hypothesis. The rate `h^{min(s,1)}` for relative-class `Hˢ` states (with `L²` multiplier and pairing bounds on `M`), and `O(h)` from data in `D(L³)` (with multiplier and `S¹u` bounds along the orbit) | `Feec.Models.Cube.WeakSymmetry.cubeWave_S0_surjective`, `Feec.Models.Cube.WeakSymmetry.cubeWave_exists_iff_compatible_u`, `Feec.BGG.DiscreteSolution.sqrt_energy_le`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr'`, `Feec.Models.Cube.WeakSymmetry.cubeWave_converges`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_cube`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_tr_cube`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_tr_nonvacuous_cube`, `Feec.EinsteinBianchi.BoundedConvergence.tendsto_of_mem_wave_domain`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_sobolev_cube`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_of_mem_domain_cube` |
| Prop 6.1 | Solutions of (6.1) and (6.2) correspond, with `λ := (S*)⁻¹d*u ∈ W¹` and a prescribed `λ₀` | `d*u ∈ range S*` fails in general; on the cube `B = (d, −S)` has non-closed range, so `λ ∈ W¹` is not available | Every solution of (6.1) has a unique multiplier `Λ(t) ∈ W̌¹ = closure J(W¹)` (no `λ₀`, `M` arbitrary), `W¹`-valued under closed range or extra regularity; on the cube `W̌¹` carries the norm `‖div λ‖_{H⁻¹} + ‖λ‖_{H⁻¹}` and is a proper completion | `Feec.BGG.WaveData.Solution.exists_multiplierSolution`, `Feec.BGG.WaveData.Solution.exists_multiplierSolution_of_dense`, `Feec.EinsteinBianchi.WaveFEM.exists_multiplierSolution`, `Feec.EinsteinBianchi.WaveFEM.negNorm_le_tripleNorm`, `Feec.EinsteinBianchi.WaveFEM.not_isClosed_range_B` |
| Prop 6.2 | (6.3) has a unique solution for every initial datum with `(σ₀, φ₀) ∈ Γ_h` | False | Solvable ⇔ (C1)–(C3), uniquely; for dynamic data `(σ₀, u₀, M₀, ρ₀)` ⇔ `(u₀, dψ) = 0` for `ψ ∈ ker S₀,h`, with `φ_h(0)` forced; projected data give a solution and the error bound | `Feec.BGG.exists_discreteSolution_iff`, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, `Feec.BGG.exists_discreteSolution_unique`, `Feec.BGG.exists_discreteSolution_norm_sub_le`, `Feec.Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution`, `Feec.Counterexamples.ConstrainedEvolution.not_projected_compatible_phi` |
| Ch. 6 | The weak-symmetry method with the §6.3 conditions propagates TSD | Fails on every bounded domain | Propagates TSD on `ℝ³`, on `𝕋³`, and on `(0, ½)³` with mirror conditions: unique solution, `σ ≡ 0`, `u` TSD, `M ≡ 0`, `B` TSD and symmetric; the mirror semi-discrete scheme on cube meshes is well posed and converges to the TSD solution from every TSD datum in `D(L²)` (`σₕ, Mₕ → 0`, `Bₕ` asymptotically symmetric; with no regularity from every point of the constraint; `O(h)` for every TSD datum in `D(L³)`, `O(hˢ)` for TSD data in `H^{2+s}`); with the §6.3 conditions (6.5) converges to the solution from the TSD datum, which leaves TSD, and its discrete fields leave TSD | `Feec.Models.Cube.MirrorBGG.propagatesQ`, `Feec.Models.Cube.MirrorBGG.existsUnique_memQ`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_exists_unique`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_of_mem_tsd`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`, `Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`, `Feec.Models.Euclidean.BGG.tsd_existsUnique`, `Feec.Models.Torus.BGG.tsd_existsUnique`, `Feec.Counterexamples.BoundedBGG.bggComplex_verdict` |
| Ch. 7 | "Other matrices are inverted with MINRES" | The Crank–Nicolson matrix is not symmetric | `J(M + sK)` is symmetric (for any number of blocks), nonsingular, indefinite, and its system is solved exactly by the CN update (assembled from Gram, `grad`, `curl` matrices); the Schur complement of block elimination is SPD | `Feec.TimeStepping.isSymm_diagonal_mul_add_smul`, `Feec.TimeStepping.mulVec_diagonal_mul_iff`, `Feec.TimeStepping.not_isSymm_blockMass_add_smul`, `Feec.TimeStepping.isSymm_isUnit_indefinite_blockSign_mul`, `Feec.TimeStepping.existsUnique_blockSign_mul_mulVec`, `Feec.TimeStepping.blockSign_mul_mulVec_iff_fullCNStep`, `Feec.TimeStepping.blockMass_add_smul_mulVec_eq_iff_schur`, `Feec.TimeStepping.posDef_schurComplement` |
| Ch. 7 (as run) | The plane-wave runs with boundary data from the exact solution preserve the constraints | Inhomogeneous boundary data are outside every homogeneous statement; not every TSD datum propagates with them | With a lifting `G`, `U' = L_max U + F`, `U − G ∈ D(L)` is uniquely solvable (skew-adjoint `L`) with energy bounds; on every bounded `Ω` the restriction `R` of a whole-space TSD solution (the plane wave) is the unique solution with its data and stays TSD, and from `U₀` it is `R + e^{tL}(U₀ − R(0))`, TSD iff the homogeneous part is (e.g. `U₀ − R(0) ∈ K*`); the fully discrete CN scheme on the three-row Whitney spaces of the cube is well posed for every `Δt`, with every `fem4gr` monitor bounded by the comparison residual, the initial error and the summed consistency errors, and the error and the five monitors `O(h + Δt²)` for smooth (TSD) solutions, the plane-wave run included, on `(0, ½)³` and dilated to the unit cube; on `𝕋³` the CN iterates conserve energy and stay TSD, with phase `2 arctan(sω) ≠ 2sω`; in the FEEC theorem, the solution is the lifting plus the mild solution with the forcing `F − G' + L_max G`, the lifted fully discrete iterates have the lifting error plus the forced error for every time scheme, and the `fem4gr` iterates are the interpolant plus forced Crank–Nicolson iterates of the scheme compressed to `V̊ₕ` (identification of the compression with the crown's discrete operator open; no forced rate) | `Feec.Evolution.IsBoundarySolution.eq_add_mild`, `Feec.Instances.Lifting.lifted`, `Feec.Instances.Lifting.whitney_cn_eq_lifted`, `Feec.TimeStepping.exists_eq_add_forcedIter_of_isDirichletCNStep`, `Feec.Evolution.isBoundarySolution_iff`, `Feec.Evolution.existsUnique_isBoundarySolution`, `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.restrict_unique`, `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.eq_add_waveGroup`, `Feec.Models.Cube.Inhomogeneous.WholeSpaceTSD.mem_iff`, `Feec.Models.Cube.Inhomogeneous.whitney_existsUnique_cnStep3`, `Feec.Models.Cube.Inhomogeneous.whitney_norm_residuals_le`, `Feec.Models.Cube.Inhomogeneous.whitney_cn_error_le`, `Feec.Models.Cube.Inhomogeneous.whitney_cn_monitors_le`, `Feec.Numerics.PlaneWaveCube.planeWave_cn_error_le`, `Feec.Numerics.PlaneWaveCube.unit_planeWave_cn_error_le`, `Feec.Numerics.PlaneWaveCube.exists_not_propagates`, `Feec.Numerics.PlaneWaveCube.cnTorusPlaneWave_props`, `Feec.Numerics.PlaneWaveCube.amp_eq_exp_phase` |

Limits of the repairs. Props 4.17, 4.19 and the Ch. 6 claim are repaired on domains without
boundary and on axis-parallel cubes (Prop 4.17 also on boxes) only: on a curved bounded domain no boundary condition is
proved to propagate non-stationary TSD data (the mirror conditions do not form a complex there),
and the Ch. 6 system with mirror conditions is proved only on `(0, ½)³`, since it is not
dilation-invariant. The mirror conditions of Prop 4.17 are characterized on every open cube by
Green's formulas against `C¹` test functions (weak trace conditions); reading them as pointwise
traces `σ·n = 0`, `E_{nτ} = E_{τn} = 0`, `B_{ττ} = 0` is an interpretation, since traces of `L²`
fields are not formalized, and Prop 4.19 (`MirrorSym`, whose first operator is second order) is
not characterized this way. On cubes other than `(0, ½)³` the operators of (4.16) are dilation
conjugates, not identified with the weak Hessian and curl. The §4.10 repair is at the level of polynomial shape functions, without
a mesh or cochain projections. The §6.3 finite element facts that Prop 6.2 and the Ch. 6
convergence theorem take as hypotheses (`S₀,h` onto, `grad` injective on `P₂Λ⁰ ⊗ V`, the
elliptic projection and its rate) are proved for Table 6.1 on the Freudenthal meshes of
`(0, ½)³`, with `S_h = πS` for smoothed projections `π`, with no hypothesis
(`Feec.EinsteinBianchi.WaveFEM.waveFEM_cube`; the regular decomposition is
`Feec.Models.Cube.WeakSymmetry.curlPotential`). The Ch. 5 and Ch. 6 rates need solutions `C²` up
to `∂Q` (restrictions of `C²` fields on `ℝ³`) with vanishing tangential traces, `M` and `ρ`
included (that the condition on `M`, `ρ` is needed, by an `h^{1/2}` lower bound, is not
formalized); without regularity (6.5) converges, without rate, for every datum in `D(L)`. For
relative-class Sobolev states the rate is `h^{min(s,1)}`
(`Feec.Models.Cube.WeakSymmetry.cubeWave_rate_sobolev_cube`), with an `L²`-bounded multiplier and
pairing bounds on `M` as hypotheses. From data in `D(L³)` the `O(h)` rate
(`Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_of_mem_domain_cube`) still assumes bounds on the
multipliers and `S¹u ∈ H¹` along the orbit, and `M(U₀) ∈ H¹` and `H¹` magnetic rows of the
stationary part `P_{N(L)} U₀` on the datum: no `D(Lᵏ)` gives the multiplier bound (argued in
`Feec.Physics.EinsteinBianchi.WaveFEMRegularity`, not formalized), and `D(L^∞)` does not control the tangential traces of `ρ`
(`Feec.EinsteinBianchi.WaveFEM.exists_memDomainPow_compρL_not_mem`). With mirror conditions the scheme
(6.5) with parity-smoothed projections converges to the TSD solution
(`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`, data in `D(L²)`; with no regularity, from
every point of the constraint, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_of_mem_tsd`),
with no hypothesis at
rate `O(h)` for TSD data in `D(L³)` and `O(hˢ)` for TSD data in `H^{2+s}`
(`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`,
`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`; whether less than
`D(L³)` suffices for `O(h)` is not shown), and the scheme with the canonical coupling `S_h = Π'S` of
`Feec.Models.Cube.MirrorWeakSymmetryFEM` is not analysed. For Ch. 7, which matrix
the thesis applies MINRES to is undetermined; both readings are treated. The Ch. 7 runs with
inhomogeneous data are covered through a lifting, the continuous problem on every bounded domain
and the discrete scheme on the Freudenthal meshes of `(0, ½)³`, with error and monitors
`O(h + Δt²)` for smooth solutions and `V̊ₕ ≠ 0` (`Feec.Models.Cube.Inhomogeneous.whitney_cn_error_le`,
`Feec.Models.Cube.Inhomogeneous.whitneyInterior3_ne_bot`), transported to the unit cube of
`fem4gr` by dilation (`Feec.Numerics.PlaneWaveCube.unit_planeWave_cn_error_le`; the dilated Whitney
spaces are not identified with those assembled on the unit-cube mesh); the discrete-divergence
monitor and data of finite Sobolev regularity are not covered. The §3.4 repair is
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
| Approximation of Hilbert complexes: subcomplexes, bounded cochain projections, discrete Poincaré and Hodge decomposition, harmonic gap, cohomology isomorphism `Hⁱ(H) ≅ Hⁱ(Vₕ)`; bounded cochain projections exist iff discrete stability holds ([AFW2010], Thms 3.6, 3.7) | covered | `HilbertComplex.Approximation.{Subcomplex,CochainProjection,DiscreteHodge,DiscreteCohomology,MixedError,CochainProjectionExistence}`, `Feec.HilbertComplex.Subcomplex.exists_cochainProjection`, `Feec.HilbertComplex.SubcomplexFamily.exists_isGraphBounded_iff`, `Feec.HilbertComplex.Subcomplex.CochainProjection.existsUnique_mixed`, `Feec.HilbertComplex.Subcomplex.CochainProjection.cohomologyEquiv`, eventually for every conforming family (`Feec.HilbertComplex.ConformingFamily.eventually_bijective_cohomologyMap`) |
| Quasi-optimal error estimate of the mixed method ([AFW2010], Thm 3.9) | covered | `Feec.HilbertComplex.Subcomplex.CochainProjection.norm_sub_le_infDist`, `Feec.HilbertComplex.Subcomplex.CochainProjection.norm_sub_le_infDist_domainSub` |
| Improved (duality) error estimates ([AFW2010], Thm 3.11) | partial | `Feec.HilbertComplex.Subcomplex.CochainProjection.norm_sub_u_le_improved`, with `η`, `δ`, `μ` defined (`improvedEta`, `improvedDelta`, `harmonicGap`) and bounded; that `η, δ → 0` (elliptic regularity) is shown for no concrete family |
| Eigenvalue problem: compact resolvent ⇒ eigenbasis | partial | `Feec.C0Group.eigenDense_of_compactResolvent`, and from compactness off the kernel, in degrees `0` and `1` only (`Feec.HilbertComplex.eigenDense_wave_fin3`); instances `Feec.Models.Cube.DeRham.eigenDense`, `Feec.Models.Cube.Ident.eigenDense_gradCurl_cube`, `Feec.Models.Box.eigenDense_gradCurl_box`, and for `H̊¹ → H̊(curl) → L²` on every domain star-shaped with respect to a ball, balls and bounded convex sets included (`Feec.Models.StarShaped.StarDomain.eigenDense_gradCurl`, `Feec.Models.StarShaped.eigenDense_gradCurl_convex`, `Feec.Models.StarShaped.eigenDense_gradCurl_ball`): degree `0` by Rellich on every bounded open set (`Feec.Models.BoundedDomain.hasCompactBall_minimal_grad`), degree `1` by Weber compactness transported from the cube along bi-Lipschitz radial maps (`Feec.Models.StarShaped.hasWeberCompactness_of_biLipschitz`); general bounded Lipschitz domains (a partition of unity over star-shaped pieces) and convergence of discrete eigenvalues: not |
| Evolution: Hodge wave equation, semi-discrete convergence and rate | covered | `HilbertComplex.HodgeWave`, `Approximation.{SemidiscreteWave,Convergence}`: `Feec.HodgeWave.norm_sub_le_of_semidiscrete` |
| Evolution: Lumer–Phillips, Hodge heat equation, its FEEC discretization and rate | covered | `Semigroup.LumerPhillips`, `HilbertComplex.HodgeHeat`: `LinearPMap.isMDissipative_iff_exists_contraction`, `Feec.HilbertComplex.existsUnique_classicalSolution_heat`, `Feec.HilbertComplex.norm_heatSemigroup_sub_starProjection_le`; `HilbertComplex.Approximation.HeatFEEC` (through the total complex, `HilbertComplex.Total`): `Feec.HilbertComplex.ConstrainedFEEC.heatFEEC` for every constrained FEEC discretization of a finite complex with closed range, `Feec.HilbertComplex.ConstrainedFEEC.rate_heat` (the static rate of [AFW2010], Thm 3.9 along the orbit), on the cube `Feec.Models.Cube.FEM.crown_heat_nonvacuous` |
| Model problems as corollaries of the FEEC theorem: acoustic waves, unsteady Stokes flow with slip boundary conditions, magnetostatics, Crank–Nicolson and θ-schemes for Maxwell and heat | covered | `Instances.Corollaries`: `Feec.Instances.Corollaries.acoustic` (windows in degrees `0, 1` and `n − 1, n`; on cubes, parallelepipeds and star-shaped domains `Feec.Instances.Corollaries.Cube.FEM.acoustic`, `Feec.Instances.Corollaries.Parallelepiped.acoustic`, `Feec.Instances.Corollaries.StarShaped.MeshFamily.acoustic`), `Feec.Instances.Corollaries.slipStokes` (`Feec.HilbertComplex.isReducing_hodgeLaplacian_ker_adjoint`: `ker 𝐝†` reduces `Δ`; on the cube, with a nonzero divergence-free velocity in degree `1`, `Feec.Instances.Corollaries.Cube.FEM.slipStokes`), `Feec.Instances.Corollaries.maxwell_fullyDiscrete`, `Feec.Instances.Corollaries.heat_fullyDiscrete`, `Feec.Instances.Corollaries.Cube.FEM.magnetostatic`, `Feec.Instances.Corollaries.mixed_converges` |
| Exterior algebra and polynomial forms: Koszul complex, `P_rΛᵏ`, `P_r⁻Λᵏ`, direct sums, dimensions, exactness | covered | `Algebra.{ExteriorFibre,Koszul,PolynomialForm,PolynomialFormDim,Wedge}`: `Feec.Koszul.finrank_polyForm`, `Feec.Koszul.finrank_polyFormMinus`, `Feec.ExteriorFibre.wedgeForm_assoc` |
| Smooth forms, pullback, integration over simplices, Stokes' theorem | covered | `FiniteElement.{SmoothForm,SimplexIntegral,Stokes,MeshDivergence}`: `Feec.FiniteElement.simplexIntegral_extDeriv`, `Feec.FiniteElement.setIntegral_image_simplexMap_divergence` |
| `L²` de Rham complex on a domain: `HΛ`, `H̊Λ`, duality | covered | `Feec.Domain.deRham`, `Feec.Domain.deRham_dual_minimalComplex_d`, `Feec.Domain.deRham_minimalComplex_univ_eq_maximalComplex_univ` (any open `Ω ⊆ ℝⁿ`) |
| Closed range, compactness and harmonic forms of the de Rham complex | partial | proved on `𝕋ⁿ` (`Models.Torus.DeRham`: `Feec.Models.Torus.DeRham.window_hasCompactProperty`, `H^k ≅ Λᵏ`) and for `HΛ` and `H̊Λ` of `Feec.Domain.DeRham` on `(0, ½)ⁿ`, every `n` and degree, through the identification with the parity model (`Models.Cube.DeRhamIdent*`: `Feec.Models.Cube.DeRhamIdent.HQmax_eq_compress`, `Feec.Models.Cube.DeRhamIdent.HQmin_eq_compress`, `Feec.Models.Cube.DeRhamIdent.Hmax_norm_le`, `Feec.Models.Cube.DeRhamIdent.Hmin_hasCompactProperty`, `Feec.Models.Cube.DeRhamIdent.Hmin_harmonic_top`, `Feec.Models.Cube.FEM.finrank_cohomology`), for `HΛ_J((0, ½)ⁿ)` with boundary conditions on the faces normal to `J` (`Models.Cube.DeRhamPartial*`: `Feec.Models.Cube.DeRhamIdent.Hpart_norm_le`, `Feec.Models.Cube.DeRhamIdent.Hpart_hasCompactProperty`, `Feec.Models.Cube.DeRhamIdent.finrank_Hpart_cohomology`), and on every parallelepiped `A · (0, ½)ⁿ + b` by affine transport (`Feec.Models.Parallelepiped.hasCompactProperty`, `Feec.Models.Parallelepiped.finrank_harmonic`); on other bounded domains only Rellich for `H̊¹` (every bounded open set, `Feec.Models.BoundedDomain.hasCompactBall_minimal_gradOp`) and Weber compactness of `H̊(curl) ∩ H(div)` for `3 × 3` matrix fields on domains star-shaped with respect to a ball (`Feec.Models.StarShaped.StarDomain.hasWeberCompactness`); the compactness property of the de Rham complex on other bounded domains, Gaffney off the cube and traces on Lipschitz domains: not |
| Simplicial meshes, shape regularity | covered | `Mesh.{Basic,Kuhn,Freudenthal,ShapeRegular}`: `Feec.Mesh.SimplicialMesh`, `Feec.Mesh.freudenthalMesh`, `Feec.Mesh.IsShapeRegular` |
| Degrees of freedom of `P_rΛᵏ(T)`, `P_r⁻Λᵏ(T)`: unisolvence, trace determination, commuting interpolants | covered | `FiniteElement.{Dof,LocalSpace,LocalDof}`: `Feec.FiniteElement.isUnisolvent_localDof`, `Feec.FiniteElement.isUnisolvent_localDofMinus`, `Feec.FiniteElement.polyInterp_extDeriv`, `Feec.FiniteElement.polyMinusInterp_extDeriv` |
| Global finite element spaces, conformity | covered | `FiniteElement.{Assembly,Conformity,PolyElement,PolyComplex,PolyElementMixed,TensorElement}`: assembly and conformity for any element family (`Feec.FiniteElement.LocalElement`, `Feec.FiniteElement.pieceL2_mem_maximal_domain`), instantiated for Whitney forms and for every admissible sequence of `P_rΛᵏ`/`P_r⁻Λᵏ` families of any order (`Feec.FiniteElement.polyElement`, moment DOFs on lexicographically ordered faces), with dimensions and the subcomplexes of `HΛ(Ω)` and `H̊Λ(Ω)` (`Feec.FiniteElement.PolySeq.subcomplex`, `Feec.FiniteElement.PolySeq.subcomplexMin`, `Feec.FiniteElement.PolySeq.freudenthalSubcomplexMin`), nonzero interior spaces on Freudenthal meshes (`Feec.FiniteElement.PolySeq.finrank_V₀_freudenthalMesh_pos_of_two_le`), vector-valued spaces `Vₕ ⊗ ℝᵐ` (`Feec.FiniteElement.LocalElement.tensorSubcomplexMin`); spaces with boundary DOFs on part of the boundary (`Feec.FiniteElement.LocalElement.globalSpacePartial`) are conforming in `HΛ_J` on the cube (`Feec.Models.Cube.FEM.glue_mem_dPart`) and give nonzero subcomplexes for every `J` (`Feec.Models.Cube.FEM.polyPartial`, `Feec.Models.Cube.FEM.lagrangeP2_polyPartial_V_ne_bot`); Whitney and `P_rΛ`/`P_r⁻Λ` spaces are affine invariant (`Feec.Models.Parallelepiped.isAffineNatural_poly`) |
| Whitney forms and the lowest-order complex | covered | `FiniteElement.{Whitney,WhitneyComplex}`: `Feec.FiniteElement.whitneySubcomplex`, `Feec.FiniteElement.whitneySubcomplexMin`, `Feec.FiniteElement.finrank_whitney_globalSpace`; the Whitney complex is the trimmed complex `P₁⁻Λ` on every mesh (`Feec.FiniteElement.whitneyElement_equivalent_trimmed`, `Feec.FiniteElement.whitneySubcomplex_eq_trimmed`, `Feec.FiniteElement.whitneySubcomplexMin_eq_trimmed`, through `Feec.FiniteElement.LocalElement.Equivalent.subcomplex_eq`) |
| The periodic table of simplicial elements | covered | `FiniteElement.PolyComplex`: every admissible sequence ending in `P_sΛⁿ` (`Feec.FiniteElement.PolySeq.ofKinds`, `Feec.FiniteElement.PolySeq.ofKinds_space_top`), the trimmed and full sequences (`Feec.FiniteElement.PolySeq.trimmed_eq_ofKinds`, `Feec.FiniteElement.PolySeq.full_space`), `P_r⁻Λ⁰ = P_rΛ⁰`, `P_r⁻Λⁿ = P_{r-1}Λⁿ` (`Feec.FiniteElement.polyMinusSpace_zero`, `Feec.FiniteElement.polyMinusSpace_top`), closed-form dimensions of Lagrange, Nédélec (both kinds), Raviart–Thomas and BDM in `ℝ²`, `ℝ³` (`Feec.FiniteElement.finrank_polyMinusSpace_three_one`, `Feec.FiniteElement.finrank_polySpace_three_two`, `Feec.FiniteElement.finrank_polyMinusSpace_two_one`) and over every field (`Feec.Koszul.finrank_polyFormMinus_three_one`, `Feec.Koszul.finrank_polyForm_three_two`); over every field of characteristic `0`, the polynomial complex of every admissible sequence is a resolution of the constants with the dimensions of the degrees of freedom (`Feec.FiniteElement.PolySeq.exists_extDeriv_eq`, `Feec.FiniteElement.PolySeq.finrank_form_eq_sum`, `Feec.Instances.Corollaries.Cube.FEM.feec_polyComplex`); the tensor-product cubical family `Q_r⁻Λᵏ` of any multidegree, with moment DOFs, unisolvence and commuting interpolants on the cube (`Feec.Koszul.cubeFormMinus`, `Feec.FiniteElement.Cube.isUnisolvent_cubeDof`, `Feec.FiniteElement.Cube.cubeFieldInterp_extDeriv`), and on uniform cubical meshes of `(0, L)ⁿ` with the same number `N` of cells in every direction (the Freudenthal refinement used for conformity is isotropic) the conforming subcomplex and the `O(hʳ)` sup-norm interpolation error (`Feec.FiniteElement.Cube.cubeSubcomplex`, `Feec.FiniteElement.Cube.exists_norm_sub_cubeFieldGlobalInterp_le`), with smoothed commuting maps (`Feec.FiniteElement.Cube.cubeSmoothedCommutingMap`) and, on `(0, ½)ⁿ`, a conforming family of `HΛ` for every multidegree `b ≥ 1` (`Feec.Models.Cube.FEM.qMinusFamily`); the serendipity forms `S_rΛᵏ` of the cube with the subcomplex, inclusion and degree properties, stability under traces, and `S_rΛ⁰` the serendipity space (`Feec.Koszul.serendipityForm`, `Feec.Koszul.extDeriv_mem_serendipityForm`, `Feec.Koszul.serendipityForm_mono`, `Feec.Koszul.serendipityForm_le_superlinForm`, `Feec.Koszul.cubeTrace_mem_serendipityForm`, `Feec.Koszul.serendipityForm_zero`), its dimension `dim S_rΛᵏ = dim M_rΛᵏ` through the exactness of the Koszul complex at bounded superlinear degree (`Feec.Koszul.finrank_serendipityForm`, `Feec.Koszul.mem_map_koszul_highForm`); the cubical family with vanishing boundary DOFs (`H̊Λ`), the traces of `S_rΛᵏ` as the serendipity spaces of the faces, the degrees of freedom, unisolvence and meshes of `S_rΛᵏ`, trimmed serendipity, and the count `2ⁿ⁻¹`: not |
| Bramble–Hilbert, interpolation error | partial | `FiniteElement.{BrambleHilbert,InterpolationError,WhitneyInterpolation,PolyInterpolation}`: `Feec.FiniteElement.norm_iteratedFDeriv_sub_taylorPoly_le`, `Feec.FiniteElement.norm_sub_transportInterp_le_of_isShapeRegular`; for Whitney forms the global `L²` error with explicit constants (`Feec.FiniteElement.norm_formL2_sub_glue_le_of_isShapeRegular`); for `P_rΛᵏ`, `P_r⁻Λᵏ` of every order the local estimates `sup_T ‖w − Π_T w‖ ≤ C h^{s+1} sup_T ‖D^{s+1}w‖` (`Feec.FiniteElement.exists_norm_sub_polyInterp_le`, `Feec.FiniteElement.exists_norm_sub_polyMinusInterp_le`), their `L²(T)` and graph-norm versions and the kernel lemma; on the cube the global error of order `h^{s+1}` (`Feec.Models.Cube.FEM.exists_mem_poly_le`), and for Sobolev data `dist(y, Vₕ) ≤ C h^{min(s,1)} ‖y‖_{Hˢ}` in `HΛ`, `HΛ_J` and `H̊Λ` (`Feec.Models.Cube.FEM.infDist_poly_le_sobolevQ`, `Feec.Models.Cube.FEM.infDist_polyPartial_le_sobolevPar`); the `L²` Bramble–Hilbert lemma `∫_K ‖f − Q f‖² ≲ ∫_K ‖D^{k+1} f‖²` for averaged Taylor polynomials in every order and dimension, the Sobolev embedding for `2(k + 1) > n`, and the `L²` interpolation errors `‖w − Π_T w‖_{L²(T)} ≲ h^{s+1} ‖D^{s+1} w‖_{L²(T)}` of `P_rΛᵏ`, `P_r⁻Λᵏ`, for smooth functions (`Feec.FiniteElement.lintegral_sub_avgTaylorPoly_sq_le`, `Feec.FiniteElement.enorm_sub_avgTaylorPoly_le_L2`, `Feec.FiniteElement.exists_formL2Sq_sub_polyInterp_le_L2`, `Feec.FiniteElement.exists_formL2Sq_sub_polyMinusInterp_le_L2`); on the cube, in every dimension, `dist(y, Vₕ) ≤ C h^{min(s, r_eff)} ‖y‖_{Hˢ}` (`Feec.Models.Cube.FEM.infDist_poly_le_sobolevQ_high`, `Feec.Models.Cube.FEM.infDist_polyPartial_le_sobolevPar_high`), through the interpolation error with lower-order terms `‖w − Π_h w‖ ≲ h^{r_eff} Σ_{i ≤ ⌊n/2⌋+1} hⁱ ‖D^{r_eff+i} w‖` (`Feec.Models.Cube.FEM.norm_formL2_sub_glue_globalInterp_le_sum`, from the Sobolev embedding with lower-order terms `Feec.FiniteElement.enorm_le_L2`) applied to the Fourier truncations; Sobolev-space versions off the cube (which need a quasi-interpolant): not |
| Smoothed (bounded commuting) projections | partial | `FiniteElement.{SmoothedProjection,SmoothedInterp,SmoothingBasic,PolySmoothingBasic}`, `Domain.StarShapedSmoothing`, `Models.StarShaped.{Smoothing,PolySmoothing}`, `Models.Cube.{SmoothingEstimates,PolySmoothingEstimates}`: `Feec.HilbertComplex.Subcomplex.CommutingMap.toCochainProjection`, `Feec.FiniteElement.LocalElement.smoothedCommutingMap`; the estimates (uniform `L²` bound, `‖v − Qv‖ ≤ ½‖v‖` on `Vₕ`) are proved on the Freudenthal meshes of `(0, ½)ⁿ`, both boundary-condition families, for the Whitney complexes (`Feec.Models.Cube.FEM.smoothingEstimates_pMax`, `Feec.Models.Cube.FEM.smoothingEstimatesMin_pMin`) and for every admissible sequence of higher-order families, for all small dilation parameters (`Feec.Models.Cube.FEM.polySmoothingEstimates_pMax`, `Feec.Models.Cube.FEM.polySmoothingEstimatesMin_pMin`), one smoother serving finitely many families (`Feec.Models.Cube.FEM.exists_common_gamma`), and for the cubical elements `Q_b⁻Λ` of the cubical meshes of `(0, ½)ⁿ`, `HΛ` only (`Feec.Models.Cube.FEM.qMinusSmoothingEstimates_pMax`); the simplicial cube estimates are instances of the star-shaped ones below (`Feec.Models.Cube.FEM.meshData`, `Feec.Models.Cube.FEM.exists_gamma₀`, `Feec.Models.Cube.FEM.Poly.exists_gamma₀`); conforming families of the smoothed projections (`Feec.HilbertComplex.ConformingFamily.ofSmoothing`, `Feec.Models.Cube.FEM.whitneyFamily`, `Feec.Models.Cube.FEM.polyFamily`, `Feec.Models.Cube.FEM.qMinusFamily`) and their `H¹` approximation `‖y − π y‖ ≤ C h ‖∇y‖` (`Feec.Models.Cube.FEM.PolySmoothingEstimatesMin.norm_sub_proj_le_grad`); parity smoothers without dilation for every boundary class `J`, every admissible sequence (`Feec.Models.Cube.FEM.exists_uniform_cochainProjection_part`), with rate `h^{s+1}` for smooth forms (`Feec.Models.Cube.FEM.ParitySmoothingEstimates.norm_sub_proj_le_smooth`); on parallelepipeds by affine transport (`Feec.HilbertComplex.IsChainIso.comapFamily`, `Feec.Models.Parallelepiped.whitneyFamily`, `Feec.Models.Parallelepiped.polyFamily`); on quasi-uniform shape-regular meshes of domains star-shaped with respect to a ball, Whitney forms, both boundary conditions (`Feec.Models.StarShaped.exists_uniform_cochainProjection`, `Feec.Models.StarShaped.exists_uniform_cochainProjectionMin`), and every admissible sequence of higher-order families (`Feec.Models.StarShaped.exists_uniform_polyCochainProjection`, `Feec.Models.StarShaped.exists_uniform_polyCochainProjectionMin`); domains not star-shaped with respect to a ball: not |
| Convergence of the finite element method | partial | with no hypothesis on the Freudenthal meshes of `Q = (0, ½)ⁿ`, lowest-order Whitney forms, `HΛ(Q)` and `H̊Λ(Q)` (`Models.Cube.FiniteElementConvergence`): the static FEEC theorem for the conforming families `Feec.Models.Cube.FEM.whitneyFamily`, `Feec.Models.Cube.FEM.whitneyFamilyMin` (`Feec.HilbertComplex.ConformingFamily.staticFEEC`: uniform discrete Poincaré, stability, quasi-optimality, harmonic gap, cohomology), `O(h)` rates for `C²` solutions from their Jackson estimates (`Feec.Models.Cube.FEM.whitneyJackson`, `Feec.HilbertComplex.ConformingFamily.StaticVerdict.rate`), semi-discrete Hodge wave convergence and `O(h)` rates on every window (`Feec.Models.Cube.FEM.exists_tendstoUniformlyOn_window_whitney`, `Feec.Models.Cube.FEM.exists_tendstoUniformlyOn_windowMin_whitney`, `Feec.Models.Cube.FEM.norm_sub_le_meshSize_window_smooth`); for other smoothing parameters, the conforming families `Feec.Models.Cube.FEM.SmoothingEstimates.family`; the same for every admissible sequence of higher-order families (`Models.Cube.{PolyFiniteElementConvergence,PolyRate,TangentialRate}`): the static FEEC theorem for `Feec.Models.Cube.FEM.polyFamily`, rates `h^{s+1}` for `C^{s+2}` solutions, with degreewise orders (`O(h²)` for the bottom row of Tables 5.1/6.1) (`Feec.Models.Cube.FEM.mixed_rate_poly`, `Feec.Models.Cube.FEM.mixed_rate_polyMin`, `Feec.Models.Cube.FEM.mixed_rate_lagrangeP2Min`) and the semi-discrete Hodge wave equation (`Feec.Models.Cube.FEM.exists_tendstoUniformlyOn_window_poly`, `Feec.Models.Cube.FEM.norm_sub_le_window_poly_smooth`); the cubical elements `Q_b⁻Λ` on the cubical meshes of `(0, ½)ⁿ`, `HΛ` only: the FEEC theorem for `Feec.Models.Cube.FEM.qMinusFamily`, with rates `h^{s+1}` for `IsCsForm s` data, `s + 1 ≤ min b` (`Feec.Models.Cube.FEM.qMinusJackson`, `Feec.Instances.Maxwell.cubeQMinus_maxwellFEEC`); also spectral Galerkin on `𝕋ⁿ` (`Feec.Models.Torus.DeRham.tendsto_bandGalerkin`); on every parallelepiped, both families and both boundary conditions, with no hypothesis (`Feec.Models.Parallelepiped.whitneyJackson`, `Feec.Models.Parallelepiped.mixed_rate_poly`, `Feec.Models.Parallelepiped.exists_tendstoUniformlyOn_window_poly`); on domains star-shaped with respect to a ball with quasi-uniform shape-regular meshes, Whitney forms, with the Poincaré inequality of the domain as the one hypothesis (`HasPoincare`, true on Lipschitz domains by [CostabelMcIntosh2010], absent from Mathlib; `Feec.Models.StarShaped.MeshFamily.whitneyJackson`, `Feec.HilbertComplex.ConformingFamily.rate`; wave convergence unconditional, `Feec.Models.StarShaped.MeshFamily.exists_tendstoUniformlyOn_window`), and the same for every admissible sequence of higher-order families with rates `h^{s+1}` (`Feec.Models.StarShaped.MeshFamily.mixed_rate_poly`, `Feec.Models.StarShaped.MeshFamily.exists_tendstoUniformlyOn_window_poly`), with no hypothesis on every parallelepiped for every quasi-uniform shape-regular mesh family of it (`Feec.Models.StarShaped.Parallelepiped.mixed_rate_poly_general`); for the mixed boundary conditions `HΛ_J` and Sobolev data on the cube, rates `h^{min(s,1)}` for every admissible sequence (`Feec.Models.Cube.FEM.mixed_rate_sobolevQ`, `Feec.Models.Cube.FEM.mixed_rate_sobolevPar`, `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_sub_le_window_sobolevQ`) and `h^{min(s, r_eff)}` in every dimension (`Feec.Models.Cube.FEM.mixed_rate_sobolevQ_high`, `Feec.Models.Cube.FEM.mixed_rate_sobolevPar_high`, `Feec.Models.Cube.FEM.exists_norm_sub_le_window_sobolevQ_high`); not: Sobolev rates off the cube, domains not star-shaped with respect to a ball, the Poincaré inequality on star-shaped domains |
| Other complexes: elasticity, Hessian, div-div, BGG | partial | `Feec.Domain.elasticityComplex`, `Feec.Domain.hessianComplex`, `Feec.Domain.divDivComplex` on open `Ω ⊆ ℝ³` with duality; abstract BGG (`HilbertComplex.BGG`): for two complexes of any length on any shape over any ring linked by `S` with `d S = −S d̃`, the derived complex obtained by eliminating the pairs matched by `S` has the cohomology of the twisted complex (`Feec.BGG.Data.derivedHomologyIso`), with the Arnold–Hu BGG complex on `ℤ` (`Feec.BGG.Data.bggHomologyIso`) and (5.1) as instances (`Feec.BGG.Data.Γ_eq_segment_Γ`), and analytically for bounded data (`HilbertComplex.BGG.Analytic`: the derived complex is a Hilbert complex, `Feec.BGG.BoundedData.derivedComplex`, with the quotient norm of `Γ / Δ` as for every subquotient of a complex of bounded operators, `Feec.HilbertComplex.Subquotient.toQuotEquiv`, [ArnoldHu2021] Thm 6, with the twisted cohomology under the eliminations, dimension at most that of the rows and closed range where the rows have finite-dimensional cohomology, `Feec.BGG.BoundedData.derivedComplexCohomologyEquiv`, `Feec.BGG.BoundedData.finrank_derivedComplex_cohomology_le`, `Feec.BGG.BoundedData.derivedComplex_closedRangeAt`; for Hilbert complexes `Feec.BGG.HilbertData.bggVerdict`); on smooth fields of `ℝ³` the Hessian, elasticity and div-div complexes are `Feec.BGG.Data.bgg` of vector-valued de Rham rows (`Feec.Domain.hessianBGGIso`, `Feec.Domain.elasticityBGGIso`, `Feec.Domain.divDivBGGIso`), and on `L²(Ω)`, every open `Ω ⊆ ℝ³`, their maximal BGG data satisfy the analytic verdict given the regular decompositions after `J` and finite-dimensional row cohomology (`Feec.Domain.hessianMaximalData_derivedVerdict`, `Feec.Domain.elasticityMaximalData_derivedVerdict`, `Feec.Domain.divDivMaximalData_derivedVerdict`); the regular decompositions follow from the `H¹`-regular decompositions of the rows (`Feec.Domain.hessianMaximalData_regularDecomposition`, `Feec.Domain.ConstCoeffBGG.maximalData_regularDecomposition`), which are proved on the cube `(0, ½)³` over `ℝ` (`Feec.Models.Cube.Sobolev.deRham_hasRegularDecomposition_Q`, Gaffney in the absolute class), and so is the finite-dimensional cohomology of the rows (`Feec.Domain.deRhamVec_finiteDimensional_cohomology`, `Feec.Models.Cube.finiteDimensional_cohomology_deRhamVec_Q`); both pass from `ℝ` to every `RCLike 𝕜` (`ℂ` in particular) through real and imaginary parts, the rows having real coefficients (`Feec.Domain.ConstCoeffComplex.HasRegularDecomposition.ofReal`, `Feec.Domain.ConstCoeffComplex.finiteDimensional_cohomology_ofReal`), so there the FEEC theorem for discrete Hessian, elasticity and div-div complexes has no hypothesis, over every `RCLike 𝕜` (`Feec.Models.Cube.hessianFEEC_Q`, `Feec.Models.Cube.elasticityFEEC_Q`, `Feec.Models.Cube.divDivFEEC_Q`), nor on every open parallelepiped and box, the affine preimages of the cube, both hypotheses being transported along the pullback of forms (`Feec.Domain.FormPullData.hasRegularDecomposition`, `Feec.Domain.FormPullData.finiteDimensional_cohomology`; `Feec.Models.Parallelepiped.hessianFEEC_affine`, `Feec.Models.Parallelepiped.elasticityFEEC_affine`, `Feec.Models.Parallelepiped.divDivFEEC_affine`, `Feec.Models.Parallelepiped.hessianFEEC_box`); no stacked conforming family of these diagrams is constructed on any domain, so these theorems quantify over one; in differential forms on the cube `(0, ½)ⁿ` (`HΛ(Q)` and `HΛ(Q) ⊗ ℝⁿ` linked by maps built from `dxₐ ∧ ·`: `Feec.FiniteElement.hessianFormData`, `Feec.FiniteElement.divDivFormData` and, on `(0, ½)³`, `Feec.FiniteElement.elasticityFormData`) the three BGG complexes have closed range in every degree and cohomology of dimension `n + 1`, `n + 1` (`n ≥ 1`), `6` in degree `0` and `0` in the other degrees (`Feec.Models.Cube.FormBGG.hessianBGG_Q`, `Feec.Models.Cube.FormBGG.divDivBGG_Q`, `Feec.Models.Cube.FormBGG.elasticityBGG_Q`), the degree-`0` cohomology being the affine functions, the fields `a + b x` and the rigid motions (`Feec.Models.Cube.FormBGG.hessianBGG_Q_homology_zero`, `Feec.Models.Cube.FormBGG.divDivBGG_Q_homology_zero`, `Feec.Models.Cube.FormBGG.elasticityBGG_Q_homology_zero`); the regular decompositions on non-affine domains (bi-Lipschitz images of the cube included), the identification of these `L²` spaces with `Feec.Domain.hessianComplex` and the others, and exactness on smooth fields: not; the BGG complex (4.16) with weak symmetries on `(0, ½)³` (`Feec.Models.Cube.WeakSymmetry.bggStability'`, `Feec.Models.Cube.WeakSymmetry.bggStability_curlPotentialConst`, with the regular decomposition proved, `Feec.Models.Cube.WeakSymmetry.curlPotential`), with mirror conditions modulo harmonic forms (`Feec.Models.Cube.MirrorWeakSymmetry.mirror_harmonicStability`), and its finite elements of Tables 5.1/6.1 on the Freudenthal meshes: (5.4), uniform bounds, Props 5.7–5.9(1), the static error estimate and the semi-discrete wave convergence with `O(h)` rates (`Feec.Models.Cube.WeakSymmetry.cubeFEM_compatible`, `Feec.EinsteinBianchi.StaticFEM.staticFEM_cube`, `Feec.EinsteinBianchi.WaveFEM.waveFEM_cube`, `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`), with rates `h^{min(s,1)}` for Sobolev data (`Feec.Models.Cube.WeakSymmetry.staticFEM_rate_sobolev_cube`, `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_sobolev_cube`) and, with mirror conditions, `O(h)` from `D(L³)` (`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`); closed range of these complexes on other bounded domains and their finite elements: not |
| Maxwell's equations | covered | `Physics.Maxwell.*`: `Feec.Maxwell.pecForms_three_gauss_propagates`, `Feec.Maxwell.Medium.exists_anisotropic`, `Feec.Maxwell.Medium.ohmic_existsUnique`, `Feec.Maxwell.Medium.ohmic_magnetic_gauss_propagates`; finite elements on the cube, parallelepipeds and star-shaped domains, PMC and PEC, Whitney forms and every admissible sequence, as instances of the FEEC theorem (`Feec.Instances.Maxwell.maxwellFEEC`; rates `O(h)`, `O(h^{s+1})` by `Feec.HilbertComplex.ConformingFamily.feec_rated`) |
| Sobolev spaces, traces, elliptic regularity, Lipschitz domains | partial | on `(0, ½)ⁿ` only: fractional Sobolev spaces `Hˢ(Q)` (restrictions from `𝕋ⁿ`) and the parity classes `Hˢ_J(Q)`, `H⁰ = L²`, `H¹` identified with the weak-derivative spaces (`Models.Cube.Sobolev`: `Feec.Models.Cube.Sobolev.mem_sobolevPar_one_iff`, `Feec.Models.Cube.Sobolev.qNorm_one_sq_equiv`); integer orders by weak derivatives (`Models.Cube.SobolevWeak`): `Hᵐ(Q)` has weak derivatives up to order `m` with the norm bound (`Feec.Models.Cube.Sobolev.hasWeakDerivs_of_mem_sobolevQ`), and `Hᵐ(𝕋ⁿ)` and the parity classes `Hᵐ_J(Q)` are characterized by weak derivatives, with equivalent norms (`Feec.Models.Cube.Sobolev.memSob_nat_iff`, `Feec.Models.Cube.Sobolev.mem_sobolevPar_add_one_iff`, `Feec.Models.Cube.Sobolev.mem_sobolevPar_two_iff`, `Feec.Models.Cube.Sobolev.parNorm_sq_le_weakHmNormSq`); Gaffney on the cube, `D(d) ∩ D(d*) = H¹` in the relative class (`Feec.Models.Cube.WeakSymmetry.gaffney_HQmin`, `Feec.Models.Cube.WeakSymmetry.mem_HQmin_of_sobolevPar_one`), `D(d) ∩ D(d*) ⊆ H¹` in the absolute class (`Feec.Models.Cube.Sobolev.memSob_one_of_mem_HQmax`) and the regular decompositions `HΛᵏ⁺¹(Q) = d HΛᵏ(Q) + H¹` (`Feec.Models.Cube.Sobolev.deRham_hasRegularDecomposition_Q`); off the cube, Rellich for `H̊¹` on bounded open sets and bi-Lipschitz pullbacks of `H̊(curl)` and `H(div)` (`Feec.Domain.BiLipschitz.pull1_mem_minimal_curl`, `Feec.Domain.BiLipschitz.piola_mem_maximal_divT`); restrictions to `Q` of forms with coefficients in `Hᵐ(ℝⁿ)` lie in `Hᵐ(Q)` with the norm bound (`Models.Cube.SobolevRestriction`: `Feec.Models.Cube.SobolevRestriction.exists_qNorm_le`). Not: the backward direction `HasWeakDerivs Q m u → u ∈ Hᵐ(Q)` for `m ≥ 2` without boundary condition (it needs an `Hᵐ` extension operator), traces, elliptic regularity, Lipschitz domains |

## The pre-refactor tree

The chapter-ordered tree (`Feec.Ch2`–`Feec.Ch7`, `Feec.Repair`, `Feec.Foundation`) and the
real-scalar layer that remained of it (`Feec.Legacy`, built on a short complex
`Feec.Legacy.HilbertComplex2` with concrete ℝ³ models of the torus, the box, the mirror cubes and
bounded domains) are gone. Every declaration of the old tree was re-derived in the general layers
or deleted as a helper, and `docs/migration/map.tsv` records where each one went
(`lake exe feec-mapcheck --strict` checks that every old declaration is covered and every new name
exists). Thesis-numbered names, `_unconditional` variants, strangler shims and deprecated
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
equation of every Hilbert complex (`Feec.HilbertComplex.heatSemigroup`). Bounded dissipative
perturbations of every dissipative FEEC discretization with a dense core keep its verdict
(`Feec.HilbertComplex.perturbFEEC`; damped waves and Ohmic loss on every conforming window,
`Feec.HilbertComplex.ConformingFamily.Verdict.perturbed`). Semi-discrete convergence holds for every datum in `W`, and in the
thesis's form for `ξ₀ ∈ D(L)`; the error bound of Thm 4.14 needs `C¹(V)` solutions, which exist
for `ξ₀ ∈ D(L²)`, and no rate is formalized for `D(L)` or `W` data.

Mathlib has no Sobolev spaces with traces. Meshes, finite element spaces and Whitney complexes are
built here (`Feec.Mesh`, `Feec.FiniteElement`), but abstract results still take concrete complexes
as instances of abstract structures, with their analytic facts on general domains (closed range,
the estimates behind bounded cochain projections, density, regular decompositions) as hypotheses;
on the cube `(0, ½)ⁿ` these facts are proved, and on parallelepipeds by affine transport. The concrete models are:
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
  compactness property, Poincaré constant `(2π)⁻¹` and the harmonic forms of both classes. It is
  identified with `H̊Λ((0, ½)ⁿ)` (relative class) and `HΛ((0, ½)ⁿ)` (absolute class) of
  `Feec.Domain.DeRham` by the parity extension, a scaled isometry intertwining `d`
  (`Feec.Models.Cube.DeRhamIdent`), so these facts hold for `HΛ` and `H̊Λ` themselves
  (`Feec.Models.Cube.DeRhamIdentPoincare`, `Feec.Models.Cube.DeRhamIdentFEM`). The same holds
  for the partial boundary conditions `HΛ_J((0, ½)ⁿ)` (vanishing tangential traces on the faces
  normal to `e_j`, `j ∈ J`; `Feec.Models.Cube.DeRhamPartial`, `Feec.Models.Cube.DeRhamPartialIdent`),
  with `Hᵏ ≅ ℝ` for `k = |J|` and `0` otherwise. Boxes with unequal sides are the compressions of
  anisotropic torus complexes along diagonal changes of variables (`Feec.Domain.DiagonalPullback`,
  `Feec.Models.Box`).
* Finite elements (`Feec.Mesh`, `Feec.FiniteElement`, `Feec.Models.Cube.FiniteElementMethod`):
  the Whitney complex on every conforming simplicial mesh is a subcomplex of `HΛ(Ω)` (of `H̊Λ(Ω)`
  with vanishing boundary DOFs, for strictly star-shaped `Ω`), and the smoothed interpolant
  `Π_h R` is a commuting map into it. On the Freudenthal meshes of `(0, ½)ⁿ` the three inputs
  of the finite element method are theorems: the estimates of [AFW2010] §5.5 that make
  `J⁻¹ Π_h R` a uniformly bounded cochain projection (`Feec.Models.Cube.SmoothingEstimates`, from
  the inverse estimates of `Feec.FiniteElement.InverseEstimate`), the Poincaré inequalities of
  `HΛ` and `H̊Λ` (`Feec.Models.Cube.DeRhamIdentFEM`) and the Whitney interpolation error
  (`Feec.FiniteElement.WhitneyInterpolation`; in the graph norm of `HΛ(Ω)`, `H̊Λ(Ω)` for any
  element family on any mesh of `Ω`, `Feec.FiniteElement.GlobalInterpolation`;
  `Feec.Models.Cube.WhitneyApprox`, with the density of smooth forms
  `Feec.FiniteElement.SmoothDensity`, `Feec.Models.Cube.WhitneyRate`). `Feec.Models.Cube.FiniteElementConvergence` states stability,
  quasi-optimality, `O(h)` rates and the semi-discrete Hodge wave equation with no hypothesis
  beyond the data and, for the rates, `C²` regularity of the solution; Maxwell (PMC and PEC) is
  `Feec.Instances.Maxwell.cubePMC`, `Feec.Instances.Maxwell.cubePEC`. The same holds for the
  higher-order families `P_rΛᵏ`,
  `P_r⁻Λᵏ` of every admissible sequence (`Feec.FiniteElement.PolyElement`,
  `Feec.Models.Cube.PolySmoothingEstimates`, `Feec.Models.Cube.PolyFiniteElementConvergence`,
  `Feec.Models.Cube.PolyRate`, `Feec.Models.Cube.TangentialRate`, with rates `h^{s+1}` for the
  polynomial order of `Feec.FiniteElement.PolyOrder`), and for
  the Einstein–Bianchi (BGG) pair of
  Tables 5.1/6.1 (vector-valued spaces, `S_h = πS` for smoothed projections of one smoother):
  (5.4), Props 5.7–5.9(1), the static estimate and the semi-discrete wave convergence
  (`Feec.Physics.EinsteinBianchi.StaticFEM`, `Feec.Physics.EinsteinBianchi.WaveFEM`), with no
  hypothesis: the regular decomposition `Feec.Models.Cube.WeakSymmetry.CurlPotential` is proved
  (`Feec.Models.Cube.RegularDecomposition`, `Feec.Physics.EinsteinBianchi.Unconditional`), and the
  rates hold for solutions `C²` up to `∂Q` with vanishing tangential traces
  (`Feec.Models.Cube.TangentialRate`, `Feec.Models.Cube.WeakSymmetryFEM`,
  `Feec.Models.Cube.WeakSymmetryWave`, `Feec.Models.Cube.WeakSymmetryTangentialRate`,
  `Feec.Physics.EinsteinBianchi.WaveFEMTangentialCube`); (6.5) converges without rate for every
  datum in `D(L)` (`Feec.Models.Cube.WeakSymmetryConvergence`,
  `Feec.Physics.EinsteinBianchi.BoundedConvergence`). For `HΛ_J(Q)` the partial-boundary finite
  element spaces are conforming (`Feec.Models.Cube.DeRhamPartialFEM`) and parity smoothers give
  uniformly bounded cochain projections onto them (`Feec.Models.Cube.ParitySmoother`,
  `Feec.Models.Cube.ParitySmoothingEstimates`). With mirror boundary conditions: the BGG elements,
  the well-posed scheme (6.5) (`Feec.Models.Cube.MirrorWeakSymmetryFEM`) and, with parity-smoothed
  projections, its convergence to the TSD solution (`Feec.Models.Cube.MirrorWeakSymmetryComplex`,
  `Feec.Models.Cube.MirrorWeakSymmetryConvergence`, `Feec.Models.Cube.MirrorWeakSymmetryTSD`).
  Sobolev data: `Feec.Models.Cube.Sobolev`, `Feec.Models.Cube.SobolevWeak`,
  `Feec.Models.Cube.SobolevRate`, `Feec.Models.Cube.SobolevRateHigh` (rates `h^{min(s, r_eff)}`,
  every dimension); for the BGG elements `Feec.Models.Cube.WeakSymmetrySobolevRate` and
  `Feec.Physics.EinsteinBianchi.WaveFEMRegularity`, with mirror conditions
  `Feec.Models.Cube.MirrorWaveRegularity`. Regular decompositions of `HΛ(Q)` and the FEEC theorem
  for the Hessian, elasticity and div-div diagrams on `Q`: `Feec.Models.Cube.MaximalRegularDecomposition`,
  `Feec.Models.Cube.BGGFEEC` (on general domains, `Feec.Domain.RegularDecomposition`; on
  parallelepipeds and boxes, `Feec.Models.Parallelepiped.BGGFEEC`). Other domains:
  parallelepipeds `A · (0, ½)ⁿ + b`, every box included, with the
  whole theory and no hypothesis (`Feec.Domain.FormPullback`,
  `Feec.Models.Parallelepiped.FiniteElement`), and domains star-shaped with respect to a ball with
  quasi-uniform shape-regular meshes, Whitney and higher-order families, with the Poincaré
  inequality as hypothesis (`Feec.FiniteElement.ShapeRegularInverse`,
  `Feec.FiniteElement.ShapeRegularSmoothing`, `Feec.Models.StarShaped.FiniteElement`,
  `Feec.Models.StarShaped.PolySmoothing`, `Feec.Models.StarShaped.PolyFiniteElement`; on
  parallelepipeds every quasi-uniform shape-regular mesh family, with no hypothesis,
  `Feec.Models.Parallelepiped.StarShaped`). Not built:
  domains not star-shaped with respect to a ball, the Poincaré inequality on star-shaped ones,
  mixed boundary conditions off the cube, Sobolev rates off the cube, discrete eigenvalue
  convergence.

The thesis states its Ch. 4 results with boundary conditions on a bounded `Ω` (§4.10, §6.3), so
the bounded-domain models are the faithful setting; `𝕋³` and `ℝ³` have no boundary and serve as
a contrast. For the boundary conditions printed in Prop 4.19, the hypotheses fail, and the
conclusion and the density fail on every ball (transported from the unit ball by affine maps,
`Feec.Models.BoundedDomain.SymDualGeneral`); other domains, and whether `K*` is nonzero there,
are not decided (on domains of revolution the sign of a boundary pairing decides, and it is not
formalized). On boxes with unequal sides `K*` is stationary, as on cubes
(`Feec.Models.Box.mem_invariantCore_tsd_iff`, `Feec.Counterexamples.BoxStationary.forward_iff_stationary_box`),
and with mirror conditions `K* = K` (`Feec.Models.Box.Mirror.invariantCore_eqBox`). On a general
bounded domain no non-stationary element of `K*` is known;
`Feec.Models.BoundedDomain.gradCurl_coreSub_spectral` reduces the question to the existence of a nonzero TSD
eigenfield of `curl* curl`, and `Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff` narrows
it to one with `curl u ∉ H̊(curl)` (eigenfields with `u, curl u ∈ H̊(curl)` vanish on every bounded
domain, by a Pohozaev identity; the expectation that `K*` is stationary when every boundary
component is a sphere is not formalized). Both need pure point spectrum; that is derived from a
compact resolvent (`Feec.C0Group.eigenDense_of_compactResolvent`) or from compactness in degrees
`0` and `1` (`Feec.HilbertComplex.eigenDense_wave_fin3`), and proved on `𝕋³`, on every open cube
and on every box (`Feec.Models.Cube.Ident.eigenDense_gradCurl_cube`,
`Feec.Models.Box.eigenDense_gradCurl_box`, by compression of the torus) and on every domain
star-shaped with respect to a ball, balls and bounded convex sets included
(`Feec.Models.StarShaped.StarDomain.eigenDense_gradCurl`: Rellich in degree `0`, Weber
compactness transported from the cube in degree `1`); on general bounded Lipschitz domains it is
open. On every ball the criterion therefore holds with no hypothesis: `K*` is stationary iff no
TSD eigenfield has `curl u ∉ H̊(curl)` (`Feec.Models.StarShaped.coreSub_le_stationary_ball_iff`).
On the unit ball no TSD eigenfield `C²` up to the boundary exists
(`Feec.Counterexamples.BallEigenfields.eq_zero_of_isEigenfield_of_contDiff_ball`: the boundary
values vanish, and so does the normal derivative, since the round sphere carries no
transverse–traceless tensors). Whether every TSD eigenfield is `C²` up to the boundary
(`Feec.Counterexamples.BallEigenfields.TSDEigenfieldRegularity`) is elliptic boundary regularity,
absent from Mathlib; on the ball this TSD form is equivalent to the absence of TSD eigenfields
(`Feec.Counterexamples.BallEigenfields.tsdEigenfieldRegularity_ball_iff`), so the genuine missing
input is the row-wise regularity of Maxwell eigenfields,
`Feec.Counterexamples.BallEigenfields.MaxwellEigenfieldRegularity`, under which `K*` is
stationary on the ball
(`Feec.Counterexamples.BallEigenDense.coreSub_le_stationary_ball3_of_maxwellRegularity`). For Ch. 6, `Γ ≅ H̊²(Q)`:
`(σ, φ) ↦ σ` maps `Γ` of the forms model `Feec.Models.Cube.WeakSymmetry.bggHilb` bijectively onto
the first domain of the matrix model `Feec.Models.BoundedDomain.bggComplex`, with `D₀` the Hessian
(`Feec.EinsteinBianchi.WaveFEM.gamma_equiv_hessMin`), and the rows map `H̊Λ¹(Q)³` onto
`H̊(curl, Q; ℝ³ˣ³)` intertwining `(S¹, d)` with `(skwL, curl)`, so that the forms complex is the
unitary transport of the matrix complex (`Feec.EinsteinBianchi.MatrixModel.mem_curlMin_domain_iff`,
`Feec.EinsteinBianchi.MatrixModel.skwL_rowsEquiv`, `Feec.EinsteinBianchi.MatrixModel.matrixComplex_eq_map`).
The bounded-domain failure therefore carries to (6.5): the scheme converges, with no hypothesis, to
the solution from the TSD datum `(0, 0, (0, β))`, which leaves TSD, and for large `N` the discrete
fields leave TSD (`Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`); the
`O(h)` rate does not apply to it (its magnetic datum has nonzero tangential traces,
`Feec.EinsteinBianchi.BoundedFailure.not_isRateClass_of_rho`). On the cube `B = (d, −S)` has dense,
non-closed range (`Feec.EinsteinBianchi.WaveFEM.denseRange_B`,
`Feec.EinsteinBianchi.WaveFEM.not_isClosed_range_B`), so the multiplier space `W̌¹` of (6.2) is a
genuine completion, with norm equivalent to `‖div λ‖_{H⁻¹} + ‖λ‖_{H⁻¹}`
(`Feec.EinsteinBianchi.WaveFEM.negNorm_le_tripleNorm`). Ch. 7 states no boundary conditions; its runs (read from `fem4gr`) prescribe `σ`, `E × n`
and `B · n` from the exact plane wave. These inhomogeneous data are formalized by a lifting
(`Feec.Evolution.BoundaryLifting`, `Feec.Models.Cube.Inhomogeneous`): the plane wave is the unique
solution with its own data and stays TSD on every bounded domain, a TSD perturbation of its
initial value does not (`Feec.Numerics.PlaneWaveCube.exists_not_propagates`), and the fully
discrete scheme on the Whitney spaces of the cube is well posed with its constraint monitors
bounded by the consistency error, which is `O(h + Δt²)` for smooth solutions
(`Feec.Models.Cube.Inhomogeneous.whitney_cn_error_le`,
`Feec.Models.Cube.Inhomogeneous.whitney_cn_monitors_le`), the plane-wave run included, also
dilated to the unit cube (`Feec.Numerics.PlaneWaveCube.unit_planeWave_cn_error_le`). Not formalized
for Ch. 7: the discrete-divergence monitor on Whitney spaces, `B · n` (a remark: it is not a
condition of the continuous problem), the identification of the dilated Whitney spaces with those
assembled on the unit-cube mesh, data of finite Sobolev regularity, and periodic Whitney spaces.

Pseudo-Riemannian geometry is done in components, at the jet level and for fields on a global
chart of `ℝⁿ` (metrics of any signature, Christoffel symbols of a `C³` metric, the second Bianchi
identity and its contractions, `Feec.Geometry.Bianchi`). The nonlinear Einstein–Bianchi system
(§3.4) is derived in an orthonormal frame for every vacuum metric on `ℝ⁴`
(`Feec.Physics.EinsteinBianchi.Nonlinear`), with the frame and its connection coefficients as
given data; not formalized: existence of solutions or of the `3 + 1` frame (the Frobenius
theorem enters only through `Feec.EinsteinBianchi.extrinsic_symm_iff_bracket`), local versions
on an open set (so charts such as Schwarzschild's are not covered as stated), the non-vacuum
system of [ACBY1997], and a vacuum example with `E, B ≠ 0`. Out of scope: the numerical results
of Ch. 7 beyond the plane-wave runs (error tables and convergence rates). All cited works are collected in [`references.bib`](references.bib).
