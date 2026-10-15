# Overview

Module map, corrections to the thesis, and scope of the formalization.

## Contents

| Module | Thesis |
|---|---|
| `Feec.Foundation.{Operators, Evolution, Complex, BGG, Tensor}` | Shared definitions: unbounded operators, strong solutions and existence hypotheses, Hilbert complexes and the Hodge wave operator, BGG data, component tensors (re-exported by `Feec.Foundation`) |
| `Feec.Ch2.Curvature` | §2.3–2.4: Riemann symmetries, Prop 2.1, Ricci and Einstein tensors |
| `Feec.Ch2.Linearized` | §2.4–2.8: Thm 2.3, Props 2.4–2.6, TT gauge, plane waves, geodesic deviation |
| `Feec.Ch3.Bivector` | §3.1–3.3: Hodge duality, Props 3.1–3.3, Weyl block structure |
| `Feec.Ch3.EB` | §3.3–3.5: Prop 3.4, Lemma 3.5, Prop 3.6, plane-wave solutions |
| `Feec.Ch4.Adjoint` | §4.1–4.2: adjoints, (4.1a–d), `T** = T`, closed range theorem, dual complex |
| `Feec.Ch4.Hodge`, `Feec.Ch4.HodgeW` | §4.2: Thm 4.1 (Hodge decomposition), Thm 4.2 (Poincaré), compactness and Fredholm |
| `Feec.Ch4.Restriction`, `Feec.Ch4.Existence` | §4.3: Thm 4.3 (as hypothesis, shown non-vacuous), Thm 4.4, Cor 4.5 |
| `Feec.Ch4.Stone` | §4.3: Stone's theorem on a real Hilbert space (`L` skew-adjoint ⇔ `L` generates an orthogonal group) |
| `Feec.Ch4.Duhamel`, `Feec.Ch4.StoneDuhamel` | §4.3: Duhamel's formula; Thm 4.3 with forcing in `C([0,T];D(L))` or of `W^{1,1}` type |
| `Feec.Ch4.StoneForcing` | §4.3: Thm 4.3 for the thesis's full forcing class `C([0,T];X) ∩ (W^{1,1}(0,T;X) ∪ L¹(0,T;D(L)))` |
| `Feec.Ch4.StoneApplications`, `Feec.Ch4.Unconditional` | Ch. 4: Thm 4.3, Cor 4.5, Thms 4.6–4.7, Props 4.16–4.18 and semi-discrete convergence without existence hypotheses |
| `Feec.Ch4.HodgeWave` | §4.4: Thm 4.6, Thm 4.7, weak uniqueness |
| `Feec.Ch4.Galerkin` | §4.5: Thms 4.8–4.11 (Lax–Milgram, Babuška–Nečas, quasi-optimality, Brezzi) |
| `Feec.Ch4.ErrorEstimate` | §4.6: Lemma 4.12, Prop 4.13, elliptic projection, Thm 4.14, convergence |
| `Feec.Ch4.ErrorEstimateDL` | §4.6: the convergence remark after Thm 4.14 for data in `D(L)` and in `W`; `C¹(V)` solutions can fail to exist for `D(L)` data |
| `Feec.Ch4.Constraints` | §4.7–4.11: Koszul complexes, wave equations, Props 4.16–4.19 |
| `Feec.Ch4.Torus` | §4.10: Prop 4.17 on the periodic complex over 𝕋³ (Fourier model) |
| `Feec.Ch4.TorusWeak` | §4.10: the Fourier-weight `H¹`, `H(curl)`, `H(div)` on 𝕋³ are the weak-derivative Sobolev spaces |
| `Feec.Ch4.TorusGroup` | §4.3, §4.10: explicit Stone group on 𝕋³, Thm 4.3 (with forcing), existence for Prop 4.17 |
| `Feec.Ch4.TorusSym` | §4.11: complex (4.16) on 𝕋³, closed range and Hodge decomposition, Prop 4.19 with existence |
| `Feec.Ch4.WholeMul`, `Feec.Ch4.Whole`, `Feec.Ch4.WholeWeak`, `Feec.Ch4.WholeIdent` | §4.10: Prop 4.17 on ℝ³ (Fourier multipliers on `L²`), with existence; `H¹`, `H(curl)`, `H(div)` and `L²(TSD)` identified with their weak-derivative versions |
| `Feec.Ch4.WholeReal`, `Feec.Ch4.WholeRange` | §4.10: Prop 4.17 on ℝ³ for real fields; `grad` and `curl` on ℝ³ do not have closed range |
| `Feec.Ch4.WholeSym` | §4.11: Prop 4.19 on ℝ³, with existence |
| `Feec.Ch4.BoundedDomain`, `Feec.Ch4.BoundedDomainExt` | §4.10: the complex `H̊¹ → H̊(curl) → L²` on bounded domains, `D(curl*) = H(curl)`; Prop 4.17 fails there |
| `Feec.Ch4.BoundedSalvage`, `Feec.Ch4.BoundedSalvageMax`, `Feec.Ch4.BoundedSalvageDim` | §4.10: what survives on bounded domains: the obstruction space (infinite-dimensional), a necessary condition for propagation, Prop 4.17 on the maximal invariant constraint space |
| `Feec.Ch4.BoundedDensity` | §4.10: the density conjectures of Prop 4.17 are true; the density inferred from them fails for `H̊(curl)` (star-shaped domains) |
| `Feec.Ch4.BoundedInterior` | §4.10, Prop 3.6: TSD propagates in the interior at unit speed; the violation starts at the boundary |
| `Feec.Ch4.BoundedSym` | §4.11: complex (4.16) on bounded domains; Prop 4.19 fails there, and its corrected maximal form |
| `Feec.Ch4.BoundedSymExt` | §4.11: adjoint domains of (4.16); the boundary conditions as printed in Prop 4.19 |
| `Feec.Ch4.Box`, `Feec.Ch4.BoxRestrict`, `Feec.Ch4.BoxReduce`, `Feec.Ch4.BoxStatic`, `Feec.Ch4.BoxThesis`, `Feec.Ch4.BoxForward` | §4.10: the box `(0, ½)³` as parity subspaces of the 𝕋³ model; with the thesis's boundary conditions only stationary data propagate, even forward in time |
| `Feec.Ch4.BoxMirror` | §4.10–4.11: Props 4.17 and 4.19 on the box with tensorial mirror boundary conditions |
| `Feec.Ch5.BGG` | §5.1: Props 5.1–5.2 |
| `Feec.Ch5.Discrete` | §5.2–5.3: Props 5.3, 5.4, 5.6, Thm 5.5, abstract core of Prop 5.7 |
| `Feec.Ch6.TimeDependent` | Ch. 6: Props 6.1–6.3, a convergence theorem |
| `Feec.Ch6.Bounded` | Ch. 6: the complex (5.1) on bounded domains with the boundary conditions of §6.3; TSD and the symmetry of `B` are lost |
| `Feec.Ch6.Whole` | Ch. 6: the complex (5.1) on ℝ³; the hypotheses of Prop 4.17 hold and TSD propagates |
| `Feec.Ch7.CrankNicolson` | Ch. 7: full and reduced Crank–Nicolson schemes, energy, MINRES system |

## Corrections to the thesis

The most significant errors and gaps found during formalization. Each line names the Lean
declaration that refutes or corrects the original; module docstrings list the rest.

- **Prop 2.4(b)**: `H = −□h̄` is false; it is `H = −½□h̄` (`thesis_prop_2_4b_false`).
- **Prop 2.6**: the gauge vector `B` has the wrong sign and does not reach TT gauge (`thesis_gauge_fails`, `tt_gauge`).
- **(2.15)**: the geodesic-deviation accelerations have the wrong sign and `f` in place of `f''` (`thesis_accel_fails`, `tt_accel_fun`).
- **§2.4**: `8πG/c⁴ ≈ 2.08·10⁻⁴³`, not `5·10⁻⁴⁴` (`einstein_const_bounds`); `G = 0 ⇔ Ric = 0` needs `n ≠ 2` (`einstein_zero_iff_fails_two`).
- **§4.3**: the kernel of an unbounded operator need not be closed (`exists_not_isClosed_ker`).
- **§4.2**: "Fredholm ⇒ closed" is false (`fredholm_not_closed`); compactness does imply it (`closed_and_fredholm_of_compact`).
- **Thm 4.6**: closed range is unnecessary (`adjoint_waveOp_domain_le`); density of `D(L)` and the sign of the evolution are supplied (`thm_4_6`).
- **Thm 4.9**: the converse needs a *unique* solution; the backward shift is a counterexample (`surjective_not_infSup`).
- **Thm 4.11 (Brezzi)**: the inf-sup condition on `b` is quantified over the wrong argument and the thesis gives no proof; stated correctly and proved (`brezzi`, `thm_4_11`, `not_infSup_first_of_ker_ne_bot`).
- **Lemma 4.12**: `Q ∈ C¹` fails where the lemma is applied; only `Q²` needs to be differentiable (`lemma_4_12`).
- **Thm 4.14**: it needs `ξ ∈ C¹(V)`, and the `(1 + T)` factor is sharpened (`thm_4_14_pointwise`, `thm_4_14`). `ξ₀ ∈ D(L)` does not give `C¹(V)` (`cxK1_exists_not_isWeakSol`), but the convergence claimed after the theorem holds for every `ξ₀ ∈ D(L)`, without a rate (`convergence_domL_weakSolution`, `convergence_W`).
- **§4.10**: two of the four proposed discretizations are not subcomplexes (`pgrad_not_mem_PminusLambda1`).
- **Props 4.17, 4.19**: the density conjectures are unnecessary (`prop_4_17`), and the projection hypothesis is necessary for the conclusion (`prop_4_17_necessary`, `prop_4_17_iff`). Without a boundary the projection conjecture is a theorem and Props 4.17 and 4.19 hold with no extra hypothesis, with existence of solutions: on 𝕋³ (`projKc_mem_domL`, `prop_4_17_torus_exists`, `prop_4_19_torus_exists`) and on ℝ³ (`Whole.projKc_mem_domL`, `prop_4_17_whole_exists`, `prop_4_19_whole_exists`, and for real fields `real_prop_4_17_whole_exists`). On every nonempty bounded open `Ω ⊆ ℝ³` both projection hypotheses are false for the thesis's complexes, so Props 4.17 and 4.19 are vacuous as stated (`thesisComplex_not_projection_hyp`, `thesisComplex_not_projection_hyp2`, `symComplexB_not_projection_hyp`). Their conclusions fail too, with no extra hypothesis: for explicit TSD data, (4.14) and (4.18) have a strong solution and every strong solution leaves the constraint set (`thesisComplex_orbit_not_propagate_unconditional`, `symComplexB_not_propagate_unconditional`). The density conjectures themselves are true on every bounded domain (`thesisComplex_dense_literal`, `dense_HcurlM_inter_HdivZero`); the invalid step is the inference that `H̊(curl) ∩ L²(TSD)` is dense in `L²(TSD)`: its closure has infinite codimension (`not_dense_TSD_inter_HcurlZero`, `not_TSD_le_span_closure_sup_finiteDimensional`), and on domains star-shaped with respect to a ball it is exactly `L²(TSD₀)` (`prop417_density_gap`). The failure starts at the boundary: TSD propagates in the interior at unit speed, and for the datum `(0, 0, β)` the violation is present in the boundary layer (`thesisComplex_TSD_depDomain`, `thesisComplex_beta_violation_boundary_layer`). What survives on bounded domains: Props 4.16 and 4.18, and Props 4.17/4.19 on the largest invariant constraint space `K* ⊊ K` (`thesisComplex_prop_4_17_max`, `symComplexB_prop_4_19_max`). On the box `(0, ½)³` with the boundary conditions of Prop 4.17, in a parity model, `K*` consists exactly of the stationary data, and forward invariance alone already forces this (`thesisBox_mem_Kmax_iff`, `thesisBox_forward_iff`); with tensorial mirror conditions Props 4.17 and 4.19 hold (`mirror_prop_4_17_exists`, `mirror_prop_4_19_exists`). For the boundary conditions as printed in Prop 4.19 (`symComplexD`), the projection hypothesis and the density fail (`symComplexD_not_projection_hyp`, `symComplexD_not_dense`).
- **(5.1)**: exactness at `Ṽ¹` is used but never proved (`exact_mid`).
- **Prop 5.4**: exactness at `V_h¹` cannot be dropped (`prop54_counterexample_noTopExact`).
- **Prop 6.2**: false as stated; it holds exactly under compatibility conditions (C1)–(C3) (`prop_6_2_false`, `prop_6_2`).
- **Ch. 6**: on bounded domains with the boundary conditions of §6.3, the weak-symmetry method inherits the failure: from the TSD datum `(0, 0, (0, β))` the unique solution has `u(t) ∉ L²(TSD)` and `B(t)` non-symmetric for some `t` in every `[0, T]` (`bggComplex_verdict`). On ℝ³ the same system propagates TSD (`bggWhole_verdict`).
- **Ch. 7**: MINRES does not apply to the unsymmetrized Crank–Nicolson matrix; a sign change symmetrizes it (`minres_symm`).

## Scope

Mathlib lacks C₀-semigroups and the Hille–Yosida and Stone theorems. The core Ch. 4 modules
state existence for evolution problems as the explicit hypotheses `WellPosedExistence` or
`WellPosedHom` (standing for Thm 4.3), never as axioms. Stone's theorem is proved in
`Feec.Ch4.Stone` for every real Hilbert space, which discharges these hypotheses for every
skew-adjoint generator, in particular for the Hodge wave operator of every Hilbert complex
(`Feec.HilbertComplex2.waveGroup`), bounded domains included; `Feec.Ch4.TorusGroup` and
`Feec.Ch4.TorusSym` also construct the periodic groups explicitly by Fourier series. Thm 4.3
holds for the thesis's full forcing class `C([0,T];X) ∩ (W^{1,1}(0,T;X) ∪ L¹(0,T;D(L)))`, with
`W^{1,1}` in integral form (`Feec.thm_4_3_full`); its equivalence with "absolutely continuous with
an integrable derivative" is not formalized. Semi-discrete convergence holds for every datum in
`W` (`Feec.HilbertComplex2.convergence_W`), and in the thesis's form for `ξ₀ ∈ D(L)`
(`convergence_domL_weakSolution`); the error bound of Thm 4.14 needs `ξ₀ ∈ D(L²)`, and no rate
is formalized for `D(L)` or `W` data. Uniqueness, energy conservation and constraint
propagation are proved.

Mathlib has no Sobolev spaces on domains, traces or finite element spaces. Abstract results
therefore take concrete complexes (de Rham, `H(curl)`, `H(div)`, polynomial finite element
spaces) as instances of abstract structures, with their analytic facts (closed range, bounded
cochain projections, density, regular decompositions) as hypotheses. Four concrete models are
built:
* 𝕋³ (`Feec.Ch4.Torus`): fields by their Fourier coefficients (a proved isometry
  `L²(𝕋³) ≃ ℓ²(ℤ³)`), with `H¹`, `H(curl)`, `H(div)` defined by Fourier weights;
  `Feec.Ch4.TorusWeak` proves these are the weak-derivative Sobolev spaces.
* ℝ³ (`Feec.Ch4.Whole*`, `Feec.Ch6.Whole`): Fourier multipliers on `L²(ℝ³)`. Through the `L²`
  Fourier transform, `H¹`, `H(curl)`, `H(div)` and `L²(TSD)` are the weak-derivative spaces
  tested against Schwartz fields (`Feec.WholeIdent`, `Feec.WholeWeak`); the S- and T-valued
  spaces of (4.16) are not identified this way. Fields are complex-valued; real fields are the
  fixed points of a reality involution, and Prop 4.17 is proved for the complex restricted to
  them (`Feec.WholeReal`). That the Stone group of the full complex maps real data to real states
  is not proved.
* Bounded domains (`Feec.Ch4.BoundedDomain` and sequels, `Feec.Ch6.Bounded`): `H̊¹`, `H̊²`,
  `H̊(curl)`, `H(curl)`, `H(div)` from their definitions (graph closures and weak derivatives),
  with `L²(Ω; ℝ³ˣ³)` modelled as nine copies of `L²(Ω)` (isometric to the Bochner space,
  `Feec.BoundedDomain.piL2Equiv`). Lemma 3.5 is proved there in distributional form, with the
  `H̊(curl)` boundary condition (`Feec.BoundedDomain.curl_symm_of_mem_TSD`,
  `Feec.BoundedSym.curlS_mem_TSDT`) and without it (`Feec.BoundedSym.symm_of_weakCurl_TSD`,
  `Feec.BoundedSym.symComplexD_d1_mem_TSDT`). Prop 3.6 holds in its interior form at unit speed
  (`Feec.Ch4.BoundedInterior`), and on ℝ³ for solutions of the weak equations
  (`WeakEB.mem_TSD_univ`), which are assumed, not constructed. Density of `L²(TSD) ∩ H̊(curl)` in
  `L²(TSD₀)` is proved for domains star-shaped with respect to a ball, not for Lipschitz domains.
* The box `(0, ½)³` (`Feec.Ch4.Box*`): parity subspaces of the 𝕋³ model, encoding the thesis's
  boundary conditions or tensorial mirror conditions. These subspaces are not identified with the
  Sobolev and trace spaces of the box.

The thesis states its Ch. 4 results with boundary conditions on a bounded `Ω` (§4.10, §6.3), so
the bounded-domain modules are the faithful setting; 𝕋³ and ℝ³ have no boundary and serve as a
contrast. Verdicts: Props 4.17 and 4.19 hold on 𝕋³ and ℝ³ and fail on every bounded domain; on
the box with the boundary conditions of Prop 4.17 only stationary data propagate, and with mirror
conditions both propositions hold. For the boundary conditions printed in Prop 4.19
(`symComplexD`), the hypotheses fail and the conclusion is not decided, nor is whether its `K*`
is nonzero. The Ch. 6 weak-symmetry system on bounded domains loses TSD and the symmetry of `B`
(`Feec.Ch6.Bounded.bggComplex_verdict`), with homogeneous boundary conditions and zero forcing,
and propagates TSD on ℝ³ (`Feec.Ch6.Whole.bggWhole_verdict`). Not formalized for Ch. 6: the
multiplier form (6.2), the transfer of the failure to the semi-discrete scheme (6.5), and its
bearing on Ch. 7, which states no boundary conditions and whose plane-wave exact solution does
not satisfy the homogeneous ones.

Pseudo-Riemannian geometry is done in components at the jet level. Out of scope: the nonlinear
Einstein–Bianchi system (§3.4), the concrete finite element computations of §5.3 (Props 5.7–5.9
beyond the abstract core of Prop 5.7), and the numerical results of Ch. 7. All cited works are
collected in [`references.bib`](references.bib).
