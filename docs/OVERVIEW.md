# Overview

Module map, corrections to the thesis, the proved repaired statements, and scope of the
formalization.

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
| `Feec.Ch4.BoundedKstar` | §4.10–4.11: `K*` by spectral theory: forward invariance ⇔ `K*` under pure point spectrum; under `EigenDense`, `K*` moves iff a TSD eigenfield of `curl* curl` exists |
| `Feec.Ch4.BoundedInterior` | §4.10, Prop 3.6: TSD propagates in the interior at unit speed; the violation starts at the boundary |
| `Feec.Ch4.BoundedSym` | §4.11: complex (4.16) on bounded domains; Prop 4.19 fails there, and its corrected maximal form |
| `Feec.Ch4.BoundedSymExt` | §4.11: adjoint domains of (4.16); the boundary conditions as printed in Prop 4.19 |
| `Feec.Ch4.BoundedSymDual` | §4.11: with the boundary conditions as printed, the conclusion of Prop 4.19 fails on the unit ball |
| `Feec.Ch4.Box`, `Feec.Ch4.BoxRestrict`, `Feec.Ch4.BoxReduce`, `Feec.Ch4.BoxStatic`, `Feec.Ch4.BoxThesis`, `Feec.Ch4.BoxForward` | §4.10: the box `(0, ½)³` as parity subspaces of the 𝕋³ model; with the thesis's boundary conditions only stationary data propagate, even forward in time |
| `Feec.Ch4.BoxIdent` | §4.10: the parity model is the bounded-domain complex on `(0, ½)³`; the box results hold on every open cube, `(0, π)³` included |
| `Feec.Ch4.BoxMirror` | §4.10–4.11: Props 4.17 and 4.19 on the box with tensorial mirror boundary conditions |
| `Feec.Ch5.BGG` | §5.1: Props 5.1–5.2 |
| `Feec.Ch5.Discrete` | §5.2–5.3: Props 5.3, 5.4, 5.6, Thm 5.5, abstract core of Prop 5.7 |
| `Feec.Ch6.TimeDependent` | Ch. 6: Props 6.1–6.3, a convergence theorem |
| `Feec.Ch6.Bounded` | Ch. 6: the complex (5.1) on bounded domains with the boundary conditions of §6.3; TSD and the symmetry of `B` are lost |
| `Feec.Ch6.Whole` | Ch. 6: the complex (5.1) on ℝ³; the hypotheses of Prop 4.17 hold and TSD propagates |
| `Feec.Ch7.CrankNicolson` | Ch. 7: full and reduced Crank–Nicolson schemes, energy, MINRES system |
| `Feec.Repair.C2` | §2.5: Prop 2.6 as an existence theorem (gauge vector from an antiderivative of `f`) |
| `Feec.Repair.C410` | §4.10: polynomial `curl`, `P_rΛ¹`, `P_rΛ²`, `P_r⁻Λ²`, `⊗V`; the corrected list of discretizations |
| `Feec.Repair.C417Compress`, `Feec.Repair.C417Ext`, `Feec.Repair.C417Cube`, `Feec.Repair.C417CubeDense` | §4.10: compression of a Hilbert complex; mirror extensions `L²(Q) → L²(𝕋³)`; Prop 4.17 on `Q = (0, ½)³` with tensorial mirror conditions for `L²(Q)` fields |
| `Feec.Repair.C417Pi`, `Feec.Repair.C419Cube`, `Feec.Repair.C419Pi` | §4.10–4.11: Prop 4.17 on every open cube, `(0, 1)³` and `(0, π)³` included; Prop 4.19 on `Q` and on every open cube, with mirror conditions |
| `Feec.Repair.C417BggTorus`, `Feec.Repair.C417BggCube` | Ch. 6: the BGG system (5.1) on 𝕋³ and on `Q` with mirror conditions; TSD propagates |
| `Feec.Repair.C417` | §4.10–4.11, Ch. 6: bundled corrected statements of Props 4.17, 4.19 and of the Ch. 6 claim |
| `Feec.Repair.C67`, `Feec.Repair.C67Prop62`, `Feec.Repair.C67Minres` | Ch. 6–7: Prop 6.2 for dynamic data, convergence without an assumed discrete solution; the MINRES systems of Ch. 7 |

## Corrections to the thesis

The most significant errors and gaps found during formalization. Each line names the Lean
declaration that refutes or corrects the original; module docstrings list the rest.

- **Prop 2.4(b)**: `H = −□h̄` is false; it is `H = −½□h̄` (`thesis_prop_2_4b_false`).
- **Prop 2.6**: the gauge vector `B` has the wrong sign and does not reach TT gauge (`thesis_gauge_fails`); with the sign fixed it does (`tt_gauge`, `prop_2_6`).
- **(2.15)**: the geodesic-deviation accelerations have the wrong sign and `f` in place of `f''` (`thesis_accel_fails`, `tt_accel_fun`).
- **§2.4**: `8πG/c⁴ ≈ 2.08·10⁻⁴³`, not `5·10⁻⁴⁴` (`einstein_const_bounds`); `G = 0 ⇔ Ric = 0` needs `n ≠ 2` (`einstein_zero_iff_fails_two`).
- **§4.3**: the kernel of an unbounded operator need not be closed (`exists_not_isClosed_ker`).
- **§4.2**: "Fredholm ⇒ closed" is false (`fredholm_not_closed`); compactness does imply it (`closed_and_fredholm_of_compact`).
- **Thm 4.6**: closed range is unnecessary (`adjoint_waveOp_domain_le`); density of `D(L)` and the sign of the evolution are supplied (`thm_4_6`).
- **Thm 4.9**: the converse needs a *unique* solution; the backward shift is a counterexample (`surjective_not_infSup`).
- **Thm 4.11 (Brezzi)**: the inf-sup condition on `b` is quantified over the wrong argument and the thesis gives no proof; stated correctly and proved (`brezzi`, `thm_4_11`, `not_infSup_first_of_ker_ne_bot`).
- **Lemma 4.12**: `Q ∈ C¹` fails where the lemma is applied; only `Q²` needs to be differentiable (`lemma_4_12`).
- **Thm 4.14**: it needs `ξ ∈ C¹(V)`, and the `(1 + T)` factor is sharpened (`thm_4_14_pointwise`, `thm_4_14`). `ξ₀ ∈ D(L)` does not give `C¹(V)` (`cxK1_exists_not_isWeakSol`), but the convergence claimed after the theorem holds for every `ξ₀ ∈ D(L)`, without a rate (`convergence_domL_weakSolution`, `convergence_W`).
- **§4.10**: two of the four proposed discretizations are not subcomplexes (`pgrad_not_mem_PminusLambda1`, `sec410_printed_fail`); replacing `P_{r+1}Λ⁰` by `P_rΛ⁰` in them fixes this (`sec410_corrected`).
- **Props 4.17, 4.19**: the density conjectures are unnecessary (`prop_4_17`), and the projection hypothesis is necessary for the conclusion (`prop_4_17_necessary`, `prop_4_17_iff`). Without a boundary the projection conjecture is a theorem and Props 4.17 and 4.19 hold with no extra hypothesis, with existence of solutions: on 𝕋³ (`projKc_mem_domL`, `prop_4_17_torus_exists`, `prop_4_19_torus_exists`) and on ℝ³ (`Whole.projKc_mem_domL`, `prop_4_17_whole_exists`, `prop_4_19_whole_exists`, and for real fields `real_prop_4_17_whole_exists`). On every nonempty bounded open `Ω ⊆ ℝ³` both projection hypotheses are false for the thesis's complexes, so Props 4.17 and 4.19 are vacuous as stated (`thesisComplex_not_projection_hyp`, `thesisComplex_not_projection_hyp2`, `symComplexB_not_projection_hyp`). Their conclusions fail too, with no extra hypothesis: for explicit TSD data, (4.14) and (4.18) have a strong solution and every strong solution leaves the constraint set (`thesisComplex_orbit_not_propagate_unconditional`, `symComplexB_not_propagate_unconditional`). The density conjectures themselves are true on every bounded domain (`thesisComplex_dense_literal`, `dense_HcurlM_inter_HdivZero`); the invalid step is the inference that `H̊(curl) ∩ L²(TSD)` is dense in `L²(TSD)`: its closure has infinite codimension (`not_dense_TSD_inter_HcurlZero`, `not_TSD_le_span_closure_sup_finiteDimensional`), and on domains star-shaped with respect to a ball it is exactly `L²(TSD₀)` (`prop417_density_gap`). The failure starts at the boundary: TSD propagates in the interior at unit speed, and for the datum `(0, 0, β)` the violation is present in the boundary layer (`thesisComplex_TSD_depDomain`, `thesisComplex_beta_violation_boundary_layer`). What survives on bounded domains: Props 4.16 and 4.18, and Props 4.17/4.19 on the largest invariant constraint space `K* ⊊ K` (`thesisComplex_prop_4_17_max`, `symComplexB_prop_4_19_max`). On every open cube, `(0, π)³` included, with the boundary conditions of Prop 4.17, `K*` consists exactly of the stationary data, and forward invariance alone already forces this (`openCube_mem_Kmax_iff'`, `openCube_forward_iff`, `piCube_mem_Kmax_iff`; proved in a parity model of `(0, ½)³`, `thesisBox_mem_Kmax_iff`, `thesisBox_forward_iff`, which `Feec.Ch4.BoxIdent` identifies with the bounded-domain complex); with tensorial mirror conditions Props 4.17 and 4.19 hold, in the parity model (`mirror_prop_4_17_exists`, `mirror_prop_4_19_exists`) and for `L²` fields on `(0, ½)³` and on every open cube (`mirrorCxQ_prop_4_17_exists`, `piCube_mirror_prop_4_17_exists`, `mirrorSymCxCube_prop_4_19_exists`). For the boundary conditions as printed in Prop 4.19 (`symComplexD`), the projection hypothesis and the density fail (`symComplexD_not_projection_hyp`, `symComplexD_not_dense`), and on the unit ball so does the conclusion: for an explicit TSD datum the unique strong solution leaves the constraint set (`symComplexD_ball_not_propagate_unconditional`).
- **(5.1)**: exactness at `Ṽ¹` is used but never proved (`exact_mid`).
- **Prop 5.4**: exactness at `V_h¹` cannot be dropped (`prop54_counterexample_noTopExact`).
- **Prop 6.2**: false as stated; it holds exactly under compatibility conditions (C1)–(C3) (`prop_6_2_false`, `prop_6_2`), of which only (C2) constrains the dynamic data (`prop_6_2_dynamic`).
- **Ch. 6**: on bounded domains with the boundary conditions of §6.3, the weak-symmetry method inherits the failure: from the TSD datum `(0, 0, (0, β))` the unique solution has `u(t) ∉ L²(TSD)` and `B(t)` non-symmetric for some `t` in every `[0, T]` (`bggComplex_verdict`). On ℝ³ and 𝕋³ the same system propagates TSD (`bggWhole_verdict`, `bggTorus_verdict`), and so it does on `(0, ½)³` with mirror conditions (`bggCxQ_verdict`).
- **Ch. 7**: MINRES does not apply to the unsymmetrized Crank–Nicolson matrix (`cn_matrix_not_isSymm`); a sign change symmetrizes it (`minres_symm`). The thesis does not say which matrix MINRES is applied to; for the Schur complement of block elimination the claim holds as stated (`schurE_posDef`).

## Repaired statements

Every correction above comes with a proved corrected statement: the strongest true form of what
the thesis claims and uses downstream that is formalized here. Names are given without
namespace; the repairs added in this round live in `Feec.Repair.*`. All are kernel-checked and
depend only on `propext`, `Classical.choice` and `Quot.sound`. The last paragraph of this
section lists what the repairs do not cover.

| Thesis | Claim | Defect | Proved corrected statement | Lean |
|---|---|---|---|---|
| Prop 2.4(b), (2.11) | In Lorentz gauge `H_bd = −□h̄_bd`, so `□h̄ = −16πT` | Factor `½` missing | For every C² symmetric `h` with `∂^a h̄_ab = 0`: `H_bd = −½□h̄_bd`, hence `H = 8πT ⇔ □h̄ = −16πT` | `Hfun_lorentz`, `Hjet_lorentz`, `lorentz_fun_iff`, `thesis_prop_2_4b_false` |
| Prop 2.6 | `ξ_a = B_a g(k·x)` with the printed `B` brings a plane wave to TT gauge | Printed `B` fails under both index readings | For `κ ≠ 0`, `A` symmetric with `Ak = 0`, `f ∈ C²`: there is a C³ gauge vector (`B` = minus the printed one, `g = ∫₀ f`) with `h̄ − (2∂_(aξ_b) − η_ab∂·ξ) = A' f(k·x)`, `A' = ttAmp((A₁₁−A₂₂)/2, A₁₂)` TT, again a vacuum plane wave; `□ξ = 0` | `prop_2_6`, `prop_2_6_metric`, `box_ttGaugeVec`, `tt_gauge`, `thesis_gauge_fails` |
| (2.15) | `a¹ = −(κ²/2)(A₊v¹ + Aₓv²) f`, `a² = −(κ²/2)(Aₓv¹ − A₊v²) f` | Wrong sign, `f` in place of `f''` | `a¹ = (κ²/2)(A₊v¹ + Aₓv²) f''(k·x)`, `a² = (κ²/2)(Aₓv¹ − A₊v²) f''(k·x)`, `a⁰ = a³ = 0`; the printed Riemann components hold for every TT jet | `tt_accel_fun`, `tt_accel`, `Rjet_tt`, `Rjet_tt_support`, `thesis_accel_fails` |
| §2.4 | `8πG/c⁴ ≈ 5·10⁻⁴⁴`; `G = 0 ⇔ Ric = 0` | The value is `2πG/c⁴`; the equivalence needs `n ≠ 2` | `8πG/c⁴ ∈ (2.07, 2.09)·10⁻⁴³`; for every `n ≠ 2`, `Ric − ½ tr(g⁻¹Ric) g = 0 ⇔ Ric = 0`, false for `n = 2` | `einstein_const_bounds`, `einstein_zero_iff`, `einstein_zero_iff_fails_two` |
| §4.3 | The kernel of any linear operator is closed, so `MU = 0` on `[0,T]` | False for non-closed operators | `ker M` is closed for closed `M`; for closed `M` with the invariance hypotheses every strong solution has `MU(t) = 0`, with existence for skew-adjoint `L`; the constraint spaces used downstream (`ker d0*`, `L²(TSD)`) are closed | `isClosed_ker`, `constraint_ker`, `constraint_ker_exists_unconditional`, `isClosed_ker_adj0`, `exists_not_isClosed_ker` |
| §4.2 | Compactness ⇒ Fredholm ⇒ closed | "Fredholm ⇒ closed" false with finite-dimensional harmonic forms | Finite-dimensional cohomology ⇒ closed range; compact inclusion ⇒ closed and Fredholm, with the Hodge decomposition without closures, in every degree | `isClosedAt_of_finiteDimensional_cohomology`, `closed_and_fredholm_of_compact`, `closed_and_fredholm_of_isCompactOperator`, `fredholm_not_closed` |
| Thm 4.6 | Under closed range, `L` is skew-adjoint and data in `D(L)` have unique solutions | Closed range unneeded; density of `D(L)` and existence not shown | For every length-2 complex of closed densely defined operators: `D(L)` dense, `L` skew-adjoint, a unique solution in `C⁰(D(L)) ∩ C¹(W)` for `ξ₀ ∈ D(L)`, energy conserved | `thm_4_6`, `thm_4_6_unconditional`, `thm_4_6_strong_unconditional`, `adjoint_waveOp_domain_le`, `waveOp_isSkewAdjoint` |
| Thm 4.9 | Inf-sup and dense range ⇔ `a(u,·) = f` solvable for every `f` | Needs a unique solution; the backward shift is a counterexample | (Inf-sup ∧ dense range in the second slot) ⇔ `∀ f, ∃! u, a(u,·) = f`; `γ` admissible ⇔ `γ‖L⁻¹‖ ≤ 1` | `babuska_necas_iff`, `babuska_necas_iff_dual`, `infSup_const_iff`, `surjective_not_infSup` |
| Thm 4.11 | Brezzi well-posedness, inf-sup on `b` over `u`; no proof | The printed inf-sup is unsatisfiable when `Z ≠ 0` | With inf over `q ∈ Y`, inf-sup and dense range of `a` on `Z`: a unique `(u,p)` with `‖u‖ + ‖p‖ ≤ C(‖F‖ + ‖G‖)`, explicit `C(‖a‖, γ, β)` | `thm_4_11`, `brezzi_wellPosed`, `brezzi_stability`, `not_infSup_first_of_ker_ne_bot` |
| Lemma 4.12 | `Q ∈ C¹`, `(Q²)' ≤ FQ` ⇒ `Q(t) ≤ Q(0) + ½∫₀ᵗF` | Applied to `‖ε_h‖`, which is not C¹ | `Q ≥ 0` continuous with `Q²` right-differentiable and `(Q²)' ≤ FQ` ⇒ the same bound; sharp | `lemma_4_12`, `lemma_4_12_integral`, `lemma_4_12_sharp` |
| Thm 4.14 | Error bound for `ξ ∈ C⁰(V) ∩ C¹(W)`; convergence under compactness | Needs `ξ ∈ C¹(V)`, which `ξ₀ ∈ D(L)` does not give | Pointwise bound with `t` in place of `T` for `ξ ∈ C¹(V)`, which exists uniquely for `ξ₀ ∈ D(L²)`; convergence (no rate) for every `ξ₀ ∈ D(L)`, and every `ξ₀ ∈ W`, from density alone | `thm_4_14_pointwise`, `thm_4_14`, `exists_isWeakSol_unconditional`, `convergence_domL_weakSolution`, `convergence_W`, `cxK1_exists_not_isWeakSol` |
| §4.10 | Four discretizations of (4.14), four of (4.15) | `P_{r+1}Λ⁰ × P_r⁻Λ¹` is not a subcomplex | With `P_rΛ⁰` paired with `P_r⁻Λ¹`, all four (4.14) choices are subcomplexes (row-wise `⊗V`); the (4.15) list is correct as printed; the 0-form degree is maximal | `sec410_corrected`, `sec410_printed_fail`, `sec410_reduced`, `sec410_reduced_V0`, `sec410_alt`, `pgrad_PLambda0_sub_PminusLambda1_iff` |
| Props 4.17, 4.19 | On bounded `Ω`, under projection and density conjectures, TSD data propagate | Hypotheses false and conclusions fail on every bounded `Ω` with the stated conditions; the density inference is invalid | Hold on 𝕋³ and ℝ³ for all TSD data, with existence and uniqueness; with the thesis's conditions only on `K*`, stationary on cubes (4.17); with tensorial mirror conditions on every open cube, `(0,1)³` and `(0,π)³` included, with `K* = K` and moving data | `prop_4_17_corrected`, `prop_4_17_corrected_cube`, `prop_4_19_corrected`, `prop_4_19_corrected_cube`, `prop_4_17_iff`, `piCube_mirror_prop_4_17_exists`, `mirrorSymCxCube_prop_4_19_exists`, `openCube_forward_sub_iff` |
| (5.1) | Exactness at `Ṽ¹` (used in Props 5.2, 5.4) | Never proved | `N(S₁) ∩ N(d̃¹) = R(0 d)` from exactness of the two complexes; used in Prop 5.2 | `exact_mid`, `range_D0`, `BGGHilb.mem_Z1_iff` |
| Prop 5.4 | The discrete system (5.6) is invertible | The proof never uses exactness at `V_h¹`, which is necessary | With exactness at `V_h¹` and `Ṽ_h¹`, `d̃` injective and `V_h¹ = dV_h⁰ + S₀Ṽ_h⁰` (weaker than `S₀` onto): unique solution for all data; derived from the continuous hypotheses | `prop54_existsUnique`, `Disc.prop_5_4`, `prop54_counterexample_noTopExact`, `prop54_hB_necessary` |
| Prop 6.2 | (6.3) has a unique solution for every initial datum with `(σ₀, φ₀) ∈ Γ_h` | False | Solvable ⇔ (C1)–(C3), uniquely; for dynamic data `(σ₀, u₀, M₀, ρ₀)` ⇔ `(u₀, dψ) = 0` for `ψ ∈ ker S₀,h`, with `φ_h(0)` forced; projected data give a solution and the error bound | `prop_6_2`, `prop_6_2_dynamic`, `prop_6_2_wellposed`, `ch6_convergence_projected`, `prop_6_2_false`, `projected_Q0_counterexample` |
| Ch. 6 | The weak-symmetry method with the §6.3 conditions propagates TSD | Fails on every bounded domain | Propagates TSD on ℝ³, on 𝕋³, and on `(0, ½)³` with mirror conditions: unique solution, `σ ≡ 0`, `u` TSD, `M ≡ 0`, `B` TSD and symmetric | `ch6_corrected`, `bggWhole_verdict`, `bggTorus_verdict`, `bggCxQ_verdict`, `bggComplex_verdict` |
| Ch. 7 | "Other matrices are inverted with MINRES" | The Crank–Nicolson matrix is not symmetric | `J(M + sK)` is symmetric, nonsingular, indefinite, and its system is solved exactly by the CN update (assembled from Gram, `grad`, `curl` matrices); the Schur complement of block elimination is SPD | `minres_symm`, `cn_matrix_not_isSymm`, `minres_matrix_indefinite`, `minres_cn_existsUnique`, `minres_solution_iff_cnStep`, `cn_schur_iff`, `schurE_posDef` |

Limits of the repairs. Props 4.17, 4.19 and the Ch. 6 claim are repaired on domains without
boundary and on axis-parallel cubes only: on a curved bounded domain no boundary condition is
proved to propagate non-stationary TSD data (the mirror conditions do not form a complex there),
and the Ch. 6 system with mirror conditions is proved only on `(0, ½)³`, since it is not
dilation-invariant. The mirror conditions hold in the reflection sense, not as trace conditions;
on cubes other than `(0, ½)³` the operators of (4.16) are dilation conjugates, not identified with
the weak Hessian and curl. The §4.10 repair is at the level of polynomial shape functions, without
a mesh or cochain projections. Prop 6.2 keeps the §6.3 finite element facts (`S₀,h` onto,
`grad` injective on `P₂Λ⁰ ⊗ V`, the elliptic projection) as hypotheses, and its dynamic-data form
does not carry the `C¹` regularity of `prop_6_2_exists_regular`. For Ch. 7, which matrix the
thesis applies MINRES to is undetermined; both readings are treated. The Ch. 7 plane-wave test
solution satisfies no homogeneous boundary condition and is outside every proved statement.

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
  boundary conditions or tensorial mirror conditions. For the thesis's conditions,
  `Feec.Ch4.BoxIdent` identifies them (real fields, by restriction) with `H̊¹`, `H̊(curl)`,
  `H(curl)`, `H(div)` and `L²(TSD)` of the bounded-domain model on `(0, ½)³`, and carries the results
  to every open cube by `x ↦ a x + b`. The mirror classes are realized as complexes of `L²(Q)`
  fields by compression of the 𝕋³ model (`Feec.Repair.C417Cube`, `Feec.Repair.C419Cube`), with
  the weak `grad`, `curl`, `−div` and, for (4.16), Hessian on `Q`, and carried to every open cube
  by dilation (`Feec.Repair.C417Pi`, `Feec.Repair.C419Pi`); the mirror boundary conditions hold in
  the reflection sense and are not characterized by traces.

The thesis states its Ch. 4 results with boundary conditions on a bounded `Ω` (§4.10, §6.3), so
the bounded-domain modules are the faithful setting; 𝕋³ and ℝ³ have no boundary and serve as a
contrast. Verdicts: Props 4.17 and 4.19 hold on 𝕋³ and ℝ³ and fail on every bounded domain; on
every open cube with the boundary conditions of Prop 4.17 only stationary data propagate, and on
every open cube with mirror conditions both propositions hold (`Feec.Repair.C417`). For the boundary conditions
printed in Prop 4.19 (`symComplexD`), the hypotheses fail, and the conclusion fails on the unit
ball (`Feec.BoundedSymDual`); other domains, and whether its `K*` is nonzero, are not decided. On
a general bounded domain no non-stationary element of `K*` is known; `Feec.Ch4.BoundedKstar`
reduces the question to the existence of a nonzero TSD eigenfield of `curl* curl`, under the
explicit hypothesis `EigenDense` (pure point spectrum), which is proved on 𝕋³ but for no bounded
domain (it needs Rellich–Kondrachov and Maxwell compactness). The Ch. 6 weak-symmetry system on
bounded domains loses TSD and the symmetry of `B` (`Feec.Ch6.Bounded.bggComplex_verdict`), with
homogeneous boundary conditions and zero forcing, and propagates TSD on ℝ³
(`Feec.Ch6.Whole.bggWhole_verdict`), on 𝕋³ and on `(0, ½)³` with mirror conditions
(`Feec.Repair.C417.ch6_corrected`). Not formalized for Ch. 6: the multiplier form (6.2), the
transfer of the failure to the semi-discrete scheme (6.5), and its bearing on Ch. 7, which states
no boundary conditions and whose plane-wave exact solution does not satisfy the homogeneous ones.

Pseudo-Riemannian geometry is done in components at the jet level. Out of scope: the nonlinear
Einstein–Bianchi system (§3.4), the concrete finite element computations of §5.3 (Props 5.7–5.9
beyond the abstract core of Prop 5.7), and the numerical results of Ch. 7. All cited works are
collected in [`references.bib`](references.bib).
