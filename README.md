# feec

A Lean 4 / Mathlib formalization of the abstract framework from the thesis
*A New Approach to Finite Element Simulations of General Relativity*
(Quenneville-Bélair, 2015): Hilbert complexes, the abstract Hodge wave equation, Brezzi-type
stability, and the BGG construction with weakly imposed symmetries that underlies the
finite element discretization of the linearized Einstein–Bianchi system.

The thesis argues informally in places; here every step is checked by Lean's kernel.
Where the thesis leaves a gap or states a result imprecisely, the formal statement says
exactly what is proved and under which hypotheses. The development contains no `sorry`,
`admit` or `axiom`; every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

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
| `Feec.Ch4.HodgeWave` | §4.4: Thm 4.6, Thm 4.7, weak uniqueness |
| `Feec.Ch4.Galerkin` | §4.5: Thms 4.8–4.11 (Lax–Milgram, Babuška–Nečas, quasi-optimality, Brezzi) |
| `Feec.Ch4.ErrorEstimate` | §4.6: Lemma 4.12, Prop 4.13, elliptic projection, Thm 4.14, convergence |
| `Feec.Ch4.Constraints` | §4.7–4.11: Koszul complexes, wave equations, Props 4.16–4.19 |
| `Feec.Ch4.Torus` | §4.10: Prop 4.17 on the periodic complex over 𝕋³ (Fourier model) |
| `Feec.Ch4.TorusWeak` | §4.10: the Fourier-weight `H¹`, `H(curl)`, `H(div)` on 𝕋³ are the weak-derivative Sobolev spaces |
| `Feec.Ch4.TorusGroup` | §4.3, §4.10: explicit Stone group on 𝕋³, Thm 4.3 (with forcing), existence for Prop 4.17 |
| `Feec.Ch4.TorusSym` | §4.11: complex (4.16) on 𝕋³, closed range and Hodge decomposition, Prop 4.19 with existence |
| `Feec.Ch4.BoundedDomain` | §4.10: the complex `H̊¹ → H̊(curl) → L²` on bounded domains; Prop 4.17 fails there |
| `Feec.Ch5.BGG` | §5.1: Props 5.1–5.2 |
| `Feec.Ch5.Discrete` | §5.2–5.3: Props 5.3, 5.4, 5.6, Thm 5.5, abstract core of Prop 5.7 |
| `Feec.Ch6.TimeDependent` | Ch. 6: Props 6.1–6.3, a convergence theorem |
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
- **Thm 4.14**: it needs `ξ ∈ C¹(V)`, and the `(1 + T)` factor is sharpened (`thm_4_14_pointwise`, `thm_4_14`).
- **§4.10**: two of the four proposed discretizations are not subcomplexes (`pgrad_not_mem_PminusLambda1`).
- **Props 4.17, 4.19**: the density conjectures are unnecessary (`prop_4_17`), and the projection hypothesis is necessary for the conclusion (`prop_4_17_necessary`, `prop_4_17_iff`). On 𝕋³ the projection conjecture is a theorem (`projTSD_mem_H1`, `projKc_mem_domL`), and Props 4.17 and 4.19 hold with no extra hypothesis, with existence of solutions (`prop_4_17_torus_exists`, `prop_4_19_torus_exists`). On every nonempty bounded open `Ω ⊆ ℝ³` the projection conjecture is false for the thesis's complex, so Prop 4.17 is vacuous as stated (`thesisComplex_not_projection_hyp`); assuming the unitary group of Thm 4.3 (Stone's theorem, not constructed on bounded domains), its conclusion fails for explicit TSD data (`thesisComplex_orbit_not_propagate`). The proof's step from the density hypothesis to density of `H̊(curl) ∩ L²(TSD)` in `L²(TSD)` is invalid (`not_dense_TSD_inter_HcurlZero`).
- **(5.1)**: exactness at `Ṽ¹` is used but never proved (`exact_mid`).
- **Prop 5.4**: exactness at `V_h¹` cannot be dropped (`prop54_counterexample_noTopExact`).
- **Prop 6.2**: false as stated; it holds exactly under compatibility conditions (C1)–(C3) (`prop_6_2_false`, `prop_6_2`).
- **Ch. 7**: MINRES does not apply to the unsymmetrized Crank–Nicolson matrix; a sign change symmetrizes it (`minres_symm`).

## Scope

The thesis's analytic existence results are taken as explicit hypotheses, never as axioms,
because Mathlib lacks C₀-semigroups and the Hille–Yosida and Stone theorems. Existence for
evolution problems enters as `WellPosedExistence` or `WellPosedHom` (standing for Thm 4.3).
`Feec.Ch4.Existence` shows these hypotheses hold for bounded generators, and
`Feec.Ch4.TorusGroup` and `Feec.Ch4.TorusSym` construct the groups for the periodic complexes;
on bounded domains the group is still a hypothesis.
Uniqueness, energy conservation and constraint propagation are proved. Mathlib also has no
Sobolev spaces on domains, traces or finite element spaces. Concrete complexes (de Rham,
`H(curl)`, `H(div)`, polynomial finite element spaces) therefore enter only as instances of
abstract structures, with their analytic facts (closed range, bounded cochain projections,
density, regular decompositions) as hypotheses. The exception is `Feec.Ch4.Torus`, which
models fields on 𝕋³ by their Fourier coefficients (a proved isometry `L²(𝕋³) ≃ ℓ²(ℤ³)`) and
defines `H¹`, `H(curl)` and `H(div)` by Fourier weights; `Feec.Ch4.TorusWeak` proves these are
the weak-derivative Sobolev spaces. `Feec.Ch4.BoundedDomain` builds `H̊¹`, `H̊(curl)` and `H(div)`
on bounded domains from their definitions (graph closures and weak derivatives), with
`L²(Ω; ℝ³ˣ³)` modelled as nine copies of `L²(Ω)`. Pseudo-Riemannian geometry is done in components at the jet
level. Lemma 3.5 is proved on bounded domains in distributional form for fields with the
`H̊(curl)` boundary condition: `curl B` is symmetric for `B ∈ L²(TSD) ∩ H̊(curl)`
(`Feec.BoundedDomain.curl_symm_of_mem_TSD`), and `curl` maps `H̊(curl, S) ∩ L²(TSD)` into
`L²(TSD)` (`Feec.BoundedSym.curlS_mem_TSDT`; the adjoint version is `adjoint_curlS_mem_TSDS`).
Out of scope: the nonlinear Einstein–Bianchi system (§3.4), Lemma 3.5 on bounded domains for
fields in `H(curl)` without a boundary condition (`Feec.BoundedDomain.HcurlM`), Prop 3.6 on
bounded domains, the concrete finite element computations of §5.3 (Props 5.7–5.9 beyond the
abstract core of Prop 5.7), and the numerical results of Ch. 7. All cited works are collected in
[`docs/references.bib`](docs/references.bib).

## Citing

```bibtex
@software{QuennevilleBelair_feec,
  author  = {Quenneville-B{\'e}lair, Vincent},
  title   = {feec: A Lean formalization of finite element exterior calculus for the Einstein--Bianchi system},
  year    = {2026},
  url     = {https://github.com/vincentqb/feec}
}
```

## References

```bibtex
@phdthesis{QuennevilleBelair2015,
  author  = {Quenneville-B{\'e}lair, Vincent},
  title   = {A New Approach to Finite Element Simulations of General Relativity},
  school  = {University of Minnesota},
  year    = {2015},
  month   = jun,
  url     = {https://www-users.cse.umn.edu/~arnold/papers/QuennevilleThesis.pdf}
}

@book{Arnold2018FEEC,
  author    = {Arnold, Douglas N.},
  title     = {Finite Element Exterior Calculus},
  series    = {CBMS-NSF Regional Conference Series in Applied Mathematics},
  volume    = {93},
  publisher = {Society for Industrial and Applied Mathematics},
  address   = {Philadelphia, PA},
  year      = {2018},
  doi       = {10.1137/1.9781611975543},
  isbn      = {978-1-611975-53-6}
}
```
