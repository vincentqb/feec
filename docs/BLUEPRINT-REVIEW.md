**Verdict:** the foundation compiles cleanly. The blueprint needs changes before implementation starts. Two problems are the most serious: several [S] claims are false, and a few signatures are trivial or cannot be stated as written.

**Compilation (verified):** I rebuilt §2.1 from the blueprint text into `/tmp/feec_scratch_critic/Foundation.lean` and ran `lake env lean`. It exits 0 in about 18 s, with no errors, no warnings and no `sorry`. `#print axioms` on `orth_range_eq_ker_adjoint`, `energy_zero`, `IsSkewAdjoint.isSkewSymm` and `BGGData.D1_D0` shows only `propext, Classical.choice, Quot.sound`. `/tmp/feec_scratch_architect/Sig.lean` also elaborates, with only "declaration uses sorry" warnings.

**Holes spot-checked against `/tmp/thesis_dl/thesis.txt`:** I found these in the text and they are real.
- "Fredholm ⇒ closed" (l.1895). It is false under the thesis's own definition of Fredholm (finite-dimensional harmonic forms).
- Thm 4.7 cites itself (l.2142).
- Lemma 4.12 assumes Q ∈ C¹ (l.2287), but it is applied to Q = ‖ε_h‖, which is not C¹ where it vanishes (l.2423).
- Prop 2.4(b) gives H = −□h̄ (l.892). That contradicts (2.11), □h̄ = −16πT, together with H = 8πT; the correct form is −½□h̄.
- Prop 6.2 (l.4112). It is a DAE called "square", and φ_h is never shown to be zero.
- Brezzi (l.2229) writes B : Y → X* while defining b(u,q) = Bu(q).
- Thm 4.6 assumes closed range (l.2059), but the proof only needs closure(range d1*) ⊆ ker d0*.
- Thm 4.4 hypothesis (ii) is redundant (l.1944).
- §4.10: discretizations 3 and 4 use P_{r+1}Λ⁰ with P_r⁻Λ¹ (l.2810).
- Thm 4.9: "exists" should be "exists unique"; the dense-range "equivalently" swaps the arguments.
- Thm 4.10 assumes boundedness only on X_h but the proof uses it on X.
- The constant 8πG/c⁴ is stated as about 5·10⁻⁴⁴ (l.556).
- Prop 5.9 is consistent with the claimed scaling counterexample. I checked this by reasoning about the scaling, not by computing the example.

## Required changes

1. **Correct the [S] claim for M3.** `/tmp/feec_scratch_ch3/Biv2.lean` and `Biv3.lean` each have 2 `sorry`s, inside `tracefree_iff`. Only the 16-entry table `h` is proved. Mark `tracefree_iff` (and so `weyl_iff`, `prop_3_1`, `ldual_eq_rdual`) as not done. All the other [S] files I checked have 0 `sorry`; `ch52/*` has 0.

2. **Make Props 6.1(i) non-trivial.** As written, with Λ an arbitrary linear map vanishing on Γ, the statement is trivial: take Λ to be the residual of (6.2). Require the representation Λ(τ,ψ) = ⟨λ, dτ − Sψ⟩ with λ in the stated space (W̌¹, or a completion). Its existence is the actual content, and it needs closed range of (d, −S).

3. **Prop 5.3(b) and Thm 5.5 must not assume their conclusions.** "Poincaré/open-mapping constants as hypotheses" must mean *continuous* constants plus bounded cochain projections. The discrete Poincaré constant has to be derived (the AFW argument), not assumed. `thm_5_5 (…)` has no hypotheses written at all; give a full signature before it counts as Tier A.

4. **Props 4.17/4.19: the "true on 𝕋³" fix is wrong as written.** The hypothesis P_{L²(TSD)} H(curl) ⊂ H(curl) fails on every domain, including 𝕋³. Counterexample: A = e₁(∇f)ᵀ with f = f(x₂) ∈ H¹ \ H². Then A ∈ H(curl) and tr A = 0, but curl of the rows of sym A involves f'', so sym A ∉ H(curl). So the hypothesis is vacuous everywhere. The table should say that, and state that any 𝕋³ result needs a different proof (e.g. Fourier, or the abstract Prop 4.16 route).

5. **Say which theorems are weaker than the thesis.** `IsStrongSolution` drops C⁰([0,T];D(L)) and C¹([0,T];W): it only has pointwise `HasDerivWithinAt`. That makes uniqueness stronger than the thesis. But the existence conclusions of `cor_4_5`, `thm_4_6` and `weak_imp_strong` are weaker than Thm 4.3/4.6/4.7. Either add an `IsClassicalSolution` (continuity of t ↦ L U t and of U′) supplied by the existence hypothesis, or record the weakening in docstrings and the README. Likewise, `IsWeakSolution` on `H.d0.domain` (W-norm subtype) does not capture ξ ∈ C⁰(V).

6. **Add a non-vacuity witness for the existence hypotheses.** Prove `WellPosedHom L T` (and `WellPosedExistence` for continuous F) for an everywhere-defined bounded skew L, via `NormedSpace.exp`. This shows the hypotheses are satisfiable. Optionally derive `WellPosedHom` from the `UnitaryGroupGenerator` structure, so the existence conclusions rest on a recognisable stand-in for Stone's theorem.

7. **Hodge decomposition in W is listed as Tier A but has no signature.** M5 calls it "optional, in M8", and M8 has no signature for it. Add mandatory signatures, in M4 or a new `Ch4/HodgeW.lean` against `HilbertComplex2`:
   - W1 = cl(range d0) ⊕ ℌ ⊕ cl(range d1*), unconditionally;
   - the same without closures under `ClosedRange`;
   - ℌ = ker d1 ⊓ ker d0†;
   - B* = Zᗮ under closed range.

8. **Add a bridge from the unbounded to the bounded model.** Nothing builds a `HilbertComplex` (graph-norm V) from a `UHilbertComplex` or `HilbertComplex2`. Without it, M5's `poincare_iff`, `hodge_V` and closedness results say nothing about the complex used in Thm 4.6/4.7. Add `UHilbertComplex.toHilbertComplex`, the graph inner product on the domain (via the complete graph in `Design.lean`), with `IsClosedAt k ↔ IsClosed (range (d k))` in W.

9. **Fix the compactness results in M5.** `finiteDimensional_H_of_compact` has a placeholder hypothesis ("<sequential compactness of the V∩V* ball>") that cannot be stated in the bounded model, which has no V*. Move it to the W-level model with a precise compact-embedding hypothesis. Also add the missing `isClosedAt_of_compact`: the thesis's actual claim is compactness ⇒ closed, and the blueprint's own fix asserts it, but only finite-dimensional ℌ is planned.

10. **State `fredholm_not_closed` with the project's own definitions.** Give a `HilbertComplex` (or `HilbertComplex2`) instance with `FiniteDimensional (C.H k)` and `¬ C.IsClosedAt k`, using diag(1/(n+1)) on ℓ². A bare operator statement does not formally refute the thesis claim. Document that it fails only under the thesis's definition (finite-dimensional ℌ); under Brüning–Lesch's (finite-dimensional Z/B) the claim holds, which is `isClosedAt_of_finite_cohomology`.

11. **M4: list the missing (4.1) relations explicitly.** (4.1b) (ker T)ᗮ = closure(range T†) and (4.1d) (ker T†)ᗮ = closure(range T) are claimed as covered but have no signatures. Add both, plus the graph relation Γ(T)ᗮ = rotated Γ(T*).

12. **M8 `prop_4_16`: K is undefined.** Define `K := ⊥ ×ˢ H.d0†.ker ×ˢ Y` as a submodule of `Tot` via `tot`. Give `hYinv` a proper subtype form, e.g. `∀ u : H.d1.domain, (u : W1) ∈ H.d0†.domain → H.d1 u ∈ Y`.

13. **Fix the M2 `plane_wave` sign convention.** The Minkowski sum ∑ηᵢ kᵢ kᵢ needs a stated sign convention, η-raised or lowered, to match `Hsym`. Also state the Prop 2.4(a) wave-solver hypothesis as an explicit predicate; at present it appears only in the table.

14. **Add the missing §4.8/§4.9 abstract reduction (Tier B).** Mixed weak Hodge wave on a two-space segment (W⁻¹ = 0) ⇒ second-order weak form (ü,v) = −(du,dv), and the converse under the compatibility condition. This is what the "constant mode / ∫u̇(0)=0" fix relies on. Also generalise `grad_sq_not_whitney` from r = 1 to all r ≥ 1: x₀^{r+1} gives (r+1)x₀^r e₀ ∉ P_r⁻Λ¹, because x·v ≠ 0 on the top-degree part.

15. **Small consistency fixes.**
    - Remove "or golden ratio" from `bigA_bound`, or state the constant actually used, since `ellProj_quasiopt`'s (1+2√12)² depends on it.
    - Document that `HilbertComplex.H k` lives at index k+1, so ℌ⁰ = Z 0 needs its own definition.
    - In §2 conventions, note that `IsSkewAdjoint` uses Mathlib's junk value for non-dense domains. That is what makes `IsSkewAdjoint.dense_domain` provable; keep that lemma as stated.