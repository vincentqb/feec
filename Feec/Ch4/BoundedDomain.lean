module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.CrossProduct
public import Feec.Ch4.Constraints
public import Feec.Models.BoundedDomain.GradCurl

/-!
# Thesis Prop 4.17 on bounded domains: the projection hypothesis and TSD propagation fail

Prop 4.17 ([QuennevilleBelair2015, §4.10]) propagates the TSD constraint (symmetric, trace-free,
divergence-free) for the matrix Hodge wave (4.14) of the complex
`H̊¹(V) → H̊(curl, M) → L²(M)` on a bounded contractible `Ω ⊆ ℝ³`. Its hypotheses are the
"conjectures" `P_{L²(TSD)} (H̊(curl, M) ∩ H(div, M)) ⊆ H̊(curl, M) ∩ H(div, M)`,
`P_{L²(TSD)} H(curl, M) ⊆ H(curl, M)`, and "`H̊(curl, M) ∩ H(div, M, 0)` is dense in
`H(div, M, 0)`" (plus the same with `H(curl, M)`), from which the proof infers
"`H̊(curl, M) ∩ L²(TSD)` is dense in `L²(TSD)`". `Feec.Constraints.prop_4_17` proves the abstract
statement under the projection hypothesis; `Feec.Ch4.Torus` proves the hypothesis and Prop 4.17 on
the flat torus. This file settles the bounded case, on every nonempty bounded open `Ω ⊆ ℝ³`
(contractible or not; e.g. the cube `(0, π)³` or a ball), for the thesis' complex itself
(`thesisComplex`, with `d0 = grad` on `H̊¹` and `d1 = curl` on `H̊(curl)`):
* the first projection hypothesis is **false**, so Prop 4.17 as stated is vacuously true;
* the literal density hypothesis is **true** (in every Hilbert complex), but the inferred density
  of `H̊(curl, M) ∩ L²(TSD)` in `L²(TSD)` is **false**;
* the **conclusion** of Prop 4.17 fails: there is TSD data in `D(L)` for which no strong solution
  of (4.14) stays TSD, and the Stone-group orbit (Thm 4.3) is such a solution leaving `K`. The
  group exists by Stone's theorem (`Feec.stoneGroup`), so this holds with no hypothesis
  (`thesisComplex_orbit_not_propagate_unconditional` in `Feec.Ch4.StoneApplications`).

## The mathematics

1. *Pointwise boundary lemma* (`eq_zero_of_symm_of_trace_of_cross`): if `M` is symmetric,
   `tr M = 0` and every row of `M` has zero tangential part for a unit normal `n`
   (`n × M_i = 0`), then `M = 0` (`M = λ nᵀ`, symmetry gives `M = μ n nᵀ`, trace gives `μ = 0`).
   So a smooth TSD field in `H̊(curl)` vanishes on `∂Ω`, and `∫_Ω B : ∇v = ∫_{∂Ω} (B n)·v = 0`.
2. *Integrated form without traces or regularity* (`integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`):
   every `B ∈ L²(TSD) ∩ H̊(curl)` has zero mean, `∫_Ω B = 0`. Let `C = curl B`. Testing the graph
   closure of curl against `skewOf ψ` (rows `e_j × ψ`), whose curl is `e_j div ψ - ∂_j ψ`
   (`curlM_skewOf`), shows that `C` is symmetric (`curl_symm_of_mem_TSD`; the distributional
   form of part of Lemma 3.5, via the fundamental lemma `L2_ext_of_integral`). Then, for the
   *linear* field `v = x_a e_b` (no boundary condition),
   `0 = ∫ C : skewOf v = ∫ B : curl (skewOf v) = δ_{ab} ∫ tr B - ∫ B_{ab} = -∫ B_{ab}`.
3. *Counterexample to the projection hypothesis* (`projTSD_not_mem_HcurlZero`,
   `exists_projTSD_not_mem_HcurlZero`): constant symmetric trace-free fields `A` lie in `L²(TSD)`
   (no boundary condition), so `⟪P_TSD E, A⟫ = ⟪E, A⟫`. For `E = g · diag(1, -1, 0)` with a bump
   `g ≥ 0`, `g ≠ 0`, we have `E ∈ C_c^∞ ⊆ H̊(curl) ∩ H(div)` and `⟪E, A⟫ = 2 ∫ g > 0`, so
   `P_TSD E` has nonzero mean and `P_TSD E ∉ H̊(curl)`. (`P_TSD` is nonlocal: `E` is compactly
   supported but `P_TSD E` is not, and it does not vanish on `∂Ω`.)
4. *Density* (`dense_domain_d1_inter_ker_adj0`, `not_dense_TSD_inter_HcurlZero`): in any Hilbert
   complex `P_{ker d0*}` maps `D(d1)` into itself, since `(ker d0*)ᗮ = closure (range d0) ⊆ ker d1`;
   so `D(d1) ∩ ker d0*` is dense in `ker d0*`. But `H̊(curl) ∩ L²(TSD)` lies in the closed
   subspace of zero-mean fields, which misses `diag(1, -1, 0) ∈ L²(TSD)`.
5. *TSD propagation fails* (`exists_data_not_propagate`): for the TSD datum `(0, 0, β)`,
   `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ) ∈ H(curl) ∩ L²(TSD)`, the functional `ℓ(E) = ⟪E, diag(1, -1, 0)⟫`
   vanishes on `K ∩ D(L)`, but `d/dt ℓ(E)|₀ = ℓ(-curl β) = ℓ(diag(1, -1, 0)) = 2|Ω| ≠ 0`
   (`curlM_betaField`). Hence every strong solution leaves `K` immediately.
6. *The thesis' complex* (`thesisComplex`): `grad` is the graph closure of the row-wise gradient
   on `C_c^∞(Ω; ℝ³)` (`gradClosure`, closable by the fundamental lemma); `curl grad = 0` on
   `C_c^∞` (Schwarz, `pd_pd_comm`) passes to the closures, so `grad H̊¹ ⊆ ker curl`;
   `D(grad*) = H(div)` with `grad* = -div` (`mem_adjoint_gradClosure_iff`) and
   `ker grad* = H(div, 0) ⊇ L²(TSD)` (`mem_ker_adjoint_gradClosure_iff`,
   `thesisComplex_TSD_le_ker`).

## Model

`Ω ⊆ ℝ³ = Fin 3 → ℝ` is open and bounded, with Lebesgue measure. `L²(Ω; ℝ³ˣ³)` is `L2M Ω`, the
`ℓ²`-sum of nine copies of `L²(Ω)`, and `L²(Ω; ℝ³)` is `L2V Ω` (three copies); these are
canonically isometric to the Bochner spaces with the Frobenius/Euclidean norms (the isometry is
`piL2Equiv` in `Feec.Ch4.BoundedDomainExt`). Spaces are defined honestly, by their standard definitions:
* `C_c^∞(Ω)`: `IsTest` (smooth, compact support inside `Ω`); `pd k` is `∂_k` (`fderiv`).
* `H̊¹(Ω; ℝ³)`: the domain of `gradClosure`, the closure of `C_c^∞(Ω; ℝ³)` in the graph norm of
  the row-wise gradient `(grad φ)_{ij} = ∂_j φ_i`.
* `H̊(curl, M)`: `HcurlZero`, the closure of `C_c^∞(Ω; ℝ³ˣ³)` in the graph norm of the
  row-wise curl `curlM` (thesis convention `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`);
  `curlClosure` is the corresponding closed, densely defined operator (`isClosed_curlClosure`,
  `dense_domain_curlClosure`, `mem_domain_curlClosure`).
* `H(div, M)`: `HdivM`, fields with a weak row-wise divergence in `L²`; `H(div, M, 0)`:
  `HdivZero`, weakly divergence-free fields (no boundary condition).
* `L²(TSD)`: `TSD`, symmetric, trace-free and weakly divergence-free in `Ω`, no boundary
  condition; a closed subspace (`isClosed_TSD`), so `P_{L²(TSD)}` is `(TSD Ω).starProjection`.

## Main results

* `eq_zero_of_symm_of_trace_of_cross` (pointwise lemma), `curl_symm_of_mem_TSD`,
  `integral_eq_zero_of_mem_TSD_of_mem_HcurlZero` (zero mean).
* `projTSD_not_mem_HcurlZero`, `exists_projTSD_not_mem_HcurlZero` (projection hypothesis false),
  `not_dense_TSD_inter_HcurlZero` (inferred density false), `dense_domain_d1_inter_ker_adj0`
  (literal density true in any Hilbert complex).
* For any Hilbert complex `H : W0 → L²(Ω; ℝ³ˣ³) → W2` with `D(d1) ⊆ H̊(curl)`:
  `not_projection_hyp` (the hypothesis `hPD` of `Feec.Constraints.prop_4_17` fails, if
  `C_c^∞ ⊆ V1 ∩ V1*`) and `not_dense_domL_inter_Kc` (the density hypothesis of
  `Feec.Constraints.prop_4_17_iff` fails). If moreover `W2 = L²(Ω; ℝ³ˣ³)` and `d1` is (a
  restriction of) `curlClosure`: `smoothField_mem_adjoint` (`d1* ⊇ curl` on `C¹` fields),
  `exists_data_not_propagate` (every strong solution from `(0, 0, β)` leaves `K`) and
  `exists_orbit_not_propagate` (given a Stone group, its orbit is such a solution).
* The thesis' complex `thesisComplex` (`H̊¹ → H̊(curl) → L²`): `thesisComplex_TSD_le_ker`,
  `thesisComplex_dense_literal`, `thesisComplex_not_projection_hyp`,
  `thesisComplex_not_propagate`, `thesisComplex_orbit_not_propagate`. The simpler
  `curlComplex` (`0 → H̊(curl) → L²`) satisfies the same hypotheses.

## Correction

The first projection hypothesis of Prop 4.17 is false on bounded domains, so the proposition as
stated is vacuously true; its conclusion is false: there is TSD initial data in `D(L)` for which
no strong solution of (4.14) stays TSD, and the orbit of the unitary group of `-L` (Thm 4.3,
which exists by Stone's theorem) is a strong solution leaving `K`. The obstruction is global: `H̊(curl) ∩ L²(TSD)` fields have zero
mean, while `L²(TSD)` contains constants and `curl` does not preserve the zero-mean condition on
`H(curl)` (no boundary condition on `B`). On the torus the hypothesis holds
(`Feec.Torus.prop_4_17_torus`).

Thesis gap: the density hypothesis "`H̊(curl, M) ∩ H(div, M, 0)` is dense in `H(div, M, 0)`" is
true, but the step "so that `H̊(curl, M) ∩ L²(TSD)` is dense in `L²(TSD)`" in the proof of
Prop 4.17 is invalid (its conclusion is false); and with the electric boundary condition the
constraint set `K` is not invariant, so Theorem 4.5 does not apply.

In this file the non-vacuous refutations `exists_orbit_not_propagate` and
`thesisComplex_orbit_not_propagate` take the group as the hypothesis
`G : Feec.UnitaryGroupGenerator (-L)`, while `exists_data_not_propagate` and
`thesisComplex_not_propagate` quantify over all strong solutions. The group hypothesis is
discharged by Stone's theorem (`Feec.stoneGroup`, `Feec.Ch4.Stone`):
`exists_orbit_not_propagate_unconditional` and `thesisComplex_orbit_not_propagate_unconditional`
(`Feec.Ch4.StoneApplications`) need no hypothesis beyond `Ω` nonempty, bounded and open.
Prop 4.19 on bounded domains is treated in `Feec.Ch4.BoundedSym`, and the salvage (the maximal
invariant constraint space and the infinite-dimensional obstruction) in `Feec.Ch4.BoundedSalvage`,
`Feec.Ch4.BoundedSalvageMax` and `Feec.Ch4.BoundedSalvageDim`; the density question in
`Feec.Ch4.BoundedDensity`; interior propagation at unit speed in `Feec.Ch4.BoundedInterior`; the
box `(0, ½)³` in a parity model in `Feec.Ch4.BoxThesis` and `Feec.Ch4.BoxMirror`. The second
projection hypothesis `P_{L²(TSD)} H(curl, M) ⊆ H(curl, M)` is also false on every nonempty bounded open `Ω`, and `D(curl*) = H(curl, M)` exactly; both are proved in
`Feec.Ch4.BoundedDomainExt` (`thesisComplex_not_projection_hyp2`, `mem_adjoint_curlClosure_iff`).

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.10 (Prop 4.17, (4.14), Theorem 4.5)
* [ACBY1997] (the Einstein–Bianchi system)
* [Brezis2011] (Sobolev spaces, the fundamental lemma of the calculus of variations)
* [AFW2010], [BruningLesch1992] (Hilbert complexes)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal ContDiff Matrix
open MeasureTheory Set Filter Topology

namespace Feec.BoundedDomain

/-! ## The pointwise boundary lemma -/

/-- **Pointwise boundary lemma.** A symmetric, trace-free `3 × 3` matrix whose rows all have
zero tangential component for a unit vector `n` (`n × M_i = 0`) vanishes. Hence a TSD field with
zero tangential trace (the `H̊(curl)` boundary condition) vanishes on `∂Ω` wherever it has a
trace; `integral_eq_zero_of_mem_TSD_of_mem_HcurlZero` is the trace-free integrated form.

See [QuennevilleBelair2015, §4.10, Prop 4.17] (the conjecture this refutes). -/
theorem eq_zero_of_symm_of_trace_of_cross (M : Matrix (Fin 3) (Fin 3) ℝ) (n : Fin 3 → ℝ)
    (hn : n ⬝ᵥ n = 1) (hsym : Mᵀ = M) (htr : M.trace = 0) (hcross : ∀ i, n ⨯₃ M i = 0) :
    M = 0 := by
  have hn' : n 0 * n 0 + n 1 * n 1 + n 2 * n 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three] using hn
  have key : ∀ i j, M i j = (n 0 * M i 0 + n 1 * M i 1 + n 2 * M i 2) * n j := by
    intro i j
    have h := hcross i
    rw [cross_apply] at h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    have e2 := congrFun h 2
    simp at e0 e1 e2
    fin_cases j
    · simp; linear_combination (-M i 0) * hn' - n 1 * e2 + n 2 * e1
    · simp; linear_combination (-M i 1) * hn' + n 0 * e2 - n 2 * e0
    · simp; linear_combination (-M i 2) * hn' - n 0 * e1 + n 1 * e0
  have hs : ∀ i j, M i j = M j i := fun i j => by
    rw [← Matrix.transpose_apply M j i, hsym]
  have htr' : M 0 0 + M 1 1 + M 2 2 = 0 := by simpa [Matrix.trace, Fin.sum_univ_three] using htr
  set l : Fin 3 → ℝ := fun i => n 0 * M i 0 + n 1 * M i 1 + n 2 * M i 2 with hl
  have key' : ∀ i j, M i j = l i * n j := key
  have hl0 : ∀ i, l i = 0 := by
    intro i
    have h1 : l i = n 0 * M 0 i + n 1 * M 1 i + n 2 * M 2 i := by
      rw [hl]; simp only; rw [hs i 0, hs i 1, hs i 2]
    rw [key' 0 i, key' 1 i, key' 2 i] at h1
    rw [key' 0 0, key' 1 1, key' 2 2] at htr'
    linear_combination h1 + n i * htr'
  ext i j
  rw [key' i j, hl0 i, zero_mul]; rfl

/-! ## Test functions, partial derivatives, row-wise curl -/

/-- Points of `ℝ³`. -/
abbrev R3 := Fin 3 → ℝ

/-- Index pairs `(i, j)` of `3 × 3` matrices. -/
abbrev Ix := Fin 3 × Fin 3

/-- The partial derivative `∂_k f`. -/
def pd (k : Fin 3) (f : R3 → ℝ) (x : R3) : ℝ := fderiv ℝ f x (Pi.single k 1)

/-- The row-wise curl of a matrix field given by its components `Φ (i, j)`:
`(curl Φ)_{ik} = ∂_{k+1} Φ_{i,k+2} - ∂_{k+2} Φ_{i,k+1}` (indices mod 3), i.e. the thesis'
`(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`. -/
def curlM (Φ : Ix → R3 → ℝ) (ik : Ix) (x : R3) : ℝ :=
  pd (ik.2 + 1) (Φ (ik.1, ik.2 + 2)) x - pd (ik.2 + 2) (Φ (ik.1, ik.2 + 1)) x

/-- `f ∈ C_c^∞(Ω)`: smooth, compactly supported, with support in `Ω`. -/
structure IsTest (Ω : Set R3) (f : R3 → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ f
  hasCompactSupport : HasCompactSupport f
  tsupport_subset : tsupport f ⊆ Ω

/-- Partial derivatives of `C¹` functions are continuous. -/
theorem continuous_pd {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (k : Fin 3) : Continuous (pd k f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The curl of a `C¹` field is continuous. -/
theorem continuous_curlM {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (ij : Ix) :
    Continuous (curlM Ψ ij) :=
  (continuous_pd (hΨ _) _).sub (continuous_pd (hΨ _) _)

namespace IsTest

variable {Ω : Set R3} {f : R3 → ℝ}

/-- Test functions are `C¹`. -/
theorem contDiff_one (hf : IsTest Ω f) : ContDiff ℝ 1 f := hf.contDiff.of_le (by simp)

/-- Test functions are continuous. -/
theorem continuous (hf : IsTest Ω f) : Continuous f := hf.contDiff.continuous

/-- Test functions are differentiable. -/
theorem differentiable (hf : IsTest Ω f) : Differentiable ℝ f :=
  hf.contDiff_one.differentiable one_ne_zero

/-- Partial derivatives of test functions are test functions. -/
theorem pdiff (hf : IsTest Ω f) (k : Fin 3) : IsTest Ω (pd k f) where
  contDiff := (hf.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  hasCompactSupport := HasCompactSupport.fderiv_apply ℝ hf.hasCompactSupport _
  tsupport_subset := (tsupport_fderiv_apply_subset _ _).trans hf.tsupport_subset

/-- Test functions vanish off `Ω`. -/
theorem eq_zero_of_notMem (hf : IsTest Ω f) {x : R3} (hx : x ∉ Ω) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hf.tsupport_subset h)

/-- Test functions are in `L²(Ω)`. -/
theorem memLp (hf : IsTest Ω f) : MemLp f 2 (volume.restrict Ω) :=
  hf.continuous.memLp_of_hasCompactSupport hf.hasCompactSupport

/-- `0 ∈ C_c^∞(Ω)`. -/
theorem zero : IsTest Ω (0 : R3 → ℝ) := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

/-- `C_c^∞(Ω)` is closed under addition. -/
theorem add {g : R3 → ℝ} (hf : IsTest Ω f) (hg : IsTest Ω g) : IsTest Ω (f + g) :=
  ⟨hf.contDiff.add hg.contDiff, hf.hasCompactSupport.add hg.hasCompactSupport,
    (tsupport_add f g).trans (union_subset hf.tsupport_subset hg.tsupport_subset)⟩

/-- `C_c^∞(Ω)` is closed under scalar multiplication. -/
theorem const_mul (hf : IsTest Ω f) (c : ℝ) : IsTest Ω (fun x => c * f x) :=
  ⟨contDiff_const.mul hf.contDiff, hf.hasCompactSupport.mul_left,
    tsupport_mul_subset_right.trans hf.tsupport_subset⟩

end IsTest

/-- Test functions here are `Feec.Domain` test functions. -/
theorem IsTest.toDomain {Ω : Set R3} {f : R3 → ℝ} (hf : IsTest Ω f) : Feec.Domain.IsTest Ω f :=
  ⟨hf.1, hf.2, hf.3⟩

theorem IsTest.ofDomain {Ω : Set R3} {f : R3 → ℝ} (hf : Feec.Domain.IsTest Ω f) : IsTest Ω f :=
  ⟨hf.1, hf.2, hf.3⟩

theorem isTestField_of_forall {Ω : Set R3} {ι : Type*} {Φ : ι → R3 → ℝ}
    (hΦ : ∀ i, IsTest Ω (Φ i)) : Feec.Domain.IsTestField Ω Φ := fun i => (hΦ i).toDomain

/-- The row-wise curl is the constant-coefficient operator `Feec.Domain.curlOp 3`. -/
theorem curlM_eq_apply (Φ : Ix → R3 → ℝ) :
    curlM Φ = (Feec.Domain.curlOp 3 : Feec.Domain.ConstCoeffOp R3 ℝ Ix Ix).apply Φ := by
  funext ik x
  rw [Feec.Domain.curlOp_apply]
  rfl

/-! ## `L²` spaces on a domain -/

variable (Ω : Set R3)

/-- `L²(Ω)` (Lebesgue measure restricted to `Ω`). -/
abbrev L2 := Lp ℝ 2 (volume.restrict Ω)

/-- `L²(Ω; ℝ³ˣ³)`, as the `ℓ²`-sum of nine copies of `L²(Ω)` (canonically isometric). -/
abbrev L2M := PiLp 2 (fun _ : Ix => L2 Ω)

/-- `L²(Ω; ℝ³)`, as the `ℓ²`-sum of three copies of `L²(Ω)`. -/
abbrev L2V := PiLp 2 (fun _ : Fin 3 => L2 Ω)

variable {Ω}

/-- Continuous functions on `ℝ³` are in `L²(Ω)` for bounded open `Ω`. -/
theorem memLp_of_continuous (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f : R3 → ℝ}
    (hf : Continuous f) : MemLp f 2 (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem hΩ.measurableSet fun x hx => hC x (subset_closure hx))

/-- `∫_Ω f g = ⟪f, g⟫_{L²(Ω)}`. -/
theorem integral_mul_eq_inner (f : L2 Ω) {g : R3 → ℝ} (hg : MemLp g 2 (volume.restrict Ω)) :
    ∫ x, f x * g x ∂volume.restrict Ω = ⟪f, hg.toLp g⟫ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx, Real.inner_apply]

/-- Products of `L²(Ω)` functions are integrable on `Ω`. -/
theorem integrable_mul (f : L2 Ω) {g : R3 → ℝ} (hg : MemLp g 2 (volume.restrict Ω)) :
    Integrable (fun x => f x * g x) (volume.restrict Ω) := by
  refine (L2.integrable_inner f (hg.toLp g)).congr ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx, Real.inner_apply]

/-! ## Integration by parts -/

/-- A function vanishing off `Ω` has the same integral over `Ω` and over `ℝ³`. -/
theorem integral_restrict_of_eq_zero {f : R3 → ℝ} (hf : ∀ x, x ∉ Ω → f x = 0) :
    ∫ x, f x ∂volume.restrict Ω = ∫ x, f x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero hf

/-- Integration by parts against a test function: `∫ ∂_k f g = -∫ f ∂_k g`. -/
theorem integral_pd_mul {f g : R3 → ℝ} (hf : IsTest Ω f) (hg : ContDiff ℝ 1 g) (k : Fin 3) :
    ∫ x, pd k f x * g x ∂volume.restrict Ω = -∫ x, f x * pd k g x ∂volume.restrict Ω := by
  have h0 : ∀ x, x ∉ Ω → pd k f x * g x = 0 := fun x hx => by
    rw [(hf.pdiff k).eq_zero_of_notMem hx, zero_mul]
  have h1 : ∀ x, x ∉ Ω → f x * pd k g x = 0 := fun x hx => by
    rw [hf.eq_zero_of_notMem hx, zero_mul]
  rw [integral_restrict_of_eq_zero h0, integral_restrict_of_eq_zero h1]
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f) (g := g)
    (v := Pi.single k 1)
    (((continuous_pd hf.contDiff_one k).mul hg.continuous).integrable_of_hasCompactSupport
      ((hf.pdiff k).hasCompactSupport.mul_right))
    ((hf.continuous.mul (continuous_pd hg k)).integrable_of_hasCompactSupport
      hf.hasCompactSupport.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      hf.hasCompactSupport.mul_right)
    (fun x _ => hf.differentiable x) (fun x _ => hgd x)
  simp only [pd]
  rw [this, neg_neg]

/-- A compactly supported continuous function times a continuous one is integrable. -/
theorem integrable_mul_of_compact {f g : R3 → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) : Integrable (fun x => f x * g x) (volume.restrict Ω) :=
  ((hf.mul hg).integrable_of_hasCompactSupport hfc.mul_right).restrict

/-- `curl` is symmetric between a compactly supported field and a `C¹` field:
`∫ curl Φ : Ψ = ∫ Φ : curl Ψ`. -/
theorem sum_integral_curlM_mul {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij))
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ∑ ij, ∫ x, curlM Φ ij x * Ψ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, Φ ij x * curlM Ψ ij x ∂volume.restrict Ω := by
  set a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun i k l m =>
    ∫ x, Φ (i, k) x * pd l (Ψ (i, m)) x ∂volume.restrict Ω with ha
  have hL : ∀ i k, ∫ x, curlM Φ (i, k) x * Ψ (i, k) x ∂volume.restrict Ω =
      -a i (k + 2) (k + 1) k + a i (k + 1) (k + 2) k := by
    intro i k
    simp only [curlM, sub_mul]
    rw [integral_sub, integral_pd_mul (hΦ _) (hΨ _), integral_pd_mul (hΦ _) (hΨ _)]
    · simp only [ha]; ring
    · exact integrable_mul_of_compact (continuous_pd (hΦ _).contDiff_one _)
        ((hΦ _).pdiff _).hasCompactSupport (hΨ _).continuous
    · exact integrable_mul_of_compact (continuous_pd (hΦ _).contDiff_one _)
        ((hΦ _).pdiff _).hasCompactSupport (hΨ _).continuous
  have hR : ∀ i k, ∫ x, Φ (i, k) x * curlM Ψ (i, k) x ∂volume.restrict Ω =
      a i k (k + 1) (k + 2) - a i k (k + 2) (k + 1) := by
    intro i k
    simp only [curlM, mul_sub]
    rw [integral_sub]
    · exact integrable_mul_of_compact (hΦ _).continuous (hΦ _).hasCompactSupport
        (continuous_pd (hΨ _) _)
    · exact integrable_mul_of_compact (hΦ _).continuous (hΦ _).hasCompactSupport
        (continuous_pd (hΨ _) _)
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, hL, hR]
  simp only [Fin.isValue, Fin.reduceAdd]
  ring

/-! ## The spaces `H̊(curl)`, `H(div)` and `L²(TSD)` on `Ω` -/

variable (Ω) in
/-- The graph of the row-wise curl on `C_c^∞(Ω; ℝ³ˣ³)`, as a subset of `L²(Ω; ℝ³ˣ³)²`. -/
def curlGraph : Set (L2M Ω × L2M Ω) :=
  {p | ∃ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) ∧
    ∀ ij, (p.1 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] Φ ij ∧
      (p.2 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] curlM Φ ij}

/-- The curl graph is the test graph of `Feec.Domain.curlOp 3`. -/
theorem curlGraph_eq_testGraph :
    curlGraph Ω = ((Feec.Domain.curlOp 3 : Feec.Domain.ConstCoeffOp R3 ℝ Ix Ix).testGraph Ω :
      Set (L2M Ω × L2M Ω)) := by
  ext ⟨u, c⟩
  constructor
  · rintro ⟨Φ, hΦ, hp⟩
    have hΦ' : Feec.Domain.IsTestField Ω Φ := fun ij => (hΦ ij).toDomain
    refine ⟨Φ, hΦ', ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨Feec.Domain.eq_testField hΦ' fun ij => (hp ij).1,
      Feec.Domain.eq_testField _ fun ij => by rw [← curlM_eq_apply]; exact (hp ij).2⟩
  · rintro ⟨Φ, hΦ, h⟩
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Φ, fun ij => IsTest.ofDomain (hΦ ij), fun ij => ⟨Feec.Domain.coeFn_testField hΦ ij, by
      rw [curlM_eq_apply]; exact Feec.Domain.coeFn_testField _ ij⟩⟩

variable (Ω) in
/-- `H̊(curl, Ω; ℝ³ˣ³)`: the closure of `C_c^∞(Ω; ℝ³ˣ³)` in the graph norm of the row-wise curl,
i.e. the fields `B` such that `(B, C)` is an `L²`-limit of `(Φₙ, curl Φₙ)`, `Φₙ ∈ C_c^∞`. -/
def HcurlZero : Set (L2M Ω) := {B | ∃ C, (B, C) ∈ closure (curlGraph Ω)}

/-- `H̊(curl)` is the domain of the minimal realization of the row-wise curl. -/
theorem mem_HcurlZero_iff_minimal {B : L2M Ω} :
    B ∈ HcurlZero Ω ↔ B ∈ ((Feec.Domain.curlOp 3 : Feec.Domain.ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain := by
  rw [Feec.Domain.ConstCoeffOp.minimal, Submodule.toLinearPMap_domain, Submodule.mem_map, HcurlZero,
    mem_ofPred_eq, curlGraph_eq_testGraph, ← Submodule.topologicalClosure_coe]
  constructor
  · rintro ⟨C, h⟩
    exact ⟨(B, C), h, rfl⟩
  · rintro ⟨⟨B', C⟩, h, rfl⟩
    exact ⟨C, h⟩

variable (Ω) in
/-- `H(div, Ω; ℝ³ˣ³)` (row-wise divergence, no boundary condition): `B` has a weak divergence
`D ∈ L²(Ω; ℝ³)`, `∫ Σ_{ij} B_{ij} ∂_j φ_i = -∫ Σ_i D_i φ_i` for all `φ ∈ C_c^∞(Ω; ℝ³)`. -/
def HdivM : Set (L2M Ω) :=
  {B | ∃ D : L2V Ω, ∀ φ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (φ i)) →
    ∑ ij : Ix, ∫ x, B ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
      -∑ i, ∫ x, D i x * φ i x ∂volume.restrict Ω}

/-- The defining identity of the closure of the curl graph, tested against a `C¹` field `Ψ`
(no boundary condition on `Ψ`): `∫ C : Ψ = ∫ B : curl Ψ`. -/
theorem closure_curlGraph_identity (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B C : L2M Ω}
    (h : (B, C) ∈ closure (curlGraph Ω)) {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ∑ ij, ∫ x, C ij x * Ψ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, B ij x * curlM Ψ ij x ∂volume.restrict Ω := by
  have m1 : ∀ ij, MemLp (Ψ ij) 2 (volume.restrict Ω) := fun ij =>
    memLp_of_continuous hΩ hb (hΨ ij).continuous
  have m2 : ∀ ij, MemLp ((Feec.Domain.curlOp 3 : Feec.Domain.ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply
      Ψ ij) 2 (volume.restrict Ω) := fun ij => by
    rw [Feec.Domain.curlOp_formalAdj_apply, ← curlM_eq_apply]
    exact memLp_of_continuous hΩ hb (continuous_curlM hΨ ij)
  rw [curlGraph_eq_testGraph, ← Submodule.topologicalClosure_coe] at h
  have := (Feec.Domain.curlOp 3 : Feec.Domain.ConstCoeffOp R3 ℝ Ix Ix).closure_testGraph_inner
    (N := 1) Feec.Domain.curlOp_isOrderLE h (fun ij => (hΨ ij).of_le (by norm_num)) m1 m2
  rw [Feec.Domain.inner_toL2F, Feec.Domain.inner_toL2F] at this
  simpa only [Feec.Domain.curlOp_formalAdj_apply, ← curlM_eq_apply, RCLike.conj_to_real]
    using this

/-- Continuity of a component `B ↦ B_{ij}`. -/
theorem continuous_component (ij : Ix) : Continuous fun B : L2M Ω => B ij :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Ix => L2 Ω) ij).continuous

/-- The divergence pairing `∫ Σ_{ij} B_{ij} ∂_j φ_i` as a sum of `L²` inner products. -/
theorem divPairing_eq {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Ω (φ i)) (B : L2M Ω) :
    ∑ ij : Ix, ∫ x, B ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
      ∑ ij : Ix, ⟪B ij, ((hφ ij.1).pdiff ij.2).memLp.toLp _⟫ :=
  Finset.sum_congr rfl fun _ _ => integral_mul_eq_inner _ _

variable (Ω) in
/-- `L²(TSD)`: symmetric, trace-free matrix fields whose (row-wise) divergence vanishes weakly in
`Ω`, with **no** boundary condition: `∫ Σ_{ij} B_{ij} ∂_j φ_i = 0` for all `φ ∈ C_c^∞(Ω; ℝ³)`. -/
def TSD : Submodule ℝ (L2M Ω) where
  carrier := {B | (∀ i j, B (i, j) = B (j, i)) ∧ ∑ i, B (i, i) = 0 ∧
    ∀ φ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (φ i)) →
      ∑ ij : Ix, ∫ x, B ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0}
  zero_mem' := ⟨fun _ _ => rfl, by simp, fun φ hφ => by rw [divPairing_eq hφ]; simp⟩
  add_mem' := by
    rintro B B' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun i j => by simp [h1 i j, h1' i j], by simp [Finset.sum_add_distrib, h2, h2'],
      fun φ hφ => ?_⟩
    have e := h3 φ hφ
    have e' := h3' φ hφ
    rw [divPairing_eq hφ] at e e' ⊢
    simp [inner_add_left, Finset.sum_add_distrib, e, e']
  smul_mem' := by
    rintro r B ⟨h1, h2, h3⟩
    refine ⟨fun i j => by simp [h1 i j], by simp [← Finset.smul_sum, h2], fun φ hφ => ?_⟩
    have e := h3 φ hφ
    rw [divPairing_eq hφ] at e ⊢
    simp [real_inner_smul_left, ← Finset.mul_sum, e]

/-- Membership in `L²(TSD)`, by definition. -/
theorem mem_TSD {B : L2M Ω} : B ∈ TSD Ω ↔ (∀ i j, B (i, j) = B (j, i)) ∧ ∑ i, B (i, i) = 0 ∧
    ∀ φ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (φ i)) →
      ∑ ij : Ix, ∫ x, B ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0 := Iff.rfl

/-- `L²(TSD)` is closed. -/
theorem isClosed_TSD : IsClosed (TSD Ω : Set (L2M Ω)) := by
  have e : (TSD Ω : Set (L2M Ω)) = ((⋂ i : Fin 3, ⋂ j : Fin 3, {B : L2M Ω | B (i, j) = B (j, i)}) ∩
      {B | ∑ i, B (i, i) = 0}) ∩ ⋂ φ : Fin 3 → R3 → ℝ, ⋂ hφ : (∀ i, IsTest Ω (φ i)),
        {B | ∑ ij : Ix, ⟪B ij, ((hφ ij.1).pdiff ij.2).memLp.toLp _⟫ = 0} := by
    ext B
    simp only [SetLike.mem_coe, mem_TSD, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun φ hφ => (divPairing_eq hφ B) ▸ h3 φ hφ⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun φ hφ => (divPairing_eq hφ B).symm ▸ h3 φ hφ⟩
  rw [e]
  refine (IsClosed.inter ?_ ?_).inter ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_component (i, j)) (continuous_component (j, i))
  · exact isClosed_eq (continuous_finsetSum Finset.univ fun i _ => continuous_component (i, i))
      continuous_const
  · exact isClosed_iInter fun φ => isClosed_iInter fun hφ => isClosed_eq
      (continuous_finsetSum Finset.univ fun ij _ => (continuous_component ij).inner
        continuous_const) continuous_const

/-- `P_{L²(TSD)}` exists (`L²(TSD)` is closed). -/
instance : (TSD Ω).HasOrthogonalProjection := by
  have : CompleteSpace (TSD Ω) := isClosed_TSD.completeSpace_coe
  infer_instance

/-- `L²(TSD)` is `Feec.Models.BoundedDomain.tsd`. -/
theorem TSD_eq_tsd : TSD Ω = Feec.Models.BoundedDomain.tsd Ω := by
  ext B
  rw [mem_TSD, Feec.Models.BoundedDomain.mem_tsd]
  refine and_congr_right' (and_congr_right' ?_)
  constructor
  · intro h φ hφ
    rw [Feec.Models.BoundedDomain.inner_grad_testField _ hφ]
    exact h φ fun i => IsTest.ofDomain (hφ i)
  · intro h φ hφ
    have := h φ fun i => (hφ i).toDomain
    rw [Feec.Models.BoundedDomain.inner_grad_testField _ (fun i => (hφ i).toDomain)] at this
    exact this

/-- Weakly divergence-free fields are in `H(div)`: `L²(TSD) ⊆ H(div)`. -/
theorem TSD_subset_HdivM : (TSD Ω : Set (L2M Ω)) ⊆ HdivM Ω := by
  intro B hB
  refine ⟨0, fun φ hφ => ?_⟩
  rw [hB.2.2 φ hφ, Finset.sum_congr rfl fun i _ => integral_mul_eq_inner _ (hφ i).memLp]
  simp

/-! ## Skew fields `Ψ_{j·} = e_j × ψ` and their curl -/

/-- The skew matrix field with rows `e_j × ψ`:
`skewOf ψ (j, k) = [j = k+1] ψ_{k+2} - [j = k+2] ψ_{k+1}`. -/
def skewOf (ψ : Fin 3 → R3 → ℝ) (jk : Ix) : R3 → ℝ :=
  (if jk.1 = jk.2 + 1 then ψ (jk.2 + 2) else 0) - (if jk.1 = jk.2 + 2 then ψ (jk.2 + 1) else 0)

/-- `skewOf ψ` is skew-symmetric. -/
theorem skewOf_swap (ψ : Fin 3 → R3 → ℝ) (j k : Fin 3) (x : R3) :
    skewOf ψ (k, j) x = -skewOf ψ (j, k) x := by
  fin_cases j <;> fin_cases k <;> simp [skewOf]

/-- `skewOf ψ` is as smooth as `ψ`. -/
theorem contDiff_skewOf {n : WithTop ℕ∞} {ψ : Fin 3 → R3 → ℝ} (hψ : ∀ i, ContDiff ℝ n (ψ i))
    (jk : Ix) : ContDiff ℝ n (skewOf ψ jk) := by
  unfold skewOf
  apply ContDiff.sub <;> split_ifs <;> first | exact hψ _ | exact contDiff_const

/-- `∂_k (f - g) = ∂_k f - ∂_k g`. -/
theorem pd_sub {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (k : Fin 3)
    (x : R3) : pd k (f - g) x = pd k f x - pd k g x := by
  rw [pd, fderiv_sub (hf x) (hg x)]
  rfl

/-- `∂_k (f + g) = ∂_k f + ∂_k g`. -/
theorem pd_add {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (k : Fin 3)
    (x : R3) : pd k (f + g) x = pd k f x + pd k g x := by
  rw [pd, fderiv_add (hf x) (hg x)]
  rfl

/-- `∂_k (c f) = c ∂_k f`. -/
theorem pd_const_mul {f : R3 → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (k : Fin 3) (x : R3) :
    pd k (fun y => c * f y) x = c * pd k f x := by
  rw [pd, fderiv_const_mul (hf x)]
  rfl

/-- `∂_k 0 = 0`. -/
@[simp] theorem pd_zero (k : Fin 3) (x : R3) : pd k (0 : R3 → ℝ) x = 0 := by simp [pd]

/-- Partial derivatives commute with a constant case split. -/
theorem pd_ite_zero (c : Prop) [Decidable c] (f : R3 → ℝ) (k : Fin 3) (x : R3) :
    pd k (if c then f else 0) x = if c then pd k f x else 0 := by
  split_ifs
  · rfl
  · simp [pd]

/-- `curl (e_j × ψ) = e_j div ψ - ∂_j ψ`, row by row. -/
theorem curlM_skewOf {ψ : Fin 3 → R3 → ℝ} (hψ : ∀ i, Differentiable ℝ (ψ i)) (jk : Ix)
    (x : R3) : curlM (skewOf ψ) jk x =
      (if jk.1 = jk.2 then ∑ m, pd m (ψ m) x else 0) - pd jk.1 (ψ jk.2) x := by
  have hd : ∀ (c : Prop) [Decidable c] (m : Fin 3), Differentiable ℝ (if c then ψ m else 0) := by
    intro c _ m
    split_ifs
    exacts [hψ m, differentiable_const 0]
  obtain ⟨j, k⟩ := jk
  simp only [curlM, skewOf, pd_sub (hd _ _) (hd _ _), pd_ite_zero]
  fin_cases j <;> fin_cases k <;> simp [Fin.sum_univ_three] <;> ring

/-- For a symmetric `C`, `∫ C : skewOf ψ = 0`. -/
theorem sum_integral_mul_skewOf_eq_zero {C : L2M Ω} (hC : ∀ j k, C (j, k) = C (k, j))
    (ψ : Fin 3 → R3 → ℝ) : ∑ jk, ∫ x, C jk x * skewOf ψ jk x ∂volume.restrict Ω = 0 := by
  have h : ∑ jk, ∫ x, C jk x * skewOf ψ jk x ∂volume.restrict Ω =
      -∑ jk, ∫ x, C jk x * skewOf ψ jk x ∂volume.restrict Ω := by
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
    obtain ⟨j, k⟩ := jk
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hC j k, ← integral_neg]
    congr 1
    ext x
    rw [skewOf_swap ψ j k x]
    ring
  linarith

/-- Integrals commute with a constant case split. -/
theorem integral_ite_zero (c : Prop) [Decidable c] (f : R3 → ℝ) :
    ∫ x, (if c then f x else 0) ∂volume.restrict Ω =
      if c then ∫ x, f x ∂volume.restrict Ω else 0 := by
  split_ifs <;> simp

/-- For `B ∈ L²(TSD)` and `ψ ∈ C_c^∞(Ω; ℝ³)`: `∫ B : curl (skewOf ψ) = 0`, the weak form of
"`curl B` is symmetric" (part of Lemma 3.5). -/
theorem sum_integral_mul_curlM_skewOf_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B : L2M Ω} (hB : B ∈ TSD Ω) {ψ : Fin 3 → R3 → ℝ} (hψ : ∀ i, IsTest Ω (ψ i)) :
    ∑ jk, ∫ x, B jk x * curlM (skewOf ψ) jk x ∂volume.restrict Ω = 0 := by
  obtain ⟨hsym, htr, hdiv⟩ := hB
  set d : R3 → ℝ := fun x => ∑ m, pd m (ψ m) x with hd
  have hdc : Continuous d := continuous_finsetSum _ fun m _ => continuous_pd (hψ m).contDiff_one m
  have hdm : MemLp d 2 (volume.restrict Ω) := memLp_of_continuous hΩ hb hdc
  simp only [curlM_skewOf (fun i => (hψ i).differentiable), mul_sub]
  rw [Finset.sum_congr rfl fun jk _ => integral_sub ?_ ?_]
  rotate_left
  · exact integrable_mul _ (by split_ifs; exacts [hdm, MemLp.zero])
  · exact integrable_mul _ ((hψ _).pdiff _).memLp
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ jk : Ix, ∫ x, B jk x * (if jk.1 = jk.2 then d x else 0) ∂volume.restrict Ω = 0 := by
    simp only [mul_ite, mul_zero, integral_ite_zero, Fintype.sum_prod_type, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    simp only [fun f : L2 Ω => integral_mul_eq_inner f hdm, ← sum_inner, htr, inner_zero_left]
  have h2 : ∑ jk : Ix, ∫ x, B jk x * pd jk.1 (ψ jk.2) x ∂volume.restrict Ω = 0 := by
    rw [← hdiv ψ hψ]
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
    obtain ⟨j, k⟩ := jk
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hsym j k]
  rw [h1, h2, sub_zero]

/-- Fundamental lemma of the calculus of variations in `L²(Ω)`. -/
theorem L2_ext_of_integral (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f f' : L2 Ω}
    (h : ∀ g, IsTest Ω g →
      ∫ x, f x * g x ∂volume.restrict Ω = ∫ x, f' x * g x ∂volume.restrict Ω) : f = f' := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hint : IntegrableOn (fun x => f x - f' x) Ω volume :=
    ((Lp.memLp f).integrable one_le_two).sub ((Lp.memLp f').integrable one_le_two)
  have hae := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hint.locallyIntegrableOn
    fun g hg hgc hgs => by
      have hgt : IsTest Ω g := ⟨hg, hgc, hgs⟩
      rw [← integral_restrict_of_eq_zero (Ω := Ω) fun x hx => by
        simp [hgt.eq_zero_of_notMem hx]]
      simp only [smul_eq_mul]
      rw [show (fun x => g x * (f x - f' x)) = fun x => f x * g x - f' x * g x by ext; ring,
        integral_sub (integrable_mul f hgt.memLp) (integrable_mul f' hgt.memLp), h g hgt,
        sub_self]
  refine Lp.ext ?_
  filter_upwards [(ae_restrict_iff' hΩ.measurableSet).2 hae] with x hx
  exact sub_eq_zero.1 hx

/-- **Lemma 3.5 (symmetry part), distributional form on `H̊(curl)`.** If `(B, C)` is in the
closure of the curl graph and `B ∈ L²(TSD)`, then `C = curl B` is symmetric.

See [QuennevilleBelair2015, §3.4, Lemma 3.5]. -/
theorem curl_symm_of_mem_TSD (hΩ : IsOpen Ω) (_hb : Bornology.IsBounded Ω) {B C : L2M Ω}
    (h : (B, C) ∈ closure (curlGraph Ω)) (hB : B ∈ TSD Ω) (j k : Fin 3) :
    C (j, k) = C (k, j) := by
  rw [curlGraph_eq_testGraph, ← Submodule.topologicalClosure_coe, SetLike.mem_coe,
    ← Feec.Domain.ConstCoeffOp.minimal_graph _ hΩ] at h
  have hdom := LinearPMap.mem_domain_of_mem_graph h
  have hC := ((LinearPMap.image_iff hdom).2 h)
  rw [hC]
  exact Feec.Models.BoundedDomain.curl_symm_of_mem_tsd hΩ ⟨B, hdom⟩ (TSD_eq_tsd ▸ hB) j k

/-- `∂_k x_a = δ_{ka}`. -/
theorem pd_coord (a k : Fin 3) (x : R3) :
    pd k (fun y : R3 => y a) x = if k = a then 1 else 0 := by
  rw [pd, (hasFDerivAt_apply a x).fderiv]
  simp [Pi.single_apply, eq_comm]

/-! ## Main result: `H̊(curl) ∩ L²(TSD)` fields have zero mean -/

/-- **Key theorem.** On a bounded open `Ω ⊆ ℝ³`, every `B ∈ L²(TSD) ∩ H̊(curl)` has zero mean:
`∫_Ω B_{ab} = 0` for all `a, b`. This is the integrated (trace-free) form of the pointwise boundary
lemma `eq_zero_of_symm_of_trace_of_cross`: formally `∫_Ω B : ∇v = ∫_{∂Ω} (B n)·v = 0`.

Proof: let `C = curl B` (from the graph closure). `C` is symmetric (`curl_symm_of_mem_TSD`). For
the linear field `v = x_a e_b`, test the graph closure against `Ψ = skewOf v` (rows `e_j × v`,
not compactly supported): `0 = ∫ C : Ψ = ∫ B : curl Ψ = δ_{ab} ∫ tr B - ∫ B_{ab}`.

Correction: this refutes the first projection hypothesis of Prop 4.17 and the density of
`H̊(curl) ∩ L²(TSD)` in `L²(TSD)` claimed in its proof, on bounded domains
(`projTSD_not_mem_HcurlZero`, `not_dense_TSD_inter_HcurlZero`).
See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem integral_eq_zero_of_mem_TSD_of_mem_HcurlZero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B : L2M Ω} (hB : B ∈ TSD Ω) (hB' : B ∈ HcurlZero Ω) (a b : Fin 3) :
    ∫ x, B (a, b) x ∂volume.restrict Ω = 0 :=
  Feec.Models.BoundedDomain.integral_eq_zero_of_mem_tsd hΩ hb ⟨B, mem_HcurlZero_iff_minimal.1 hB'⟩
    (TSD_eq_tsd ▸ hB) a b

/-! ## Test fields, constant fields, and the counterexample -/

/-- The `L²` class of a matrix field with components in `C_c^∞(Ω)`. -/
def testField {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) : L2M Ω :=
  WithLp.toLp 2 fun ij => (hΦ ij).memLp.toLp (Φ ij)

/-- The components of `testField` are a.e. the given test functions. -/
theorem coeFn_testField {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) (ij : Ix) :
    (testField hΦ ij : R3 → ℝ) =ᵐ[volume.restrict Ω] Φ ij :=
  (hΦ ij).memLp.coeFn_toLp

/-- `C_c^∞(Ω; ℝ³ˣ³) ⊆ H̊(curl)`. -/
theorem testField_mem_HcurlZero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) : testField hΦ ∈ HcurlZero Ω := by
  have hc : ∀ ij, MemLp (curlM Φ ij) 2 (volume.restrict Ω) := fun ij =>
    memLp_of_continuous hΩ hb ((continuous_pd (hΦ _).contDiff_one _).sub
      (continuous_pd (hΦ _).contDiff_one _))
  refine ⟨WithLp.toLp 2 fun ij => (hc ij).toLp _, subset_closure ⟨Φ, hΦ, fun ij => ?_⟩⟩
  exact ⟨coeFn_testField hΦ ij, (hc ij).coeFn_toLp⟩

/-- `C_c^∞(Ω; ℝ³ˣ³) ⊆ H(div)`. -/
theorem testField_mem_HdivM (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) : testField hΦ ∈ HdivM Ω := by
  have hd : ∀ i, MemLp (fun x => ∑ j, pd j (Φ (i, j)) x) 2 (volume.restrict Ω) := fun i =>
    memLp_of_continuous hΩ hb (continuous_finsetSum _ fun j _ =>
      continuous_pd (hΦ _).contDiff_one _)
  refine ⟨WithLp.toLp 2 fun i => (hd i).toLp _, fun φ hφ => ?_⟩
  have hL : ∀ ij : Ix, ∫ x, testField hΦ ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
      -∫ x, pd ij.2 (Φ ij) x * φ ij.1 x ∂volume.restrict Ω := by
    intro ij
    rw [integral_pd_mul (hΦ ij) (hφ ij.1).contDiff_one, neg_neg]
    exact integral_congr_ae ((coeFn_testField hΦ ij).mono fun x hx => by simp only; rw [hx])
  have hR : ∀ i, ∫ x, (WithLp.toLp 2 fun i => (hd i).toLp _ : L2V Ω) i x * φ i x
      ∂volume.restrict Ω = ∑ j, ∫ x, pd j (Φ (i, j)) x * φ i x ∂volume.restrict Ω := by
    intro i
    rw [← integral_finsetSum _ fun j _ => integrable_mul_of_compact
      (continuous_pd (hΦ _).contDiff_one _) ((hΦ _).pdiff _).hasCompactSupport (hφ i).continuous]
    refine integral_congr_ae (((hd i).coeFn_toLp).mono fun x hx => ?_)
    simp only at hx ⊢
    rw [hx, Finset.sum_mul]
  simp only [hL, hR, Finset.sum_neg_distrib, Fintype.sum_prod_type]

/-- The constant matrix field `A` on a bounded open `Ω`, as an element of `L²(Ω; ℝ³ˣ³)`. -/
def constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    L2M Ω :=
  WithLp.toLp 2 fun ij => (memLp_of_continuous hΩ hb
    (continuous_const : Continuous fun _ : R3 => A ij.1 ij.2)).toLp _

/-- The components of `constField A` are a.e. the constants `A_{ij}`. -/
theorem coeFn_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (ij : Ix) :
    (constField hΩ hb A ij : R3 → ℝ) =ᵐ[volume.restrict Ω] fun _ => A ij.1 ij.2 :=
  MemLp.coeFn_toLp (memLp_of_continuous hΩ hb continuous_const)

/-- Pairing with a constant field: `⟪F, A⟫ = Σ_{ij} A_{ij} ∫_Ω F_{ij}`. -/
theorem inner_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (F : L2M Ω) :
    ⟪F, constField hΩ hb A⟫ = ∑ ij : Ix, A ij.1 ij.2 * ∫ x, F ij x ∂volume.restrict Ω := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [constField, ← integral_mul_eq_inner, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- `∫_Ω A_{ij} = |Ω| A_{ij}`. -/
theorem integral_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (ij : Ix) :
    ∫ x, constField hΩ hb A ij x ∂volume.restrict Ω = volume.real Ω * A ij.1 ij.2 := by
  rw [integral_congr_ae (coeFn_constField hΩ hb A ij), integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul]

/-- **Constant symmetric trace-free fields are in `L²(TSD)`** (there is no boundary condition in
`L²(TSD)`). -/
theorem constField_mem_TSD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = A) (htrA : A.trace = 0) :
    constField hΩ hb A ∈ TSD Ω := by
  set K := constField hΩ hb A
  have hKc := coeFn_constField hΩ hb A
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [hKc (i, j), hKc (j, i)] with x h1 h2
    rw [h1, h2]
    show A i j = A j i
    rw [← Matrix.transpose_apply A j i, hA]
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (K (0, 0) + K (1, 1)) (K (2, 2)),
      Lp.coeFn_add (K (0, 0)) (K (1, 1)), hKc (0, 0), hKc (1, 1), hKc (2, 2),
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6]
    simpa [Matrix.trace, Fin.sum_univ_three] using htrA
  · refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_congr_ae (g := fun x => A ij.1 ij.2 * pd ij.2 (φ ij.1) x)
      ((hKc ij).mono fun x hx => by simp only; rw [hx]), integral_const_mul]
    have h0 := integral_pd_mul (hφ ij.1) (contDiff_const (c := (1 : ℝ))) ij.2
    simp only [mul_one] at h0
    rw [h0]
    simp [pd]

/-- If `∫_Ω E : A ≠ 0` for some constant symmetric trace-free `A`, then `P_{L²(TSD)} E ∉ H̊(curl)`.
Proof: `A ∈ L²(TSD)`, so `⟪P E, A⟫ = ⟪E, A⟫ ≠ 0`, while `⟪P E, A⟫ = Σ A_{ij} ∫ (P E)_{ij} = 0`
if `P E ∈ H̊(curl)` (`integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`).

Correction: this refutes the first conjecture of [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem projTSD_not_mem_HcurlZero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (E : L2M Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = A) (htrA : A.trace = 0)
    (hE : ∑ ij : Ix, A ij.1 ij.2 * ∫ x, E ij x ∂volume.restrict Ω ≠ 0) :
    (TSD Ω).starProjection E ∉ HcurlZero Ω := by
  intro hP
  have h1 : ⟪(TSD Ω).starProjection E, constField hΩ hb A⟫ = ⟪E, constField hΩ hb A⟫ := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (constField_mem_TSD hΩ hb hA htrA)]
  have h2 : ⟪(TSD Ω).starProjection E, constField hΩ hb A⟫ = 0 := by
    rw [inner_constField]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_eq_zero_of_mem_TSD_of_mem_HcurlZero hΩ hb
      (Submodule.starProjection_apply_mem _ _) hP, mul_zero]
  exact hE (by rw [← inner_constField hΩ hb A E, ← h1, h2])

/-- The matrix `diag(1, -1, 0)`. -/
def diagA : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- `diag(1, -1, 0)` is symmetric. -/
theorem diagA_transpose : diagA.transpose = diagA := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `diag(1, -1, 0)` is trace-free. -/
theorem diagA_trace : diagA.trace = 0 := by simp [diagA, Matrix.trace, Fin.sum_univ_three]

/-- **The density claimed in the proof of Prop 4.17 fails on every nonempty bounded open `Ω`:**
`H̊(curl, M) ∩ L²(TSD)` is not dense in `L²(TSD)`. Indeed it lies in the closed subspace
`{B | ∫_Ω B = 0}`, which misses the constant field `diag(1, -1, 0) ∈ L²(TSD)`.

Thesis gap: the claim that `H̊(curl, M) ∩ L²(TSD)` is dense in `L²(TSD)`
([QuennevilleBelair2015, §4.10, proof of Prop 4.17]) is false; it does not follow from the
stated (and true, `dense_domain_d1_inter_ker_adj0`) density of `H̊(curl, M) ∩ H(div, M, 0)` in
`H(div, M, 0)`. -/
theorem not_dense_TSD_inter_HcurlZero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    constField hΩ hb diagA ∈ TSD Ω ∧
      constField hΩ hb diagA ∉ closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) := by
  set K := constField hΩ hb diagA
  refine ⟨constField_mem_TSD hΩ hb diagA_transpose diagA_trace, fun hK => ?_⟩
  have hsub : (TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω ⊆ (fun F => ⟪F, K⟫) ⁻¹' {0} := by
    rintro F ⟨hF, hF'⟩
    simp only [mem_preimage, mem_singleton_iff, K, inner_constField]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_eq_zero_of_mem_TSD_of_mem_HcurlZero hΩ hb hF hF', mul_zero]
  have h0 := closure_minimal hsub (isClosed_singleton.preimage (continuous_id.inner
    continuous_const)) hK
  simp only [mem_preimage, mem_singleton_iff, K, inner_constField, integral_constField] at h0
  have hpos : 0 < volume.real Ω := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA] at h0
  linarith

/-- A nonnegative test function with positive integral (a bump at a point of `Ω`). -/
theorem exists_isTest_integral_pos (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ g : R3 → ℝ, IsTest Ω g ∧ 0 < ∫ x, g x ∂volume.restrict Ω := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ c hc
  let f : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have ht : tsupport f ⊆ Ω := by
    rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show ε / 2 < ε; linarith)).trans hball
  refine ⟨f, ⟨f.contDiff, f.hasCompactSupport, ht⟩, ?_⟩
  rw [integral_restrict_of_eq_zero fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (ht h)]
  exact f.integral_pos

/-- **The projection hypothesis of Prop 4.17 fails on every nonempty bounded open `Ω ⊆ ℝ³`.**
There is `E ∈ C_c^∞(Ω; ℝ³ˣ³) ⊆ H̊(curl) ∩ H(div)` with `P_{L²(TSD)} E ∉ H̊(curl)`; explicitly
`E = g · diag(1, -1, 0)` for any bump `g ≥ 0`, `g ≠ 0`.

Correction: the hypothesis `P_{L²(TSD)} (H̊(curl, M) ∩ H(div, M)) ⊂ H̊(curl, M) ∩ H(div, M)` of
[QuennevilleBelair2015, §4.10, Prop 4.17] is false. -/
theorem exists_projTSD_not_mem_HcurlZero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ∃ (Φ : Ix → R3 → ℝ) (hΦ : ∀ ij, IsTest Ω (Φ ij)),
      testField hΦ ∈ HcurlZero Ω ∧ testField hΦ ∈ HdivM Ω ∧
        (TSD Ω).starProjection (testField hΦ) ∉ HcurlZero Ω := by
  obtain ⟨g, hg, hgpos⟩ := exists_isTest_integral_pos hΩ hne
  let Φ : Ix → R3 → ℝ := fun ij x => diagA ij.1 ij.2 * g x
  have hΦ : ∀ ij, IsTest Ω (Φ ij) := fun ij =>
    ⟨contDiff_const.mul hg.contDiff, hg.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans hg.tsupport_subset⟩
  refine ⟨Φ, hΦ, testField_mem_HcurlZero hΩ hb hΦ, testField_mem_HdivM hΩ hb hΦ,
    projTSD_not_mem_HcurlZero hΩ hb _ diagA diagA_transpose diagA_trace ?_⟩
  have hI : ∀ ij : Ix, ∫ x, testField hΦ ij x ∂volume.restrict Ω =
      diagA ij.1 ij.2 * ∫ x, g x ∂volume.restrict Ω := fun ij => by
    rw [← integral_const_mul]
    exact integral_congr_ae (coeFn_testField hΦ ij)
  simp only [hI, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [diagA]
  positivity

/-! ## The closed operator `curl` on `H̊(curl)` -/

variable (Ω) in
/-- The graph of curl on `C_c^∞(Ω; ℝ³ˣ³)` is a linear subspace. -/
def curlGraphSub : Submodule ℝ (L2M Ω × L2M Ω) where
  carrier := curlGraph Ω
  zero_mem' := by
    refine ⟨0, fun _ => IsTest.zero, fun ij => ⟨?_, ?_⟩⟩
    · filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
      simpa using hx
    · filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
      simpa [curlM] using hx
  add_mem' := by
    rintro ⟨u, c⟩ ⟨u', c'⟩ ⟨Φ, hΦ, hp⟩ ⟨Φ', hΦ', hq⟩
    refine ⟨Φ + Φ', fun ij => (hΦ ij).add (hΦ' ij), fun ij => ⟨?_, ?_⟩⟩
    · filter_upwards [Lp.coeFn_add (u ij) (u' ij), (hp ij).1, (hq ij).1] with x h1 h2 h3
      simp only [Prod.fst_add, PiLp.add_apply, Pi.add_apply] at h1 ⊢
      rw [h1, h2, h3]
    · filter_upwards [Lp.coeFn_add (c ij) (c' ij), (hp ij).2, (hq ij).2] with x h1 h2 h3
      simp only [Prod.snd_add, PiLp.add_apply, Pi.add_apply] at h1 ⊢
      rw [h1, h2, h3]
      simp only [curlM, Pi.add_apply]
      rw [pd_add (hΦ _).differentiable (hΦ' _).differentiable,
        pd_add (hΦ _).differentiable (hΦ' _).differentiable]
      ring
  smul_mem' := by
    rintro r ⟨u, c⟩ ⟨Φ, hΦ, hp⟩
    refine ⟨fun ij x => r * Φ ij x, fun ij => (hΦ ij).const_mul r, fun ij => ⟨?_, ?_⟩⟩
    · filter_upwards [Lp.coeFn_smul r (u ij), (hp ij).1] with x h1 h2
      simp only [Prod.smul_fst, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1, h2]
    · filter_upwards [Lp.coeFn_smul r (c ij), (hp ij).2] with x h1 h2
      simp only [Prod.smul_snd, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1, h2]
      simp only [curlM]
      rw [pd_const_mul (hΦ _).differentiable, pd_const_mul (hΦ _).differentiable]
      ring

/-- The closure of `curlGraphSub` is the closure of the curl graph. -/
theorem coe_topologicalClosure_curlGraphSub :
    ((curlGraphSub Ω).topologicalClosure : Set (L2M Ω × L2M Ω)) = closure (curlGraph Ω) := rfl

/-- A single-entry test matrix field `g E_{ij}`. -/
theorem isTest_single {g : R3 → ℝ} (hg : IsTest Ω g) (ij kl : Ix) :
    IsTest Ω (if kl = ij then g else 0) := by
  split_ifs
  exacts [hg, IsTest.zero]

/-- A matrix field orthogonal to every test field vanishes. -/
theorem eq_zero_of_forall_integral (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {C : L2M Ω}
    (h : ∀ Ψ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Ψ ij)) →
      ∑ ij, ∫ x, C ij x * Ψ ij x ∂volume.restrict Ω = 0) : C = 0 := by
  refine (WithLp.ext_iff 2).2 (funext fun ij => ?_)
  refine L2_ext_of_integral hΩ hb fun g hg => ?_
  have e := h (fun kl => if kl = ij then g else 0) fun kl => isTest_single hg ij kl
  have e2 : ∀ kl : Ix, ∫ x, C kl x * (if kl = ij then g else 0) x ∂volume.restrict Ω =
      if kl = ij then ∫ x, C ij x * g x ∂volume.restrict Ω else 0 := by
    intro kl
    split_ifs with hkl
    · rw [hkl]
    · simp
  simp only [e2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e
  rw [e]
  have : ∫ x, (0 : L2M Ω).ofLp ij x * g x ∂volume.restrict Ω = 0 := by
    rw [integral_mul_eq_inner _ hg.memLp]
    simp
  exact this.symm

/-- The curl graph submodule is the test graph of `Feec.Domain.curlOp 3`. -/
theorem curlGraphSub_eq :
    curlGraphSub Ω = (Feec.Domain.curlOp 3 : Feec.Domain.ConstCoeffOp R3 ℝ Ix Ix).testGraph Ω :=
  SetLike.coe_injective curlGraph_eq_testGraph

/-- The closure of the curl graph is a graph (curl on `C_c^∞` is closable). -/
theorem curlGraph_closable (hΩ : IsOpen Ω) (_hb : Bornology.IsBounded Ω) :
    ∀ x ∈ (curlGraphSub Ω).topologicalClosure, x.1 = 0 → x.2 = 0 := by
  rw [curlGraphSub_eq]
  exact (Feec.Domain.curlOp 3).testGraph_closable hΩ

/-- `curl : H̊(curl, Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)`, the closure of curl on `C_c^∞`. -/
def curlClosure : L2M Ω →ₗ.[ℝ] L2M Ω := (curlGraphSub Ω).topologicalClosure.toLinearPMap

/-- **`curlClosure` is the minimal realization** of the row-wise curl
(`Feec.Domain.ConstCoeffOp.minimal`). -/
theorem curlClosure_eq_minimal :
    curlClosure (Ω := Ω) = (Feec.Domain.curlOp 3 : Feec.Domain.ConstCoeffOp R3 ℝ Ix Ix).minimal Ω := by
  rw [curlClosure, curlGraphSub_eq]
  rfl

/-- The graph of `curlClosure` is the closure of the curl graph. -/
theorem curlClosure_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (curlClosure (Ω := Ω)).graph = (curlGraphSub Ω).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (curlGraph_closable hΩ hb)

/-- `(u, curl u)` is a graph-norm limit of `(Φₙ, curl Φₙ)`, `Φₙ ∈ C_c^∞`. -/
theorem mem_closure_curlClosure (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (curlClosure (Ω := Ω)).domain) :
    ((u : L2M Ω), curlClosure u) ∈ closure (curlGraph Ω) :=
  Submodule.mem_graph_toLinearPMap (curlGraph_closable hΩ hb) u

/-- The domain of `curlClosure` is `H̊(curl)`. -/
theorem mem_domain_curlClosure {u : L2M Ω} :
    u ∈ (curlClosure (Ω := Ω)).domain ↔ u ∈ HcurlZero Ω := by
  rw [curlClosure, Submodule.toLinearPMap_domain, Submodule.mem_map]
  constructor
  · rintro ⟨⟨B, C⟩, h, rfl⟩
    exact ⟨C, h⟩
  · rintro ⟨C, h⟩
    exact ⟨(u, C), h, rfl⟩

/-- `curlClosure` is a closed operator. -/
theorem isClosed_curlClosure (hΩ : IsOpen Ω) (_hb : Bornology.IsBounded Ω) :
    (curlClosure (Ω := Ω)).IsClosed := by
  rw [curlClosure_eq_minimal]
  exact (Feec.Domain.curlOp 3).isClosed_minimal hΩ

/-- `C_c^∞` is dense in `L²(Ω; ℝ³ˣ³)`, hence so is `H̊(curl)`. -/
theorem dense_domain_curlClosure (hΩ : IsOpen Ω) (_hb : Bornology.IsBounded Ω) :
    Dense ((curlClosure (Ω := Ω)).domain : Set (L2M Ω)) := by
  rw [curlClosure_eq_minimal]
  exact (Feec.Domain.curlOp 3).dense_minimal_domain hΩ

/-! ## The closed operator `grad` on `H̊¹` and the thesis' complex -/

section Grad

open scoped LinearPMap

/-- Schwarz: partial derivatives of a `C²` function commute. -/
theorem pd_pd_comm {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (a b : Fin 3) (x : R3) :
    pd a (pd b f) x = pd b (pd a f) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e : ∀ v w : R3, fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    intro v w
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single b 1)) x (Pi.single a 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single a 1)) x (Pi.single b 1)
  rw [e, e]
  exact (ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt (x := x)) (by simp)) _ _

/-- The row-wise gradient of a vector field, `(grad φ)_{ij} = ∂_j φ_i`. -/
def gradM (φ : Fin 3 → R3 → ℝ) : Ix → R3 → ℝ := fun ij => pd ij.2 (φ ij.1)

/-- The row-wise gradient is the constant-coefficient operator `Feec.Domain.gradOp 3 3`. -/
theorem gradM_eq_apply (φ : Fin 3 → R3 → ℝ) :
    gradM φ = (Feec.Domain.gradOp 3 3 : Feec.Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).apply φ := by
  funext ij x
  rw [Feec.Domain.gradOp_apply]
  rfl

/-- The gradient of a test vector field has test components. -/
theorem isTest_gradM {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Ω (φ i)) (ij : Ix) :
    IsTest Ω (gradM φ ij) := (hφ ij.1).pdiff ij.2

/-- `curl grad = 0` for `C²` vector fields (row-wise). -/
theorem curlM_gradM {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (ik : Ix) (x : R3) :
    curlM (gradM φ) ik x = 0 := by
  simp only [curlM, gradM]
  rw [pd_pd_comm (hφ _), sub_self]

variable (Ω) in
/-- The graph of the row-wise gradient on `C_c^∞(Ω; ℝ³)`, in `L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³)`. -/
def gradGraph : Set (L2V Ω × L2M Ω) :=
  {p | ∃ φ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (φ i)) ∧
    (∀ i, (p.1 i : R3 → ℝ) =ᵐ[volume.restrict Ω] φ i) ∧
      ∀ ij, (p.2 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] gradM φ ij}

/-- The grad graph is the test graph of `Feec.Domain.gradOp 3 3`. -/
theorem gradGraph_eq_testGraph :
    gradGraph Ω = ((Feec.Domain.gradOp 3 3 : Feec.Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).testGraph Ω :
      Set (L2V Ω × L2M Ω)) := by
  ext ⟨u, c⟩
  constructor
  · rintro ⟨φ, hφ, hp1, hp2⟩
    have hφ' : Feec.Domain.IsTestField Ω φ := fun i => (hφ i).toDomain
    refine ⟨φ, hφ', ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨Feec.Domain.eq_testField hφ' hp1,
      Feec.Domain.eq_testField _ fun ij => by rw [← gradM_eq_apply]; exact hp2 ij⟩
  · rintro ⟨φ, hφ, h⟩
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨φ, fun i => IsTest.ofDomain (hφ i), fun i => Feec.Domain.coeFn_testField hφ i,
      fun ij => by rw [gradM_eq_apply]; exact Feec.Domain.coeFn_testField _ ij⟩

variable (Ω) in
/-- The graph of grad on `C_c^∞(Ω; ℝ³)` is a linear subspace. -/
def gradGraphSub : Submodule ℝ (L2V Ω × L2M Ω) where
  carrier := gradGraph Ω
  zero_mem' := by
    refine ⟨0, fun _ => IsTest.zero, fun i => ?_, fun ij => ?_⟩
    · filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
      simpa using hx
    · filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
      simpa [gradM] using hx
  add_mem' := by
    rintro ⟨u, c⟩ ⟨u', c'⟩ ⟨φ, hφ, hp1, hp2⟩ ⟨φ', hφ', hq1, hq2⟩
    refine ⟨φ + φ', fun i => (hφ i).add (hφ' i), fun i => ?_, fun ij => ?_⟩
    · filter_upwards [Lp.coeFn_add (u i) (u' i), hp1 i, hq1 i] with x h1 h2 h3
      simp only [Prod.fst_add, PiLp.add_apply, Pi.add_apply] at h1 ⊢
      rw [h1, h2, h3]
    · filter_upwards [Lp.coeFn_add (c ij) (c' ij), hp2 ij, hq2 ij] with x h1 h2 h3
      simp only [Prod.snd_add, PiLp.add_apply, Pi.add_apply] at h1 ⊢
      rw [h1, h2, h3]
      simp only [gradM, Pi.add_apply]
      rw [pd_add (hφ _).differentiable (hφ' _).differentiable]
  smul_mem' := by
    rintro r ⟨u, c⟩ ⟨φ, hφ, hp1, hp2⟩
    refine ⟨fun i x => r * φ i x, fun i => (hφ i).const_mul r, fun i => ?_, fun ij => ?_⟩
    · filter_upwards [Lp.coeFn_smul r (u i), hp1 i] with x h1 h2
      simp only [Prod.smul_fst, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1, h2]
    · filter_upwards [Lp.coeFn_smul r (c ij), hp2 ij] with x h1 h2
      simp only [Prod.smul_snd, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1, h2]
      simp only [gradM]
      rw [pd_const_mul (hφ _).differentiable]

/-- The defining identity of the closure of the grad graph, tested against a `C¹` matrix field
`Ψ` (no boundary condition on `Ψ`): `∫ G : Ψ = -Σ_{ij} ∫ v_i ∂_j Ψ_{ij}`. -/
theorem closure_gradGraph_identity (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {v : L2V Ω}
    {G : L2M Ω} (h : (v, G) ∈ closure (gradGraph Ω)) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ∑ ij, ∫ x, G ij x * Ψ ij x ∂volume.restrict Ω =
      -∑ ij : Ix, ∫ x, v ij.1 x * pd ij.2 (Ψ ij) x ∂volume.restrict Ω := by
  have m1 : ∀ ij, MemLp (Ψ ij) 2 (volume.restrict Ω) := fun ij =>
    memLp_of_continuous hΩ hb (hΨ ij).continuous
  have m2 : ∀ ij : Ix, MemLp (pd ij.2 (Ψ ij)) 2 (volume.restrict Ω) := fun ij =>
    memLp_of_continuous hΩ hb (continuous_pd (hΨ _) _)
  have e3 : ∀ i, (Feec.Domain.gradOp 3 3 : Feec.Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.apply
      Ψ i = fun x => -∑ j, pd j (Ψ (i, j)) x :=
    fun i => funext fun x => Feec.Domain.gradOp_formalAdj_apply Ψ i x
  have m3 : ∀ i, MemLp ((Feec.Domain.gradOp 3 3 : Feec.Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.apply
      Ψ i) 2 (volume.restrict Ω) := fun i => by
    rw [e3]
    exact memLp_of_continuous hΩ hb
      (continuous_finsetSum _ fun j _ => continuous_pd (hΨ _) _).neg
  rw [gradGraph_eq_testGraph, ← Submodule.topologicalClosure_coe] at h
  have := (Feec.Domain.gradOp 3 3 : Feec.Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).closure_testGraph_inner
    (N := 1) Feec.Domain.gradOp_isOrderLE h (fun ij => (hΨ ij).of_le (by norm_num)) m1 m3
  rw [Feec.Domain.inner_toL2F, Feec.Domain.inner_toL2F] at this
  simp only [RCLike.conj_to_real] at this
  rw [this, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_finsetSum _ fun j _ => integrable_mul _ (m2 (i, j)), ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [e3, Finset.mul_sum, mul_neg]

/-- A vector field orthogonal to every test vector field vanishes. -/
theorem eq_zero_of_forall_integralV (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {v : L2V Ω}
    (h : ∀ ψ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (ψ i)) →
      ∑ i, ∫ x, v i x * ψ i x ∂volume.restrict Ω = 0) : v = 0 := by
  refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
  refine L2_ext_of_integral hΩ hb fun g hg => ?_
  have e := h (fun k => if k = i then g else 0) fun k => by
    split_ifs
    exacts [hg, IsTest.zero]
  have e2 : ∀ k : Fin 3, ∫ x, v k x * (if k = i then g else 0) x ∂volume.restrict Ω =
      if k = i then ∫ x, v i x * g x ∂volume.restrict Ω else 0 := by
    intro k
    split_ifs with hk
    · rw [hk]
    · simp
  simp only [e2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e
  rw [e]
  have : ∫ x, (0 : L2V Ω).ofLp i x * g x ∂volume.restrict Ω = 0 := by
    rw [integral_mul_eq_inner _ hg.memLp]
    simp
  exact this.symm

/-- The grad graph submodule is the test graph of `Feec.Domain.gradOp 3 3`. -/
theorem gradGraphSub_eq :
    gradGraphSub Ω = (Feec.Domain.gradOp 3 3 : Feec.Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).testGraph Ω :=
  SetLike.coe_injective gradGraph_eq_testGraph

/-- The closure of the grad graph is a graph (grad on `C_c^∞` is closable). -/
theorem gradGraph_closable (hΩ : IsOpen Ω) (_hb : Bornology.IsBounded Ω) :
    ∀ x ∈ (gradGraphSub Ω).topologicalClosure, x.1 = 0 → x.2 = 0 := by
  rw [gradGraphSub_eq]
  exact (Feec.Domain.gradOp 3 3).testGraph_closable hΩ

/-- `grad : H̊¹(Ω; ℝ³) → L²(Ω; ℝ³ˣ³)`. -/
def gradClosure : L2V Ω →ₗ.[ℝ] L2M Ω := (gradGraphSub Ω).topologicalClosure.toLinearPMap

/-- **`gradClosure` is the minimal realization** of the row-wise gradient
(`Feec.Domain.ConstCoeffOp.minimal`). -/
theorem gradClosure_eq_minimal :
    gradClosure (Ω := Ω) =
      (Feec.Domain.gradOp 3 3 : Feec.Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal Ω := by
  rw [gradClosure, gradGraphSub_eq]
  rfl

/-- The graph of `gradClosure` is the closure of the grad graph. -/
theorem gradClosure_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (gradClosure (Ω := Ω)).graph = (gradGraphSub Ω).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (gradGraph_closable hΩ hb)

/-- `(u, grad u)` is a graph-norm limit of `(φₙ, grad φₙ)`, `φₙ ∈ C_c^∞`. -/
theorem mem_closure_gradClosure (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (gradClosure (Ω := Ω)).domain) :
    ((u : L2V Ω), gradClosure u) ∈ closure (gradGraph Ω) :=
  Submodule.mem_graph_toLinearPMap (gradGraph_closable hΩ hb) u

/-- `gradClosure` is a closed operator. -/
theorem isClosed_gradClosure (hΩ : IsOpen Ω) (_hb : Bornology.IsBounded Ω) :
    (gradClosure (Ω := Ω)).IsClosed := by
  rw [gradClosure_eq_minimal]
  exact (Feec.Domain.gradOp 3 3).isClosed_minimal hΩ

/-- The `L²` class of a vector field with components in `C_c^∞(Ω)`. -/
def testFieldV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Ω (φ i)) : L2V Ω :=
  WithLp.toLp 2 fun i => (hφ i).memLp.toLp (φ i)

/-- Reading off the value of a partial map from a point of its graph. -/
theorem apply_eq_of_mem_graph {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T : E →ₗ.[ℝ] F} {a : E} {b : F} (h : (a, b) ∈ T.graph) (ha : a ∈ T.domain) :
    T ⟨a, ha⟩ = b := by
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff T).1 h
  have e : y = ⟨a, ha⟩ := Subtype.ext hy1
  rw [← e]
  exact hy2

/-- `(φ, grad φ)` lies in the graph of `gradClosure` for `φ ∈ C_c^∞(Ω; ℝ³)`. -/
theorem testFieldV_mem_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Ω (φ i)) :
    (testFieldV hφ, testField (isTest_gradM hφ)) ∈ (gradClosure (Ω := Ω)).graph := by
  rw [gradClosure_graph hΩ hb]
  exact subset_closure ⟨φ, hφ, fun i => (hφ i).memLp.coeFn_toLp,
    fun ij => coeFn_testField (isTest_gradM hφ) ij⟩

/-- `C_c^∞(Ω; ℝ³) ⊆ H̊¹(Ω; ℝ³)`. -/
theorem testFieldV_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Ω (φ i)) :
    testFieldV hφ ∈ (gradClosure (Ω := Ω)).domain := by
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 (testFieldV_mem_graph hΩ hb hφ)
  have e : (y : L2V Ω) = testFieldV hφ := hy
  exact e ▸ y.2

/-- On `C_c^∞(Ω; ℝ³)`, `gradClosure` is the classical gradient. -/
theorem gradClosure_testFieldV (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Ω (φ i)) :
    gradClosure ⟨testFieldV hφ, testFieldV_mem_domain hΩ hb hφ⟩ =
      testField (isTest_gradM hφ) :=
  apply_eq_of_mem_graph (testFieldV_mem_graph hΩ hb hφ) _

/-- `H̊¹(Ω; ℝ³)` is dense in `L²(Ω; ℝ³)`. -/
theorem dense_domain_gradClosure (hΩ : IsOpen Ω) (_hb : Bornology.IsBounded Ω) :
    Dense ((gradClosure (Ω := Ω)).domain : Set (L2V Ω)) := by
  rw [gradClosure_eq_minimal]
  exact (Feec.Domain.gradOp 3 3).dense_minimal_domain hΩ

/-- `grad H̊¹ ⊆ H̊(curl)` with `curl grad = 0`. -/
theorem gradClosure_mem_closure_curlGraph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (gradClosure (Ω := Ω)).domain) :
    (gradClosure u, (0 : L2M Ω)) ∈ closure (curlGraph Ω) := by
  let f : L2V Ω × L2M Ω →L[ℝ] L2M Ω × L2M Ω :=
    (ContinuousLinearMap.snd ℝ (L2V Ω) (L2M Ω)).prod 0
  have := map_mem_closure f.continuous (mem_closure_gradClosure hΩ hb u)
    (t := curlGraph Ω) ?_
  · simpa [f] using this
  rintro ⟨v, G⟩ ⟨φ, hφ, -, hp2⟩
  refine ⟨gradM φ, isTest_gradM hφ, fun ij => ⟨hp2 ij, ?_⟩⟩
  filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
  simp only [f, ContinuousLinearMap.prod_apply]
  rw [curlM_gradM (fun i => (hφ i).contDiff.of_le (by simp))]
  simpa using hx


/-- `⟪B, Φ⟫ = Σ_{ij} ∫_Ω B_{ij} Φ_{ij}` for a test matrix field `Φ`. -/
theorem inner_testField (B : L2M Ω) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) :
    ⟪B, testField hΦ⟫ = ∑ ij, ∫ x, B ij x * Φ ij x ∂volume.restrict Ω := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun ij _ => (integral_mul_eq_inner _ (hΦ ij).memLp).symm

/-- `⟪v, φ⟫ = Σ_i ∫_Ω v_i φ_i` for a test vector field `φ`. -/
theorem inner_testFieldV (v : L2V Ω) {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Ω (φ i)) :
    ⟪v, testFieldV hφ⟫ = ∑ i, ∫ x, v i x * φ i x ∂volume.restrict Ω := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => (integral_mul_eq_inner _ (hφ i).memLp).symm

/-- A point of the grad graph is `(φ, grad φ)` as `L²` classes. -/
theorem eq_of_mem_gradGraph {v : L2V Ω} {G : L2M Ω} {φ : Fin 3 → R3 → ℝ}
    (hφ : ∀ i, IsTest Ω (φ i)) (hp1 : ∀ i, (v i : R3 → ℝ) =ᵐ[volume.restrict Ω] φ i)
    (hp2 : ∀ ij, (G ij : R3 → ℝ) =ᵐ[volume.restrict Ω] gradM φ ij) :
    v = testFieldV hφ ∧ G = testField (isTest_gradM hφ) :=
  ⟨(WithLp.ext_iff 2).2 (funext fun i => Lp.ext ((hp1 i).trans (hφ i).memLp.coeFn_toLp.symm)),
    (WithLp.ext_iff 2).2 (funext fun ij =>
      Lp.ext ((hp2 ij).trans (coeFn_testField (isTest_gradM hφ) ij).symm))⟩

/-- If `B` has weak row-wise divergence `D`, then `B ∈ D(grad*)` and `grad* B = -D`. -/
theorem adjoint_gradClosure_of_weakDiv (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B : L2M Ω} {D : L2V Ω} (hD : ∀ φ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (φ i)) →
      ∑ ij : Ix, ∫ x, B ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω =
        -∑ i, ∫ x, D i x * φ i x ∂volume.restrict Ω) :
    ∃ h : B ∈ (gradClosure (Ω := Ω))†.domain, (gradClosure (Ω := Ω))† ⟨B, h⟩ = -D := by
  have key : ∀ u : (gradClosure (Ω := Ω)).domain,
      ⟪-D, (u : L2V Ω)⟫ = ⟪B, gradClosure u⟫ := by
    intro u
    have hsub : gradGraph Ω ⊆
        (fun p : L2V Ω × L2M Ω => ⟪B, p.2⟫ - ⟪-D, p.1⟫) ⁻¹' {0} := by
      rintro ⟨v, G⟩ ⟨φ, hφ, hp1, hp2⟩
      obtain ⟨rfl, rfl⟩ := eq_of_mem_gradGraph hφ hp1 hp2
      simp only [mem_preimage, mem_singleton_iff, inner_neg_left, sub_neg_eq_add]
      rw [inner_testField, inner_testFieldV]
      have := hD φ hφ
      simp only [gradM] at this ⊢
      linarith
    have h := closure_minimal hsub (isClosed_singleton.preimage
      ((continuous_const.inner continuous_snd).sub (continuous_const.inner continuous_fst)))
      (mem_closure_gradClosure hΩ hb u)
    simp only [mem_preimage, mem_singleton_iff, sub_eq_zero] at h
    exact h.symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_domain_gradClosure hΩ hb) ⟨_, hmem⟩ key⟩

/-- The adjoint identity against test vector fields:
`⟪grad* B, φ⟫ = Σ_{ij} ∫ B_{ij} ∂_j φ_i`. -/
theorem adjoint_gradClosure_inner (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (B : (gradClosure (Ω := Ω))†.domain) {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Ω (φ i)) :
    ∑ i, ∫ x, (gradClosure (Ω := Ω))† B i x * φ i x ∂volume.restrict Ω =
      ∑ ij : Ix, ∫ x, B.1 ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω := by
  have e := LinearPMap.adjoint_isFormalAdjoint (dense_domain_gradClosure hΩ hb) B
    ⟨_, testFieldV_mem_domain hΩ hb hφ⟩
  simp only at e
  rw [gradClosure_testFieldV hΩ hb hφ, inner_testField, inner_testFieldV] at e
  exact e

/-- `D(grad*) = H(div)` (row-wise divergence, no boundary condition), `grad* = -div`. -/
theorem mem_adjoint_gradClosure_iff (hΩ : IsOpen Ω) (_hb : Bornology.IsBounded Ω) {B : L2M Ω} :
    B ∈ (gradClosure (Ω := Ω))†.domain ↔ B ∈ HdivM Ω := by
  rw [gradClosure_eq_minimal,
    (Feec.Domain.gradOp 3 3 : Feec.Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).mem_adjoint_minimal_domain_iff hΩ]
  have hneg : ∀ (w : L2V Ω) (φ : Fin 3 → R3 → ℝ) (i : Fin 3),
      ∫ x, (-w) i x * φ i x ∂volume.restrict Ω = -∫ x, w i x * φ i x ∂volume.restrict Ω := by
    intro w φ i
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg (w i)] with x hx
    simp only [PiLp.neg_apply] at hx ⊢
    rw [hx, Pi.neg_apply, neg_mul]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨-w, fun φ hφ => ?_⟩
    have := hw φ (isTestField_of_forall hφ)
    rw [Feec.Models.BoundedDomain.inner_grad_testField _ (isTestField_of_forall hφ),
      Feec.Models.BoundedDomain.inner_testField_eq] at this
    simp only [hneg, Finset.sum_neg_distrib, neg_neg]
    exact this.symm
  · rintro ⟨D, hD⟩
    refine ⟨-D, fun φ hφ => ?_⟩
    rw [Feec.Models.BoundedDomain.inner_grad_testField _ hφ,
      Feec.Models.BoundedDomain.inner_testField_eq]
    have := hD φ fun i => IsTest.ofDomain (hφ i)
    simp only [hneg, Finset.sum_neg_distrib]
    exact this.symm

variable (Ω) in
/-- `H(div, Ω; ℝ³ˣ³, 0)`: weakly (row-wise) divergence-free fields, no boundary condition. -/
def HdivZero : Set (L2M Ω) :=
  {B | ∀ φ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (φ i)) →
    ∑ ij : Ix, ∫ x, B ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0}

/-- `ker grad* = H(div, 0)`. -/
theorem mem_ker_adjoint_gradClosure_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B : L2M Ω} : B ∈ (gradClosure (Ω := Ω))†.ker ↔ B ∈ HdivZero Ω := by
  constructor
  · intro hB φ hφ
    obtain ⟨y, rfl, hy0⟩ := LinearPMap.mem_ker_iff.1 hB
    rw [← adjoint_gradClosure_inner hΩ hb y hφ, hy0]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_mul_eq_inner _ (hφ i).memLp]
    simp
  · intro hB
    obtain ⟨h, h'⟩ := adjoint_gradClosure_of_weakDiv hΩ hb (D := 0) fun φ hφ => by
      rw [hB φ hφ, eq_comm, neg_eq_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_mul_eq_inner _ (hφ i).memLp]
      simp
    exact LinearPMap.mem_ker_iff.2 ⟨⟨B, h⟩, rfl, by rw [h', neg_zero]⟩

end Grad

/-! ## The literal density hypothesis holds in every Hilbert complex -/

section Gen

open Feec.HilbertComplex2 Feec.Constraints LinearPMap

variable {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- In any Hilbert complex, `P_{ker d0*}` maps `D(d1)` into `D(d1)`: `u - P u ∈ (ker d0*)ᗮ =
closure (range d0) ⊆ ker d1`. -/
theorem starProjection_ker_adj0_mem_domain (H : HilbertComplex2 W0 W1 W2) {u : W1}
    (hu : u ∈ H.d1.domain) : (H.d0†.ker).starProjection u ∈ H.d1.domain := by
  have h1 := (H.d0†.ker).sub_starProjection_mem_orthogonal u
  obtain ⟨y, hy, -⟩ := mem_ker_iff.1 (ker_adj0_orth_le H h1)
  have e : (H.d0†.ker).starProjection u = u - (u - (H.d0†.ker).starProjection u) := by abel
  rw [e]
  exact H.d1.domain.sub_mem hu (hy ▸ y.2)

/-- **The thesis' literal density hypothesis holds in every Hilbert complex**: `V1 ∩ ker d0*` is
dense in `ker d0*`. For the thesis' complex this is "`H̊(curl, M) ∩ H(div, M, 0)` is dense in
`H(div, M, 0)`" (`thesisComplex_dense_literal`). Proof: `P_{ker d0*}` maps `D(d1)` into
`D(d1) ∩ ker d0*` (`starProjection_ker_adj0_mem_domain`), is continuous, and `D(d1)` is dense.

Thesis gap: [QuennevilleBelair2015, §4.10, proof of Prop 4.17] infers from this that
"`H̊(curl, M) ∩ L²(TSD)` is dense in `L²(TSD)`"; the inference is invalid and its conclusion
false on bounded domains (`not_dense_TSD_inter_HcurlZero`). -/
theorem dense_domain_d1_inter_ker_adj0 (H : HilbertComplex2 W0 W1 W2) :
    ∀ k ∈ H.d0†.ker, k ∈ closure ((H.d1.domain : Set W1) ∩ H.d0†.ker) := by
  intro k hk
  have := map_mem_closure (H.d0†.ker).starProjection.continuous (H.dense1 k)
    (t := (H.d1.domain : Set W1) ∩ H.d0†.ker) fun u hu =>
      ⟨starProjection_ker_adj0_mem_domain H hu, (H.d0†.ker).starProjection_apply_mem u⟩
  rwa [(H.d0†.ker).starProjection_eq_self_iff.2 hk] at this

end Gen


/-! ## Consequences for Prop 4.17 on bounded domains -/

section Complex

open Feec.HilbertComplex2 Feec.Constraints LinearPMap

variable {W0 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- **The projection hypothesis `hPD` of `Feec.Constraints.prop_4_17` fails on bounded
domains.** Let `H : W0 → L²(Ω; ℝ³ˣ³) → W2` be any Hilbert complex modelling the thesis' bounded
complex in the sense that `V1 = D(d1) ⊆ H̊(curl)` (electric boundary condition) and test fields
lie in `V1 ∩ V1*` (for `H̊¹ → H̊(curl) → L²`: `C_c^∞ ⊆ H̊(curl) ∩ H(div)`). Then for
`S1 = L²(TSD)` and any `S2`, `P_K D(L) ⊄ D(L)`, `K = {0} × S1 × S2`.

See [QuennevilleBelair2015, §4.10, Prop 4.17] and `Feec.Constraints.prop_4_17`. -/
theorem not_projection_hyp (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (H : HilbertComplex2 W0 (L2M Ω) W2) (S2 : Submodule ℝ W2) [S2.HasOrthogonalProjection]
    (hV1 : ∀ u ∈ H.d1.domain, u ∈ HcurlZero Ω)
    (htest : ∀ (Φ : Ix → R3 → ℝ) (hΦ : ∀ ij, IsTest Ω (Φ ij)), testField hΦ ∈ H.midDomain) :
    ¬ ∀ x ∈ H.domL, projKc W0 (TSD Ω) S2 x ∈ H.domL := by
  intro hPD
  obtain ⟨Φ, hΦ, -, -, hnot⟩ := exists_projTSD_not_mem_HcurlZero hΩ hb hne
  have hx : ini W0 (testField hΦ) (0 : W2) ∈ H.domL := by
    rw [Feec.Constraints.mem_domL H, tot_ini]
    exact ⟨Submodule.zero_mem _, htest Φ hΦ, Submodule.zero_mem _⟩
  have h := (Feec.Constraints.mem_domL H).1 (hPD _ hx)
  rw [tot_projKc, tot_ini] at h
  exact hnot (hV1 _ (Submodule.mem_inf.1 h.2.1).1)

/-- **The density hypothesis of `prop_4_17_iff` fails on bounded domains**: if `V1 ⊆ H̊(curl)`,
`D(L) ∩ K` is not dense in `K = {0} × L²(TSD) × S2`; e.g. `(0, diag(1, -1, 0), 0) ∈ K` is not in
its closure. (So `prop_4_17_iff` does not apply; `exists_data_not_propagate` shows directly that
propagation fails.)

Cf. [QuennevilleBelair2015, §4.10, Prop 4.17] and `Feec.Constraints.prop_4_17_iff`. -/
theorem not_dense_domL_inter_Kc (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (H : HilbertComplex2 W0 (L2M Ω) W2) (S2 : Submodule ℝ W2)
    (hV1 : ∀ u ∈ H.d1.domain, u ∈ HcurlZero Ω) :
    ∃ k ∈ Kc W0 (TSD Ω) S2,
      k ∉ closure ((H.domL : Set (Tot W0 (L2M Ω) W2)) ∩ Kc W0 (TSD Ω) S2) := by
  obtain ⟨hK, hKn⟩ := not_dense_TSD_inter_HcurlZero hΩ hb hne
  refine ⟨ini W0 (constField hΩ hb diagA) 0, ?_, fun hk => hKn ?_⟩
  · rw [mem_Kc, tot_ini]
    exact ⟨rfl, hK, Submodule.zero_mem _⟩
  have hπ : Continuous fun y : Tot W0 (L2M Ω) W2 => (tot W0 (L2M Ω) W2 y).2.1 :=
    (continuous_fst.comp continuous_snd).comp (totL (W0 := W0) (W1 := L2M Ω) (W2 := W2)).continuous
  have := map_mem_closure (t := (TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) hπ hk fun y hy => by
    obtain ⟨hyD, hyK⟩ := hy
    exact ⟨((mem_Kc).1 hyK).2.1,
      hV1 _ (Submodule.mem_inf.1 ((Feec.Constraints.mem_domL H).1 hyD).2.1).1⟩
  simpa [tot_ini] using this

/-- The linear field `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` (entries `(0,1)`, `(1,0)` equal to `x 2`). -/
def betaField : Ix → R3 → ℝ := fun ij =>
  if ij = (0, 1) ∨ ij = (1, 0) then (fun x : R3 => x 2) else 0

/-- `β` is smooth. -/
theorem contDiff_betaField (ij : Ix) : ContDiff ℝ ∞ (betaField ij) := by
  unfold betaField
  split_ifs
  exacts [contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 2, contDiff_const]

/-- `curl β = diag(-1, 1, 0) = -diagA`. -/
theorem curlM_betaField (ij : Ix) (x : R3) : curlM betaField ij x = -diagA ij.1 ij.2 := by
  obtain ⟨i, k⟩ := ij
  simp only [curlM, betaField, pd_ite_zero, pd_coord]
  fin_cases i <;> fin_cases k <;> simp [diagA]

/-- The `L²` class of a continuous matrix field on a bounded open `Ω`. -/
def smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : Ix → R3 → ℝ)
    (hΨ : ∀ ij, Continuous (Ψ ij)) : L2M Ω :=
  WithLp.toLp 2 fun ij => (memLp_of_continuous hΩ hb (hΨ ij)).toLp _

/-- The components of `smoothField Ψ` are a.e. `Ψ_{ij}`. -/
theorem coeFn_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : Ix → R3 → ℝ)
    (hΨ : ∀ ij, Continuous (Ψ ij)) (ij : Ix) :
    (smoothField hΩ hb Ψ hΨ ij : R3 → ℝ) =ᵐ[volume.restrict Ω] Ψ ij :=
  MemLp.coeFn_toLp (memLp_of_continuous hΩ hb (hΨ ij))

/-- `⟪F, Ψ⟫ = Σ_{ij} ∫_Ω F_{ij} Ψ_{ij}`. -/
theorem inner_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : Ix → R3 → ℝ)
    (hΨ : ∀ ij, Continuous (Ψ ij)) (F : L2M Ω) :
    ⟪F, smoothField hΩ hb Ψ hΨ⟫ = ∑ ij : Ix, ∫ x, F ij x * Ψ ij x ∂volume.restrict Ω := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun ij _ =>
    (integral_mul_eq_inner _ (memLp_of_continuous hΩ hb (hΨ ij))).symm

/-- `β ∈ L²(TSD)`: symmetric, trace-free, and divergence-free (`∂₂ x₃ = ∂₁ x₃ = 0`). -/
theorem betaField_mem_TSD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    smoothField hΩ hb betaField (fun ij => (contDiff_betaField ij).continuous) ∈ TSD Ω := by
  set K := smoothField hΩ hb betaField (fun ij => (contDiff_betaField ij).continuous)
  have hKc := coeFn_smoothField hΩ hb betaField (fun ij => (contDiff_betaField ij).continuous)
  have hsym : ∀ i j, betaField (i, j) = betaField (j, i) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [betaField]
  have hdiag : ∀ i, betaField (i, i) = 0 := by
    intro i
    fin_cases i <;> simp [betaField]
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [hKc (i, j), hKc (j, i)] with x h1 h2
    rw [h1, h2, hsym]
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (K (0, 0) + K (1, 1)) (K (2, 2)),
      Lp.coeFn_add (K (0, 0)) (K (1, 1)), hKc (0, 0), hKc (1, 1), hKc (2, 2),
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6, hdiag, hdiag, hdiag]
    simp
  · have hpd : ∀ ij : Ix, ∀ x, pd ij.2 (betaField ij) x = 0 := by
      rintro ⟨i, j⟩ x
      fin_cases i <;> fin_cases j <;> simp [betaField, pd_coord, pd_zero]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_congr_ae (g := fun x => pd ij.2 (φ ij.1) x * betaField ij x)
      ((hKc ij).mono fun x hx => by simp only; rw [hx, mul_comm]),
      integral_pd_mul (hφ ij.1) ((contDiff_betaField ij).of_le (by simp)) ij.2]
    simp [hpd]

variable {W0 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0] in
/-- If `d1` is (a restriction of) the closure of curl on `C_c^∞` (the electric boundary
condition), every `C¹` field `Ψ` with no boundary condition lies in `D(d1*)` with
`d1* Ψ = curl Ψ` (`d1* ⊇ curl` on `H(curl)`). -/
theorem smoothField_mem_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (H : HilbertComplex2 W0 (L2M Ω) (L2M Ω))
    (hd1 : ∀ u : H.d1.domain, ((u : L2M Ω), H.d1 u) ∈ closure (curlGraph Ω))
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ∃ h : smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous) ∈ H.d1†.domain,
      H.d1† ⟨_, h⟩ = smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ) := by
  have key : ∀ u : H.d1.domain, ⟪smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ),
      (u : L2M Ω)⟫ = ⟪smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous), H.d1 u⟫ := fun u => by
    rw [real_inner_comm (u : L2M Ω), real_inner_comm (H.d1 u), inner_smoothField,
      inner_smoothField]
    exact (closure_curlGraph_identity hΩ hb (hd1 u) hΨ).symm
  have hmem := mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, adjoint_apply_eq H.dense1 ⟨_, hmem⟩ key⟩

variable {W0 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0] in
/-- **The conclusion of Prop 4.17 fails on every nonempty bounded open `Ω ⊆ ℝ³`** (for every
strong solution; see `exists_orbit_not_propagate` for one that exists given a Stone group, and
`exists_orbit_not_propagate_unconditional` for existence via Stone's theorem). Let
`H : W0 → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` be any Hilbert complex whose `d1` is (a restriction of)
the closure of curl on `C_c^∞` (the thesis' `curl` on `H̊(curl, M)`). Take the TSD datum
`(σ₀, E₀, B₀) = (0, 0, β)`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`, which lies in `D(L) ∩ K`,
`K = {0} × L²(TSD) × L²(TSD)`. Then for every `T > 0`, **every** strong solution of (4.14) on
`[0, T]` with this datum leaves `K`.

Proof: on `K ∩ D(L)`, `E ∈ H̊(curl) ∩ L²(TSD)`, so `ℓ(E) = ⟪E, diag(1, -1, 0)⟫ = 0`
(`integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`). If `U` stayed in `K`, `ℓ(E(t)) ≡ 0` on
`[0, T]`, so `ℓ(Ė(0)) = 0`; but `Ė(0) = -curl β = diag(1, -1, 0)` (`smoothField_mem_adjoint`,
`curlM_betaField`), and `ℓ(diag(1, -1, 0)) = 2 |Ω| > 0`.

As a statement about all strong solutions this is vacuous if none exists; Stone's theorem is not
in Mathlib, and `exists_orbit_not_propagate` supplies the solution from the group stand-in.

Correction: refutes the conclusion (TSD propagation) of [QuennevilleBelair2015, §4.10,
Prop 4.17] on bounded domains. -/
theorem exists_data_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (H : HilbertComplex2 W0 (L2M Ω) (L2M Ω))
    (hd1 : ∀ u : H.d1.domain, ((u : L2M Ω), H.d1 u) ∈ closure (curlGraph Ω)) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini W0 0 B₀ ∈ H.domL ∧ ini W0 0 B₀ ∈ Kc W0 (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, ∀ U : ℝ → Tot W0 (L2M Ω) (L2M Ω),
        IsStrongSolution (-H.waveOp) T (ini W0 0 B₀) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ Kc W0 (TSD Ω) (TSD Ω) := by
  have hβ : ∀ ij, ContDiff ℝ 1 (betaField ij) := fun ij => (contDiff_betaField ij).of_le (by simp)
  set B₀ := smoothField hΩ hb betaField (fun ij => (hβ ij).continuous)
  have hB₀ : B₀ ∈ TSD Ω := betaField_mem_TSD hΩ hb
  obtain ⟨hadj, hadj'⟩ := smoothField_mem_adjoint hΩ hb H hd1 hβ
  have hdom : ini W0 0 B₀ ∈ H.domL := by
    rw [Feec.Constraints.mem_domL H, tot_ini]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, hadj⟩
  refine ⟨B₀, hB₀, hdom, by rw [mem_Kc, tot_ini]; exact ⟨rfl, Submodule.zero_mem _, hB₀⟩, ?_⟩
  intro T hT U hU
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  set K := constField hΩ hb diagA
  let ℓ : Tot W0 (L2M Ω) (L2M Ω) →L[ℝ] ℝ := (innerSL ℝ K).comp
    ((ContinuousLinearMap.fst ℝ (L2M Ω) (L2M Ω)).comp ((ContinuousLinearMap.snd ℝ W0 _).comp
      (totL (W0 := W0) (W1 := L2M Ω) (W2 := L2M Ω)).toContinuousLinearMap))
  have hℓ : ∀ y, ℓ y = ⟪K, (tot W0 (L2M Ω) (L2M Ω) y).2.1⟫ := fun y => rfl
  have hzero : ∀ t ∈ Icc 0 T, ℓ (U t) = 0 := by
    intro t ht
    have hD := (Feec.Constraints.mem_domL H).1 (hU.mem t ht)
    have hE : (tot W0 (L2M Ω) (L2M Ω) (U t)).2.1 ∈ H.d1.domain := (Submodule.mem_inf.1 hD.2.1).1
    rw [hℓ, real_inner_comm, inner_constField]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_eq_zero_of_mem_TSD_of_mem_HcurlZero hΩ hb ((mem_Kc).1 (hall t ht)).2.1
      ⟨_, hd1 ⟨_, hE⟩⟩, mul_zero]
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hd := ℓ.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) (hU.deriv 0 h0)
  have hd0 : HasDerivWithinAt (ℓ ∘ U) 0 (Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Icc 0 T) (0 : ℝ)).congr (fun t ht => hzero t ht)
      (hzero 0 h0)
  have heq := (uniqueDiffOn_Icc hT 0 h0).eq_deriv _ hd hd0
  have hp0 : H.pr0 ⟨U 0, hU.mem 0 h0⟩ = 0 := Subtype.ext (by simp [hU.init])
  have hp2 : H.prV2s ⟨U 0, hU.mem 0 h0⟩ = ⟨B₀, hadj⟩ := Subtype.ext (by simp [hU.init])
  rw [Pi.zero_apply, add_zero, LinearPMap.neg_apply, _root_.map_neg, hℓ, tot_waveOp] at heq
  simp only at heq
  rw [hp0, hp2, hadj', LinearPMap.map_zero, zero_add, real_inner_comm, inner_constField] at heq
  have hI : ∀ ij : Ix, ∫ x, smoothField hΩ hb (curlM betaField) (continuous_curlM hβ) ij x
      ∂volume.restrict Ω = volume.real Ω * -diagA ij.1 ij.2 := fun ij => by
    rw [integral_congr_ae (coeFn_smoothField hΩ hb _ _ ij)]
    simp only [curlM_betaField, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  simp only [hI] at heq
  have hpos : 0 < volume.real Ω := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA] at heq
  linarith

variable {W0 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0] in
/-- **Prop 4.17 fails for the Stone group** (non-vacuous form of
`exists_data_not_propagate`). If `-L` generates an orthogonal group `G` (the Stone stand-in
`Feec.UnitaryGroupGenerator`, as in `Feec.Constraints.prop_4_17_necessary`), the orbit
`t ↦ G.S t (0, 0, β)` **is** a strong solution of (4.14) on every `[0, T]`
(`Feec.Constraints.isStrongSolution_orbit`), and it leaves `K = {0} × L²(TSD) × L²(TSD)`.
Such a `G` always exists by Stone's theorem; the hypothesis-free form is
`exists_orbit_not_propagate_unconditional` (`Feec.Ch4.StoneApplications`).

Correction: refutes the conclusion of [QuennevilleBelair2015, §4.10, Prop 4.17] on bounded
domains, given the group of Thm 4.3, which the thesis invokes and `Feec.stoneGroup` constructs. -/
theorem exists_orbit_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (H : HilbertComplex2 W0 (L2M Ω) (L2M Ω))
    (hd1 : ∀ u : H.d1.domain, ((u : L2M Ω), H.d1 u) ∈ closure (curlGraph Ω))
    (G : UnitaryGroupGenerator (-H.waveOp)) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini W0 0 B₀ ∈ H.domL ∧
      ini W0 0 B₀ ∈ Kc W0 (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, IsStrongSolution (-H.waveOp) T (ini W0 0 B₀) 0 (fun t => G.S t (ini W0 0 B₀)) ∧
        ∃ t ∈ Icc 0 T, G.S t (ini W0 0 B₀) ∉ Kc W0 (TSD Ω) (TSD Ω) := by
  obtain ⟨B₀, hB, hD, hK, hall⟩ := exists_data_not_propagate hΩ hb hne H hd1
  refine ⟨B₀, hB, hD, hK, fun T hT => ?_⟩
  have hU := isStrongSolution_orbit G T ⟨_, hD⟩
  exact ⟨hU, hall T hT _ hU⟩


/-! ### A concrete complex satisfying the hypotheses -/

/-- The zero-dimensional space, used as `W0` in `curlComplex`. -/
abbrev W0triv := EuclideanSpace ℝ (Fin 0)

/-- The Hilbert complex `0 → L²(Ω; ℝ³ˣ³) --curl--> L²(Ω; ℝ³ˣ³)`, with `d1 = curlClosure` (the
thesis' `curl` on `H̊(curl, M)`). It shows that the hypotheses of `not_projection_hyp`,
`not_dense_domL_inter_Kc` and `exists_data_not_propagate`, which only concern `d1` (and
`C_c^∞ ⊆ V1*`), are satisfiable with a trivial `d0`; the thesis' complex
`H̊¹(V) → H̊(curl, M) → L²(M)` is `thesisComplex`. -/
def curlComplex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HilbertComplex2 W0triv (L2M Ω) (L2M Ω) where
  d0 := (0 : W0triv →ₗ[ℝ] L2M Ω).toPMap ⊤
  d1 := curlClosure
  dense0 := by simp [LinearMap.toPMap_domain]
  dense1 := dense_domain_curlClosure hΩ hb
  closed0 := by
    have e : (((0 : W0triv →ₗ[ℝ] L2M Ω).toPMap ⊤).graph : Set (W0triv × L2M Ω)) =
        Prod.snd ⁻¹' {0} := by
      ext ⟨x, y⟩
      simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨z, -, rfl⟩
        rfl
      · rintro rfl
        exact ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩
    rw [LinearPMap.IsClosed, e]
    exact isClosed_singleton.preimage continuous_snd
  closed1 := isClosed_curlClosure hΩ hb
  map_mem := fun _ => Submodule.zero_mem _
  comp_zero := fun x => by
    have : (⟨(0 : W0triv →ₗ[ℝ] L2M Ω).toPMap ⊤ x, Submodule.zero_mem _⟩ :
        (curlClosure (Ω := Ω)).domain) = 0 := Subtype.ext rfl
    rw [this, LinearPMap.map_zero]

/-- `d1` of `curlComplex` is `curlClosure`. -/
theorem curlComplex_d1 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (curlComplex hΩ hb).d1 = curlClosure := rfl

/-- For `d0 = 0`, `D(d0*)` is everything. -/
theorem curlComplex_adjoint_d0_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (y : L2M Ω) :
    y ∈ (curlComplex hΩ hb).d0†.domain :=
  mem_adjoint_domain_of_exists _ ⟨0, fun x => by
    change ⟪(0 : W0triv), (x : W0triv)⟫ = ⟪y, (0 : L2M Ω)⟫
    simp⟩

/-- **The thesis' projection hypothesis fails for `curlComplex`** (unconditionally). -/
theorem curlComplex_not_projection_hyp (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ¬ ∀ x ∈ (curlComplex hΩ hb).domL,
      projKc W0triv (TSD Ω) (TSD Ω) x ∈ (curlComplex hΩ hb).domL :=
  not_projection_hyp hΩ hb hne _ _ (fun _ hu => mem_domain_curlClosure.1 hu)
    fun _ hΦ => Submodule.mem_inf.2
      ⟨mem_domain_curlClosure.2 (testField_mem_HcurlZero hΩ hb hΦ),
        curlComplex_adjoint_d0_domain hΩ hb _⟩

/-- **TSD propagation (the conclusion of Prop 4.17) fails for `curlComplex`**: explicit TSD
data in `D(L)` for which every strong solution of (4.14), on any `[0, T]`, `T > 0`, leaves
`K = {0} × L²(TSD) × L²(TSD)`. -/
theorem curlComplex_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini W0triv 0 B₀ ∈ (curlComplex hΩ hb).domL ∧
      ini W0triv 0 B₀ ∈ Kc W0triv (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, ∀ U : ℝ → Tot W0triv (L2M Ω) (L2M Ω),
        IsStrongSolution (-(curlComplex hΩ hb).waveOp) T (ini W0triv 0 B₀) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ Kc W0triv (TSD Ω) (TSD Ω) :=
  exists_data_not_propagate hΩ hb hne _ (mem_closure_curlClosure hΩ hb)

end Complex

/-! ### The thesis' complex `H̊¹(V) → H̊(curl, M) → L²(M)` -/

section Thesis

open Feec.HilbertComplex2 Feec.Constraints
open scoped LinearPMap

/-- The thesis' complex `H̊¹(Ω; ℝ³) --grad--> H̊(curl, Ω; ℝ³ˣ³) --curl--> L²(Ω; ℝ³ˣ³)`. -/
def thesisComplex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HilbertComplex2 (L2V Ω) (L2M Ω) (L2M Ω) where
  d0 := gradClosure
  d1 := curlClosure
  dense0 := dense_domain_gradClosure hΩ hb
  dense1 := dense_domain_curlClosure hΩ hb
  closed0 := isClosed_gradClosure hΩ hb
  closed1 := isClosed_curlClosure hΩ hb
  map_mem := fun u => mem_domain_curlClosure.2 ⟨0, gradClosure_mem_closure_curlGraph hΩ hb u⟩
  comp_zero := fun u => apply_eq_of_mem_graph
    (by rw [curlClosure_graph hΩ hb]; exact gradClosure_mem_closure_curlGraph hΩ hb u) _

/-- `C_c^∞(Ω; ℝ³ˣ³) ⊆ V1 ∩ V1* = H̊(curl) ∩ H(div)` for `thesisComplex`. -/
theorem thesisComplex_test_mem_midDomain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (Φ : Ix → R3 → ℝ) (hΦ : ∀ ij, IsTest Ω (Φ ij)) :
    testField hΦ ∈ (thesisComplex hΩ hb).midDomain :=
  Submodule.mem_inf.2 ⟨mem_domain_curlClosure.2 (testField_mem_HcurlZero hΩ hb hΦ),
    (mem_adjoint_gradClosure_iff hΩ hb).2 (testField_mem_HdivM hΩ hb hΦ)⟩

/-- `L²(TSD) ⊆ ker d0* = H(div, 0)` for `thesisComplex`: the hypothesis `hS1` of
`Feec.Constraints.prop_4_17` holds, so on bounded domains it is exactly `hPD` that fails. -/
theorem thesisComplex_TSD_le_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    TSD Ω ≤ (thesisComplex hΩ hb).d0†.ker := fun _ hB =>
  (mem_ker_adjoint_gradClosure_iff hΩ hb).2 hB.2.2

/-- **The thesis' density conjecture, as literally stated, is true**: `H̊(curl, M) ∩ H(div, M, 0)`
is dense in `H(div, M, 0)` (weakly divergence-free fields) on every bounded open `Ω`. (Then so is
the larger `H(curl, M) ∩ H(div, M, 0)`: `dense_HcurlM_inter_HdivZero` in
`Feec.Ch4.BoundedDensity`.)

Thesis gap: what fails is the deduction "so that `H̊(curl, M) ∩ L²(TSD)` is dense in `L²(TSD)`"
in [QuennevilleBelair2015, §4.10, proof of Prop 4.17]; see `not_dense_TSD_inter_HcurlZero` and,
on domains star-shaped with respect to a ball, `prop417_density_gap`. -/
theorem thesisComplex_dense_literal (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∀ k ∈ HdivZero Ω, k ∈ closure (HcurlZero Ω ∩ HdivZero Ω) := by
  intro k hk
  have := dense_domain_d1_inter_ker_adj0 (thesisComplex hΩ hb) k
    ((mem_ker_adjoint_gradClosure_iff hΩ hb).2 hk)
  refine closure_mono ?_ this
  rintro u ⟨hu1, hu2⟩
  exact ⟨mem_domain_curlClosure.1 hu1, (mem_ker_adjoint_gradClosure_iff hΩ hb).1 hu2⟩

/-- **The projection hypothesis of Prop 4.17 fails for the thesis' complex**
`H̊¹ → H̊(curl) → L²` on every nonempty bounded open `Ω`, for `S1 = L²(TSD)` and any `S2`.
So Prop 4.17, as stated, has a false hypothesis on bounded domains.

Correction: refutes the first conjecture of [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_not_projection_hyp (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S2 : Submodule ℝ (L2M Ω)) [S2.HasOrthogonalProjection] :
    ¬ ∀ x ∈ (thesisComplex hΩ hb).domL,
      projKc (L2V Ω) (TSD Ω) S2 x ∈ (thesisComplex hΩ hb).domL :=
  not_projection_hyp hΩ hb hne _ S2 (fun _ hu => mem_domain_curlClosure.1 hu)
    (thesisComplex_test_mem_midDomain hΩ hb)

/-- **The conclusion of Prop 4.17 fails for the thesis' complex**: explicit TSD data
`(0, 0, β) ∈ D(L) ∩ K` such that every strong solution of (4.14) on any `[0, T]`, `T > 0`, leaves
`K = {0} × L²(TSD) × L²(TSD)`. (Existence of a solution: `thesisComplex_orbit_not_propagate`.)

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini (L2V Ω) 0 B₀ ∈ (thesisComplex hΩ hb).domL ∧
      ini (L2V Ω) 0 B₀ ∈ Kc (L2V Ω) (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, ∀ U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω),
        IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ Kc (L2V Ω) (TSD Ω) (TSD Ω) :=
  exists_data_not_propagate hΩ hb hne _ (mem_closure_curlClosure hΩ hb)

/-- **The conclusion of Prop 4.17 fails for the thesis' complex, given a Stone group**: if `-L`
generates an orthogonal group `G` (Thm 4.3 via Stone's theorem; `Feec.UnitaryGroupGenerator`),
the orbit of the TSD datum `(0, 0, β)` is a strong solution of (4.14) that leaves `K` on every
`[0, T]`, `T > 0`. Such a `G` always exists by Stone's theorem; the hypothesis-free form is
`thesisComplex_orbit_not_propagate_unconditional` (`Feec.Ch4.StoneApplications`).

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_orbit_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (G : UnitaryGroupGenerator (-(thesisComplex hΩ hb).waveOp)) :
    ∃ B₀ : L2M Ω, B₀ ∈ TSD Ω ∧ ini (L2V Ω) 0 B₀ ∈ (thesisComplex hΩ hb).domL ∧
      ini (L2V Ω) 0 B₀ ∈ Kc (L2V Ω) (TSD Ω) (TSD Ω) ∧
      ∀ T > 0, IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) 0 B₀) 0
          (fun t => G.S t (ini (L2V Ω) 0 B₀)) ∧
        ∃ t ∈ Icc 0 T, G.S t (ini (L2V Ω) 0 B₀) ∉ Kc (L2V Ω) (TSD Ω) (TSD Ω) :=
  exists_orbit_not_propagate hΩ hb hne _ (mem_closure_curlClosure hΩ hb) G

end Thesis

end Feec.BoundedDomain

namespace Feec.BoundedDomain

variable {Ω : Set R3}

/-- **The thesis' complex is the minimal grad–curl complex** of `Feec.Models.BoundedDomain`. -/
theorem thesisComplex_toShort (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (thesisComplex hΩ hb).toShort = Feec.Models.BoundedDomain.gradCurl ℝ hΩ := by
  have h0 : (thesisComplex hΩ hb).d0 = (Feec.Models.BoundedDomain.gradCurl ℝ hΩ).d₀ :=
    gradClosure_eq_minimal
  have h1 : (thesisComplex hΩ hb).d1 = (Feec.Models.BoundedDomain.gradCurl ℝ hΩ).d₁ :=
    curlClosure_eq_minimal
  generalize Feec.Models.BoundedDomain.gradCurl ℝ hΩ = S at h0 h1
  cases S
  simp only at h0 h1
  subst h0 h1
  rfl

end Feec.BoundedDomain
