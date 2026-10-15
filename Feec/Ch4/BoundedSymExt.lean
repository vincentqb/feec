module

public import Feec.Ch4.BoundedSym

/-!
# Prop 4.19 on bounded domains, continued: adjoint domains and the boundary conditions as printed

Sequel to `Feec.Ch4.BoundedSym` (same model: `Ω ⊆ ℝ³` bounded open, `L²(S)`, `L²(T)` the
symmetric and trace-free fields in `L2M Ω`, `L²(TSD)` with no boundary condition). It closes two
items left open there.

## 1. The adjoint domains of (4.16) are exactly the weak spaces

For the thesis' complex (4.16), `symComplexB`:
`H̊²(Ω) --grad grad--> H̊(curl, S) --curl--> L²(T)`,
* `mem_adjoint_curlS_iff`: `D(curl*) = H(sym curl, T)` (`HsymcurlT`: trace-free `B` with a weak
  symmetric curl in `L²(S)`, tested against `C_c^∞(Ω; S)`), and `curl*` is the weak symmetric
  curl (`adjoint_curlS_of_weak`);
* `mem_adjoint_hessS_iff`: `D((grad grad)*) = H(div div, S)` (`HdivdivS`, tested against
  `C_c^∞(Ω)`).
Both mirror `Feec.BoundedDomain.mem_adjoint_curlClosure_iff`; neither has a boundary condition.

## 2. Prop 4.19 with the data space of its statement

Prop 4.19 is stated for data in `H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`, while its
proof (and `symComplexB`) uses `H̊² × (H̊(curl, S) ∩ H(div div, S)) × H(sym curl, T)`. The printed
space is `D(L)` for the complex with the boundary conditions moved to the adjoints:
* `symComplexBC`: `H̊(sym curl, T) --sym curl--> H̊(div div, S) --div div--> L²(Ω)`, closures of the
  operators on `C_c^∞(Ω; T)`, `C_c^∞(Ω; S)` (`symcurlD`, `divdivD`; `div div sym curl = 0`,
  `divdivF_symF_curlM`);
* `symComplexD := symComplexBC.dual`: `H²(Ω) --grad grad--> H(curl, S) --curl--> L²(T)` with no
  boundary condition (`mem_symComplexD_d0_iff`, `mem_symComplexD_d1_iff`: weak Hessian, weak curl),
  `d0* = div div` on `H̊(div div, S)` and `d1* = sym curl` on `H̊(sym curl, T)`
  (`symComplexD_adjoint_d0`, `symComplexD_adjoint_d1`, von Neumann `T** = T`). So
  `D(L) = H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`.

Results for Prop 4.19 on `symComplexD`, on every nonempty bounded open `Ω`
(`symComplexD_diagnosis`):
* **A new zero-mean obstruction.** `ker d0* ⊥ ∇²H²` contains no nonzero constant:
  every `E ∈ ker d0*` has `∫_Ω E = 0` (`integral_eq_zero_of_mem_ker_symComplexD`, tested against
  `∇²(x_a x_b)`), and `L²(TSD) ∩ H̊(div div, S) ⊆ ker d0*` (`TSDS_inf_domain_le_ker`). The boundary
  condition of `H̊(div div, S)` now plays the role that `H̊(curl, S)` plays in `Feec.Ch4.BoundedSym`.
* **Hypotheses.** `L²(TSD) ⊄ ker d0*` (`diag(1, -1, 0) ∉ H̊(div div, S)`,
  `symComplexD_not_TSDS_le_ker`), so `hS1` of `Feec.Constraints.prop_4_17` fails for the thesis'
  `K`. It holds for `TSDSk = L²(TSD) ∩ ker d0*`, which has the same data in `D(L)`
  (`symComplexD_mem_Kc_iff`). The projection hypothesis fails for `K = {0} × L²(TSD) × S2`, every
  `S2` (`symComplexD_not_projection_hyp`: `P_{L²(TSD)} (g · diag(1, -1, 0))` has nonzero mean); the
  density of `H(curl, S) ∩ H̊(div div, S) ∩ L²(TSD)` in `L²(TSD)` fails (`symComplexD_not_dense`).
  `hd1`, `hd1s` hold: Lemma 3.5 without boundary condition (`symComplexD_d1_mem_TSDT`,
  `symComplexD_adjoint_d1_mem_TSDS`).
* **The obstruction does not reach the conclusion.** Unlike for `symComplexB`, the constant
  direction is invisible to the evolution: `⟪sym curl B, diag(1, -1, 0)⟫ = 0` for every
  `B ∈ H̊(sym curl, T)` (`symComplexD_inner_adjoint_d1_constS`), and for TSD data in `D(L)` the
  unique solution has `σ ≡ 0`, `E(t) ∈ ker d0*` and `∫_Ω E(t) = 0` for all `t`
  (`symComplexD_prop_4_16`). The refutation `symComplexB_betaT_not_propagate` has no analogue:
  `β ∉ H̊(sym curl, T)`.
* **What holds** (`symComplexD_prop_4_19_max`): Prop 4.19 on the maximal invariant subspace
  `K* = {0} × S1* × S2*` of `{0} × TSDSk × L²(TSD)`, with every hypothesis of
  `Feec.Constraints.prop_4_17`, maximality, `diag(1, -1, 0) ∉ S1*`, and unconditional existence,
  uniqueness and propagation.

## Correction

[QuennevilleBelair2015, §4.11, Prop 4.19], read with its printed data space
`H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`: on every nonempty bounded open `Ω ⊆ ℝ³` its
projection and density hypotheses are false, and its `K = {0} × L²(TSD) × L²(TSD)` violates the
requirement `L²(TSD) ⊆ ker (div div)` used in the proof (`L²(TSD) ∩ ker (div div)` must be used).
The proof's argument therefore does not apply with either placement of the boundary conditions.

## Thesis gap (open)

Whether the *conclusion* of Prop 4.19 holds for `symComplexD` is not settled. A refutation in the
style of `Feec.Ch4.BoundedSym` needs a vector `N ⊥ D(L) ∩ K` with `⟪L x₀, N⟫ ≠ 0` for some
`x₀ ∈ D(L) ∩ K`; the constant fields (the only such `N` found) give `0`. Heuristically (not formalized), in the
interior the constraint violations `(div E, tr E, skew B, div B)` obey a closed first-order system
(Lemma 3.5), so whether TSD propagates is decided by the boundary conditions this system inherits
from `H̊(div div, S)` and `H̊(sym curl, T)`; deciding it needs boundary regularity (traces,
elliptic estimates) that is not available for general bounded open `Ω` in this framework.
Equivalently (not formalized), it asks whether the closed subspace
`{0} × closure(L²(TSD) ∩ H(curl, S) ∩ H̊(div div, S)) × closure(L²(TSD) ∩ H̊(sym curl, T))` is
invariant under the Hodge wave group, i.e. (time reversal) reduces `L`.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.2 (dual complex), §4.10 (Prop 4.16),
  §4.11 ((4.16)–(4.18), Prop 4.19)
* [ArnoldHu2021], [Eastwood2000] (the `grad grad`–`curl`–`div` complex and its adjoint)
* [Brezis2011] (weak derivatives, the fundamental lemma)
* [AFW2010], [BruningLesch1992] (Hilbert complexes, dual complexes)
* [Pazy1983], §1.10 (Stone's theorem, behind `Feec.HilbertComplex2.waveGroup`)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal ContDiff Matrix LinearPMap
open MeasureTheory Set Filter Topology

namespace Feec.BoundedSym

open Feec.BoundedDomain Feec.HilbertComplex2 Feec.Constraints

variable {Ω : Set R3}

/-! ## A closure lemma -/

/-- A continuous functional vanishing on `S` vanishes on the closure of its span. -/
theorem eq_zero_of_mem_closure_span {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (G : E →L[ℝ] ℝ) (hS : ∀ p ∈ S, G p = 0) {p : E}
    (hp : p ∈ (Submodule.span ℝ S).topologicalClosure) : G p = 0 := by
  have hle : Submodule.span ℝ S ≤ LinearMap.ker (G : E →ₗ[ℝ] ℝ) :=
    Submodule.span_le.2 fun q hq => by simpa using hS q hq
  have := Submodule.topologicalClosure_minimal _ hle G.isClosed_ker hp
  simpa using this

/-! ## `D(curl*) = H(sym curl, T)` and `D((grad grad)*) = H(div div, S)` for (4.16) -/

variable (Ω) in
/-- `H(sym curl, Ω; T)` (**no** boundary condition): trace-free `B` with a weak symmetric curl
`C ∈ L²(Ω; S)`, `∫ B : curl Φ = ∫ C : Φ` for every symmetric test field `Φ ∈ C_c^∞(Ω; S)`. -/
def HsymcurlT : Set (L2T Ω) :=
  {B | ∃ C : L2S Ω, ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) → (∀ i j, Φ (i, j) = Φ (j, i)) →
    ∑ ij, ∫ x, (B : L2M Ω) ij x * curlM Φ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, (C : L2M Ω) ij x * Φ ij x ∂volume.restrict Ω}

variable (Ω) in
/-- `H(div div, Ω; S)` (**no** boundary condition): symmetric `B` with a weak double divergence
`D ∈ L²(Ω)`, `Σ_{ij} ∫ B_{ij} ∂_j ∂_i φ = ∫ D φ` for every `φ ∈ C_c^∞(Ω)`. -/
def HdivdivS : Set (L2S Ω) :=
  {B | ∃ D : L2 Ω, ∀ φ : R3 → ℝ, IsTest Ω φ →
    ∑ ij, ∫ x, (B : L2M Ω) ij x * hessField φ ij x ∂volume.restrict Ω =
      ∫ x, D x * φ x ∂volume.restrict Ω}

/-- **`curl* ⊇ weak sym curl`**: if `B ∈ L²(T)` has a weak symmetric curl `C`, then
`B ∈ D(curl*)` and `curl* B = C`, for `curl` on `H̊(curl, S)`. -/
theorem adjoint_curlS_of_weak (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2T Ω}
    {C : L2S Ω} (hC : ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) → (∀ i j, Φ (i, j) = Φ (j, i)) →
      ∑ ij, ∫ x, (B : L2M Ω) ij x * curlM Φ ij x ∂volume.restrict Ω =
        ∑ ij, ∫ x, (C : L2M Ω) ij x * Φ ij x ∂volume.restrict Ω) :
    ∃ h : B ∈ (curlS (Ω := Ω))†.domain, (curlS (Ω := Ω))† ⟨B, h⟩ = C := by
  have key : ∀ u : (curlS (Ω := Ω)).domain, ⟪C, (u : L2S Ω)⟫ = ⟪B, curlS u⟫ := by
    intro u
    let G : L2M Ω × L2M Ω →L[ℝ] ℝ :=
      (innerSL ℝ (B : L2M Ω)).comp (ContinuousLinearMap.snd ℝ _ _) -
        (innerSL ℝ (C : L2M Ω)).comp (ContinuousLinearMap.fst ℝ _ _)
    have hG : ∀ p : L2M Ω × L2M Ω, G p = ⟪(B : L2M Ω), p.2⟫ - ⟪(C : L2M Ω), p.1⟫ := fun p => rfl
    have hS : ∀ p ∈ curlGraphS Ω, G p = 0 := by
      rintro ⟨v, c⟩ ⟨Φ, hΦ, hs, hp⟩
      obtain ⟨rfl, rfl⟩ := eq_of_mem_curlGraph hΦ hp
      change ⟪(B : L2M Ω), testField (isTest_curlM hΦ)⟫ - ⟪(C : L2M Ω), testField hΦ⟫ = 0
      rw [inner_testField, inner_testField, hC Φ hΦ hs, sub_self]
    have h := eq_zero_of_mem_closure_span G hS (mem_closure_curlS hΩ hb u)
    rw [hG, sub_eq_zero] at h
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact h.symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_domain_curlS hΩ hb) ⟨_, hmem⟩ key⟩

/-- **`D(curl*) = H(sym curl, T)`** for `curl` on `H̊(curl, S)` (no boundary condition on
`D(curl*)`), and `curl*` is the weak symmetric curl. -/
theorem mem_adjoint_curlS_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2T Ω} :
    B ∈ (curlS (Ω := Ω))†.domain ↔ B ∈ HsymcurlT Ω := by
  constructor
  · intro hB
    exact ⟨(curlS (Ω := Ω))† ⟨B, hB⟩, fun Φ hΦ hs =>
      (adjoint_curlS_inner hΩ hb ⟨B, hB⟩ hΦ hs).symm⟩
  · rintro ⟨C, hC⟩
    exact (adjoint_curlS_of_weak hΩ hb hC).1

/-- **`D((grad grad)*) = H(div div, S)`** for `grad grad` on `H̊²(Ω)` (no boundary condition on
`D((grad grad)*)`), and `(grad grad)*` is the weak double divergence. -/
theorem mem_adjoint_hessS_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2S Ω} :
    B ∈ (hessS (Ω := Ω))†.domain ↔ B ∈ HdivdivS Ω := by
  constructor
  · intro hB
    refine ⟨(hessS (Ω := Ω))† ⟨B, hB⟩, fun φ hφ => ?_⟩
    have e := LinearPMap.adjoint_isFormalAdjoint (dense_domain_hessS hΩ hb) ⟨B, hB⟩
      ⟨_, testFieldR_mem_domain hΩ hb hφ⟩
    simp only at e
    rw [hessS_testFieldR hΩ hb hφ, inner_hessTestField, inner_testFieldR] at e
    exact e.symm
  · rintro ⟨D, hD⟩
    exact (adjoint_hessS_of_weak hΩ hb hD).1

/-- The thesis' complex (4.16): `D(d1*) = H(sym curl, T)`. -/
theorem symComplexB_adjoint_d1_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2T Ω} :
    B ∈ (symComplexB hΩ hb).d1†.domain ↔ B ∈ HsymcurlT Ω :=
  mem_adjoint_curlS_iff hΩ hb

/-- The thesis' complex (4.16): `D(d0*) = H(div div, S)`. -/
theorem symComplexB_adjoint_d0_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2S Ω} :
    B ∈ (symComplexB hΩ hb).d0†.domain ↔ B ∈ HdivdivS Ω :=
  mem_adjoint_hessS_iff hΩ hb

/-! ## Auxiliary: trace-free parts, symmetric parts, smooth fields -/

/-- A matrix field equal a.e. to a continuous field `F` is `smoothField F`. -/
theorem eq_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {p : L2M Ω}
    {F : Ix → R3 → ℝ} (hF : ∀ ij, Continuous (F ij))
    (hp : ∀ ij, (p ij : R3 → ℝ) =ᵐ[volume.restrict Ω] F ij) : p = smoothField hΩ hb F hF :=
  (WithLp.ext_iff 2).2 (funext fun ij =>
    Lp.ext ((hp ij).trans (coeFn_smoothField hΩ hb F hF ij).symm))

/-- `∫ Σ p_{ij} Ψ_{ij}` depends only on the a.e. class of the components of `p`. -/
theorem sum_integral_congr {p : L2M Ω} {F : Ix → R3 → ℝ}
    (hp : ∀ ij, (p ij : R3 → ℝ) =ᵐ[volume.restrict Ω] F ij) (Ψ : Ix → R3 → ℝ) :
    ∑ ij, ∫ x, p ij x * Ψ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, F ij x * Ψ ij x ∂volume.restrict Ω :=
  Finset.sum_congr rfl fun ij _ =>
    integral_congr_ae ((hp ij).mono fun x hx => by simp only; rw [hx])

/-- The trace-free part `dev Ψ = Ψ - ⅓ (tr Ψ) I` of a matrix field. -/
def devF (Ψ : Ix → R3 → ℝ) : Ix → R3 → ℝ := fun ij x =>
  Ψ ij x - diagOf (fun y => (∑ k, Ψ (k, k) y) / 3) ij x

theorem devF_trace (Ψ : Ix → R3 → ℝ) (x : R3) : ∑ i, devF Ψ (i, i) x = 0 := by
  simp only [devF, diagOf, Fin.sum_univ_three]
  simp
  ring

theorem isTest_diagOf {g : R3 → ℝ} (hg : IsTest Ω g) (ij : Ix) : IsTest Ω (diagOf g ij) := by
  unfold diagOf
  split_ifs
  exacts [hg, IsTest.zero]

theorem continuous_diagOf {g : R3 → ℝ} (hg : Continuous g) (ij : Ix) :
    Continuous (diagOf g ij) := by
  unfold diagOf
  split_ifs
  exacts [hg, continuous_const]

theorem isTest_trace {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, IsTest Ω (Ψ ij)) :
    IsTest Ω (fun y => (∑ k, Ψ (k, k) y) / 3) := by
  have h := (((hΨ (0, 0)).add (hΨ (1, 1))).add (hΨ (2, 2))).const_mul (1 / 3)
  convert h using 1
  funext y
  simp only [Fin.sum_univ_three, Pi.add_apply]
  ring

/-- The trace-free part of a test field is a test field. -/
theorem isTest_devF {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, IsTest Ω (Ψ ij)) (ij : Ix) :
    IsTest Ω (devF Ψ ij) :=
  (hΨ ij).sub (isTest_diagOf (isTest_trace hΨ) ij)

/-- Trace-free fields pair with `g I` to zero. -/
theorem sum_integral_mul_diagOf_eq_zero {v : L2M Ω} (hv : v ∈ trL2 Ω) {g : R3 → ℝ}
    (hg : MemLp g 2 (volume.restrict Ω)) :
    ∑ ij : Ix, ∫ x, v ij x * diagOf g ij x ∂volume.restrict Ω = 0 := by
  have e2 : ∑ ij : Ix, ∫ x, v ij x * diagOf g ij x ∂volume.restrict Ω =
      ∑ i, ∫ x, v (i, i) x * g x ∂volume.restrict Ω := by
    simp only [diagOf]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  rw [e2]
  simp only [fun f : L2 Ω => integral_mul_eq_inner f hg]
  rw [← sum_inner, (mem_trL2 (B := v)).1 hv, inner_zero_left]

/-- Trace-free fields pair with `Ψ` as with its trace-free part. -/
theorem sum_integral_mul_devF (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {v : L2M Ω}
    (hv : v ∈ trL2 Ω) {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) :
    ∑ ij : Ix, ∫ x, v ij x * devF Ψ ij x ∂volume.restrict Ω =
      ∑ ij : Ix, ∫ x, v ij x * Ψ ij x ∂volume.restrict Ω := by
  have hg : Continuous fun y => (∑ k, Ψ (k, k) y) / 3 :=
    (continuous_finsetSum _ fun k _ => hΨ _).div_const 3
  have e : ∀ ij : Ix, ∫ x, v ij x * devF Ψ ij x ∂volume.restrict Ω =
      ∫ x, v ij x * Ψ ij x ∂volume.restrict Ω -
        ∫ x, v ij x * diagOf (fun y => (∑ k, Ψ (k, k) y) / 3) ij x ∂volume.restrict Ω := by
    intro ij
    rw [← integral_sub (integrable_mul _ (memLp_of_continuous hΩ hb (hΨ ij)))
      (integrable_mul _ (memLp_of_continuous hΩ hb (continuous_diagOf hg ij)))]
    congr 1
    ext x
    simp only [devF]
    ring
  rw [Finset.sum_congr rfl fun ij _ => e ij, Finset.sum_sub_distrib,
    sum_integral_mul_diagOf_eq_zero hv (memLp_of_continuous hΩ hb hg), sub_zero]

/-- Pointwise: a symmetric `Ψ` pairs with `M` as with `sym M`. -/
theorem sum_symF_mul (M Ψ : Ix → R3 → ℝ) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) (x : R3) :
    ∑ ij : Ix, symF M ij x * Ψ ij x = ∑ ij : Ix, M ij x * Ψ ij x := by
  have h : ∑ ij : Ix, M (ij.2, ij.1) x * Ψ ij x = ∑ ij : Ix, M ij x * Ψ ij x := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
    obtain ⟨j, k⟩ := jk
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hs j k]
  have e : ∀ ij : Ix, symF M ij x * Ψ ij x =
      (M ij x * Ψ ij x + M (ij.2, ij.1) x * Ψ ij x) / 2 := fun ij => by
    simp only [symF]
    ring
  simp only [e, ← Finset.sum_div, Finset.sum_add_distrib, h]
  ring

/-- Trace-free test fields: `C_c^∞(Ω; T)`. -/
def testFieldT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) (htr : ∀ x, ∑ i, Φ (i, i) x = 0) : L2T Ω :=
  ⟨smoothField hΩ hb Φ (fun ij => (hΦ ij).continuous), smoothField_mem_trL2 hΩ hb _ htr⟩

/-- `sym curl Φ` of a trace-free test field, in `L²(S)`. -/
def symcurlTestField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) : L2S Ω :=
  ⟨smoothField hΩ hb (symF (curlM Φ)) (continuous_symF (continuous_curlM fun ij =>
    (hΦ ij).contDiff_one)), smoothField_mem_symL2 hΩ hb _ (symF_swap _)⟩

/-- `div div Ψ` of a test field, in `L²(Ω)`. -/
def divdivTestField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, IsTest Ω (Ψ ij)) : L2 Ω :=
  (memLp_of_continuous hΩ hb (continuous_divdivF fun ij =>
    (hΨ ij).contDiff.of_le (by simp))).toLp _

/-- Symmetric test fields are dense in `L²(S)`. -/
theorem eq_zero_of_forall_symTest (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {v : L2S Ω}
    (h : ∀ Ψ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Ψ ij)) → (∀ i j, Ψ (i, j) = Ψ (j, i)) →
      ∑ ij, ∫ x, (v : L2M Ω) ij x * Ψ ij x ∂volume.restrict Ω = 0) : v = 0 := by
  refine Subtype.ext (eq_zero_of_forall_integral hΩ hb fun Ψ hΨ => ?_)
  rw [← sum_integral_mul_symF hΩ hb v.2 fun ij => (hΨ ij).continuous]
  exact h _ (isTest_symF hΨ) (symF_swap Ψ)

/-- Trace-free test fields are dense in `L²(T)`. -/
theorem eq_zero_of_forall_trTest (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {v : L2T Ω}
    (h : ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) → (∀ x, ∑ i, Φ (i, i) x = 0) →
      ∑ ij, ∫ x, (v : L2M Ω) ij x * Φ ij x ∂volume.restrict Ω = 0) : v = 0 := by
  refine Subtype.ext (eq_zero_of_forall_integral hΩ hb fun Ψ hΨ => ?_)
  rw [← sum_integral_mul_devF hΩ hb v.2 fun ij => (hΨ ij).continuous]
  exact h _ (isTest_devF hΨ) (devF_trace Ψ)

/-! ## `sym curl : H̊(sym curl, T) → L²(S)` -/

variable (Ω) in
/-- The graph of `sym curl` on trace-free test fields `C_c^∞(Ω; T)`. -/
def symcurlGraph : Set (L2M Ω × L2M Ω) :=
  {p | ∃ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) ∧ (∀ x, ∑ i, Φ (i, i) x = 0) ∧
    ∀ ij, (p.1 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] Φ ij ∧
      (p.2 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] symF (curlM Φ) ij}

variable (Ω) in
/-- The span of `symcurlGraph`. -/
def symcurlGraphSub : Submodule ℝ (L2M Ω × L2M Ω) := Submodule.span ℝ (symcurlGraph Ω)

/-- The defining identity of `H̊(sym curl, T)`, tested against a symmetric `C¹` field `Ψ`
(no boundary condition on `Ψ`): `∫ C : Ψ = ∫ B : curl Ψ`. -/
theorem closure_symcurlGraph_identity (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B C : L2M Ω} (h : (B, C) ∈ (symcurlGraphSub Ω).topologicalClosure) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) :
    ∑ ij, ∫ x, C ij x * Ψ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, B ij x * curlM Ψ ij x ∂volume.restrict Ω := by
  have hc : ∀ ij, Continuous (Ψ ij) := fun ij => (hΨ ij).continuous
  let G : L2M Ω × L2M Ω →L[ℝ] ℝ :=
    (innerSL ℝ (smoothField hΩ hb Ψ hc)).comp (ContinuousLinearMap.snd ℝ _ _) -
      (innerSL ℝ (smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ))).comp
        (ContinuousLinearMap.fst ℝ _ _)
  have hG : ∀ p : L2M Ω × L2M Ω, G p = ∑ ij, ∫ x, p.2 ij x * Ψ ij x ∂volume.restrict Ω -
      ∑ ij, ∫ x, p.1 ij x * curlM Ψ ij x ∂volume.restrict Ω := by
    intro p
    change ⟪smoothField hΩ hb Ψ hc, p.2⟫ -
      ⟪smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ), p.1⟫ = _
    rw [real_inner_comm, inner_smoothField, real_inner_comm, inner_smoothField]
  have hS : ∀ p ∈ symcurlGraph Ω, G p = 0 := by
    rintro ⟨u, c⟩ ⟨Φ, hΦ, -, hp⟩
    rw [hG, sub_eq_zero, sum_integral_congr (fun ij => (hp ij).2),
      sum_integral_congr (fun ij => (hp ij).1)]
    have hi : ∀ ij, Integrable (fun x => symF (curlM Φ) ij x * Ψ ij x) (volume.restrict Ω) :=
      fun ij => integrable_mul_of_compact (isTest_symF (isTest_curlM hΦ) ij).continuous
        (isTest_symF (isTest_curlM hΦ) ij).hasCompactSupport (hc ij)
    have hi' : ∀ ij, Integrable (fun x => curlM Φ ij x * Ψ ij x) (volume.restrict Ω) :=
      fun ij => integrable_mul_of_compact (isTest_curlM hΦ ij).continuous
        (isTest_curlM hΦ ij).hasCompactSupport (hc ij)
    rw [← integral_finsetSum _ fun ij _ => hi ij]
    simp only [sum_symF_mul _ _ hs]
    rw [integral_finsetSum _ fun ij _ => hi' ij]
    exact sum_integral_curlM_mul hΦ hΨ
  have := eq_zero_of_mem_closure_span G hS h
  rw [hG, sub_eq_zero] at this
  exact this

/-- The embedding `L²(T) × L²(S) → L²(M) × L²(M)`. -/
def embTS : L2T Ω × L2S Ω →L[ℝ] L2M Ω × L2M Ω := (trL2 Ω).subtypeL.prodMap (symL2 Ω).subtypeL

variable (Ω) in
/-- The graph of `sym curl` on `H̊(sym curl, T)`: the closure of
`{(Φ, sym curl Φ) : Φ ∈ C_c^∞(Ω; T)}`. -/
def symcurlDGraph : Submodule ℝ (L2T Ω × L2S Ω) :=
  (symcurlGraphSub Ω).topologicalClosure.comap (embTS (Ω := Ω)).toLinearMap

theorem symcurlDGraph_closable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∀ x ∈ symcurlDGraph Ω, x.1 = 0 → x.2 = 0 := by
  rintro ⟨u, w⟩ hx (h0 : u = 0)
  subst h0
  have hx' : (((0 : L2T Ω) : L2M Ω), (w : L2M Ω)) ∈ (symcurlGraphSub Ω).topologicalClosure := hx
  refine eq_zero_of_forall_symTest hΩ hb fun Ψ hΨ hs => ?_
  rw [closure_symcurlGraph_identity hΩ hb hx' (fun ij => (hΨ ij).contDiff_one) hs,
    ← inner_smoothField hΩ hb _ (continuous_curlM fun ij => (hΨ ij).contDiff_one),
    ZeroMemClass.coe_zero, inner_zero_left]

/-- **`sym curl : H̊(sym curl, Ω; T) → L²(Ω; S)`**, the closure of `sym curl` on `C_c^∞(Ω; T)`
(the boundary condition is "`sym (B × n) = 0`"). -/
def symcurlD : L2T Ω →ₗ.[ℝ] L2S Ω := (symcurlDGraph Ω).toLinearPMap

theorem symcurlD_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (symcurlD (Ω := Ω)).graph = symcurlDGraph Ω :=
  Submodule.toLinearPMap_graph_eq _ (symcurlDGraph_closable hΩ hb)

theorem isClosed_symcurlD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (symcurlD (Ω := Ω)).IsClosed := by
  rw [LinearPMap.IsClosed, symcurlD_graph hΩ hb]
  exact (Submodule.isClosed_topologicalClosure _).preimage embTS.continuous

theorem mem_closure_symcurlD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (symcurlD (Ω := Ω)).domain) :
    ((u : L2M Ω), (symcurlD u : L2M Ω)) ∈ (symcurlGraphSub Ω).topologicalClosure :=
  Submodule.mem_graph_toLinearPMap (symcurlDGraph_closable hΩ hb) u

theorem testFieldT_mem_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) (htr : ∀ x, ∑ i, Φ (i, i) x = 0) :
    (testFieldT hΩ hb hΦ htr, symcurlTestField hΩ hb hΦ) ∈ (symcurlD (Ω := Ω)).graph := by
  rw [symcurlD_graph hΩ hb]
  refine subset_closure (Submodule.subset_span ⟨Φ, hΦ, htr, fun ij => ⟨?_, ?_⟩⟩)
  · exact coeFn_smoothField hΩ hb Φ (fun ij => (hΦ ij).continuous) ij
  · exact coeFn_smoothField hΩ hb _
      (continuous_symF (continuous_curlM fun ij => (hΦ ij).contDiff_one)) ij

/-- `C_c^∞(Ω; T) ⊆ H̊(sym curl, T)`. -/
theorem testFieldT_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) (htr : ∀ x, ∑ i, Φ (i, i) x = 0) :
    testFieldT hΩ hb hΦ htr ∈ (symcurlD (Ω := Ω)).domain := by
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 (testFieldT_mem_graph hΩ hb hΦ htr)
  have e : (y : L2T Ω) = testFieldT hΩ hb hΦ htr := hy
  exact e ▸ y.2

theorem symcurlD_testFieldT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) (htr : ∀ x, ∑ i, Φ (i, i) x = 0) :
    symcurlD ⟨_, testFieldT_mem_domain hΩ hb hΦ htr⟩ = symcurlTestField hΩ hb hΦ :=
  apply_eq_of_mem_graph (testFieldT_mem_graph hΩ hb hΦ htr) _

theorem dense_domain_symcurlD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    Dense ((symcurlD (Ω := Ω)).domain : Set (L2T Ω)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  refine eq_zero_of_forall_trTest hΩ hb fun Φ hΦ htr => ?_
  have h0 := (Submodule.mem_orthogonal' _ _).1 hv _ (testFieldT_mem_domain hΩ hb hΦ htr)
  rw [Submodule.coe_inner, testFieldT, inner_smoothField] at h0
  exact h0

/-! ## `div div : H̊(div div, S) → L²(Ω)` -/

variable (Ω) in
/-- The graph of `div div` on symmetric test fields `C_c^∞(Ω; S)`. -/
def divdivGraph : Set (L2M Ω × L2 Ω) :=
  {p | ∃ Ψ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Ψ ij)) ∧ (∀ i j, Ψ (i, j) = Ψ (j, i)) ∧
    (∀ ij, (p.1 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] Ψ ij) ∧
      (p.2 : R3 → ℝ) =ᵐ[volume.restrict Ω] divdivF Ψ}

variable (Ω) in
/-- The span of `divdivGraph`. -/
def divdivGraphSub : Submodule ℝ (L2M Ω × L2 Ω) := Submodule.span ℝ (divdivGraph Ω)

/-- Integration by parts twice: `∫ (div div Ψ) φ = ∫ Ψ : ∇²φ` for `Ψ ∈ C_c^∞(Ω; ℝ³ˣ³)` and
`φ ∈ C²` (no boundary condition on `φ`). -/
theorem integral_divdivF_mul {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, IsTest Ω (Ψ ij)) {φ : R3 → ℝ}
    (hφ : ContDiff ℝ 2 φ) :
    ∫ x, divdivF Ψ x * φ x ∂volume.restrict Ω =
      ∑ ij, ∫ x, Ψ ij x * hessField φ ij x ∂volume.restrict Ω := by
  have hi : ∀ ij : Ix, Integrable (fun x => BoundedDomain.pd ij.1 (BoundedDomain.pd ij.2 (Ψ ij)) x *
      φ x) (volume.restrict Ω) := fun ij =>
    integrable_mul_of_compact ((hΨ ij).pdiff _ |>.pdiff _).continuous
      ((hΨ ij).pdiff _ |>.pdiff _).hasCompactSupport hφ.continuous
  simp only [divdivF, Finset.sum_mul]
  rw [integral_finsetSum _ fun ij _ => hi ij]
  refine Finset.sum_congr rfl fun ij _ => ?_
  exact integral_hessField_mul (hΨ ij) hφ ij.2 ij.1

/-- The defining identity of `H̊(div div, S)`, tested against a `C²` function `φ` (no boundary
condition on `φ`): `∫ f φ = ∫ B : ∇²φ`. -/
theorem closure_divdivGraph_identity (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B : L2M Ω} {f : L2 Ω} (h : (B, f) ∈ (divdivGraphSub Ω).topologicalClosure) {φ : R3 → ℝ}
    (hφ : ContDiff ℝ 2 φ) :
    ∫ x, f x * φ x ∂volume.restrict Ω =
      ∑ ij, ∫ x, B ij x * hessField φ ij x ∂volume.restrict Ω := by
  have hH : ∀ ij, Continuous (hessField φ ij) := fun ij =>
    continuous_pd (contDiff_pd hφ ij.1) ij.2
  have hm := memLp_of_continuous hΩ hb hφ.continuous
  let G : L2M Ω × L2 Ω →L[ℝ] ℝ :=
    (innerSL ℝ (hm.toLp φ)).comp (ContinuousLinearMap.snd ℝ _ _) -
      (innerSL ℝ (smoothField hΩ hb (hessField φ) hH)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hG : ∀ p : L2M Ω × L2 Ω, G p = ∫ x, p.2 x * φ x ∂volume.restrict Ω -
      ∑ ij, ∫ x, p.1 ij x * hessField φ ij x ∂volume.restrict Ω := by
    intro p
    change ⟪hm.toLp φ, p.2⟫ - ⟪smoothField hΩ hb (hessField φ) hH, p.1⟫ = _
    rw [real_inner_comm, ← integral_mul_eq_inner, real_inner_comm, inner_smoothField]
  have hS : ∀ p ∈ divdivGraph Ω, G p = 0 := by
    rintro ⟨u, c⟩ ⟨Ψ, hΨ, -, hp1, hp2⟩
    rw [hG, sub_eq_zero, sum_integral_congr hp1]
    rw [integral_congr_ae (hp2.mono fun x hx => by simp only; rw [hx])]
    exact integral_divdivF_mul hΨ hφ
  have := eq_zero_of_mem_closure_span G hS h
  rw [hG, sub_eq_zero] at this
  exact this

/-- The embedding `L²(S) × L²(Ω) → L²(M) × L²(Ω)`. -/
def embSR : L2S Ω × L2 Ω →L[ℝ] L2M Ω × L2 Ω :=
  (symL2 Ω).subtypeL.prodMap (ContinuousLinearMap.id ℝ (L2 Ω))

variable (Ω) in
/-- The graph of `div div` on `H̊(div div, S)`: the closure of
`{(Ψ, div div Ψ) : Ψ ∈ C_c^∞(Ω; S)}`. -/
def divdivDGraph : Submodule ℝ (L2S Ω × L2 Ω) :=
  (divdivGraphSub Ω).topologicalClosure.comap (embSR (Ω := Ω)).toLinearMap

theorem divdivDGraph_closable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∀ x ∈ divdivDGraph Ω, x.1 = 0 → x.2 = 0 := by
  rintro ⟨u, f⟩ hx (h0 : u = 0)
  subst h0
  have hx' : (((0 : L2S Ω) : L2M Ω), f) ∈ (divdivGraphSub Ω).topologicalClosure := hx
  show f = 0
  refine L2_ext_of_integral hΩ hb fun g hg => ?_
  rw [closure_divdivGraph_identity hΩ hb hx' (hg.contDiff.of_le (by simp)),
    ← inner_smoothField hΩ hb _ (fun ij => (isTest_hessField hg ij).continuous),
    ZeroMemClass.coe_zero, inner_zero_left, integral_mul_eq_inner _ hg.memLp, inner_zero_left]

/-- **`div div : H̊(div div, Ω; S) → L²(Ω)`**, the closure of `div div` on `C_c^∞(Ω; S)`. -/
def divdivD : L2S Ω →ₗ.[ℝ] L2 Ω := (divdivDGraph Ω).toLinearPMap

theorem divdivD_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (divdivD (Ω := Ω)).graph = divdivDGraph Ω :=
  Submodule.toLinearPMap_graph_eq _ (divdivDGraph_closable hΩ hb)

theorem isClosed_divdivD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (divdivD (Ω := Ω)).IsClosed := by
  rw [LinearPMap.IsClosed, divdivD_graph hΩ hb]
  exact (Submodule.isClosed_topologicalClosure _).preimage embSR.continuous

theorem mem_closure_divdivD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (divdivD (Ω := Ω)).domain) :
    ((u : L2M Ω), (divdivD u : L2 Ω)) ∈ (divdivGraphSub Ω).topologicalClosure :=
  Submodule.mem_graph_toLinearPMap (divdivDGraph_closable hΩ hb) u

theorem testFieldS_mem_graph_divdivD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, IsTest Ω (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) :
    (testFieldS hΩ hb hΨ hs, divdivTestField hΩ hb hΨ) ∈ (divdivD (Ω := Ω)).graph := by
  rw [divdivD_graph hΩ hb]
  refine subset_closure (Submodule.subset_span ⟨Ψ, hΨ, hs, fun ij => ?_, ?_⟩)
  · exact coeFn_smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous) ij
  · exact (memLp_of_continuous hΩ hb (continuous_divdivF fun ij =>
      (hΨ ij).contDiff.of_le (by simp))).coeFn_toLp

/-- `C_c^∞(Ω; S) ⊆ H̊(div div, S)`. -/
theorem testFieldS_mem_domain_divdivD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, IsTest Ω (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) :
    testFieldS hΩ hb hΨ hs ∈ (divdivD (Ω := Ω)).domain := by
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 (testFieldS_mem_graph_divdivD hΩ hb hΨ hs)
  have e : (y : L2S Ω) = testFieldS hΩ hb hΨ hs := hy
  exact e ▸ y.2

theorem divdivD_testFieldS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, IsTest Ω (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) :
    divdivD ⟨_, testFieldS_mem_domain_divdivD hΩ hb hΨ hs⟩ = divdivTestField hΩ hb hΨ :=
  apply_eq_of_mem_graph (testFieldS_mem_graph_divdivD hΩ hb hΨ hs) _

theorem dense_domain_divdivD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    Dense ((divdivD (Ω := Ω)).domain : Set (L2S Ω)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  refine eq_zero_of_forall_symTest hΩ hb fun Ψ hΨ hs => ?_
  have h0 := (Submodule.mem_orthogonal' _ _).1 hv _ (testFieldS_mem_domain_divdivD hΩ hb hΨ hs)
  rw [Submodule.coe_inner, testFieldS, inner_smoothField] at h0
  exact h0

/-! ## The complex `H̊(sym curl, T) → H̊(div div, S) → L²(Ω)` -/

/-- `∂_j (curl Φ)_{ij} = ∂_j ∂_{j+1} Φ_{i,j+2} - ∂_j ∂_{j+2} Φ_{i,j+1}`. -/
theorem pd_curlM {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, ContDiff ℝ ∞ (Φ ij)) (i j : Fin 3) :
    BoundedDomain.pd j (curlM Φ (i, j)) = fun y =>
      BoundedDomain.pd j (BoundedDomain.pd (j + 1) (Φ (i, j + 2))) y -
        BoundedDomain.pd j (BoundedDomain.pd (j + 2) (Φ (i, j + 1))) y := by
  funext y
  have hd : ∀ k ij, Differentiable ℝ (BoundedDomain.pd k (Φ ij)) := fun k ij =>
    (contDiff_pd ((hΦ ij).of_le (by simp)) k).differentiable one_ne_zero
  exact pd_sub (hd _ _) (hd _ _) j y

/-- `div div curl = 0` (pointwise, for smooth fields). -/
theorem divdivF_curlM {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, ContDiff ℝ ∞ (Φ ij)) (x : R3) :
    divdivF (curlM Φ) x = 0 := by
  have h2 : ∀ k ij, ContDiff ℝ 2 (BoundedDomain.pd k (Φ ij)) := fun k ij =>
    (contDiff_pd_top (hΦ ij) k).of_le (by simp)
  have hd : ∀ a k ij, Differentiable ℝ (BoundedDomain.pd a (BoundedDomain.pd k (Φ ij))) :=
    fun a k ij => (contDiff_pd (h2 k ij) a).differentiable one_ne_zero
  have hc : ∀ a b ij, BoundedDomain.pd a (BoundedDomain.pd b (Φ ij)) =
      BoundedDomain.pd b (BoundedDomain.pd a (Φ ij)) := fun a b ij =>
    funext fun y => pd_pd_comm ((hΦ ij).of_le (by simp)) a b y
  simp only [divdivF, Fintype.sum_prod_type, pd_curlM hΦ]
  have e : ∀ i j, BoundedDomain.pd i (fun y =>
      BoundedDomain.pd j (BoundedDomain.pd (j + 1) (Φ (i, j + 2))) y -
        BoundedDomain.pd j (BoundedDomain.pd (j + 2) (Φ (i, j + 1))) y) x =
      BoundedDomain.pd i (BoundedDomain.pd j (BoundedDomain.pd (j + 1) (Φ (i, j + 2)))) x -
        BoundedDomain.pd i (BoundedDomain.pd j (BoundedDomain.pd (j + 2) (Φ (i, j + 1)))) x :=
    fun i j => pd_sub (hd _ _ _) (hd _ _ _) i x
  simp only [e, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.reduceAdd]
  simp only [hc 1 0, hc 2 0, hc 2 1]
  ring

/-- `div div sym M = div div M` for `C²` fields (Schwarz). -/
theorem divdivF_symF {M : Ix → R3 → ℝ} (hM : ∀ ij, ContDiff ℝ 2 (M ij)) (x : R3) :
    divdivF (symF M) x = divdivF M x := by
  have hd : ∀ ij, Differentiable ℝ (M ij) := fun ij => (hM ij).differentiable (by simp)
  have hd1 : ∀ k ij, Differentiable ℝ (BoundedDomain.pd k (M ij)) := fun k ij =>
    (contDiff_pd (hM ij) k).differentiable one_ne_zero
  have e1 : ∀ i j, BoundedDomain.pd j (symF M (i, j)) = fun y =>
      (BoundedDomain.pd j (M (i, j)) y + BoundedDomain.pd j (M (j, i)) y) / 2 := fun i j =>
    funext fun y => pd_avg (hd _) (hd _) j y
  have e2 : ∀ i j, BoundedDomain.pd i (BoundedDomain.pd j (symF M (i, j))) x =
      (BoundedDomain.pd i (BoundedDomain.pd j (M (i, j))) x +
        BoundedDomain.pd i (BoundedDomain.pd j (M (j, i))) x) / 2 := fun i j => by
    rw [e1]
    exact pd_avg (hd1 _ _) (hd1 _ _) i x
  have hswap : ∑ ij : Ix, BoundedDomain.pd ij.1 (BoundedDomain.pd ij.2 (M (ij.2, ij.1))) x =
      ∑ ij : Ix, BoundedDomain.pd ij.1 (BoundedDomain.pd ij.2 (M ij)) x := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
    obtain ⟨j, k⟩ := jk
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    exact pd_pd_comm (hM _) j k x
  simp only [divdivF]
  rw [Finset.sum_congr rfl fun ij _ => e2 ij.1 ij.2, ← Finset.sum_div, Finset.sum_add_distrib,
    hswap]
  ring

/-- `div div sym curl Φ = 0` for smooth `Φ`. -/
theorem divdivF_symF_curlM {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, ContDiff ℝ ∞ (Φ ij)) (x : R3) :
    divdivF (symF (curlM Φ)) x = 0 := by
  have h2 : ∀ ij, ContDiff ℝ 2 (curlM Φ ij) := fun ij =>
    ((contDiff_pd_top (hΦ _) _).sub (contDiff_pd_top (hΦ _) _)).of_le (by simp)
  rw [divdivF_symF h2, divdivF_curlM hΦ]

/-- `sym curl H̊(sym curl, T) ⊆ H̊(div div, S)` with `div div sym curl = 0`. -/
theorem symcurlD_mem_divdivDGraph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (symcurlD (Ω := Ω)).domain) : (symcurlD u, (0 : L2 Ω)) ∈ divdivDGraph Ω := by
  show ((symcurlD u : L2M Ω), (0 : L2 Ω)) ∈ (divdivGraphSub Ω).topologicalClosure
  let f : L2M Ω × L2M Ω →L[ℝ] L2M Ω × L2 Ω := (ContinuousLinearMap.snd ℝ (L2M Ω) (L2M Ω)).prod 0
  have hle : symcurlGraphSub Ω ≤ (divdivGraphSub Ω).comap (f : L2M Ω × L2M Ω →ₗ[ℝ] _) := by
    refine Submodule.span_le.2 ?_
    rintro ⟨v, c⟩ ⟨Φ, hΦ, -, hp⟩
    refine Submodule.subset_span ⟨symF (curlM Φ), isTest_symF (isTest_curlM hΦ), symF_swap _,
      fun ij => (hp ij).2, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
    change ((0 : L2 Ω) : R3 → ℝ) x = _
    rw [hx, divdivF_symF_curlM fun ij => (hΦ ij).contDiff]
    rfl
  have h := mem_closure_symcurlD hΩ hb u
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h
  have := map_mem_closure f.continuous h (t := (divdivGraphSub Ω : Set (L2M Ω × L2 Ω)))
    fun p hp => hle hp
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  simpa [f] using this

theorem symcurlD_mem_domain_divdivD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (symcurlD (Ω := Ω)).domain) : symcurlD u ∈ (divdivD (Ω := Ω)).domain := by
  have h : (symcurlD u, (0 : L2 Ω)) ∈ (divdivD (Ω := Ω)).graph := by
    rw [divdivD_graph hΩ hb]; exact symcurlD_mem_divdivDGraph hΩ hb u
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 h
  have e : (y : L2S Ω) = symcurlD u := hy
  exact e ▸ y.2

/-- **The complex with the dual boundary conditions** on a bounded open `Ω ⊆ ℝ³`:
`H̊(sym curl, Ω; T) --sym curl--> H̊(div div, Ω; S) --div div--> L²(Ω)`
(the adjoint complex (4.17) with the boundary conditions moved to it). -/
def symComplexBC (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HilbertComplex2 (L2T Ω) (L2S Ω) (L2 Ω) where
  d0 := symcurlD
  d1 := divdivD
  dense0 := dense_domain_symcurlD hΩ hb
  dense1 := dense_domain_divdivD hΩ hb
  closed0 := isClosed_symcurlD hΩ hb
  closed1 := isClosed_divdivD hΩ hb
  map_mem := symcurlD_mem_domain_divdivD hΩ hb
  comp_zero := fun u => apply_eq_of_mem_graph
    (by rw [divdivD_graph hΩ hb]; exact symcurlD_mem_divdivDGraph hΩ hb u) _

/-- **The complex (4.16) with the boundary conditions of the thesis' statement of Prop 4.19**:
`H²(Ω) --grad grad--> H(curl, Ω; S) --curl--> L²(Ω; T)` (no boundary conditions), defined as the
dual (adjoint) complex of `symComplexBC`: `d0 = (div div)*`, `d1 = (sym curl)*`. Its adjoints are
`d0* = div div` on `H̊(div div, S)` and `d1* = sym curl` on `H̊(sym curl, T)`
(`symComplexD_adjoint_d0`, `symComplexD_adjoint_d1`), so its Hodge wave operator has domain
`D(L) = H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`, the data space of Prop 4.19 as
printed. -/
def symComplexD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HilbertComplex2 (L2 Ω) (L2S Ω) (L2T Ω) :=
  (symComplexBC hΩ hb).dual

@[simp] theorem symComplexD_d0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (symComplexD hΩ hb).d0 = (divdivD (Ω := Ω))† := rfl

@[simp] theorem symComplexD_d1 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (symComplexD hΩ hb).d1 = (symcurlD (Ω := Ω))† := rfl

/-- `d0* = div div` on `H̊(div div, S)` for `symComplexD` (von Neumann, `T** = T`). -/
theorem symComplexD_adjoint_d0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (symComplexD hΩ hb).d0† = divdivD :=
  adjoint_adjoint _ (dense_domain_divdivD hΩ hb) (isClosed_divdivD hΩ hb)

/-- `d1* = sym curl` on `H̊(sym curl, T)` for `symComplexD`. -/
theorem symComplexD_adjoint_d1 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (symComplexD hΩ hb).d1† = symcurlD :=
  adjoint_adjoint _ (dense_domain_symcurlD hΩ hb) (isClosed_symcurlD hΩ hb)

/-! ## The domains of `symComplexD`: `H²`, `H(curl, S)`, `H̊(div div, S)`, `H̊(sym curl, T)` -/

/-- **`H(curl, S) ⊆ D(d1)`** for `symComplexD`: if `E ∈ L²(S)` has a weak curl `C ∈ L²(T)`
(`∫ E : curl Φ = ∫ C : Φ` for every trace-free test field `Φ`, no boundary condition), then
`E ∈ D((sym curl)*)` and `(sym curl)* E = C`. -/
theorem adjoint_symcurlD_of_weak (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {E : L2S Ω}
    {C : L2T Ω} (hC : ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) → (∀ x, ∑ i, Φ (i, i) x = 0) →
      ∑ ij, ∫ x, (E : L2M Ω) ij x * curlM Φ ij x ∂volume.restrict Ω =
        ∑ ij, ∫ x, (C : L2M Ω) ij x * Φ ij x ∂volume.restrict Ω) :
    ∃ h : E ∈ (symcurlD (Ω := Ω))†.domain, (symcurlD (Ω := Ω))† ⟨E, h⟩ = C := by
  have key : ∀ u : (symcurlD (Ω := Ω)).domain, ⟪C, (u : L2T Ω)⟫ = ⟪E, symcurlD u⟫ := by
    intro u
    let G : L2M Ω × L2M Ω →L[ℝ] ℝ :=
      (innerSL ℝ (E : L2M Ω)).comp (ContinuousLinearMap.snd ℝ _ _) -
        (innerSL ℝ (C : L2M Ω)).comp (ContinuousLinearMap.fst ℝ _ _)
    have hG : ∀ p : L2M Ω × L2M Ω, G p = ⟪(E : L2M Ω), p.2⟫ - ⟪(C : L2M Ω), p.1⟫ := fun p => rfl
    have hS : ∀ p ∈ symcurlGraph Ω, G p = 0 := by
      rintro ⟨v, c⟩ ⟨Φ, hΦ, htr, hp⟩
      have hc := continuous_curlM fun ij => (hΦ ij).contDiff_one
      rw [hG, eq_smoothField hΩ hb (fun ij => (hΦ ij).continuous) (fun ij => (hp ij).1),
        eq_smoothField hΩ hb (continuous_symF hc) (fun ij => (hp ij).2), inner_smoothField,
        inner_smoothField, sum_integral_mul_symF hΩ hb E.2 hc, hC Φ hΦ htr, sub_self]
    have h := eq_zero_of_mem_closure_span G hS (mem_closure_symcurlD hΩ hb u)
    rw [hG, sub_eq_zero] at h
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact h.symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_domain_symcurlD hΩ hb) ⟨_, hmem⟩ key⟩

/-- The adjoint identity against trace-free test fields: `∫ d1 E : Φ = ∫ E : curl Φ`. -/
theorem symComplexD_d1_inner (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (E : (symComplexD hΩ hb).d1.domain) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij))
    (htr : ∀ x, ∑ i, Φ (i, i) x = 0) :
    ∑ ij, ∫ x, (((symComplexD hΩ hb).d1 E : L2T Ω) : L2M Ω) ij x * Φ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, ((E : L2S Ω) : L2M Ω) ij x * curlM Φ ij x ∂volume.restrict Ω := by
  have e := LinearPMap.adjoint_isFormalAdjoint (dense_domain_symcurlD hΩ hb) E
    ⟨_, testFieldT_mem_domain hΩ hb hΦ htr⟩
  simp only at e
  rw [symcurlD_testFieldT, Submodule.coe_inner, Submodule.coe_inner, testFieldT,
    symcurlTestField, inner_smoothField, inner_smoothField,
    sum_integral_mul_symF hΩ hb (E : L2S Ω).2 (continuous_curlM fun ij => (hΦ ij).contDiff_one)]
    at e
  exact e

/-- **`D(d1) = H(curl, S)`** for `symComplexD` (no boundary condition): `E ∈ L²(S)` with a weak
curl in `L²(T)`, tested against trace-free test fields. -/
theorem mem_symComplexD_d1_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {E : L2S Ω} :
    E ∈ (symComplexD hΩ hb).d1.domain ↔ ∃ C : L2T Ω, ∀ Φ : Ix → R3 → ℝ,
      (∀ ij, IsTest Ω (Φ ij)) → (∀ x, ∑ i, Φ (i, i) x = 0) →
        ∑ ij, ∫ x, (E : L2M Ω) ij x * curlM Φ ij x ∂volume.restrict Ω =
          ∑ ij, ∫ x, (C : L2M Ω) ij x * Φ ij x ∂volume.restrict Ω := by
  constructor
  · intro hE
    exact ⟨(symComplexD hΩ hb).d1 ⟨E, hE⟩, fun Φ hΦ htr =>
      (symComplexD_d1_inner hΩ hb ⟨E, hE⟩ hΦ htr).symm⟩
  · rintro ⟨C, hC⟩
    exact (adjoint_symcurlD_of_weak hΩ hb hC).1

/-- A symmetric `C¹` field `Ψ` (no boundary condition), as an element of `L²(S)`. -/
def smoothS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) : L2S Ω :=
  ⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous), smoothField_mem_symL2 hΩ hb _ hs⟩

/-- Its curl, as an element of `L²(T)`. -/
def curlSmoothS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) : L2T Ω :=
  ⟨smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ),
    smoothField_mem_trL2 hΩ hb _ (sum_curlM_diag_of_symm hs)⟩

/-- **Symmetric `C¹` fields lie in `D(d1) = H(curl, S)`** for `symComplexD`, with `d1 Ψ = curl Ψ`
(no boundary condition: constants, linear fields, Hessians of polynomials). -/
theorem smoothS_mem_symComplexD_d1 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) :
    ∃ h : smoothS hΩ hb hΨ hs ∈ (symComplexD hΩ hb).d1.domain,
      (symComplexD hΩ hb).d1 ⟨_, h⟩ = curlSmoothS hΩ hb hΨ hs := by
  refine adjoint_symcurlD_of_weak hΩ hb fun Φ hΦ _ => ?_
  have e := sum_integral_curlM_mul hΦ hΨ
  simp only [smoothS, curlSmoothS]
  rw [sum_integral_congr (coeFn_smoothField hΩ hb Ψ _),
    sum_integral_congr (coeFn_smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ))]
  have c1 : ∀ ij, ∫ x, Ψ ij x * curlM Φ ij x ∂volume.restrict Ω =
      ∫ x, curlM Φ ij x * Ψ ij x ∂volume.restrict Ω := fun ij =>
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have c2 : ∀ ij, ∫ x, curlM Ψ ij x * Φ ij x ∂volume.restrict Ω =
      ∫ x, Φ ij x * curlM Ψ ij x ∂volume.restrict Ω := fun ij =>
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  simp only [c1, c2]
  exact e

/-- **`H² ⊆ D(d0)`** for `symComplexD`: if `f ∈ L²(Ω)` has a weak Hessian `H ∈ L²(S)`
(`∫ f div div Ψ = ∫ H : Ψ` for every symmetric test field `Ψ`, no boundary condition), then
`f ∈ D((div div)*)` and `(div div)* f = H`. -/
theorem adjoint_divdivD_of_weak (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f : L2 Ω}
    {H : L2S Ω} (hH : ∀ Ψ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Ψ ij)) → (∀ i j, Ψ (i, j) = Ψ (j, i)) →
      ∫ x, f x * divdivF Ψ x ∂volume.restrict Ω =
        ∑ ij, ∫ x, (H : L2M Ω) ij x * Ψ ij x ∂volume.restrict Ω) :
    ∃ h : f ∈ (divdivD (Ω := Ω))†.domain, (divdivD (Ω := Ω))† ⟨f, h⟩ = H := by
  have key : ∀ u : (divdivD (Ω := Ω)).domain, ⟪H, (u : L2S Ω)⟫ = ⟪f, divdivD u⟫ := by
    intro u
    let G : L2M Ω × L2 Ω →L[ℝ] ℝ :=
      (innerSL ℝ f).comp (ContinuousLinearMap.snd ℝ _ _) -
        (innerSL ℝ (H : L2M Ω)).comp (ContinuousLinearMap.fst ℝ _ _)
    have hG : ∀ p : L2M Ω × L2 Ω, G p = ⟪f, p.2⟫ - ⟪(H : L2M Ω), p.1⟫ := fun p => rfl
    have hS : ∀ p ∈ divdivGraph Ω, G p = 0 := by
      rintro ⟨v, c⟩ ⟨Ψ, hΨ, hs, hp1, hp2⟩
      have hm := memLp_of_continuous hΩ hb (continuous_divdivF fun ij =>
        (hΨ ij).contDiff.of_le (by simp))
      have ec : c = hm.toLp _ := Lp.ext (hp2.trans hm.coeFn_toLp.symm)
      rw [hG, eq_smoothField hΩ hb (fun ij => (hΨ ij).continuous) hp1, ec, inner_smoothField,
        ← integral_mul_eq_inner, hH Ψ hΨ hs, sub_self]
    have h := eq_zero_of_mem_closure_span G hS (mem_closure_divdivD hΩ hb u)
    rw [hG, sub_eq_zero] at h
    rw [Submodule.coe_inner]
    exact h.symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_domain_divdivD hΩ hb) ⟨_, hmem⟩ key⟩

/-- **`D(d0) = H²(Ω)`** for `symComplexD` (no boundary condition): `f ∈ L²(Ω)` with a weak Hessian
in `L²(S)`. -/
theorem mem_symComplexD_d0_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f : L2 Ω} :
    f ∈ (symComplexD hΩ hb).d0.domain ↔ ∃ H : L2S Ω, ∀ Ψ : Ix → R3 → ℝ,
      (∀ ij, IsTest Ω (Ψ ij)) → (∀ i j, Ψ (i, j) = Ψ (j, i)) →
        ∫ x, f x * divdivF Ψ x ∂volume.restrict Ω =
          ∑ ij, ∫ x, (H : L2M Ω) ij x * Ψ ij x ∂volume.restrict Ω := by
  constructor
  · intro hf
    refine ⟨(symComplexD hΩ hb).d0 ⟨f, hf⟩, fun Ψ hΨ hs => ?_⟩
    have e := LinearPMap.adjoint_isFormalAdjoint (dense_domain_divdivD hΩ hb) ⟨f, hf⟩
      ⟨_, testFieldS_mem_domain_divdivD hΩ hb hΨ hs⟩
    simp only at e
    rw [divdivD_testFieldS, Submodule.coe_inner, testFieldS, inner_smoothField, divdivTestField,
      ← integral_mul_eq_inner] at e
    exact e.symm
  · rintro ⟨H, hH⟩
    exact (adjoint_divdivD_of_weak hΩ hb hH).1

theorem continuous_hessField {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) (ij : Ix) :
    Continuous (hessField φ ij) :=
  continuous_pd (contDiff_pd hφ ij.1) ij.2

/-- The Hessian of a `C²` function (no boundary condition), as an element of `L²(S)`. -/
def hessSmooth (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) :
    L2S Ω :=
  ⟨smoothField hΩ hb (hessField φ) (continuous_hessField hφ),
    smoothField_mem_symL2 hΩ hb _ (hessField_swap hφ)⟩

/-- **`C²` functions lie in `D(d0) = H²`** for `symComplexD`, with `d0 φ = ∇²φ` (no boundary
condition: e.g. all polynomials). -/
theorem smooth_mem_symComplexD_d0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ}
    (hφ : ContDiff ℝ 2 φ) :
    ∃ h : (memLp_of_continuous hΩ hb hφ.continuous).toLp φ ∈ (symComplexD hΩ hb).d0.domain,
      (symComplexD hΩ hb).d0 ⟨_, h⟩ = hessSmooth hΩ hb hφ := by
  refine adjoint_divdivD_of_weak hΩ hb fun Ψ hΨ _ => ?_
  simp only [hessSmooth]
  rw [sum_integral_congr (coeFn_smoothField hΩ hb _ _),
    integral_congr_ae ((memLp_of_continuous hΩ hb hφ.continuous).coeFn_toLp.mono fun x hx => by
      rw [hx, mul_comm]), integral_divdivF_mul hΨ hφ]
  exact Finset.sum_congr rfl fun ij _ =>
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- The quadratic monomial `x_a x_b`. -/
def quadF (a b : Fin 3) : R3 → ℝ := fun y => y a * y b

theorem contDiff_quadF (a b : Fin 3) : ContDiff ℝ ∞ (quadF a b) :=
  (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) a).mul (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) b)

theorem pd_quadF (a b k : Fin 3) :
    BoundedDomain.pd k (quadF a b) = fun y =>
      (if k = a then 1 else 0) * y b + (if k = b then 1 else 0) * y a := by
  funext y
  have h := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a y).mul (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) b y)
  refine (pd_of_hasFDerivAt (f := quadF a b) h k).trans ?_
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply]
  simp only [@eq_comm _ b k, @eq_comm _ a k]
  ring

theorem hessField_quadF (a b : Fin 3) (ij : Ix) (x : R3) :
    hessField (quadF a b) ij x =
      (if ij.1 = a then 1 else 0) * (if ij.2 = b then 1 else 0) +
        (if ij.1 = b then 1 else 0) * (if ij.2 = a then 1 else 0) := by
  simp only [hessField, pd_quadF]
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) b x).const_mul (if ij.1 = a then (1 : ℝ) else 0)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) a x).const_mul (if ij.1 = b then (1 : ℝ) else 0)))
  refine (pd_of_hasFDerivAt (f := fun y => (if ij.1 = a then (1 : ℝ) else 0) * y b +
    (if ij.1 = b then (1 : ℝ) else 0) * y a) h ij.2).trans ?_
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply]
  simp only [@eq_comm _ b ij.2, @eq_comm _ a ij.2]


theorem hessField_quadF' (a b : Fin 3) (ij : Ix) (x : R3) :
    hessField (quadF a b) ij x =
      (if ij = (a, b) then 1 else 0) + (if ij = (b, a) then 1 else 0) := by
  obtain ⟨i, j⟩ := ij
  rw [hessField_quadF]
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- `x_a x_b` as an element of `D(d0) = H²` of `symComplexD`. -/
theorem quadF_mem_symComplexD_d0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (a b : Fin 3) :
    ∃ h : (memLp_of_continuous hΩ hb (contDiff_quadF a b).continuous).toLp (quadF a b) ∈
        (symComplexD hΩ hb).d0.domain,
      (symComplexD hΩ hb).d0 ⟨_, h⟩ = hessSmooth hΩ hb ((contDiff_quadF a b).of_le (by simp)) :=
  smooth_mem_symComplexD_d0 hΩ hb _

/-- **The zero-mean property of `ker d0* = ker (div div on H̊(div div, S))`**: every
`E ∈ L²(S)` orthogonal to `∇² H²` (in particular to the Hessians `∇²(x_a x_b)`, constant fields)
has zero mean, `∫_Ω E_{ab} = 0`. Formally `⟪E, ∇²φ⟫ = ∫_{∂Ω} (E n)·∇φ - ...`: this is the boundary
condition of `H̊(div div, S)`. -/
theorem integral_eq_zero_of_mem_ker_symComplexD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E : L2S Ω} (hE : E ∈ (symComplexD hΩ hb).d0†.ker) (a b : Fin 3) :
    ∫ x, (E : L2M Ω) (a, b) x ∂volume.restrict Ω = 0 := by
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hE
  obtain ⟨hq, eq⟩ := quadF_mem_symComplexD_d0 hΩ hb a b
  have e := LinearPMap.adjoint_isFormalAdjoint (symComplexD hΩ hb).dense0 y ⟨_, hq⟩
  simp only at e
  rw [hy0, inner_zero_left, eq, ← hy, hessSmooth, Submodule.coe_inner, inner_smoothField] at e
  have hc : ∀ ij : Ix, ∫ x, (E : L2M Ω) ij x * hessField (quadF a b) ij x ∂volume.restrict Ω =
      (∫ x, (E : L2M Ω) ij x ∂volume.restrict Ω) *
        ((if ij = (a, b) then 1 else 0) + (if ij = (b, a) then 1 else 0)) := fun ij => by
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hessField_quadF']
  simp only [hc, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e
  have hs : (E : L2M Ω) (b, a) = (E : L2M Ω) (a, b) := E.2 b a
  rw [hs] at e
  linarith

/-! ## Prop 4.19 for `symComplexD`: hypotheses -/

/-- **`L²(TSD) ∩ H̊(div div, S) ⊆ ker (div div)`**: a TSD field in `D(d0*)` of `symComplexD` is
`div div`-free (`d0* E` is tested against `C_c^∞(Ω)`, where `⟪E, ∇²φ⟫ = 0` by `div E = 0`). -/
theorem TSDS_inf_domain_le_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {E : L2S Ω}
    (hE : E ∈ TSDS Ω) (hD : E ∈ (symComplexD hΩ hb).d0†.domain) :
    E ∈ (symComplexD hΩ hb).d0†.ker := by
  refine LinearPMap.mem_ker_iff.2 ⟨⟨E, hD⟩, rfl, ?_⟩
  refine L2_ext_of_integral hΩ hb fun g hg => ?_
  have hg2 : ContDiff ℝ 2 g := hg.contDiff.of_le (by simp)
  obtain ⟨hq, eq⟩ := smooth_mem_symComplexD_d0 hΩ hb hg2
  have e := LinearPMap.adjoint_isFormalAdjoint (symComplexD hΩ hb).dense0 ⟨E, hD⟩ ⟨_, hq⟩
  simp only at e
  rw [eq, hessSmooth, Submodule.coe_inner, inner_smoothField] at e
  have h0 : ∑ ij, ∫ x, (E : L2M Ω) ij x * hessField g ij x ∂volume.restrict Ω = 0 :=
    hE.2.2 (fun i => BoundedDomain.pd i g) fun i => hg.pdiff i
  rw [h0, ← integral_mul_eq_inner] at e
  rw [e, integral_mul_eq_inner _ hg.memLp, inner_zero_left]

/-- **Every TSD field in `H̊(div div, S)` has zero mean**, `∫_Ω E = 0`, on every bounded open `Ω`:
the boundary condition of `H̊(div div, S)` replaces that of `H̊(curl, S)` in the zero-mean
obstruction (`integral_eq_zero_of_mem_TSDS`). -/
theorem integral_eq_zero_of_mem_TSDS_dual (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {E : L2S Ω} (hE : E ∈ TSDS Ω) (hD : E ∈ (symComplexD hΩ hb).d0†.domain) (a b : Fin 3) :
    ∫ x, (E : L2M Ω) (a, b) x ∂volume.restrict Ω = 0 :=
  integral_eq_zero_of_mem_ker_symComplexD hΩ hb (TSDS_inf_domain_le_ker hΩ hb hE hD) a b

theorem inner_constS_eq_zero_of_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {E : L2S Ω}
    (hE : E ∈ (symComplexD hΩ hb).d0†.ker) : ⟪E, constS hΩ hb⟫ = 0 := by
  rw [Submodule.coe_inner, constS, inner_constField]
  exact Finset.sum_eq_zero fun ij _ => by
    rw [integral_eq_zero_of_mem_ker_symComplexD hΩ hb hE, mul_zero]

/-- `∫_Ω diag(1, -1, 0)_{00} = |Ω| ≠ 0`. -/
theorem integral_constS_00 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∫ x, ((constS hΩ hb : L2S Ω) : L2M Ω) (0, 0) x ∂volume.restrict Ω = volume.real Ω := by
  change ∫ x, constField hΩ hb diagA (0, 0) x ∂volume.restrict Ω = _
  rw [integral_constField]
  simp [diagA]

/-- **`L²(TSD) ⊄ D(d0*) = H̊(div div, S)`** for `symComplexD`: the constant TSD field
`diag(1, -1, 0)` is not in `H̊(div div, S)`. So the hypothesis `L²(TSD) ⊆ ker d0*` of
`Feec.Constraints.prop_4_17` fails for the thesis' `K = {0} × L²(TSD) × S2` with these boundary
conditions (it holds for `{0} × (L²(TSD) ∩ ker d0*) × S2`, which has the same `D(L) ∩ K`,
`TSDS_inf_domain_le_ker`). -/
theorem constS_not_mem_adjoint_d0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : constS hΩ hb ∉ (symComplexD hΩ hb).d0†.domain := fun hD => by
  have h := integral_eq_zero_of_mem_TSDS_dual hΩ hb (constS_mem_TSDS hΩ hb) hD 0 0
  rw [integral_constS_00] at h
  exact (volume_real_pos hΩ hb hne).ne' h

theorem symComplexD_not_TSDS_le_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ¬ TSDS Ω ≤ (symComplexD hΩ hb).d0†.ker := fun h => by
  obtain ⟨y, hy, -⟩ := LinearPMap.mem_ker_iff.1 (h (constS_mem_TSDS hΩ hb))
  exact constS_not_mem_adjoint_d0 hΩ hb hne (hy ▸ y.2)

/-- Symmetric test fields lie in `D(d1) ∩ D(d0*) = H(curl, S) ∩ H̊(div div, S)` of
`symComplexD`. -/
theorem testFieldS_mem_midDomain_D (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    testFieldS hΩ hb hΦ hs ∈ (symComplexD hΩ hb).midDomain := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · exact (smoothS_mem_symComplexD_d1 hΩ hb (fun ij => (hΦ ij).contDiff_one) hs).1
  · rw [symComplexD_adjoint_d0]
    exact testFieldS_mem_domain_divdivD hΩ hb hΦ hs

/-- **The projection hypothesis of Prop 4.19 fails also with the boundary conditions of its
statement** (`symComplexD`, `D(L) = H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`), on
every nonempty bounded open `Ω ⊆ ℝ³` and for every `S2`: for `E = g · diag(1, -1, 0)`,
`P_{L²(TSD)} E` has nonzero mean, so it is not in `H̊(div div, S)`
(`integral_eq_zero_of_mem_TSDS_dual`).

Correction: [QuennevilleBelair2015, §4.11, Prop 4.19], first conjecture, for the data space as
printed. -/
theorem symComplexD_not_projection_hyp (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S2 : Submodule ℝ (L2T Ω)) [S2.HasOrthogonalProjection] :
    ¬ ∀ x ∈ (symComplexD hΩ hb).domL,
      projKc (L2 Ω) (TSDS Ω) S2 x ∈ (symComplexD hΩ hb).domL := by
  intro hPD
  obtain ⟨g, hg, hgpos⟩ := exists_isTest_integral_pos hΩ hne
  have hΦ := isTest_diagA_mul hg
  have hs : ∀ i j, (fun x => diagA (i, j).1 (i, j).2 * g x) =
      (fun x => diagA (j, i).1 (j, i).2 * g x) := fun i j => by
    simp only [diagA_swap i j]
  set E := testFieldS hΩ hb hΦ hs
  have hx : ini (L2 Ω) E (0 : L2T Ω) ∈ (symComplexD hΩ hb).domL := by
    rw [Feec.Constraints.mem_domL, tot_ini]
    exact ⟨Submodule.zero_mem _, testFieldS_mem_midDomain_D hΩ hb hΦ hs, Submodule.zero_mem _⟩
  have h := (Feec.Constraints.mem_domL _).1 (hPD _ hx)
  rw [tot_projKc, tot_ini] at h
  have hP : (TSDS Ω).starProjection E ∈ (symComplexD hΩ hb).d0†.domain :=
    (Submodule.mem_inf.1 h.2.1).2
  have h0 := inner_constS_eq_zero_of_ker hΩ hb
    (TSDS_inf_domain_le_ker hΩ hb (Submodule.starProjection_apply_mem _ _) hP)
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 (constS_mem_TSDS hΩ hb), Submodule.coe_inner,
    constS, inner_constField] at h0
  have hI : ∀ ij : Ix, ∫ x, ((E : L2S Ω) : L2M Ω) ij x ∂volume.restrict Ω =
      diagA ij.1 ij.2 * ∫ x, g x ∂volume.restrict Ω := fun ij => by
    rw [← integral_const_mul]
    exact integral_congr_ae (coeFn_smoothField hΩ hb _ (fun ij => (hΦ ij).continuous) ij)
  simp only [hI, Fintype.sum_prod_type, Fin.sum_univ_three] at h0
  simp [diagA] at h0
  linarith

/-- **The density hypothesis of Prop 4.19 fails also with the boundary conditions of its
statement**: `H(curl, S) ∩ H̊(div div, S) ∩ L²(TSD)` is not dense in `L²(TSD)`;
`diag(1, -1, 0)` is not in its closure. -/
theorem symComplexD_not_dense (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    constS hΩ hb ∈ TSDS Ω ∧ constS hΩ hb ∉
      closure ((TSDS Ω : Set (L2S Ω)) ∩ (symComplexD hΩ hb).midDomain) := by
  refine ⟨constS_mem_TSDS hΩ hb, fun hK => ?_⟩
  have hsub : (TSDS Ω : Set (L2S Ω)) ∩ (symComplexD hΩ hb).midDomain ⊆
      (fun F => ⟪F, constS hΩ hb⟫) ⁻¹' {0} := by
    rintro F ⟨hF, hF'⟩
    exact inner_constS_eq_zero_of_ker hΩ hb
      (TSDS_inf_domain_le_ker hΩ hb hF (Submodule.mem_inf.1 hF').2)
  have h0 := closure_minimal hsub (isClosed_singleton.preimage (continuous_id.inner
    continuous_const)) hK
  simp only [mem_preimage, mem_singleton_iff] at h0
  rw [Submodule.coe_inner, constS, inner_constField] at h0
  simp only [integral_constField] at h0
  have hpos := volume_real_pos hΩ hb hne
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA] at h0
  linarith

/-! ## Prop 4.19 for `symComplexD`: the zero-mean obstruction does not fire -/

/-- `diag(1, -1, 0) ∈ H(curl, S)` with `curl diag(1, -1, 0) = 0`. -/
theorem constS_mem_symComplexD_d1 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ h : constS hΩ hb ∈ (symComplexD hΩ hb).d1.domain, (symComplexD hΩ hb).d1 ⟨_, h⟩ = 0 := by
  have hΨ : ∀ ij : Ix, ContDiff ℝ 1 (fun _ : R3 => diagA ij.1 ij.2) := fun _ => contDiff_const
  have hs : ∀ i j, (fun _ : R3 => diagA (i, j).1 (i, j).2) = fun _ => diagA (j, i).1 (j, i).2 :=
    fun i j => by simp only [diagA_swap i j]
  obtain ⟨h, e⟩ := smoothS_mem_symComplexD_d1 hΩ hb hΨ hs
  have hc : smoothS hΩ hb hΨ hs = constS hΩ hb := rfl
  refine ⟨hc ▸ h, ?_⟩
  have hz : curlSmoothS hΩ hb hΨ hs = 0 := by
    refine Subtype.ext ((WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_))
    filter_upwards [coeFn_smoothField hΩ hb (curlM fun ij _ => diagA ij.1 ij.2)
      (continuous_curlM hΨ) ij, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2
    simp only [curlSmoothS] at h1 ⊢
    rw [h1]
    simp [curlM, BoundedDomain.pd]
    exact h2.symm
  rw [← hz, ← e]
  rfl

/-- **The mechanism refuting Prop 4.19 for (4.16) does not apply to `symComplexD`**: for every
`B ∈ D(d1*) = H̊(sym curl, T)`, `⟪sym curl B, diag(1, -1, 0)⟫ = 0` (`diag(1, -1, 0)` is curl-free
in `H(curl, S)`). Compare `inner_constS_adjoint_betaT`, where `β ∈ H(sym curl, T)` (no boundary
condition) gives `⟪sym curl β, diag(1, -1, 0)⟫ = -2 |Ω|`. -/
theorem symComplexD_inner_adjoint_d1_constS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (B : (symComplexD hΩ hb).d1†.domain) : ⟪(symComplexD hΩ hb).d1† B, constS hΩ hb⟫ = 0 := by
  obtain ⟨h, e⟩ := constS_mem_symComplexD_d1 hΩ hb
  have := LinearPMap.adjoint_isFormalAdjoint (symComplexD hΩ hb).dense1 B ⟨_, h⟩
  simp only at this
  rw [this, e, inner_zero_right]

/-- **Prop 4.16 for `symComplexD`, and the zero mean propagates** (unconditional): for TSD data
`(0, E₀, B₀) ∈ D(L)`, the Hodge wave equation has a unique strong solution on `[0, T]`, and for
all `t`: `σ(t) = 0`, `E(t) ∈ ker d0*` (`div div E = 0` with the `H̊(div div)` boundary condition)
and `∫_Ω E(t) = 0`. So, unlike for (4.16) with the boundary conditions of the proof
(`symComplexB_betaT_not_propagate`), the zero-mean obstruction is propagated and does not refute
Prop 4.19 here. -/
theorem symComplexD_prop_4_16 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (T : ℝ)
    {E₀ : L2S Ω} {B₀ : L2T Ω} (hD : ini (L2 Ω) E₀ B₀ ∈ (symComplexD hΩ hb).domL)
    (hE₀ : E₀ ∈ TSDS Ω) :
    ∃ U, IsStrongSolution (-(symComplexD hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U ∧
      (∀ t ∈ Icc 0 T, (tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).1 = 0 ∧
        (tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).2.1 ∈ (symComplexD hΩ hb).d0†.ker ∧
        ∀ a b, ∫ x, (((tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).2.1 : L2S Ω) : L2M Ω) (a, b) x
          ∂volume.restrict Ω = 0) ∧
      ∀ U', IsStrongSolution (-(symComplexD hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U' →
        EqOn U U' (Icc 0 T) := by
  have hDm := (Feec.Constraints.mem_domL _).1 hD
  rw [tot_ini] at hDm
  have hk := TSDS_inf_domain_le_ker hΩ hb hE₀ (Submodule.mem_inf.1 hDm.2.1).2
  have hK : ini (L2 Ω) E₀ B₀ ∈ K (symComplexD hΩ hb) ⊤ := by
    rw [mem_K, tot_ini]
    exact ⟨rfl, hk, Submodule.mem_top⟩
  obtain ⟨U, hU, hUK, huniq⟩ :=
    prop_4_16_exists_unconditional (symComplexD hΩ hb) ⊤ le_top T hD hK
  refine ⟨U, hU, fun t ht => ?_, huniq⟩
  obtain ⟨h1, h2, -⟩ := (mem_K _).1 (hUK t ht)
  exact ⟨h1, h2, integral_eq_zero_of_mem_ker_symComplexD hΩ hb h2⟩

/-! ## Prop 4.19 for `symComplexD`: Lemma 3.5 without boundary conditions -/

theorem isTest_skewOf {ψ : Fin 3 → R3 → ℝ} (hψ : ∀ i, IsTest Ω (ψ i)) (jk : Ix) :
    IsTest Ω (skewOf ψ jk) := by
  have h : ∀ (c : Prop) [Decidable c] (m : Fin 3), IsTest Ω (if c then ψ m else 0) := by
    intro c _ m
    split_ifs
    exacts [hψ m, IsTest.zero]
  exact (h _ _).sub (h _ _)

theorem skewOf_trace (ψ : Fin 3 → R3 → ℝ) (x : R3) : ∑ i, skewOf ψ (i, i) x = 0 := by
  simp [skewOf]

/-- **Lemma 3.5 (symmetry part), weak form with no boundary condition**: if `B ∈ L²(TSD)` and
`C` satisfies `∫ C : Ψ = ∫ B : curl Ψ` for the trace-free test fields `Ψ = e_j × ψ`, then `C` is
symmetric. -/
theorem symm_of_weakCurl_TSD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B C : L2M Ω}
    (hB : B ∈ TSD Ω) (h : ∀ ψ : Fin 3 → R3 → ℝ, (∀ i, IsTest Ω (ψ i)) →
      ∑ ij, ∫ x, C ij x * skewOf ψ ij x ∂volume.restrict Ω =
        ∑ ij, ∫ x, B ij x * curlM (skewOf ψ) ij x ∂volume.restrict Ω) (j k : Fin 3) :
    C (j, k) = C (k, j) := by
  have key : ∀ m : Fin 3, C (m + 2, m + 1) = C (m + 1, m + 2) := by
    intro m
    refine L2_ext_of_integral hΩ hb fun g hg => ?_
    let ψ : Fin 3 → R3 → ℝ := fun i => if i = m then g else 0
    have hψ : ∀ i, IsTest Ω (ψ i) := fun i => by
      by_cases hi : i = m
      · simpa [ψ, hi] using hg
      · simp only [ψ, hi, ite_false]
        exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
    have e := h ψ hψ
    rw [sum_integral_mul_curlM_skewOf_eq_zero hΩ hb hB hψ] at e
    fin_cases m <;>
      simp [ψ, skewOf, Fintype.sum_prod_type, Fin.sum_univ_three, integral_neg] at e ⊢ <;>
      linarith
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  simp only [Fin.isValue, Fin.reduceAdd] at k0 k1 k2
  fin_cases j <;> fin_cases k <;> simp [k0, k1, k2]

/-- `curl dev Ψ = curl Ψ - curl (⅓ (tr Ψ) I)`. -/
theorem curlM_devF {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Differentiable ℝ (Ψ ij))
    (hg : Differentiable ℝ fun y => (∑ k, Ψ (k, k) y) / 3) (ij : Ix) (x : R3) :
    curlM (devF Ψ) ij x =
      curlM Ψ ij x - curlM (diagOf fun y => (∑ k, Ψ (k, k) y) / 3) ij x := by
  have hd : ∀ ij, Differentiable ℝ (diagOf (fun y => (∑ k, Ψ (k, k) y) / 3) ij) := by
    intro ij
    unfold diagOf
    split_ifs
    exacts [hg, differentiable_const 0]
  have e : ∀ ij, devF Ψ ij = Ψ ij - diagOf (fun y => (∑ k, Ψ (k, k) y) / 3) ij := fun _ => rfl
  simp only [curlM, e, pd_sub (hΨ _) (hd _)]
  ring

/-- **`curl (H(curl, S) ∩ L²(TSD)) ⊆ L²(TSD)`** for `symComplexD` (Lemma 3.5, no boundary
condition): the hypothesis `hd1` of `Feec.Constraints.prop_4_17`. `curl E` is symmetric
(`symm_of_weakCurl_TSD`), trace-free, and weakly divergence-free:
`⟪curl E, ∇φ⟫ = ⟪curl E, dev ∇φ⟫ = ⟪E, curl dev ∇φ⟫ = -⟪E, curl (⅓ div φ I)⟫ = 0` (a skew
field against a symmetric one). -/
theorem symComplexD_d1_mem_TSDT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (symComplexD hΩ hb).d1.domain) (hu : (u : L2S Ω) ∈ TSDS Ω) :
    (symComplexD hΩ hb).d1 u ∈ TSDT Ω := by
  set C : L2M Ω := (((symComplexD hΩ hb).d1 u : L2T Ω) : L2M Ω)
  refine ⟨fun j k => symm_of_weakCurl_TSD hΩ hb hu (fun ψ hψ =>
    symComplexD_d1_inner hΩ hb u (isTest_skewOf hψ) (skewOf_trace ψ)) j k,
    ((symComplexD hΩ hb).d1 u).2, fun φ hφ => ?_⟩
  have hG : ∀ ij, IsTest Ω (gradM φ ij) := isTest_gradM hφ
  have hg := isTest_trace hG
  have e1 := sum_integral_mul_devF hΩ hb ((symComplexD hΩ hb).d1 u).2
    (fun ij => (hG ij).continuous)
  have e2 := symComplexD_d1_inner hΩ hb u (isTest_devF hG) (devF_trace _)
  have hcd : ∀ ij x, curlM (devF (gradM φ)) ij x =
      -skewOf (fun i y => -BoundedDomain.pd i (fun y => (∑ k, gradM φ (k, k) y) / 3) y) ij x := by
    intro ij x
    rw [curlM_devF (fun ij => (hG ij).differentiable) hg.differentiable, curlM_diagOf,
      curlM_gradM (fun i => (hφ i).contDiff.of_le (by simp)), zero_sub]
  have e3 : ∑ ij, ∫ x, ((u : L2S Ω) : L2M Ω) ij x * curlM (devF (gradM φ)) ij x
      ∂volume.restrict Ω = 0 := by
    simp only [hcd, mul_neg, integral_neg, Finset.sum_neg_distrib]
    rw [sum_integral_mul_skewOf_eq_zero (C := ((u : L2S Ω) : L2M Ω)) hu.1, neg_zero]
  change ∑ ij : Ix, ∫ x, C ij x * gradM φ ij x ∂volume.restrict Ω = 0
  rw [← e1, e2, e3]

/-- **`sym curl (H̊(sym curl, T) ∩ L²(TSD)) ⊆ L²(TSD)`** for `symComplexD` (Lemma 3.5): the
hypothesis `hd1s` of `Feec.Constraints.prop_4_17`. Here `d1* = sym curl` on `H̊(sym curl, T)`
satisfies `⟪d1* ρ, Φ⟫ = ⟪ρ, curl Φ⟫` for symmetric test fields `Φ`, so `ρ ∈ D(curl*)` for the
complex (4.16) with the same value (`adjoint_curlS_of_weak`), and `adjoint_curlS_mem_TSDS`
applies. -/
theorem symComplexD_adjoint_d1_mem_TSDS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (ρ : (symComplexD hΩ hb).d1†.domain) (hρ : (ρ : L2T Ω) ∈ TSDT Ω) :
    (symComplexD hΩ hb).d1† ρ ∈ TSDS Ω := by
  obtain ⟨h, e⟩ := adjoint_curlS_of_weak hΩ hb (B := (ρ : L2T Ω))
    (C := (symComplexD hΩ hb).d1† ρ) fun Φ hΦ hs => by
      obtain ⟨hm, em⟩ := smoothS_mem_symComplexD_d1 hΩ hb (fun ij => (hΦ ij).contDiff_one) hs
      have := LinearPMap.adjoint_isFormalAdjoint (symComplexD hΩ hb).dense1 ρ ⟨_, hm⟩
      simp only at this
      rw [em, smoothS, curlSmoothS, Submodule.coe_inner, Submodule.coe_inner, inner_smoothField,
        inner_smoothField] at this
      exact this.symm
  rw [← e]
  exact adjoint_curlS_mem_TSDS hΩ hb ⟨_, h⟩ hρ

/-! ## Prop 4.19 for `symComplexD`: diagnosis and the maximal form -/

variable (Ω) in
/-- `L²(TSD) ∩ ker d0*` for `symComplexD`: the TSD fields that are `div div`-free with the
`H̊(div div)` boundary condition. It has the same intersection with `D(L)` as `L²(TSD)`
(`TSDS_inf_domain_le_ker`). -/
def TSDSk (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : Submodule ℝ (L2S Ω) :=
  TSDS Ω ⊓ (symComplexD hΩ hb).d0†.ker

theorem isClosed_TSDSk (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    IsClosed (TSDSk Ω hΩ hb : Set (L2S Ω)) :=
  isClosed_TSDS.inter (isClosed_ker (LinearPMap.adjoint_isClosed (symComplexD hΩ hb).dense0))

instance (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (TSDSk Ω hΩ hb).HasOrthogonalProjection := by
  have : CompleteSpace (TSDSk Ω hΩ hb) := (isClosed_TSDSk hΩ hb).completeSpace_coe
  infer_instance

theorem TSDSk_le_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    TSDSk Ω hΩ hb ≤ (symComplexD hΩ hb).d0†.ker := inf_le_right

/-- `D(L) ∩ ({0} × L²(TSD) × S2) = D(L) ∩ ({0} × (L²(TSD) ∩ ker d0*) × S2)` for `symComplexD`:
replacing `L²(TSD)` by `TSDSk` changes no datum of Prop 4.19. -/
theorem symComplexD_mem_Kc_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S2 : Submodule ℝ (L2T Ω)) {x : Tot (L2 Ω) (L2S Ω) (L2T Ω)}
    (hx : x ∈ (symComplexD hΩ hb).domL) :
    x ∈ Kc (L2 Ω) (TSDS Ω) S2 ↔ x ∈ Kc (L2 Ω) (TSDSk Ω hΩ hb) S2 := by
  have hD := (Feec.Constraints.mem_domL _).1 hx
  rw [mem_Kc, mem_Kc]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, ⟨h1, TSDS_inf_domain_le_ker hΩ hb h1 (Submodule.mem_inf.1 hD.2.1).2⟩, h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1.1, h2⟩

/-- **Diagnosis of Prop 4.19 with the boundary conditions of its statement** (`symComplexD`,
`D(L) = H² × (H(curl, S) ∩ H̊(div div, S)) × H̊(sym curl, T)`), on every nonempty bounded open
`Ω ⊆ ℝ³`, for the thesis' `K = {0} × L²(TSD) × L²(TSD)`:
1. `L²(TSD) ⊄ ker d0*` (`diag(1, -1, 0) ∉ H̊(div div, S)`), so `hS1` of
   `Feec.Constraints.prop_4_17` fails; it holds for `L²(TSD) ∩ ker d0*`, which has the same
   data in `D(L)` (`symComplexD_mem_Kc_iff`);
2. `hd1` and `hd1s` hold (Lemma 3.5 without boundary condition);
3. the projection hypothesis fails for `K` (every `S2`), and `H(curl, S) ∩ H̊(div div, S) ∩ L²(TSD)`
   is not dense in `L²(TSD)`;
4. for `L²(TSD) ∩ ker d0*` the `H̊(div div)` part of the projection hypothesis holds
   automatically: `P_{L²(TSD) ∩ ker d0*}` maps into `ker d0* ⊆ D(d0*)`;
5. the obstruction behind the refutation of Prop 4.19 for (4.16) is absent:
   `⟪sym curl B, diag(1, -1, 0)⟫ = 0` for every `B ∈ H̊(sym curl, T)`.

Correction / Thesis gap: [QuennevilleBelair2015, §4.11, Prop 4.19]. Whether the conclusion of
Prop 4.19 holds for `symComplexD` is not settled here (see the module docstring). -/
theorem symComplexD_diagnosis (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ¬ TSDS Ω ≤ (symComplexD hΩ hb).d0†.ker ∧
      TSDSk Ω hΩ hb ≤ (symComplexD hΩ hb).d0†.ker ∧
      (∀ u : (symComplexD hΩ hb).d1.domain, (u : L2S Ω) ∈ TSDS Ω →
        (symComplexD hΩ hb).d1 u ∈ TSDT Ω) ∧
      (∀ ρ : (symComplexD hΩ hb).d1†.domain, (ρ : L2T Ω) ∈ TSDT Ω →
        (symComplexD hΩ hb).d1† ρ ∈ TSDSk Ω hΩ hb) ∧
      (¬ ∀ x ∈ (symComplexD hΩ hb).domL,
        projKc (L2 Ω) (TSDS Ω) (TSDT Ω) x ∈ (symComplexD hΩ hb).domL) ∧
      constS hΩ hb ∉ closure ((TSDS Ω : Set (L2S Ω)) ∩ (symComplexD hΩ hb).midDomain) ∧
      (∀ E : L2S Ω, (TSDSk Ω hΩ hb).starProjection E ∈ (symComplexD hΩ hb).d0†.domain) ∧
      ∀ B : (symComplexD hΩ hb).d1†.domain,
        ⟪(symComplexD hΩ hb).d1† B, constS hΩ hb⟫ = 0 := by
  refine ⟨symComplexD_not_TSDS_le_ker hΩ hb hne, TSDSk_le_ker hΩ hb,
    symComplexD_d1_mem_TSDT hΩ hb, fun ρ hρ => ⟨symComplexD_adjoint_d1_mem_TSDS hΩ hb ρ hρ, ?_⟩,
    symComplexD_not_projection_hyp hΩ hb hne _, (symComplexD_not_dense hΩ hb hne).2,
    fun E => ?_, symComplexD_inner_adjoint_d1_constS hΩ hb⟩
  · exact LinearPMap.mem_ker_iff.2 ⟨⟨_, (symComplexD hΩ hb).adjoint_map_mem ρ⟩, rfl,
      (symComplexD hΩ hb).adjoint_comp_zero ρ⟩
  · obtain ⟨y, hy, -⟩ := LinearPMap.mem_ker_iff.1
      (TSDSk_le_ker hΩ hb (Submodule.starProjection_apply_mem (TSDSk Ω hΩ hb) E))
    exact hy ▸ y.2

theorem constS_not_mem_TSDSk (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    constS hΩ hb ∉ TSDSk Ω hΩ hb := fun h => by
  obtain ⟨y, hy, -⟩ := LinearPMap.mem_ker_iff.1 h.2
  exact constS_not_mem_adjoint_d0 hΩ hb hne (hy ▸ y.2)

/-- **Corrected Prop 4.19 for `symComplexD`, maximal form** (unconditional). For the Hodge wave
group of `symComplexD` (Stone's theorem) and `K = {0} × (L²(TSD) ∩ ker d0*) × L²(TSD)`, the largest
invariant subspace `K* = {0} × S1* × S2*` satisfies every hypothesis of
`Feec.Constraints.prop_4_17`, is the largest such constraint space, misses `diag(1, -1, 0)`, and
its data propagate: every `(0, E₀, B₀) ∈ D(L)` with `E₀ ∈ S1*`, `B₀ ∈ S2*` has a unique strong
solution, which stays in `{0} × L²(TSD) × L²(TSD)` and solves the reduced system.

Scope: as for `symComplexB_prop_4_19_max`, `K*` is invariant by construction. What is open here is
whether `K* ⊇ D(L) ∩ K`, i.e. the conclusion of Prop 4.19 for these boundary conditions. -/
theorem symComplexD_prop_4_19_max (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    let G := (symComplexD hΩ hb).waveGroup
    Kmax G (Kc (L2 Ω) (TSDSk Ω hΩ hb) (TSDT Ω)) =
        Kc (L2 Ω) (S1max G (TSDSk Ω hΩ hb) (TSDT Ω)) (S2max G (TSDSk Ω hΩ hb) (TSDT Ω)) ∧
      S1max G (TSDSk Ω hΩ hb) (TSDT Ω) ≤ TSDSk Ω hΩ hb ∧
      S2max G (TSDSk Ω hΩ hb) (TSDT Ω) ≤ TSDT Ω ∧
      (∀ x ∈ (symComplexD hΩ hb).domL, projKc (L2 Ω) (S1max G (TSDSk Ω hΩ hb) (TSDT Ω))
        (S2max G (TSDSk Ω hΩ hb) (TSDT Ω)) x ∈ (symComplexD hΩ hb).domL) ∧
      (∀ u : (symComplexD hΩ hb).d1.domain, (u : L2S Ω) ∈ S1max G (TSDSk Ω hΩ hb) (TSDT Ω) →
        (symComplexD hΩ hb).d1 u ∈ S2max G (TSDSk Ω hΩ hb) (TSDT Ω)) ∧
      (∀ ρ : (symComplexD hΩ hb).d1†.domain,
        (ρ : L2T Ω) ∈ S2max G (TSDSk Ω hΩ hb) (TSDT Ω) →
        (symComplexD hΩ hb).d1† ρ ∈ S1max G (TSDSk Ω hΩ hb) (TSDT Ω)) ∧
      (∀ (S1' : Submodule ℝ (L2S Ω)) (S2' : Submodule ℝ (L2T Ω)) [S1'.HasOrthogonalProjection]
        [S2'.HasOrthogonalProjection], S1' ≤ TSDSk Ω hΩ hb → S2' ≤ TSDT Ω →
        (∀ x ∈ (symComplexD hΩ hb).domL, projKc (L2 Ω) S1' S2' x ∈ (symComplexD hΩ hb).domL) →
        (∀ u : (symComplexD hΩ hb).d1.domain, (u : L2S Ω) ∈ S1' →
          (symComplexD hΩ hb).d1 u ∈ S2') →
        (∀ ρ : (symComplexD hΩ hb).d1†.domain, (ρ : L2T Ω) ∈ S2' →
          (symComplexD hΩ hb).d1† ρ ∈ S1') →
        S1' ≤ S1max G (TSDSk Ω hΩ hb) (TSDT Ω) ∧ S2' ≤ S2max G (TSDSk Ω hΩ hb) (TSDT Ω)) ∧
      constS hΩ hb ∉ S1max G (TSDSk Ω hΩ hb) (TSDT Ω) ∧
      ∀ (T : ℝ) (E₀ : L2S Ω) (B₀ : L2T Ω), ini (L2 Ω) E₀ B₀ ∈ (symComplexD hΩ hb).domL →
        E₀ ∈ S1max G (TSDSk Ω hΩ hb) (TSDT Ω) → B₀ ∈ S2max G (TSDSk Ω hΩ hb) (TSDT Ω) →
        ∃ U, IsStrongSolution (-(symComplexD hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U ∧
          (∀ U', IsStrongSolution (-(symComplexD hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U' →
            EqOn U' U (Icc 0 T)) ∧
          (∀ t ∈ Icc 0 T, U t ∈ Kc (L2 Ω) (TSDS Ω) (TSDT Ω)) ∧
          IsReducedSolution (symComplexD hΩ hb) T E₀ B₀
            (fun t => (tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).2.1)
            (fun t => (tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).2.2) := by
  intro G
  refine ⟨Kmax_eq_Kc G, S1max_le G, S2max_le G, projKcMax_mem_domL G,
    fun u hu => d1_mem_S2max G (TSDSk_le_ker hΩ hb) u hu,
    fun ρ hρ => adj1_mem_S1max G ρ hρ,
    fun S1' S2' _ _ h1 h2 hPD hd1 hd1s =>
      le_max_of_prop_4_17_hyps G (TSDSk_le_ker hΩ hb) h1 h2 hPD hd1 hd1s,
    fun h => constS_not_mem_TSDSk hΩ hb hne (S1max_le G h),
    fun T E₀ B₀ hD hE₀ hB₀ => ?_⟩
  obtain ⟨U, hU, huniq, hK, hred⟩ := prop_4_17_max_unconditional (symComplexD hΩ hb)
    (TSDSk_le_ker hΩ hb) T hD hE₀ hB₀
  exact ⟨U, hU, huniq, fun t ht => Kc_mono ((S1max_le G).trans inf_le_left) (S2max_le G)
    (hK t ht), hred⟩

end Feec.BoundedSym
