module

public import Feec.Domain.Operators
public import Feec.Domain.Obstruction
public import Feec.HilbertComplex.Reducing
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# The grad–curl complex on a bounded domain (thesis §4.10)

On an open `Ω ⊆ ℝ³` the thesis' complex for the Einstein–Bianchi system (4.14) is
`H̊¹(Ω; 𝕜³) --grad--> H̊(curl, Ω; 𝕜³ˣ³) --curl--> L²(Ω; 𝕜³ˣ³)` (row-wise grad and curl), the
**minimal complex** of the operators `Feec.Domain.gradOp 3 3`, `Feec.Domain.curlOp 3`
(`gradCurl`); the maximal complex `H¹ → H(curl) → L²` is `gradCurlMax`, and the duality of
`Feec.Domain.Complexes` identifies the adjoints: `d₀† = -div` on `H(div)` and `d₁† = curl` on
`H(curl)` (`adjoint_gradCurl_d₀`, `adjoint_gradCurl_d₁`, `mem_adjoint_gradCurl_d₁_domain_iff`).

The constraint of thesis Prop 4.17 is `L²(TSD)` (`tsd`): symmetric, trace-free, weakly
divergence-free in `Ω`, with **no** boundary condition. On every bounded open `Ω`:

* **zero mean** (`integral_eq_zero_of_mem_tsd`): every `B ∈ L²(TSD) ∩ H̊(curl)` has
  `∫_Ω B = 0` (curl `B` is symmetric, `curl_symm_of_mem_tsd`, then Green's formula against
  linear fields with no boundary condition, `Feec.Domain.ConstCoeffOp.minimal_green`);
* hence the projection hypothesis is false (`exists_projTSD_not_mem_domain`), `L²(TSD) ∩ H̊(curl)`
  is not dense in `L²(TSD)` (`not_dense_tsd_inter`), the TSD family is **not a reducing
  subcomplex** of any complex with `d₁ ⊆ curl_min` (`not_reducingSubcomplex_tsd`), and TSD data
  do **not propagate** (`not_propagates`, through the `Ė(0)` obstruction
  `Feec.ShortHilbertComplex.not_propagates_of_inner_ne_zero`).

These refutations move to `Counterexamples` in wave 6.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.10 (Prop 4.17)
* [Arnold2018], §6.2
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff Matrix ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

/-- Points of `ℝ³`. -/
abbrev R3 := Fin 3 → ℝ

/-- Index pairs `(i, j)` of `3 × 3` matrices. -/
abbrev Ix := Fin 3 × Fin 3

/-! ## The complexes -/

section Complexes

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3}

variable (𝕜) in
/-- **The thesis' complex** `H̊¹(Ω; 𝕜³) --grad--> H̊(curl, Ω; 𝕜³ˣ³) --curl--> L²(Ω; 𝕜³ˣ³)`:
the minimal complex of the row-wise grad and curl (electric boundary conditions). -/
def gradCurl (hΩ : IsOpen Ω) :
    ShortHilbertComplex 𝕜 (L2F 𝕜 Ω (Fin 3)) (L2F 𝕜 Ω Ix) (L2F 𝕜 Ω Ix) :=
  ConstCoeffOp.shortMinimal (gradOp 3 3) (curlOp 3) hΩ isComplexPair_grad_curl

variable (𝕜) in
/-- The maximal complex `H¹(Ω; 𝕜³) --grad--> H(curl, Ω; 𝕜³ˣ³) --curl--> L²(Ω; 𝕜³ˣ³)`
(no boundary conditions). -/
def gradCurlMax (hΩ : IsOpen Ω) :
    ShortHilbertComplex 𝕜 (L2F 𝕜 Ω (Fin 3)) (L2F 𝕜 Ω Ix) (L2F 𝕜 Ω Ix) :=
  ConstCoeffOp.shortMaximal (gradOp 3 3) (curlOp 3) hΩ isComplexPair_grad_curl

@[simp] theorem gradCurl_d₀ (hΩ : IsOpen Ω) :
    (gradCurl 𝕜 hΩ).d₀ = (gradOp 3 3 : ConstCoeffOp R3 𝕜 _ _).minimal Ω := rfl

@[simp] theorem gradCurl_d₁ (hΩ : IsOpen Ω) :
    (gradCurl 𝕜 hΩ).d₁ = (curlOp 3 : ConstCoeffOp R3 𝕜 _ _).minimal Ω := rfl

/-- `d₀† = (gradᵗ)_max = -div` on `H(div, Ω; 𝕜³ˣ³)` (no boundary condition). -/
theorem adjoint_gradCurl_d₀ (hΩ : IsOpen Ω) :
    (gradCurl 𝕜 hΩ).d₀† = (gradOp 3 3 : ConstCoeffOp R3 𝕜 _ _).formalAdj.maximal Ω :=
  ConstCoeffOp.adjoint_minimal _

/-- `d₁† = (curlᵗ)_max`, the weak curl on `H(curl, Ω; 𝕜³ˣ³)` (no boundary condition). -/
theorem adjoint_gradCurl_d₁ (hΩ : IsOpen Ω) :
    (gradCurl 𝕜 hΩ).d₁† = (curlOp 3 : ConstCoeffOp R3 𝕜 _ _).formalAdj.maximal Ω :=
  ConstCoeffOp.adjoint_minimal _

/-- Duality: the adjoints of the maximal complex are the minimal realizations of the formal
adjoints (`d₀† = -div` on `H̊(div)`, `d₁† = curl` on `H̊(curl)`). -/
theorem adjoint_gradCurlMax_d₀ (hΩ : IsOpen Ω) :
    (gradCurlMax 𝕜 hΩ).d₀† = (gradOp 3 3 : ConstCoeffOp R3 𝕜 _ _).formalAdj.minimal Ω :=
  ConstCoeffOp.adjoint_maximal _ hΩ

theorem adjoint_gradCurlMax_d₁ (hΩ : IsOpen Ω) :
    (gradCurlMax 𝕜 hΩ).d₁† = (curlOp 3 : ConstCoeffOp R3 𝕜 _ _).formalAdj.minimal Ω :=
  ConstCoeffOp.adjoint_maximal _ hΩ

/-- **`D(d₁†) = H(curl)`**: `B ∈ D(d₁†)` iff `B` has a weak curl in `L²`. -/
theorem mem_adjoint_gradCurl_d₁_domain_iff (hΩ : IsOpen Ω) {B : L2F 𝕜 Ω Ix} :
    B ∈ (gradCurl 𝕜 hΩ).d₁†.domain ↔ ∃ C : L2F 𝕜 Ω Ix, ∀ Φ : Ix → R3 → 𝕜,
      ∀ hΦ : IsTestField Ω Φ,
        ⟪C, testField hΦ⟫_𝕜 = ⟪B, testField ((curlOp 3).isTestField_apply hΦ)⟫_𝕜 :=
  ConstCoeffOp.mem_adjoint_minimal_domain_iff _ hΩ

/-- **`D(d₀†) = H(div)`**: `B ∈ D(d₀†)` iff `B` has a weak (row-wise) divergence in `L²`. -/
theorem mem_adjoint_gradCurl_d₀_domain_iff (hΩ : IsOpen Ω) {B : L2F 𝕜 Ω Ix} :
    B ∈ (gradCurl 𝕜 hΩ).d₀†.domain ↔ ∃ D : L2F 𝕜 Ω (Fin 3), ∀ φ : Fin 3 → R3 → 𝕜,
      ∀ hφ : IsTestField Ω φ,
        ⟪D, testField hφ⟫_𝕜 = ⟪B, testField ((gradOp 3 3).isTestField_apply hφ)⟫_𝕜 :=
  ConstCoeffOp.mem_adjoint_minimal_domain_iff _ hΩ

end Complexes

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


/-! ## Partial derivatives and the row-wise curl of real fields -/

/-- The partial derivative `∂_k f`. -/
def pd (k : Fin 3) (f : R3 → ℝ) (x : R3) : ℝ := fderiv ℝ f x (Pi.single k 1)

/-- The row-wise curl `(curl Φ)_{ik} = ∂_{k+1} Φ_{i,k+2} - ∂_{k+2} Φ_{i,k+1}`. -/
def curlM (Φ : Ix → R3 → ℝ) (ik : Ix) (x : R3) : ℝ :=
  pd (ik.2 + 1) (Φ (ik.1, ik.2 + 2)) x - pd (ik.2 + 2) (Φ (ik.1, ik.2 + 1)) x

@[simp] theorem pd_zero (k : Fin 3) (x : R3) : pd k (0 : R3 → ℝ) x = 0 := by simp [pd]

theorem curlM_eq_apply (Φ : Ix → R3 → ℝ) :
    curlM Φ = (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply Φ := by
  funext ik x
  rw [curlOp_apply]
  rfl

theorem curlM_eq_formalAdj_apply (Φ : Ix → R3 → ℝ) :
    curlM Φ = (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply Φ := by
  rw [curlOp_formalAdj_apply, curlM_eq_apply]

theorem continuous_pd {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (k : Fin 3) : Continuous (pd k f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_curlM {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (ij : Ix) :
    Continuous (curlM Ψ ij) :=
  (continuous_pd (hΨ _) _).sub (continuous_pd (hΨ _) _)

theorem pd_sub {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (k : Fin 3)
    (x : R3) : pd k (f - g) x = pd k f x - pd k g x := by
  rw [pd, fderiv_sub (hf x) (hg x)]
  rfl

theorem pd_ite_zero (c : Prop) [Decidable c] (f : R3 → ℝ) (k : Fin 3) (x : R3) :
    pd k (if c then f else 0) x = if c then pd k f x else 0 := by
  split_ifs
  · rfl
  · simp [pd]

/-- `∂_k x_a = δ_{ka}`. -/
theorem pd_coord (a k : Fin 3) (x : R3) :
    pd k (fun y : R3 => y a) x = if k = a then 1 else 0 := by
  rw [pd, (hasFDerivAt_apply a x).fderiv]
  simp [Pi.single_apply, eq_comm]

/-! ## Real `L²` pairings -/

variable {Ω : Set R3}

theorem integral_mul_eq_inner (f : L2 ℝ Ω) {g : R3 → ℝ} (hg : MemLp g 2 (volume.restrict Ω)) :
    ∫ x, f x * g x ∂volume.restrict Ω = ⟪f, hg.toLp g⟫_ℝ := by
  rw [inner_toLp]
  simp

theorem integrable_mul (f : L2 ℝ Ω) {g : R3 → ℝ} (hg : MemLp g 2 (volume.restrict Ω)) :
    Integrable (fun x => f x * g x) (volume.restrict Ω) := by
  simpa using integrable_conj_mul f hg

/-- `⟪B, Φ⟫ = Σ_{ij} ∫_Ω B_{ij} Φ_{ij}` for a test field `Φ`. -/
theorem inner_testField_eq {ι : Type*} [Fintype ι] (B : L2F ℝ Ω ι) {Φ : ι → R3 → ℝ}
    (hΦ : IsTestField Ω Φ) :
    ⟪B, testField hΦ⟫_ℝ = ∑ ij, ∫ x, B ij x * Φ ij x ∂volume.restrict Ω := by
  rw [inner_testField]
  simp

/-- `⟪B, Ψ⟫ = Σ_{ij} ∫_Ω B_{ij} Ψ_{ij}` for an `L²` field given by functions. -/
theorem inner_toL2F_eq {ι : Type*} [Fintype ι] (B : L2F ℝ Ω ι) {Ψ : ι → R3 → ℝ}
    (hΨ : ∀ i, MemLp (Ψ i) 2 (volume.restrict Ω)) :
    ⟪B, toL2F hΨ⟫_ℝ = ∑ ij, ∫ x, B ij x * Ψ ij x ∂volume.restrict Ω := by
  rw [inner_toL2F]
  simp

/-- Integration by parts against a test function, no boundary condition on `g ∈ C¹`. -/
theorem integral_pd_mul {f g : R3 → ℝ} (hf : IsTest Ω f) (hg : ContDiff ℝ 1 g) (k : Fin 3) :
    ∫ x, pd k f x * g x ∂volume.restrict Ω = -∫ x, f x * pd k g x ∂volume.restrict Ω := by
  have h0 : ∀ x, x ∉ Ω → pd k f x * g x = 0 := fun x hx => by
    have := (hf.fderiv_apply (Pi.single k 1)).eq_zero_of_notMem hx
    rw [pd, this, zero_mul]
  have h1 : ∀ x, x ∉ Ω → f x * pd k g x = 0 := fun x hx => by
    rw [hf.eq_zero_of_notMem hx, zero_mul]
  rw [integral_restrict_of_eq_zero h0, integral_restrict_of_eq_zero h1]
  simpa [pd] using integral_conj_fderiv_mul (𝕜 := ℝ) hf hg (Pi.single k 1)

/-- **Fundamental lemma** in `L²(Ω)` (`Ω` open, bounded or not). -/
theorem L2_ext_of_integral (hΩ : IsOpen Ω) {f f' : L2 ℝ Ω}
    (h : ∀ g, IsTest Ω g →
      ∫ x, f x * g x ∂volume.restrict Ω = ∫ x, f' x * g x ∂volume.restrict Ω) : f = f' := by
  refine sub_eq_zero.1 (L2.eq_zero_of_forall_inner_toL2 hΩ _ fun g hg => ?_)
  rw [inner_sub_left, inner_toL2, inner_toL2]
  simpa [sub_eq_zero] using h g hg

/-! ## The constraint space `L²(TSD)` -/

variable (Ω) in
/-- `L²(TSD)`: symmetric, trace-free matrix fields whose (row-wise) divergence vanishes weakly in
`Ω`, with **no** boundary condition: `∫ Σ_{ij} B_{ij} ∂_j φ_i = 0` for all `φ ∈ C_c^∞(Ω; ℝ³)`.
Thesis: Prop 4.17 -/
def tsd : Submodule ℝ (L2F ℝ Ω Ix) where
  carrier := {B | (∀ i j, B (i, j) = B (j, i)) ∧ ∑ i, B (i, i) = 0 ∧
    ∀ φ : Fin 3 → R3 → ℝ, ∀ hφ : IsTestField Ω φ,
      ⟪B, testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)⟫_ℝ = 0}
  zero_mem' := ⟨fun _ _ => rfl, by simp, fun _ _ => inner_zero_left _⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
    · simp only [PiLp.add_apply, ha1 i j, hb1 i j]
    · simp only [PiLp.add_apply, Finset.sum_add_distrib, ha2, hb2, add_zero]
    · rw [inner_add_left, ha3 φ hφ, hb3 φ hφ, add_zero]
  smul_mem' := by
    rintro c B ⟨h1, h2, h3⟩
    refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
    · simp only [PiLp.smul_apply, h1 i j]
    · simp only [PiLp.smul_apply, ← Finset.smul_sum, h2, smul_zero]
    · rw [inner_smul_left, h3 φ hφ, mul_zero]

theorem mem_tsd {B : L2F ℝ Ω Ix} : B ∈ tsd Ω ↔ (∀ i j, B (i, j) = B (j, i)) ∧
    ∑ i, B (i, i) = 0 ∧ ∀ φ : Fin 3 → R3 → ℝ, ∀ hφ : IsTestField Ω φ,
      ⟪B, testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)⟫_ℝ = 0 :=
  Iff.rfl

/-- `L²(TSD) = sym ∩ trace-free ∩ N(d₀†)`: the divergence condition is `d₀† B = 0` for the thesis'
complex. -/
theorem mem_tsd_iff_ker (hΩ : IsOpen Ω) {B : L2F ℝ Ω Ix} :
    B ∈ tsd Ω ↔ (∀ i j, B (i, j) = B (j, i)) ∧ ∑ i, B (i, i) = 0 ∧
      B ∈ (gradCurl ℝ hΩ).d₀†.ker := by
  rw [mem_tsd]
  refine and_congr_right' (and_congr_right' ?_)
  rw [LinearPMap.mem_ker_iff]
  constructor
  · intro h
    have hmem := ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).mem_adjoint_minimal_domain_iff hΩ).2
      ⟨0, fun φ hφ => by rw [inner_zero_left, h φ hφ]⟩
    exact ⟨⟨B, hmem⟩, rfl, (gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).adjoint_minimal_apply_eq hΩ _
      fun φ hφ => by rw [inner_zero_left, h φ hφ]⟩
  · rintro ⟨y, rfl, hy⟩ φ hφ
    rw [← (gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).adjoint_minimal_inner_testField hΩ y hφ]
    erw [hy]
    exact inner_zero_left _

theorem isClosed_tsd : IsClosed (tsd Ω : Set (L2F ℝ Ω Ix)) := by
  have e : (tsd Ω : Set (L2F ℝ Ω Ix)) =
      ((⋂ i : Fin 3, ⋂ j : Fin 3, {B : L2F ℝ Ω Ix | B (i, j) = B (j, i)}) ∩
        {B | ∑ i, B (i, i) = 0}) ∩ ⋂ φ : Fin 3 → R3 → ℝ, ⋂ hφ : IsTestField Ω φ,
          {B | ⟪B, testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)⟫_ℝ = 0} := by
    ext B
    simp only [SetLike.mem_coe, mem_tsd, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    tauto
  rw [e]
  refine (IsClosed.inter ?_ ?_).inter ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (L2F.continuous_apply (i, j)) (L2F.continuous_apply (j, i))
  · exact isClosed_eq (continuous_finsetSum Finset.univ fun i _ => L2F.continuous_apply (i, i))
      continuous_const
  · exact isClosed_iInter fun φ => isClosed_iInter fun hφ =>
      isClosed_eq (continuous_id.inner continuous_const) continuous_const

instance : (tsd Ω).HasOrthogonalProjection := by
  have : CompleteSpace (tsd Ω) := isClosed_tsd.completeSpace_coe
  infer_instance

/-! ## Skew fields `Ψ_{j·} = e_j × ψ` and their curl -/

/-- The skew matrix field with rows `e_j × ψ`:
`skewOf ψ (j, k) = [j = k+1] ψ_{k+2} - [j = k+2] ψ_{k+1}`. -/
def skewOf (ψ : Fin 3 → R3 → ℝ) (jk : Ix) : R3 → ℝ :=
  (if jk.1 = jk.2 + 1 then ψ (jk.2 + 2) else 0) - (if jk.1 = jk.2 + 2 then ψ (jk.2 + 1) else 0)

theorem skewOf_swap (ψ : Fin 3 → R3 → ℝ) (j k : Fin 3) (x : R3) :
    skewOf ψ (k, j) x = -skewOf ψ (j, k) x := by
  fin_cases j <;> fin_cases k <;> simp [skewOf]

theorem contDiff_skewOf {n : WithTop ℕ∞} {ψ : Fin 3 → R3 → ℝ} (hψ : ∀ i, ContDiff ℝ n (ψ i))
    (jk : Ix) : ContDiff ℝ n (skewOf ψ jk) := by
  unfold skewOf
  apply ContDiff.sub <;> split_ifs <;> first | exact hψ _ | exact contDiff_const

theorem isTestField_skewOf {ψ : Fin 3 → R3 → ℝ} (hψ : IsTestField Ω ψ) :
    IsTestField Ω (skewOf ψ) := by
  intro jk
  unfold skewOf
  apply IsTest.sub <;> split_ifs <;> first | exact hψ _ | exact IsTest.zero

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
theorem sum_integral_mul_skewOf_eq_zero {C : L2F ℝ Ω Ix} (hC : ∀ j k, C (j, k) = C (k, j))
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

theorem integral_ite_zero (c : Prop) [Decidable c] (f : R3 → ℝ) :
    ∫ x, (if c then f x else 0) ∂volume.restrict Ω =
      if c then ∫ x, f x ∂volume.restrict Ω else 0 := by
  split_ifs <;> simp

/-- The divergence pairing `⟪B, grad φ⟫ = Σ_{ij} ∫ B_{ij} ∂_j φ_i`. -/
theorem inner_grad_testField (B : L2F ℝ Ω Ix) {φ : Fin 3 → R3 → ℝ} (hφ : IsTestField Ω φ) :
    ⟪B, testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)⟫_ℝ =
      ∑ ij : Ix, ∫ x, B ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω := by
  rw [inner_testField_eq]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp only [gradOp_apply]
  rfl

/-- For `B ∈ L²(TSD)` and `ψ ∈ C_c^∞(Ω; ℝ³)`: `∫ B : curl (skewOf ψ) = 0`, the weak form of
"`curl B` is symmetric" (part of Lemma 3.5). -/
theorem sum_integral_mul_curlM_skewOf_eq_zero {B : L2F ℝ Ω Ix} (hB : B ∈ tsd Ω)
    {ψ : Fin 3 → R3 → ℝ} (hψ : IsTestField Ω ψ) :
    ∑ jk, ∫ x, B jk x * curlM (skewOf ψ) jk x ∂volume.restrict Ω = 0 := by
  obtain ⟨hsym, htr, hdiv⟩ := hB
  set d : R3 → ℝ := fun x => ∑ m, pd m (ψ m) x with hd
  have hdt : IsTest Ω d := IsTest.sum _ fun m _ => (hψ m).fderiv_apply _
  simp only [curlM_skewOf (fun i => (hψ i).differentiable), mul_sub]
  rw [Finset.sum_congr rfl fun jk _ => integral_sub ?_ ?_]
  rotate_left
  · exact integrable_mul _ (by split_ifs; exacts [hdt.memLp, MemLp.zero])
  · exact integrable_mul _ ((hψ _).fderiv_apply _).memLp
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ jk : Ix, ∫ x, B jk x * (if jk.1 = jk.2 then d x else 0) ∂volume.restrict Ω = 0 := by
    simp only [mul_ite, mul_zero, integral_ite_zero, Fintype.sum_prod_type, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    simp only [fun f : L2 ℝ Ω => integral_mul_eq_inner f hdt.memLp, ← sum_inner, htr,
      inner_zero_left]
  have h2 : ∑ jk : Ix, ∫ x, B jk x * pd jk.1 (ψ jk.2) x ∂volume.restrict Ω = 0 := by
    rw [← (inner_grad_testField B hψ).symm.trans (hdiv ψ hψ)]
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
    obtain ⟨j, k⟩ := jk
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hsym j k]
  rw [h1, h2, sub_zero]

/-- The graph-closure identity of the minimal curl against a `C¹` field with no boundary
condition (`Ω` bounded): `∫ C : Ψ = ∫ B : curl Ψ`. -/
theorem minimal_curl_identity (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (B : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ∑ ij, ∫ x, (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω B ij x * Ψ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, (B : L2F ℝ Ω Ix) ij x * curlM Ψ ij x ∂volume.restrict Ω := by
  have m1 : ∀ ij, MemLp (Ψ ij) 2 (volume.restrict Ω) := fun ij =>
    memLp_of_continuous hΩ.measurableSet hb (hΨ ij).continuous
  have m2 : ∀ ij, MemLp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply Ψ ij) 2
      (volume.restrict Ω) := fun ij => by
    rw [← curlM_eq_formalAdj_apply]
    exact memLp_of_continuous hΩ.measurableSet hb (continuous_curlM hΨ ij)
  have := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal_green hΩ (N := 1) curlOp_isOrderLE B
    (fun ij => (hΨ ij).of_le (by norm_num)) m1 m2
  rw [inner_toL2F_eq, inner_toL2F_eq] at this
  simpa only [← curlM_eq_formalAdj_apply] using this

/-- **Lemma 3.5 (symmetry part), distributional form on `H̊(curl)`.** If `B ∈ L²(TSD)` lies in
`D(curl_min)`, then `curl B` is symmetric. Thesis: Lemma 3.5 -/
theorem curl_symm_of_mem_tsd (hΩ : IsOpen Ω)
    (B : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) (hB : (B : L2F ℝ Ω Ix) ∈ tsd Ω)
    (j k : Fin 3) :
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω B (j, k) =
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω B (k, j) := by
  set C := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω B
  have key : ∀ m : Fin 3, C (m + 2, m + 1) = C (m + 1, m + 2) := by
    intro m
    refine L2_ext_of_integral hΩ fun g hg => ?_
    let ψ : Fin 3 → R3 → ℝ := fun i => if i = m then g else 0
    have hψ : IsTestField Ω ψ := fun i => by
      by_cases hi : i = m
      · simpa [ψ, hi] using hg
      · simpa [ψ, hi] using (IsTest.zero : IsTest Ω (0 : R3 → ℝ))
    have hΦ := isTestField_skewOf hψ
    have e := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).closure_testGraph_inner_testField
      ((curlOp 3).mem_closure_minimal hΩ B) hΦ
    rw [inner_testField_eq, inner_testField_eq] at e
    simp only [← curlM_eq_formalAdj_apply] at e
    rw [sum_integral_mul_curlM_skewOf_eq_zero hB hψ] at e
    fin_cases m <;>
      simp [ψ, skewOf, Fintype.sum_prod_type, Fin.sum_univ_three, integral_neg] at e ⊢ <;>
      linarith
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  simp only [Fin.isValue, Fin.reduceAdd] at k0 k1 k2
  fin_cases j <;> fin_cases k <;> simp [k0, k1, k2]

/-- **Zero mean.** On a bounded open `Ω ⊆ ℝ³`, every `B ∈ L²(TSD) ∩ H̊(curl)` has
`∫_Ω B_{ab} = 0`: formally `∫_Ω B : ∇v = ∫_{∂Ω} (B n)·v = 0`. Proof: `C = curl B` is symmetric;
Green's formula for `curl_min` against the linear skew field `skewOf (x_a e_b)` (no boundary
condition) gives `0 = ∫ C : Ψ = ∫ B : curl Ψ = δ_{ab} ∫ tr B - ∫ B_{ab}`. Thesis: Prop 4.17 -/
theorem integral_eq_zero_of_mem_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (B : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) (hB : (B : L2F ℝ Ω Ix) ∈ tsd Ω)
    (a b : Fin 3) : ∫ x, (B : L2F ℝ Ω Ix) (a, b) x ∂volume.restrict Ω = 0 := by
  have hCs := curl_symm_of_mem_tsd hΩ B hB
  set v : Fin 3 → R3 → ℝ := fun i => if i = b then (fun y : R3 => y a) else 0 with hv
  have hvd : ∀ i, ContDiff ℝ 1 (v i) := fun i => by
    simp only [hv]
    split_ifs
    exacts [contDiff_apply ℝ (fun _ : Fin 3 => ℝ) a, contDiff_const]
  have hpd : ∀ m i x, pd m (v i) x = if i = b ∧ m = a then 1 else 0 := by
    intro m i x
    by_cases hi : i = b
    · simp [hv, hi, pd_coord]
    · simp only [hv, hi, ite_false, false_and]
      simp [pd]
  have hdv : ∀ x, ∑ m, pd m (v m) x = if a = b then 1 else 0 := by
    intro x
    simp only [hpd, Fin.sum_univ_three]
    fin_cases a <;> fin_cases b <;> simp
  have e := minimal_curl_identity hΩ hb B (Ψ := skewOf v) (contDiff_skewOf hvd)
  rw [sum_integral_mul_skewOf_eq_zero hCs] at e
  simp only [curlM_skewOf (fun i => (hvd i).differentiable one_ne_zero), hdv] at e
  simp only [hpd, integral_mul_const] at e
  have hone : MemLp (fun _ : R3 => (1 : ℝ)) 2 (volume.restrict Ω) :=
    memLp_of_continuous hΩ.measurableSet hb continuous_const
  have hI : ∀ f : L2 ℝ Ω, ∫ x, f x ∂volume.restrict Ω = ⟪f, hone.toLp _⟫_ℝ := fun f => by
    rw [← integral_mul_eq_inner]; simp
  have htr : ∑ i, ∫ x, (B : L2F ℝ Ω Ix) (i, i) x ∂volume.restrict Ω = 0 := by
    simp only [hI, ← sum_inner, hB.2.1, inner_zero_left]
  simp only [Fin.sum_univ_three] at htr
  fin_cases a <;> fin_cases b <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three] at e ⊢ <;>
    linarith


/-! ## Constant fields and the counterexamples -/

/-- The constant matrix field `A` on a bounded open `Ω`. -/
def constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    L2F ℝ Ω Ix :=
  toL2F fun ij => memLp_of_continuous hΩ.measurableSet hb
    (continuous_const : Continuous fun _ : R3 => A ij.1 ij.2)

theorem coeFn_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (ij : Ix) :
    (constField hΩ hb A ij : R3 → ℝ) =ᵐ[volume.restrict Ω] fun _ => A ij.1 ij.2 :=
  MemLp.coeFn_toLp (memLp_of_continuous hΩ.measurableSet hb
    (continuous_const : Continuous fun _ : R3 => A ij.1 ij.2))

/-- `⟪F, A⟫ = Σ_{ij} A_{ij} ∫_Ω F_{ij}`. -/
theorem inner_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (F : L2F ℝ Ω Ix) :
    ⟪F, constField hΩ hb A⟫_ℝ = ∑ ij : Ix, A ij.1 ij.2 * ∫ x, F ij x ∂volume.restrict Ω := by
  rw [constField, inner_toL2F_eq]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

theorem integral_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (ij : Ix) :
    ∫ x, constField hΩ hb A ij x ∂volume.restrict Ω = volume.real Ω * A ij.1 ij.2 := by
  rw [integral_congr_ae (coeFn_constField hΩ hb A ij), integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul]

/-- **Constant symmetric trace-free fields are in `L²(TSD)`** (no boundary condition). -/
theorem constField_mem_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = A) (htrA : A.trace = 0) :
    constField hΩ hb A ∈ tsd Ω := by
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
  · rw [inner_grad_testField _ hφ]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_congr_ae (g := fun x => A ij.1 ij.2 * pd ij.2 (φ ij.1) x)
      ((hKc ij).mono fun x hx => by simp only; rw [hx]), integral_const_mul]
    have h0 := integral_pd_mul (hφ ij.1) (contDiff_const (c := (1 : ℝ))) ij.2
    simp only [mul_one] at h0
    rw [h0]
    simp [pd]

/-- The matrix `diag(1, -1, 0)`. -/
def diagA : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem diagA_transpose : diagA.transpose = diagA := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem diagA_trace : diagA.trace = 0 := by simp [diagA, Matrix.trace, Fin.sum_univ_three]

/-- Fields of `L²(TSD) ∩ H̊(curl)` are orthogonal to every constant field. -/
theorem inner_constField_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) {F : L2F ℝ Ω Ix}
    (hF : F ∈ tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) :
    ⟪F, constField hΩ hb A⟫_ℝ = 0 := by
  rw [inner_constField]
  refine Finset.sum_eq_zero fun ij _ => ?_
  rw [integral_eq_zero_of_mem_tsd hΩ hb ⟨F, hF.2⟩ hF.1, mul_zero]

/-- **The obstruction of `L²(TSD)` for `H̊(curl)` contains the constant symmetric trace-free
fields**: they lie in `L²(TSD)` and are orthogonal to `L²(TSD) ∩ H̊(curl)`. -/
theorem constField_mem_obstruction (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = A) (htrA : A.trace = 0) :
    constField hΩ hb A ∈
      obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω) :=
  mem_obstruction.2 ⟨constField_mem_tsd hΩ hb hA htrA, fun _ hz =>
    inner_constField_eq_zero hΩ hb A hz⟩

theorem volume_real_pos (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    0 < volume.real Ω := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne

theorem constField_diagA_ne_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : constField hΩ hb diagA ≠ 0 := by
  intro h
  have := integral_constField hΩ hb diagA (0, 0)
  rw [h, show ((0 : L2F ℝ Ω Ix) (0, 0)) = (0 : L2 ℝ Ω) from rfl,
    integral_congr_ae (Lp.coeFn_zero ℝ 2 (volume.restrict Ω))] at this
  have hpos := volume_real_pos hΩ hb hne
  simp [diagA] at this
  linarith

/-- **The density claimed in the proof of Prop 4.17 fails on every nonempty bounded open `Ω`:**
`H̊(curl) ∩ L²(TSD)` is not dense in `L²(TSD)`; the obstruction is nonzero. Thesis: Prop 4.17 -/
theorem obstruction_ne_bot (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω) ≠ ⊥ := by
  intro h
  have := constField_mem_obstruction hΩ hb diagA_transpose diagA_trace
  rw [h, Submodule.mem_bot] at this
  exact constField_diagA_ne_zero hΩ hb hne this

theorem not_dense_tsd_inter (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure ≠
      tsd Ω := fun h =>
  obstruction_ne_bot hΩ hb hne ((dense_iff_obstruction_eq_bot isClosed_tsd).1 h)

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

/-- **The projection hypothesis of Prop 4.17 fails** on every nonempty bounded open `Ω`: for
`E = g · diag(1, -1, 0) ∈ C_c^∞(Ω; ℝ³ˣ³)` (any bump `g ≥ 0`, `g ≠ 0`),
`P_{L²(TSD)} E ∉ H̊(curl)`. Thesis: Prop 4.17 -/
theorem exists_projTSD_not_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ∃ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ),
      (tsd Ω).starProjection (testField hΦ) ∉
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain := by
  obtain ⟨g, hg, hgpos⟩ := exists_isTest_integral_pos hΩ hne
  let Φ : Ix → R3 → ℝ := fun ij x => diagA ij.1 ij.2 * g x
  have hΦ : IsTestField Ω Φ := fun ij => hg.const_mul (diagA ij.1 ij.2)
  refine ⟨Φ, hΦ, fun hP => ?_⟩
  have h1 : ⟪(tsd Ω).starProjection (testField hΦ), constField hΩ hb diagA⟫_ℝ =
      ⟪testField hΦ, constField hΩ hb diagA⟫_ℝ := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (constField_mem_tsd hΩ hb diagA_transpose diagA_trace)]
  have h2 := inner_constField_eq_zero hΩ hb diagA
    ⟨Submodule.starProjection_apply_mem _ _, hP⟩
  have hI : ∀ ij : Ix, ∫ x, testField hΦ ij x ∂volume.restrict Ω =
      diagA ij.1 ij.2 * ∫ x, g x ∂volume.restrict Ω := fun ij => by
    rw [← integral_const_mul]
    exact integral_congr_ae (coeFn_testField hΦ ij)
  rw [h1, inner_constField] at h2
  simp only [hI, Fintype.sum_prod_type, Fin.sum_univ_three] at h2
  simp [diagA] at h2
  linarith

/-! ## Failure of TSD propagation for the Einstein–Bianchi system -/

-- Over `𝕜 = ℝ` the generic real structure on the window spaces (needed for time derivatives
-- over a general `𝕜`) duplicates the inner-product one; use the latter.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **`K = {0} × L²(TSD) × S₂` does not reduce the wave operator** (the projection hypothesis
`P_K D(L) ⊆ D(L)` of Prop 4.17 fails) for every short complex with `D(d₁) ⊆ H̊(curl)` containing
the test fields in `D(d₁) ∩ D(d₀†)`, on every nonempty bounded open `Ω`. Thesis: Prop 4.17 -/
theorem not_isReducing_wave_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {W₀ W₂ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) W₂) (S₂ : Submodule ℝ W₂)
    [S₂.HasOrthogonalProjection]
    (hd₁ : S.d₁.domain ≤ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (htest : ∀ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ),
      testField hΦ ∈ S.d₁.domain ∧ testField hΦ ∈ S.d₀†.domain) :
    ¬ S.wave.IsReducing (HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) S₂)) := by
  intro hred
  obtain ⟨Φ, hΦ, hnot⟩ := exists_projTSD_not_mem_domain hΩ hb hne
  let x : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂) :=
    WithLp.toLp 2 (Pi.single (M := ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂) 1 (testField hΦ))
  have hx0 : (x 0 : W₀) = 0 := rfl
  have hx1 : (x 1 : L2F ℝ Ω Ix) = testField hΦ := rfl
  have hx2 : (x 2 : W₂) = 0 := rfl
  have hxD : x ∈ S.wave.domain := by
    rw [S.mem_wave_domain, hx0, hx1, hx2]
    exact ⟨Submodule.zero_mem _, (htest Φ hΦ).1, (htest Φ hΦ).2, Submodule.zero_mem _⟩
  have hP := hred.proj_mem ⟨x, hxD⟩
  rw [S.mem_wave_domain] at hP
  have h1 := hP.2.1
  rw [HilbertComplex.totalSub_starProjection_apply] at h1
  exact hnot (hd₁ h1)

/-- The magnetic datum `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`. -/
def betaField : Ix → R3 → ℝ := fun ij =>
  if ij = (0, 1) ∨ ij = (1, 0) then (fun x : R3 => x 2) else 0

theorem contDiff_betaField (ij : Ix) : ContDiff ℝ ∞ (betaField ij) := by
  unfold betaField
  split_ifs
  exacts [contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 2, contDiff_const]

/-- `curl β = -diag(1, -1, 0)`. -/
theorem curlM_betaField (ij : Ix) (x : R3) : curlM betaField ij x = -diagA ij.1 ij.2 := by
  obtain ⟨i, k⟩ := ij
  simp only [curlM, betaField, pd_ite_zero, pd_coord]
  fin_cases i <;> fin_cases k <;> simp [diagA]

/-- `β` as an element of `L²(Ω; ℝ³ˣ³)` (`Ω` bounded). -/
def betaL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : L2F ℝ Ω Ix :=
  toL2F fun ij => memLp_of_continuous hΩ.measurableSet hb (contDiff_betaField ij).continuous

/-- `β ∈ L²(TSD)`. -/
theorem betaL2_mem_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : betaL2 hΩ hb ∈ tsd Ω := by
  set K := betaL2 hΩ hb
  have hKc : ∀ ij, (K ij : R3 → ℝ) =ᵐ[volume.restrict Ω] betaField ij := fun ij =>
    MemLp.coeFn_toLp (memLp_of_continuous hΩ.measurableSet hb (contDiff_betaField ij).continuous)
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
    rw [inner_grad_testField _ hφ]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_congr_ae (g := fun x => pd ij.2 (φ ij.1) x * betaField ij x)
      ((hKc ij).mono fun x hx => by simp only; rw [hx, mul_comm]),
      integral_pd_mul (hφ ij.1) ((contDiff_betaField ij).of_le (by simp)) ij.2]
    simp [hpd]

/-- `β ∈ D(d₁†)` with `d₁† β = curl β = -diag(1, -1, 0)`, for every complex with
`d₁ ⊆ curl_min`. -/
theorem betaL2_mem_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {W₀ : Type*}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :
    ∃ h : betaL2 hΩ hb ∈ S.d₁†.domain, S.d₁† ⟨_, h⟩ = -constField hΩ hb diagA := by
  have hmax : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)† ≤ S.d₁† :=
    LinearPMap.adjoint_le_adjoint_of_le S.dense₁ hd₁
  have hcurl : ∀ ij, MemLp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply betaField ij) 2
      (volume.restrict Ω) := fun ij => by
    rw [← curlM_eq_formalAdj_apply]
    exact memLp_of_continuous hΩ.measurableSet hb
      (continuous_curlM (fun ij => (contDiff_betaField ij).of_le (by simp)) ij)
  obtain ⟨hmem, hval⟩ := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.smooth_mem_maximal_domain
    hΩ (N := 1) curlOp_isOrderLE.formalAdj (fun ij => (contDiff_betaField ij).of_le (by simp))
    (fun ij => memLp_of_continuous hΩ.measurableSet hb (contDiff_betaField ij).continuous) hcurl
  have e := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).adjoint_minimal (Ω := Ω)
  have hmem' : betaL2 hΩ hb ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)†.domain := by
    rw [e]; exact hmem
  have hval' : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)† ⟨_, hmem'⟩ = toL2F hcurl := by
    have key : ∀ T : L2F ℝ Ω Ix →ₗ.[ℝ] L2F ℝ Ω Ix,
        T = (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω →
        ∀ h : betaL2 hΩ hb ∈ T.domain, T ⟨_, h⟩ = toL2F hcurl := by
      rintro _ rfl h; exact hval
    exact key _ e _
  refine ⟨hmax.1 hmem', ?_⟩
  rw [← hmax.2 (x := ⟨_, hmem'⟩) (y := ⟨_, hmax.1 hmem'⟩) rfl, hval']
  refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
  filter_upwards [MemLp.coeFn_toLp (hcurl ij), Lp.coeFn_neg (constField hΩ hb diagA ij),
    coeFn_constField hΩ hb diagA ij] with x h1 h2 h3
  simp only [toL2F, PiLp.neg_apply] at h1 h2 ⊢
  rw [h1, h2, Pi.neg_apply, h3, ← curlM_eq_formalAdj_apply, curlM_betaField]

/-- **TSD data do not propagate** (the conclusion of thesis Prop 4.17 fails on every nonempty
bounded open `Ω ⊆ ℝ³`): for every short complex `W₀ → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` with
`d₁ ⊆ curl_min` (the electric boundary condition), the TSD datum `(0, 0, β)` lies in
`D(L) ∩ K`, `K = {0} × L²(TSD) × L²(TSD)`, and for every `T > 0` **every** strong solution of
`U' = L U` on `[0, T]` from it leaves `K`. Proof: the `Ė(0)` obstruction
(`ShortHilbertComplex.not_propagates_of_inner_ne_zero`) with `G = diag(1, -1, 0)`, orthogonal
to `L²(TSD) ∩ H̊(curl)` by the zero-mean theorem, and `⟪G, d₁† β⟫ = -2 |Ω| ≠ 0`.
Thesis: Prop 4.17 -/
theorem not_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :
    ∃ U₀ ∈ S.wave.domain, U₀ ∈ HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) (tsd Ω)) ∧
      ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)), U 0 = U₀ →
        Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) (tsd Ω)) := by
  obtain ⟨hβ, hβv⟩ := betaL2_mem_adjoint hΩ hb S hd₁
  let U₀ : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)) :=
    WithLp.toLp 2 (Pi.single (M := ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)) 2 (betaL2 hΩ hb))
  have h0 : (U₀ 0 : W₀) = 0 := rfl
  have h1 : (U₀ 1 : L2F ℝ Ω Ix) = 0 := rfl
  have h2 : (U₀ 2 : L2F ℝ Ω Ix) = betaL2 hΩ hb := rfl
  have hD : U₀ ∈ S.wave.domain := by
    rw [S.mem_wave_domain, h0, h1, h2]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, Submodule.zero_mem _, hβ⟩
  have hK : U₀ ∈ HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) (tsd Ω)) := by
    intro i
    match i with
    | 0 =>
      show (U₀ 0 : W₀) ∈ (⊥ : Submodule ℝ W₀)
      rw [h0]; exact Submodule.zero_mem _
    | 1 => exact h1 ▸ Submodule.zero_mem _
    | 2 => exact h2 ▸ betaL2_mem_tsd hΩ hb
  refine ⟨U₀, hD, hK, fun T hT U hU0 hU => ?_⟩
  have hG : constField hΩ hb diagA ∈ (tsd Ω ⊓ S.d₁.domain)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact inner_constField_eq_zero hΩ hb diagA ⟨hz.1, hd₁.1 hz.2⟩
  have hne0 : ⟪constField hΩ hb diagA, S.d₁† ⟨_, hβ⟩⟫_ℝ ≠ 0 := by
    rw [hβv, inner_neg_right, real_inner_comm, inner_constField]
    simp only [integral_constField, Fintype.sum_prod_type, Fin.sum_univ_three]
    have hpos := volume_real_pos hΩ hb hne
    simp [diagA]
    positivity
  obtain ⟨t, ht, hnot⟩ := S.not_propagates_of_inner_ne_zero hG ⟨_, hβ⟩ hne0 hT hU
    (by rw [hU0]; exact h0) (by rw [hU0]; exact h2)
  exact ⟨t, ht, fun hmem => hnot (hmem 1)⟩

end Feec.Models.BoundedDomain
