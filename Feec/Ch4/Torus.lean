module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Feec.Ch4.Constraints

/-!
# Thesis Props 4.17/4.19 on the flat torus `𝕋³`: the projection hypothesis holds

Props 4.17/4.19 ([QuennevilleBelair2015, §4.10–4.11]) propagate the TSD constraint
(symmetric, trace-free, divergence-free) for the matrix Hodge wave (4.14), under the thesis'
"conjecture" `P_{L²(TSD)} D(L) ⊆ D(L)`. `Feec.Constraints.prop_4_17` proves the abstract
statement under this projection hypothesis, and `prop_4_17_iff` shows it cannot be dropped.
This file settles the hypothesis for the periodic complex on `𝕋³ = ℝ³/ℤ³` and proves the
periodic Prop 4.17 with no hypothesis beyond the solution itself.

## Model

Fields are modelled by their Fourier coefficients: `L2V = ℓ²(ℤ³; ℂ³)` (vector fields),
`L2M = ℓ²(ℤ³; ℂ³ˣ³)` (matrix fields), as real Hilbert spaces (inner product `Re ⟨·,·⟩`).
`fieldFourier` is the linear isometric equivalence `L²(𝕋³; ℂᴾ) ≃ₗᵢ ℓ²(ℤ³; ℂᴾ)`, built from
Mathlib's Hilbert basis `UnitAddTorus.mFourierBasis` componentwise (`fieldFourier_apply`: the
coefficients are `mFourierCoeff`). The operators are Fourier multipliers with `ξ = 2πk`
(`freq`): `grad u ↦ i u ξᵀ`, row-wise `curl A ↦ i (ξ × A_a)_a` (thesis convention
`(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`, as in `Feec.curl`), `div A ↦ i A ξ`. The Sobolev spaces
`H¹`, `H(curl)`, `H(div)` are the corresponding weighted-`ℓ²` conditions (`mulDomain`). This is
the standard Fourier characterization of periodic Sobolev spaces; the identification of these
multipliers with weak derivatives of `L²(𝕋³)` functions is *not* formalized here.

Real vs complex: the theorems are stated for complex-valued fields, viewed as a real Hilbert
space. Real-valued fields are exactly the conjugate-symmetric sequences `Â(-k) = conj Â(k)`
(`IsReal`); `P_TSD` and `curl` preserve them (`isReal_projTSD`, `isReal_curlT`). The real
propagation statement is the special case of `prop_4_17_torus` for real data and solutions: a
real-valued strong solution is in particular a complex-valued one.

## Main results

* Generic multipliers on `ℓ²` (`mulOp`): closed (`isClosed_mulOp`), densely defined
  (`dense_mulDomain`), adjoint = multiplier by fibre adjoints (`adjoint_mulOp`); fibrewise
  subspaces and their projections (`fibreSub`, `starProjection_fibreSub_apply`).
* (a) Fibre algebra at `ξ ∈ ℝ³`: `tsd ξ = {M | Mᵀ = M, tr M = 0, M ξ = 0}` (at `ξ = 0`,
  symmetric trace-free: `mem_tsd_zero`); `inner_outer_tsd` (`c ξᵀ ⊥ tsd ξ`), `proj_outer`
  (`P_ξ (c ξᵀ) = 0`); `curlR_mem_tsd` (Lemma 3.5 on the symbol); `proj_curlSym` (`P_ξ` commutes
  with the curl symbol); `lagrange` (`|ξ × M_a|² + |M_a·ξ|² = |ξ|²|M_a|²`); the key estimate in
  exact form `norm_freq_mul_norm_proj`: `|ξ| ‖P_ξ A‖ = ‖P_ξ (curl_ξ A)‖ ≤ ‖rows(A) × ξ‖`
  (`norm_freq_mul_norm_proj_le`).
* (b) `projTSD_apply` (`P_TSD` is the fibrewise projection), `projTSD_mem_H1`
  (`P_TSD H(curl) ⊆ H¹`), `H1M_le_Hcurl`, `projTSD_mem_Hcurl`, `curlT_projTSD`
  (`curl P_TSD = P_TSD curl`), `norm_H1_projTSD_le`, `projTSD_mem_Hcurl_Hdiv`
  (`P_TSD (H(curl) ∩ H(div)) ⊆ H(curl) ∩ H(div)`).
* (c) `periodicComplex : HilbertComplex2 L2V L2M L2M` (`H¹(V) → H(curl; M) → L²(M)`), with
  `adjoint_curlT` (`curl* = curl`), `adjoint_gradT`/`adjoint_gradT_domain` (`grad* = -div` on
  `H(div)`); all hypotheses of `prop_4_17` for `S1 = S2 = L²(TSD)`: `L2TSD_le_ker` (`hS1`),
  `projKc_mem_domL` (`hPD`), `curlT_mem_L2TSD` (`hd1`), `adjoint_curlT_mem_L2TSD` (`hd1s`);
  hence **`prop_4_17_torus`** and its group form `prop_4_17_torus_group`.
* The review's counterexample: `projTSD_eq_zero_of_outer`, `mem_Hcurl_of_outer`.

## Correction

The thesis states Props 4.17/4.19 under the "conjecture" `P_{L²(TSD)} D(L) ⊆ D(L)` (and
density conjectures, which `prop_4_17` shows are unnecessary). For the periodic complex on
`𝕋³` (no boundary conditions) this file proves the projection hypothesis, in the stronger
form `P_TSD H(curl) ⊆ H¹` with `curl P_TSD = P_TSD curl`, and hence Prop 4.17 on `𝕋³`
unconditionally: every strong solution of (4.14) with data `(0, E₀, B₀)`, `E₀, B₀ ∈ L²(TSD)`,
keeps `σ ≡ 0`, `E, B ∈ L²(TSD)`, and solves (4.15).

The blueprint review (`docs/BLUEPRINT-REVIEW.md`, item 4) claimed the hypothesis fails on every
domain, including `𝕋³`, via `A = e₁ (∇f)ᵀ`, `f = f(x₂) ∈ H¹ \ H²`. That claim is false: it
computes `dev sym A`, the *pointwise* projection onto symmetric trace-free matrices, but
`L²(TSD)` also imposes `div = 0`, and `P_TSD` is not pointwise. Here `Â(k) = c_k ξ_kᵀ` with
`c_k = i f̂(k) e₁`, which is orthogonal to every TSD fibre, so `P_TSD A = 0 ∈ H(curl)`
(`projTSD_eq_zero_of_outer`).

What remains open: bounded domains (the thesis' setting `H̊¹(V) → H̊(curl; M) → L²(M)`), where the
`H̊(curl)` part of the hypothesis is expected to fail (see the docstring of `prop_4_17`), and
Prop 4.19 (complex (4.16), `W1 = L²(S)`, `W2 = L²(T)`), whose periodic case should follow from
the same fibre algebra but is not formalized. The existence of solutions is not constructed
here: `prop_4_17_torus` quantifies over strong solutions, and `prop_4_17_torus_group` assumes a
Stone group (`Feec.UnitaryGroupGenerator`) for `-L`.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.10 (Prop 4.17, (4.14), (4.15)), §4.11
  (Prop 4.19)
* [ACBY1997] (the Einstein–Bianchi system)
* [AFW2010], [Arnold2018], [BruningLesch1992] (Hilbert complexes)
* [Pazy1983], §1.10 (unitary groups and Stone's theorem, behind `Feec.UnitaryGroupGenerator`)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal
open LinearPMap Set MeasureTheory

namespace Feec.Torus

section Multiplier

variable {ι : Type*} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable (ι E) in
/-- `ℓ²(ι; E)`. -/
abbrev L2 := lp (fun _ : ι => E) 2

variable (m : ι → E →L[ℝ] F)

/-- The domain `{u ∈ ℓ² | (m i (u i))ᵢ ∈ ℓ²}` of a multiplier. -/
def mulDomain : Submodule ℝ (L2 ι E) where
  carrier := {u | Memℓp (fun i => m i (u i)) 2}
  zero_mem' := by
    change Memℓp (fun i => m i ((0 : L2 ι E) i)) 2
    convert (zero_memℓp : Memℓp (0 : ι → F) 2) using 1
    ext i; simp
  add_mem' := by
    intro u v hu hv
    change Memℓp (fun i => m i ((u + v : L2 ι E) i)) 2
    convert Memℓp.add hu hv using 1
    ext i; simp
  smul_mem' := by
    intro r u hu
    change Memℓp (fun i => m i ((r • u : L2 ι E) i)) 2
    convert Memℓp.const_smul hu r using 1
    ext i; simp

theorem mem_mulDomain {u : L2 ι E} : u ∈ mulDomain m ↔ Memℓp (fun i => m i (u i)) 2 := Iff.rfl

/-- The (unbounded) multiplier operator `u ↦ (m i (u i))ᵢ` on `ℓ²`. -/
def mulOp : L2 ι E →ₗ.[ℝ] L2 ι F where
  domain := mulDomain m
  toFun :=
    { toFun := fun u => ⟨fun i => m i ((u : L2 ι E) i), u.2⟩
      map_add' := fun u v => by ext i; simp; rfl
      map_smul' := fun r u => by ext i; simp [Pi.smul_apply] }

theorem mulOp_apply (u : (mulOp m).domain) (i : ι) : mulOp m u i = m i ((u : L2 ι E) i) := rfl

theorem single_mem_mulDomain [DecidableEq ι] (i : ι) (x : E) :
    lp.single 2 i x ∈ mulDomain m := by
  have : (fun j => m j ((lp.single 2 i x : L2 ι E) j)) = ⇑(lp.single 2 i (m i x) : L2 ι F) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [mem_mulDomain, this]
  exact lp.memℓp _

theorem mulOp_single [DecidableEq ι] (i : ι) (x : E) :
    mulOp m ⟨lp.single 2 i x, single_mem_mulDomain m i x⟩ = lp.single 2 i (m i x) := by
  ext j
  rw [mulOp_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Finitely supported sequences lie in the domain, so it is dense. -/
theorem dense_mulDomain : Dense (mulDomain m : Set (L2 ι E)) := by
  classical
  intro u
  have h := lp.hasSum_single (p := 2) (by norm_num) u
  refine mem_closure_of_tendsto h (Filter.Eventually.of_forall fun s => ?_)
  exact Submodule.sum_mem _ fun i _ => single_mem_mulDomain m i (u i)

/-- Multipliers are closed operators. -/
theorem isClosed_mulOp : (mulOp m).IsClosed := by
  have : ((mulOp m).graph : Set (L2 ι E × L2 ι F)) = ⋂ i, {p | m i (p.1 i) = p.2 i} := by
    ext ⟨u, v⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      rw [mulOp_apply, ← hy]
    · intro h
      have hfun : (fun i => m i (u i)) = ⇑v := funext h
      refine ⟨⟨u, (mem_mulDomain m).2 (by rw [hfun]; exact lp.memℓp v)⟩, rfl, ?_⟩
      ext i; exact h i
  change IsClosed ((mulOp m).graph : Set (L2 ι E × L2 ι F))
  rw [this]
  exact isClosed_iInter fun i => isClosed_eq
    ((m i).continuous.comp ((lp.evalCLM ℝ (fun _ : ι => E) 2 i).continuous.comp continuous_fst))
    ((lp.evalCLM ℝ (fun _ : ι => F) 2 i).continuous.comp continuous_snd)

variable [CompleteSpace E] [CompleteSpace F]

/-- The fibrewise-adjoint multiplier is a formal adjoint. -/
theorem mulOp_isFormalAdjoint :
    (mulOp m).IsFormalAdjoint (mulOp fun i => ContinuousLinearMap.adjoint (m i)) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1; ext i
  exact (ContinuousLinearMap.adjoint_inner_right (m i) _ _).symm

/-- The adjoint of a multiplier acts fibrewise by the fibre adjoints. -/
theorem adjoint_mulOp_apply (y : (mulOp m)†.domain) (i : ι) :
    (mulOp m)† y i = ContinuousLinearMap.adjoint (m i) ((y : L2 ι F) i) := by
  classical
  refine ext_inner_right ℝ fun v => ?_
  have h1 := LinearPMap.adjoint_isFormalAdjoint (dense_mulDomain m) y
    ⟨lp.single 2 i v, single_mem_mulDomain m i v⟩
  rw [lp.inner_single_right, mulOp_single, lp.inner_single_right] at h1
  rw [h1, ContinuousLinearMap.adjoint_inner_left]

/-- **The adjoint of a multiplier is the multiplier by the fibrewise adjoints.** -/
theorem adjoint_mulOp : (mulOp m)† = mulOp fun i => ContinuousLinearMap.adjoint (m i) := by
  have hle := (mulOp_isFormalAdjoint m).le_adjoint (dense_mulDomain m)
  have hdom : (mulOp m)†.domain ≤ (mulOp fun i => ContinuousLinearMap.adjoint (m i)).domain := by
    intro y hy
    have : (fun i => ContinuousLinearMap.adjoint (m i) (y i)) = ⇑((mulOp m)† ⟨y, hy⟩) :=
      funext fun i => (adjoint_mulOp_apply m ⟨y, hy⟩ i).symm
    change Memℓp _ 2
    rw [this]; exact lp.memℓp _
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

end Multiplier

section Fibre

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Fibrewise subspace `{u ∈ ℓ² | u i ∈ K i ∀ i}`. -/
def fibreSub (K : ι → Submodule ℝ E) : Submodule ℝ (L2 ι E) where
  carrier := {u | ∀ i, u i ∈ K i}
  zero_mem' := fun i => by simp
  add_mem' := fun hu hv i => by simpa using (K i).add_mem (hu i) (hv i)
  smul_mem' := fun r u hu i => by simpa using (K i).smul_mem r (hu i)

theorem mem_fibreSub {K : ι → Submodule ℝ E} {u : L2 ι E} : u ∈ fibreSub K ↔ ∀ i, u i ∈ K i :=
  Iff.rfl

theorem isClosed_fibreSub [FiniteDimensional ℝ E] (K : ι → Submodule ℝ E) :
    IsClosed (fibreSub K : Set (L2 ι E)) := by
  have : (fibreSub K : Set (L2 ι E)) = ⋂ i, (lp.evalCLM ℝ (fun _ : ι => E) 2 i) ⁻¹' (K i) := by
    ext u; simp [mem_fibreSub]; rfl
  rw [this]
  exact isClosed_iInter fun i =>
    (K i).closed_of_finiteDimensional.preimage (ContinuousLinearMap.continuous _)

instance [FiniteDimensional ℝ E] (K : ι → Submodule ℝ E) : CompleteSpace (fibreSub K) :=
  (isClosed_fibreSub K).completeSpace_coe

/-- The orthogonal projection onto a fibrewise subspace acts fibrewise. -/
theorem starProjection_fibreSub_apply [FiniteDimensional ℝ E] (K : ι → Submodule ℝ E)
    (u : L2 ι E) (i : ι) :
    (fibreSub K).starProjection u i = (K i).starProjection (u i) := by
  let v : L2 ι E := ⟨fun i => (K i).starProjection (u i),
    (lp.memℓp u).mono' fun i => (K i).norm_starProjection_apply_le (u i)⟩
  have : (fibreSub K).starProjection u = v := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (fun i => (K i).starProjection_apply_mem _) fun w hw => ?_
    rw [lp.inner_eq_tsum]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    exact (K i).starProjection_inner_eq_zero (u i) (w i) (hw i)
  rw [this]

end Fibre



abbrev Vec3 := EuclideanSpace ℂ (Fin 3)
abbrev Mat3 := EuclideanSpace ℂ (Fin 3 × Fin 3)
abbrev Freq := EuclideanSpace ℝ (Fin 3)

theorem inner_vec (u v : Vec3) :
    ⟪u, v⟫ = ∑ a, ((u a).re * (v a).re + (u a).im * (v a).im) := by
  simp [PiLp.inner_apply, Complex.mul_re]; congr 1; ext a; ring

theorem inner_mat (A B : Mat3) :
    ⟪A, B⟫ = ∑ a, ∑ b, ((A (a, b)).re * (B (a, b)).re + (A (a, b)).im * (B (a, b)).im) := by
  simp only [PiLp.inner_apply, Complex.inner, Fintype.sum_prod_type, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  congr 1; ext a; congr 1; ext b; ring

theorem norm_sq_vec (u : Vec3) : ‖u‖ ^ 2 = ∑ a, ((u a).re ^ 2 + (u a).im ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_vec]; simp [sq]

theorem norm_sq_mat (A : Mat3) : ‖A‖ ^ 2 = ∑ a, ∑ b, ((A (a, b)).re ^ 2 + (A (a, b)).im ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_mat]; simp [sq]

theorem norm_sq_freq (ξ : Freq) : ‖ξ‖ ^ 2 = ∑ c, ξ c ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp

/-- A matrix from its entries. -/
def mat (f : Fin 3 → Fin 3 → ℂ) : Mat3 := WithLp.toLp 2 fun p => f p.1 p.2

@[simp] theorem mat_apply (f : Fin 3 → Fin 3 → ℂ) (a b : Fin 3) : mat f (a, b) = f a b := rfl

/-- A vector from its entries. -/
def vec (f : Fin 3 → ℂ) : Vec3 := WithLp.toLp 2 f

@[simp] theorem vec_apply (f : Fin 3 → ℂ) (a : Fin 3) : vec f a = f a := rfl

/-- The cross product `ξ × v` of a real and a complex vector. -/
def cross (ξ : Freq) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(ξ 1 : ℂ) * v 2 - ξ 2 * v 1, (ξ 2 : ℂ) * v 0 - ξ 0 * v 2, (ξ 0 : ℂ) * v 1 - ξ 1 * v 0]

/-- The real curl symbol: row `a` of `curlR ξ M` is `ξ × M_a`. -/
def curlR (ξ : Freq) : Mat3 →L[ℝ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => mat fun a => cross ξ fun d => M (a, d)
      map_add' := fun M N => by
        ext ⟨a, b⟩; fin_cases b <;> simp [cross] <;> ring
      map_smul' := fun r M => by
        ext ⟨a, b⟩; fin_cases b <;> simp [cross, Complex.real_smul] <;> ring }

theorem curlR_apply (ξ : Freq) (M : Mat3) (a b : Fin 3) :
    curlR ξ M (a, b) = cross ξ (fun d => M (a, d)) b := rfl

/-- `curlR` is the thesis' row-wise curl `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}` (`Feec.curl`) with
`∂_c ↦ ξ_c`. See [QuennevilleBelair2015, Lemma 3.5]. -/
theorem curlR_apply_eps3 (ξ : Freq) (M : Mat3) (a b : Fin 3) :
    curlR ξ M (a, b) = ∑ c, ∑ d, (eps3 b c d : ℂ) * ξ c * M (a, d) := by
  fin_cases b <;> simp [curlR_apply, cross, Constraints.eps3_apply, Fin.sum_univ_three] <;> ring

/-- The divergence symbol `M ↦ M ξ` (row-wise). -/
def divR (ξ : Freq) : Mat3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => vec fun a => ∑ b, M (a, b) * ξ b
      map_add' := fun M N => by ext a; simp [Finset.sum_add_distrib, add_mul]
      map_smul' := fun r M => by
        ext a; simp [Complex.real_smul, Finset.mul_sum, mul_assoc] }

theorem divR_apply (ξ : Freq) (M : Mat3) (a : Fin 3) : divR ξ M a = ∑ b, M (a, b) * ξ b := rfl

/-- The outer product `c ξᵀ`. -/
def outer (c : Vec3) (ξ : Freq) : Mat3 := mat fun a b => c a * ξ b

/-- The TSD fibre at frequency `ξ`: symmetric, trace-free, `M ξ = 0`. -/
def tsd (ξ : Freq) : Submodule ℝ Mat3 where
  carrier := {M | (∀ a b, M (a, b) = M (b, a)) ∧ ∑ a, M (a, a) = 0 ∧ ∀ a, ∑ b, M (a, b) * ξ b = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro M N ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun a b => by simp [h1 a b, k1 a b], by simp [Finset.sum_add_distrib, h2, k2],
      fun a => by simp [add_mul, Finset.sum_add_distrib, h3 a, k3 a]⟩
  smul_mem' := by
    rintro r M ⟨h1, h2, h3⟩
    refine ⟨fun a b => by simp [h1 a b], ?_, fun a => ?_⟩
    · simp [Complex.real_smul, ← Finset.mul_sum, h2]
    · simp [Complex.real_smul, mul_assoc, ← Finset.mul_sum, h3 a]

theorem mem_tsd {ξ : Freq} {M : Mat3} : M ∈ tsd ξ ↔
    (∀ a b, M (a, b) = M (b, a)) ∧ ∑ a, M (a, a) = 0 ∧ ∀ a, ∑ b, M (a, b) * ξ b = 0 := Iff.rfl

/-- At `ξ = 0` the TSD fibre is the space of symmetric trace-free matrices. -/
theorem mem_tsd_zero {M : Mat3} : M ∈ tsd 0 ↔ (∀ a b, M (a, b) = M (b, a)) ∧ ∑ a, M (a, a) = 0 := by
  simp [mem_tsd]

/-- **Lemma 3.5 on the symbol**: `ξ × ·` (row-wise) maps the TSD fibre into itself.
See [QuennevilleBelair2015, §3.4, Lemma 3.5]; cf. `Feec.Constraints.curl_TSD`. -/
theorem curlR_mem_tsd {ξ : Freq} {M : Mat3} (hM : M ∈ tsd ξ) : curlR ξ M ∈ tsd ξ := by
  obtain ⟨h1, h2, h3⟩ := hM
  simp only [Fin.sum_univ_three] at h2 h3
  have e0 := h3 0; have e1 := h3 1; have e2 := h3 2
  have s10 := h1 1 0; have s20 := h1 2 0; have s21 := h1 2 1
  have t : M (2, 2) = -M (0, 0) - M (1, 1) := by linear_combination h2
  simp only [s10, s20, s21, t] at e0 e1 e2
  refine ⟨fun a b => ?_, ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;>
      simp [curlR_apply, cross, s10, s20, s21, t] <;>
      first | linear_combination e0 | linear_combination -e0 | linear_combination e1 |
        linear_combination -e1 | linear_combination e2 | linear_combination -e2
  · simp [curlR_apply, cross, Fin.sum_univ_three, s10, s20, s21]
  · fin_cases a <;> simp [curlR_apply, cross, Fin.sum_univ_three] <;> ring

/-- Multiplication by `i`, as a real-linear map. -/
def jM : Mat3 →L[ℝ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (Complex.I : ℂ) • M
      map_add' := fun M N => smul_add _ M N
      map_smul' := fun r M => smul_comm _ r M }

theorem jM_apply (M : Mat3) (p : Fin 3 × Fin 3) : jM M p = Complex.I * M p := rfl

theorem norm_jM (M : Mat3) : ‖jM M‖ = ‖M‖ := by
  change ‖(Complex.I : ℂ) • M‖ = ‖M‖
  rw [norm_smul, Complex.norm_I, one_mul]

theorem jM_mem_tsd {ξ : Freq} {M : Mat3} (hM : M ∈ tsd ξ) : jM M ∈ tsd ξ := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun a b => by simp [jM_apply, h1 a b], ?_, fun a => ?_⟩
  · simp [jM_apply, ← Finset.mul_sum, h2]
  · simp [jM_apply, mul_assoc, ← Finset.mul_sum, h3 a]

theorem inner_curlR (ξ : Freq) (A B : Mat3) : ⟪curlR ξ A, B⟫ = -⟪A, curlR ξ B⟫ := by
  simp only [inner_mat, curlR_apply, cross, Fin.sum_univ_three]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem inner_jM (A B : Mat3) : ⟪jM A, B⟫ = -⟪A, jM B⟫ := by
  simp only [inner_mat, jM_apply, Fin.sum_univ_three]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem jM_curlR (ξ : Freq) (A : Mat3) : jM (curlR ξ A) = curlR ξ (jM A) := by
  ext ⟨a, b⟩; fin_cases b <;> simp [jM_apply, curlR_apply, cross] <;> ring

/-- Row-wise Lagrange identity: `|ξ × M_a|² + |M_a · ξ|² = |ξ|² |M_a|²`, summed over rows. -/
theorem lagrange (ξ : Freq) (A : Mat3) :
    ‖curlR ξ A‖ ^ 2 + ‖divR ξ A‖ ^ 2 = ‖ξ‖ ^ 2 * ‖A‖ ^ 2 := by
  simp only [norm_sq_mat, norm_sq_vec, norm_sq_freq, curlR_apply, divR_apply, cross,
    Fin.sum_univ_three]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem divR_eq_zero_of_mem_tsd {ξ : Freq} {M : Mat3} (hM : M ∈ tsd ξ) : divR ξ M = 0 := by
  ext a; simp [divR_apply, hM.2.2 a]

/-- The gradient symbol `u ↦ i u ξᵀ`. -/
def gradSym (ξ : Freq) : Vec3 →L[ℝ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => mat fun a b => Complex.I * u a * ξ b
      map_add' := fun u v => by ext ⟨a, b⟩; simp; ring
      map_smul' := fun r u => by ext ⟨a, b⟩; simp [Complex.real_smul]; ring }

theorem gradSym_apply (ξ : Freq) (u : Vec3) (a b : Fin 3) :
    gradSym ξ u (a, b) = Complex.I * u a * ξ b := rfl

theorem curlR_gradSym (ξ : Freq) (u : Vec3) : curlR ξ (gradSym ξ u) = 0 := by
  ext ⟨a, b⟩; fin_cases b <;> simp [curlR_apply, gradSym_apply, cross] <;> ring

/-- `outer c ξ = c ξᵀ` is orthogonal to the TSD fibre. -/
theorem inner_outer_tsd {ξ : Freq} {M : Mat3} (hM : M ∈ tsd ξ) (c : Vec3) :
    ⟪outer c ξ, M⟫ = 0 := by
  have h := hM.2.2
  have r : ∀ a, ∑ b, (M (a, b)).re * ξ b = 0 := fun a => by
    simpa [Complex.mul_re] using congrArg Complex.re (h a)
  have i : ∀ a, ∑ b, (M (a, b)).im * ξ b = 0 := fun a => by
    simpa [Complex.mul_im] using congrArg Complex.im (h a)
  simp only [Fin.sum_univ_three] at r i
  simp only [inner_mat, outer, mat_apply, Fin.sum_univ_three]
  simp [Complex.mul_re, Complex.mul_im]
  linear_combination (c 0).re * r 0 + (c 1).re * r 1 + (c 2).re * r 2 + (c 0).im * i 0 +
    (c 1).im * i 1 + (c 2).im * i 2

theorem gradSym_eq_outer (ξ : Freq) (u : Vec3) : gradSym ξ u = outer ((Complex.I : ℂ) • u) ξ := by
  ext ⟨a, b⟩; simp [gradSym_apply, outer, mul_assoc]

section Torus

/-- skew maps commute with projections onto invariant subspaces -/
theorem starProjection_comm_of_skew {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (T : E →L[ℝ] E)
    (hT : ∀ x y, ⟪T x, y⟫ = -⟪x, T y⟫) (hK : ∀ x ∈ K, T x ∈ K) (x : E) :
    K.starProjection (T x) = T (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hK _ (K.starProjection_apply_mem x)) fun w hw => ?_
  rw [← _root_.map_sub, hT, K.starProjection_inner_eq_zero x _ (hK w hw), neg_zero]

/-- The curl symbol `M ↦ i (ξ × M_a)_a`. -/
def curlSym (ξ : Freq) : Mat3 →L[ℝ] Mat3 := jM ∘L curlR ξ

theorem curlSym_apply (ξ : Freq) (M : Mat3) : curlSym ξ M = jM (curlR ξ M) := rfl

theorem norm_curlSym (ξ : Freq) (M : Mat3) : ‖curlSym ξ M‖ = ‖curlR ξ M‖ := norm_jM _

theorem curlSym_mem_tsd {ξ : Freq} {M : Mat3} (hM : M ∈ tsd ξ) : curlSym ξ M ∈ tsd ξ :=
  jM_mem_tsd (curlR_mem_tsd hM)

theorem adjoint_curlSym (ξ : Freq) : ContinuousLinearMap.adjoint (curlSym ξ) = curlSym ξ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
  simp only [curlSym_apply]
  rw [inner_jM, inner_curlR, jM_curlR, neg_neg]

theorem curlSym_gradSym (ξ : Freq) (u : Vec3) : curlSym ξ (gradSym ξ u) = 0 := by
  rw [curlSym_apply, curlR_gradSym, _root_.map_zero]

/-- The TSD projection commutes with the curl symbol. -/
theorem proj_curlSym (ξ : Freq) (M : Mat3) :
    (tsd ξ).starProjection (curlSym ξ M) = curlSym ξ ((tsd ξ).starProjection M) := by
  rw [curlSym_apply, curlSym_apply,
    starProjection_comm_of_skew _ jM inner_jM (fun _ h => jM_mem_tsd h),
    starProjection_comm_of_skew _ (curlR ξ) (inner_curlR ξ) (fun _ h => curlR_mem_tsd h)]

theorem norm_curlR_of_mem_tsd {ξ : Freq} {M : Mat3} (hM : M ∈ tsd ξ) :
    ‖curlR ξ M‖ = ‖ξ‖ * ‖M‖ := by
  have h := lagrange ξ M
  rw [divR_eq_zero_of_mem_tsd hM, norm_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 (by rw [mul_pow]; linarith)

/-- **Key fibre estimate** (exact form): `|ξ| ‖P_ξ A‖ = ‖P_ξ (curl_ξ A)‖ ≤ ‖curl_ξ A‖`. -/
theorem norm_freq_mul_norm_proj (ξ : Freq) (A : Mat3) :
    ‖ξ‖ * ‖(tsd ξ).starProjection A‖ = ‖(tsd ξ).starProjection (curlSym ξ A)‖ := by
  rw [proj_curlSym, norm_curlSym, norm_curlR_of_mem_tsd ((tsd ξ).starProjection_apply_mem A)]

theorem norm_freq_mul_norm_proj_le (ξ : Freq) (A : Mat3) :
    ‖ξ‖ * ‖(tsd ξ).starProjection A‖ ≤ ‖curlSym ξ A‖ := by
  rw [norm_freq_mul_norm_proj]; exact (tsd ξ).norm_starProjection_apply_le _

theorem norm_curlSym_le (ξ : Freq) (A : Mat3) : ‖curlSym ξ A‖ ≤ ‖ξ‖ * ‖A‖ := by
  rw [norm_curlSym]
  have h := lagrange ξ A
  have h2 : ‖curlR ξ A‖ ^ 2 ≤ (‖ξ‖ * ‖A‖) ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg ‖divR ξ A‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- `c ξᵀ` is killed by the TSD projection. -/
theorem proj_outer (ξ : Freq) (c : Vec3) : (tsd ξ).starProjection (outer c ξ) = 0 := by
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact (Submodule.mem_orthogonal' _ _).2 fun M hM => inner_outer_tsd hM c

end Torus

section Periodic

open HilbertComplex2 Constraints

/-- The frequency lattice `ℤ³`. -/
abbrev Z3 := Fin 3 → ℤ

/-- The angular frequency `2π k` of the mode `e^{2πi k·x}` on `𝕋³ = ℝ³/ℤ³`. -/
def freq (k : Z3) : Freq := WithLp.toLp 2 fun j => 2 * Real.pi * k j

/-- Fourier coefficients of vector fields. -/
abbrev L2V := L2 Z3 Vec3
/-- Fourier coefficients of matrix fields. -/
abbrev L2M := L2 Z3 Mat3

/-- The divergence symbol `M ↦ i M ξ`. -/
def divSym (ξ : Freq) : Mat3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => vec fun a => Complex.I * ∑ b, M (a, b) * ξ b
      map_add' := fun M N => by ext a; simp [Finset.sum_add_distrib, add_mul, mul_add]
      map_smul' := fun r M => by
        ext a; simp [Complex.real_smul, Finset.mul_sum]; congr 1; ext b; ring }

theorem divSym_apply (ξ : Freq) (M : Mat3) (a : Fin 3) :
    divSym ξ M a = Complex.I * ∑ b, M (a, b) * ξ b := rfl

theorem norm_divSym (ξ : Freq) (M : Mat3) : ‖divSym ξ M‖ = ‖divR ξ M‖ := by
  have : divSym ξ M = (Complex.I : ℂ) • divR ξ M := by ext a; simp [divSym_apply, divR_apply]
  rw [this, norm_smul, Complex.norm_I, one_mul]

/-- `grad* = -div` fibrewise. -/
theorem adjoint_gradSym (ξ : Freq) : ContinuousLinearMap.adjoint (gradSym ξ) = -divSym ξ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun M u => ?_).symm
  simp only [_root_.neg_apply, inner_neg_left, inner_vec, inner_mat, divSym_apply,
    gradSym_apply, Fin.sum_univ_three]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The periodic gradient `H¹(𝕋³; V) → L²(𝕋³; M)` on the Fourier side. -/
def gradT : L2V →ₗ.[ℝ] L2M := mulOp fun k => gradSym (freq k)
/-- The periodic row-wise curl on the Fourier side. -/
def curlT : L2M →ₗ.[ℝ] L2M := mulOp fun k => curlSym (freq k)
/-- `H(curl; M)`. -/
def Hcurl : Submodule ℝ L2M := mulDomain fun k => curlSym (freq k)
/-- `H(div; M)` (row-wise divergence). -/
def Hdiv : Submodule ℝ L2M := mulDomain fun k => divSym (freq k)
/-- `H¹(M)`: `(|ξ_k| A_k)_k ∈ ℓ²`. -/
def H1M : Submodule ℝ L2M := mulDomain fun k => ‖freq k‖ • ContinuousLinearMap.id ℝ Mat3
/-- `L²(TSD)`: symmetric, trace-free, divergence-free matrix fields. -/
def L2TSD : Submodule ℝ L2M := fibreSub fun k => tsd (freq k)

instance : L2TSD.HasOrthogonalProjection :=
  inferInstanceAs (fibreSub fun k => tsd (freq k)).HasOrthogonalProjection

theorem curlT_domain : curlT.domain = Hcurl := rfl

/-- `curl* = curl` on the torus. -/
theorem adjoint_curlT : curlT† = curlT := by
  rw [curlT, adjoint_mulOp]; simp only [adjoint_curlSym]

/-- `grad* = -div` with domain `H(div)`. -/
theorem adjoint_gradT : gradT† = mulOp fun k => -divSym (freq k) := by
  rw [gradT, adjoint_mulOp]; simp only [adjoint_gradSym]

theorem adjoint_gradT_domain : gradT†.domain = Hdiv := by
  rw [adjoint_gradT]
  ext A
  change Memℓp _ 2 ↔ Memℓp _ 2
  rw [← memℓp_norm_iff, ← memℓp_norm_iff (f := fun k => divSym (freq k) (A k))]
  simp only [_root_.neg_apply, norm_neg]

/-- **The periodic matrix complex** `H¹(V) --grad--> H(curl; M) --curl--> L²(M)` on `𝕋³`. -/
def periodicComplex : HilbertComplex2 L2V L2M L2M where
  d0 := gradT
  d1 := curlT
  dense0 := dense_mulDomain _
  dense1 := dense_mulDomain _
  closed0 := isClosed_mulOp _
  closed1 := isClosed_mulOp _
  map_mem x := by
    change Memℓp _ 2
    convert (zero_memℓp : Memℓp (0 : Z3 → Mat3) 2) using 1
    funext k
    exact curlSym_gradSym _ _
  comp_zero x := by
    refine lp.ext (funext fun k => ?_)
    rw [lp.coeFn_zero]
    exact curlSym_gradSym _ _

/-- `P_TSD` acts fibrewise. -/
theorem projTSD_apply (A : L2M) (k : Z3) :
    L2TSD.starProjection A k = (tsd (freq k)).starProjection (A k) :=
  starProjection_fibreSub_apply _ A k

/-- `P_TSD H(curl) ⊆ H(curl)`, with `curl P_TSD = P_TSD curl`. -/
theorem projTSD_mem_Hcurl {A : L2M} (hA : A ∈ Hcurl) : L2TSD.starProjection A ∈ Hcurl := by
  change Memℓp _ 2
  refine Memℓp.mono' hA fun k => ?_
  rw [projTSD_apply, ← proj_curlSym]
  exact Submodule.norm_starProjection_apply_le _ _

/-- `P_TSD H(curl) ⊆ H¹`. -/
theorem projTSD_mem_H1 {A : L2M} (hA : A ∈ Hcurl) : L2TSD.starProjection A ∈ H1M := by
  change Memℓp _ 2
  refine Memℓp.mono' hA fun k => ?_
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, norm_smul, norm_norm,
    projTSD_apply]
  exact norm_freq_mul_norm_proj_le _ _

/-- `curl P_TSD = P_TSD curl` on `H(curl)`. -/
theorem curlT_projTSD (A : curlT.domain) :
    curlT ⟨L2TSD.starProjection A, projTSD_mem_Hcurl A.2⟩ = L2TSD.starProjection (curlT A) :=
  lp.ext (funext fun k => by
    change curlSym (freq k) (L2TSD.starProjection A k) = _
    rw [projTSD_apply, projTSD_apply, ← proj_curlSym]; rfl)

/-- The `H¹` estimate `‖|ξ| P_TSD A‖_{ℓ²} ≤ ‖curl A‖_{ℓ²}`. -/
theorem norm_H1_projTSD_le (A : curlT.domain) :
    ‖mulOp (fun k => ‖freq k‖ • ContinuousLinearMap.id ℝ Mat3)
      ⟨L2TSD.starProjection A, projTSD_mem_H1 A.2⟩‖ ≤ ‖curlT A‖ :=
  lp.norm_mono (by norm_num) fun k => by
    rw [mulOp_apply]
    change ‖‖freq k‖ • L2TSD.starProjection A k‖ ≤ ‖curlSym (freq k) ((A : L2M) k)‖
    rw [norm_smul, norm_norm, projTSD_apply]
    exact norm_freq_mul_norm_proj_le _ _

/-- `H¹ ⊆ H(curl)`. -/
theorem H1M_le_Hcurl : H1M ≤ Hcurl := fun A hA => by
  change Memℓp _ 2
  refine Memℓp.mono' hA fun k => ?_
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, norm_smul, norm_norm]
  exact norm_curlSym_le _ _

theorem L2TSD_le_Hdiv : L2TSD ≤ Hdiv := fun A hA => by
  change Memℓp _ 2
  convert (zero_memℓp : Memℓp (0 : Z3 → Vec3) 2) using 1
  funext k
  ext a
  simp [divSym_apply, (hA k).2.2 a]

/-- `P_TSD (H(curl) ∩ H(div)) ⊆ H(curl) ∩ H(div)`. -/
theorem projTSD_mem_Hcurl_Hdiv {A : L2M} (hA : A ∈ Hcurl ⊓ Hdiv) :
    L2TSD.starProjection A ∈ Hcurl ⊓ Hdiv :=
  ⟨projTSD_mem_Hcurl hA.1, L2TSD_le_Hdiv (L2TSD.starProjection_apply_mem A)⟩

/-- `L²(TSD) ⊆ ker div` (`hS1` of `prop_4_17`). -/
theorem L2TSD_le_ker : L2TSD ≤ periodicComplex.d0†.ker := by
  intro A hA
  change A ∈ gradT†.ker
  have hdom : A ∈ gradT†.domain := adjoint_gradT_domain ▸ L2TSD_le_Hdiv hA
  refine LinearPMap.mem_ker_iff.2 ⟨⟨A, hdom⟩, rfl, lp.ext (funext fun k => ?_)⟩
  have h := adjoint_mulOp_apply (fun k => gradSym (freq k)) ⟨A, hdom⟩ k
  rw [adjoint_gradSym] at h
  rw [lp.coeFn_zero, Pi.zero_apply]
  refine h.trans ?_
  ext a
  simp [divSym_apply, (hA k).2.2 a]

/-- `curl` maps `H(curl) ∩ L²(TSD)` into `L²(TSD)` (`hd1` of `prop_4_17`; Lemma 3.5). -/
theorem curlT_mem_L2TSD (u : periodicComplex.d1.domain) (hu : (u : L2M) ∈ L2TSD) :
    periodicComplex.d1 u ∈ L2TSD := fun k => curlSym_mem_tsd (hu k)

/-- `curl* = curl` maps `L²(TSD)` into itself (`hd1s` of `prop_4_17`). -/
theorem adjoint_curlT_mem_L2TSD (ρ : periodicComplex.d1†.domain) (hρ : (ρ : L2M) ∈ L2TSD) :
    periodicComplex.d1† ρ ∈ L2TSD := fun k => by
  have h := adjoint_mulOp_apply (fun k => curlSym (freq k)) ρ k
  rw [adjoint_curlSym] at h
  change _ ∈ tsd (freq k)
  exact h ▸ curlSym_mem_tsd (hρ k)

/-- **The projection hypothesis holds on `𝕋³`** (`hPD` of `prop_4_17`):
`P_K D(L) ⊆ D(L)` for `K = {0} × L²(TSD) × L²(TSD)`, where
`D(L) = H¹(V) × (H(curl) ∩ H(div)) × H(curl)`.

See [QuennevilleBelair2015, §4.10, Prop 4.17] (first itemized hypothesis of Thm 4.4/4.5). -/
theorem projKc_mem_domL : ∀ x ∈ periodicComplex.domL,
    projKc L2V L2TSD L2TSD x ∈ periodicComplex.domL := by
  intro x hx
  rw [mem_domL] at hx ⊢
  rw [tot_projKc]
  refine ⟨periodicComplex.d0.domain.zero_mem, ⟨projTSD_mem_Hcurl hx.2.1.1, ?_⟩, ?_⟩
  · exact (LinearPMap.mem_ker_iff.1 (L2TSD_le_ker (L2TSD.starProjection_apply_mem _))).elim
      fun y hy => hy.1 ▸ y.2
  · have h : (tot L2V L2M L2M x).2.2 ∈ curlT.domain := by
      have := hx.2.2; change _ ∈ curlT†.domain at this; rwa [adjoint_curlT] at this
    change _ ∈ curlT†.domain
    rw [adjoint_curlT]
    exact projTSD_mem_Hcurl h

/-- **Thesis Prop 4.17 on `𝕋³`, unconditional.** For the periodic matrix complex
`H¹(V) → H(curl; M) → L²(M)` and the Hodge wave (4.14) (`ξ' = -L ξ`), any strong solution with
data `(0, E₀, B₀)`, `E₀, B₀ ∈ L²(TSD)`, keeps `σ ≡ 0` and `E, B ∈ L²(TSD)` for all
`t ∈ [0, T]`, and `(E, B)` solves the reduced system (4.15). No projection or density
hypothesis is assumed: they are proved (`projKc_mem_domL`) or unnecessary (`prop_4_17`).

Correction: the thesis' "conjecture" `P_{L²(TSD)} H(curl) ⊆ H(curl)` (and its `H(div)`
variant) is a theorem on `𝕋³`; the bounded-domain case remains open here.

See [QuennevilleBelair2015, §4.10, Prop 4.17]; cf. [ACBY1997]. -/
theorem prop_4_17_torus {T : ℝ} {E₀ B₀ : L2M} {U : ℝ → Tot L2V L2M L2M} (hE₀ : E₀ ∈ L2TSD)
    (hB₀ : B₀ ∈ L2TSD) (hU : IsStrongSolution (-periodicComplex.waveOp) T (ini L2V E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc L2V L2TSD L2TSD) ∧
      IsReducedSolution periodicComplex T E₀ B₀ (fun t => (tot L2V L2M L2M (U t)).2.1)
        (fun t => (tot L2V L2M L2M (U t)).2.2) :=
  prop_4_17 L2TSD_le_ker projKc_mem_domL curlT_mem_L2TSD adjoint_curlT_mem_L2TSD hE₀ hB₀ hU

/-- Group form of `prop_4_17_torus`: given a Stone group for `-L` (the existence input,
`Feec.UnitaryGroupGenerator`), every orbit starting in `D(L) ∩ K` stays in
`K = {0} × L²(TSD) × L²(TSD)` for `t ≥ 0`.

See [QuennevilleBelair2015, Prop 4.17 and Thm 4.3]; cf. [Pazy1983, §1.10]. -/
theorem prop_4_17_torus_group (G : UnitaryGroupGenerator (-periodicComplex.waveOp)) {t : ℝ}
    (ht : 0 ≤ t) {x : Tot L2V L2M L2M} (hx : x ∈ periodicComplex.domL)
    (hxK : x ∈ Kc L2V L2TSD L2TSD) : G.S t x ∈ Kc L2V L2TSD L2TSD :=
  Kc_propagate L2TSD_le_ker projKc_mem_domL curlT_mem_L2TSD adjoint_curlT_mem_L2TSD
    (isStrongSolution_orbit G t ⟨x, hx⟩) hxK t ⟨ht, le_rfl⟩

theorem curlSym_outer (ξ : Freq) (c : Vec3) : curlSym ξ (outer c ξ) = 0 := by
  have : curlR ξ (outer c ξ) = 0 := by
    ext ⟨a, b⟩; fin_cases b <;> simp [curlR_apply, outer, cross] <;> ring
  rw [curlSym_apply, this, _root_.map_zero]

/-- **The review's counterexample is orthogonal to `L²(TSD)`.** If every Fourier coefficient
of `A` has the gradient form `c_k ξ_kᵀ`, e.g. `A = e₁ (∇f)ᵀ` (`Â(k) = i f̂(k) e₁ ξ_kᵀ`), then
`P_TSD A = 0`. So `A ∈ H(curl)` (`mem_Hcurl_of_outer`) does not refute
`P_TSD H(curl) ⊆ H(curl)`: the review's computation concerns `dev sym A`, which is the pointwise
projection onto symmetric trace-free matrices, not `P_TSD` (which also imposes `div = 0`). -/
theorem projTSD_eq_zero_of_outer {A : L2M} (c : Z3 → Vec3)
    (hA : ∀ k, A k = outer (c k) (freq k)) : L2TSD.starProjection A = 0 :=
  lp.ext (funext fun k => by rw [projTSD_apply, hA, proj_outer]; rfl)

/-- Such fields are curl-free, so lie in `H(curl)`. -/
theorem mem_Hcurl_of_outer {A : L2M} (c : Z3 → Vec3) (hA : ∀ k, A k = outer (c k) (freq k)) :
    A ∈ Hcurl := by
  change Memℓp _ 2
  convert (zero_memℓp : Memℓp (0 : Z3 → Mat3) 2) using 1
  funext k
  rw [hA, curlSym_outer]; rfl

end Periodic

section Real

/-- self-adjoint maps commute with projections onto invariant subspaces -/
theorem starProjection_comm_of_selfAdj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (T : E →L[ℝ] E)
    (hT : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hK : ∀ x ∈ K, T x ∈ K) (x : E) :
    K.starProjection (T x) = T (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hK _ (K.starProjection_apply_mem x)) fun w hw => ?_
  rw [← _root_.map_sub, hT, K.starProjection_inner_eq_zero x _ (hK w hw)]

/-- Entrywise complex conjugation of matrices. -/
def conjM : Mat3 →L[ℝ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => mat fun a b => (starRingEnd ℂ) (M (a, b))
      map_add' := fun M N => by ext ⟨a, b⟩; simp
      map_smul' := fun r M => by ext ⟨a, b⟩; simp [Complex.real_smul] }

theorem conjM_apply (M : Mat3) (a b : Fin 3) : conjM M (a, b) = (starRingEnd ℂ) (M (a, b)) := rfl

theorem inner_conjM (A B : Mat3) : ⟪conjM A, B⟫ = ⟪A, conjM B⟫ := by
  simp only [inner_mat, conjM_apply, Complex.conj_re, Complex.conj_im]
  congr 1; ext a; congr 1; ext b; ring

theorem tsd_neg (ξ : Freq) : tsd (-ξ) = tsd ξ := by
  ext M
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun a => ?_))
  simp only [PiLp.neg_apply, Complex.ofReal_neg, mul_neg, Finset.sum_neg_distrib, neg_eq_zero]

theorem conjM_mem_tsd {ξ : Freq} {M : Mat3} (hM : M ∈ tsd ξ) : conjM M ∈ tsd ξ := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun a b => by simp [conjM_apply, h1 a b], ?_, fun a => ?_⟩
  · simpa [conjM_apply] using congrArg (starRingEnd ℂ) h2
  · simpa [conjM_apply] using congrArg (starRingEnd ℂ) (h3 a)

theorem freq_neg (k : Z3) : freq (-k) = -freq k := by
  ext j; simp [freq]

/-- Fourier coefficients of a real-valued matrix field: `Â(-k) = conj Â(k)`. -/
def IsReal (A : L2M) : Prop := ∀ k, A (-k) = conjM (A k)

/-- `P_TSD` maps real fields to real fields. -/
theorem isReal_projTSD {A : L2M} (hA : IsReal A) : IsReal (L2TSD.starProjection A) := fun k => by
  rw [projTSD_apply, projTSD_apply, hA, freq_neg, tsd_neg]
  exact starProjection_comm_of_selfAdj _ conjM inner_conjM (fun _ h => conjM_mem_tsd h) _

/-- `curl` maps real fields to real fields. -/
theorem isReal_curlT (A : curlT.domain) (hA : IsReal A) : IsReal (curlT A) := fun k => by
  change curlSym (freq (-k)) ((A : L2M) (-k)) = conjM (curlSym (freq k) ((A : L2M) k))
  rw [hA, freq_neg]
  ext ⟨a, b⟩
  fin_cases b <;> simp [curlSym_apply, jM_apply, curlR_apply, cross, conjM_apply] <;> ring

end Real

section Swap

variable {ι P : Type*} [Fintype P]

/-- The swapped sequence is square-summable. -/
theorem swap_memℓp (f : PiLp 2 (fun _ : P => lp (fun _ : ι => ℂ) 2)) :
    Memℓp (fun k => (WithLp.toLp 2 fun p => (f p : ι → ℂ) k : EuclideanSpace ℂ P)) 2 := by
  refine memℓp_gen ?_
  have : ∀ k, ‖(WithLp.toLp 2 fun p => (f p : ι → ℂ) k : EuclideanSpace ℂ P)‖ ^ (2 : ℝ≥0∞).toReal =
      ∑ p, ‖(f p : ι → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal := by
    intro k
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, EuclideanSpace.norm_sq_eq]
  simp_rw [this]
  exact summable_sum fun p _ => (lp.memℓp (f p)).summable (by norm_num)

/-- Components of an `ℓ²(ι; ℂᴾ)` sequence are square-summable. -/
theorem swap_inv_memℓp (g : lp (fun _ : ι => EuclideanSpace ℂ P) 2) (p : P) :
    Memℓp (fun k => (g k : EuclideanSpace ℂ P) p) 2 :=
  (lp.memℓp g).mono' fun k => PiLp.norm_apply_le (g k) p

/-- Exchanging the finite `ℓ²` sum over components with the `ℓ²` sum over frequencies. -/
def swapL2 : PiLp 2 (fun _ : P => lp (fun _ : ι => ℂ) 2) ≃ₗᵢ[ℂ]
    lp (fun _ : ι => EuclideanSpace ℂ P) 2 where
  toFun f := ⟨fun k => WithLp.toLp 2 fun p => (f p : ι → ℂ) k, swap_memℓp f⟩
  map_add' f g := by ext k p; simp; rfl
  map_smul' c f := by ext k p; simp
  invFun g := WithLp.toLp 2 fun p => ⟨fun k => (g k : EuclideanSpace ℂ P) p, swap_inv_memℓp g p⟩
  left_inv f := by ext p k; rfl
  right_inv g := by ext k p; rfl
  norm_map' f := by
    have h1 := lp.hasSum_norm (p := 2) (by norm_num)
      (⟨fun k => WithLp.toLp 2 fun p => (f p : ι → ℂ) k, swap_memℓp f⟩ :
        lp (fun _ : ι => EuclideanSpace ℂ P) 2)
    have h2 : HasSum (fun k => ∑ p, ‖(f p : ι → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal)
        (∑ p, ‖f p‖ ^ (2 : ℝ≥0∞).toReal) :=
      hasSum_sum fun p _ => lp.hasSum_norm (by norm_num) (f p)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2
    have h3 := h1.unique (by
      convert h2 using 2 with k
      rw [EuclideanSpace.norm_sq_eq])
    rw [← PiLp.norm_sq_eq_of_L2] at h3
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

@[simp] theorem swapL2_apply (f : PiLp 2 (fun _ : P => lp (fun _ : ι => ℂ) 2)) (k : ι) (p : P) :
    swapL2 f k p = (f p : ι → ℂ) k := rfl

end Swap

/-- The normalised (probability) Haar measure on `ℝ/ℤ`, the measure used by
`Mathlib.Analysis.Fourier.AddCircleMulti` for `UnitAddTorus.mFourierBasis`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- **Fourier coefficients of `L²` fields on `𝕋³`**: componentwise
`UnitAddTorus.mFourierBasis.repr` (Parseval), then `swapL2`; a linear isometric equivalence
`L²(𝕋³; ℂᴾ) ≃ₗᵢ ℓ²(ℤ³; ℂᴾ)`. -/
def fieldFourier (P : Type*) [Fintype P] :
    PiLp 2 (fun _ : P => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))) ≃ₗᵢ[ℂ]
      lp (fun _ : (Fin 3 → ℤ) => EuclideanSpace ℂ P) 2 :=
  (LinearIsometryEquiv.piLpCongrRight 2 fun _ => UnitAddTorus.mFourierBasis.repr).trans swapL2

theorem fieldFourier_apply (P : Type*) [Fintype P]
    (f : PiLp 2 (fun _ : P => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))))
    (k : Fin 3 → ℤ) (p : P) :
    fieldFourier P f k p = UnitAddTorus.mFourierCoeff (f p) k := by
  simp [fieldFourier, LinearIsometryEquiv.piLpCongrRight_apply, UnitAddTorus.mFourierBasis_repr]

/-- Vector fields: `L²(𝕋³; ℂ³) ≃ₗᵢ L2V`, the model of `W0`. -/
def vectorFourier :
    PiLp 2 (fun _ : Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))) ≃ₗᵢ[ℂ] L2V :=
  fieldFourier (Fin 3)

/-- Matrix fields: `L²(𝕋³; ℂ³ˣ³) ≃ₗᵢ L2M`, the model of `W1 = W2`. -/
def matrixFourier :
    PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))) ≃ₗᵢ[ℂ]
      L2M :=
  fieldFourier (Fin 3 × Fin 3)

/-- `matrixFourier f k (a, b)` is the `k`-th Fourier coefficient of the entry `f_{ab}`. -/
theorem matrixFourier_apply
    (f : PiLp 2 (fun _ : Fin 3 × Fin 3 => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))))
    (k : Z3) (a b : Fin 3) :
    matrixFourier f k (a, b) = UnitAddTorus.mFourierCoeff (f (a, b)) k :=
  fieldFourier_apply _ f k (a, b)

end Feec.Torus
