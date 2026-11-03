module

public import Feec.Fourier.ClosedRange
public import Feec.Fourier.Reality
public import Feec.Algebra.ExteriorFibre
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The symbol of the exterior derivative in any dimension

Differential `k`-forms on `ℝᵈ` or `𝕋ᵈ` with constant coefficients are, at a frequency `ξ`, elements
of `Λᵏ = 𝕜^{#k-subsets of d}` (coefficients of `dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`, `s₁ < ⋯ < s_k`). The
exterior derivative has symbol `i ξ ∧ ·`, built from the **Koszul differential**
`(κ_ξ ω)_s = Σ_{j ∈ s} ε(j, s) ξ_j ω_{s ∖ j}` with the sign `ε(j, s) = (-1)^{#{l ∈ s | l < j}}`,
and its adjoint is the contraction `(ι_ξ ω)_s = Σ_{j ∉ s} ε(j, s) ξ_j ω_{s ∪ j}`.

## Main results

* `koszul_koszul`: `κ_ξ κ_ξ = 0`.
* `koszul_contr_add_contr_koszul`: the **Cartan identity** `κ_ξ ι_ξ + ι_ξ κ_ξ = |ξ|²`.
* `inner_koszul`: `⟪κ_ξ ω, η⟫ = ⟪ω, ι_ξ η⟫` (real `ξ`).
* `norm_koszul_sq_add_norm_contr_sq`: `‖κ_ξ ω‖² + ‖ι_ξ ω‖² = |ξ|² ‖ω‖²`.
* The graded operators `koszulDeg k ξ : Λᵏ →L Λᵏ⁺¹`, with `koszulDeg_comp` (`κ κ = 0`),
  `adjoint_koszulDeg` (adjoint = contraction) and the **fibre gap**
  `mul_norm_le_norm_koszulDeg`: `|ξ| ‖v‖ ≤ ‖κ_ξ v‖` for `v ⊥ N(κ_ξ)` (exactness for `ξ ≠ 0` with
  Poincaré constant `1/|ξ|`).
* `Exterior.deRham d`: the de Rham family `ξ ↦ (i κ_ξ)` of fibre complexes on
  `ComplexShape.up ℕ`, with `deRham_gap` and `deRham_isHomogeneous`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (the Koszul complex and differential forms)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (the Koszul complex and
  differential forms)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (the de Rham complex as a Hilbert complex)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace Feec.Fourier.Exterior

variable {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d] [LinearOrder d]

open ExteriorFibre (sgn sgn_insert_self wedge interior)

omit [Fintype d] in
theorem conj_sgn (j : d) (s : Finset d) : conj (sgn j s : 𝕜) = sgn j s := by
  simp [sgn]

/-- Reindexing pairs `(s, j)` with `j ∈ s` by `(t, j) = (s ∖ j, j)` with `j ∉ t`. -/
theorem sum_sum_mem_eq (F : Finset d → d → 𝕜) :
    ∑ s, ∑ j ∈ s, F s j = ∑ t, ∑ j ∈ tᶜ, F (insert j t) j := by
  have h1 : ∑ s, ∑ j ∈ s, F s j = ∑ j, ∑ s with j ∈ s, F s j := by
    rw [sum_comm' (t' := univ) (s' := fun j => {s | j ∈ s})]
    intro s j; simp
  have h2 : ∑ t, ∑ j ∈ tᶜ, F (insert j t) j = ∑ j, ∑ t with j ∉ t, F (insert j t) j := by
    rw [sum_comm' (t' := univ) (s' := fun j => {t | j ∉ t})]
    intro t j; simp
  rw [h1, h2]
  refine sum_congr rfl fun j _ => ?_
  refine sum_nbij' (fun s => s.erase j) (insert j) (fun s _ => by simp)
    (fun t _ => by simp) (fun s hs => insert_erase (mem_filter.1 hs).2)
    (fun t ht => erase_insert (mem_filter.1 ht).2) fun s hs => ?_
  rw [insert_erase (mem_filter.1 hs).2]

/-! ### The Koszul differential and the contraction on the full exterior algebra -/

variable (𝕜 d) in
/-- The full exterior algebra `Λ = ⊕ₖ Λᵏ`, coefficients indexed by all subsets of `d`. -/
abbrev Lam := EuclideanSpace 𝕜 (Finset d)

/-- The Koszul differential `(κ_ξ ω)_s = Σ_{j ∈ s} ε(j, s) ξ_j ω_{s ∖ j}`: exterior multiplication
`ξ ∧ ·` by the real covector `ξ`, as a continuous linear map on `Λ`. -/
def koszul (ξ : EuclideanSpace ℝ d) : Lam 𝕜 d →L[𝕜] Lam 𝕜 d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => WithLp.toLp 2 (wedge (fun j => (ξ j : 𝕜)) ω)
      map_add' := fun ω η => by simp [ExteriorFibre.wedge_add]
      map_smul' := fun a ω => by simp [ExteriorFibre.wedge_smul] }

/-- The contraction `(ι_ξ ω)_s = Σ_{j ∉ s} ε(j, s) ξ_j ω_{s ∪ j}` with `ξ`, as a continuous linear
map on `Λ`. -/
def contr (ξ : EuclideanSpace ℝ d) : Lam 𝕜 d →L[𝕜] Lam 𝕜 d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => WithLp.toLp 2 (interior (fun j => (ξ j : 𝕜)) ω)
      map_add' := fun ω η => by simp [ExteriorFibre.interior_add]
      map_smul' := fun a ω => by simp [ExteriorFibre.interior_smul] }

theorem koszul_apply (ξ : EuclideanSpace ℝ d) (ω : Lam 𝕜 d) (s : Finset d) :
    koszul ξ ω s = ∑ j ∈ s, sgn j s * (ξ j : 𝕜) * ω (s.erase j) := rfl

theorem contr_apply (ξ : EuclideanSpace ℝ d) (ω : Lam 𝕜 d) (s : Finset d) :
    contr ξ ω s = ∑ j ∈ sᶜ, sgn j s * (ξ j : 𝕜) * ω (insert j s) := rfl

/-- **`κ_ξ κ_ξ = 0`** (`ExteriorFibre.wedge_wedge_self`). -/
theorem koszul_koszul (ξ : EuclideanSpace ℝ d) (ω : Lam 𝕜 d) : koszul ξ (koszul ξ ω) = 0 := by
  ext s
  exact congrFun (ExteriorFibre.wedge_wedge_self _ _) s

/-- **The Cartan identity** `κ_ξ ι_ξ + ι_ξ κ_ξ = |ξ|²` (`ExteriorFibre.wedge_interior_add_interior_wedge`). -/
theorem koszul_contr_add_contr_koszul (ξ : EuclideanSpace ℝ d) (ω : Lam 𝕜 d) :
    koszul ξ (contr ξ ω) + contr ξ (koszul ξ ω) = ((∑ j, ξ j ^ 2 : ℝ) : 𝕜) • ω := by
  ext s
  convert congrFun (ExteriorFibre.wedge_interior_add_interior_wedge (fun j => (ξ j : 𝕜))
    (fun j => (ξ j : 𝕜)) ω) s using 1
  · rfl
  · simp [sq]

/-- **The contraction is the adjoint of the Koszul differential** (real `ξ`). -/
theorem inner_koszul (ξ : EuclideanSpace ℝ d) (ω η : Lam 𝕜 d) :
    ⟪koszul ξ ω, η⟫_𝕜 = ⟪ω, contr ξ η⟫_𝕜 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, koszul_apply, contr_apply, map_sum, map_mul,
    conj_sgn, RCLike.conj_ofReal, sum_mul, mul_sum]
  rw [sum_sum_mem_eq]
  refine sum_congr rfl fun t _ => sum_congr rfl fun j hj => ?_
  rw [sgn_insert_self, erase_insert (mem_compl.1 hj)]
  ring

theorem norm_koszul_sq_add_norm_contr_sq (ξ : EuclideanSpace ℝ d) (ω : Lam 𝕜 d) :
    ‖koszul ξ ω‖ ^ 2 + ‖contr ξ ω‖ ^ 2 = (∑ j, ξ j ^ 2) * ‖ω‖ ^ 2 := by
  have h := congrArg (fun x => RCLike.re ⟪x, ω⟫_𝕜) (koszul_contr_add_contr_koszul ξ ω)
  simp only [inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add] at h
  have h1 : ⟪koszul ξ (contr ξ ω), ω⟫_𝕜 = ⟪contr ξ ω, contr ξ ω⟫_𝕜 := inner_koszul ξ _ _
  have h2 : ⟪contr ξ (koszul ξ ω), ω⟫_𝕜 = ⟪koszul ξ ω, koszul ξ ω⟫_𝕜 := by
    rw [← inner_conj_symm, ← inner_koszul, inner_conj_symm]
  rw [h1, h2, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, ← RCLike.ofReal_pow, ← RCLike.ofReal_pow,
    RCLike.ofReal_re, RCLike.ofReal_re, ← RCLike.ofReal_mul, RCLike.ofReal_re] at h
  linarith

/-! ### Degrees -/

variable (𝕜 d) in
/-- The `k`-forms at one frequency: coefficients on the `k`-element subsets of `d`. -/
abbrev Form (k : ℕ) := EuclideanSpace 𝕜 {s : Finset d // #s = k}

omit [LinearOrder d] in
open Classical in
theorem sum_dite_card {M : Type*} [AddCommMonoid M] (k : ℕ) (g : {s : Finset d // #s = k} → M) :
    ∑ s : Finset d, (if h : #s = k then g ⟨s, h⟩ else 0) = ∑ t, g t := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun s : Finset d => #s = k)]
  have h1 : ∀ t : {s : Finset d // #s = k},
      (if h : #(t : Finset d) = k then g ⟨t, h⟩ else 0) = g t := fun t => by simp [t.2]
  have h2 : ∀ t : {s : Finset d // ¬ #s = k},
      (if h : #(t : Finset d) = k then g ⟨t, h⟩ else 0) = 0 := fun t => by simp [t.2]
  simp only [h1, h2, sum_const_zero, add_zero]

open Classical in
/-- Extension by zero `Λᵏ → Λ`. -/
def ext (k : ℕ) : Form 𝕜 d k →ₗᵢ[𝕜] Lam 𝕜 d where
  toFun ω := WithLp.toLp 2 fun s => if h : #s = k then ω ⟨s, h⟩ else 0
  map_add' ω η := by
    ext s; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' a ω := by
    ext s; simp only [PiLp.smul_apply, RingHom.id_apply]; split_ifs <;> simp
  norm_map' ω := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← sum_dite_card k fun t => ‖ω t‖ ^ 2]
    refine sum_congr rfl fun s _ => ?_
    split_ifs <;> simp


omit [LinearOrder d] in
theorem sum_sq_eq_norm_sq (ξ : EuclideanSpace ℝ d) : ∑ j, ξ j ^ 2 = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp

omit [LinearOrder d] in
theorem ext_apply (k : ℕ) (ω : Form 𝕜 d k) {s : Finset d} (h : #s = k) :
    ext k ω s = ω ⟨s, h⟩ := by
  simp [ext, h]

omit [LinearOrder d] in
theorem ext_apply_of_ne (k : ℕ) (ω : Form 𝕜 d k) {s : Finset d} (h : #s ≠ k) :
    ext k ω s = 0 := by
  simp [ext, h]

/-- Restriction `Λ → Λᵏ` to the coefficients of degree `k`. -/
def res (k : ℕ) : Lam 𝕜 d →L[𝕜] Form 𝕜 d k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => WithLp.toLp 2 fun t => ω t.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [LinearOrder d] in
@[simp] theorem res_apply (k : ℕ) (ω : Lam 𝕜 d) (t : {s : Finset d // #s = k}) :
    res k ω t = ω t.1 := rfl

omit [LinearOrder d] in
theorem ext_res {k : ℕ} {ω : Lam 𝕜 d} (h : ∀ s, #s ≠ k → ω s = 0) : ext k (res k ω) = ω := by
  ext s
  by_cases hs : #s = k
  · rw [ext_apply k _ hs, res_apply]
  · rw [ext_apply_of_ne k _ hs, h s hs]

omit [LinearOrder d] in
theorem inner_ext (k : ℕ) (ω η : Form 𝕜 d k) : ⟪ext k ω, ext k η⟫_𝕜 = ⟪ω, η⟫_𝕜 :=
  (ext k).inner_map_map ω η

theorem koszul_ext_eq_zero (ξ : EuclideanSpace ℝ d) (k : ℕ) (ω : Form 𝕜 d k) {s : Finset d}
    (hs : #s ≠ k + 1) : koszul ξ (ext k ω) s = 0 := by
  rw [koszul_apply]
  refine sum_eq_zero fun j hj => ?_
  rw [ext_apply_of_ne k ω, mul_zero]
  rw [card_erase_of_mem hj]
  have : 1 ≤ #s := card_pos.2 ⟨j, hj⟩
  omega

theorem contr_ext_eq_zero (ξ : EuclideanSpace ℝ d) (k : ℕ) (ω : Form 𝕜 d k) {s : Finset d}
    (hs : #s + 1 ≠ k) : contr ξ (ext k ω) s = 0 := by
  rw [contr_apply]
  refine sum_eq_zero fun j hj => ?_
  rw [ext_apply_of_ne k ω, mul_zero]
  rwa [card_insert_of_notMem (mem_compl.1 hj)]

/-! ### The graded Koszul complex -/

/-- The graded Koszul differential `κ_ξ : Λᵏ → Λᵏ⁺¹`. -/
def koszulDeg (k : ℕ) (ξ : EuclideanSpace ℝ d) : Form 𝕜 d k →L[𝕜] Form 𝕜 d (k + 1) :=
  res (k + 1) ∘L koszul ξ ∘L (ext k).toContinuousLinearMap

/-- The graded contraction `ι_ξ : Λᵏ⁺¹ → Λᵏ`. -/
def contrDeg (k : ℕ) (ξ : EuclideanSpace ℝ d) : Form 𝕜 d (k + 1) →L[𝕜] Form 𝕜 d k :=
  res k ∘L contr ξ ∘L (ext (k + 1)).toContinuousLinearMap

theorem koszulDeg_apply (k : ℕ) (ξ : EuclideanSpace ℝ d) (ω : Form 𝕜 d k) :
    koszulDeg k ξ ω = res (k + 1) (koszul ξ (ext k ω)) := rfl

theorem ext_koszulDeg (k : ℕ) (ξ : EuclideanSpace ℝ d) (ω : Form 𝕜 d k) :
    ext (k + 1) (koszulDeg k ξ ω) = koszul ξ (ext k ω) :=
  ext_res fun _ hs => koszul_ext_eq_zero ξ k ω hs

theorem ext_contrDeg (k : ℕ) (ξ : EuclideanSpace ℝ d) (ω : Form 𝕜 d (k + 1)) :
    ext k (contrDeg k ξ ω) = contr ξ (ext (k + 1) ω) :=
  ext_res fun _ hs => contr_ext_eq_zero ξ (k + 1) ω (by omega)

/-- **`κ_ξ κ_ξ = 0` in every degree.** -/
theorem koszulDeg_comp (k : ℕ) (ξ : EuclideanSpace ℝ d) :
    (koszulDeg (k + 1) ξ).comp (koszulDeg k ξ) = (0 : Form 𝕜 d k →L[𝕜] Form 𝕜 d (k + 1 + 1)) := by
  refine ContinuousLinearMap.ext fun ω => ?_
  rw [ContinuousLinearMap.comp_apply, koszulDeg_apply, ext_koszulDeg, koszul_koszul, map_zero]
  rfl

/-- **The adjoint of the graded Koszul differential is the graded contraction.** -/
theorem adjoint_koszulDeg (k : ℕ) (ξ : EuclideanSpace ℝ d) :
    ContinuousLinearMap.adjoint (koszulDeg k ξ : Form 𝕜 d k →L[𝕜] Form 𝕜 d (k + 1)) =
      contrDeg k ξ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun ω η => ?_).symm
  rw [← inner_ext, ext_contrDeg, ← inner_ext (k + 1), ext_koszulDeg, ← inner_conj_symm,
    ← inner_koszul, inner_conj_symm]

/-- The fibre norm identity: `‖κ_ξ ω‖² + ‖ι_ξ ω‖² = |ξ|² ‖ω‖²` on `k`-forms, with the contraction
taken in the full algebra. -/
theorem norm_koszulDeg_sq_add (k : ℕ) (ξ : EuclideanSpace ℝ d) (ω : Form 𝕜 d k) :
    ‖koszulDeg k ξ ω‖ ^ 2 + ‖contr ξ (ext k ω)‖ ^ 2 = ‖ξ‖ ^ 2 * ‖ω‖ ^ 2 := by
  rw [← (ext (k + 1)).norm_map, ext_koszulDeg, norm_koszul_sq_add_norm_contr_sq,
    sum_sq_eq_norm_sq, (ext k).norm_map]

/-- On forms orthogonal to `N(κ_ξ)` the contraction vanishes (they are orthogonal to `R(κ_ξ)`). -/
theorem contr_ext_eq_zero_of_mem_orthogonal {k : ℕ} {ξ : EuclideanSpace ℝ d} {v : Form 𝕜 d k}
    (hv : v ∈ (LinearMap.ker (koszulDeg (𝕜 := 𝕜) k ξ : Form 𝕜 d k →ₗ[𝕜] Form 𝕜 d (k + 1)))ᗮ) :
    contr ξ (ext k v) = 0 := by
  cases k with
  | zero =>
    ext s
    exact contr_ext_eq_zero ξ 0 v (by omega)
  | succ k =>
    rw [← ext_contrDeg]
    set w := contrDeg k ξ v
    have hw : ⟪koszulDeg k ξ w, v⟫_𝕜 = 0 := by
      refine Submodule.inner_right_of_mem_orthogonal ?_ hv
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      exact congrArg (fun T : Form 𝕜 d k →L[𝕜] _ => T w) (koszulDeg_comp k ξ)
    have hw' : ⟪w, ContinuousLinearMap.adjoint (koszulDeg k ξ) v⟫_𝕜 = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_right]; exact hw
    rw [adjoint_koszulDeg] at hw'
    have : w = 0 := inner_self_eq_zero.1 hw'
    rw [this, map_zero]

/-- **The fibre gap of the Koszul complex**: `‖κ_ξ v‖ = |ξ| ‖v‖` for `v ⊥ N(κ_ξ)`. In particular
`R(κ_ξ)` is closed with Poincaré constant `1/|ξ|` (exactness of the Koszul complex for `ξ ≠ 0`). -/
theorem norm_koszulDeg_of_mem_orthogonal {k : ℕ} {ξ : EuclideanSpace ℝ d} {v : Form 𝕜 d k}
    (hv : v ∈ (LinearMap.ker (koszulDeg (𝕜 := 𝕜) k ξ : Form 𝕜 d k →ₗ[𝕜] Form 𝕜 d (k + 1)))ᗮ) :
    ‖koszulDeg k ξ v‖ = ‖ξ‖ * ‖v‖ := by
  have h := norm_koszulDeg_sq_add k ξ v
  rw [contr_ext_eq_zero_of_mem_orthogonal hv, norm_zero, zero_pow two_ne_zero, add_zero,
    ← mul_pow] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- For `ξ ≠ 0` there are no fibre harmonic forms: `N(κ_ξ) ∩ N(ι_ξ) = 0`. -/
theorem eq_zero_of_koszul_eq_zero_of_contr_eq_zero {k : ℕ} {ξ : EuclideanSpace ℝ d} (hξ : ξ ≠ 0)
    {v : Form 𝕜 d k} (h1 : koszulDeg k ξ v = 0) (h2 : contr ξ (ext k v) = 0) : v = 0 := by
  have h := norm_koszulDeg_sq_add k ξ v
  rw [h1, h2] at h
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  have : ‖v‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 h.symm with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) (norm_ne_zero_iff.2 hξ)
    · exact h
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- The graded Koszul differential depends continuously on the frequency. -/
theorem continuous_koszulDeg (k : ℕ) : Continuous (koszulDeg (𝕜 := 𝕜) (d := d) k) := by
  refine continuous_clm_apply.2 fun ω => ?_
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun t => ?_)
  change Continuous fun ξ : EuclideanSpace ℝ d =>
    ∑ j ∈ t.1, sgn j t.1 * ((ξ j : ℝ) : 𝕜) * ext k ω (t.1.erase j)
  refine continuous_finsetSum _ fun j _ => ?_
  refine (continuous_const.mul ?_).mul continuous_const
  exact RCLike.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)


theorem koszulDeg_smul (k : ℕ) (t : ℝ) (ξ : EuclideanSpace ℝ d) :
    koszulDeg (𝕜 := 𝕜) k (t • ξ) = (t : 𝕜) • koszulDeg k ξ := by
  refine ContinuousLinearMap.ext fun ω => ?_
  ext u
  simp only [koszulDeg_apply, res_apply, koszul_apply, _root_.smul_apply, PiLp.smul_apply,
    smul_eq_mul, mul_sum, RCLike.ofReal_mul]
  refine sum_congr rfl fun j _ => by ring

@[simp] theorem koszulDeg_zero (k : ℕ) : koszulDeg (𝕜 := 𝕜) k (0 : EuclideanSpace ℝ d) = 0 := by
  refine ContinuousLinearMap.ext fun ω => ?_
  ext u
  simp [koszulDeg_apply, koszul_apply]

/-! ### The de Rham family -/

variable (d) in
/-- **The symbol of the de Rham complex** on `ℝᵈ` or `𝕋ᵈ`: `d_ξ = i κ_ξ : Λᵏ → Λᵏ⁺¹` on
`ComplexShape.up ℕ` (`k`-forms in degree `k`, zero spaces above `#d`). -/
def deRham : FibreComplex ℂ (EuclideanSpace ℝ d) (ComplexShape.up ℕ) (Form ℂ d) :=
  FibreComplex.ofSucc (fun k ξ => Complex.I • koszulDeg k ξ)
    (fun k ξ => by
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, koszulDeg_comp,
        smul_zero, smul_zero])
    fun k => (continuous_koszulDeg k).const_smul Complex.I

theorem deRham_m_succ (k : ℕ) (ξ : EuclideanSpace ℝ d) :
    (deRham d).m k (k + 1) ξ = Complex.I • koszulDeg k ξ := by
  simp [deRham]

theorem norm_deRham_apply (k : ℕ) (ξ : EuclideanSpace ℝ d) (v : Form ℂ d k) :
    ‖(deRham d).m k (k + 1) ξ v‖ = ‖koszulDeg k ξ v‖ := by
  rw [deRham_m_succ, _root_.smul_apply, norm_smul, Complex.norm_I, one_mul]

theorem ker_deRham (k : ℕ) (ξ : EuclideanSpace ℝ d) :
    LinearMap.ker ((deRham d).m k (k + 1) ξ : Form ℂ d k →ₗ[ℂ] Form ℂ d (k + 1)) =
      LinearMap.ker (koszulDeg (𝕜 := ℂ) k ξ : Form ℂ d k →ₗ[ℂ] Form ℂ d (k + 1)) := by
  ext v
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, deRham_m_succ, _root_.smul_apply,
    smul_eq_zero, Complex.I_ne_zero, false_or]

theorem adjoint_deRham (k : ℕ) (ξ : EuclideanSpace ℝ d) :
    ContinuousLinearMap.adjoint ((deRham d).m k (k + 1) ξ) = -Complex.I • contrDeg k ξ := by
  rw [deRham_m_succ, map_smulₛₗ, adjoint_koszulDeg, Complex.conj_I]

/-- **The fibre gap of the de Rham symbol**: `‖d_ξ v‖ = |ξ| ‖v‖` for `v ⊥ N(d_ξ)`. -/
theorem norm_deRham_of_mem_orthogonal {k : ℕ} {ξ : EuclideanSpace ℝ d} {v : Form ℂ d k}
    (hv : v ∈ (LinearMap.ker ((deRham d).m k (k + 1) ξ : Form ℂ d k →ₗ[ℂ] Form ℂ d (k + 1)))ᗮ) :
    ‖(deRham d).m k (k + 1) ξ v‖ = ‖ξ‖ * ‖v‖ := by
  rw [norm_deRham_apply]
  rw [ker_deRham] at hv
  exact norm_koszulDeg_of_mem_orthogonal hv

/-- The de Rham symbol is homogeneous of degree `1`. -/
theorem deRham_isHomogeneous (k : ℕ) : (deRham d).IsHomogeneous k (k + 1) 1 := by
  intro t ξ _
  rw [deRham_m_succ, deRham_m_succ, koszulDeg_smul, pow_one, smul_comm]

@[simp] theorem deRham_m_zero (i j : ℕ) : (deRham d).m i j 0 = 0 := by
  by_cases h : i + 1 = j
  · subst h; rw [deRham_m_succ, koszulDeg_zero]; simp
  · rw [(deRham d).shape i j h]; rfl

/-- **No fibre harmonic forms off `ξ = 0`**: `N(d_ξ) ∩ N(d_ξ*) = 0` in every degree. -/
theorem deRham_harmonic_fibre {ξ : EuclideanSpace ℝ d} (hξ : ξ ≠ 0) (k : ℕ) :
    LinearMap.ker ((deRham d).m k ((ComplexShape.up ℕ).next k) ξ :
        Form ℂ d k →ₗ[ℂ] Form ℂ d ((ComplexShape.up ℕ).next k)) ⊓
      LinearMap.ker (ContinuousLinearMap.adjoint ((deRham d).m ((ComplexShape.up ℕ).prev k) k ξ) :
        Form ℂ d k →ₗ[ℂ] Form ℂ d ((ComplexShape.up ℕ).prev k)) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨h1, h2⟩
  rw [Submodule.mem_bot]
  have hn : (ComplexShape.up ℕ).next k = k + 1 := (ComplexShape.up ℕ).next_eq' rfl
  have h1' : koszulDeg k ξ v = 0 := by
    have := (LinearMap.mem_ker.1 h1)
    revert this
    rw [hn]
    intro this
    rw [ContinuousLinearMap.coe_coe, deRham_m_succ, _root_.smul_apply] at this
    exact (smul_eq_zero.1 this).resolve_left Complex.I_ne_zero
  refine eq_zero_of_koszul_eq_zero_of_contr_eq_zero hξ h1' ?_
  cases k with
  | zero => ext s; exact contr_ext_eq_zero ξ 0 v (by omega)
  | succ k =>
    have hp : (ComplexShape.up ℕ).prev (k + 1) = k := (ComplexShape.up ℕ).prev_eq' rfl
    have h2' := LinearMap.mem_ker.1 h2
    revert h2'
    rw [hp]
    intro h2'
    rw [ContinuousLinearMap.coe_coe, adjoint_deRham, _root_.smul_apply] at h2'
    have : contrDeg k ξ v = 0 := (smul_eq_zero.1 h2').resolve_left (by simp)
    rw [← ext_contrDeg, this, map_zero]

/-! ### The de Rham symbol is real -/

theorem koszulDeg_neg_entryConj (k : ℕ) (ξ : EuclideanSpace ℝ d) (v : Form ℂ d k) :
    koszulDeg k (-ξ) (entryConj v) = -entryConj (koszulDeg k ξ v) := by
  ext u
  simp only [koszulDeg_apply, res_apply, koszul_apply, entryConj_apply, PiLp.neg_apply,
    map_sum, map_mul, conj_sgn, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (ext k (entryConj v) : Lam ℂ d) (u.1.erase j) =
      conj ((ext k v : Lam ℂ d) (u.1.erase j)) := by
    by_cases h : #(u.1.erase j) = k
    · rw [ext_apply k _ h, ext_apply k _ h, entryConj_apply]
    · rw [ext_apply_of_ne k _ h, ext_apply_of_ne k _ h, map_zero]
  rw [h1]
  simp

/-- **The de Rham symbol is real**: `d_{-ξ} (conj v) = conj (d_ξ v)`. -/
theorem deRham_neg_entryConj (i j : ℕ) (ξ : EuclideanSpace ℝ d) (v : Form ℂ d i) :
    (deRham d).m i j (-ξ) (entryConj v) = entryConj ((deRham d).m i j ξ v) := by
  by_cases h : i + 1 = j
  · subst h
    rw [deRham_m_succ, deRham_m_succ, _root_.smul_apply, _root_.smul_apply,
      koszulDeg_neg_entryConj, entryConj_smul, Complex.conj_I, smul_neg, neg_smul]
  · rw [(deRham d).shape i j h]
    simp

end Feec.Fourier.Exterior
