module

public import Feec.Fourier.FibreReducing
public import Feec.Fourier.ClosedRange
public import Feec.Algebra.MatrixSymbol
public import Feec.Fourier.Reality

/-!
# The symbol of the row-wise grad–curl matrix complex

The complex `H¹(ℂ³) --grad--> H(curl; ℂ³ˣ³) --curl--> L²(ℂ³ˣ³)` of the matrix Hodge wave
equation (Thesis (4.14)), with the row-wise curl `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`, has at a
frequency `ξ ∈ ℝ³` the symbols `grad_ξ u = i u ξᵀ` and `curl_ξ A = i curlSymbol ξ A`
(`Feec.MatrixSymbol.curlSymbol`). This file proves the fibre algebra once, for every frequency:

* `curl_grad`: `curl_ξ grad_ξ = 0`; `adjoint_curl`: `curl_ξ* = curl_ξ`; `adjoint_grad`:
  `grad_ξ* = div_ξ`, `div_ξ A = -i A ξ`.
* `tsd ξ`: the transverse–traceless fibre (symmetric, trace-free, `A ξ = 0`,
  `Feec.TT.ttSub`), and **`isFibreReducing`**: `({0}, tsd ξ, tsd ξ)` reduces the fibre complex
  (Lemma 3.5 on the symbol, `Feec.MatrixSymbol.curlSymbol_mem_ttSub`, and `grad_ξ u ⊥ tsd ξ`).
* `norm_grad`: `‖grad_ξ u‖ = |ξ| ‖u‖`; `norm_curl_sq_add_norm_div_sq`:
  `‖curl_ξ A‖² + ‖div_ξ A‖² = |ξ|² ‖A‖²` (Lagrange's identity row by row), hence the fibre gaps
  `norm_curl_of_mem_orthogonal`.
* `gradCurl : FibreComplex ℂ ℝ³ ComplexShape.fin3 (W3 ℂ³ ℂ³ˣ³ ℂ³ˣ³)`, homogeneous of degree `1`;
  `measurable_starProjection_tsd` (the fibre projection is measurable in `ξ`).

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.10 (Prop 4.17, (4.14))
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Matrix Finset

namespace Feec

namespace Fourier

section W3

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u} [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂]
  [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂]
  [FiniteDimensional 𝕜 W₀] [FiniteDimensional 𝕜 W₁] [FiniteDimensional 𝕜 W₂]

instance instFiniteDimensionalW3 : ∀ i, FiniteDimensional 𝕜 (ShortHilbertComplex.W3 W₀ W₁ W₂ i)
  | 0 => inferInstanceAs (FiniteDimensional 𝕜 W₀)
  | 1 => inferInstanceAs (FiniteDimensional 𝕜 W₁)
  | 2 => inferInstanceAs (FiniteDimensional 𝕜 W₂)

end W3

namespace GradCurl

/-- Vectors `ℂ³`. -/
abbrev Vec := EuclideanSpace ℂ (Fin 3)
/-- Matrices `ℂ³ˣ³` with the Frobenius inner product. -/
abbrev Mat := EuclideanSpace ℂ (Fin 3 × Fin 3)
/-- Frequencies `ξ ∈ ℝ³`. -/
abbrev Freq := EuclideanSpace ℝ (Fin 3)

/-- The matrix of an element of `Mat`. -/
def toMatrix : Mat →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun M := Matrix.of fun a b => M (a, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The element of `Mat` of a matrix. -/
def ofMatrix : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Mat where
  toFun A := WithLp.toLp 2 fun p => A p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem toMatrix_apply (M : Mat) (a b : Fin 3) : toMatrix M a b = M (a, b) := rfl

@[simp] theorem ofMatrix_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (p : Fin 3 × Fin 3) :
    ofMatrix A p = A p.1 p.2 := rfl

/-- The complexified frequency. -/
def cfreq (ξ : Freq) : Fin 3 → ℂ := fun j => (ξ j : ℂ)

/-- **The transverse–traceless fibre** at `ξ`: symmetric, trace-free, `A ξ = 0`. -/
def tsd (ξ : Freq) : Submodule ℂ Mat := (TT.ttSub (cfreq ξ)).comap toMatrix

theorem mem_tsd {ξ : Freq} {M : Mat} :
    M ∈ tsd ξ ↔ (toMatrix M)ᵀ = toMatrix M ∧ (toMatrix M).trace = 0 ∧
      toMatrix M *ᵥ cfreq ξ = 0 := Iff.rfl

/-! ### The symbols -/

/-- The gradient symbol `grad_ξ u = i u ξᵀ`, `(grad u)_{ab} = ∂_b u_a`. -/
def grad (ξ : Freq) : Vec →L[ℂ] Mat :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 fun p => Complex.I * u p.1 * (ξ p.2 : ℂ)
      map_add' := fun u v => by ext p; simp; ring
      map_smul' := fun a u => by ext p; simp; ring }

theorem grad_apply (ξ : Freq) (u : Vec) (a b : Fin 3) :
    grad ξ u (a, b) = Complex.I * u a * (ξ b : ℂ) := rfl

/-- The row-wise curl symbol `curl_ξ A = i curlSymbol ξ A`,
`(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`. -/
def curl (ξ : Freq) : Mat →L[ℂ] Mat :=
  LinearMap.toContinuousLinearMap
    (ofMatrix ∘ₗ (Complex.I • MatrixSymbol.curlSymbolₗ (cfreq ξ)) ∘ₗ toMatrix)

theorem curl_apply (ξ : Freq) (M : Mat) (a b : Fin 3) :
    curl ξ M (a, b) = Complex.I * ∑ c, ∑ d, leviCivita3 ℂ b c d * ((ξ c : ℂ) * M (a, d)) := by
  simp [curl, MatrixSymbol.curlSymbolₗ, MatrixSymbol.curlSymbol, MatrixSymbol.curl,
    MatrixSymbol.symbolJet, cfreq]

/-- The divergence symbol `div_ξ A = -i A ξ` (the adjoint of `grad_ξ`). -/
def div (ξ : Freq) : Mat →L[ℂ] Vec :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => WithLp.toLp 2 fun a => -Complex.I * ∑ b, M (a, b) * (ξ b : ℂ)
      map_add' := fun M N => by ext a; simp [add_mul, sum_add_distrib]; ring
      map_smul' := fun c M => by ext a; simp [mul_sum]; refine sum_congr rfl fun b _ => by ring }

theorem div_apply (ξ : Freq) (M : Mat) (a : Fin 3) :
    div ξ M a = -Complex.I * ∑ b, M (a, b) * (ξ b : ℂ) := rfl

theorem inner_mat (M N : Mat) : ⟪M, N⟫_ℂ = ∑ a, ∑ b, conj (M (a, b)) * N (a, b) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [RCLike.inner_apply, mul_comm]

theorem inner_vec (u v : Vec) : ⟪u, v⟫_ℂ = ∑ a, conj (u a) * v a := by
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- **`curl_ξ grad_ξ = 0`**. -/
theorem curl_grad (ξ : Freq) (u : Vec) : curl ξ (grad ξ u) = 0 := by
  ext ⟨a, b⟩
  rw [curl_apply]
  simp only [grad_apply, PiLp.zero_apply]
  fin_cases b <;> simp [Fin.sum_univ_three, leviCivita3_apply] <;> ring

/-- **`grad_ξ* = div_ξ`**. -/
theorem adjoint_grad (ξ : Freq) : ContinuousLinearMap.adjoint (grad ξ) = div ξ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun M u => ?_).symm
  rw [inner_vec, inner_mat]
  simp only [div_apply, grad_apply, map_mul, map_neg, map_sum, Complex.conj_I,
    Complex.conj_ofReal, sum_mul, mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- `conj` commutes with `ε`. -/
theorem conj_leviCivita3 (i j k : Fin 3) : conj (leviCivita3 ℂ i j k) = leviCivita3 ℂ i j k :=
  map_leviCivita (starRingEnd ℂ) _

/-- **`curl_ξ* = curl_ξ`**: the row-wise curl symbol is self-adjoint. -/
theorem inner_curl (ξ : Freq) (M N : Mat) : ⟪curl ξ M, N⟫_ℂ = ⟪M, curl ξ N⟫_ℂ := by
  rw [inner_mat, inner_mat]
  simp only [curl_apply, map_mul, map_sum, Complex.conj_I, conj_leviCivita3, Complex.conj_ofReal]
  simp only [Fin.sum_univ_three, leviCivita3_apply]
  simp
  ring

theorem adjoint_curl (ξ : Freq) : ContinuousLinearMap.adjoint (curl ξ) = curl ξ :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun M N => inner_curl ξ M N).symm


/-! ### The transverse–traceless fibre -/

theorem toMatrix_curl (ξ : Freq) (M : Mat) :
    toMatrix (curl ξ M) = Complex.I • MatrixSymbol.curlSymbol (cfreq ξ) (toMatrix M) := rfl

/-- **Lemma 3.5 on the symbol**: `curl_ξ` maps `tsd ξ` to itself. Thesis: Lemma 3.5 -/
theorem curl_mem_tsd {ξ : Freq} {M : Mat} (hM : M ∈ tsd ξ) : curl ξ M ∈ tsd ξ := by
  change toMatrix (curl ξ M) ∈ TT.ttSub (cfreq ξ)
  rw [toMatrix_curl]
  exact Submodule.smul_mem _ _ (MatrixSymbol.curlSymbol_mem_ttSub hM)

theorem mulVec_apply_eq_zero {ξ : Freq} {M : Mat} (hM : M ∈ tsd ξ) (a : Fin 3) :
    ∑ b, M (a, b) * (ξ b : ℂ) = 0 := by
  have := congrFun hM.2.2 a
  simpa [mulVec, dotProduct, cfreq] using this

/-- Gradients are orthogonal to the transverse–traceless fibre. -/
theorem inner_grad_eq_zero {ξ : Freq} {M : Mat} (hM : M ∈ tsd ξ) (u : Vec) :
    ⟪grad ξ u, M⟫_ℂ = 0 := by
  rw [inner_mat]
  simp only [grad_apply, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have : ∀ a, ∑ b, -Complex.I * conj (u a) * (ξ b : ℂ) * M (a, b) =
      -Complex.I * conj (u a) * ∑ b, M (a, b) * (ξ b : ℂ) := fun a => by
    rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
  simp_rw [this, mulVec_apply_eq_zero hM, mul_zero, sum_const_zero]

theorem grad_mem_orthogonal (ξ : Freq) (u : Vec) : grad ξ u ∈ (tsd ξ)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro M hM
  rw [← inner_conj_symm, inner_grad_eq_zero hM, map_zero]

/-- `curl_ξ` maps `(tsd ξ)ᗮ` to itself (it is self-adjoint and preserves `tsd ξ`). -/
theorem curl_mem_orthogonal {ξ : Freq} {N : Mat} (hN : N ∈ (tsd ξ)ᗮ) : curl ξ N ∈ (tsd ξ)ᗮ := by
  rw [Submodule.mem_orthogonal] at hN ⊢
  intro M hM
  rw [← inner_curl]
  exact hN _ (curl_mem_tsd hM)

/-! ### Norms and fibre gaps -/

theorem norm_grad (ξ : Freq) (u : Vec) : ‖grad ξ u‖ = ‖ξ‖ * ‖u‖ := by
  have h : ‖grad ξ u‖ ^ 2 = (‖ξ‖ * ‖u‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [grad_apply, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, mul_pow]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- **The Lagrange identity for the curl symbol**: `‖curl_ξ A‖² + ‖div_ξ A‖² = |ξ|² ‖A‖²`. -/
theorem norm_curl_sq_add_norm_div_sq (ξ : Freq) (M : Mat) :
    ‖curl ξ M‖ ^ 2 + ‖div ξ M‖ ^ 2 = ‖ξ‖ ^ 2 * ‖M‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [curl_apply, div_apply, Fin.sum_univ_three, leviCivita3_apply]
  simp only [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
  simp
  ring

/-- `‖curl_ξ A‖ ≤ |ξ| ‖A‖`. -/
theorem norm_curl_le (ξ : Freq) (M : Mat) : ‖curl ξ M‖ ≤ ‖ξ‖ * ‖M‖ := by
  have h := norm_curl_sq_add_norm_div_sq ξ M
  have : ‖curl ξ M‖ ^ 2 ≤ (‖ξ‖ * ‖M‖) ^ 2 := by
    rw [mul_pow, ← h]; nlinarith [sq_nonneg ‖div ξ M‖]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 this

/-- On `N(curl_ξ)ᗮ` the divergence symbol vanishes (it is orthogonal to `R(grad_ξ)`). -/
theorem div_eq_zero_of_mem_orthogonal {ξ : Freq} {v : Mat}
    (hv : v ∈ (LinearMap.ker (curl ξ : Mat →ₗ[ℂ] Mat))ᗮ) : div ξ v = 0 := by
  have h : ∀ w : Vec, ⟪grad ξ w, v⟫_ℂ = 0 := fun w =>
    Submodule.inner_right_of_mem_orthogonal (by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact curl_grad ξ w) hv
  have h2 := h (div ξ v)
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_grad] at h2
  exact inner_self_eq_zero.1 h2

/-- **The fibre gap of the curl symbol**: `‖curl_ξ v‖ = |ξ| ‖v‖` for `v ⊥ N(curl_ξ)`. -/
theorem norm_curl_of_mem_orthogonal {ξ : Freq} {v : Mat}
    (hv : v ∈ (LinearMap.ker (curl ξ : Mat →ₗ[ℂ] Mat))ᗮ) : ‖curl ξ v‖ = ‖ξ‖ * ‖v‖ := by
  have h := norm_curl_sq_add_norm_div_sq ξ v
  rw [div_eq_zero_of_mem_orthogonal hv, norm_zero, zero_pow two_ne_zero, add_zero, ← mul_pow] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h


/-- The divergence symbol vanishes on the TSD fibre. -/
theorem div_eq_zero_of_mem_tsd {ξ : Freq} {M : Mat} (hM : M ∈ tsd ξ) : div ξ M = 0 := by
  ext a
  rw [div_apply, mulVec_apply_eq_zero hM a, mul_zero]; rfl

/-- On the TSD fibre the curl symbol is `|ξ|` times an isometry: `‖curl_ξ v‖ = |ξ| ‖v‖`. -/
theorem norm_curl_of_mem_tsd {ξ : Freq} {v : Mat} (hv : v ∈ tsd ξ) :
    ‖curl ξ v‖ = ‖ξ‖ * ‖v‖ := by
  have h := norm_curl_sq_add_norm_div_sq ξ v
  rw [div_eq_zero_of_mem_tsd hv, norm_zero, zero_pow two_ne_zero, add_zero, ← mul_pow] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- **`H¹` regularity of the TSD projection, fibrewise**: `|ξ| ‖P_ξ A‖ ≤ ‖curl_ξ A‖`, since
`P_ξ` commutes with `curl_ξ` and `curl_ξ` is `|ξ|` times an isometry on `tsd ξ`. -/
theorem mul_norm_starProjection_le (ξ : Freq) (A : Mat) :
    ‖ξ‖ * ‖(tsd ξ).starProjection A‖ ≤ ‖curl ξ A‖ := by
  have hcomm := starProjection_comm_of_map (curl ξ) (tsd ξ) (tsd ξ)
    (by rintro _ ⟨v, hv, rfl⟩; exact curl_mem_tsd hv)
    (by rw [adjoint_curl]; rintro _ ⟨v, hv, rfl⟩; exact curl_mem_tsd hv) A
  rw [← norm_curl_of_mem_tsd (Submodule.starProjection_apply_mem _ A), ← hcomm]
  exact Submodule.norm_starProjection_apply_le _ _

/-! ### Dependence on the frequency -/

theorem grad_smul (t : ℝ) (ξ : Freq) : grad (t • ξ) = (t : ℂ) • grad ξ := by
  refine ContinuousLinearMap.ext fun u => ?_
  ext ⟨a, b⟩
  simp only [grad_apply, _root_.smul_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem curl_smul (t : ℝ) (ξ : Freq) : curl (t • ξ) = (t : ℂ) • curl ξ := by
  refine ContinuousLinearMap.ext fun M => ?_
  ext ⟨a, b⟩
  simp only [curl_apply, _root_.smul_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    mul_sum]
  refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => by ring

/-- The gradient symbol is linear in the frequency. -/
theorem grad_eq_sum (ξ : Freq) :
    grad ξ = ∑ j, ((ξ j : ℝ) : ℂ) • grad (EuclideanSpace.single j (1 : ℝ)) := by
  refine ContinuousLinearMap.ext fun u => ?_
  ext ⟨a, b⟩
  simp only [_root_.sum_apply, _root_.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, grad_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The curl symbol is linear in the frequency. -/
theorem curl_eq_sum (ξ : Freq) :
    curl ξ = ∑ j, ((ξ j : ℝ) : ℂ) • curl (EuclideanSpace.single j (1 : ℝ)) := by
  refine ContinuousLinearMap.ext fun M => ?_
  ext ⟨a, b⟩
  fin_cases b <;> simp [curl_apply, Fin.sum_univ_three, leviCivita3_apply] <;> ring

theorem continuous_grad : Continuous grad := by
  refine continuous_clm_apply.2 fun u => ?_
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  change Continuous fun ξ : Freq => Complex.I * u p.1 * ((ξ p.2 : ℝ) : ℂ)
  exact continuous_const.mul (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ p.2))

theorem continuous_curl : Continuous curl := by
  refine continuous_clm_apply.2 fun M => ?_
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  change Continuous fun ξ : Freq => curl ξ M (p.1, p.2)
  simp only [curl_apply]
  refine continuous_const.mul (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
    continuous_const.mul ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ c)).mul
      continuous_const))

/-! ### The fibre complex -/

open ShortHilbertComplex in
/-- The symbols of the grad–curl complex on the window `Fin 3`. -/
def sym : ∀ i j : Fin 3, Freq → W3 Vec Mat Mat i →L[ℂ] W3 Vec Mat Mat j
  | 0, 1 => grad
  | 1, 2 => curl
  | _, _ => 0

open ShortHilbertComplex in
/-- **The grad–curl family of fibre complexes** `ℂ³ --grad_ξ--> ℂ³ˣ³ --curl_ξ--> ℂ³ˣ³`. -/
def gradCurl : FibreComplex ℂ Freq ComplexShape.fin3 (W3 Vec Mat Mat) where
  m := sym
  shape i j h := by
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl h
  comp i j k ξ := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first
      | exact ContinuousLinearMap.ext fun u => curl_grad ξ u
      | exact ContinuousLinearMap.zero_comp _
      | exact ContinuousLinearMap.comp_zero _
  cont i j := by
    fin_cases i <;> fin_cases j <;>
      first | exact continuous_grad | exact continuous_curl | exact continuous_const

@[simp] theorem gradCurl_m01 (ξ : Freq) : gradCurl.m 0 1 ξ = grad ξ := rfl
@[simp] theorem gradCurl_m12 (ξ : Freq) : gradCurl.m 1 2 ξ = curl ξ := rfl

theorem gradCurl_isHomogeneous01 : gradCurl.IsHomogeneous 0 1 1 := fun t ξ _ => by
  rw [gradCurl_m01, gradCurl_m01, grad_smul, pow_one]; rfl

theorem gradCurl_isHomogeneous12 : gradCurl.IsHomogeneous 1 2 1 := fun t ξ _ => by
  rw [gradCurl_m12, gradCurl_m12, curl_smul, pow_one]; rfl

open ShortHilbertComplex in
/-- **The constraint fibres** `({0}, tsd ξ, tsd ξ)` (Thesis Prop 4.17: `σ = 0`, `E, B` TSD). -/
def tsdK : ∀ i : Fin 3, Freq → Submodule ℂ (W3 Vec Mat Mat i)
  | 0 => fun _ => ⊥
  | 1 => tsd
  | 2 => tsd

instance (i : Fin 3) (ξ : Freq) : (tsdK i ξ).HasOrthogonalProjection := by
  fin_cases i <;> infer_instance

/-- **`({0}, tsd ξ, tsd ξ)` reduces the grad–curl fibre complex at every frequency.**
Thesis: Lemma 3.5, Prop 4.17 -/
theorem isFibreReducing : gradCurl.IsFibreReducing tsdK := by
  refine FibreComplex.IsFibreReducing.of_orthogonal (fun i j ξ => ?_) (fun i j ξ => ?_)
  · fin_cases i <;> fin_cases j
    all_goals first
      | (rintro _ ⟨v, -, rfl⟩; exact Submodule.zero_mem _)
      | (rintro _ ⟨v, hv, rfl⟩; exact curl_mem_tsd hv)
      | (rintro _ ⟨v, hv, rfl⟩; rw [(Submodule.mem_bot ℂ).1 hv]; simp)
  · fin_cases i <;> fin_cases j
    all_goals first
      | (rintro _ ⟨v, -, rfl⟩; exact Submodule.zero_mem _)
      | (rintro _ ⟨v, hv, rfl⟩; exact curl_mem_orthogonal hv)
      | (rintro _ ⟨v, -, rfl⟩; exact grad_mem_orthogonal ξ v)


/-! ### Measurability of the fibre projection -/

/-- The constraint map `A ↦ (A - Aᵀ, tr A, A ξ)` whose kernel is `tsd ξ`. -/
def tsdMap (ξ : Freq) : Mat →L[ℂ] EuclideanSpace ℂ ((Fin 3 × Fin 3) ⊕ (Unit ⊕ Fin 3)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => WithLp.toLp 2 (Sum.elim (fun p => M p - M (p.2, p.1))
        (Sum.elim (fun _ => ∑ a, M (a, a)) fun a => ∑ b, M (a, b) * (ξ b : ℂ)))
      map_add' := fun M N => by
        ext (p | _ | a)
        · simp; ring
        · simp [sum_add_distrib]
        · simp [sum_add_distrib, add_mul]
      map_smul' := fun c M => by
        ext (p | _ | a)
        · simp [mul_sub]
        · simp [mul_sum]
        · simp [mul_sum]; refine sum_congr rfl fun _ _ => by ring }

theorem tsd_eq_ker (ξ : Freq) :
    tsd ξ = LinearMap.ker (tsdMap ξ : Mat →ₗ[ℂ] EuclideanSpace ℂ ((Fin 3 × Fin 3) ⊕ (Unit ⊕ Fin 3))) := by
  ext M
  rw [mem_tsd, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨h1, h2, h3⟩
    ext (p | _ | a)
    · have := congrFun (congrFun h1 p.2) p.1
      simp only [transpose_apply, toMatrix_apply] at this
      simp [tsdMap, this]
    · simpa [tsdMap, trace] using h2
    · simpa [tsdMap, mulVec, dotProduct, cfreq] using congrFun h3 a
  · intro h
    have h' := fun q => congrArg (fun x : EuclideanSpace ℂ _ => x q) h
    refine ⟨?_, ?_, ?_⟩
    · ext a b
      have := h' (Sum.inl (b, a))
      simp only [tsdMap] at this
      simpa [sub_eq_zero] using this
    · have := h' (Sum.inr (Sum.inl ()))
      simpa [tsdMap, trace] using this
    · ext a
      have := h' (Sum.inr (Sum.inr a))
      simpa [tsdMap, mulVec, dotProduct, cfreq] using this

theorem continuous_tsdMap : Continuous tsdMap := by
  refine continuous_clm_apply.2 fun M => ?_
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun q => ?_)
  rcases q with p | _ | a
  · exact continuous_const
  · exact continuous_const
  · change Continuous fun ξ : Freq => ∑ b, M (a, b) * ((ξ b : ℝ) : ℂ)
    exact continuous_finsetSum _ fun b _ =>
      continuous_const.mul (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ b))

/-- **The transverse–traceless fibre projection is measurable in the frequency** (it is
discontinuous at `ξ = 0`). -/
theorem measurable_starProjection_tsd : Measurable fun ξ : Freq => (tsd ξ).starProjection := by
  have h := (stronglyMeasurable_starProjection_ker_clm (𝕜 := ℂ) (E := Mat)
    (F := EuclideanSpace ℂ ((Fin 3 × Fin 3) ⊕ (Unit ⊕ Fin 3)))).measurable.comp
      continuous_tsdMap.measurable
  have e : (fun ξ : Freq => (tsd ξ).starProjection) =
      (fun b : Mat →L[ℂ] EuclideanSpace ℂ ((Fin 3 × Fin 3) ⊕ (Unit ⊕ Fin 3)) =>
        (LinearMap.ker (b : Mat →ₗ[ℂ] EuclideanSpace ℂ ((Fin 3 × Fin 3) ⊕ (Unit ⊕ Fin 3)))).starProjection) ∘
          tsdMap := by
    funext ξ; simp only [Function.comp_apply]; simp_rw [tsd_eq_ker]
  rw [e]; exact h

theorem measurable_starProjection_tsdK (i : Fin 3) :
    Measurable fun ξ : Freq => (tsdK i ξ).starProjection := by
  fin_cases i
  · change Measurable fun _ : Freq => (⊥ : Submodule ℂ Vec).starProjection
    exact measurable_const
  · exact measurable_starProjection_tsd
  · exact measurable_starProjection_tsd


/-! ### Gaps and non-degeneracy -/

@[simp] theorem grad_zero : grad 0 = 0 :=
  ContinuousLinearMap.ext fun u => by ext ⟨a, b⟩; simp [grad_apply]

@[simp] theorem curl_zero : curl 0 = 0 :=
  ContinuousLinearMap.ext fun M => by ext ⟨a, b⟩; simp [curl_apply]

@[simp] theorem gradCurl_m_zero (i j : Fin 3) : gradCurl.m i j 0 = 0 := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact grad_zero
  · rfl
  · rfl
  · rfl
  · exact curl_zero
  · rfl
  · rfl
  · rfl

open ShortHilbertComplex in
theorem gap_of_zero {i j : Fin 3} {ξ : Freq} (h : gradCurl.m i j ξ = 0) :
    ∀ v ∈ (LinearMap.ker (gradCurl.m i j ξ : W3 Vec Mat Mat i →ₗ[ℂ] W3 Vec Mat Mat j))ᗮ,
      ‖ξ‖ * ‖v‖ ≤ ‖gradCurl.m i j ξ v‖ := by
  intro v hv
  rw [h] at hv
  rw [eq_zero_of_mem_orthogonal_ker_zero hv, norm_zero, mul_zero]
  exact norm_nonneg _

open ShortHilbertComplex in
/-- **The fibre gaps of the grad–curl complex**: `|ξ| ‖v‖ ≤ ‖m_ξ v‖` on `N(m_ξ)ᗮ`, for every
arrow. -/
theorem gradCurl_gap (i j : Fin 3) (ξ : Freq) :
    ∀ v ∈ (LinearMap.ker (gradCurl.m i j ξ : W3 Vec Mat Mat i →ₗ[ℂ] W3 Vec Mat Mat j))ᗮ,
      ‖ξ‖ * ‖v‖ ≤ ‖gradCurl.m i j ξ v‖ := by
  fin_cases i <;> fin_cases j
  · exact gap_of_zero rfl
  · intro v _; exact (norm_grad ξ v).ge
  · exact gap_of_zero rfl
  · exact gap_of_zero rfl
  · exact gap_of_zero rfl
  · intro v hv; exact (norm_curl_of_mem_orthogonal hv).ge
  · exact gap_of_zero rfl
  · exact gap_of_zero rfl
  · exact gap_of_zero rfl

theorem grad_ne_zero : gradCurl.m 0 1 ≠ 0 := by
  intro h
  have h' : grad (EuclideanSpace.single 0 1) = 0 := congrFun h _
  have := congrArg (fun T : Vec →L[ℂ] Mat => T (EuclideanSpace.single 0 1) (0, 0)) h'
  simp [grad_apply] at this

theorem curl_ne_zero : gradCurl.m 1 2 ≠ 0 := by
  intro h
  have h' : curl (EuclideanSpace.single 0 1) = 0 := congrFun h _
  have := congrArg (fun T : Mat →L[ℂ] Mat => T (EuclideanSpace.single (0, 2) 1) (0, 1)) h'
  simp [curl_apply, Fin.sum_univ_three, leviCivita3_apply] at this


/-! ### Real symbols -/

theorem grad_neg_entryConj (ξ : Freq) (u : Vec) :
    grad (-ξ) (entryConj u) = entryConj (grad ξ u) := by
  ext ⟨a, b⟩
  simp [grad_apply]

theorem curl_neg_entryConj (ξ : Freq) (M : Mat) :
    curl (-ξ) (entryConj M) = entryConj (curl ξ M) := by
  ext ⟨a, b⟩
  simp only [curl_apply, entryConj_apply, map_mul, map_sum, Complex.conj_I, conj_leviCivita3,
    Complex.conj_ofReal, PiLp.neg_apply, Complex.ofReal_neg]
  simp only [mul_sum, neg_mul, mul_neg, sum_neg_distrib]

open ShortHilbertComplex in
/-- Entrywise conjugation on the three fibres. -/
def cjW3 : ∀ i : Fin 3, W3 Vec Mat Mat i →L[ℝ] W3 Vec Mat Mat i
  | 0 => entryConj
  | 1 => entryConj
  | 2 => entryConj

open ShortHilbertComplex in
/-- **The grad–curl symbols are real**: `m (-ξ) (conj v) = conj (m ξ v)`. -/
theorem gradCurl_neg_cj (i j : Fin 3) (ξ : Freq) (v : W3 Vec Mat Mat i) :
    gradCurl.m i j (-ξ) (cjW3 i v) = cjW3 j (gradCurl.m i j ξ v) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact grad_neg_entryConj ξ v
    | exact curl_neg_entryConj ξ v
    | exact (map_zero (cjW3 _)).symm

open ShortHilbertComplex in
theorem cjW3_smul (i : Fin 3) (a : ℂ) (v : W3 Vec Mat Mat i) :
    cjW3 i (a • v) = (starRingEnd ℂ) a • cjW3 i v := by
  fin_cases i <;> exact entryConj_smul a v

open ShortHilbertComplex in
theorem cjW3_cjW3 (i : Fin 3) (v : W3 Vec Mat Mat i) : cjW3 i (cjW3 i v) = v := by
  fin_cases i <;> exact entryConj_entryConj v

open ShortHilbertComplex in
theorem inner_cjW3 (i : Fin 3) (v w : W3 Vec Mat Mat i) :
    ⟪cjW3 i v, cjW3 i w⟫_ℂ = ⟪w, v⟫_ℂ := by
  fin_cases i <;> exact inner_entryConj v w

end GradCurl

end Fourier

end Feec
