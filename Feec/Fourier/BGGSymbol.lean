module

public import Feec.Fourier.SymCurlSymbol

/-!
# The symbol of the BGG weak-symmetry complex (Thesis (5.1), §6.3)

The complex `H²(ℂ) --grad grad--> H(curl; ℂ³ˣ³) --(S₁, curl)--> L²(ℂ³) × L²(ℂ³ˣ³)` of the weakly
symmetric formulation (Thesis Ch. 5–6, `S₀ = I`, `S₁ = 2 vskw`), whose first differential is the
Hessian and whose second couples the skew part `S₁ A = axial A` (no derivative) to the row-wise
curl. At a frequency `ξ` the symbols are `hess_ξ c = -c ξ ξᵀ` and `bgg_ξ A = (axial A, curl_ξ A)`.

## Main results

* `bgg ξ`, `bgg_hess` (`(S₁, curl) grad grad = 0`: Hessians are symmetric and curl-free).
* `tsdB ξ = {0} × tsd ξ`, and **`isFibreReducing`**: `({0}, tsd ξ, {0} × tsd ξ)` reduces the
  fibre complex at every frequency (`S₁` kills symmetric matrices; Lemma 3.5 for the curl).
* `bggFamily : FibreComplex ℂ ℝ³ ComplexShape.fin3 (W3 ℂ ℂ³ˣ³ (ℂ³ × ℂ³ˣ³))`, with measurable
  fibre projections `aestronglyMeasurable_starProjection_bggK`.
* **`bgg_gap`**, `bgg_gap_zero`, **`bggFamily_gap`**: `‖v‖ ≤ 4 ‖m_ξ v‖` on `N(m_ξ)ᗮ` for every arrow
  at `ξ = 0` and `|ξ| ≥ 2π` (symmetric part via the curl, skew part via `S₁`), giving closed range
  on the torus.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 (§5.1, (5.1)), Ch. 6 (§6.1, §6.3), §3.4 (Lemma 3.5)
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021] (the BGG construction)
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
  (weakly imposed symmetry)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Matrix Finset

namespace Feec.Fourier.BGG

open GradCurl SymCurl

/-- The target fibre `ℂ³ × ℂ³ˣ³` of `(S₁, curl)`, with the `ℓ²` product inner product. -/
abbrev VM := WithLp 2 (Vec × Mat)

/-- `S₁ = 2 vskw`: the axial vector `(A₁₂ - A₂₁, A₂₀ - A₀₂, A₀₁ - A₁₀)` of the skew part. -/
def axialL : Mat →L[ℂ] Vec :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => WithLp.toLp 2 (MatrixSymbol.axial (toMatrix M))
      map_add' := fun M N => by ext a; simp [MatrixSymbol.axial_add]
      map_smul' := fun c M => by
        ext a; simp [MatrixSymbol.axial, mul_sum]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring }

theorem axialL_apply (M : Mat) : axialL M = WithLp.toLp 2 (MatrixSymbol.axial (toMatrix M)) := rfl

theorem axialL_eq_zero_of_mem_symSub {M : Mat} (hM : M ∈ symSub) : axialL M = 0 := by
  have h : (toMatrix M)ᵀ = toMatrix M := by ext a b; exact (hM b a)
  have := (MatrixSymbol.transpose_eq_iff_axial_eq_zero (toMatrix M)).1 h
  rw [axialL_apply, this]; rfl

/-- The embedding `M ↦ (0, M)`. -/
def inr : Mat →L[ℂ] VM :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ Vec Mat).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ Vec Mat

theorem inr_apply (M : Mat) : inr M = WithLp.toLp 2 (0, M) := rfl

/-- The BGG symbol `bgg_ξ A = (S₁ A, curl_ξ A)`. -/
def bgg (ξ : Freq) : Mat →L[ℂ] VM :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ Vec Mat).symm.toContinuousLinearMap ∘L
    (axialL.prod (curl ξ))

theorem bgg_apply (ξ : Freq) (M : Mat) : bgg ξ M = WithLp.toLp 2 (axialL M, curl ξ M) := rfl

/-- **`(S₁, curl_ξ) hess_ξ = 0`**. -/
theorem bgg_hess (ξ : Freq) (c : ℂ) : bgg ξ (hessM ξ c) = 0 := by
  rw [bgg_apply, axialL_eq_zero_of_mem_symSub (hessM_mem_symSub ξ c)]
  change WithLp.toLp 2 (0, curl ξ (grad ξ _)) = 0
  rw [curl_grad]; rfl

theorem inner_VM (v w : VM) :
    ⟪v, w⟫_ℂ = ⟪(WithLp.ofLp v).1, (WithLp.ofLp w).1⟫_ℂ + ⟪(WithLp.ofLp v).2, (WithLp.ofLp w).2⟫_ℂ :=
  WithLp.prod_inner_apply v w

/-! ### The constraint fibres -/

/-- The fibre `{0} × tsd ξ`. -/
def tsdB (ξ : Freq) : Submodule ℂ VM :=
  ((⊥ : Submodule ℂ Vec).prod (tsd ξ)).comap (WithLp.linearEquiv 2 ℂ (Vec × Mat)).toLinearMap

theorem mem_tsdB {ξ : Freq} {w : VM} :
    w ∈ tsdB ξ ↔ (WithLp.ofLp w).1 = 0 ∧ (WithLp.ofLp w).2 ∈ tsd ξ := by
  simp [tsdB, Submodule.mem_prod]

/-- The projection onto `{0} × tsd ξ` is `(v, M) ↦ (0, P_ξ M)`. -/
theorem starProjection_tsdB (ξ : Freq) (w : VM) :
    (tsdB ξ).starProjection w = inr ((tsd ξ).starProjection (WithLp.ofLp w).2) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact mem_tsdB.2 ⟨rfl, Submodule.starProjection_apply_mem _ _⟩
  intro v hv
  obtain ⟨h1, h2⟩ := mem_tsdB.1 hv
  rw [inner_VM, inr_apply, WithLp.ofLp_sub, WithLp.ofLp_toLp, Prod.fst_sub, Prod.snd_sub, h1,
    inner_zero_right, zero_add]
  exact (tsd ξ).starProjection_inner_eq_zero _ _ h2

theorem bgg_mem_tsdB {ξ : Freq} {M : Mat} (hM : M ∈ tsd ξ) : bgg ξ M ∈ tsdB ξ :=
  mem_tsdB.2 ⟨axialL_eq_zero_of_mem_symSub (tsd_le_symSub ξ hM), curl_mem_tsd hM⟩

theorem bgg_mem_orthogonal {ξ : Freq} {N : Mat} (hN : N ∈ (tsd ξ)ᗮ) : bgg ξ N ∈ (tsdB ξ)ᗮ := by
  rw [Submodule.mem_orthogonal] at hN ⊢
  intro w hw
  obtain ⟨h1, h2⟩ := mem_tsdB.1 hw
  rw [inner_VM, bgg_apply, WithLp.ofLp_toLp, h1, inner_zero_left, zero_add, ← inner_curl]
  exact hN _ (curl_mem_tsd h2)

theorem hessM_mem_orthogonal (ξ : Freq) (c : ℂ) : hessM ξ c ∈ (tsd ξ)ᗮ :=
  grad_mem_orthogonal ξ _

/-! ### The fibre complex -/

theorem bgg_smul_curl (t : ℝ) (ξ : Freq) (M : Mat) :
    bgg (t • ξ) M = WithLp.toLp 2 (axialL M, (t : ℂ) • curl ξ M) := by
  rw [bgg_apply, curl_smul]; rfl

theorem continuous_bgg : Continuous bgg := by
  refine continuous_clm_apply.2 fun M => ?_
  have h : Continuous fun ξ : Freq => curl ξ M := continuous_curl.clm_apply continuous_const
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ Vec Mat).symm.continuous.comp
    (continuous_const.prodMk h)

open ShortHilbertComplex in
/-- The symbols of the BGG complex on the window `Fin 3`. -/
def sym : ∀ i j : Fin 3, Freq → W3 ℂ Mat VM i →L[ℂ] W3 ℂ Mat VM j
  | 0, 1 => hessM
  | 1, 2 => bgg
  | _, _ => 0

open ShortHilbertComplex in
/-- **The BGG weak-symmetry family** `ℂ --hess_ξ--> ℂ³ˣ³ --(S₁, curl_ξ)--> ℂ³ × ℂ³ˣ³`. -/
def bggFamily : FibreComplex ℂ Freq ComplexShape.fin3 (W3 ℂ Mat VM) where
  m := sym
  shape i j h := by
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl h
  comp i j k ξ := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first
      | exact ContinuousLinearMap.ext fun c => bgg_hess ξ c
      | exact ContinuousLinearMap.zero_comp _
      | exact ContinuousLinearMap.comp_zero _
  cont i j := by
    fin_cases i <;> fin_cases j <;>
      first | exact continuous_hessM | exact continuous_bgg | exact continuous_const

@[simp] theorem bggFamily_m01 (ξ : Freq) : bggFamily.m 0 1 ξ = hessM ξ := rfl
@[simp] theorem bggFamily_m12 (ξ : Freq) : bggFamily.m 1 2 ξ = bgg ξ := rfl

theorem bggFamily_isHomogeneous01 : bggFamily.IsHomogeneous 0 1 2 := fun t ξ _ => by
  rw [bggFamily_m01, bggFamily_m01, hessM_smul]; rfl

open ShortHilbertComplex in
/-- **The constraint fibres** `({0}, tsd ξ, {0} × tsd ξ)`: `σ = 0`, `u` TSD, `(M, B) = (0, B)` with
`B` TSD. -/
def bggK : ∀ i : Fin 3, Freq → Submodule ℂ (W3 ℂ Mat VM i)
  | 0 => fun _ => ⊥
  | 1 => tsd
  | 2 => tsdB

instance (i : Fin 3) (ξ : Freq) : (bggK i ξ).HasOrthogonalProjection := by
  fin_cases i <;> infer_instance

/-- **`({0}, tsd ξ, {0} × tsd ξ)` reduces the BGG fibre complex at every frequency.** -/
theorem isFibreReducing : bggFamily.IsFibreReducing bggK := by
  refine FibreComplex.IsFibreReducing.of_orthogonal (fun i j ξ => ?_) (fun i j ξ => ?_)
  · fin_cases i <;> fin_cases j
    all_goals first
      | (rintro _ ⟨v, -, rfl⟩; exact Submodule.zero_mem _)
      | (rintro _ ⟨v, hv, rfl⟩; exact bgg_mem_tsdB hv)
      | (rintro _ ⟨v, hv, rfl⟩; rw [(Submodule.mem_bot ℂ).1 hv]; simp)
  · fin_cases i <;> fin_cases j
    all_goals first
      | (rintro _ ⟨v, -, rfl⟩; exact Submodule.zero_mem _)
      | (rintro _ ⟨v, hv, rfl⟩; exact bgg_mem_orthogonal hv)
      | (rintro _ ⟨v, -, rfl⟩; exact hessM_mem_orthogonal ξ v)

/-! ### Measurability of the fibre projections -/

theorem starProjection_tsdB_eq (ξ : Freq) :
    (tsdB ξ).starProjection = inr ∘L (tsd ξ).starProjection ∘L
      (ContinuousLinearMap.snd ℂ Vec Mat ∘L
        (WithLp.prodContinuousLinearEquiv 2 ℂ Vec Mat).toContinuousLinearMap) :=
  ContinuousLinearMap.ext fun w => starProjection_tsdB ξ w

theorem aestronglyMeasurable_starProjection_bggK {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → Freq} (hf : Measurable f) (i : Fin 3) :
    MeasureTheory.AEStronglyMeasurable (fun a => (bggK i (f a)).starProjection) μ := by
  fin_cases i
  · exact MeasureTheory.aestronglyMeasurable_const (b := (⊥ : Submodule ℂ ℂ).starProjection)
  · exact aestronglyMeasurable_starProjection_tsd hf
  · change MeasureTheory.AEStronglyMeasurable (fun a => (tsdB (f a)).starProjection) μ
    simp_rw [starProjection_tsdB_eq]
    exact ((ContinuousLinearMap.compL ℂ VM Mat VM inr).continuous.comp
      ((ContinuousLinearMap.compL ℂ VM Mat Mat).flip (ContinuousLinearMap.snd ℂ Vec Mat ∘L
        (WithLp.prodContinuousLinearEquiv 2 ℂ Vec Mat).toContinuousLinearMap)).continuous
        |>.comp_aestronglyMeasurable (aestronglyMeasurable_starProjection_tsd hf))

theorem hessM_ne_zero : bggFamily.m 0 1 ≠ 0 := by
  intro h
  have h' : hessM (EuclideanSpace.single 0 1) = 0 := congrFun h _
  have := congrArg (fun T : ℂ →L[ℂ] Mat => T 1 (0, 0)) h'
  simp [hessM_apply] at this

/-! ### The fibre gap of `(S₁, curl)` -/

/-- The symmetric part `(A + Aᵀ)/2`. -/
def symPart (M : Mat) : Mat := WithLp.toLp 2 fun p => (M p + M (p.2, p.1)) / 2

theorem symPart_mem (M : Mat) : symPart M ∈ symSub := fun a b => by
  simp only [symPart, WithLp.ofLp_toLp]; ring

theorem axialL_sub_symPart (M : Mat) : axialL (M - symPart M) = axialL M := by
  rw [_root_.map_sub, axialL_eq_zero_of_mem_symSub (symPart_mem M), sub_zero]

theorem norm_sq_sub_symPart (M : Mat) : 2 * ‖M - symPart M‖ ^ 2 = ‖axialL M‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [axialL_apply, Fin.sum_univ_three, MatrixSymbol.axial_apply_zero,
    MatrixSymbol.axial_apply_one, MatrixSymbol.axial_apply_two, PiLp.sub_apply, symPart,
    WithLp.ofLp_toLp, toMatrix_apply]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem quad_symPart (ξ : Freq) (M : Mat) :
    ∑ a, ∑ b, (ξ a : ℂ) * (ξ b : ℂ) * symPart M (a, b) =
      ∑ a, ∑ b, (ξ a : ℂ) * (ξ b : ℂ) * M (a, b) := by
  simp only [symPart, WithLp.ofLp_toLp, Fin.sum_univ_three]
  ring

theorem norm_bgg_sq (ξ : Freq) (M : Mat) :
    ‖bgg ξ M‖ ^ 2 = ‖axialL M‖ ^ 2 + ‖curl ξ M‖ ^ 2 := by
  rw [bgg_apply, WithLp.prod_norm_sq_eq_of_L2]; rfl

/-- **The fibre gap of the BGG symbol** at the torus frequencies: `‖v‖ ≤ 4 ‖(S₁, curl_ξ) v‖` on
`N(S₁, curl_ξ)ᗮ` for `|ξ| ≥ 2π` (split `v` into its symmetric part, controlled by the curl through
`Feec.Fourier.SymCurl.mul_norm_le_two_norm_curl`, and its skew part, controlled by `S₁`). -/
theorem bgg_gap {ξ : Freq} (hξ : 2 * Real.pi ≤ ‖ξ‖) :
    ∀ v ∈ (LinearMap.ker (bgg ξ : Mat →ₗ[ℂ] VM))ᗮ, ‖v‖ ≤ 4 * ‖bgg ξ v‖ := by
  intro v hv
  have hξ1 : 1 ≤ ‖ξ‖ := by nlinarith [Real.two_le_pi]
  have hξpos : 0 < ‖ξ‖ := by linarith
  have h0 : ⟪hessM ξ 1, v⟫_ℂ = 0 := by
    refine Submodule.inner_right_of_mem_orthogonal ?_ hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact bgg_hess ξ 1
  rw [inner_hessM_one, neg_eq_zero] at h0
  have hS0 : ∑ a, ∑ b, (ξ a : ℂ) * (ξ b : ℂ) * symPart v (a, b) = 0 := by
    rw [quad_symPart]; exact h0
  have hS : ‖ξ‖ * ‖symPart v‖ ≤ 2 * ‖curl ξ (symPart v)‖ :=
    mul_norm_le_two_norm_curl (symPart_mem v) hS0
  have hb := norm_bgg_sq ξ v
  have hnb1 : ‖axialL v‖ ≤ ‖bgg ξ v‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖curl ξ v‖])
  have hnb2 : ‖curl ξ v‖ ≤ ‖bgg ξ v‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖axialL v‖])
  have hK : ‖v - symPart v‖ ≤ ‖axialL v‖ := by
    have := norm_sq_sub_symPart v
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖v - symPart v‖])
  have hcK := norm_curl_le ξ (v - symPart v)
  have hcS : ‖curl ξ (symPart v)‖ ≤ ‖curl ξ v‖ + ‖ξ‖ * ‖v - symPart v‖ := by
    have e : curl ξ (symPart v) = curl ξ v - curl ξ (v - symPart v) := by
      rw [← _root_.map_sub (curl ξ) v (v - symPart v), sub_sub_cancel]
    rw [e]
    linarith [norm_sub_le (curl ξ v) (curl ξ (v - symPart v))]
  have hvSK : ‖v‖ ≤ ‖symPart v‖ + ‖v - symPart v‖ := by
    have := norm_add_le (symPart v) (v - symPart v)
    rwa [add_sub_cancel] at this
  have hS' : ‖symPart v‖ ≤ 2 * ‖curl ξ v‖ + 2 * ‖v - symPart v‖ := by
    have h1 : ‖ξ‖ * ‖symPart v‖ ≤ ‖ξ‖ * (2 * ‖curl ξ v‖ + 2 * ‖v - symPart v‖) := by
      nlinarith [norm_nonneg (curl ξ v), norm_nonneg (v - symPart v)]
    exact le_of_mul_le_mul_left h1 hξpos
  nlinarith [norm_nonneg (v - symPart v), norm_nonneg (symPart v)]

theorem inner_symPart_sub (v : Mat) : ⟪symPart v, v - symPart v⟫_ℂ = 0 := by
  rw [inner_mat]
  simp only [symPart, PiLp.sub_apply, WithLp.ofLp_toLp, map_div₀, map_add, Fin.sum_univ_three]
  ring

/-- At `ξ = 0` the BGG symbol is `(S₁, 0)`, with gap `‖v‖ ≤ ‖S₁ v‖` on `N(S₁)ᗮ` (skew
matrices). -/
theorem bgg_gap_zero : ∀ v ∈ (LinearMap.ker (bgg 0 : Mat →ₗ[ℂ] VM))ᗮ, ‖v‖ ≤ 4 * ‖bgg 0 v‖ := by
  intro v hv
  have hker : symPart v ∈ LinearMap.ker (bgg 0 : Mat →ₗ[ℂ] VM) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, bgg_apply,
      axialL_eq_zero_of_mem_symSub (symPart_mem v), curl_zero]
    rfl
  have h1 : ⟪symPart v, v⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hker hv
  have h2 : symPart v = 0 := by
    have : ⟪symPart v, symPart v⟫_ℂ = 0 := by
      have e := inner_add_right (𝕜 := ℂ) (symPart v) (symPart v) (v - symPart v)
      rw [add_sub_cancel, inner_symPart_sub, add_zero] at e
      rw [← e]; exact h1
    exact inner_self_eq_zero.1 this
  have hK := norm_sq_sub_symPart v
  rw [h2, sub_zero] at hK
  have hb := norm_bgg_sq 0 v
  have : ‖v‖ ≤ ‖bgg 0 v‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    nlinarith [sq_nonneg ‖curl 0 v‖, sq_nonneg ‖v‖]
  linarith [norm_nonneg (bgg 0 v)]

open ShortHilbertComplex in
/-- **The fibre gaps of the BGG complex at every torus frequency**: `‖v‖ ≤ 4 ‖m_ξ v‖` on
`N(m_ξ)ᗮ` for `ξ = 0` or `|ξ| ≥ 2π`, for every arrow. -/
theorem bggFamily_gap (i j : Fin 3) {ξ : Freq} (hξ : ξ = 0 ∨ 2 * Real.pi ≤ ‖ξ‖) :
    ∀ v ∈ (LinearMap.ker (bggFamily.m i j ξ : W3 ℂ Mat VM i →ₗ[ℂ] W3 ℂ Mat VM j))ᗮ,
      ‖v‖ ≤ 4 * ‖bggFamily.m i j ξ v‖ := by
  have zero_case : ∀ {i j : Fin 3}, bggFamily.m i j ξ = 0 →
      ∀ v ∈ (LinearMap.ker (bggFamily.m i j ξ : W3 ℂ Mat VM i →ₗ[ℂ] W3 ℂ Mat VM j))ᗮ,
        ‖v‖ ≤ 4 * ‖bggFamily.m i j ξ v‖ := by
    intro i j h v hv
    rw [h] at hv
    rw [eq_zero_of_mem_orthogonal_ker_zero hv, norm_zero]; positivity
  fin_cases i <;> fin_cases j
  · exact zero_case rfl
  · rcases hξ with rfl | hξ
    · exact zero_case hessM_zero
    · intro c _
      change ‖(show ℂ from c)‖ ≤ 4 * ‖hessM ξ (show ℂ from c)‖
      rw [norm_hessM]
      have : (1 : ℝ) ≤ ‖ξ‖ ^ 2 := by nlinarith [Real.two_le_pi]
      nlinarith [norm_nonneg (show ℂ from c)]
  · exact zero_case rfl
  · exact zero_case rfl
  · exact zero_case rfl
  · rcases hξ with rfl | hξ
    · exact bgg_gap_zero
    · exact bgg_gap hξ
  · exact zero_case rfl
  · exact zero_case rfl
  · exact zero_case rfl

end Feec.Fourier.BGG
