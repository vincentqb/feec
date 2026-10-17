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

## References

* [QuennevilleBelair2015], Ch. 5 (§5.1, (5.1)), Ch. 6 (§6.1, §6.3), §3.4 (Lemma 3.5)
* [ArnoldHu2021] (the BGG construction), [AFW2007] (weakly imposed symmetry)
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

end Feec.Fourier.BGG
