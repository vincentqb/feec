module

public import Feec.TimeStepping.Cayley
public import Feec.Semigroup.DissipativeInvariance

/-!
# θ-schemes through resolvents, and products of them

The θ-scheme `r_θ(τ A) = (1 + (1 - θ) τ A)(1 - θ τ A)⁻¹` through the resolvent: energy identity,
stability for m-dissipative `A`, `re θ ≥ 1/2`, constraint propagation and products of substeps.

## Main results

* `IsThetaStep.norm_sq_eq`: the discrete energy identity.
* `norm_thetaStep_le`: `‖r_θ(τ A)‖ ≤ 1` for every m-dissipative `A`, `re θ ≥ 1/2`, `τ > 0`.
* `thetaStep_mem_of_isReducing`: discrete constraint propagation.
* `norm_splitStep_le`: `‖∏ᵢ r_{θᵢ}(cᵢ τ Aᵢ)‖ ≤ 1` for m-dissipative `Aᵢ`, `re θᵢ ≥ 1/2`, `cᵢ > 0`,
  `τ > 0`.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 9
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.18

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Feec.Operator

@[expose] public noncomputable section

namespace Feec.TimeStepping

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {θ : 𝕜} {τ s : ℝ} {u u' : E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Resolvents in the right half-plane -/

theorem _root_.LinearPMap.IsMDissipative.isResolvent_of_re_pos [CompleteSpace E]
    (hA : A.IsMDissipative) {z : 𝕜} (hz : 0 < RCLike.re z) :
    IsResolvent A z (resolvent A z) := by
  set μ : ℝ := ‖z‖ ^ 2 / RCLike.re z
  have hμz : μ * RCLike.re z = ‖z‖ ^ 2 := div_mul_cancel₀ _ hz.ne'
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => by simp [h] at hz
  have hμ : 0 < μ := div_pos (by positivity) hz
  have hRμ := hA.isResolvent hμ
  set R := resolvent A (μ : 𝕜)
  set T : E →L[𝕜] E := ((μ : 𝕜) - z) • R
  have hT : ‖T‖ < 1 := by
    have h1 : ‖R‖ ≤ μ⁻¹ := hA.norm_resolvent_le hμ
    have hsq : ‖(μ : 𝕜) - z‖ ^ 2 = μ ^ 2 - ‖z‖ ^ 2 := by
      have h2 := RCLike.norm_sq_eq_def (z := z)
      rw [RCLike.norm_sq_eq_def]
      simp only [_root_.map_sub, RCLike.ofReal_re, RCLike.ofReal_im]
      linear_combination (-2) * hμz - h2
    have hlt : ‖(μ : 𝕜) - z‖ < μ := by
      have : ‖(μ : 𝕜) - z‖ ^ 2 < μ ^ 2 := by rw [hsq]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hμ.le this
    calc ‖T‖ ≤ ‖(μ : 𝕜) - z‖ * μ⁻¹ := by rw [norm_smul]; gcongr
      _ < μ * μ⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hμ.ne'
  set U := Units.oneSub T hT
  have hU : ∀ y, (↑U⁻¹ : E →L[𝕜] E) y - T ((↑U⁻¹ : E →L[𝕜] E) y) = y := fun y => by
    have h := congrArg (fun C : E →L[𝕜] E => C y) U.mul_inv
    simpa [U, Units.val_oneSub] using h
  have hU' : ∀ y, (↑U⁻¹ : E →L[𝕜] E) (y - T y) = y := fun y => by
    have h := congrArg (fun C : E →L[𝕜] E => C y) U.inv_mul
    simpa [U, Units.val_oneSub] using h
  have hR' : IsResolvent A z (R * ↑U⁻¹) :=
    { mem_domain := fun y => hRμ.mem_domain _
      sub_apply := fun y => by
        have h := hRμ.apply_resolvent ((↑U⁻¹ : E →L[𝕜] E) y)
        change z • R ((↑U⁻¹ : E →L[𝕜] E) y) - A (hRμ.toDomain ((↑U⁻¹ : E →L[𝕜] E) y)) = y
        rw [h]
        conv_rhs => rw [← hU y]
        simp only [T, _root_.smul_apply]
        module
      apply_sub := fun x => by
        have e : z • (x : E) - A x =
            ((μ : 𝕜) • (x : E) - A x) - T ((μ : 𝕜) • (x : E) - A x) := by
          simp only [T, _root_.smul_apply]
          rw [hRμ.apply_sub]
          module
        change R ((↑U⁻¹ : E →L[𝕜] E) _) = _
        rw [e, hU', hRμ.apply_sub] }
  exact hR'.isResolvent_resolvent

/-! ### θ-steps -/

/-- `u'` is a θ-step from `u`: `u' - u = τ A (θ u' + (1 - θ) u)` with `θ u' + (1 - θ) u ∈ D(A)`. -/
def IsThetaStep (A : E →ₗ.[𝕜] E) (θ : 𝕜) (τ : ℝ) (u u' : E) : Prop :=
  ∃ h : θ • u' + (1 - θ) • u ∈ A.domain, u' - u = (τ : 𝕜) • A ⟨θ • u' + (1 - θ) • u, h⟩

/-- The θ-scheme `r_θ(τ A) = (1 + (1 - θ) τ A)(1 - θ τ A)⁻¹`, through the resolvent of `A`. -/
def thetaStep (A : E →ₗ.[𝕜] E) (θ : 𝕜) (τ : ℝ) : E →L[𝕜] E :=
  (θ ^ 2 * (τ : 𝕜))⁻¹ • resolvent A (θ * (τ : 𝕜))⁻¹ - ((1 - θ) / θ) • 1

theorem cayley_eq_thetaStep (A : E →ₗ.[𝕜] E) (s : ℝ) :
    cayley A s = thetaStep A (1 / 2) (2 * s) := by
  unfold cayley thetaStep
  push_cast
  congr 2
  · ring
  · ring_nf
  · norm_num

theorem cayley_half_eq_thetaStep (A : E →ₗ.[𝕜] E) (τ : ℝ) :
    cayley A (τ / 2) = thetaStep A ((1 / 2 : ℝ) : 𝕜) τ := by
  rw [cayley_eq_thetaStep, show 2 * (τ / 2) = τ by ring]
  congr 1; push_cast; ring

theorem isCNStep_iff_isThetaStep :
    IsCNStep A s u u' ↔ IsThetaStep A (1 / 2) (2 * s) u u' := by
  have hw : (1 / 2 : 𝕜) • u' + (1 - 1 / 2 : 𝕜) • u = (1 / 2 : 𝕜) • (u' + u) := by module
  constructor
  · rintro ⟨h, e⟩
    have hm : (1 / 2 : 𝕜) • u' + (1 - 1 / 2 : 𝕜) • u ∈ A.domain := hw ▸ A.domain.smul_mem _ h
    refine ⟨hm, ?_⟩
    have : A ⟨_, hm⟩ = (1 / 2 : 𝕜) • A ⟨u' + u, h⟩ := by
      rw [← A.map_smul]; congr 1; exact Subtype.ext hw
    rw [this, smul_smul, e]; push_cast; congr 1; ring
  · rintro ⟨hm, e⟩
    have h : u' + u ∈ A.domain := by
      have := A.domain.smul_mem (2 : 𝕜) hm
      rwa [hw, smul_smul, show (2 : 𝕜) * (1 / 2) = 1 by norm_num, one_smul] at this
    refine ⟨h, ?_⟩
    have : A ⟨_, hm⟩ = (1 / 2 : 𝕜) • A ⟨u' + u, h⟩ := by
      rw [← A.map_smul]; congr 1; exact Subtype.ext hw
    rw [e, this, smul_smul]; push_cast; congr 1; ring

omit [InnerProductSpace 𝕜 E] in
open scoped RealInnerProductSpace in
theorem isDirichletCNStep_top_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {A : V →ₗ[ℝ] V} {g' w w' : V} :
    IsDirichletCNStep ⊤ A s 0 g' w w' ↔ IsCNStep (A.toPMap ⊤) s w w' := by
  constructor
  · rintro ⟨_, h⟩
    refine ⟨trivial, ext_inner_right ℝ fun v => ?_⟩
    rw [h v trivial, inner_zero_left, add_zero, real_inner_smul_left]
    rfl
  · rintro ⟨_, h⟩
    refine ⟨trivial, fun v _ => ?_⟩
    rw [h, inner_zero_left, add_zero, RCLike.ofReal_real_eq_id, id, real_inner_smul_left]
    rfl

theorem isThetaStep_thetaStep {R : E →L[𝕜] E} (hR : IsResolvent A (θ * (τ : 𝕜))⁻¹ R)
    (hθ : θ ≠ 0) (hτ : τ ≠ 0) (u : E) : IsThetaStep A θ τ u (thetaStep A θ τ u) := by
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ
  set r := hR.toDomain u
  have hr : (θ * (τ : 𝕜))⁻¹ • (r : E) - A r = u := hR.sub_apply_toDomain u
  have hw : θ • thetaStep A θ τ u + (1 - θ) • u = (θ * (τ : 𝕜))⁻¹ • (r : E) := by
    simp only [thetaStep, hR.resolvent_eq, _root_.sub_apply,
      _root_.smul_apply, one_apply_eq_self, smul_sub, smul_smul, r,
      IsResolvent.coe_toDomain]
    rw [show θ * (θ ^ 2 * (τ : 𝕜))⁻¹ = (θ * (τ : 𝕜))⁻¹ by field_simp,
      show θ * ((1 - θ) / θ) = 1 - θ by field_simp]
    abel
  refine ⟨hw ▸ A.domain.smul_mem _ r.2, ?_⟩
  have hA : A ⟨_, hw ▸ A.domain.smul_mem _ r.2⟩ = (θ * (τ : 𝕜))⁻¹ • A r := by
    rw [← A.map_smul]; congr 1; exact Subtype.ext hw
  rw [hA, smul_smul, show (τ : 𝕜) * (θ * (τ : 𝕜))⁻¹ = θ⁻¹ by field_simp]
  have e : A r = (θ * (τ : 𝕜))⁻¹ • (r : E) - u := by rw [← hr]; abel
  rw [e]
  simp only [thetaStep, hR.resolvent_eq, _root_.sub_apply,
    _root_.smul_apply, one_apply_eq_self, r, IsResolvent.coe_toDomain]
  rw [smul_sub, smul_smul, show θ⁻¹ * (θ * (τ : 𝕜))⁻¹ = (θ ^ 2 * (τ : 𝕜))⁻¹ by field_simp]
  have : ((1 - θ) / θ) • u + u = θ⁻¹ • u := by
    rw [← one_smul 𝕜 u, smul_smul, ← add_smul, mul_one, one_smul]
    congr 1; field_simp; ring
  rw [← this]; abel

private theorem norm_sq_add_smul (w d : E) (θ : 𝕜) :
    ‖w + (1 - θ) • d‖ ^ 2 =
      ‖w - θ • d‖ ^ 2 + 2 * RCLike.re ⟪w, d⟫ - (2 * RCLike.re θ - 1) * ‖d‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜), inner_smul_right, inner_smul_right, norm_smul,
    norm_smul, mul_pow, mul_pow]
  have h1 : ‖(1 : 𝕜) - θ‖ ^ 2 = 1 - 2 * RCLike.re θ + ‖θ‖ ^ 2 := by
    rw [RCLike.norm_sq_eq_def, RCLike.norm_sq_eq_def]
    simp only [_root_.map_sub, RCLike.one_re, RCLike.one_im]
    ring
  have h2 : RCLike.re ((1 - θ) * ⟪w, d⟫) = RCLike.re ⟪w, d⟫ - RCLike.re (θ * ⟪w, d⟫) := by
    rw [sub_mul, one_mul, _root_.map_sub]
  rw [h1, h2]
  ring

/-- **The discrete energy identity of a θ-step**: with `w = θ u' + (1 - θ) u`,
`‖u'‖² = ‖u‖² + 2 τ re ⟪A w, w⟫ - (2 re θ - 1) ‖u' - u‖²`. [Thomee2006], Ch. 7 -/
theorem IsThetaStep.norm_sq_eq (h : IsThetaStep A θ τ u u') :
    ‖u'‖ ^ 2 = ‖u‖ ^ 2 + 2 * τ * RCLike.re ⟪A ⟨_, h.1⟩, θ • u' + (1 - θ) • u⟫ -
      (2 * RCLike.re θ - 1) * ‖u' - u‖ ^ 2 := by
  obtain ⟨hm, e⟩ := h
  set w := θ • u' + (1 - θ) • u
  have h1 : u' = w + (1 - θ) • (u' - u) := by simp only [w]; module
  have h2 : u = w - θ • (u' - u) := by simp only [w]; module
  have h3 := norm_sq_add_smul w (u' - u) θ
  rw [← h1, ← h2] at h3
  rw [h3]
  have : RCLike.re ⟪w, u' - u⟫ = τ * RCLike.re ⟪A ⟨w, hm⟩, w⟫ := by
    rw [e, inner_smul_right, RCLike.re_ofReal_mul, inner_re_symm]
  rw [this]; ring

theorem IsThetaStep.norm_le (hA : A.IsDissipative) (hθ : 1 / 2 ≤ RCLike.re θ) (hτ : 0 ≤ τ)
    (h : IsThetaStep A θ τ u u') : ‖u'‖ ≤ ‖u‖ := by
  have e := h.norm_sq_eq
  have h1 : τ * RCLike.re ⟪A ⟨_, h.1⟩, θ • u' + (1 - θ) • u⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hτ (hA _)
  have h2 : 0 ≤ (2 * RCLike.re θ - 1) * ‖u' - u‖ ^ 2 := by
    apply mul_nonneg <;> [linarith; positivity]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

theorem IsThetaStep.norm_eq (hA : A.IsSkewSymmetric) (hθ : RCLike.re θ = 1 / 2)
    (h : IsThetaStep A θ τ u u') : ‖u'‖ = ‖u‖ := by
  have e := h.norm_sq_eq
  rw [hA.re_inner_self, hθ] at e
  have : ‖u'‖ ^ 2 = ‖u‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

theorem re_inv_mul_pos (hθ : 0 < RCLike.re θ) (hτ : 0 < τ) :
    0 < RCLike.re (θ * (τ : 𝕜))⁻¹ := by
  have hne : θ * (τ : 𝕜) ≠ 0 :=
    mul_ne_zero (fun h => by simp [h] at hθ) (RCLike.ofReal_ne_zero.2 hτ.ne')
  rw [RCLike.inv_re, RCLike.re_mul_ofReal]
  exact div_pos (mul_pos hθ hτ) (RCLike.normSq_pos.2 hne)

variable [CompleteSpace E]

theorem isThetaStep_thetaStep_of_isMDissipative (hA : A.IsMDissipative) (hθ : 0 < RCLike.re θ)
    (hτ : 0 < τ) (u : E) : IsThetaStep A θ τ u (thetaStep A θ τ u) :=
  isThetaStep_thetaStep (hA.isResolvent_of_re_pos (re_inv_mul_pos hθ hτ))
    (fun h => by simp [h] at hθ) hτ.ne' u

theorem norm_thetaStep_apply_le (hA : A.IsMDissipative) (hθ : 1 / 2 ≤ RCLike.re θ)
    (hτ : 0 < τ) (u : E) : ‖thetaStep A θ τ u‖ ≤ ‖u‖ :=
  (isThetaStep_thetaStep_of_isMDissipative hA (by linarith) hτ u).norm_le hA.dissipative hθ
    hτ.le

/-- `‖r_θ(τ A)‖ ≤ 1` for every m-dissipative `A`, `re θ ≥ 1/2`, `τ > 0`. -/
theorem norm_thetaStep_le (hA : A.IsMDissipative) (hθ : 1 / 2 ≤ RCLike.re θ) (hτ : 0 < τ) :
    ‖thetaStep A θ τ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_thetaStep_apply_le hA hθ hτ u

/-! ### The Cayley transform of an m-dissipative operator -/

private theorem re_half : RCLike.re (1 / 2 : 𝕜) = 1 / 2 := by
  rw [show (1 / 2 : 𝕜) = ((1 / 2 : ℝ) : 𝕜) by push_cast; ring, RCLike.ofReal_re]

theorem _root_.LinearPMap.IsMDissipative.isCNStep_cayley (hA : A.IsMDissipative) (hs : 0 < s)
    (u : E) : IsCNStep A s u (cayley A s u) := by
  rw [isCNStep_iff_isThetaStep, cayley_eq_thetaStep]
  exact isThetaStep_thetaStep_of_isMDissipative hA (by rw [re_half]; norm_num) (by linarith) u

theorem norm_cayley_le (hA : A.IsMDissipative) (hs : 0 < s) : ‖cayley A s‖ ≤ 1 := by
  rw [cayley_eq_thetaStep]
  exact norm_thetaStep_le hA (by rw [re_half]) (by linarith)

theorem cayley_sub_smul (hA : A.IsMDissipative) (hs : 0 < s) (x : A.domain) :
    cayley A s ((x : E) - (s : 𝕜) • A x) = x + (s : 𝕜) • A x := by
  have h2 : (x : E) + (s : 𝕜) • A x + ((x : E) - (s : 𝕜) • A x) = (2 : 𝕜) • (x : E) := by
    module
  have hm : (x : E) + (s : 𝕜) • A x + ((x : E) - (s : 𝕜) • A x) ∈ A.domain :=
    h2 ▸ A.domain.smul_mem _ x.2
  have hstep : IsCNStep A s ((x : E) - (s : 𝕜) • A x) (x + (s : 𝕜) • A x) := by
    refine ⟨hm, ?_⟩
    have : A ⟨_, hm⟩ = (2 : 𝕜) • A x :=
      (congrArg A (Subtype.ext h2 : (⟨_, hm⟩ : A.domain) = (2 : 𝕜) • x)).trans (A.map_smul _ _)
    rw [this]; module
  exact (hA.isCNStep_cayley hs _).unique hA.dissipative hs.le hstep

theorem eq_cayley_of_apply_sub_smul (hA : A.IsMDissipative) (hs : 0 < s) {T : E →L[𝕜] E}
    (hT : ∀ x : A.domain, T ((x : E) - (s : 𝕜) • A x) = x + (s : 𝕜) • A x) : T = cayley A s := by
  ext u
  obtain ⟨hw, e⟩ := hA.isCNStep_cayley hs u
  set x : A.domain := (2 : 𝕜)⁻¹ • ⟨_, hw⟩
  have hAx : A x = (2 : 𝕜)⁻¹ • A ⟨_, hw⟩ := A.map_smul _ _
  have hx : (x : E) = (2 : 𝕜)⁻¹ • (cayley A s u + u) := rfl
  have h1 : (x : E) - (s : 𝕜) • A x = u := by
    rw [hAx, hx, smul_comm, ← e]; module
  have h2 : (x : E) + (s : 𝕜) • A x = cayley A s u := by
    rw [hAx, hx, smul_comm, ← e]; module
  rw [← h1, hT, h2, h1]

theorem apply_sub_smul_eq_iff (hA : A.IsMDissipative) {τ : ℝ} (hτ : 0 < τ) (T : E →L[𝕜] E) :
    (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x) ↔
      T = (τ : 𝕜)⁻¹ • resolvent A (τ : 𝕜)⁻¹ := by
  have hR : IsResolvent A (τ : 𝕜)⁻¹ (resolvent A (τ : 𝕜)⁻¹) :=
    hA.isResolvent_of_re_pos (by rw [← RCLike.ofReal_inv, RCLike.ofReal_re]; positivity)
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ.ne'
  have e : ∀ x : A.domain, (x : E) - (τ : 𝕜) • A x = (τ : 𝕜) • ((τ : 𝕜)⁻¹ • (x : E) - A x) :=
    fun x => by rw [smul_sub, smul_smul, mul_inv_cancel₀ hτ', one_smul]
  have hS : ∀ x : A.domain, ((τ : 𝕜)⁻¹ • resolvent A (τ : 𝕜)⁻¹) ((x : E) - (τ : 𝕜) • A x) = x :=
    fun x => by
      rw [e, _root_.smul_apply, _root_.map_smul, hR.apply_sub, smul_smul, inv_mul_cancel₀ hτ',
        one_smul]
  refine ⟨fun hT => ?_, fun h => h ▸ hS⟩
  ext y
  have hy : y = (hR.toDomain ((τ : 𝕜)⁻¹ • y) : E) -
      (τ : 𝕜) • A (hR.toDomain ((τ : 𝕜)⁻¹ • y)) := by
    rw [e, hR.coe_toDomain, hR.sub_apply_toDomain, smul_smul, mul_inv_cancel₀ hτ', one_smul]
  rw [hy, hT, hS]

theorem norm_thetaStep_apply_eq (hA : A.IsSkewAdjoint) (hθ : RCLike.re θ = 1 / 2) (hτ : τ ≠ 0)
    (u : E) : ‖thetaStep A θ τ u‖ = ‖u‖ := by
  have hθ0 : θ ≠ 0 := fun h => by simp [h] at hθ
  have hne : θ * (τ : 𝕜) ≠ 0 := mul_ne_zero hθ0 (RCLike.ofReal_ne_zero.2 hτ)
  have hre : RCLike.re (θ * (τ : 𝕜))⁻¹ ≠ 0 := by
    rw [RCLike.inv_re, RCLike.re_mul_ofReal, hθ]
    exact div_ne_zero (mul_ne_zero (by norm_num) hτ) (RCLike.normSq_pos.2 hne).ne'
  exact (isThetaStep_thetaStep (Operator.isResolvent_resolvent hA hre) hθ0 hτ u).norm_eq
    hA.isSkewSymmetric hθ

/-! ### Discrete constraint propagation -/

omit [CompleteSpace E] in
theorem thetaStep_mem {K : Submodule 𝕜 E} (hK : ∀ y ∈ K, resolvent A (θ * (τ : 𝕜))⁻¹ y ∈ K)
    (hu : u ∈ K) : thetaStep A θ τ u ∈ K := by
  simp only [thetaStep, _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self]
  exact K.sub_mem (K.smul_mem _ (hK u hu)) (K.smul_mem _ hu)

omit [CompleteSpace E] in
theorem _root_.Feec.Operator.IsResolvent.apply_mem_of_isReducing {z : 𝕜} {R : E →L[𝕜] E}
    (hR : IsResolvent A z R) {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (hK : A.IsReducing K) {y : E} (hy : y ∈ K) : R y ∈ K := by
  set x := hR.toDomain y
  have key : z • (x : E) - A x = y := hR.sub_apply_toDomain y
  have hPx : z • K.starProjection (x : E) - A ⟨_, hK.proj_mem x⟩ = y := by
    rw [hK.comm x, ← ContinuousLinearMap.map_smul, ← _root_.map_sub, key,
      (K.starProjection_eq_self_iff).2 hy]
  have h2 : R (z • K.starProjection (x : E) - A ⟨_, hK.proj_mem x⟩) = K.starProjection x :=
    hR.apply_sub ⟨_, hK.proj_mem x⟩
  rw [hPx] at h2
  rw [h2]
  exact K.starProjection_apply_mem _

/-- **Discrete constraint propagation for reducing subspaces**: if `K` reduces the m-dissipative
`A`, `r_θ(τ A) K ⊆ K` (`re θ > 0`, `τ > 0`). [QuennevilleBelair2015], Prop 4.18 (adapted) -/
theorem thetaStep_mem_of_isReducing (hA : A.IsMDissipative) (hθ : 0 < RCLike.re θ) (hτ : 0 < τ)
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] (hK : A.IsReducing K) (hu : u ∈ K) :
    thetaStep A θ τ u ∈ K :=
  thetaStep_mem (fun _ hy =>
    (hA.isResolvent_of_re_pos (re_inv_mul_pos hθ hτ)).apply_mem_of_isReducing hK hy) hu

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

theorem thetaStep_mem_of_keeps (hA : A.IsMDissipative) {K : Submodule 𝕜 E}
    (hKc : IsClosed (K : Set E)) (hK : ∀ t, 0 ≤ t → ∀ x ∈ K, hA.semigroup.S t x ∈ K) {θ : ℝ}
    (hθ : 0 < θ) (hτ : 0 < τ) (hu : u ∈ K) : thetaStep A (θ : 𝕜) τ u ∈ K := by
  refine thetaStep_mem (fun y hy => ?_) hu
  have := (hA.invariant_iff_resolvent hKc).1 hK (θ * τ)⁻¹ (by positivity) y hy
  simpa using this

/-! ### Products of θ-substeps: composite rational schemes and splittings -/

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] in
/-- A product `∏ᵢ r_{θᵢ}(cᵢ τ Aᵢ)` of θ-substeps, the first applied last. [Thomee2006], Ch. 9 -/
def splitStep (σ : List ((E →ₗ.[𝕜] E) × 𝕜 × ℝ)) (τ : ℝ) : E →L[𝕜] E :=
  (σ.map fun p => thetaStep p.1 p.2.1 (p.2.2 * τ)).prod

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **Products of A-stable θ-substeps of m-dissipative operators are contractions**:
`‖∏ᵢ r_{θᵢ}(cᵢ τ Aᵢ)‖ ≤ 1` when every `Aᵢ` is m-dissipative, `re θᵢ ≥ 1/2`, `cᵢ > 0`, `τ > 0`. -/
theorem norm_splitStep_le {σ : List ((E →ₗ.[𝕜] E) × 𝕜 × ℝ)}
    (hσ : ∀ p ∈ σ, p.1.IsMDissipative ∧ 1 / 2 ≤ RCLike.re p.2.1 ∧ 0 < p.2.2) (hτ : 0 < τ) :
    ‖splitStep σ τ‖ ≤ 1 := by
  induction σ with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons p σ ih =>
    have hp := hσ p (List.mem_cons_self ..)
    simp only [splitStep, List.map_cons, List.prod_cons] at ih ⊢
    refine (norm_mul_le _ _).trans ?_
    have h1 := norm_thetaStep_le hp.1 hp.2.1 (mul_pos hp.2.2 hτ)
    have h2 := ih fun q hq => hσ q (List.mem_cons_of_mem _ hq)
    nlinarith [norm_nonneg (thetaStep p.1 p.2.1 (p.2.2 * τ)),
      norm_nonneg (σ.map fun p => thetaStep p.1 p.2.1 (p.2.2 * τ)).prod]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem splitStep_mem_of_isReducing {σ : List ((E →ₗ.[𝕜] E) × 𝕜 × ℝ)}
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (hσ : ∀ p ∈ σ, p.1.IsMDissipative ∧ 0 < RCLike.re p.2.1 ∧ 0 < p.2.2 ∧ p.1.IsReducing K)
    (hτ : 0 < τ) (hu : u ∈ K) : splitStep σ τ u ∈ K := by
  induction σ generalizing u with
  | nil => simpa [splitStep] using hu
  | cons p σ ih =>
    have hp := hσ p (List.mem_cons_self ..)
    simp only [splitStep, List.map_cons, List.prod_cons] at ih ⊢
    exact thetaStep_mem_of_isReducing hp.1 hp.2.1 (mul_pos hp.2.2.1 hτ) hp.2.2.2
      (ih (fun q hq => hσ q (List.mem_cons_of_mem _ hq)) hu)

end Feec.TimeStepping
