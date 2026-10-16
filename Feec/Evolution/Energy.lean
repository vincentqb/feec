module

public import Feec.ForMathlib.Analysis.Gronwall
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Energy estimates

For a curve `e : ℝ → E` in an inner product space over `𝕜 = ℝ` or `ℂ`, continuous on `[a,b]`
with right derivative `e'` on `[a,b)`:

* `norm_le_add_integral_of_re_inner_deriv_le`: if `re ⟪e', e⟫ ≤ g ‖e‖` with `g ≥ 0` continuous,
  then `‖e t‖ ≤ ‖e a‖ + ∫ₐᵗ g`;
* `norm_le_of_re_inner_deriv_le`: the decay-rate form. If
  `re ⟪e', e⟫ ≤ -λ ‖e‖² + g ‖e‖` then `‖e t‖ ≤ e^{-λ(t-a)} ‖e a‖ + ∫ₐᵗ e^{-λ(t-s)} g s`
  (any `λ ∈ ℝ`; `λ > 0` is decay, `λ < 0` growth);
* `norm_le_add_integral_norm_deriv`: `‖e t‖ ≤ ‖e a‖ + ∫ₐᵗ ‖e'‖`, without completeness of `E`.

No completeness of `E` is needed: the proofs go through the square-root Gronwall inequality
`le_add_half_integral_of_sq_deriv_le_mul` applied to `‖e‖`, of which only `‖e‖²` is
differentiable.
-/

open Set

@[expose] public noncomputable section

namespace Feec.Evolution.Energy

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

omit [IsScalarTower ℝ 𝕜 E] in
/-- Right derivative of `‖e‖²` over `𝕜`: `d/dt ‖e‖² = 2 re ⟪e', e⟫`. -/
theorem hasDerivWithinAt_norm_sq {e : ℝ → E} {e' : E} {s : Set ℝ} {t : ℝ}
    (he : HasDerivWithinAt e e' s t) :
    HasDerivWithinAt (fun r => ‖e r‖ ^ 2) (2 * RCLike.re ⟪e', e t⟫) s t := by
  have h := (RCLike.reCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivWithinAt t (he.inner 𝕜 he)
  have heq : (fun r => ‖e r‖ ^ 2) = (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) ∘ fun r => ⟪e r, e r⟫ := by
    funext r; exact norm_sq_eq_re_inner (𝕜 := 𝕜) (e r)
  rw [heq]
  convert h using 1
  simp only [RCLike.reCLM_apply, map_add, inner_re_symm (𝕜 := 𝕜) (e t) e']
  ring

omit [IsScalarTower ℝ 𝕜 E] in
/-- **Energy estimate.** If `e` is continuous on `[a,b]` with right derivative `e'` on `[a,b)`
and `re ⟪e', e⟫ ≤ g ‖e‖` for some continuous `g ≥ 0`, then `‖e t‖ ≤ ‖e a‖ + ∫ₐᵗ g` on `[a,b]`.
Thesis: Lemma 4.12 (corrected). -/
theorem norm_le_add_integral_of_re_inner_deriv_le {e e' : ℝ → E} {g : ℝ → ℝ} {a b : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (hle : ∀ t ∈ Ico a b, RCLike.re ⟪e' t, e t⟫ ≤ g t * ‖e t‖) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ ‖e a‖ + ∫ s in a..t, g s := by
  intro t ht
  have := le_add_half_integral_of_sq_deriv_le_mul (Q := fun s => ‖e s‖)
    (q' := fun s => 2 * RCLike.re ⟪e' s, e s⟫) (F := fun s => 2 * g s) hec.norm
    (fun _ _ => norm_nonneg _) (fun s hs => hasDerivWithinAt_norm_sq (he s hs))
    (continuousOn_const.mul hgc) (fun s hs => by have := hg0 s hs; positivity)
    (fun s hs => by have := hle s hs; linarith) t ht
  rw [intervalIntegral.integral_const_mul] at this
  linarith

/-- **Energy estimate with decay rate `λ`.** If `e` is continuous on `[a,b]` with right
derivative `e'` on `[a,b)` and `re ⟪e', e⟫ ≤ -λ ‖e‖² + g ‖e‖` for some continuous `g ≥ 0`, then
`‖e t‖ ≤ e^{-λ(t-a)} ‖e a‖ + ∫ₐᵗ e^{-λ(t-s)} g s` on `[a,b]`. Any `λ ∈ ℝ` is allowed;
`λ = 0` is `norm_le_add_integral_of_re_inner_deriv_le`.
Thesis: Lemma 4.12 (corrected). -/
theorem norm_le_of_re_inner_deriv_le {e e' : ℝ → E} {g : ℝ → ℝ} {a b lam : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (hle : ∀ t ∈ Ico a b, RCLike.re ⟪e' t, e t⟫ ≤ -lam * ‖e t‖ ^ 2 + g t * ‖e t‖) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ Real.exp (-lam * (t - a)) * ‖e a‖ +
      ∫ s in a..t, Real.exp (-lam * (t - s)) * g s := by
  set c : ℝ → ℝ := fun s => Real.exp (lam * (s - a)) with hc
  have hcd : ∀ s, HasDerivAt c (c s * lam) s := fun s => by
    have := (((hasDerivAt_id s).sub_const a).const_mul lam).exp
    simpa [hc, mul_comm] using this
  have hcpos : ∀ s, 0 < c s := fun s => Real.exp_pos _
  set u : ℝ → E := fun s => c s • e s with hu
  set u' : ℝ → E := fun s => c s • e' s + (c s * lam) • e s with hu'
  have huc : ContinuousOn u (Icc a b) :=
    ((Real.continuous_exp.comp ((continuous_id.sub continuous_const).const_mul lam)).continuousOn
      ).smul hec
  have hud : ∀ t ∈ Ico a b, HasDerivWithinAt u (u' t) (Ici t) t := fun t ht =>
    ((hcd t).hasDerivWithinAt).smul (he t ht)
  have hnu : ∀ s, ‖u s‖ = c s * ‖e s‖ := fun s => by
    simp [hu, norm_smul, abs_of_pos (hcpos s)]
  have hre : ∀ s, RCLike.re ⟪u' s, u s⟫
      = c s ^ 2 * RCLike.re ⟪e' s, e s⟫ + c s ^ 2 * lam * ‖e s‖ ^ 2 := fun s => by
    simp only [hu, hu', RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_add_left, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul,
      ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
    ring
  have hbase := norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜) huc hud
    (g := fun s => c s * g s)
    ((Real.continuous_exp.comp ((continuous_id.sub continuous_const).const_mul lam)).continuousOn
      |>.mul hgc)
    (fun s hs => mul_nonneg (hcpos s).le (hg0 s hs))
    (fun s hs => by
      rw [hre, hnu]
      have h := mul_le_mul_of_nonneg_left (hle s hs) (sq_nonneg (c s))
      nlinarith)
  intro t ht
  have h := hbase t ht
  rw [hnu, hnu] at h
  have hca : c a = 1 := by simp [hc]
  rw [hca, one_mul] at h
  have hct : Real.exp (-lam * (t - a)) * c t = 1 := by
    rw [hc, ← Real.exp_add]; simp only [neg_mul, neg_add_cancel, Real.exp_zero]
  have hint : Real.exp (-lam * (t - a)) * ∫ s in a..t, c s * g s
      = ∫ s in a..t, Real.exp (-lam * (t - s)) * g s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hc, ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hpos := Real.exp_pos (-lam * (t - a))
  calc ‖e t‖ = Real.exp (-lam * (t - a)) * (c t * ‖e t‖) := by
        rw [← mul_assoc, hct, one_mul]
    _ ≤ Real.exp (-lam * (t - a)) * (‖e a‖ + ∫ s in a..t, c s * g s) :=
        mul_le_mul_of_nonneg_left h hpos.le
    _ = _ := by rw [mul_add, hint]

/-- `‖e t‖ ≤ ‖e a‖ + ∫ₐᵗ ‖e'‖` on `[a,b]` for `e` continuous on `[a,b]` with right derivative
`e'` continuous on `[a,b]`; `E` need not be complete. -/
theorem norm_le_add_integral_norm_deriv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {e e' : ℝ → F} {a b : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (he'c : ContinuousOn e' (Icc a b)) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ ‖e a‖ + ∫ s in a..t, ‖e' s‖ :=
  norm_le_add_integral_of_re_inner_deriv_le (𝕜 := ℝ) hec he he'c.norm
    (fun _ _ => norm_nonneg _) fun _ _ => (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)

end Feec.Evolution.Energy
