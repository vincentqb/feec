module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A square-root Gronwall inequality

If `Q ≥ 0` is continuous on `[a, b]` and `Q²` has right derivative `q' ≤ F Q` on `[a, b)`, with
`F ≥ 0` the right derivative of a continuous `G`, then `Q t ≤ Q a + (G t − G a) / 2`.

Only `Q²` is assumed differentiable: this is the form needed for `Q = ‖e‖`, which fails to be
differentiable where `e` vanishes. The proof compares `√(Q² + ε²)` with
`√(Q a ² + ε²) + (G − G a)/2` and lets `ε → 0`.

* `le_add_half_sub_of_sq_deriv_le_mul`: the primitive form.
* `le_add_half_integral_of_sq_deriv_le_mul`: the integral form `Q t ≤ Q a + ½ ∫ₐᵗ F`.
* `ContinuousOn.intervalIntegral_primitive_Icc`: the primitive of a function continuous on
  `[a, b]`.

## Energy estimates

For a curve `e : ℝ → E` in an inner product space over `𝕜 = ℝ` or `ℂ` (no completeness), continuous
on `[a,b]` with right derivative `e'` on `[a,b)`:

* `HasDerivWithinAt.norm_sq_re_inner`: `d/dt ‖e‖² = 2 re ⟪e', e⟫`;
* `norm_le_add_integral_of_re_inner_deriv_le`: if `re ⟪e', e⟫ ≤ g ‖e‖` with `g ≥ 0` continuous,
  then `‖e t‖ ≤ ‖e a‖ + ∫ₐᵗ g`;
* `norm_le_of_re_inner_deriv_le`: the decay-rate form. If `re ⟪e', e⟫ ≤ -λ ‖e‖² + g ‖e‖` then
  `‖e t‖ ≤ e^{-λ(t-a)} ‖e a‖ + ∫ₐᵗ e^{-λ(t-s)} g s` (any `λ ∈ ℝ`).

They follow from the square-root Gronwall inequality applied to `Q = ‖e‖`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

/-- **Square-root Gronwall inequality**, primitive form. If `Q ≥ 0` is continuous on `[a,b]`,
`Q²` has right derivative `q'` on `[a,b)`, `G` is continuous on `[a,b]` with right derivative
`F ≥ 0` on `[a,b)`, and `q' ≤ F Q`, then `Q t ≤ Q a + (G t − G a)/2` on `[a,b]`.
[QuennevilleBelair2015], Lemma 4.12 (corrected). -/
theorem le_add_half_sub_of_sq_deriv_le_mul {Q q' F G : ℝ → ℝ} {a b : ℝ}
    (hQc : ContinuousOn Q (Icc a b)) (hQ0 : ∀ t ∈ Icc a b, 0 ≤ Q t)
    (hq : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => Q s ^ 2) (q' t) (Ici t) t)
    (hGc : ContinuousOn G (Icc a b))
    (hG : ∀ t ∈ Ico a b, HasDerivWithinAt G (F t) (Ici t) t)
    (hF : ∀ t ∈ Ico a b, 0 ≤ F t)
    (hle : ∀ t ∈ Ico a b, q' t ≤ F t * Q t) :
    ∀ t ∈ Icc a b, Q t ≤ Q a + (G t - G a) / 2 := by
  intro t ht
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set f : ℝ → ℝ := fun s => Real.sqrt (Q s ^ 2 + ε ^ 2)
  have hpos : ∀ s, 0 < Q s ^ 2 + ε ^ 2 := fun s => by positivity
  have hfc : ContinuousOn f (Icc a b) :=
    ((hQc.pow 2).add continuousOn_const).sqrt
  have hf' : ∀ s ∈ Ico a b,
      HasDerivWithinAt f (q' s / (2 * Real.sqrt (Q s ^ 2 + ε ^ 2))) (Ici s) s := by
    intro s hs
    have := ((hq s hs).add_const (ε ^ 2)).sqrt (hpos s).ne'
    simpa using this
  have hB : ContinuousOn (fun s => Real.sqrt (Q a ^ 2 + ε ^ 2) + (G s - G a) / 2) (Icc a b) :=
    continuousOn_const.add ((hGc.sub continuousOn_const).div_const 2)
  have hB' : ∀ s ∈ Ico a b, HasDerivWithinAt
      (fun s => Real.sqrt (Q a ^ 2 + ε ^ 2) + (G s - G a) / 2) (F s / 2) (Ici s) s := by
    intro s hs
    simpa using (((hG s hs).sub_const (G a)).div_const 2).const_add (Real.sqrt (Q a ^ 2 + ε ^ 2))
  have bound : ∀ s ∈ Ico a b, q' s / (2 * Real.sqrt (Q s ^ 2 + ε ^ 2)) ≤ F s / 2 := by
    intro s hs
    have hQs : Q s ≤ Real.sqrt (Q s ^ 2 + ε ^ 2) := by
      calc Q s = Real.sqrt (Q s ^ 2) := (Real.sqrt_sq (hQ0 s (Ico_subset_Icc_self hs))).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
    rw [div_le_iff₀ (by positivity)]
    calc q' s ≤ F s * Q s := hle s hs
      _ ≤ F s * Real.sqrt (Q s ^ 2 + ε ^ 2) := mul_le_mul_of_nonneg_left hQs (hF s hs)
      _ = F s / 2 * (2 * Real.sqrt (Q s ^ 2 + ε ^ 2)) := by ring
  have key := image_le_of_deriv_right_le_deriv_boundary hfc hf' (by simp [f]) hB hB' bound ht
  have hQt : Q t ≤ f t := by
    calc Q t = Real.sqrt (Q t ^ 2) := (Real.sqrt_sq (hQ0 t ht)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have hQa := hQ0 a ⟨le_rfl, ht.1.trans ht.2⟩
  have hsq0 : Real.sqrt (Q a ^ 2 + ε ^ 2) ≤ Q a + ε := by
    rw [Real.sqrt_le_left]
    · nlinarith
    · positivity
  linarith

/-- Primitive of a function continuous on `[a,b]`: `t ↦ ∫ₐᵗ F` is continuous on `[a,b]` with
right derivative `F t` on `[a,b)` (the fundamental theorem of calculus within `[a,b]`). -/
theorem ContinuousOn.intervalIntegral_primitive_Icc {F : ℝ → ℝ} {a b : ℝ}
    (hFc : ContinuousOn F (Icc a b)) :
    ContinuousOn (fun t => ∫ s in a..t, F s) (Icc a b) ∧
      ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => ∫ s in a..t, F s) (F t) (Ici t) t := by
  have hd : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun t => ∫ s in a..t, F s) (F t) (Icc a b) t := fun t ht => by
    have : Fact (t ∈ Icc a b) := ⟨ht⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right
      ((hFc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
      (hFc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hFc t ht)
  refine ⟨fun t ht => (hd t ht).continuousWithinAt, fun t ht => ?_⟩
  exact (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))

/-- **Square-root Gronwall inequality**, integral form: `Q t ≤ Q a + ½ ∫ₐᵗ F` for `F ≥ 0`
continuous on `[a,b]` and `d/dt Q² ≤ F Q` on `[a,b)`.
[QuennevilleBelair2015], Lemma 4.12 (corrected). -/
theorem le_add_half_integral_of_sq_deriv_le_mul {Q q' F : ℝ → ℝ} {a b : ℝ}
    (hQc : ContinuousOn Q (Icc a b)) (hQ0 : ∀ t ∈ Icc a b, 0 ≤ Q t)
    (hq : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => Q s ^ 2) (q' t) (Ici t) t)
    (hFc : ContinuousOn F (Icc a b)) (hF : ∀ t ∈ Ico a b, 0 ≤ F t)
    (hle : ∀ t ∈ Ico a b, q' t ≤ F t * Q t) :
    ∀ t ∈ Icc a b, Q t ≤ Q a + (1 / 2) * ∫ s in a..t, F s := by
  intro t ht
  obtain ⟨hGc, hG⟩ := hFc.intervalIntegral_primitive_Icc
  have := le_add_half_sub_of_sq_deriv_le_mul hQc hQ0 hq hGc hG hF hle t ht
  simp only [intervalIntegral.integral_same, sub_zero] at this
  linarith

/-- **The constant `½` is sharp**: `Q t = t - a` and `F = 2` satisfy the hypotheses of
`le_add_half_integral_of_sq_deriv_le_mul` (`d/dt Q² = 2 (t - a) = F Q`), and the resulting bound
`Q t ≤ Q a + ½ ∫ₐᵗ F` is an equality for every `t`. [QuennevilleBelair2015], Lemma 4.12 (the remark after it). -/
theorem le_add_half_integral_of_sq_deriv_le_mul_sharp {a b : ℝ} :
    (∀ t ∈ Icc a b, t - a ≤ (a - a) + (1 / 2) * ∫ _ in a..t, (2 : ℝ)) ∧
      ∀ t : ℝ, t - a = (a - a) + (1 / 2) * ∫ _ in a..t, (2 : ℝ) := by
  refine ⟨le_add_half_integral_of_sq_deriv_le_mul (Q := fun t => t - a)
    (q' := fun t => 2 * (t - a)) (F := fun _ => (2 : ℝ)) (continuousOn_id.sub continuousOn_const)
    (fun t ht => sub_nonneg.2 ht.1)
    (fun t _ => by
      have h : HasDerivAt (fun s : ℝ => (s - a) ^ 2) (2 * (t - a)) t := by
        have := (hasDerivAt_pow 2 (t - a)).comp t ((hasDerivAt_id t).sub_const a)
        simpa [Function.comp_def] using this
      exact h.hasDerivWithinAt)
    continuousOn_const (fun _ _ => zero_le_two) (fun _ _ => le_rfl), fun t => ?_⟩
  simp; ring

/-! ### Energy estimates for curves in inner product spaces -/

section Energy

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

omit [IsScalarTower ℝ 𝕜 E] in
/-- Right derivative of `‖e‖²` over `𝕜`: `d/dt ‖e‖² = 2 re ⟪e', e⟫`. -/
theorem HasDerivWithinAt.norm_sq_re_inner {e : ℝ → E} {e' : E} {s : Set ℝ} {t : ℝ}
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
[QuennevilleBelair2015], Lemma 4.12 (corrected). -/
theorem norm_le_add_integral_of_re_inner_deriv_le {e e' : ℝ → E} {g : ℝ → ℝ} {a b : ℝ}
    (hec : ContinuousOn e (Icc a b)) (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (hgc : ContinuousOn g (Icc a b)) (hg0 : ∀ t ∈ Ico a b, 0 ≤ g t)
    (hle : ∀ t ∈ Ico a b, RCLike.re ⟪e' t, e t⟫ ≤ g t * ‖e t‖) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ ‖e a‖ + ∫ s in a..t, g s := by
  intro t ht
  have := le_add_half_integral_of_sq_deriv_le_mul (Q := fun s => ‖e s‖)
    (q' := fun s => 2 * RCLike.re ⟪e' s, e s⟫) (F := fun s => 2 * g s) hec.norm
    (fun _ _ => norm_nonneg _) (fun s hs => (he s hs).norm_sq_re_inner)
    (continuousOn_const.mul hgc) (fun s hs => by have := hg0 s hs; positivity)
    (fun s hs => by have := hle s hs; linarith) t ht
  rw [intervalIntegral.integral_const_mul] at this
  linarith

/-- **Energy estimate with decay rate `λ`.** If `e` is continuous on `[a,b]` with right
derivative `e'` on `[a,b)` and `re ⟪e', e⟫ ≤ -λ ‖e‖² + g ‖e‖` for some continuous `g ≥ 0`, then
`‖e t‖ ≤ e^{-λ(t-a)} ‖e a‖ + ∫ₐᵗ e^{-λ(t-s)} g s` on `[a,b]`. Any `λ ∈ ℝ` is allowed;
`λ = 0` is `norm_le_add_integral_of_re_inner_deriv_le`.
[QuennevilleBelair2015], Lemma 4.12 (corrected). -/
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

end Energy
