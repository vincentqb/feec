module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Interval integrals: Fubini on a triangle, primitives on `[a,b]`, the Laplace identity

Fubini's theorem on a triangle, `∫ₐᵗ ∫ₐˢ k s r dr ds = ∫ₐᵗ ∫ᵣᵗ k s r ds dr` for `k` dominated by an
integrable function of `r`, derivatives of primitives within `[a,b]`, and
`∫₀ᵀ e⁻ˢ (u s - u' s) ds = u 0 - e⁻ᵀ u T` for `u`, `u'` continuous on `[0, T]`.
-/

open Set MeasureTheory

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_integral_triangle_swap {k : ℝ → ℝ → E} {g : ℝ → ℝ} {a t : ℝ} (hat : a ≤ t)
    (hk : AEStronglyMeasurable (Function.uncurry k)
      ((volume.restrict (Ioc a t)).prod (volume.restrict (Ioc a t))))
    (hg : IntegrableOn g (Ioc a t)) (hb : ∀ s ∈ Ioc a t, ∀ r ∈ Ioc a t, ‖k s r‖ ≤ g r) :
    ∫ s in a..t, ∫ r in a..s, k s r = ∫ r in a..t, ∫ s in r..t, k s r := by
  set μ := volume.restrict (Ioc a t)
  set K : ℝ → ℝ → E := fun s r => if r ≤ s then k s r else 0 with hK
  have hKi : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine Integrable.mono' (hg.comp_snd μ) ?_ ?_
    · have : Function.uncurry K = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (Function.uncurry k) := by
        ext ⟨s, r⟩; simp [hK, Set.indicator, Function.uncurry]
      rw [this]
      exact hk.indicator (measurableSet_le measurable_snd measurable_fst)
    · filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (μ := volume) measurableSet_Ioc), Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (μ := volume) measurableSet_Ioc)] with p hp hp'
      simp only [Function.uncurry, hK]
      split_ifs
      · exact hb _ hp _ hp'
      · simpa using (norm_nonneg _).trans (hb p.1 hp p.2 hp')
  have hL : ∀ s ∈ Ioc a t, ∫ r in a..s, k s r = ∫ r, K s r ∂μ := fun s hs => by
    rw [intervalIntegral.integral_of_le hs.1.le]
    have : (fun r => K s r) = (Iic s).indicator (k s) := by
      ext r; simp [hK, Set.indicator]
    rw [this, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hs.2]
  have hR : ∀ r ∈ Ioc a t, ∫ s in r..t, k s r = ∫ s, K s r ∂μ := fun r hr => by
    rw [intervalIntegral.integral_of_le hr.2, ← integral_Icc_eq_integral_Ioc]
    have : (fun s => K s r) = (Ici r).indicator (fun s => k s r) := by
      ext s; simp [hK, Set.indicator]
    have e : Ioc a t ∩ Ici r = Icc r t := by
      ext s; simp only [mem_Icc, mem_inter_iff, mem_Ioc, mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hr.1.trans_le h1, h2⟩, h1⟩
    rw [this, setIntegral_indicator measurableSet_Ici, e]
  rw [intervalIntegral.integral_of_le hat, intervalIntegral.integral_of_le hat,
    setIntegral_congr_fun measurableSet_Ioc hL, setIntegral_congr_fun measurableSet_Ioc hR]
  exact integral_integral_swap hKi

variable [CompleteSpace E]

theorem hasDerivWithinAt_integral_of_continuousOn {W : ℝ → E} {a b t : ℝ}
    (hW : ContinuousOn W (Icc a b)) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun τ => ∫ s in a..τ, W s) (W t) (Icc a b) t := by
  have : Fact (t ∈ Icc a b) := ⟨ht⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hW.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
    (hW.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hW t ht)

theorem integral_exp_neg_smul_sub_eq {u w : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hu : ContinuousOn u (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ s ∈ Ico 0 T, HasDerivWithinAt u (w s) (Ici s) s) :
    ∫ s in (0 : ℝ)..T, Real.exp (-s) • (u s - w s) = u 0 - Real.exp (-T) • u T := by
  have he : Continuous fun s : ℝ => Real.exp (-s) := Real.continuous_exp.comp continuous_neg
  have hf : ∀ s ∈ Ioo 0 T, HasDerivWithinAt (fun s => Real.exp (-s) • u s)
      (-(Real.exp (-s) • (u s - w s))) (Ioi s) s := fun s hs => by
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by
      simpa using (hasDerivAt_neg s).exp
    convert h1.hasDerivWithinAt.smul ((hd s ⟨hs.1.le, hs.2⟩).mono Ioi_subset_Ici_self) using 1
    module
  have hint := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
    (he.continuousOn.smul hu) hf
    ((he.continuousOn.smul (hu.sub hw)).neg.intervalIntegrable_of_Icc hT)
  rw [intervalIntegral.integral_neg, neg_eq_iff_eq_neg] at hint
  rw [hint]
  simp only [Pi.smul_apply', neg_zero, Real.exp_zero, one_smul, neg_sub]
