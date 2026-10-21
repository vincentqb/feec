module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Interval integrals: Fubini on a triangle, primitives on `[a,b]`

* `integral_integral_triangle_swap`: `∫ₐᵗ ∫ₐˢ k s r dr ds = ∫ₐᵗ ∫ᵣᵗ k s r ds dr` for `k` dominated
  by an integrable function of `r`.
* `hasDerivWithinAt_integral_of_continuousOn`: the primitive of a function continuous on `[a,b]`
  has derivative within `[a,b]`.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §4.1 (Fubini's theorem)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set MeasureTheory

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Fubini on a triangle**: for `a ≤ t` and `k` a.e.-measurable on `(a,t]²` with
`‖k s r‖ ≤ g r`, `g` integrable,
`∫ₐᵗ ∫ₐˢ k s r dr ds = ∫ₐᵗ ∫ᵣᵗ k s r ds dr`. -/
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

/-- The primitive of a function continuous on `[a,b]` has derivative within `[a,b]`. -/
theorem hasDerivWithinAt_integral_of_continuousOn {W : ℝ → E} {a b t : ℝ}
    (hW : ContinuousOn W (Icc a b)) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun τ => ∫ s in a..τ, W s) (W t) (Icc a b) t := by
  have hab : a ≤ b := ht.1.trans ht.2
  set W' : ℝ → E := fun s => W (projIcc a b hab s)
  have hW' : Continuous W' :=
    hW.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc a b hab s).2
  have e : ∀ τ ∈ Icc a b, ∫ s in a..τ, W s = ∫ s in a..τ, W' s := fun τ hτ =>
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le hτ.1] at hs
      simp [W', projIcc_of_mem hab ⟨hs.1, hs.2.trans hτ.2⟩]
  have hd := ((hW'.integral_hasStrictDerivAt a t).hasDerivAt).hasDerivWithinAt (s := Icc a b)
  rw [show W' t = W t by simp [W', projIcc_of_mem hab ht]] at hd
  exact hd.congr_of_mem e ht
