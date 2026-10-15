module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Function.L2Space
public import Feec.Ch4.Stone
public import Feec.Ch4.Duhamel

/-!
# Duhamel's formula for `W^{1,1}`-in-time forcing

For a strongly continuous orthogonal group `S(t) = e^{tA}` (`Feec.UnitaryGroupGenerator A`) and a
forcing `F : [0,T] → X` that is continuous, differentiable off a countable set, and has an
integrable derivative `F'` (so `F(t) = F(0) + ∫₀ᵗ F'`, i.e. `F ∈ W^{1,1}(0,T; X)`), the Duhamel
formula `U(t) = S(t) U₀ + S(t) ∫₀ᵗ S(-s) F(s) ds` is a classical solution of `U' = A U + F`,
`U(0) = U₀`, for every `U₀ ∈ D(A)`. No regularity of `F` in `D(A)` is needed: the integral lies in
`D(A)` by an integration by parts against the adjoint,
`A ∫₀ᵗ S(-s) F(s) ds = F(0) - S(-t) F(t) + ∫₀ᵗ S(-s) F'(s) ds`.

This is the `W^{1,1}` branch of the forcing class of [QuennevilleBelair2015, Thm 4.3]; the
`C([0,T]; D(A))` branch is `UnitaryGroupGenerator.wellPosedClassical_forcing`
(`Feec.Ch4.Duhamel`). The two are combined in `ForcingThm43`.

## Main results

* `UnitaryGroupGenerator.integral_mem_domain_of_hasDerivAt`: the integration-by-parts identity.
* `ForcingW11`, `UnitaryGroupGenerator.wellPosedClassical_W11`: classical solutions for
  `W^{1,1}`-type forcing.
* `ForcingThm43`, `UnitaryGroupGenerator.wellPosedClassical_thm43`: classical solutions for
  `C([0,T]; D(A)) ∪ ForcingW11`.

Correction: `ForcingW11` asks for a derivative at every point of `(0,T)` off a countable set, with
`F'` integrable. Such `F` lie in `C([0,T]; X) ∩ W^{1,1}(0,T; X)`, but a general `W^{1,1}` function
is only differentiable almost everywhere, so this is a (large) subclass of the thesis' class; it
contains `C¹([0,T]; X)` and piecewise-`C¹` forcing.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3)
* [Pazy1983], §4.2 (Cor 4.2.5: `f ∈ W^{1,1}` gives a classical solution)
* [CazenaveHaraux1998], Prop 4.1.6
-/

open scoped RealInnerProductSpace LinearPMap
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

namespace UnitaryGroupGenerator

variable (G : UnitaryGroupGenerator A)

omit [CompleteSpace E] in
/-- `s ↦ S(φ s) (g s)` is interval integrable if `g` is and `φ` is continuous (`S` is an isometry
and jointly continuous). -/
theorem intervalIntegrable_apply {g : ℝ → E} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntervalIntegrable (fun s => G.S (φ s) (g s)) volume a b := by
  have hm : ∀ μ : Measure ℝ, AEStronglyMeasurable g μ →
      AEStronglyMeasurable (fun s => G.S (φ s) (g s)) μ := fun μ h =>
    G.continuous_uncurry.comp_aestronglyMeasurable (hφ.aestronglyMeasurable.prodMk h)
  refine hg.norm.mono_fun' ?_ (Eventually.of_forall fun s => (G.norm_map _ _).le)
  rw [uIoc]
  exact hm _ (hg.def'.aestronglyMeasurable)

/-- **Integration by parts against the generator.** If `F` is continuous on `[0,t]`,
differentiable off a countable set with integrable derivative `F'`, then
`∫₀ᵗ S(-s) F(s) ds ∈ D(A)` and
`A ∫₀ᵗ S(-s) F(s) ds = F(0) + ∫₀ᵗ S(-s) F'(s) ds - S(-t) F(t)`.
Proof: for `z ∈ D(A)`, `⟪∫₀ᵗ S(-s) F(s) ds, A z⟫ = ⟪S(-t) F(t) - F(0) - ∫₀ᵗ S(-s) F'(s) ds, z⟫`
(fundamental theorem of calculus for `s ↦ ⟪S(s) z, F(s)⟫`), so the integral lies in
`D(A†) = D(A)`. Cf. [Pazy1983, §4.2, Thm 4.2.4]. -/
theorem integral_mem_domain_of_hasDerivAt {F F' : ℝ → E} {t : ℝ} (ht : 0 ≤ t) {s : Set ℝ}
    (hs : s.Countable) (hF : ContinuousOn F (Icc 0 t))
    (hd : ∀ x ∈ Ioo 0 t \ s, HasDerivAt F (F' x) x) (hi : IntervalIntegrable F' volume 0 t) :
    ∃ h : (∫ r in (0 : ℝ)..t, G.S (-r) (F r)) ∈ A.domain,
      A ⟨_, h⟩ = F 0 + (∫ r in (0 : ℝ)..t, G.S (-r) (F' r)) - G.S (-t) (F t) := by
  have hA : IsSkewAdjoint A := G.isSkewAdjoint
  set w := ∫ r in (0 : ℝ)..t, G.S (-r) (F r) with hw
  set I := ∫ r in (0 : ℝ)..t, G.S (-r) (F' r) with hI
  have hwc : ContinuousOn (fun r => G.S (-r) (F r)) (Icc 0 t) :=
    G.continuous_uncurry.comp_continuousOn (continuous_neg.continuousOn.prodMk hF)
  have hwi : IntervalIntegrable (fun r => G.S (-r) (F r)) volume 0 t :=
    hwc.intervalIntegrable_of_Icc ht
  have hIi : IntervalIntegrable (fun r => G.S (-r) (F' r)) volume 0 t :=
    G.intervalIntegrable_apply hi continuous_neg
  have key : ∀ z : A.domain, ⟪G.S (-t) (F t) - F 0 - I, (z : E)⟫ = ⟪w, A z⟫ := by
    intro z
    have hfd : ∀ x ∈ Ioo 0 t \ s, HasDerivAt (fun τ => ⟪G.S τ z, F τ⟫)
        (⟪(z : E), G.S (-x) (F' x)⟫ + ⟪A z, G.S (-x) (F x)⟫) x := by
      intro x hx
      have := (G.hasDerivAt_apply z x).inner ℝ (hd x hx)
      convert this using 1
      rw [G.inner_S_left, G.inner_S_left, add_comm]
    have hfc : ContinuousOn (fun τ => ⟪G.S τ z, F τ⟫) (Icc 0 t) :=
      (G.continuous_apply _).continuousOn.inner hF
    have h1 : IntervalIntegrable (fun x => ⟪(z : E), G.S (-x) (F' x)⟫) volume 0 t :=
      ⟨(hIi.1.const_inner _), (hIi.2.const_inner _)⟩
    have h2 : IntervalIntegrable (fun x => ⟪A z, G.S (-x) (F x)⟫) volume 0 t :=
      ⟨(hwi.1.const_inner _), (hwi.2.const_inner _)⟩
    have hftc := integral_eq_of_hasDerivAt_off_countable_of_le _ _ ht hs hfc hfd (h1.add h2)
    rw [intervalIntegral.integral_add h1 h2] at hftc
    have e1 : (∫ x in (0 : ℝ)..t, ⟪(z : E), G.S (-x) (F' x)⟫) = ⟪(z : E), I⟫ := by
      have := (innerSL ℝ (z : E)).intervalIntegral_comp_comm hIi
      simpa only [innerSL_apply_apply] using this
    have e2 : (∫ x in (0 : ℝ)..t, ⟪A z, G.S (-x) (F x)⟫) = ⟪A z, w⟫ := by
      have := (innerSL ℝ (A z)).intervalIntegral_comp_comm hwi
      simpa only [innerSL_apply_apply] using this
    rw [e1, e2, G.inner_S_left, G.map_zero, one_apply_eq_self] at hftc
    rw [inner_sub_left, inner_sub_left]
    linarith [real_inner_comm (z : E) I, real_inner_comm (A z) w,
      real_inner_comm (z : E) (G.S (-t) (F t)), real_inner_comm (z : E) (F 0)]
  obtain ⟨hmem, hval⟩ := hA.mem_domain_of_adjoint key
  exact ⟨hmem, by rw [hval]; abel⟩

end UnitaryGroupGenerator

/-- The `W^{1,1}`-type forcing class: `F` continuous on `[0,T]`, differentiable at every point of
`(0,T)` off a countable set, with an interval-integrable derivative `F'`. Contains
`C¹([0,T]; X)`; contained in `C([0,T]; X) ∩ W^{1,1}(0,T; X)`. -/
def ForcingW11 (T : ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Icc 0 T) ∧ ∃ (F' : ℝ → E) (s : Set ℝ), s.Countable ∧
    IntervalIntegrable F' volume 0 T ∧ ∀ t ∈ Ioo 0 T \ s, HasDerivAt F (F' t) t

namespace UnitaryGroupGenerator

variable (G : UnitaryGroupGenerator A)

include G in
/-- **Thesis Thm 4.3 (existence), `W^{1,1}` forcing**: for `U₀ ∈ D(A)` and `F ∈ ForcingW11 T`
there is a classical solution `U ∈ C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)` of `U' = A U + F`,
`U(0) = U₀`, namely Duhamel's `U(t) = S(t) U₀ + S(t) ∫₀ᵗ S(-s) F(s) ds`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2, Cor 4.2.5],
[CazenaveHaraux1998, Prop 4.1.6]. -/
theorem wellPosedClassical_W11 (T : ℝ) : WellPosedClassical A T (ForcingW11 T) := by
  rintro U₀ hU₀ F ⟨hFc, F', s, hs, hi, hd⟩
  by_cases hT : 0 ≤ T
  · set P := projIcc 0 T hT
    set Fe : ℝ → E := fun r => F (P r) with hFe
    have hFe_c : Continuous Fe :=
      hFc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun r => (P r).2
    have hP : ∀ t ∈ Icc 0 T, Fe t = F t := fun t ht => by
      simp only [Fe, P, projIcc_of_mem hT ht]
    set w : ℝ → E := fun t => ∫ r in (0 : ℝ)..t, G.S (-r) (Fe r) with hw_def
    have hg : Continuous fun r => G.S (-r) (Fe r) :=
      G.continuous_uncurry.comp (continuous_neg.prodMk hFe_c)
    have hw : ∀ t, HasDerivAt w (G.S (-t) (Fe t)) t := fun t =>
      (hg.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hIB : ∀ t ∈ Icc 0 T, ∃ h : w t ∈ A.domain,
        A ⟨w t, h⟩ = Fe 0 + (∫ r in (0 : ℝ)..t, G.S (-r) (F' r)) - G.S (-t) (Fe t) := by
      intro t ht
      refine G.integral_mem_domain_of_hasDerivAt ht.1 hs hFe_c.continuousOn (fun x hx => ?_)
        (hi.mono_set ?_)
      · have hxT : x ∈ Ioo 0 T := ⟨hx.1.1, hx.1.2.trans_le ht.2⟩
        refine (hd x ⟨hxT, hx.2⟩).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hxT.1 hxT.2] with y hy
        exact hP y (Ioo_subset_Icc_self hy)
      · rw [uIcc_of_le ht.1, uIcc_of_le hT]
        exact Icc_subset_Icc le_rfl ht.2
    choose mem hAw using hIB
    have hU : ∀ t (ht : t ∈ Icc 0 T), G.S t U₀ + G.S t (w t) ∈ A.domain := fun t ht =>
      A.domain.add_mem (G.mem_domain_apply ⟨U₀, hU₀⟩ t) (G.mem_domain_apply ⟨w t, mem t ht⟩ t)
    have hval : ∀ t (ht : t ∈ Icc 0 T), A ⟨_, hU t ht⟩ = G.S t (A ⟨U₀, hU₀⟩) +
        G.S t (Fe 0 + (∫ r in (0 : ℝ)..t, G.S (-r) (F' r)) - G.S (-t) (Fe t)) := by
      intro t ht
      have e : (⟨_, hU t ht⟩ : A.domain) = ⟨_, G.mem_domain_apply ⟨U₀, hU₀⟩ t⟩ +
          ⟨_, G.mem_domain_apply ⟨w t, mem t ht⟩ t⟩ := rfl
      rw [e, LinearPMap.map_add, G.apply_comm, G.apply_comm, hAw t ht]
    -- continuity of the right-hand side of `hval` on `[0,T]`
    have hIc : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, G.S (-r) (F' r)) (Icc 0 T) := by
      have h := intervalIntegral.continuousOn_primitive_interval
        (μ := volume) (a := 0) (b := T) (f := fun r => G.S (-r) (F' r))
        (by rw [uIcc_of_le hT, ← intervalIntegrable_iff_integrableOn_Icc_of_le hT]
            exact G.intervalIntegrable_apply hi continuous_neg)
      rwa [uIcc_of_le hT] at h
    have hvc : ContinuousOn (fun t => Fe 0 + (∫ r in (0 : ℝ)..t, G.S (-r) (F' r)) -
        G.S (-t) (Fe t)) (Icc 0 T) :=
      (continuousOn_const.add hIc).sub
        (G.continuous_uncurry.comp (continuous_neg.prodMk hFe_c)).continuousOn
    have hGc : ContinuousOn (fun t => G.S t (A ⟨U₀, hU₀⟩) +
        G.S t (Fe 0 + (∫ r in (0 : ℝ)..t, G.S (-r) (F' r)) - G.S (-t) (Fe t))) (Icc 0 T) :=
      (G.continuous_apply _).continuousOn.add
        (G.continuous_uncurry.comp_continuousOn (continuousOn_id.prodMk hvc))
    refine ⟨fun τ => G.S τ U₀ + G.S τ (w τ), ⟨hU, fun t ht => ?_, ?_⟩,
      ⟨_, hGc, hval⟩, ⟨_, hGc.add hFc, fun t ht => by rw [hval t ht]; rfl⟩⟩
    · have h1 := G.hasDerivAt_apply ⟨U₀, hU₀⟩ t
      have h2 := G.hasDerivAt_apply_comp (hw t) (G.hasDerivAt_apply ⟨w t, mem t ht⟩ t)
      have h3 := (h1.add h2).hasDerivWithinAt (s := Icc 0 T)
      convert h3 using 1
      have e : (⟨_, hU t ht⟩ : A.domain) = ⟨_, G.mem_domain_apply ⟨U₀, hU₀⟩ t⟩ +
          ⟨_, G.mem_domain_apply ⟨w t, mem t ht⟩ t⟩ := rfl
      have hinv : G.S t (G.S (-t) (Fe t)) = Fe t := by
        have := congrArg (fun B : E →L[ℝ] E => B (Fe t)) (G.map_add t (-t))
        simp only [add_neg_cancel, G.map_zero, one_apply_eq_self,
          mul_apply_eq_comp] at this
        exact this.symm
      rw [e, LinearPMap.map_add, hinv, hP t ht, G.apply_comm, G.apply_comm]
      abel
    · simp [w, G.map_zero]
  · have hE : Icc (0 : ℝ) T = ∅ := Icc_eq_empty (by linarith)
    refine ⟨fun _ => U₀, ⟨fun t ht => ?_, fun t ht => ?_, rfl⟩, ⟨0, ?_, fun t ht => ?_⟩,
      ⟨0, ?_, fun t ht => ?_⟩⟩ <;>
      first | (rw [hE] at ht; exact absurd ht (Set.notMem_empty t)) |
        (rw [hE]; exact continuousOn_empty _)

end UnitaryGroupGenerator

/-- The forcing class of Thm 4.3 as covered here: `C([0,T]; D(A))` (`ForcingDL`) or the
`W^{1,1}`-type class `ForcingW11`. Cf. the thesis' `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪
L¹(0,T; D(A)))`. -/
def ForcingThm43 (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ForcingDL A T F ∨ ForcingW11 T F

/-- **Thesis Thm 4.3 (existence) from a unitary group**, for the combined forcing class
`ForcingThm43 = C([0,T]; D(A)) ∪ ForcingW11`. See [QuennevilleBelair2015, Thm 4.3]. -/
theorem UnitaryGroupGenerator.wellPosedClassical_thm43 (G : UnitaryGroupGenerator A) (T : ℝ) :
    WellPosedClassical A T (ForcingThm43 A T) := by
  rintro U₀ hU₀ F (hF | hF)
  · exact G.wellPosedClassical_forcing T U₀ hU₀ F hF
  · exact G.wellPosedClassical_W11 T U₀ hU₀ F hF

end Feec
