module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Feec.Ch4.StoneDuhamel

/-!
# Thesis Thm 4.3 with the full forcing class `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(L)))`

[QuennevilleBelair2015, Thm 4.3] (citing [CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9]): for `L`
skew-adjoint with dense domain, `U₀ ∈ D(L)`, and `F ∈ C([0,T], X)` lying in at least one of
`W^{1,1}(0,T; X)` and `L¹(0,T; D(L))`, there is a unique solution
`U ∈ C⁰([0,T], D(L)) ∩ C¹([0,T], X)` of `U' = L U + F`, `U(0) = U₀`.

This module proves exactly that, for every real Hilbert space, with the group of Stone's theorem
(`Feec.stoneGroup`). The solution is Duhamel's `U(t) = S(t) U₀ + S(t) ∫₀ᵗ S(-s) F(s) ds`.

## The forcing classes

* `IsW11 T F`: `F` agrees a.e. on `(0,T)` with `x₀ + ∫₀ᵗ g` for some `x₀ ∈ X` and some `g`
  Bochner integrable on `(0,T)`. This is the definition of `W^{1,1}(0,T; X)` via the integral
  representation of its elements ([CazenaveHaraux1998, Ch. 1]: `u ∈ W^{1,1}` iff
  `u = x₀ + ∫₀ᵗ g` a.e. with `g ∈ L¹`, and then `g = u'` is the weak derivative). We take the
  integral form as the definition and do not prove its equivalence with absolute continuity.
  For continuous `F` the a.e. identity holds at every point of `[0,T]` with `x₀ = F 0`
  (`isW11_iff`).
* `IsL1D A T F`: `F(t) ∈ D(A)` for a.e. `t ∈ (0,T)`, and `t ↦ A F(t)` agrees a.e. with an
  integrable `H`. Together with continuity of `F` (so `F` is integrable), this says that `F`
  has a representative in `L¹(0,T; D(A))` for the graph norm: `t ↦ (F t, A F t)` is
  integrable with values a.e. in the graph of `A`.
* `ForcingThm43Full A T F := ContinuousOn F [0,T] ∧ (IsW11 T F ∨ IsL1D A T F)`, the thesis'
  class. It contains the class `ForcingThm43` of `Feec.Ch4.StoneDuhamel`
  (`forcingThm43Full_of_forcingThm43`).

## Main results

* `UnitaryGroupGenerator.integral_mem_domain_of_primitive`: for `F = x₀ + ∫₀^· g`,
  `g ∈ L¹`, `A ∫₀ᵗ S(-s) F(s) ds = x₀ + ∫₀ᵗ S(-s) g(s) ds - S(-t) F(t)` (integration by
  parts; proved for continuous `g` in `Feec.Ch4.StoneDuhamel` and extended by density of
  continuous functions in `L¹`).
* `UnitaryGroupGenerator.integral_mem_domain_of_L1`: for `F ∈ L¹(0,t; D(A))`,
  `A ∫₀ᵗ S(-s) F(s) ds = ∫₀ᵗ S(-s) A F(s) ds`.
* `UnitaryGroupGenerator.wellPosedClassical_thm43Full`, `IsSkewAdjoint.wellPosedClassical_thm43Full`:
  classical solutions for every forcing in `ForcingThm43Full`.
* **`thm_4_3_full`**: Thesis Thm 4.3 as stated: existence of a solution in
  `C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)`, unique among strong solutions.

Thesis gap: the thesis gives no proof (it cites [CazenaveHaraux1998]); this module supplies one,
with no hypothesis beyond those of the statement. Uniqueness is proved among strong solutions
(`IsStrongSolution`: values in `D(A)` and a pointwise derivative), a larger class than the
thesis' `C⁰([0,T]; D(L)) ∩ C¹([0,T]; X)`.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3)
* [CazenaveHaraux1998], Prop 4.1.6, Cor 2.4.9 (cited by the thesis); Ch. 1 (`W^{1,p}` in time)
* [Pazy1983], §4.2 (Duhamel's formula; forcing in `W^{1,1}` or in `L¹(0,T; D(A))`)
-/

open scoped RealInnerProductSpace LinearPMap
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

/-! ### Forcing classes -/

/-- `F ∈ W^{1,1}(0,T; X)`: `F = x₀ + ∫₀^· g` a.e. on `(0,T)`, for some `x₀ ∈ X` and some
`g` Bochner integrable on `(0,T)`. See [CazenaveHaraux1998, Ch. 1]. -/
def IsW11 (T : ℝ) (F : ℝ → E) : Prop :=
  ∃ (x₀ : E) (g : ℝ → E), IntegrableOn g (Ioc 0 T) ∧
    F =ᵐ[volume.restrict (Ioo 0 T)] fun t => x₀ + ∫ s in (0 : ℝ)..t, g s

/-- `F ∈ L¹(0,T; D(A))` (graph norm): `F(t) ∈ D(A)` for a.e. `t ∈ (0,T)`, with `t ↦ A F(t)`
a.e. equal to a Bochner integrable `H`. (Integrability of `F` itself is automatic in
`ForcingThm43Full`, where `F` is continuous on `[0,T]`.) -/
def IsL1D (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ∃ H : ℝ → E, IntegrableOn H (Ioc 0 T) ∧
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∃ h : F t ∈ A.domain, A ⟨F t, h⟩ = H t

/-- The forcing class of [QuennevilleBelair2015, Thm 4.3]:
`F ∈ C([0,T], X)` and `F ∈ W^{1,1}(0,T; X) ∪ L¹(0,T; D(A))`. -/
def ForcingThm43Full (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Icc 0 T) ∧ (IsW11 T F ∨ IsL1D A T F)

omit [CompleteSpace E] in
/-- The primitive `t ↦ ∫₀ᵗ g` of `g ∈ L¹(0,T)` is continuous on `[0,T]`. -/
theorem continuousOn_primitive_Icc_of_integrableOn {g : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hg : IntegrableOn g (Ioc 0 T)) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, g s) (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hg) left_mem_uIcc
  rwa [uIcc_of_le hT] at h

omit [CompleteSpace E] in
/-- For continuous `F`, membership in `W^{1,1}` holds pointwise on `[0,T]`:
`F ∈ C([0,T]; X) ∩ W^{1,1}(0,T; X)` iff `F(t) = F(0) + ∫₀ᵗ g` for all `t ∈ [0,T]`, with `g`
integrable. -/
theorem isW11_iff {T : ℝ} {F : ℝ → E} (hF : ContinuousOn F (Icc 0 T)) :
    IsW11 T F ↔ ∃ g : ℝ → E, IntegrableOn g (Ioc 0 T) ∧
      ∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, g s := by
  constructor
  · rintro ⟨x₀, g, hg, hae⟩
    refine ⟨g, hg, ?_⟩
    rcases lt_or_ge 0 T with hT | hT
    · have hP : ContinuousOn (fun t => x₀ + ∫ s in (0 : ℝ)..t, g s) (Icc 0 T) := by
        exact continuousOn_const.add (continuousOn_primitive_Icc_of_integrableOn hT.le hg)
      have hae' : F =ᵐ[volume.restrict (Icc 0 T)] fun t => x₀ + ∫ s in (0 : ℝ)..t, g s := by
        rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
      have heq := Measure.eqOn_Icc_of_ae_eq volume hT.ne hae' hF hP
      have h0 : F 0 = x₀ := by
        simpa using heq (left_mem_Icc.2 hT.le)
      intro t ht
      rw [heq ht, h0]
    · intro t ht
      have : t = 0 := le_antisymm (ht.2.trans hT) ht.1
      subst this
      simp
  · rintro ⟨g, hg, hpt⟩
    refine ⟨F 0, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hpt t (Ioo_subset_Icc_self ht)

/-- `ForcingThm43` (`C([0,T]; D(A))` or continuous with integrable derivative off a countable
set) is contained in the thesis' class `ForcingThm43Full`. -/
theorem forcingThm43Full_of_forcingThm43 {T : ℝ} {F : ℝ → E} (hF : ForcingThm43 A T F) :
    ForcingThm43Full A T F := by
  rcases hF with ⟨hFD, hFc, H, hHc, hH⟩ | ⟨hFc, F', s, hs, hi, hd⟩
  · refine ⟨hFc, Or.inr ⟨H, ?_, ?_⟩⟩
    · exact (hHc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ⟨hFD t (Ioo_subset_Icc_self ht), hH t (Ioo_subset_Icc_self ht)⟩
  · refine ⟨hFc, Or.inl ((isW11_iff hFc).2 ⟨F', hi.1, fun t ht => ?_⟩)⟩
    have := integral_eq_of_hasDerivAt_off_countable_of_le F F' ht.1 hs (hFc.mono
      (Icc_subset_Icc le_rfl ht.2)) (fun x hx => hd x ⟨⟨hx.1.1, hx.1.2.trans_le ht.2⟩, hx.2⟩)
      (hi.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
                       exact Icc_subset_Icc le_rfl ht.2))
    rw [this]; abel

/-! ### Duhamel's formula, given the domain property of the integral term -/

namespace UnitaryGroupGenerator

variable (G : UnitaryGroupGenerator A)

include G in
/-- Duhamel's formula gives a classical solution as soon as the integral term lies in the domain
with a continuous image. Let `Fe` be continuous on `ℝ` and equal to `F` on `[0,T]`, and suppose
`w(t) = ∫₀ᵗ S(-s) Fe(s) ds ∈ D(A)` with `t ↦ A w(t)` continuous on `[0,T]`. Then
`U(t) = S(t) U₀ + S(t) w(t)` is a classical solution of `U' = A U + F`, `U(0) = U₀`. -/
theorem isClassicalSolution_duhamel {T : ℝ} {U₀ : E} (hU₀ : U₀ ∈ A.domain) {F Fe V : ℝ → E}
    (hFe : Continuous Fe) (hP : ∀ t ∈ Icc 0 T, Fe t = F t) (hV : ContinuousOn V (Icc 0 T))
    (hw : ∀ t ∈ Icc 0 T, ∃ h : (∫ r in (0 : ℝ)..t, G.S (-r) (Fe r)) ∈ A.domain,
      A ⟨_, h⟩ = V t) :
    IsClassicalSolution A T U₀ F
      (fun τ => G.S τ U₀ + G.S τ (∫ r in (0 : ℝ)..τ, G.S (-r) (Fe r))) := by
  set w : ℝ → E := fun t => ∫ r in (0 : ℝ)..t, G.S (-r) (Fe r) with hw_def
  have hFc : ContinuousOn F (Icc 0 T) := hFe.continuousOn.congr fun t ht => (hP t ht).symm
  have hg : Continuous fun r => G.S (-r) (Fe r) :=
    G.continuous_uncurry.comp (continuous_neg.prodMk hFe)
  have hwd : ∀ t, HasDerivAt w (G.S (-t) (Fe t)) t := fun t =>
    (hg.integral_hasStrictDerivAt 0 t).hasDerivAt
  choose mem hAw using hw
  have hU : ∀ t (ht : t ∈ Icc 0 T), G.S t U₀ + G.S t (w t) ∈ A.domain := fun t ht =>
    A.domain.add_mem (G.mem_domain_apply ⟨U₀, hU₀⟩ t) (G.mem_domain_apply ⟨w t, mem t ht⟩ t)
  have hval : ∀ t (ht : t ∈ Icc 0 T), A ⟨_, hU t ht⟩ = G.S t (A ⟨U₀, hU₀⟩) + G.S t (V t) := by
    intro t ht
    have e : (⟨_, hU t ht⟩ : A.domain) = ⟨_, G.mem_domain_apply ⟨U₀, hU₀⟩ t⟩ +
        ⟨_, G.mem_domain_apply ⟨w t, mem t ht⟩ t⟩ := rfl
    rw [e, LinearPMap.map_add, G.apply_comm, G.apply_comm, hAw t ht]
  have hGc : ContinuousOn (fun t => G.S t (A ⟨U₀, hU₀⟩) + G.S t (V t)) (Icc 0 T) :=
    (G.continuous_apply _).continuousOn.add
      (G.continuous_uncurry.comp_continuousOn (continuousOn_id.prodMk hV))
  refine ⟨⟨hU, fun t ht => ?_, ?_⟩, ⟨_, hGc, hval⟩,
    ⟨_, hGc.add hFc, fun t ht => by rw [hval t ht]; rfl⟩⟩
  · have h1 := G.hasDerivAt_apply ⟨U₀, hU₀⟩ t
    have h2 := G.hasDerivAt_apply_comp (hwd t) (G.hasDerivAt_apply ⟨w t, mem t ht⟩ t)
    have h3 := (h1.add h2).hasDerivWithinAt (s := Icc 0 T)
    convert h3 using 1
    have e : (⟨_, hU t ht⟩ : A.domain) = ⟨_, G.mem_domain_apply ⟨U₀, hU₀⟩ t⟩ +
        ⟨_, G.mem_domain_apply ⟨w t, mem t ht⟩ t⟩ := rfl
    have hinv : G.S t (G.S (-t) (Fe t)) = Fe t := by
      have := congrArg (fun B : E →L[ℝ] E => B (Fe t)) (G.map_add t (-t))
      simp only [add_neg_cancel, G.map_zero, one_apply_eq_self, mul_apply_eq_comp] at this
      exact this.symm
    rw [e, LinearPMap.map_add, hinv, hP t ht, G.apply_comm, G.apply_comm]
    abel
  · simp [G.map_zero]

/-! ### The `L¹(0,T; D(A))` branch -/

/-- **`A` commutes with the Duhamel integral on `L¹(0,t; D(A))`.** If `f` is continuous on
`[0,t]`, `f(s) ∈ D(A)` for a.e. `s ∈ (0,t]` with `A f(s) = H(s)` and `H` integrable, then
`∫₀ᵗ S(-s) f(s) ds ∈ D(A)` and `A ∫₀ᵗ S(-s) f(s) ds = ∫₀ᵗ S(-s) H(s) ds`.
Proof: for `z ∈ D(A)`, `⟪S(-s) f(s), A z⟫ = ⟪f(s), A S(s) z⟫ = -⟪H(s), S(s) z⟫` a.e., so the
integral lies in `D(A†) = D(A)`. Cf. [Pazy1983, §4.2], [CazenaveHaraux1998, Prop 4.1.6]. -/
theorem integral_mem_domain_of_L1 {f H : ℝ → E} {t : ℝ} (ht : 0 ≤ t)
    (hf : ContinuousOn f (Icc 0 t)) (hH : IntegrableOn H (Ioc 0 t))
    (hD : ∀ᵐ s ∂(volume.restrict (Ioc 0 t)), ∃ h : f s ∈ A.domain, A ⟨f s, h⟩ = H s) :
    ∃ h : (∫ r in (0 : ℝ)..t, G.S (-r) (f r)) ∈ A.domain,
      A ⟨_, h⟩ = ∫ r in (0 : ℝ)..t, G.S (-r) (H r) := by
  have hA : IsSkewAdjoint A := G.isSkewAdjoint
  have hS := G.isSkewSymm
  set w := ∫ r in (0 : ℝ)..t, G.S (-r) (f r) with hw
  set I := ∫ r in (0 : ℝ)..t, G.S (-r) (H r) with hI
  have hwi : IntervalIntegrable (fun r => G.S (-r) (f r)) volume 0 t :=
    (G.continuous_uncurry.comp_continuousOn (continuous_neg.continuousOn.prodMk hf)
      |>.intervalIntegrable_of_Icc ht)
  have hIi : IntervalIntegrable (fun r => G.S (-r) (H r)) volume 0 t :=
    G.intervalIntegrable_apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hH)
      continuous_neg
  have key : ∀ z : A.domain, ⟪-I, (z : E)⟫ = ⟪w, A z⟫ := by
    intro z
    have e1 : ⟪w, A z⟫ = ∫ r in (0 : ℝ)..t, ⟪A z, G.S (-r) (f r)⟫ := by
      rw [real_inner_comm]
      have := (innerSL ℝ (A z)).intervalIntegral_comp_comm hwi
      simpa only [innerSL_apply_apply] using this.symm
    have e2 : ⟪I, (z : E)⟫ = ∫ r in (0 : ℝ)..t, ⟪(z : E), G.S (-r) (H r)⟫ := by
      rw [real_inner_comm]
      have := (innerSL ℝ (z : E)).intervalIntegral_comp_comm hIi
      simpa only [innerSL_apply_apply] using this.symm
    have e3 : (∫ r in (0 : ℝ)..t, ⟪A z, G.S (-r) (f r)⟫) =
        ∫ r in (0 : ℝ)..t, -⟪(z : E), G.S (-r) (H r)⟫ := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le ht]
      have := (ae_restrict_iff' measurableSet_Ioc).1 hD
      filter_upwards [this] with r hr hrm
      obtain ⟨hfr, hAfr⟩ := hr hrm
      have hz := hS ⟨f r, hfr⟩ ⟨_, G.mem_domain_apply z r⟩
      rw [G.apply_comm, hAfr] at hz
      rw [real_inner_comm, G.inner_S_left, neg_neg, real_inner_comm _ (z : E), G.inner_S_left,
        neg_neg]
      linarith
    rw [e1, e3, intervalIntegral.integral_neg, inner_neg_left, e2]
  obtain ⟨hmem, hval⟩ := hA.mem_domain_of_adjoint key
  exact ⟨hmem, by rw [hval, neg_neg]⟩

/-! ### The `W^{1,1}(0,T; X)` branch -/

/-- **Integration by parts against the generator, `W^{1,1}` case.** For `x₀ ∈ X`, `g`
integrable on `(0,t)` and `F(r) = x₀ + ∫₀ʳ g`, `∫₀ᵗ S(-r) F(r) dr ∈ D(A)` and
`A ∫₀ᵗ S(-r) F(r) dr = x₀ + ∫₀ᵗ S(-r) g(r) dr - S(-t) F(t)`.
Proof: for continuous `g` this is `integral_mem_domain_of_hasDerivAt`. For general `g`, fix
`z ∈ D(A)` and approximate `g` in `L¹(0,t)` by continuous `gₙ`; each term of the adjoint
identity `⟪S(-t) F(t) - x₀ - ∫₀ᵗ S(-r) g(r) dr, z⟫ = ⟪∫₀ᵗ S(-r) F(r) dr, A z⟫` moves by at most
`(2‖z‖ + t ‖A z‖) ‖g - gₙ‖_{L¹}`, so the identity passes to the limit. -/
theorem integral_mem_domain_of_primitive {x₀ : E} {g : ℝ → E} {t : ℝ} (ht : 0 ≤ t)
    (hg : IntegrableOn g (Ioc 0 t)) :
    ∃ h : (∫ r in (0 : ℝ)..t, G.S (-r) (x₀ + ∫ s in (0 : ℝ)..r, g s)) ∈ A.domain,
      A ⟨_, h⟩ = x₀ + (∫ r in (0 : ℝ)..t, G.S (-r) (g r)) -
        G.S (-t) (x₀ + ∫ s in (0 : ℝ)..t, g s) := by
  have hA : IsSkewAdjoint A := G.isSkewAdjoint
  have hS := G.isSkewSymm
  -- the three ingredients, for an arbitrary integrable `k`
  set P : (ℝ → E) → ℝ → E := fun k r => x₀ + ∫ s in (0 : ℝ)..r, k s with hP_def
  set W : (ℝ → E) → E := fun k => ∫ r in (0 : ℝ)..t, G.S (-r) (P k r) with hW_def
  set J : (ℝ → E) → E := fun k => ∫ r in (0 : ℝ)..t, G.S (-r) (k r) with hJ_def
  have hgi : IntervalIntegrable g volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hg
  have hPc : ∀ k : ℝ → E, IntegrableOn k (Ioc 0 t) → ContinuousOn (P k) (Icc 0 t) := fun k hk =>
    continuousOn_const.add (continuousOn_primitive_Icc_of_integrableOn ht hk)
  have hWi : ∀ k : ℝ → E, IntegrableOn k (Ioc 0 t) →
      IntervalIntegrable (fun r => G.S (-r) (P k r)) volume 0 t := fun k hk =>
    (G.continuous_uncurry.comp_continuousOn (continuous_neg.continuousOn.prodMk (hPc k hk))
      |>.intervalIntegrable_of_Icc ht)
  have hJi : ∀ k : ℝ → E, IntegrableOn k (Ioc 0 t) →
      IntervalIntegrable (fun r => G.S (-r) (k r)) volume 0 t := fun k hk =>
    G.intervalIntegrable_apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hk)
      continuous_neg
  suffices key : ∀ z : A.domain,
      ⟪G.S (-t) (P g t) - x₀ - J g, (z : E)⟫ = ⟪W g, A z⟫ by
    obtain ⟨hmem, hval⟩ := hA.mem_domain_of_adjoint key
    exact ⟨hmem, by rw [hval]; abel⟩
  intro z
  set D := ⟪G.S (-t) (P g t) - x₀ - J g, (z : E)⟫ - ⟪W g, A z⟫ with hD_def
  set C := 2 * ‖(z : E)‖ + t * ‖A z‖ with hC_def
  have hC : 0 ≤ C := by positivity
  suffices hε : ∀ ε > 0, |D| ≤ ε * C by
    have hD0 : D = 0 := by
      by_contra hne
      have hpos : 0 < |D| := abs_pos.2 hne
      have := hε (|D| / (C + 1)) (by positivity)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      nlinarith
    linarith
  intro ε hε
  -- a continuous approximation of `g` in `L¹(0,t)`
  have hgt : Integrable ((Ioc 0 t).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Ioc).2 hg
  obtain ⟨g', -, hgg', hg'c, hg'i⟩ := hgt.exists_hasCompactSupport_integral_sub_le hε
  have hg'o : IntegrableOn g' (Ioc 0 t) := hg'i.integrableOn
  set δ := ∫ r in (0 : ℝ)..t, ‖g r - g' r‖ with hδ_def
  have hdi : IntervalIntegrable (fun r => ‖g r - g' r‖) volume 0 t :=
    (hgi.sub (hg'c.intervalIntegrable 0 t)).norm
  have hδε : δ ≤ ε := by
    rw [hδ_def, intervalIntegral.integral_of_le ht]
    calc ∫ r in Ioc 0 t, ‖g r - g' r‖
        = ∫ r in Ioc 0 t, ‖(Ioc 0 t).indicator g r - g' r‖ := by
          refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
          simp only [indicator_of_mem hr]
      _ ≤ ∫ r, ‖(Ioc 0 t).indicator g r - g' r‖ :=
          setIntegral_le_integral (hgt.sub hg'i).norm (Eventually.of_forall fun _ => norm_nonneg _)
      _ ≤ ε := hgg'
  -- the identity for the continuous approximation
  have hD' : ⟪G.S (-t) (P g' t) - x₀ - J g', (z : E)⟫ - ⟪W g', A z⟫ = 0 := by
    have hd' : ∀ x ∈ Ioo 0 t \ (∅ : Set ℝ), HasDerivAt (P g') (g' x) x := fun x _ =>
      ((hg'c.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add x₀
    obtain ⟨h', hval'⟩ := G.integral_mem_domain_of_hasDerivAt (F := P g') (F' := g') ht
      countable_empty (hPc g' hg'o) hd' (hg'c.intervalIntegrable 0 t)
    have hsk := hS ⟨_, h'⟩ z
    rw [hval'] at hsk
    have h0 : P g' 0 = x₀ := by simp [hP_def]
    rw [h0] at hsk
    have : G.S (-t) (P g' t) - x₀ - J g' = -(x₀ + J g' - G.S (-t) (P g' t)) := by abel
    rw [this, inner_neg_left, hsk, neg_neg]
    exact sub_self _
  -- the estimates
  have hPd : ∀ r ∈ Icc 0 t, ‖P g r - P g' r‖ ≤ δ := by
    intro r hr
    have hgr : IntervalIntegrable g volume 0 r :=
      hgi.mono_set (by rw [uIcc_of_le hr.1, uIcc_of_le ht]; exact Icc_subset_Icc le_rfl hr.2)
    have e : P g r - P g' r = ∫ s in (0 : ℝ)..r, (g s - g' s) := by
      simp only [hP_def]
      rw [intervalIntegral.integral_sub hgr (hg'c.intervalIntegrable 0 r)]
      abel
    rw [e]
    refine (intervalIntegral.norm_integral_le_integral_norm hr.1).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
      (Eventually.of_forall fun _ => norm_nonneg _) hdi
  have hJd : ‖J g - J g'‖ ≤ δ := by
    have e : J g - J g' = ∫ r in (0 : ℝ)..t, G.S (-r) (g r - g' r) := by
      simp only [hJ_def]
      rw [← intervalIntegral.integral_sub (hJi g hg) (hJi g' hg'o)]
      simp only [map_sub]
    rw [e]
    refine (intervalIntegral.norm_integral_le_integral_norm ht).trans (le_of_eq ?_)
    simp only [G.norm_map, hδ_def]
  have hWd : ‖W g - W g'‖ ≤ δ * t := by
    have e : W g - W g' = ∫ r in (0 : ℝ)..t, G.S (-r) (P g r - P g' r) := by
      simp only [hW_def]
      rw [← intervalIntegral.integral_sub (hWi g hg) (hWi g' hg'o)]
      simp only [map_sub]
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (f := fun r => G.S (-r) (P g r - P g' r)) (C := δ) fun r hr => by
        rw [G.norm_map]
        rw [uIoc_of_le ht] at hr
        exact hPd r (Ioc_subset_Icc_self hr)
    rwa [sub_zero, abs_of_nonneg ht] at this
  -- combine
  have hδ0 : 0 ≤ δ := intervalIntegral.integral_nonneg ht fun _ _ => norm_nonneg _
  have hdiff : D = ⟪G.S (-t) (P g t - P g' t) - (J g - J g'), (z : E)⟫ -
      ⟪W g - W g', A z⟫ := by
    have e1 : G.S (-t) (P g t - P g' t) - (J g - J g') =
        (G.S (-t) (P g t) - x₀ - J g) - (G.S (-t) (P g' t) - x₀ - J g') := by
      rw [map_sub]; abel
    rw [e1, inner_sub_left, inner_sub_left (W g)]
    linarith [hD', hD_def]
  have hb1 : |⟪G.S (-t) (P g t - P g' t) - (J g - J g'), (z : E)⟫| ≤ (2 * δ) * ‖(z : E)‖ := by
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_sub_le _ _).trans ?_
    rw [G.norm_map]
    linarith [hPd t (right_mem_Icc.2 ht)]
  have hb2 : |⟪W g - W g', A z⟫| ≤ (δ * t) * ‖A z‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hWd (norm_nonneg _))
  calc |D| ≤ |⟪G.S (-t) (P g t - P g' t) - (J g - J g'), (z : E)⟫| + |⟪W g - W g', A z⟫| := by
        rw [hdiff]; exact abs_sub _ _
    _ ≤ (2 * δ) * ‖(z : E)‖ + (δ * t) * ‖A z‖ := add_le_add hb1 hb2
    _ = δ * C := by rw [hC_def]; ring
    _ ≤ ε * C := mul_le_mul_of_nonneg_right hδε hC

/-! ### Thm 4.3 -/

include G in
/-- **Thesis Thm 4.3 (existence) for the thesis' forcing class**: for `U₀ ∈ D(A)` and
`F ∈ C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))` there is a classical solution
`U ∈ C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)` of `U' = A U + F`, `U(0) = U₀`, namely
`U(t) = S(t) U₀ + S(t) ∫₀ᵗ S(-s) F(s) ds`. In the `W^{1,1}` case
`A U(t) = S(t) A U₀ + S(t) F(0) + ∫₀ᵗ S(t-s) F'(s) ds - F(t)`; in the `L¹(D(A))` case
`A U(t) = S(t) A U₀ + ∫₀ᵗ S(t-s) A F(s) ds`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [CazenaveHaraux1998, Prop 4.1.6],
[Pazy1983, §4.2]. -/
theorem wellPosedClassical_thm43Full (T : ℝ) : WellPosedClassical A T (ForcingThm43Full A T) := by
  rintro U₀ hU₀ F ⟨hFc, hF⟩
  by_cases hT : 0 ≤ T
  swap
  · have hE : Icc (0 : ℝ) T = ∅ := Icc_eq_empty (by linarith)
    exact ⟨_, G.isClassicalSolution_duhamel hU₀ (Fe := 0) (V := 0) continuous_const
      (by simp [hE]) continuousOn_const (by simp [hE])⟩
  set Pr := projIcc 0 T hT
  set Fe : ℝ → E := fun r => F (Pr r) with hFe
  have hFe_c : Continuous Fe :=
    hFc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun r => (Pr r).2
  have hP : ∀ t ∈ Icc 0 T, Fe t = F t := fun t ht => by
    simp only [Fe, Pr, projIcc_of_mem hT ht]
  have hsub : ∀ t ∈ Icc 0 T, Ioc 0 t ⊆ Ioc 0 T := fun t ht => Ioc_subset_Ioc le_rfl ht.2
  -- `∫₀ᵗ S(-r) Fe r = ∫₀ᵗ S(-r) F r` for `t ∈ [0,T]`
  have hcongr : ∀ t ∈ Icc 0 T, ∀ φ : ℝ → E, (∀ r ∈ Icc 0 t, F r = φ r) →
      (∫ r in (0 : ℝ)..t, G.S (-r) (Fe r)) = ∫ r in (0 : ℝ)..t, G.S (-r) (φ r) := by
    intro t ht φ hφ
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.1] at hr
    rw [hP r ⟨hr.1, hr.2.trans ht.2⟩, hφ r hr]
  rcases hF with hW | ⟨H, hH, hD⟩
  · -- `W^{1,1}` branch
    obtain ⟨g, hg, hpt⟩ := (isW11_iff hFc).1 hW
    have hgi : IntervalIntegrable (fun r => G.S (-r) (g r)) volume 0 T :=
      G.intervalIntegrable_apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hg)
        continuous_neg
    have hJc : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, G.S (-r) (g r)) (Icc 0 T) :=
      continuousOn_primitive_Icc_of_integrableOn hT
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hgi)
    refine ⟨_, G.isClassicalSolution_duhamel hU₀ hFe_c hP
      (V := fun t => F 0 + (∫ r in (0 : ℝ)..t, G.S (-r) (g r)) - G.S (-t) (F t))
      ((continuousOn_const.add hJc).sub
        (G.continuous_uncurry.comp_continuousOn (continuous_neg.continuousOn.prodMk hFc)))
      fun t ht => ?_⟩
    rw [hcongr t ht (fun r => F 0 + ∫ s in (0 : ℝ)..r, g s)
      fun r hr => hpt r ⟨hr.1, hr.2.trans ht.2⟩]
    obtain ⟨h, hval⟩ := G.integral_mem_domain_of_primitive (x₀ := F 0) ht.1 (hg.mono_set (hsub t ht))
    exact ⟨h, by rw [hval, ← hpt t ht]⟩
  · -- `L¹(0,T; D(A))` branch
    have hHi : IntervalIntegrable (fun r => G.S (-r) (H r)) volume 0 T :=
      G.intervalIntegrable_apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hH)
        continuous_neg
    have hJc : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, G.S (-r) (H r)) (Icc 0 T) :=
      continuousOn_primitive_Icc_of_integrableOn hT
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hHi)
    refine ⟨_, G.isClassicalSolution_duhamel hU₀ hFe_c hP hJc fun t ht => ?_⟩
    rw [hcongr t ht F fun _ _ => rfl]
    refine G.integral_mem_domain_of_L1 ht.1 (hFc.mono (Icc_subset_Icc le_rfl ht.2))
      (hH.mono_set (hsub t ht)) ?_
    have h1 : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)), ∃ h : F s ∈ A.domain, A ⟨F s, h⟩ = H s :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2) hD
    rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]

end UnitaryGroupGenerator

/-- Classical solutions of `U' = A U + F` for every skew-adjoint `A` and every forcing in the
thesis' class `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))`, from Stone's theorem.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedClassical_thm43Full (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (ForcingThm43Full A T) :=
  (stoneGroup hA).wellPosedClassical_thm43Full T

/-- `WellPosedExistence A T (ForcingThm43Full A T)` for every skew-adjoint `A`: the existence
hypothesis of `Feec.Foundation.Evolution` holds for the thesis' full forcing class.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedExistence_thm43Full (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedExistence A T (ForcingThm43Full A T) :=
  (hA.wellPosedClassical_thm43Full T).wellPosedExistence

/-- **Thesis Thm 4.3**, as stated: for `A` skew-adjoint (its domain is then dense), `U₀ ∈ D(A)`
and `F ∈ C([0,T], X)` in at least one of `W^{1,1}(0,T; X)` and `L¹(0,T; D(A))`, there is a
solution `U ∈ C⁰([0,T], D(A)) ∩ C¹([0,T], X)` of `U' = A U + F`, `U(0) = U₀`, and it is unique
among strong solutions (a larger class than `C⁰(D(A)) ∩ C¹(X)`).
See [QuennevilleBelair2015, Thm 4.3]; cf. [CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9]. -/
theorem thm_4_3_full (hA : IsSkewAdjoint A) (T : ℝ) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} (hF : ForcingThm43Full A T F) :
    ∃ U, IsClassicalSolution A T U₀ F U ∧
      ∀ U', IsStrongSolution A T U₀ F U' → EqOn U' U (Icc 0 T) := by
  obtain ⟨U, hU⟩ := hA.wellPosedClassical_thm43Full T U₀ hU₀ F hF
  exact ⟨U, hU, fun U' hU' => strongSolution_unique A (hA.isSkewSymm hA.dense_domain) hU'
    hU.toIsStrongSolution⟩

end Feec
