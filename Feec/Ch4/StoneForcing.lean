module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Feec.Ch4.StoneDuhamel
public import Feec.Evolution.Forcing

/-!
# Thesis Thm 4.3 with the full forcing class `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(L)))`

[QuennevilleBelair2015, Thm 4.3] (citing [CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9]): for `L`
skew-adjoint with dense domain, `U₀ ∈ D(L)`, and `F ∈ C([0,T], X)` lying in at least one of
`W^{1,1}(0,T; X)` and `L¹(0,T; D(L))`, there is a unique solution
`U ∈ C⁰([0,T], D(L)) ∩ C¹([0,T], X)` of `U' = L U + F`, `U(0) = U₀`.

This module proves exactly that, for every real Hilbert space, with the group of Stone's theorem
(`Feec.stoneGroup`). The solution is Duhamel's `U(t) = S(t) U₀ + S(t) ∫₀ᵗ S(-s) F(s) ds`.

## The forcing classes

The classes are defined in `Feec.Evolution.Forcing`: `ForcingClass.w11` (`W^{1,1}(0,T; X)` in its
integral form `F = x₀ + ∫₀^· g` a.e., [CazenaveHaraux1998, Ch. 1]), `ForcingClass.l1Domain`
(`L¹(0,T; D(A))` for the graph norm) and `ForcingClass.admissible`, the thesis' class
`C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))`. This module proves that `g` is the weak
derivative (`ForcingClass.w11.exists_weakDeriv`: `∫₀ᵀ φ' F = -∫₀ᵀ φ g` for `C¹` test functions
vanishing at `0` and `T`). The equivalence with "absolutely continuous with integrable a.e.
derivative" is not proved; it holds because a Hilbert space has the Radon–Nikodým property, and
it fails for general Banach `X`. In the `W^{1,1}` branch the requirement `F ∈ C([0,T]; X)` only
selects the continuous representative; it is kept to mirror the thesis statement.

## Main results

* `UnitaryGroupGenerator.integral_mem_domain_of_primitive`: for `F = x₀ + ∫₀^· g`,
  `g ∈ L¹`, `A ∫₀ᵗ S(-s) F(s) ds = x₀ + ∫₀ᵗ S(-s) g(s) ds - S(-t) F(t)` (integration by
  parts; proved for continuous `g` in `Feec.Ch4.StoneDuhamel` and extended by density of
  continuous functions in `L¹`).
* `UnitaryGroupGenerator.integral_mem_domain_of_L1`: for `F ∈ L¹(0,t; D(A))`,
  `A ∫₀ᵗ S(-s) F(s) ds = ∫₀ᵗ S(-s) A F(s) ds`.
* `UnitaryGroupGenerator.duhamel_W11`, `UnitaryGroupGenerator.duhamel_L1`: Duhamel's
  `U = G.duhamelSol U₀ F` is a classical solution, with the explicit generator image
  `A U(t) = S(t) A U₀ + S(t) F(0) + ∫₀ᵗ S(t-s) g(s) ds - F(t)` (`W^{1,1}`, `g` the weak
  derivative) and `A U(t) = S(t) A U₀ + ∫₀ᵗ S(t-s) A F(s) ds` (`L¹(D(A))`). For skew-adjoint
  `A` apply them to `G = stoneGroup hA`.
* `UnitaryGroupGenerator.wellPosedClassical_admissible`, `IsSkewAdjoint.wellPosedClassical_of_le`:
  classical solutions for every admissible forcing (and so for every smaller class:
  `wellPosedClassical_W11`, `wellPosedClassical_thm43`, `IsSkewAdjoint.wellPosedClassical_thm43Full`
  are corollaries).
* `integral_deriv_smul_primitive`, `ForcingClass.w11.exists_weakDeriv`: `g` is the weak derivative.
* **`IsSkewAdjoint.existsUnique_classicalSolution`** (formerly `thm_4_3_full`): Thesis Thm 4.3 as
  stated: existence of a solution in `C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)`, unique among strong
  solutions.

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

/-! ### `L¹` approximation by continuous functions -/

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A vector that is `≤ ε C` in norm for every `ε > 0` vanishes. -/
theorem eq_zero_of_forall_norm_le_mul {D : E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, ‖D‖ ≤ ε * C) : D = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  have h1 := h (δ / (C + 1)) (by positivity)
  have h2 : δ / (C + 1) * C ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

omit [CompleteSpace E] in
/-- Continuous functions are dense in `L¹(0,t; X)`: for `g` integrable on `(0,t)` and `ε > 0`
there is a continuous `g'` with `∫₀ᵗ ‖g - g'‖ ≤ ε`
(from `Integrable.exists_hasCompactSupport_integral_sub_le`). -/
theorem exists_continuous_intervalIntegral_norm_sub_le {g : ℝ → E} {t : ℝ} (ht : 0 ≤ t)
    (hg : IntegrableOn g (Ioc 0 t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g' : ℝ → E, Continuous g' ∧ ∫ r in (0 : ℝ)..t, ‖g r - g' r‖ ≤ ε := by
  have hgt : Integrable ((Ioc 0 t).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Ioc).2 hg
  obtain ⟨g', -, hgg', hg'c, hg'i⟩ := hgt.exists_hasCompactSupport_integral_sub_le hε
  refine ⟨g', hg'c, ?_⟩
  rw [intervalIntegral.integral_of_le ht]
  calc ∫ r in Ioc 0 t, ‖g r - g' r‖
      = ∫ r in Ioc 0 t, ‖(Ioc 0 t).indicator g r - g' r‖ := by
        refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        simp only [indicator_of_mem hr]
    _ ≤ ∫ r, ‖(Ioc 0 t).indicator g r - g' r‖ :=
        setIntegral_le_integral (hgt.sub hg'i).norm (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ε := hgg'

omit [CompleteSpace E] in
/-- `‖∫₀ʳ g - ∫₀ʳ g'‖ ≤ ∫₀ᵗ ‖g - g'‖` for `r ∈ [0,t]`. -/
theorem norm_primitive_sub_le {g g' : ℝ → E} {t r : ℝ} (ht : 0 ≤ t)
    (hg : IntegrableOn g (Ioc 0 t)) (hg' : Continuous g') (hr : r ∈ Icc 0 t) :
    ‖(∫ s in (0 : ℝ)..r, g s) - ∫ s in (0 : ℝ)..r, g' s‖ ≤ ∫ s in (0 : ℝ)..t, ‖g s - g' s‖ := by
  have hgi : IntervalIntegrable g volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hg
  have hgr : IntervalIntegrable g volume 0 r :=
    hgi.mono_set (by rw [uIcc_of_le hr.1, uIcc_of_le ht]; exact Icc_subset_Icc le_rfl hr.2)
  rw [← intervalIntegral.integral_sub hgr (hg'.intervalIntegrable 0 r)]
  refine (intervalIntegral.norm_integral_le_integral_norm hr.1).trans ?_
  exact intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
    (Eventually.of_forall fun _ => norm_nonneg _) (hgi.sub (hg'.intervalIntegrable 0 t)).norm

/-! ### `g` is the weak derivative of `x₀ + ∫₀^· g` -/

/-- **`g` is the weak (distributional) derivative of `F = x₀ + ∫₀^· g`**, for `g ∈ L¹(0,T; X)`:
`∫₀ᵀ φ'(t) F(t) dt = -∫₀ᵀ φ(t) g(t) dt` for every `C¹` test function `φ` vanishing at `0` and
`T` (in particular for every `φ ∈ C_c^∞(0,T)`). This is the characterisation of
`W^{1,1}(0,T; X)` in [CazenaveHaraux1998, Ch. 1]; it justifies reading `g` in `ForcingClass.w11` as `F'`.
Proof: integration by parts for continuous `g`, extended by `L¹` density with the error bound
`(T ‖φ'‖_∞ + ‖φ‖_∞) ‖g - gₙ‖_{L¹}`. -/
theorem integral_deriv_smul_primitive {x₀ : E} {g : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hg : IntegrableOn g (Ioc 0 T)) {φ φ' : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (φ' t) t)
    (hφ' : Continuous φ') (h0 : φ 0 = 0) (hT0 : φ T = 0) :
    ∫ t in (0 : ℝ)..T, φ' t • (x₀ + ∫ s in (0 : ℝ)..t, g s) = -∫ t in (0 : ℝ)..T, φ t • g t := by
  set P : (ℝ → E) → ℝ → E := fun k r => x₀ + ∫ s in (0 : ℝ)..r, k s with hP_def
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφc.continuousOn (s := Icc 0 T))
  obtain ⟨M', hM'⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hφ'.continuousOn (s := Icc 0 T))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (left_mem_Icc.2 hT))
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0 (left_mem_Icc.2 hT))
  have hgi : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hg
  have hPc : ∀ k : ℝ → E, IntegrableOn k (Ioc 0 T) → ContinuousOn (P k) (Icc 0 T) := fun k hk =>
    continuousOn_const.add (ForcingClass.continuousOn_primitive hT hk)
  have hI1 : ∀ k : ℝ → E, IntegrableOn k (Ioc 0 T) →
      IntervalIntegrable (fun t => φ' t • P k t) volume 0 T := fun k hk =>
    (hφ'.continuousOn.smul (hPc k hk)).intervalIntegrable_of_Icc hT
  have hI2 : ∀ k : ℝ → E, IntegrableOn k (Ioc 0 T) →
      IntervalIntegrable (fun t => φ t • k t) volume 0 T := fun k hk =>
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hk).continuousOn_smul hφc.continuousOn
  rw [← sub_eq_zero, sub_neg_eq_add]
  refine eq_zero_of_forall_norm_le_mul (C := T * M' + M) (by positivity) fun ε hε => ?_
  obtain ⟨g', hg'c, hδε⟩ := exists_continuous_intervalIntegral_norm_sub_le hT hg hε
  have hg'o : IntegrableOn g' (Ioc 0 T) := hg'c.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  set δ := ∫ r in (0 : ℝ)..T, ‖g r - g' r‖ with hδ_def
  have hδ0 : 0 ≤ δ := intervalIntegral.integral_nonneg hT fun _ _ => norm_nonneg _
  -- integration by parts for the continuous approximation
  have hd' : ∀ x, HasDerivAt (P g') (g' x) x := fun x =>
    ((hg'c.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add x₀
  have hibp : ∫ t in (0 : ℝ)..T, φ t • g' t = -∫ t in (0 : ℝ)..T, φ' t • P g' t := by
    have := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt (a := 0) (b := T)
      (u := φ) (u' := φ') (v := P g') (v' := g') hφc.continuousOn
      (continuous_iff_continuousAt.2 fun x => (hd' x).continuousAt).continuousOn
      (fun x _ => hφ x) (fun x _ => hd' x) (hφ'.intervalIntegrable 0 T)
      (hg'c.intervalIntegrable 0 T)
    rw [this, h0, hT0]
    simp
  have hdiff : (∫ t in (0 : ℝ)..T, φ' t • P g t) + ∫ t in (0 : ℝ)..T, φ t • g t =
      (∫ t in (0 : ℝ)..T, φ' t • (P g t - P g' t)) + ∫ t in (0 : ℝ)..T, φ t • (g t - g' t) := by
    simp only [smul_sub]
    rw [intervalIntegral.integral_sub (hI1 g hg) (hI1 g' hg'o),
      intervalIntegral.integral_sub (hI2 g hg) (hI2 g' hg'o), hibp]
    abel
  have hPd : ∀ r ∈ Icc 0 T, ‖P g r - P g' r‖ ≤ δ := fun r hr => by
    simp only [hP_def, add_sub_add_left_eq_sub]
    exact norm_primitive_sub_le hT hg hg'c hr
  have hb1 : ‖∫ t in (0 : ℝ)..T, φ' t • (P g t - P g' t)‖ ≤ M' * δ * T := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
      (f := fun t => φ' t • (P g t - P g' t)) (C := M' * δ) fun t ht => by
        rw [uIoc_of_le hT] at ht
        rw [norm_smul]
        exact mul_le_mul (hM' t (Ioc_subset_Icc_self ht)) (hPd t (Ioc_subset_Icc_self ht))
          (norm_nonneg _) hM'0
    rwa [sub_zero, abs_of_nonneg hT] at this
  have hdi : IntervalIntegrable (fun r => ‖g r - g' r‖) volume 0 T :=
    (hgi.sub (hg'c.intervalIntegrable 0 T)).norm
  have hb2 : ‖∫ t in (0 : ℝ)..T, φ t • (g t - g' t)‖ ≤ M * δ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hT).trans ?_
    rw [hδ_def, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT
      ((hgi.sub (hg'c.intervalIntegrable 0 T)).continuousOn_smul hφc.continuousOn).norm
      (hdi.const_mul M) fun t ht => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)
  show ‖(∫ t in (0 : ℝ)..T, φ' t • P g t) + ∫ t in (0 : ℝ)..T, φ t • g t‖ ≤ ε * (T * M' + M)
  rw [hdiff]
  calc _ ≤ M' * δ * T + M * δ := (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ = δ * (T * M' + M) := by ring
    _ ≤ ε * (T * M' + M) := mul_le_mul_of_nonneg_right hδε (by positivity)

/-- **Weak-derivative form of `ForcingClass.w11`**: if `F ∈ W^{1,1}(0,T; X)` (`T ≥ 0`), there is
`g ∈ L¹(0,T; X)` with `∫₀ᵀ φ' F = -∫₀ᵀ φ g` for every `C¹` function `φ` vanishing at `0` and `T`.
See [CazenaveHaraux1998, Ch. 1]. -/
theorem ForcingClass.w11.exists_weakDeriv {T : ℝ} {F : ℝ → E} (hT : 0 ≤ T)
    (hF : ForcingClass.w11 T F) :
    ∃ g : ℝ → E, IntegrableOn g (Ioc 0 T) ∧ ∀ φ φ' : ℝ → ℝ, (∀ t, HasDerivAt φ (φ' t) t) →
      Continuous φ' → φ 0 = 0 → φ T = 0 →
        ∫ t in (0 : ℝ)..T, φ' t • F t = -∫ t in (0 : ℝ)..T, φ t • g t := by
  obtain ⟨x₀, g, hg, hae⟩ := hF
  refine ⟨g, hg, fun φ φ' hφ hφ' h0 hT0 => ?_⟩
  rw [← integral_deriv_smul_primitive (x₀ := x₀) hT hg hφ hφ' h0 hT0]
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le hT]
  have h : F =ᵐ[volume.restrict (Ioc 0 T)] fun t => x₀ + ∫ s in (0 : ℝ)..t, g s := by
    rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 h] with t ht htm
  rw [ht htm]

@[deprecated (since := "2026-10-16")] alias IsW11.exists_weakDeriv :=
  ForcingClass.w11.exists_weakDeriv

/-! ### Classical solutions: congruence and the empty interval -/

omit [CompleteSpace E] in
/-- A classical solution can be replaced by any function agreeing with it on `[0,T]` and at `0`. -/
theorem IsClassicalSolution.congr {T : ℝ} {U₀ : E} {F U U' : ℝ → E}
    (hU : IsClassicalSolution A T U₀ F U) (heq : EqOn U' U (Icc 0 T)) (h0 : U' 0 = U₀) :
    IsClassicalSolution A T U₀ F U' := by
  have mem : ∀ t ∈ Icc 0 T, U' t ∈ A.domain := fun t ht => heq ht ▸ hU.mem t ht
  have key : ∀ t (ht : t ∈ Icc 0 T), A ⟨U' t, mem t ht⟩ = A ⟨U t, hU.mem t ht⟩ := fun t ht =>
    congrArg A (Subtype.ext (heq ht))
  obtain ⟨Gg, hGg, hg⟩ := hU.graph
  obtain ⟨Gc, hGc, hc⟩ := hU.c1
  exact ⟨⟨mem, fun t ht => by
      rw [key t ht]; exact (hU.deriv t ht).congr_of_mem (fun x hx => heq hx) ht, h0⟩,
    ⟨Gg, hGg, fun t ht => (key t ht).trans (hg t ht)⟩,
    ⟨Gc, hGc, fun t ht => by rw [key t ht]; exact hc t ht⟩⟩

omit [CompleteSpace E] in
/-- For `T < 0` the interval `[0,T]` is empty and only the initial condition is required. -/
theorem isClassicalSolution_of_neg {T : ℝ} {U₀ : E} {F U : ℝ → E} (hT : T < 0) (h0 : U 0 = U₀) :
    IsClassicalSolution A T U₀ F U := by
  have hE : ∀ t, t ∉ Icc (0 : ℝ) T := fun t ht => absurd (ht.1.trans ht.2) (not_le.2 hT)
  exact ⟨⟨fun t ht => (hE t ht).elim, fun t ht => (hE t ht).elim, h0⟩,
    ⟨0, fun t ht => (hE t ht).elim, fun t ht => (hE t ht).elim⟩,
    ⟨0, fun t ht => (hE t ht).elim, fun t ht => (hE t ht).elim⟩⟩

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
    continuousOn_const.add (ForcingClass.continuousOn_primitive ht hk)
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
  suffices hε : ∀ ε > 0, ‖D‖ ≤ ε * C by
    have := eq_zero_of_forall_norm_le_mul hC hε
    linarith
  intro ε hε
  -- a continuous approximation of `g` in `L¹(0,t)`
  obtain ⟨g', hg'c, hδε⟩ := exists_continuous_intervalIntegral_norm_sub_le ht hg hε
  have hg'o : IntegrableOn g' (Ioc 0 t) := hg'c.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  set δ := ∫ r in (0 : ℝ)..t, ‖g r - g' r‖ with hδ_def
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
  have hPd : ∀ r ∈ Icc 0 t, ‖P g r - P g' r‖ ≤ δ := fun r hr => by
    simp only [hP_def, add_sub_add_left_eq_sub]
    exact norm_primitive_sub_le ht hg hg'c hr
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

/-! ### Duhamel's solution and its generator image -/

/-- Duhamel's formula `U(t) = S(t) U₀ + S(t) ∫₀ᵗ S(-s) F(s) ds`. -/
def duhamelSol (U₀ : E) (F : ℝ → E) (τ : ℝ) : E :=
  G.S τ U₀ + G.S τ (∫ r in (0 : ℝ)..τ, G.S (-r) (F r))

omit [CompleteSpace E] in
theorem duhamelSol_zero (U₀ : E) (F : ℝ → E) : G.duhamelSol U₀ F 0 = U₀ := by
  simp [duhamelSol, G.map_zero]

omit [CompleteSpace E] in
theorem S_S_neg (t : ℝ) (x : E) : G.S t (G.S (-t) x) = x := by
  have := congrArg (fun B : E →L[ℝ] E => B x) (G.map_add t (-t))
  simp only [add_neg_cancel, G.map_zero, one_apply_eq_self, mul_apply_eq_comp] at this
  exact this.symm

/-- `S(t) ∫ₐᵇ S(-r) k(r) dr = ∫ₐᵇ S(t-r) k(r) dr`. -/
theorem S_intervalIntegral_S_neg {k : ℝ → E} {a b : ℝ} (t : ℝ)
    (hk : IntervalIntegrable (fun r => G.S (-r) (k r)) volume a b) :
    G.S t (∫ r in a..b, G.S (-r) (k r)) = ∫ r in a..b, G.S (t - r) (k r) := by
  rw [← (G.S t).intervalIntegral_comp_comm hk]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [sub_eq_add_neg, G.map_add, mul_apply_eq_comp]

omit [CompleteSpace E] in
/-- If `w ∈ D(A)`, then `S(t) U₀ + S(t) w ∈ D(A)` with `A(S(t) U₀ + S(t) w) = S(t) A U₀ + S(t) A w`. -/
theorem exists_apply_S_add_S {U₀ w v : E} (hU₀ : U₀ ∈ A.domain)
    (hw : ∃ h : w ∈ A.domain, A ⟨w, h⟩ = v) (t : ℝ) :
    ∃ h : G.S t U₀ + G.S t w ∈ A.domain, A ⟨_, h⟩ = G.S t (A ⟨U₀, hU₀⟩) + G.S t v := by
  obtain ⟨hw, hv⟩ := hw
  refine ⟨A.domain.add_mem (G.mem_domain_apply ⟨U₀, hU₀⟩ t) (G.mem_domain_apply ⟨w, hw⟩ t), ?_⟩
  have e : (⟨G.S t U₀ + G.S t w, A.domain.add_mem (G.mem_domain_apply ⟨U₀, hU₀⟩ t)
      (G.mem_domain_apply ⟨w, hw⟩ t)⟩ : A.domain) =
      ⟨_, G.mem_domain_apply ⟨U₀, hU₀⟩ t⟩ + ⟨_, G.mem_domain_apply ⟨w, hw⟩ t⟩ := rfl
  rw [e, LinearPMap.map_add, G.apply_comm, G.apply_comm, hv]

/-- Duhamel's solution is classical once `∫₀ᵗ S(-s) F(s) ds ∈ D(A)` with a continuous image
`V(t)` on `[0,T]`; then `A U(t) = S(t) A U₀ + S(t) V(t)`. (`F` need only be continuous on
`[0,T]`.) -/
theorem duhamel_of_domain {T : ℝ} (hT : 0 ≤ T) {U₀ : E} (hU₀ : U₀ ∈ A.domain) {F V : ℝ → E}
    (hFc : ContinuousOn F (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hw : ∀ t ∈ Icc 0 T, ∃ h : (∫ r in (0 : ℝ)..t, G.S (-r) (F r)) ∈ A.domain, A ⟨_, h⟩ = V t) :
    IsClassicalSolution A T U₀ F (G.duhamelSol U₀ F) ∧
      ∀ t ∈ Icc 0 T, ∃ h : G.duhamelSol U₀ F t ∈ A.domain,
        A ⟨_, h⟩ = G.S t (A ⟨U₀, hU₀⟩) + G.S t (V t) := by
  set Pr := projIcc 0 T hT
  set Fe : ℝ → E := fun r => F (Pr r) with hFe
  have hFe_c : Continuous Fe :=
    hFc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun r => (Pr r).2
  have hP : ∀ t ∈ Icc 0 T, Fe t = F t := fun t ht => by
    simp only [Fe, Pr, projIcc_of_mem hT ht]
  have hcongr : ∀ t ∈ Icc 0 T, (∫ r in (0 : ℝ)..t, G.S (-r) (Fe r)) =
      ∫ r in (0 : ℝ)..t, G.S (-r) (F r) := by
    intro t ht
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.1] at hr
    rw [hP r ⟨hr.1, hr.2.trans ht.2⟩]
  have hU := G.isClassicalSolution_duhamel hU₀ hFe_c hP hV fun t ht => by
    rw [hcongr t ht]; exact hw t ht
  refine ⟨hU.congr (fun t ht => ?_) (G.duhamelSol_zero U₀ F),
    fun t ht => G.exists_apply_S_add_S hU₀ (hw t ht) t⟩
  simp only [duhamelSol, hcongr t ht]

/-- **Thesis Thm 4.3, `W^{1,1}` branch, with the explicit generator image.** For `T ≥ 0`,
`U₀ ∈ D(A)`, `F` continuous on `[0,T]` with `F(t) = F(0) + ∫₀ᵗ g` (`g ∈ L¹(0,T; X)`), Duhamel's
`U` is a classical solution and, for `t ∈ [0,T]`,
`A U(t) = S(t) A U₀ + S(t) F(0) + ∫₀ᵗ S(t-s) g(s) ds - F(t)`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2, Thm 2.9]. -/
theorem duhamel_W11 {T : ℝ} (hT : 0 ≤ T) {U₀ : E} (hU₀ : U₀ ∈ A.domain) {F g : ℝ → E}
    (hFc : ContinuousOn F (Icc 0 T)) (hg : IntegrableOn g (Ioc 0 T))
    (hpt : ∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, g s) :
    IsClassicalSolution A T U₀ F (G.duhamelSol U₀ F) ∧
      ∀ t ∈ Icc 0 T, ∃ h : G.duhamelSol U₀ F t ∈ A.domain,
        A ⟨_, h⟩ = G.S t (A ⟨U₀, hU₀⟩) + G.S t (F 0) + (∫ s in (0 : ℝ)..t, G.S (t - s) (g s)) -
          F t := by
  have hgi : IntervalIntegrable (fun r => G.S (-r) (g r)) volume 0 T :=
    G.intervalIntegrable_apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hg)
      continuous_neg
  have hJc : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, G.S (-r) (g r)) (Icc 0 T) :=
    ForcingClass.continuousOn_primitive hT
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hgi)
  have hdom : ∀ t ∈ Icc 0 T, ∃ h : (∫ r in (0 : ℝ)..t, G.S (-r) (F r)) ∈ A.domain,
      A ⟨_, h⟩ = F 0 + (∫ r in (0 : ℝ)..t, G.S (-r) (g r)) - G.S (-t) (F t) := by
    intro t ht
    have e : (∫ r in (0 : ℝ)..t, G.S (-r) (F r)) =
        ∫ r in (0 : ℝ)..t, G.S (-r) (F 0 + ∫ s in (0 : ℝ)..r, g s) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le ht.1] at hr
      rw [hpt r ⟨hr.1, hr.2.trans ht.2⟩]
    rw [e]
    obtain ⟨h, hval⟩ :=
      G.integral_mem_domain_of_primitive (x₀ := F 0) ht.1 (hg.mono_set (Ioc_subset_Ioc le_rfl ht.2))
    exact ⟨h, by rw [hval, ← hpt t ht]⟩
  obtain ⟨hU, hAU⟩ := G.duhamel_of_domain hT hU₀ hFc
    (V := fun t => F 0 + (∫ r in (0 : ℝ)..t, G.S (-r) (g r)) - G.S (-t) (F t))
    ((continuousOn_const.add hJc).sub
    (G.continuous_uncurry.comp_continuousOn (continuous_neg.continuousOn.prodMk hFc))) hdom
  refine ⟨hU, fun t ht => ?_⟩
  obtain ⟨h, hv⟩ := hAU t ht
  refine ⟨h, ?_⟩
  rw [hv, _root_.map_sub, _root_.map_add, G.S_intervalIntegral_S_neg t (hgi.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2)), G.S_S_neg]
  abel

/-- **Thesis Thm 4.3, `L¹(0,T; D(A))` branch, with the explicit generator image.** For `T ≥ 0`,
`U₀ ∈ D(A)`, `F` continuous on `[0,T]` with `F(t) ∈ D(A)` and `A F(t) = H(t)` for a.e. `t`,
`H ∈ L¹(0,T; X)`, Duhamel's `U` is a classical solution and, for `t ∈ [0,T]`,
`A U(t) = S(t) A U₀ + ∫₀ᵗ S(t-s) H(s) ds`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2, Cor 2.6]. -/
theorem duhamel_L1 {T : ℝ} (hT : 0 ≤ T) {U₀ : E} (hU₀ : U₀ ∈ A.domain) {F H : ℝ → E}
    (hFc : ContinuousOn F (Icc 0 T)) (hH : IntegrableOn H (Ioc 0 T))
    (hD : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∃ h : F t ∈ A.domain, A ⟨F t, h⟩ = H t) :
    IsClassicalSolution A T U₀ F (G.duhamelSol U₀ F) ∧
      ∀ t ∈ Icc 0 T, ∃ h : G.duhamelSol U₀ F t ∈ A.domain,
        A ⟨_, h⟩ = G.S t (A ⟨U₀, hU₀⟩) + ∫ s in (0 : ℝ)..t, G.S (t - s) (H s) := by
  have hHi : IntervalIntegrable (fun r => G.S (-r) (H r)) volume 0 T :=
    G.intervalIntegrable_apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hH)
      continuous_neg
  have hJc : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, G.S (-r) (H r)) (Icc 0 T) :=
    ForcingClass.continuousOn_primitive hT
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hHi)
  have hdom : ∀ t ∈ Icc 0 T, ∃ h : (∫ r in (0 : ℝ)..t, G.S (-r) (F r)) ∈ A.domain,
      A ⟨_, h⟩ = ∫ r in (0 : ℝ)..t, G.S (-r) (H r) := by
    intro t ht
    refine G.integral_mem_domain_of_L1 ht.1 (hFc.mono (Icc_subset_Icc le_rfl ht.2))
      (hH.mono_set (Ioc_subset_Ioc le_rfl ht.2)) ?_
    have h1 : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)), ∃ h : F s ∈ A.domain, A ⟨F s, h⟩ = H s :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2) hD
    rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
  obtain ⟨hU, hAU⟩ := G.duhamel_of_domain hT hU₀ hFc hJc hdom
  refine ⟨hU, fun t ht => ?_⟩
  obtain ⟨h, hv⟩ := hAU t ht
  exact ⟨h, by rw [hv, G.S_intervalIntegral_S_neg t (hHi.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2))]⟩

/-! ### Thm 4.3 -/

include G in
/-- **Classical solutions for the admissible forcing class** (Thesis Thm 4.3, existence): for
`U₀ ∈ D(A)` and `F ∈ C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))` (`ForcingClass.admissible`)
there is a classical solution `U ∈ C⁰([0,T]; D(A)) ∩ C¹([0,T]; X)` of `U' = A U + F`,
`U(0) = U₀`, namely Duhamel's `U = G.duhamelSol U₀ F`. The generator image `A U(t)` is given
explicitly in `duhamel_W11` and `duhamel_L1`. Every smaller forcing class
(`ForcingClass.contDomain`, `ForcingClass.derivOffCountable`, `ForcingThm43`) follows by
`WellPosedClassical.mono`. See [QuennevilleBelair2015, Thm 4.3]; cf.
[CazenaveHaraux1998, Prop 4.1.6], [Pazy1983, §4.2]. -/
theorem wellPosedClassical_admissible (T : ℝ) :
    WellPosedClassical A T (ForcingClass.admissible A T) := by
  rintro U₀ hU₀ F ⟨hFc, hF⟩
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨_, isClassicalSolution_of_neg hT (G.duhamelSol_zero U₀ F)⟩
  rcases hF with hW | ⟨H, hH, hD⟩
  · obtain ⟨g, hg, hpt⟩ := (ForcingClass.w11_iff hFc).1 hW
    exact ⟨_, (G.duhamel_W11 hT hU₀ hFc hg hpt).1⟩
  · exact ⟨_, (G.duhamel_L1 hT hU₀ hFc hH hD).1⟩

@[deprecated (since := "2026-10-16")] alias wellPosedClassical_thm43Full :=
  wellPosedClassical_admissible

include G in
/-- **Thesis Thm 4.3 (existence), `W^{1,1}`-type forcing** (`ForcingW11`, continuous with an
integrable derivative off a countable set). Corollary of `wellPosedClassical_admissible`.
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §4.2, Cor 4.2.5]. -/
theorem wellPosedClassical_W11 (T : ℝ) : WellPosedClassical A T (ForcingW11 T) :=
  (G.wellPosedClassical_admissible T).mono fun _ hF => ForcingClass.derivOffCountable.admissible hF

include G in
/-- **Thesis Thm 4.3 (existence)** for `ForcingThm43 = C([0,T]; D(A)) ∪ ForcingW11`.
Corollary of `wellPosedClassical_admissible`. See [QuennevilleBelair2015, Thm 4.3]. -/
theorem wellPosedClassical_thm43 (T : ℝ) : WellPosedClassical A T (ForcingThm43 A T) :=
  (G.wellPosedClassical_admissible T).mono fun _ hF => hF.admissible

end UnitaryGroupGenerator

/-- **Classical well-posedness for every skew-adjoint generator**: for any forcing class `Adm`
contained in `ForcingClass.admissible A T`, `WellPosedClassical A T Adm`, from Stone's theorem.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedClassical_of_le (hA : IsSkewAdjoint A) {T : ℝ}
    {Adm : (ℝ → E) → Prop} (hAdm : ∀ F, Adm F → ForcingClass.admissible A T F) :
    WellPosedClassical A T Adm :=
  ((stoneGroup hA).wellPosedClassical_admissible T).mono hAdm

/-- Classical solutions of `U' = A U + F` for every skew-adjoint `A` and every forcing in the
thesis' class `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))`, from Stone's theorem.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedClassical_thm43Full (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedClassical A T (ForcingThm43Full A T) :=
  hA.wellPosedClassical_of_le fun _ hF => hF

/-- `WellPosedExistence A T (ForcingThm43Full A T)` for every skew-adjoint `A`: the existence
hypothesis of `Feec.Foundation.Evolution` holds for the thesis' full forcing class.
See [QuennevilleBelair2015, Thm 4.3]. -/
theorem IsSkewAdjoint.wellPosedExistence_thm43Full (hA : IsSkewAdjoint A) (T : ℝ) :
    WellPosedExistence A T (ForcingThm43Full A T) :=
  (hA.wellPosedClassical_thm43Full T).wellPosedExistence

/-- **Existence and uniqueness for skew-adjoint generators** (Thesis Thm 4.3, as stated): for
`A` skew-adjoint (its domain is then dense), `U₀ ∈ D(A)` and `F` admissible
(`F ∈ C([0,T], X)` in at least one of `W^{1,1}(0,T; X)` and `L¹(0,T; D(A))`), there is a
solution `U ∈ C⁰([0,T], D(A)) ∩ C¹([0,T], X)` of `U' = A U + F`, `U(0) = U₀`, and it is unique
among strong solutions (a larger class than `C⁰(D(A)) ∩ C¹(X)`). Uniqueness is
`IsStrongSolution.unique`. The statements for smaller forcing classes (`thm_4_3_unconditional`,
`thm_4_3_of_isSkewAdjoint`) and for the Hodge wave operator are corollaries.
See [QuennevilleBelair2015, Thm 4.3]; cf. [CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9]. -/
theorem IsSkewAdjoint.existsUnique_classicalSolution (hA : IsSkewAdjoint A) (T : ℝ) {U₀ : E}
    (hU₀ : U₀ ∈ A.domain) {F : ℝ → E} (hF : ForcingClass.admissible A T F) :
    ∃ U, IsClassicalSolution A T U₀ F U ∧
      ∀ U', IsStrongSolution A T U₀ F U' → EqOn U' U (Icc 0 T) := by
  obtain ⟨U, hU⟩ := (hA.wellPosedClassical_of_le fun _ h => h) U₀ hU₀ F hF
  exact ⟨U, hU, fun U' hU' =>
    hU'.unique (hA.isSkewSymm hA.dense_domain).isDissipative hU.toIsStrongSolution⟩

@[deprecated (since := "2026-10-16")] alias thm_4_3_full :=
  IsSkewAdjoint.existsUnique_classicalSolution

end Feec
