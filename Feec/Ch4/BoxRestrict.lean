module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Feec.Ch4.TorusWeak

/-!
# Restriction to the box `(0, ½)³ ⊂ 𝕋³`, and trigonometric polynomials

Auxiliary file for the box model of `Feec.Ch4.Box`. The box `Q = (0, ½)³` is a fundamental
domain of the reflection group `(ℤ/2)³` acting on `𝕋³ = ℝ³/ℤ³` by `x_i ↦ -x_i`; the method of
images models fields on `Q` by fields on `𝕋³` with prescribed parities. Conditions "on the box"
(symmetry, trace) relate fields of *different* parities, and are not Fourier-diagonal; this file
supplies the analytic tool that handles them for trigonometric polynomials.

## Main results

* `boxSet`, the open box `Q` in `𝕋³` (`isOpen_boxSet`), and `ZeroOnBox f`: the function with
  Fourier coefficients `f` vanishes a.e. on `Q`. Characterization by orthogonality to the
  functions supported off `Q` (`zeroOnBox_iff`), hence `ZeroOnBox` defines a closed subspace
  (`boxZero`, `isClosed_boxZero`).
* **`eq_zero_of_zeroOnBox_of_finite`**: a trigonometric polynomial (finitely many nonzero
  coefficients) that vanishes a.e. on `Q` is zero. Proof: it is continuous, so it vanishes on
  the open set `Q`; its lift to `ℝ³` is real-analytic (a finite sum of exponentials) and vanishes
  on an open set, so it vanishes identically (identity theorem,
  `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`).

## References

* [QuennevilleBelair2015], §4.10 (bounded domains), §3.4
* [Brezis2011] (`L²` spaces)
-/

@[expose] public noncomputable section

open scoped ENNReal ComplexConjugate InnerProductSpace
open MeasureTheory Set Filter Topology Complex

namespace Feec.Box

open Feec.Torus Feec.TorusWeak UnitAddTorus

attribute [local instance] Feec.Torus.instMeasureSpaceUnitAddCircle_feec

/-- The local Haar measure on `ℝ/ℤ` is an additive Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The open arc `(0, ½)` of `ℝ/ℤ`. -/
def halfArc : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Ioo 0 (1 / 2)

/-- The open box `Q = (0, ½)³` in `𝕋³`. -/
def boxSet : Set T3 := univ.pi fun _ => halfArc

/-- The box is open. -/
theorem isOpen_boxSet : IsOpen boxSet :=
  isOpen_set_pi finite_univ fun _ _ => QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- The box is measurable. -/
theorem measurableSet_boxSet : MeasurableSet boxSet := isOpen_boxSet.measurableSet

/-- Points of `(0, ½)³ ⊂ ℝ³` project into the box. -/
theorem proj_mem_boxSet {y : Fin 3 → ℝ} (hy : ∀ i, y i ∈ Ioo (0 : ℝ) (1 / 2)) :
    proj y ∈ boxSet := fun i _ => ⟨y i, hy i, rfl⟩

/-- `ZeroOnBox f`: the `L²(𝕋³)` function with Fourier coefficients `f` vanishes almost
everywhere on the box `Q = (0, ½)³`. -/
def ZeroOnBox (f : L2 Z3 ℂ) : Prop := (ofCoeff f : T3 → ℂ) =ᵐ[volume.restrict boxSet] 0

/-- Functions vanishing a.e. on `s` and functions vanishing a.e. off `s` are orthogonal. -/
theorem inner_eq_zero_of_ae {s : Set T3} {g φ : L2T}
    (hg : (g : T3 → ℂ) =ᵐ[volume.restrict s] 0) (hφ : (φ : T3 → ℂ) =ᵐ[volume.restrict sᶜ] 0) :
    ⟪g, φ⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have h : (fun x => ⟪g x, φ x⟫_ℂ) =ᵐ[volume] 0 := by
    have hu : ∀ᵐ x ∂volume.restrict (s ∪ sᶜ), ⟪g x, φ x⟫_ℂ = 0 := by
      rw [ae_restrict_union_iff]
      exact ⟨hg.mono fun x hx => by simp [hx], hφ.mono fun x hx => by simp [hx]⟩
    rwa [union_compl_self, Measure.restrict_univ] at hu
  rw [integral_congr_ae h]
  simp

/-- **Characterization of `ZeroOnBox`** by orthogonality to every `L²` function supported off the
box. -/
theorem zeroOnBox_iff (f : L2 Z3 ℂ) :
    ZeroOnBox f ↔ ∀ φ : L2T, (φ : T3 → ℂ) =ᵐ[volume.restrict boxSetᶜ] 0 →
      ⟪ofCoeff f, φ⟫_ℂ = 0 := by
  refine ⟨fun h φ hφ => inner_eq_zero_of_ae h hφ, fun h => ?_⟩
  set g : L2T := ofCoeff f
  have hm : MemLp (boxSet.indicator (g : T3 → ℂ)) 2 volume :=
    (Lp.memLp g).indicator measurableSet_boxSet.nullMeasurableSet
  set φ : L2T := hm.toLp _
  have hφ : (φ : T3 → ℂ) =ᵐ[volume] boxSet.indicator g := hm.coeFn_toLp
  have hoff : (φ : T3 → ℂ) =ᵐ[volume.restrict boxSetᶜ] 0 := by
    refine EventuallyEq.trans (ae_restrict_of_ae hφ) ?_
    filter_upwards [ae_restrict_mem measurableSet_boxSet.compl] with x hx
    simp [indicator_of_notMem hx]
  have h0 := h φ hoff
  rw [MeasureTheory.L2.inner_def] at h0
  have e : (fun x => ⟪(g : T3 → ℂ) x, (φ : T3 → ℂ) x⟫_ℂ) =ᵐ[volume]
      boxSet.indicator fun x => ((‖(g : T3 → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hφ] with x hx
    rw [hx]
    by_cases hb : x ∈ boxSet
    · rw [indicator_of_mem hb, indicator_of_mem hb, RCLike.inner_apply,
        Complex.mul_conj']
      push_cast; rfl
    · rw [indicator_of_notMem hb, indicator_of_notMem hb, inner_zero_right]
  rw [integral_congr_ae e, integral_indicator measurableSet_boxSet, integral_complex_ofReal]
    at h0
  have hint : Integrable (fun x => ‖(g : T3 → ℂ) x‖ ^ 2) (volume.restrict boxSet) :=
    ((Lp.memLp g).integrable_norm_pow two_ne_zero).restrict
  have h1 := (integral_eq_zero_iff_of_nonneg (fun _ => by positivity) hint).1
    (Complex.ofReal_eq_zero.1 h0)
  filter_upwards [h1] with x hx
  simpa using hx

/-- `ZeroOnBox` as a closed (complex) subspace of `ℓ²(ℤ³)`. -/
def boxZero : Submodule ℂ (L2 Z3 ℂ) where
  carrier := {f | ZeroOnBox f}
  zero_mem' := by
    simp only [mem_ofPred_eq, zeroOnBox_iff, ofCoeff, map_zero, inner_zero_left, implies_true]
  add_mem' := by
    intro f g hf hg
    simp only [mem_ofPred_eq, zeroOnBox_iff] at hf hg ⊢
    intro φ hφ
    rw [ofCoeff, map_add, inner_add_left, ← ofCoeff, ← ofCoeff, hf φ hφ, hg φ hφ, add_zero]
  smul_mem' := by
    intro c f hf
    simp only [mem_ofPred_eq, zeroOnBox_iff] at hf ⊢
    intro φ hφ
    rw [ofCoeff, map_smul, inner_smul_left, ← ofCoeff, hf φ hφ, mul_zero]

/-- Membership in `boxZero`. -/
theorem mem_boxZero {f : L2 Z3 ℂ} : f ∈ boxZero ↔ ZeroOnBox f := Iff.rfl

/-- `boxZero` is closed. -/
theorem isClosed_boxZero : IsClosed (boxZero : Set (L2 Z3 ℂ)) := by
  have e : (boxZero : Set (L2 Z3 ℂ)) = ⋂ φ : {φ : L2T // (φ : T3 → ℂ) =ᵐ[volume.restrict boxSetᶜ] 0},
      {f | ⟪ofCoeff f, (φ : L2T)⟫_ℂ = 0} := by
    ext f
    simp only [SetLike.mem_coe, mem_boxZero, zeroOnBox_iff, mem_iInter, mem_ofPred_eq,
      Subtype.forall]
  rw [e]
  refine isClosed_iInter fun φ => isClosed_eq ?_ continuous_const
  exact (continuous_id.inner continuous_const).comp (mFourierBasis.repr.symm.continuous)

/-! ## Trigonometric polynomials vanishing on the box -/

/-- An `ℓ²` sequence with finite support is a finite sum of single modes. -/
theorem eq_sum_single_of_finite {f : L2 Z3 ℂ} (S : Finset Z3) (hS : ∀ k ∉ S, f k = 0) :
    f = ∑ k ∈ S, lp.single 2 k (f k) := by
  ext j
  have : ((∑ k ∈ S, lp.single 2 k (f k) : L2 Z3 ℂ) : Z3 → ℂ) j =
      ∑ k ∈ S, (lp.single 2 k (f k) : Z3 → ℂ) j := by
    change lp.evalCLM ℂ (fun _ : Z3 => ℂ) 2 j (∑ k ∈ S, lp.single 2 k (f k)) =
      ∑ k ∈ S, lp.evalCLM ℂ (fun _ : Z3 => ℂ) 2 j (lp.single 2 k (f k))
    exact map_sum _ _ _
  rw [this]
  by_cases hj : j ∈ S
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [lp.single_apply, Ne.symm hk])
      (fun h => absurd hj h)]
    simp
  · rw [hS j hj, Finset.sum_eq_zero fun k hk => ?_]
    have : j ≠ k := fun h => hj (h ▸ hk)
    simp [lp.single_apply, this]

/-- The trigonometric polynomial with coefficients `f` on the finite set `S`, as a function. -/
def trigPoly (f : L2 Z3 ℂ) (S : Finset Z3) : C(T3, ℂ) := ∑ k ∈ S, f k • mFourier k

/-- A finitely supported coefficient sequence is the `L²` class of its trigonometric
polynomial. -/
theorem ofCoeff_eq_toLp {f : L2 Z3 ℂ} (S : Finset Z3) (hS : ∀ k ∉ S, f k = 0) :
    ofCoeff f = (trigPoly f S).toLp 2 volume ℂ := by
  classical
  conv_lhs => rw [eq_sum_single_of_finite S hS]
  rw [ofCoeff, map_sum, trigPoly, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : lp.single 2 k (f k) = f k • lp.single (E := fun _ : Z3 => ℂ) 2 k 1 := by
    rw [← lp.single_smul]; simp
  rw [this, map_smul, HilbertBasis.repr_symm_single, coe_mFourierBasis, map_smul]

/-- The lift of a trigonometric polynomial to `ℝ³` is real-analytic. -/
theorem analyticOnNhd_trigPoly_proj (f : L2 Z3 ℂ) (S : Finset Z3) :
    AnalyticOnNhd ℝ (fun y => trigPoly f S (proj y)) univ := by
  intro y _
  have e : (fun y => trigPoly f S (proj y)) =
      fun y => ∑ k ∈ S, f k * cexp (2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ)) := by
    funext y
    simp only [trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mFourier_proj]
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ?_
  have hl : AnalyticAt ℝ (fun y : Fin 3 → ℝ => 2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ)) y := by
    refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ?_)
    exact (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).analyticAt y)
  have hc : AnalyticAt ℝ cexp (2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ)) :=
    (analyticAt_cexp (z := 2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ))).restrictScalars
      (𝕜 := ℝ) (𝕜' := ℂ) (E := ℂ) (F := ℂ)
  exact AnalyticAt.comp (f := fun y : Fin 3 → ℝ => 2 * Real.pi * I * ∑ i, (k i : ℂ) * (y i : ℂ))
    (g := cexp) hc hl

/-- **A trigonometric polynomial vanishing a.e. on the box is zero.** -/
theorem eq_zero_of_zeroOnBox_of_finite {f : L2 Z3 ℂ} (S : Finset Z3) (hS : ∀ k ∉ S, f k = 0)
    (hf : ZeroOnBox f) : f = 0 := by
  have hg := ofCoeff_eq_toLp S hS
  set h := trigPoly f S
  have h1 : (ofCoeff f : T3 → ℂ) =ᵐ[volume] h := by
    rw [hg]; exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := volume) h
  have hae : (h : T3 → ℂ) =ᵐ[volume.restrict boxSet] 0 :=
    EventuallyEq.trans (EventuallyEq.symm (ae_restrict_of_ae h1 :
      (ofCoeff f : T3 → ℂ) =ᵐ[volume.restrict boxSet] h)) hf
  have hon : EqOn (h : T3 → ℂ) 0 boxSet :=
    Measure.eqOn_open_of_ae_eq hae isOpen_boxSet h.continuous.continuousOn continuousOn_const
  set y₀ : Fin 3 → ℝ := fun _ => 1 / 4
  have hV : (univ.pi fun _ : Fin 3 => Ioo (0 : ℝ) (1 / 2)) ∈ 𝓝 y₀ :=
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).mem_nhds fun i _ => by
      simp only [y₀, mem_Ioo]; constructor <;> norm_num
  have hev : (fun y => h (proj y)) =ᶠ[𝓝 y₀] 0 :=
    Filter.mem_of_superset hV fun y hy => hon (proj_mem_boxSet fun i => hy i (mem_univ i))
  have hall := (analyticOnNhd_trigPoly_proj f S).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ y₀) hev
  have h0 : h = 0 := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective x
    exact hall (mem_univ y)
  have : ofCoeff f = 0 := by rw [hg, h0, map_zero]
  rw [ofCoeff] at this
  simpa using congrArg mFourierBasis.repr this

end Feec.Box
