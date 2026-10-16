module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Forcing classes for `U' = A U + F`

The admissible forcing terms of the inhomogeneous evolution problem `U' = A U + F` on `[0,T]`,
as predicates `ForcingClass.* A T F`, with the inclusions between them.

* `ForcingClass.contDomain A T F`: `F ∈ C([0,T]; D(A))` (graph norm).
* `ForcingClass.derivOffCountable T F`: `F` continuous on `[0,T]`, differentiable on `(0,T)` off
  a countable set, with an integrable derivative (contains `C¹([0,T]; X)` and piecewise-`C¹`
  forcing).
* `ForcingClass.w11 T F`: `F ∈ W^{1,1}(0,T; X)`, i.e. `F = x₀ + ∫₀^· g` a.e. on `(0,T)` with
  `g ∈ L¹(0,T; X)` ([CazenaveHaraux1998, Ch. 1]; `g` is the weak derivative,
  `IsW11.exists_weakDeriv` in `Feec.Ch4.StoneForcing`).
* `ForcingClass.l1Domain A T F`: `F ∈ L¹(0,T; D(A))`: `F(t) ∈ D(A)` a.e. with `A F` a.e. equal
  to an integrable function.
* `ForcingClass.admissible A T F := ContinuousOn F [0,T] ∧ (w11 T F ∨ l1Domain A T F)`: the
  class of [QuennevilleBelair2015, Thm 4.3], `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(A)))`.

Inclusions: `contDomain.admissible`, `derivOffCountable.admissible`, `admissible_of_C1`, and
`ForcingClass.w11_iff` (for continuous `F`, the a.e. identity holds pointwise with `x₀ = F 0`).

The legacy names `ForcingDL`, `ForcingW11`, `ForcingThm43`, `IsW11`, `IsL1D` and
`ForcingThm43Full` are kept as abbreviations of these predicates.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3)
* [CazenaveHaraux1998], Ch. 1 (`W^{1,p}` in time), Prop 4.1.6
* [Pazy1983], §4.2 (forcing in `W^{1,1}` or in `L¹(0,T; D(A))`)
-/

open Set Filter MeasureTheory

@[expose] public noncomputable section

namespace Feec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ForcingClass

/-- `F ∈ C([0,T]; D(A))`: `F(t) ∈ D(A)` on `[0,T]`, with `F` and `t ↦ A F(t)` continuous on
`[0,T]`. -/
def contDomain (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ∃ hF : ∀ t ∈ Icc 0 T, F t ∈ A.domain, ContinuousOn F (Icc 0 T) ∧
    ∃ H : ℝ → E, ContinuousOn H (Icc 0 T) ∧ ∀ t (ht : t ∈ Icc 0 T), A ⟨F t, hF t ht⟩ = H t

/-- `F` continuous on `[0,T]`, differentiable at every point of `(0,T)` off a countable set,
with an interval-integrable derivative `F'`. Contains `C¹([0,T]; X)`; contained in
`C([0,T]; X) ∩ W^{1,1}(0,T; X)` (`derivOffCountable.admissible`). -/
def derivOffCountable (T : ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Icc 0 T) ∧ ∃ (F' : ℝ → E) (s : Set ℝ), s.Countable ∧
    IntervalIntegrable F' volume 0 T ∧ ∀ t ∈ Ioo 0 T \ s, HasDerivAt F (F' t) t

/-- `F ∈ W^{1,1}(0,T; X)`: `F = x₀ + ∫₀^· g` a.e. on `(0,T)`, for some `x₀ ∈ X` and some `g`
Bochner integrable on `(0,T)`; `g` is then the weak derivative. Equivalence with absolute
continuity plus an integrable a.e. derivative needs the Radon–Nikodým property of `X` (true for
Hilbert spaces) and is not proved here. See [CazenaveHaraux1998, Ch. 1]. -/
def w11 (T : ℝ) (F : ℝ → E) : Prop :=
  ∃ (x₀ : E) (g : ℝ → E), IntegrableOn g (Ioc 0 T) ∧
    F =ᵐ[volume.restrict (Ioo 0 T)] fun t => x₀ + ∫ s in (0 : ℝ)..t, g s

/-- `F ∈ L¹(0,T; D(A))` (graph norm): `F(t) ∈ D(A)` for a.e. `t ∈ (0,T)`, with `t ↦ A F(t)` a.e.
equal to a Bochner integrable `H`. (Integrability of `F` itself is automatic in `admissible`,
where `F` is continuous on `[0,T]`.) -/
def l1Domain (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ∃ H : ℝ → E, IntegrableOn H (Ioc 0 T) ∧
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∃ h : F t ∈ A.domain, A ⟨F t, h⟩ = H t

/-- The forcing class of [QuennevilleBelair2015, Thm 4.3]:
`F ∈ C([0,T], X)` and `F ∈ W^{1,1}(0,T; X) ∪ L¹(0,T; D(A))`. -/
def admissible (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Icc 0 T) ∧ (w11 T F ∨ l1Domain A T F)

/-- The primitive `t ↦ ∫₀ᵗ g` of `g ∈ L¹(0,T)` is continuous on `[0,T]`. -/
theorem continuousOn_primitive {g : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hg : IntegrableOn g (Ioc 0 T)) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, g s) (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hg) left_mem_uIcc
  rwa [uIcc_of_le hT] at h

/-- For continuous `F`, membership in `W^{1,1}` holds pointwise on `[0,T]`:
`F ∈ C([0,T]; X) ∩ W^{1,1}(0,T; X)` iff `F(t) = F(0) + ∫₀ᵗ g` for all `t ∈ [0,T]`, with `g`
integrable. -/
theorem w11_iff {T : ℝ} {F : ℝ → E} (hF : ContinuousOn F (Icc 0 T)) :
    w11 T F ↔ ∃ g : ℝ → E, IntegrableOn g (Ioc 0 T) ∧
      ∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, g s := by
  constructor
  · rintro ⟨x₀, g, hg, hae⟩
    refine ⟨g, hg, ?_⟩
    rcases lt_or_ge 0 T with hT | hT
    · have hP : ContinuousOn (fun t => x₀ + ∫ s in (0 : ℝ)..t, g s) (Icc 0 T) :=
        continuousOn_const.add (continuousOn_primitive hT.le hg)
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

/-- A continuous `F` with a derivative `F'` on `(0,T)` off a countable set, `F'` integrable on
`(0,T)`, is in `W^{1,1}(0,T; X)` (fundamental theorem of calculus,
`integral_eq_of_hasDerivAt_off_countable_of_le`), with `g = F'`. -/
theorem w11_of_hasDerivAt [CompleteSpace E] {T : ℝ} {F F' : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hFc : ContinuousOn F (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T \ s, HasDerivAt F (F' t) t) (hi : IntegrableOn F' (Ioc 0 T)) :
    w11 T F := by
  refine (w11_iff hFc).2 ⟨F', hi, fun t ht => ?_⟩
  have := integral_eq_of_hasDerivAt_off_countable_of_le F F' ht.1 hs (hFc.mono
    (Icc_subset_Icc le_rfl ht.2)) (fun x hx => hd x ⟨⟨hx.1.1, hx.1.2.trans_le ht.2⟩, hx.2⟩)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2
      (hi.mono_set (Ioc_subset_Ioc le_rfl ht.2)))
  rw [this]; abel

/-- `C([0,T]; D(A))` forcing is admissible (through the `L¹(0,T; D(A))` branch). -/
theorem contDomain.admissible {A : E →ₗ.[ℝ] E} {T : ℝ} {F : ℝ → E} (hF : contDomain A T F) :
    ForcingClass.admissible A T F := by
  obtain ⟨hFD, hFc, H, hHc, hH⟩ := hF
  refine ⟨hFc, Or.inr ⟨H, ?_, ?_⟩⟩
  · exact (hHc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ⟨hFD t (Ioo_subset_Icc_self ht), hH t (Ioo_subset_Icc_self ht)⟩

/-- Continuous forcing with an integrable derivative off a countable set is admissible (through
the `W^{1,1}` branch). -/
theorem derivOffCountable.admissible [CompleteSpace E] {A : E →ₗ.[ℝ] E} {T : ℝ} {F : ℝ → E}
    (hF : derivOffCountable T F) : ForcingClass.admissible A T F := by
  obtain ⟨hFc, F', s, hs, hi, hd⟩ := hF
  exact ⟨hFc, Or.inl (w11_of_hasDerivAt hs hFc hd hi.1)⟩

/-- `C¹([0,T]; X)` forcing is admissible: a continuous `F` whose derivative on `(0,T)` extends
continuously to `[0,T]` (through the `W^{1,1}` branch). -/
theorem admissible_of_C1 [CompleteSpace E] {A : E →ₗ.[ℝ] E} {T : ℝ} {F F' : ℝ → E}
    (hFc : ContinuousOn F (Icc 0 T)) (hF' : ContinuousOn F' (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt F (F' t) t) : ForcingClass.admissible A T F :=
  ⟨hFc, Or.inl (w11_of_hasDerivAt countable_empty hFc (fun t ht => hd t ht.1)
    ((hF'.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self))⟩

end ForcingClass

/-! ### Legacy names -/

/-- The forcing class `C([0,T]; D(A))`; see `ForcingClass.contDomain`. -/
abbrev ForcingDL (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop := ForcingClass.contDomain A T F

/-- The `W^{1,1}`-type forcing class of continuous `F` with an integrable derivative off a
countable set; see `ForcingClass.derivOffCountable`. -/
abbrev ForcingW11 (T : ℝ) (F : ℝ → E) : Prop := ForcingClass.derivOffCountable T F

/-- `C([0,T]; D(A)) ∪ ForcingW11`, a subclass of `ForcingClass.admissible`
(`forcingThm43Full_of_forcingThm43`). Cf. the thesis' `C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪
L¹(0,T; D(A)))`. -/
def ForcingThm43 (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ForcingDL A T F ∨ ForcingW11 T F

/-- `F ∈ W^{1,1}(0,T; X)`; see `ForcingClass.w11`. -/
abbrev IsW11 (T : ℝ) (F : ℝ → E) : Prop := ForcingClass.w11 T F

/-- `F ∈ L¹(0,T; D(A))`; see `ForcingClass.l1Domain`. -/
abbrev IsL1D (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop := ForcingClass.l1Domain A T F

/-- The forcing class of [QuennevilleBelair2015, Thm 4.3]; see `ForcingClass.admissible`. -/
abbrev ForcingThm43Full (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ForcingClass.admissible A T F

/-- `ForcingThm43` is admissible. -/
theorem ForcingThm43.admissible [CompleteSpace E] {A : E →ₗ.[ℝ] E} {T : ℝ} {F : ℝ → E}
    (hF : ForcingThm43 A T F) : ForcingClass.admissible A T F :=
  hF.elim ForcingClass.contDomain.admissible ForcingClass.derivOffCountable.admissible

@[deprecated (since := "2026-10-16")] alias continuousOn_primitive_Icc_of_integrableOn :=
  ForcingClass.continuousOn_primitive

@[deprecated (since := "2026-10-16")] alias isW11_iff := ForcingClass.w11_iff

@[deprecated (since := "2026-10-16")] alias isW11_of_hasDerivAt := ForcingClass.w11_of_hasDerivAt

@[deprecated (since := "2026-10-16")] alias forcingThm43Full_of_C1 := ForcingClass.admissible_of_C1

@[deprecated (since := "2026-10-16")] alias forcingThm43Full_of_forcingThm43 :=
  ForcingThm43.admissible

end Feec
