module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Forcing classes for `U' = A U + F`

The admissible forcing terms of the inhomogeneous evolution problem `U' = A U + F` on a time
interval `[a,b]`, as predicates `Evolution.ForcingClass.* A a b F` (any scalar ring `𝕜`, in
particular `ℝ` and `ℂ`), with the inclusions between them.

* `ForcingClass.contDomain A a b F`: `F ∈ C([a,b]; D(A))` (graph norm).
* `ForcingClass.derivOffCountable a b F`: `F` continuous on `[a,b]`, differentiable on `(a,b)`
  off a countable set, with an integrable derivative (contains `C¹([a,b]; X)` and
  piecewise-`C¹` forcing).
* `ForcingClass.w11 a b F`: `F ∈ W^{1,1}(a,b; X)`, i.e. `F = x₀ + ∫ₐ^· g` a.e. on `(a,b)` with
  `g ∈ L¹(a,b; X)` ([CazenaveHaraux1998], Ch. 1; `g` is the weak derivative).
* `ForcingClass.l1Domain A a b F`: `F ∈ L¹(a,b; D(A))`: `F(t) ∈ D(A)` a.e. with `A F` a.e. equal
  to an integrable function.
* `ForcingClass.admissible A a b F := ContinuousOn F [a,b] ∧ (w11 a b F ∨ l1Domain A a b F)`: the
  class of [QuennevilleBelair2015], Thm 4.3, `C([a,b]; X) ∩ (W^{1,1}(a,b; X) ∪ L¹(a,b; D(A)))`.

Inclusions: `contDomain.admissible`, `derivOffCountable.admissible`, `admissible_of_C1`, and
`ForcingClass.w11_iff` (for continuous `F`, the a.e. identity holds pointwise with `x₀ = F a`).

The real, `[0,T]` predicates `Feec.ForcingClass.* A T F` and the older names `ForcingDL`,
`ForcingW11`, `ForcingThm43`, `IsW11`, `IsL1D` and `ForcingThm43Full` are kept as abbreviations
(`a = 0`, `b = T`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.3 (Thm 4.3)
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998],
  Ch. 1 (`W^{1,p}` in time), Prop 4.1.6, Cor 2.4.9
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §4.2 (forcing in `W^{1,1}` or in `L¹(0,T; D(A))`)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter MeasureTheory

@[expose] public noncomputable section

namespace Feec

namespace Evolution.ForcingClass

variable {𝕜 E : Type*} [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [NormedSpace ℝ E]

/-- `F ∈ C([a,b]; D(A))`: `F(t) ∈ D(A)` on `[a,b]`, with `F` and `t ↦ A F(t)` continuous on
`[a,b]`. -/
def contDomain (A : E →ₗ.[𝕜] E) (a b : ℝ) (F : ℝ → E) : Prop :=
  ∃ hF : ∀ t ∈ Icc a b, F t ∈ A.domain, ContinuousOn F (Icc a b) ∧
    ∃ H : ℝ → E, ContinuousOn H (Icc a b) ∧ ∀ t (ht : t ∈ Icc a b), A ⟨F t, hF t ht⟩ = H t

/-- `F` continuous on `[a,b]`, differentiable at every point of `(a,b)` off a countable set,
with an interval-integrable derivative `F'`. Contains `C¹([a,b]; X)`; contained in
`C([a,b]; X) ∩ W^{1,1}(a,b; X)` (`derivOffCountable.admissible`). -/
def derivOffCountable (a b : ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Icc a b) ∧ ∃ (F' : ℝ → E) (s : Set ℝ), s.Countable ∧
    IntervalIntegrable F' volume a b ∧ ∀ t ∈ Ioo a b \ s, HasDerivAt F (F' t) t

/-- `F ∈ W^{1,1}(a,b; X)`: `F = x₀ + ∫ₐ^· g` a.e. on `(a,b)`, for some `x₀ ∈ X` and some `g`
Bochner integrable on `(a,b)`; `g` is then the weak derivative. Equivalence with absolute
continuity plus an integrable a.e. derivative needs the Radon–Nikodým property of `X` (true for
Hilbert spaces) and is not proved here. See [CazenaveHaraux1998], Ch. 1. -/
def w11 (a b : ℝ) (F : ℝ → E) : Prop :=
  ∃ (x₀ : E) (g : ℝ → E), IntegrableOn g (Ioc a b) ∧
    F =ᵐ[volume.restrict (Ioo a b)] fun t => x₀ + ∫ s in a..t, g s

/-- `F ∈ L¹(a,b; D(A))` (graph norm): `F(t) ∈ D(A)` for a.e. `t ∈ (a,b)`, with `t ↦ A F(t)` a.e.
equal to a Bochner integrable `H`. (Integrability of `F` itself is automatic in `admissible`,
where `F` is continuous on `[a,b]`.) -/
def l1Domain (A : E →ₗ.[𝕜] E) (a b : ℝ) (F : ℝ → E) : Prop :=
  ∃ H : ℝ → E, IntegrableOn H (Ioc a b) ∧
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∃ h : F t ∈ A.domain, A ⟨F t, h⟩ = H t

/-- The forcing class of [QuennevilleBelair2015], Thm 4.3 on `[a,b]`:
`F ∈ C([a,b], X)` and `F ∈ W^{1,1}(a,b; X) ∪ L¹(a,b; D(A))`, the hypotheses on the forcing in
the Hille–Yosida corollary the thesis cites, [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9. -/
def admissible (A : E →ₗ.[𝕜] E) (a b : ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Icc a b) ∧ (w11 a b F ∨ l1Domain A a b F)

omit [Module 𝕜 E] in
/-- The primitive `t ↦ ∫ₐᵗ g` of `g ∈ L¹(a,b)` is continuous on `[a,b]`. -/
theorem continuousOn_primitive {g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Ioc a b)) :
    ContinuousOn (fun t => ∫ s in a..t, g s) (Icc a b) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hg) left_mem_uIcc
  rwa [uIcc_of_le hab] at h

omit [Module 𝕜 E] in
/-- For continuous `F`, membership in `W^{1,1}` holds pointwise on `[a,b]`:
`F ∈ C([a,b]; X) ∩ W^{1,1}(a,b; X)` iff `F(t) = F(a) + ∫ₐᵗ g` for all `t ∈ [a,b]`, with `g`
integrable. -/
theorem w11_iff {a b : ℝ} {F : ℝ → E} (hF : ContinuousOn F (Icc a b)) :
    w11 a b F ↔ ∃ g : ℝ → E, IntegrableOn g (Ioc a b) ∧
      ∀ t ∈ Icc a b, F t = F a + ∫ s in a..t, g s := by
  constructor
  · rintro ⟨x₀, g, hg, hae⟩
    refine ⟨g, hg, ?_⟩
    rcases lt_or_ge a b with hab | hab
    · have hP : ContinuousOn (fun t => x₀ + ∫ s in a..t, g s) (Icc a b) :=
        continuousOn_const.add (continuousOn_primitive hab.le hg)
      have hae' : F =ᵐ[volume.restrict (Icc a b)] fun t => x₀ + ∫ s in a..t, g s := by
        rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
      have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne hae' hF hP
      have h0 : F a = x₀ := by
        simpa using heq (left_mem_Icc.2 hab.le)
      intro t ht
      rw [heq ht, h0]
    · intro t ht
      have : t = a := le_antisymm (ht.2.trans hab) ht.1
      subst this
      simp
  · rintro ⟨g, hg, hpt⟩
    refine ⟨F a, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hpt t (Ioo_subset_Icc_self ht)

omit [Module 𝕜 E] in
/-- A continuous `F` with a derivative `F'` on `(a,b)` off a countable set, `F'` integrable on
`(a,b)`, is in `W^{1,1}(a,b; X)` (fundamental theorem of calculus,
`integral_eq_of_hasDerivAt_off_countable_of_le`), with `g = F'`. -/
theorem w11_of_hasDerivAt [CompleteSpace E] {a b : ℝ} {F F' : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hFc : ContinuousOn F (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ s, HasDerivAt F (F' t) t) (hi : IntegrableOn F' (Ioc a b)) :
    w11 a b F := by
  refine (w11_iff hFc).2 ⟨F', hi, fun t ht => ?_⟩
  have := integral_eq_of_hasDerivAt_off_countable_of_le F F' ht.1 hs (hFc.mono
    (Icc_subset_Icc le_rfl ht.2)) (fun x hx => hd x ⟨⟨hx.1.1, hx.1.2.trans_le ht.2⟩, hx.2⟩)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2
      (hi.mono_set (Ioc_subset_Ioc le_rfl ht.2)))
  rw [this]; abel

/-- `C([a,b]; D(A))` forcing is admissible (through the `L¹(a,b; D(A))` branch). -/
theorem contDomain.admissible {A : E →ₗ.[𝕜] E} {a b : ℝ} {F : ℝ → E}
    (hF : contDomain A a b F) : ForcingClass.admissible A a b F := by
  obtain ⟨hFD, hFc, H, hHc, hH⟩ := hF
  refine ⟨hFc, Or.inr ⟨H, ?_, ?_⟩⟩
  · exact (hHc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ⟨hFD t (Ioo_subset_Icc_self ht), hH t (Ioo_subset_Icc_self ht)⟩

/-- Continuous forcing with an integrable derivative off a countable set is admissible (through
the `W^{1,1}` branch). -/
theorem derivOffCountable.admissible [CompleteSpace E] {A : E →ₗ.[𝕜] E} {a b : ℝ} {F : ℝ → E}
    (hF : derivOffCountable a b F) : ForcingClass.admissible A a b F := by
  obtain ⟨hFc, F', s, hs, hi, hd⟩ := hF
  exact ⟨hFc, Or.inl (w11_of_hasDerivAt hs hFc hd hi.1)⟩

/-- `C¹([a,b]; X)` forcing is admissible: a continuous `F` whose derivative on `(a,b)` extends
continuously to `[a,b]` (through the `W^{1,1}` branch). -/
theorem admissible_of_C1 [CompleteSpace E] {A : E →ₗ.[𝕜] E} {a b : ℝ} {F F' : ℝ → E}
    (hFc : ContinuousOn F (Icc a b)) (hF' : ContinuousOn F' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt F (F' t) t) : ForcingClass.admissible A a b F :=
  ⟨hFc, Or.inl (w11_of_hasDerivAt countable_empty hFc (fun t ht => hd t ht.1)
    ((hF'.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self))⟩

/-- Forcing terms are only seen on `[a,b]`. -/
theorem admissible.congr {A : E →ₗ.[𝕜] E} {a b : ℝ} {F G : ℝ → E}
    (hF : admissible A a b F) (hFG : EqOn F G (Icc a b)) : admissible A a b G := by
  obtain ⟨hFc, hW | ⟨H, hH, hae⟩⟩ := hF
  · obtain ⟨x₀, g, hg, hae⟩ := hW
    refine ⟨hFc.congr hFG.symm, Or.inl ⟨x₀, g, hg, ?_⟩⟩
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht ht'
    rw [← hFG (Ioo_subset_Icc_self ht'), ht]
  · refine ⟨hFc.congr hFG.symm, Or.inr ⟨H, hH, ?_⟩⟩
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht ht'
    rw [← hFG (Ioo_subset_Icc_self ht')]
    exact ht

end Evolution.ForcingClass

/-! ### The real `[0,T]` predicates -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ForcingClass

/-- `F ∈ C([0,T]; D(A))`; see `Evolution.ForcingClass.contDomain`. -/
abbrev contDomain (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  Evolution.ForcingClass.contDomain A 0 T F

/-- See `Evolution.ForcingClass.derivOffCountable`. -/
abbrev derivOffCountable (T : ℝ) (F : ℝ → E) : Prop :=
  Evolution.ForcingClass.derivOffCountable 0 T F

/-- `F ∈ W^{1,1}(0,T; X)`; see `Evolution.ForcingClass.w11`. -/
abbrev w11 (T : ℝ) (F : ℝ → E) : Prop := Evolution.ForcingClass.w11 0 T F

/-- `F ∈ L¹(0,T; D(A))`; see `Evolution.ForcingClass.l1Domain`. -/
abbrev l1Domain (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  Evolution.ForcingClass.l1Domain A 0 T F

/-- The forcing class of [QuennevilleBelair2015], Thm 4.3 on `[0,T]`; see
`Evolution.ForcingClass.admissible`. -/
abbrev admissible (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  Evolution.ForcingClass.admissible A 0 T F

theorem continuousOn_primitive {g : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hg : IntegrableOn g (Ioc 0 T)) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, g s) (Icc 0 T) :=
  Evolution.ForcingClass.continuousOn_primitive hT hg

theorem w11_iff {T : ℝ} {F : ℝ → E} (hF : ContinuousOn F (Icc 0 T)) :
    w11 T F ↔ ∃ g : ℝ → E, IntegrableOn g (Ioc 0 T) ∧
      ∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, g s :=
  Evolution.ForcingClass.w11_iff hF

theorem w11_of_hasDerivAt [CompleteSpace E] {T : ℝ} {F F' : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hFc : ContinuousOn F (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T \ s, HasDerivAt F (F' t) t) (hi : IntegrableOn F' (Ioc 0 T)) :
    w11 T F :=
  Evolution.ForcingClass.w11_of_hasDerivAt hs hFc hd hi

theorem contDomain.admissible {A : E →ₗ.[ℝ] E} {T : ℝ} {F : ℝ → E} (hF : contDomain A T F) :
    ForcingClass.admissible A T F :=
  Evolution.ForcingClass.contDomain.admissible hF

theorem derivOffCountable.admissible [CompleteSpace E] {A : E →ₗ.[ℝ] E} {T : ℝ} {F : ℝ → E}
    (hF : derivOffCountable T F) : ForcingClass.admissible A T F :=
  Evolution.ForcingClass.derivOffCountable.admissible hF

theorem admissible_of_C1 [CompleteSpace E] {A : E →ₗ.[ℝ] E} {T : ℝ} {F F' : ℝ → E}
    (hFc : ContinuousOn F (Icc 0 T)) (hF' : ContinuousOn F' (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt F (F' t) t) : ForcingClass.admissible A T F :=
  Evolution.ForcingClass.admissible_of_C1 hFc hF' hd

end ForcingClass

/-! ### Short names -/

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

/-- The forcing class of [QuennevilleBelair2015], Thm 4.3; see `ForcingClass.admissible`. -/
abbrev ForcingThm43Full (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ForcingClass.admissible A T F

/-- `ForcingThm43` is admissible. -/
theorem ForcingThm43.admissible [CompleteSpace E] {A : E →ₗ.[ℝ] E} {T : ℝ} {F : ℝ → E}
    (hF : ForcingThm43 A T F) : ForcingClass.admissible A T F :=
  hF.elim ForcingClass.contDomain.admissible ForcingClass.derivOffCountable.admissible

end Feec
