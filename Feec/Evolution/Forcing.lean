module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Forcing classes for `U' = A U + F`

Forcing classes for `U' = A U + F` on `[a,b]`, among them the admissible class
`C([a,b]; X) ∩ (W^{1,1}(a,b; X) ∪ L¹(a,b; D(A)))`, with the inclusions between them.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter MeasureTheory

@[expose] public noncomputable section

namespace Feec

namespace Evolution.ForcingClass

variable {𝕜 E : Type*} [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [NormedSpace ℝ E]

/-- `F ∈ C([a,b]; D(A))`: `F(t) ∈ D(A)`, with `F` and `A F` continuous on `[a,b]`. -/
def contDomain (A : E →ₗ.[𝕜] E) (a b : ℝ) (F : ℝ → E) : Prop :=
  ∃ hF : ∀ t ∈ Icc a b, F t ∈ A.domain, ContinuousOn F (Icc a b) ∧
    ∃ H : ℝ → E, ContinuousOn H (Icc a b) ∧ ∀ t (ht : t ∈ Icc a b), A ⟨F t, hF t ht⟩ = H t

/-- `F` continuous on `[a,b]` with an integrable derivative off a countable set. -/
def derivOffCountable (a b : ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Icc a b) ∧ ∃ (F' : ℝ → E) (s : Set ℝ), s.Countable ∧
    IntervalIntegrable F' volume a b ∧ ∀ t ∈ Ioo a b \ s, HasDerivAt F (F' t) t

/-- `F ∈ W^{1,1}(a,b; X)`: `F = x₀ + ∫ₐ^· g` a.e. on `(a,b)` with `g` integrable.
[CazenaveHaraux1998], Ch. 1 -/
def w11 (a b : ℝ) (F : ℝ → E) : Prop :=
  ∃ (x₀ : E) (g : ℝ → E), IntegrableOn g (Ioc a b) ∧
    F =ᵐ[volume.restrict (Ioo a b)] fun t => x₀ + ∫ s in a..t, g s

/-- `F(t) ∈ D(A)` for a.e. `t ∈ (a,b)`, with `A F` a.e. equal to an integrable function. -/
def l1Domain (A : E →ₗ.[𝕜] E) (a b : ℝ) (F : ℝ → E) : Prop :=
  ∃ H : ℝ → E, IntegrableOn H (Ioc a b) ∧
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∃ h : F t ∈ A.domain, A ⟨F t, h⟩ = H t

/-- The forcing class `C([a,b]; X) ∩ (W^{1,1}(a,b; X) ∪ L¹(a,b; D(A)))` of [QuennevilleBelair2015],
Thm 4.3; [CazenaveHaraux1998], Prop 4.1.6, Cor 2.4.9 -/
def admissible (A : E →ₗ.[𝕜] E) (a b : ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Icc a b) ∧ (w11 a b F ∨ l1Domain A a b F)

omit [Module 𝕜 E] in
theorem continuousOn_primitive {g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Ioc a b)) :
    ContinuousOn (fun t => ∫ s in a..t, g s) (Icc a b) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hg) left_mem_uIcc
  rwa [uIcc_of_le hab] at h

omit [Module 𝕜 E] in
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

theorem contDomain.admissible {A : E →ₗ.[𝕜] E} {a b : ℝ} {F : ℝ → E}
    (hF : contDomain A a b F) : ForcingClass.admissible A a b F := by
  obtain ⟨hFD, hFc, H, hHc, hH⟩ := hF
  refine ⟨hFc, Or.inr ⟨H, ?_, ?_⟩⟩
  · exact (hHc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ⟨hFD t (Ioo_subset_Icc_self ht), hH t (Ioo_subset_Icc_self ht)⟩

theorem derivOffCountable.admissible [CompleteSpace E] {A : E →ₗ.[𝕜] E} {a b : ℝ} {F : ℝ → E}
    (hF : derivOffCountable a b F) : ForcingClass.admissible A a b F := by
  obtain ⟨hFc, F', s, hs, hi, hd⟩ := hF
  exact ⟨hFc, Or.inl (w11_of_hasDerivAt hs hFc hd hi.1)⟩

theorem admissible_of_C1 [CompleteSpace E] {A : E →ₗ.[𝕜] E} {a b : ℝ} {F F' : ℝ → E}
    (hFc : ContinuousOn F (Icc a b)) (hF' : ContinuousOn F' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt F (F' t) t) : ForcingClass.admissible A a b F :=
  ⟨hFc, Or.inl (w11_of_hasDerivAt countable_empty hFc (fun t ht => hd t ht.1)
    ((hF'.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self))⟩

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

/-- `F ∈ C([0,T]; D(A))`. -/
abbrev contDomain (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  Evolution.ForcingClass.contDomain A 0 T F

/-- `F` continuous on `[0,T]` with an integrable derivative off a countable set. -/
abbrev derivOffCountable (T : ℝ) (F : ℝ → E) : Prop :=
  Evolution.ForcingClass.derivOffCountable 0 T F

/-- `F ∈ W^{1,1}(0,T; X)`. -/
abbrev w11 (T : ℝ) (F : ℝ → E) : Prop := Evolution.ForcingClass.w11 0 T F

/-- `F(t) ∈ D(A)` a.e. on `(0,T)`, with `A F` a.e. equal to an integrable function. -/
abbrev l1Domain (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  Evolution.ForcingClass.l1Domain A 0 T F

/-- The forcing class of [QuennevilleBelair2015], Thm 4.3 on `[0,T]`. -/
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

/-- The forcing class `C([0,T]; D(A))`. -/
abbrev ForcingDL (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop := ForcingClass.contDomain A T F

/-- The forcing class of continuous `F` with an integrable derivative off a countable set. -/
abbrev ForcingW11 (T : ℝ) (F : ℝ → E) : Prop := ForcingClass.derivOffCountable T F

/-- The forcing class `C([0,T]; D(A)) ∪ ForcingW11`. -/
def ForcingDLOrW11 (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop :=
  ForcingDL A T F ∨ ForcingW11 T F

/-- `F ∈ W^{1,1}(0,T; X)`. -/
abbrev IsW11 (T : ℝ) (F : ℝ → E) : Prop := ForcingClass.w11 T F

/-- `F(t) ∈ D(A)` a.e. on `(0,T)`, with `A F` a.e. equal to an integrable function. -/
abbrev IsL1D (A : E →ₗ.[ℝ] E) (T : ℝ) (F : ℝ → E) : Prop := ForcingClass.l1Domain A T F

theorem ForcingDLOrW11.admissible [CompleteSpace E] {A : E →ₗ.[ℝ] E} {T : ℝ} {F : ℝ → E}
    (hF : ForcingDLOrW11 A T F) : ForcingClass.admissible A T F :=
  hF.elim ForcingClass.contDomain.admissible ForcingClass.derivOffCountable.admissible

end Feec
