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

This is the integration-by-parts step behind the `W^{1,1}` branch of the forcing class of
[QuennevilleBelair2015, Thm 4.3]. The classical solutions themselves, for the whole class
`ForcingClass.admissible` (`Feec.Evolution.Forcing`), are constructed in `Feec.Ch4.StoneForcing`
(`UnitaryGroupGenerator.wellPosedClassical_admissible`); the former statements for
`ForcingW11` and `ForcingThm43` (`UnitaryGroupGenerator.wellPosedClassical_W11`,
`UnitaryGroupGenerator.wellPosedClassical_thm43`) are corollaries there.

## Main results

* `UnitaryGroupGenerator.intervalIntegrable_apply`: `s ↦ S(φ s) (g s)` is interval integrable.
* `UnitaryGroupGenerator.integral_mem_domain_of_hasDerivAt`: the integration-by-parts identity.

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

end Feec
