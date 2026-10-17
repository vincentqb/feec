module

public import Feec.Semigroup.Orbit
public import Feec.Evolution.Forcing
public import Feec.Evolution.Solution
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Duhamel's formula for a strongly continuous semigroup

For a strongly continuous semigroup `G` on a Banach space `E` over `𝕜 = ℝ` or `ℂ`, with
generator `A`, the **mild solution** (Duhamel's formula) of `U' = A U + F`, `U a = U₀` is
`Evolution.mild G.S a U₀ F t = S(t - a) U₀ + ∫ₐᵗ S(t - s) F(s) ds`.

## Main results

The orbit calculus of `C0Semigroup` (`extS`, joint continuity, `mapsTo_domain`,
`hasDerivWithinAt_apply`, convolutions) is in `Feec.Semigroup.Orbit`; Hille's theorem
(`LinearPMap.integral_mem_graph_of_isClosed`) is in `Feec.ForMathlib.LinearPMap.Integral`.

Duhamel's formula:

* `C0Semigroup.integral_mem_graph`: **the domain property, once**: for admissible forcing
  (`ForcingClass.admissible`), `∫ₐᵗ S(t - s) F(s) ds ∈ D(A)` with `A`-image continuous in `t`
  (`L¹(a,b; D(A))` branch: Hille; `W^{1,1}` branch: Fubini and `A ∫₀ᵘ S = S u - 1`).
* `C0Semigroup.isClassicalSolution_mild`: the mild solution is a classical solution.
* `Evolution.IsStrongSolution.eq_mild`: every strong solution with continuous forcing is the mild
  solution (`s ↦ S(t - s) U(s)` has derivative `S(t - s) F(s)`).

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.2 (Thm 2.4: generators), §4.2 (Thm 2.4, Cor 2.5: classical solutions)
* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §II.1, §VI.7
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.3 (Thm 4.3)
-/

open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec

/-! ### The domain property of Duhamel's integral -/

namespace C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

/-- **The domain property of Duhamel's integral, once**: for admissible forcing
(`F ∈ C([a,b]; E) ∩ (W^{1,1}(a,b; E) ∪ L¹(a,b; D(A)))`), `∫ₐᵗ S(t - s) F(s) ds ∈ D(A)` for
`t ∈ [a,b]`, with an `A`-image continuous on `[a,b]`. Explicitly the image is
`∫ₐᵗ S(t - s) A F(s) ds` in the `L¹(D(A))` case and `S(t - a) F(a) - F(t) + ∫ₐᵗ S(t - s) g(s) ds`
in the `W^{1,1}` case (`g` the weak derivative). Cf. [Pazy1983], Thm 4.2.4, Cor 4.2.5. -/
theorem integral_mem_graph {F : ℝ → E} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible G.generator a b F) :
    ∃ V : ℝ → E, ContinuousOn V (Icc a b) ∧
      ∀ t ∈ Icc a b, (∫ s in a..t, G.S (t - s) (F s), V t) ∈ G.generator.graph := by
  obtain ⟨hFc, hW | ⟨H, hH, hD⟩⟩ := hF
  · -- the `W^{1,1}` branch
    obtain ⟨g, hg, hpt⟩ := (Evolution.ForcingClass.w11_iff hFc).1 hW
    refine ⟨fun t => G.S (t - a) (F a) - F t + ∫ s in a..t, G.S (t - s) (g s), ?_, ?_⟩
    · have h1 : ContinuousOn (fun t => G.S (t - a) (F a)) (Icc a b) :=
        (G.strongCont (F a)).comp (continuousOn_id.sub continuousOn_const)
          fun t (ht : t ∈ Icc a b) => (sub_nonneg.2 ht.1 : (0 : ℝ) ≤ t - a)
      exact (h1.sub hFc).add (G.continuousOn_conv hg)
    intro t ht
    have hat := ht.1
    have hg' : IntegrableOn g (Ioc a t) := hg.mono_set (Ioc_subset_Ioc_right ht.2)
    have hgi : ∀ s ∈ Icc a t, IntervalIntegrable g volume a s := fun s hs =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2
        (hg'.mono_set (Ioc_subset_Ioc_right hs.2))
    -- split `F = F a + ∫ₐ^· g`
    have hsplit : ∫ s in a..t, G.S (t - s) (F s) =
        (∫ σ in (0 : ℝ)..t - a, G.S σ (F a)) +
          ∫ r in a..t, ∫ σ in (0 : ℝ)..t - r, G.S σ (g r) := by
      rw [← G.integral_S_sub_const hat, ← G.conv_primitive hat hg', ← intervalIntegral.integral_add]
      · refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le hat] at hs
        rw [hpt s ⟨hs.1, hs.2.trans ht.2⟩, _root_.map_add]
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 (G.integrableOn_S_sub hat
          ((continuousOn_const (c := F a)).integrableOn_Icc.mono_set Ioc_subset_Icc_self))
      · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2
          (G.integrableOn_S_sub hat (g := fun s => ∫ r in a..s, g r) ?_)
        exact ((Evolution.ForcingClass.continuousOn_primitive hat hg').integrableOn_Icc).mono_set
          Ioc_subset_Icc_self
    -- the two graph pairs
    have hP1 := G.integral_mem_graph_S (sub_nonneg.2 hat) (F a)
    obtain ⟨C, hC0, hC⟩ := G.exists_bound_extS (t - a)
    have hΦ : Continuous fun p : ℝ × E => ∫ σ in (0 : ℝ)..p.1, G.extS σ p.2 :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × E) (σ : ℝ) => G.extS σ p.2)
        (G.continuous_extS_uncurry.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
        continuous_fst
    have hΨi : IntegrableOn (fun r => ∫ σ in (0 : ℝ)..t - r, G.S σ (g r)) (Ioc a t) := by
      refine Integrable.mono' ((hg'.norm.const_mul (C * (t - a)))) ?_ ?_
      · have hc : Continuous fun r : ℝ => t - r := continuous_const.sub continuous_id
        refine (hΦ.comp_aestronglyMeasurable
          ((hc.aestronglyMeasurable).prodMk hg'.aestronglyMeasurable)).congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact G.integral_extS_eq (sub_nonneg.2 hr.2) (g r)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        rw [← G.integral_extS_eq (sub_nonneg.2 hr.2)]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * ‖g r‖)
          fun σ hσ => ?_).trans ?_
        · exact ((G.extS σ).le_opNorm _).trans (mul_le_mul_of_nonneg_right
            (hC σ (by rw [uIoc_of_le (sub_nonneg.2 hr.2)] at hσ; linarith [hσ.2, hr.1]))
            (norm_nonneg _))
        · rw [sub_zero, abs_of_nonneg (sub_nonneg.2 hr.2)]
          have : t - r ≤ t - a := by linarith [hr.1]
          calc C * ‖g r‖ * (t - r) ≤ C * ‖g r‖ * (t - a) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = C * (t - a) * ‖g r‖ := by ring
    have hP2 := LinearPMap.integral_mem_graph_of_isClosed G.isClosed_generator hat hΨi
      ((G.integrableOn_S_sub hat hg').sub hg') (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact G.integral_mem_graph_S (sub_nonneg.2 hr.2) (g r))
    have hgt : ∫ r in a..t, g r = F t - F a := by rw [hpt t ht]; abel
    rw [hsplit]
    convert G.generator.graph.add_mem hP1 hP2 using 1
    refine Prod.ext rfl ?_
    simp only [Prod.snd_add, Pi.sub_apply]
    rw [intervalIntegral.integral_sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 (G.integrableOn_S_sub hat hg'))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 hg'), hgt]
    abel
  · -- the `L¹(a,b; D(A))` branch
    refine ⟨fun t => ∫ s in a..t, G.S (t - s) (H s), G.continuousOn_conv hH, fun t ht => ?_⟩
    have hae : ∀ᵐ s ∂(volume.restrict (Ioc a t)), (F s, H s) ∈ G.generator.graph := by
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))] at hD
      refine ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) ?_
      filter_upwards [hD] with s ⟨hs, e⟩
      exact LinearPMap.mem_graph_iff_exists.2 ⟨hs, e⟩
    exact G.conv_mem_graph ht.1 ((hFc.integrableOn_Icc).mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))) (hH.mono_set
      (Ioc_subset_Ioc_right ht.2)) hae

end C0Semigroup

/-! ### Mild solutions -/

namespace Evolution

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]

/-- **Duhamel's formula**: the mild solution of `U' = A U + F`, `U a = U₀`, for the propagator
`S`: `mild S a U₀ F t = S(t - a) U₀ + ∫ₐᵗ S(t - s) F(s) ds`. -/
def mild (S : ℝ → E →L[𝕜] E) (a : ℝ) (U₀ : E) (F : ℝ → E) (t : ℝ) : E :=
  S (t - a) U₀ + ∫ s in a..t, S (t - s) (F s)

theorem mild_self {S : ℝ → E →L[𝕜] E} (hS : S 0 = 1) (a : ℝ) (U₀ : E) (F : ℝ → E) :
    mild S a U₀ F a = U₀ := by
  simp [mild, hS]

end Evolution

namespace C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
@[simp] theorem mild_self (a : ℝ) (U₀ : E) (F : ℝ → E) : Evolution.mild G.S a U₀ F a = U₀ :=
  Evolution.mild_self G.map_zero a U₀ F

/-- `A ∫ₐᵗ v = v t - ∫ₐᵗ F` for the Duhamel term `v t = ∫ₐᵗ S(t - s) F(s) ds`. -/
theorem integral_conv_mem_graph {F : ℝ → E} {a t : ℝ} (hat : a ≤ t)
    (hF : IntegrableOn F (Ioc a t)) :
    (∫ s in a..t, ∫ r in a..s, G.S (s - r) (F r),
      (∫ r in a..t, G.S (t - r) (F r)) - ∫ r in a..t, F r) ∈ G.generator.graph := by
  obtain ⟨C, hC0, hC⟩ := G.exists_bound_extS (t - a)
  have h1 : ∫ s in a..t, ∫ r in a..s, G.S (s - r) (F r) =
      ∫ s in a..t, ∫ r in a..s, G.extS (s - r) (F r) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hat] at hs
    exact G.integral_S_sub_eq_extS hs.1
  have h2 := integral_integral_triangle_swap (k := fun s r => G.extS (s - r) (F r))
    (g := fun r => C * ‖F r‖) hat
    (G.continuous_extS_uncurry.comp_aestronglyMeasurable
      (((continuous_fst.sub continuous_snd).aestronglyMeasurable).prodMk
        hF.aestronglyMeasurable.comp_snd))
    (hF.norm.const_mul C) fun s hs r hr =>
      ((G.extS _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC _ (by linarith [hs.2, hr.1]))
        (norm_nonneg _))
  have h3 : ∫ r in a..t, ∫ s in r..t, G.extS (s - r) (F r) =
      ∫ r in a..t, ∫ σ in (0 : ℝ)..t - r, G.S σ (F r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hat] at hr
    rw [intervalIntegral.integral_comp_sub_right (fun σ => G.extS σ (F r)) r, sub_self,
      G.integral_extS_eq (sub_nonneg.2 hr.2)]
  rw [h1, h2, h3]
  obtain ⟨C', hC'0, hC'⟩ := G.exists_bound_extS (t - a)
  have hΦ : Continuous fun p : ℝ × E => ∫ σ in (0 : ℝ)..p.1, G.extS σ p.2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × E) (σ : ℝ) => G.extS σ p.2)
      (G.continuous_extS_uncurry.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
      continuous_fst
  have hΨi : IntegrableOn (fun r => ∫ σ in (0 : ℝ)..t - r, G.S σ (F r)) (Ioc a t) := by
    refine Integrable.mono' ((hF.norm.const_mul (C' * (t - a)))) ?_ ?_
    · have hc : Continuous fun r : ℝ => t - r := continuous_const.sub continuous_id
      refine (hΦ.comp_aestronglyMeasurable
        ((hc.aestronglyMeasurable).prodMk hF.aestronglyMeasurable)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact G.integral_extS_eq (sub_nonneg.2 hr.2) (F r)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [← G.integral_extS_eq (sub_nonneg.2 hr.2)]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C' * ‖F r‖)
        fun σ hσ => ?_).trans ?_
      · exact ((G.extS σ).le_opNorm _).trans (mul_le_mul_of_nonneg_right
          (hC' σ (by rw [uIoc_of_le (sub_nonneg.2 hr.2)] at hσ; linarith [hσ.2, hr.1]))
          (norm_nonneg _))
      · rw [sub_zero, abs_of_nonneg (sub_nonneg.2 hr.2)]
        have : t - r ≤ t - a := by linarith [hr.1]
        calc C' * ‖F r‖ * (t - r) ≤ C' * ‖F r‖ * (t - a) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = C' * (t - a) * ‖F r‖ := by ring
  have := LinearPMap.integral_mem_graph_of_isClosed G.isClosed_generator hat hΨi
    ((G.integrableOn_S_sub hat hF).sub hF) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact G.integral_mem_graph_S (sub_nonneg.2 hr.2) (F r))
  convert this using 2
  simp only [Pi.sub_apply]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 (G.integrableOn_S_sub hat hF))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 hF)]

/-- **Duhamel's formula gives a classical solution**: for `U₀ ∈ D(A)` and admissible forcing
`F ∈ C([a,b]; E) ∩ (W^{1,1}(a,b; E) ∪ L¹(a,b; D(A)))`, the mild solution
`t ↦ S(t - a) U₀ + ∫ₐᵗ S(t - s) F(s) ds` is a classical solution of `U' = A U + F` on `[a,b]`.
[QuennevilleBelair2015], Thm 4.3 (existence). Cf. [Pazy1983], Thm 4.2.4, Cor 4.2.5. -/
theorem isClassicalSolution_mild {U₀ : E} (hU₀ : U₀ ∈ G.generator.domain) {F : ℝ → E} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible G.generator a b F) :
    Evolution.IsClassicalSolution G.generator (Icc a b) F (Evolution.mild G.S a U₀ F) := by
  obtain ⟨V, hVc, hV⟩ := G.integral_mem_graph hF
  have hFc := hF.1
  set v : ℝ → E := fun t => ∫ s in a..t, G.S (t - s) (F s) with hv
  -- `v t = ∫ₐᵗ (V + F)` on `[a,b]`
  have key : ∀ t ∈ Icc a b, v t = ∫ s in a..t, (V s + F s) := by
    intro t ht
    have hFt : IntegrableOn F (Ioc a t) := (hFc.integrableOn_Icc).mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
    have hvc : ContinuousOn v (Icc a t) :=
      (G.continuousOn_conv (g := F) hFt)
    have hVt : ContinuousOn V (Icc a t) := hVc.mono (Icc_subset_Icc_right ht.2)
    have hA := G.integral_conv_mem_graph ht.1 hFt
    have hB := LinearPMap.integral_mem_graph_of_isClosed G.isClosed_generator ht.1
      (f := v) (H := V) (hvc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hVt.integrableOn_Icc.mono_set Ioc_subset_Icc_self) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hV s ⟨hs.1.le, hs.2.trans ht.2⟩)
    have e := LinearPMap.mem_graph_snd_inj G.generator hA hB rfl
    rw [intervalIntegral.integral_add
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2 hVt.integrableOn_Icc)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
        ((hFc.mono (Icc_subset_Icc_right ht.2)).integrableOn_Icc)), ← e]
    simp [hv]
  have hvd : ∀ t ∈ Icc a b, HasDerivWithinAt v (V t + F t) (Icc a b) t := fun t ht =>
    (hasDerivWithinAt_integral_of_continuousOn (hVc.add hFc) ht).congr_of_mem key ht
  -- the homogeneous part
  have hh : ∀ t ∈ Icc a b, HasDerivWithinAt (fun τ => G.S (τ - a) U₀)
      (G.S (t - a) (G.generator ⟨U₀, hU₀⟩)) (Icc a b) t := by
    intro t ht
    have h1 := G.hasDerivWithinAt_apply ⟨U₀, hU₀⟩ (sub_nonneg.2 ht.1)
    have h2 : HasDerivWithinAt (fun τ : ℝ => τ - a) 1 (Icc a b) t :=
      ((hasDerivAt_id t).sub_const a).hasDerivWithinAt
    have := HasDerivWithinAt.scomp (h := fun τ : ℝ => τ - a) t h1 h2
      fun τ (hτ : τ ∈ Icc a b) => (sub_nonneg.2 hτ.1 : (0 : ℝ) ≤ τ - a)
    rwa [one_smul] at this
  have hhc : ContinuousOn (fun t => G.S (t - a) (G.generator ⟨U₀, hU₀⟩)) (Icc a b) :=
    (G.strongCont _).comp (continuousOn_id.sub continuousOn_const)
      fun t (ht : t ∈ Icc a b) => (sub_nonneg.2 ht.1 : (0 : ℝ) ≤ t - a)
  have hgraph : ∀ t ∈ Icc a b, (Evolution.mild G.S a U₀ F t,
      G.S (t - a) (G.generator ⟨U₀, hU₀⟩) + V t) ∈ G.generator.graph := fun t ht => by
    convert G.generator.graph.add_mem (G.S_mem_graph (G.generator.mem_graph ⟨U₀, hU₀⟩)
      (sub_nonneg.2 ht.1)) (hV t ht) using 1
    simp only [Evolution.mild, Prod.mk_add_mk]
  refine ⟨Evolution.IsStrongSolution.of_deriv fun t ht => ⟨_, hgraph t ht, ?_⟩,
    _, hhc.add hVc, hgraph⟩
  have := (hh t ht).add (hvd t ht)
  rw [← add_assoc] at this
  exact this.congr_of_mem (fun τ _ => rfl) ht

/-- **Every strong solution is the mild solution**: if `U` is a strong solution of
`U' = A U + F` on `[a,b]` with `F` continuous, then `U t = S(t - a) U(a) + ∫ₐᵗ S(t - s) F(s) ds`
on `[a,b]`. Proof: `s ↦ S(t - s) U(s)` has derivative `S(t - s) F(s)` on `(a,t)`.
Cf. [Pazy1983], Thm 4.1.3. -/
theorem _root_.Feec.Evolution.IsStrongSolution.eq_mild {G : C0Semigroup 𝕜 E} {F U : ℝ → E}
    {a b : ℝ} (hU : Evolution.IsStrongSolution G.generator (Icc a b) F U)
    (hF : ContinuousOn F (Icc a b)) : ∀ t ∈ Icc a b, U t = Evolution.mild G.S a (U a) F t := by
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  set φ : ℝ → E := fun s => G.extS (t - s) (U s)
  have hφc : ContinuousOn φ (Icc a t) :=
    G.continuous_extS_uncurry.comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk (hU.continuousOn.mono hsub))
  have hφd : ∀ s ∈ Ioo a t, HasDerivWithinAt φ (G.extS (t - s) (F s)) (Ioi s) s := by
    intro s hs
    have hs' : s ∈ Ico a b := ⟨hs.1.le, hs.2.trans_le ht.2⟩
    have hy := (hU.hasDerivWithinAt_Ici hs').mono Ioi_subset_Ici_self
    have hφ' : HasDerivWithinAt (fun σ : ℝ => t - σ) (-1) (Ioi s) s :=
      ((hasDerivAt_id s).const_sub t).hasDerivWithinAt
    have hD := G.hasDerivAt_extS_apply ⟨U s, hU.mem_domain (Ico_subset_Icc_self hs')⟩
      (sub_pos.2 hs.2)
    have := G.hasDerivWithinAt_extS_comp hy hφ' hD
    refine this.congr_deriv ?_
    rw [G.extS_of_nonneg (sub_pos.2 hs.2).le, _root_.map_add, neg_one_smul]
    abel
  have hint : IntervalIntegrable (fun s => G.extS (t - s) (F s)) volume a t :=
    G.intervalIntegrable_extS_comp (T := t - a) (φ := fun s => t - s)
      ((hF.mono hsub).intervalIntegrable_of_Icc ht.1) (continuous_const.sub continuous_id)
      fun s hs => by rw [uIcc_of_le ht.1] at hs; linarith [hs.1]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hφc hφd hint
  simp only [φ, sub_self, G.extS_of_nonneg le_rfl, S_zero_apply,
    G.extS_of_nonneg (sub_nonneg.2 ht.1)] at hftc
  rw [Evolution.mild, G.integral_S_sub_eq_extS ht.1, hftc]
  abel

end C0Semigroup

end Feec
