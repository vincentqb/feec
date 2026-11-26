module

public import Feec.ForMathlib.LinearPMap.Skew
public import Feec.ForMathlib.LinearPMap.Integral
public import Feec.ForMathlib.Analysis.Gronwall

/-!
# Strong and classical solutions of `U' = A U + F`

Strong and classical solutions of `U' = A U + F` on a time set `I ⊆ ℝ`; for a dissipative `A`,
strong solutions are stable in the initial value, hence unique.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Evolution

section General

variable {𝕜 E : Type*} [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [NormedSpace ℝ E]

/-- `U` is a **strong solution** of `U' = A U + F` on `I`: continuous, with `U t ∈ D(A)` and
`U' t = A (U t) + F t` within `I`. [QuennevilleBelair2015], §4.4; [Pazy1983], §4.1 -/
structure IsStrongSolution (A : E →ₗ.[𝕜] E) (I : Set ℝ) (F U : ℝ → E) : Prop where
  continuousOn : ContinuousOn U I
  deriv : ∀ t ∈ I, ∃ v, (U t, v) ∈ A.graph ∧ HasDerivWithinAt U (v + F t) I t

/-- `U` is a **classical solution** of `U' = A U + F` on `I`: a strong solution such that
`t ↦ A (U t)` is continuous on `I`. [QuennevilleBelair2015], Thm 4.3; [Pazy1983], §4.1 -/
structure IsClassicalSolution (A : E →ₗ.[𝕜] E) (I : Set ℝ) (F U : ℝ → E) : Prop
    extends IsStrongSolution A I F U where
  deriv_cont : ∃ V : ℝ → E, ContinuousOn V I ∧ ∀ t ∈ I, (U t, V t) ∈ A.graph

variable {A : E →ₗ.[𝕜] E} {I J : Set ℝ} {F G U V : ℝ → E}

namespace IsStrongSolution

theorem of_deriv (h : ∀ t ∈ I, ∃ v, (U t, v) ∈ A.graph ∧ HasDerivWithinAt U (v + F t) I t) :
    IsStrongSolution A I F U :=
  ⟨fun t ht => (h t ht).choose_spec.2.continuousWithinAt, h⟩

theorem mem_domain (hU : IsStrongSolution A I F U) {t : ℝ} (ht : t ∈ I) : U t ∈ A.domain :=
  LinearPMap.mem_domain_of_mem_graph (hU.deriv t ht).choose_spec.1

theorem hasDerivWithinAt (hU : IsStrongSolution A I F U) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt U (A ⟨U t, hU.mem_domain ht⟩ + F t) I t := by
  obtain ⟨v, hv, hd⟩ := hU.deriv t ht
  obtain ⟨_, e⟩ := LinearPMap.mem_graph_iff_exists.1 hv
  rwa [e]

theorem iff : IsStrongSolution A I F U ↔ ∃ h : ∀ t ∈ I, U t ∈ A.domain,
    ∀ t (ht : t ∈ I), HasDerivWithinAt U (A ⟨U t, h t ht⟩ + F t) I t :=
  ⟨fun hU => ⟨fun _ => hU.mem_domain, fun _ => hU.hasDerivWithinAt⟩, fun ⟨h, hd⟩ =>
    of_deriv fun t ht => ⟨_, A.mem_graph ⟨U t, h t ht⟩, hd t ht⟩⟩

theorem of_hasDerivWithinAt (h : ∀ t ∈ I, U t ∈ A.domain)
    (hd : ∀ t (ht : t ∈ I), HasDerivWithinAt U (A ⟨U t, h t ht⟩ + F t) I t) :
    IsStrongSolution A I F U :=
  iff.2 ⟨h, hd⟩

theorem mono (hU : IsStrongSolution A I F U) (hJ : J ⊆ I) : IsStrongSolution A J F U :=
  of_deriv fun t ht =>
    let ⟨v, hv, hd⟩ := hU.deriv t (hJ ht)
    ⟨v, hv, hd.mono hJ⟩

theorem congr (hU : IsStrongSolution A I F U) (hUV : EqOn U V I) (hFG : EqOn F G I) :
    IsStrongSolution A I G V :=
  of_deriv fun t ht =>
    let ⟨v, hv, hd⟩ := hU.deriv t ht
    ⟨v, hUV ht ▸ hv, by rw [← hFG ht]; exact hd.congr_of_mem (fun s hs => (hUV hs).symm) ht⟩

theorem add (hU : IsStrongSolution A I F U) (hV : IsStrongSolution A I G V) :
    IsStrongSolution A I (F + G) (U + V) :=
  of_deriv fun t ht =>
    let ⟨v, hv, hd⟩ := hU.deriv t ht
    let ⟨w, hw, he⟩ := hV.deriv t ht
    ⟨v + w, A.graph.add_mem hv hw, by
      convert hd.add he using 1; simp only [Pi.add_apply]; abel⟩

theorem neg (hU : IsStrongSolution A I F U) : IsStrongSolution A I (-F) (-U) :=
  of_deriv fun t ht =>
    let ⟨v, hv, hd⟩ := hU.deriv t ht
    ⟨-v, A.graph.neg_mem hv, by
      have := hd.neg
      simpa only [Pi.neg_apply, neg_add] using this⟩

theorem sub (hU : IsStrongSolution A I F U) (hV : IsStrongSolution A I G V) :
    IsStrongSolution A I (F - G) (U - V) := by
  simpa only [sub_eq_add_neg] using hU.add hV.neg

theorem zero : IsStrongSolution A I 0 (0 : ℝ → E) :=
  of_deriv fun _ _ => ⟨0, A.graph.zero_mem, by
    rw [Pi.zero_apply, add_zero]; exact hasDerivWithinAt_const _ _ (0 : E)⟩

theorem hasDerivWithinAt_Ici {a b : ℝ} (hU : IsStrongSolution A (Icc a b) F U) {t : ℝ}
    (ht : t ∈ Ico a b) :
    HasDerivWithinAt U (A ⟨U t, hU.mem_domain (Ico_subset_Icc_self ht)⟩ + F t) (Ici t) t :=
  (hU.hasDerivWithinAt (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)

end IsStrongSolution

namespace IsClassicalSolution

theorem iff : IsClassicalSolution A I F U ↔ ∃ h : ∀ t ∈ I, U t ∈ A.domain,
    (∀ t (ht : t ∈ I), HasDerivWithinAt U (A ⟨U t, h t ht⟩ + F t) I t) ∧
    ∃ V : ℝ → E, ContinuousOn V I ∧ ∀ t (ht : t ∈ I), A ⟨U t, h t ht⟩ = V t := by
  constructor
  · rintro ⟨hU, V, hV, hUV⟩
    exact ⟨fun _ => hU.mem_domain, fun _ => hU.hasDerivWithinAt, V, hV, fun t ht =>
      ((LinearPMap.image_iff (hU.mem_domain ht)).2 (hUV t ht)).symm⟩
  · rintro ⟨h, hd, V, hV, hUV⟩
    exact ⟨IsStrongSolution.of_hasDerivWithinAt h hd, V, hV, fun t ht =>
      hUV t ht ▸ A.mem_graph ⟨U t, h t ht⟩⟩

theorem mono (hU : IsClassicalSolution A I F U) (hJ : J ⊆ I) : IsClassicalSolution A J F U :=
  let ⟨V, hV, hUV⟩ := hU.deriv_cont
  ⟨hU.toIsStrongSolution.mono hJ, V, hV.mono hJ, fun t ht => hUV t (hJ ht)⟩

theorem congr (hU : IsClassicalSolution A I F U) (hUV : EqOn U V I) (hFG : EqOn F G I) :
    IsClassicalSolution A I G V :=
  let ⟨W, hW, hUW⟩ := hU.deriv_cont
  ⟨hU.toIsStrongSolution.congr hUV hFG, W, hW, fun t ht => hUV ht ▸ hUW t ht⟩

theorem continuousOn_deriv (hU : IsClassicalSolution A I F U) (hF : ContinuousOn F I) :
    ∃ U' : ℝ → E, ContinuousOn U' I ∧ ∀ t ∈ I, HasDerivWithinAt U (U' t) I t := by
  obtain ⟨V, hV, hUV⟩ := hU.deriv_cont
  refine ⟨V + F, hV.add hF, fun t ht => ?_⟩
  have h := hU.hasDerivWithinAt ht
  rwa [((LinearPMap.image_iff (hU.mem_domain ht)).2 (hUV t ht)).symm] at h

end IsClassicalSolution

end General

section Smul

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E} {I : Set ℝ} {F U : ℝ → E}

namespace IsStrongSolution

theorem smul (hU : IsStrongSolution A I F U) (c : 𝕜) :
    IsStrongSolution A I (c • F) (c • U) :=
  of_deriv fun t ht =>
    let ⟨v, hv, hd⟩ := hU.deriv t ht
    ⟨c • v, A.graph.smul_mem c hv, by
      have := hd.const_smul c
      simpa only [Pi.smul_apply, smul_add] using this⟩

end IsStrongSolution

end Smul

section Dissipative

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] {A : E →ₗ.[𝕜] E} {I : Set ℝ} {F U V : ℝ → E}

namespace IsStrongSolution

theorem norm_sub_le (hA : A.IsDissipative) {a b : ℝ} (hU : IsStrongSolution A (Icc a b) F U)
    (hV : IsStrongSolution A (Icc a b) F V) : ∀ t ∈ Icc a b, ‖U t - V t‖ ≤ ‖U a - V a‖ := by
  have hW := hU.sub hV
  simp only [sub_self] at hW
  intro t ht
  have := norm_le_add_integral_of_re_inner_deriv_le (𝕜 := 𝕜) (g := fun _ => 0)
    (e := U - V) (e' := fun s => if h : s ∈ Icc a b then A ⟨(U - V) s, hW.mem_domain h⟩ else 0)
    hW.continuousOn (fun s hs => by
      rw [dite_eq_left (Ico_subset_Icc_self hs)]
      simpa using hW.hasDerivWithinAt_Ici hs) continuousOn_const (fun _ _ => le_rfl)
    (fun s hs => by
      rw [dite_eq_left (Ico_subset_Icc_self hs), zero_mul]
      exact hA _) t ht
  simpa using this

/-- **Uniqueness for a dissipative generator**: strong solutions of `U' = A U + F` on `[a,b]`
with the same value at `a` agree on `[a,b]`. [QuennevilleBelair2015], Thm 4.3, Thm 4.6 (adapted) -/
theorem unique (hA : A.IsDissipative) {a b : ℝ} (hU : IsStrongSolution A (Icc a b) F U)
    (hV : IsStrongSolution A (Icc a b) F V) (h0 : U a = V a) : EqOn U V (Icc a b) := fun t ht => by
  have := hU.norm_sub_le hA hV t ht
  rwa [h0, sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at this

end IsStrongSolution

namespace IsClassicalSolution

theorem unique (hA : A.IsDissipative) {a b : ℝ} (hU : IsClassicalSolution A (Icc a b) F U)
    (hV : IsClassicalSolution A (Icc a b) F V) (h0 : U a = V a) : EqOn U V (Icc a b) :=
  hU.toIsStrongSolution.unique hA hV.toIsStrongSolution h0

end IsClassicalSolution

end Dissipative

end Feec.Evolution
