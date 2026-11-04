module

public import Feec.FiniteElement.SmoothedInterp
public import Feec.HilbertComplex.Approximation.GraphApprox

/-!
# Density of smooth forms on domains star-shaped with respect to a ball

On a bounded open `Ω ⊆ ℝⁿ` star-shaped with respect to a ball `B(x₀, s)`, the smoothed forms
`smoothForm` of `Feec.FiniteElement.SmoothedInterp` ([AFW2010], §5.5), with dilation factor
`c → 1` and bump radius `→ 0`, are `C^∞` (`contDiff_smoothForm`), equal to the field smoothers
`R_{cᵏ} u` in `L²(Ω; Λᵏ)` (`formL2_smoothForm`), which converge strongly
(`Feec.Domain.exists_norm_smoothField_sub_lt`), and commute with `d`. Hence:

* **smooth forms are dense in the graph norm** of the maximal `d` (`exists_smooth_near_of_starBall`,
  dilation away from `x₀`) and of the minimal `d`, by smooth forms vanishing outside `Ω`
  (`exists_smooth_near_min_of_starBall`, dilation towards `x₀`);
* **graph-norm density of a family of subcomplexes** `S_N` of `HΛ(Ω)`, resp. `H̊Λ(Ω)`, follows
  from the approximation of smooth forms with rates `b_N → 0`
  (`eventually_exists_graph_of_smooth`, `eventually_exists_graph_of_smooth_min`, through
  `Feec.HilbertComplex.Subcomplex.eventually_exists_graph_of_near`).

They are used for the Freudenthal meshes of the cube (`Feec.Models.Cube.WhitneyApprox`) and for the
mesh families of star-shaped domains (`Feec.Models.StarShaped.FiniteElement`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothing by dilation and mollification)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (density of the finite
  element spaces)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh Feec.HilbertComplex Feec.ExteriorFibre

variable {n : ℕ}

theorem exists_abs_pow_sub_one_lt (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ c : ℝ, |c - 1| < δ → |c ^ k - 1| < η := by
  have h := Metric.continuousAt_iff.1 ((continuous_pow k).continuousAt (x := (1 : ℝ))) η hη
  simpa [Real.dist_eq] using h

/-- The smoothed form is `C^∞`. -/
theorem contDiff_smoothForm {Ω : Set (Fin n → ℝ)} (p : SmoothingParam (Fin n → ℝ))
    (hΩ : MeasurableSet Ω) (k : ℤ) (u : L2F ℝ Ω (formIdx n k)) :
    ContDiff ℝ ∞ (smoothForm p hΩ k u : FormField n) :=
  contDiff_pi.2 fun t => contDiff_formExt (contDiff_smoothCoeff p hΩ k u) t

/-- **The smoothed form is the field smoother** `R_{cᵏ} u` in `L²(Ω; Λᵏ)`. -/
theorem formL2_smoothForm {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (p : SmoothingParam (Fin n → ℝ)) (k : ℤ)
    (u : L2F ℝ Ω (formIdx n k)) :
    formL2 hΩ hb k (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k u)) =
      smoothField p hΩ (fun _ => p.factor ^ k) u := by
  refine PiLp.ext fun s => Lp.ext ?_
  filter_upwards [coeFn_formL2 hΩ hb k (Submodule.inclusion c1Forms_le_contForms
      (smoothForm p hΩ k u)) s, Lp.coeFn_smul (p.factor ^ k) (smoothL2 p hΩ (u s)),
    coeFn_smoothL2 (p := p) hΩ (u s)] with x h1 h2 h3
  rw [h1, smoothField_apply, h2, Pi.smul_apply, h3]
  change (smoothForm p hΩ k u : FormField n) x s.1 = _
  rw [smoothForm_apply, formExt_val]
  rfl

/-- **Smooth forms are dense in the graph norm of the maximal `d`** on every bounded open `Ω`
star-shaped with respect to a ball `B(x₀, s)` (the smoother with dilation away from `x₀`). -/
theorem exists_smooth_near_of_starBall {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {x₀ : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (k : ℕ)
    (u' : ((extDerivOp ℝ n k).maximal Ω).domain) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ w : FormField n, ∃ hw : ContDiff ℝ ∞ w, (∀ x, IsDeg k (w x)) ∧
      ‖(u' : L2F ℝ Ω (formIdx n k)) -
          formL2 hΩ.measurableSet hb k
            ⟨w, hw.continuous⟩‖ < ε ∧
      ‖(extDerivOp ℝ n k).maximal Ω u' -
          formL2 hΩ.measurableSet hb ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩‖ < ε := by
  obtain ⟨η₁, hη₁, hP₁⟩ := exists_norm_smoothField_sub_lt hΩ.measurableSet x₀
    (u' : L2F ℝ Ω (formIdx n k)) hε
  obtain ⟨η₂, hη₂, hP₂⟩ := exists_norm_smoothField_sub_lt hΩ.measurableSet x₀
    ((extDerivOp ℝ n k).maximal Ω u') hε
  obtain ⟨δ₁, hδ₁, hc₁⟩ := exists_abs_pow_sub_one_lt k hη₁
  obtain ⟨δ₂, hδ₂, hc₂⟩ := exists_abs_pow_sub_one_lt (k + 1) hη₂
  obtain ⟨p, hp, hc, hr⟩ := SmoothingParam.exists_isMaximal x₀ hs
    (η := min (min η₁ η₂) (min δ₁ δ₂)) (by positivity)
  have hcη₁ : |p.factor - 1| < η₁ := hc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hcη₂ : |p.factor - 1| < η₂ := hc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hcδ₁ : |p.factor - 1| < δ₁ := hc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcδ₂ : |p.factor - 1| < δ₂ := hc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrη₁ : p.bump.rOut < η₁ := hr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hrη₂ : p.bump.rOut < η₂ := hr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  set w : FormField n := (smoothForm p hΩ.measurableSet k (u' : L2F ℝ Ω (formIdx n k)) :
    FormField n)
  have hw : ContDiff ℝ ∞ w := contDiff_smoothForm p hΩ.measurableSet k _
  refine ⟨w, hw, isDeg_smoothForm p hΩ.measurableSet k _, ?_, ?_⟩
  · have e := formL2_smoothForm hΩ.measurableSet hb p (k : ℤ)
      (u' : L2F ℝ Ω (formIdx n k))
    change ‖(u' : L2F ℝ Ω (formIdx n k)) - formL2 hΩ.measurableSet hb k
      (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ.measurableSet k
        (u' : L2F ℝ Ω (formIdx n k))))‖ < ε
    rw [e, norm_sub_rev]
    refine hP₁ p hp.center_eq hcη₁ hrη₁ _ ?_
    rw [zpow_natCast]; exact hc₁ _ hcδ₁
  · have e1 : formL2 hΩ.measurableSet hb ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ =
        formL2 hΩ.measurableSet hb ((k : ℤ) + 1)
          (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ.measurableSet ((k : ℤ) + 1)
            ((extDerivOp ℝ n k).maximal Ω u'))) :=
      formL2_congr _ _ _ fun x hx =>
        extDeriv_smoothForm_of_maximal p hΩ.measurableSet hΩ hstar hp k u'
          (subset_closure hx)
    rw [e1, formL2_smoothForm, norm_sub_rev]
    refine hP₂ p hp.center_eq hcη₂ hrη₂ _ ?_
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact hc₂ _ hcδ₂

/-- **Smooth `k`-forms vanishing outside `Ω` are dense in the graph norm of the minimal `d`** on
every bounded open `Ω` star-shaped with respect to a ball (dilation towards the centre). -/
theorem exists_smooth_near_min_of_starBall {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {x₀ : Fin n → ℝ} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) (k : ℕ)
    (u' : ((extDerivOp ℝ n k).minimal Ω).domain) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ w : FormField n, ∃ hw : ContDiff ℝ ∞ w, (∀ x, IsDeg k (w x)) ∧ (∀ x ∉ Ω, w x = 0) ∧
      ‖(u' : L2F ℝ Ω (formIdx n k)) -
          formL2 hΩ.measurableSet hb k
            ⟨w, hw.continuous⟩‖ < ε ∧
      ‖(extDerivOp ℝ n k).minimal Ω u' -
          formL2 hΩ.measurableSet hb ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩‖ < ε := by
  obtain ⟨η₁, hη₁, hP₁⟩ := exists_norm_smoothField_sub_lt hΩ.measurableSet x₀
    (u' : L2F ℝ Ω (formIdx n k)) hε
  obtain ⟨η₂, hη₂, hP₂⟩ := exists_norm_smoothField_sub_lt hΩ.measurableSet x₀
    ((extDerivOp ℝ n k).minimal Ω u') hε
  obtain ⟨δ₁, hδ₁, hc₁⟩ := exists_abs_pow_sub_one_lt k hη₁
  obtain ⟨δ₂, hδ₂, hc₂⟩ := exists_abs_pow_sub_one_lt (k + 1) hη₂
  obtain ⟨p, hp, hc, hr⟩ := SmoothingParam.exists_isMinimal x₀ hs
    (η := min (min η₁ η₂) (min δ₁ δ₂)) (by positivity)
  have hcη₁ : |p.factor - 1| < η₁ := hc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hcη₂ : |p.factor - 1| < η₂ := hc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hcδ₁ : |p.factor - 1| < δ₁ := hc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcδ₂ : |p.factor - 1| < δ₂ := hc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrη₁ : p.bump.rOut < η₁ := hr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hrη₂ : p.bump.rOut < η₂ := hr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  set w : FormField n := (smoothForm p hΩ.measurableSet k (u' : L2F ℝ Ω (formIdx n k)) :
    FormField n)
  have hw : ContDiff ℝ ∞ w := contDiff_smoothForm p hΩ.measurableSet k _
  refine ⟨w, hw, isDeg_smoothForm p hΩ.measurableSet k _,
    fun x hx => smoothForm_eq_zero_of_minimal p hΩ hb hstar hp k _ hx, ?_, ?_⟩
  · have e := formL2_smoothForm hΩ.measurableSet hb p (k : ℤ)
      (u' : L2F ℝ Ω (formIdx n k))
    change ‖(u' : L2F ℝ Ω (formIdx n k)) - formL2 hΩ.measurableSet hb k
      (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ.measurableSet k
        (u' : L2F ℝ Ω (formIdx n k))))‖ < ε
    rw [e, norm_sub_rev]
    refine hP₁ p hp.center_eq hcη₁ hrη₁ _ ?_
    rw [zpow_natCast]; exact hc₁ _ hcδ₁
  · have e1 : formL2 hΩ.measurableSet hb ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ =
        formL2 hΩ.measurableSet hb ((k : ℤ) + 1)
          (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ.measurableSet ((k : ℤ) + 1)
            ((extDerivOp ℝ n k).minimal Ω u'))) :=
      formL2_congr _ _ _ fun x _ =>
        extDeriv_smoothForm_of_minimal p hΩ.measurableSet hΩ k u' x
    rw [e1, formL2_smoothForm, norm_sub_rev]
    refine hP₂ p hp.center_eq hcη₂ hrη₂ _ ?_
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact hc₂ _ hcδ₂

/-! ### Graph-norm density of subcomplex families from the approximation of smooth forms -/

section OfSmooth

variable {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : Fin n → ℝ}
  {s : ℝ} (hs : 0 < s) (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω)
include hs hstar

/-- **Graph-norm density in `HΛ(Ω)` from the approximation of smooth forms**, on a bounded open
`Ω` star-shaped with respect to a ball: if every `C^∞` `k`-form `w` is approximated by some
`v ∈ Vₕᵏ` with `‖w - v‖ ≤ b_N` and `‖dw - dv‖ ≤ b_N`, `b_N → 0`, then every `x ∈ D(d)` is a
graph-norm limit of the `Vₕᵏ` (smooth forms are dense, `exists_smooth_near_of_starBall`). -/
theorem eventually_exists_graph_of_smooth (S : ℕ → (maximalDeRham hΩ).Subcomplex)
    (happ : ∀ (k : ℕ) (w : FormField n) (hw : ContDiff ℝ ∞ w), (∀ x, IsDeg k (w x)) →
      ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ ∀ N, ∃ v ∈ (S N).V k,
        ‖formL2 hΩ.measurableSet hb k ⟨w, hw.continuous⟩ - v‖ ≤ b N ∧
        ∃ hv : v ∈ ((maximalDeRham hΩ).d k (k + 1)).domain,
          ‖formL2 hΩ.measurableSet hb ((k : ℤ) + 1)
              ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ -
            (maximalDeRham hΩ).d k (k + 1) ⟨v, hv⟩‖ ≤ b N)
    (k : ℤ) (x : L2F ℝ Ω (formIdx n k))
    (hx : x ∈ ((maximalDeRham hΩ).d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (S N).V k, ‖x - v‖ < ε ∧
      ‖(maximalDeRham hΩ).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  rcases k with k | k
  swap
  · have := LocalElement.subsingleton_L2F_negSucc Ω (n := n) k
    refine Eventually.of_forall fun N => ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε
  refine Subcomplex.eventually_exists_graph_of_near S hx (fun ε hε => ?_) hε
  have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) hΩ (k : ℤ)
  obtain ⟨w, hw, hdeg, h1, h2⟩ := exists_smooth_near_of_starBall hΩ hb hs hstar k
    ⟨x, hd ▸ hx⟩ hε
  have hu : (maximalDeRham hΩ).d k (k + 1) ⟨x, hx⟩ =
      (extDerivOp ℝ n k).maximal Ω ⟨x, hd ▸ hx⟩ := LinearPMap.apply_eq_of_eq' hd ⟨x, hx⟩
  obtain ⟨b, hb0, hv⟩ := happ k w hw hdeg
  refine ⟨_, _, b, h1, hu ▸ h2, hb0, fun N => ?_⟩
  obtain ⟨v, hv, hv1, _, hv2⟩ := hv N
  exact ⟨v, hv, hv1, hv2⟩

/-- **Graph-norm density in `H̊Λ(Ω)` from the approximation of smooth forms vanishing outside
`Ω`** (`exists_smooth_near_min_of_starBall`), as in `eventually_exists_graph_of_smooth`. -/
theorem eventually_exists_graph_of_smooth_min
    (S : ℕ → (minimalDeRham hΩ).Subcomplex)
    (happ : ∀ (k : ℕ) (w : FormField n) (hw : ContDiff ℝ ∞ w), (∀ x, IsDeg k (w x)) →
      (∀ x ∉ Ω, w x = 0) → ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ ∀ N, ∃ v ∈ (S N).V k,
        ‖formL2 hΩ.measurableSet hb k ⟨w, hw.continuous⟩ - v‖ ≤ b N ∧
        ∃ hv : v ∈ ((minimalDeRham hΩ).d k (k + 1)).domain,
          ‖formL2 hΩ.measurableSet hb ((k : ℤ) + 1)
              ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ -
            (minimalDeRham hΩ).d k (k + 1) ⟨v, hv⟩‖ ≤ b N)
    (k : ℤ) (x : L2F ℝ Ω (formIdx n k))
    (hx : x ∈ ((minimalDeRham hΩ).d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (S N).V k, ‖x - v‖ < ε ∧
      ‖(minimalDeRham hΩ).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  rcases k with k | k
  swap
  · have := LocalElement.subsingleton_L2F_negSucc Ω (n := n) k
    refine Eventually.of_forall fun N => ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε
  refine Subcomplex.eventually_exists_graph_of_near S hx (fun ε hε => ?_) hε
  have hd := deRham_minimalComplex_d (𝕜 := ℝ) (n := n) hΩ (k : ℤ)
  obtain ⟨w, hw, hdeg, hsupp, h1, h2⟩ := exists_smooth_near_min_of_starBall hΩ hb hs hstar k
    ⟨x, hd ▸ hx⟩ hε
  have hu : (minimalDeRham hΩ).d k (k + 1) ⟨x, hx⟩ =
      (extDerivOp ℝ n k).minimal Ω ⟨x, hd ▸ hx⟩ := LinearPMap.apply_eq_of_eq' hd ⟨x, hx⟩
  obtain ⟨b, hb0, hv⟩ := happ k w hw hdeg hsupp
  refine ⟨_, _, b, h1, hu ▸ h2, hb0, fun N => ?_⟩
  obtain ⟨v, hv, hv1, _, hv2⟩ := hv N
  exact ⟨v, hv, hv1, hv2⟩

end OfSmooth

end Feec.FiniteElement
