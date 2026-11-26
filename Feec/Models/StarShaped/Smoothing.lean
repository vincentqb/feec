module

public import Feec.FiniteElement.SmoothingBasic

/-!
# Smoothed projections on shape-regular meshes of star-shaped domains

On a bounded domain star-shaped with respect to a ball (`StarBall`), the smoothed interpolants of
the Whitney complexes of shape-regular, quasi-uniform meshes (`MeshData`) give uniformly bounded
cochain projections onto `Vₕ ⊆ HΛ(Ω)` and `V̊ₕ ⊆ H̊Λ(Ω)`.

## Main results

* `exists_norm_smoothedInterp_le`: the uniform `L²` bound of the smoothed interpolants.
* `exists_uniform_cochainProjection`: uniformly bounded smoothed cochain projections.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology

namespace Feec.Models.StarShaped

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

/-! ### Domains star-shaped with respect to a ball -/

section Geometry

variable {Ω : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {s₀ : ℝ}

/-- `Ω` is star-shaped with respect to every point of the ball `B(x₀, s₀)`. -/
def StarBall (Ω : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) (s₀ : ℝ) : Prop :=
  ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω

theorem StarBall.dil_mem (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) {x : Fin n → ℝ}
    (hx : x ∈ closure Ω) {c : ℝ} (hc2 : 1 / 2 ≤ c) (hc1 : c < 1) : x₀ + c • (x - x₀) ∈ Ω :=
  closedBall_dil_subset_of_starBall hstar hc2 hc1 (r := 0) (by nlinarith) hx
    (Metric.mem_closedBall_self le_rfl)

theorem StarBall.strict (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) {x : Fin n → ℝ}
    (hx : x ∈ closure Ω) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : x₀ + t • (x - x₀) ∈ Ω := by
  rcases le_or_gt (1 / 2) t with h | h
  · exact hstar.dil_mem hs₀ hx h ht1
  · have hy := hstar.dil_mem hs₀ hx (le_refl (1 / 2)) (by norm_num)
    have hseg := hstar _ hy x₀ (Metric.mem_ball_self hs₀)
    refine hseg ⟨1 - 2 * t, 2 * t, by linarith, by linarith, by ring, ?_⟩
    simp only [smul_add, smul_smul]
    rw [show (2 : ℝ) * t * (1 / 2) = t by ring]
    module

theorem StarBall.segment_dil_subset (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀)
    {x : Fin n → ℝ} (hx : x ∈ closure Ω) {c : ℝ} (hc2 : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    segment ℝ x (x₀ + c • (x - x₀)) ⊆ closure Ω := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  have e : a • x + b • (x₀ + c • (x - x₀)) = x₀ + (a + b * c) • (x - x₀) := by
    have ha' : a = 1 - b := by linarith
    subst ha'; module
  rw [e]
  rcases (show a + b * c ≤ 1 by nlinarith).lt_or_eq with hlt | heq
  · exact subset_closure (hstar.dil_mem hs₀ hx (by nlinarith) hlt)
  · rw [heq, one_smul, add_sub_cancel]; exact hx

theorem StarBall.interior_closure_subset (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) :
    interior (closure Ω) ⊆ Ω := by
  intro p hp
  have hc : Tendsto (fun ε : ℝ => x₀ + (1 + ε) • (p - x₀)) (𝓝 0) (𝓝 p) := by
    have : Continuous fun ε : ℝ => x₀ + (1 + ε) • (p - x₀) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), x₀ + (1 + ε) • (p - x₀) ∈ interior (closure Ω) ∧
      ε ∈ Set.Ioo (0 : ℝ) 1 :=
    ((hc.eventually (isOpen_interior.mem_nhds hp)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨ε, hε, hε01⟩ := hev.exists
  have hpos : (0 : ℝ) < 1 + ε := by linarith [hε01.1]
  have hmem := hstar.dil_mem hs₀ (interior_subset hε) (c := (1 + ε)⁻¹)
    (by rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) hpos]; linarith [hε01.2])
    (inv_lt_one_of_one_lt₀ (by linarith [hε01.1]))
  have e : x₀ + (1 + ε)⁻¹ • (x₀ + (1 + ε) • (p - x₀) - x₀) = p := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  rwa [e] at hmem

end Geometry

/-! ### The smoothing parameters -/

section Params

/-- Admissible smoothing parameters at scale `γ h`: centre `x₀` and `|c - 1| = γ h / R`. -/
structure IsAdm (x₀ : Fin n → ℝ) (R σ γ h : ℝ) (p : SmoothingParam (Fin n → ℝ)) : Prop where
  center_eq : p.center = x₀
  abs_factor_sub_one : |p.factor - 1| = γ * h / R
  rIn_eq : p.bump.rIn = γ * h * σ / 2
  rOut_eq : p.bump.rOut = γ * h * σ

/-- The parameters of the maximal family: dilation factor `1 - γ h / R` about `x₀`. -/
def pMax (x₀ : Fin n → ℝ) (R σ γ h : ℝ) (hpos : 0 < γ * h * σ) (hhalf : γ * h / R ≤ 1 / 2) :
    SmoothingParam (Fin n → ℝ) where
  center := x₀
  factor := 1 - γ * h / R
  half_le_factor := by linarith
  bump := ⟨γ * h * σ / 2, γ * h * σ, by positivity, by linarith⟩

/-- The parameters of the minimal family: dilation factor `1 + γ h / R` about `x₀`. -/
def pMin (x₀ : Fin n → ℝ) (R σ γ h : ℝ) (hpos : 0 < γ * h * σ) (hnn : 0 ≤ γ * h / R) :
    SmoothingParam (Fin n → ℝ) where
  center := x₀
  factor := 1 + γ * h / R
  half_le_factor := by linarith
  bump := ⟨γ * h * σ / 2, γ * h * σ, by positivity, by linarith⟩

variable {x₀ : Fin n → ℝ} {R σ γ h s₀ : ℝ}

theorem pMax_isAdm (hpos : 0 < γ * h * σ) (hhalf : γ * h / R ≤ 1 / 2) (hnn : 0 ≤ γ * h / R) :
    IsAdm x₀ R σ γ h (pMax x₀ R σ γ h hpos hhalf) where
  center_eq := rfl
  abs_factor_sub_one := by
    change |1 - γ * h / R - 1| = _
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hnn]
  rIn_eq := rfl
  rOut_eq := rfl

theorem pMin_isAdm (hpos : 0 < γ * h * σ) (hnn : 0 ≤ γ * h / R) :
    IsAdm x₀ R σ γ h (pMin x₀ R σ γ h hpos hnn) where
  center_eq := rfl
  abs_factor_sub_one := by
    change |1 + γ * h / R - 1| = _
    rw [add_sub_cancel_left, abs_of_nonneg hnn]
  rIn_eq := rfl
  rOut_eq := rfl

theorem pMax_isMaximal (hR : 0 < R) (hpos : 0 < γ * h * σ) (hhalf : γ * h / R ≤ 1 / 2)
    (hgh : 0 < γ * h) (hσ : σ < s₀ / (4 * R)) :
    (pMax x₀ R σ γ h hpos hhalf).IsMaximal x₀ s₀ where
  center_eq := rfl
  factor_lt_one := by
    change 1 - γ * h / R < 1
    have : 0 < γ * h / R := div_pos hgh hR
    linarith
  rOut_lt := by
    change γ * h * σ < s₀ * (1 - (1 - γ * h / R)) / 4
    rw [sub_sub_cancel]
    have h1 : γ * h * σ < γ * h * (s₀ / (4 * R)) := mul_lt_mul_of_pos_left hσ hgh
    have h2 : γ * h * (s₀ / (4 * R)) = s₀ * (γ * h / R) / 4 := by field_simp
    linarith

theorem pMin_isMinimal (hR : 0 < R) (hpos : 0 < γ * h * σ) (hnn : 0 ≤ γ * h / R)
    (hgh : 0 < γ * h) (hσ : σ < s₀ / (4 * R)) :
    (pMin x₀ R σ γ h hpos hnn).IsMinimal x₀ s₀ where
  center_eq := rfl
  one_lt_factor := by
    change 1 < 1 + γ * h / R
    have : 0 < γ * h / R := div_pos hgh hR
    linarith
  rOut_lt := by
    change γ * h * σ < s₀ * (1 + γ * h / R - 1) / 2
    rw [add_sub_cancel_left]
    have h1 : γ * h * σ < γ * h * (s₀ / (4 * R)) := mul_lt_mul_of_pos_left hσ hgh
    have h2 : γ * h * (s₀ / (4 * R)) = s₀ * (γ * h / R) / 4 := by field_simp
    have h3 : 0 < s₀ * (γ * h / R) := by
      have : 0 < s₀ / (4 * R) := lt_of_le_of_lt (by nlinarith [hpos]) hσ
      have hs : 0 < s₀ := by
        have := mul_pos this (by positivity : (0 : ℝ) < 4 * R)
        rwa [div_mul_cancel₀ _ (by positivity)] at this
      positivity
    linarith

namespace IsAdm

variable {p : SmoothingParam (Fin n → ℝ)}

theorem gh_nonneg (hp : IsAdm x₀ R σ γ h p) (hR : 0 < R) : 0 ≤ γ * h := by
  have := hp.abs_factor_sub_one ▸ abs_nonneg _
  exact (div_nonneg_iff.1 this).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_le.2 hR)

theorem factor_le_two (hp : IsAdm x₀ R σ γ h p) (hγh : γ * h / R ≤ 1) : p.factor ≤ 2 := by
  have h1 := hp.abs_factor_sub_one
  have := le_abs_self (p.factor - 1)
  linarith

theorem pow_factor_le (hp : IsAdm x₀ R σ γ h p) (hγh : γ * h / R ≤ 1) (k : ℕ) :
    p.factor ^ k ≤ 2 ^ k :=
  pow_le_pow_left₀ p.factor_pos.le (hp.factor_le_two hγh) k

theorem abs_one_sub_pow_le (hp : IsAdm x₀ R σ γ h p) (hR : 0 < R) (hγh : γ * h / R ≤ 1)
    (k : ℕ) : |1 - p.factor ^ k| ≤ k * 2 ^ k * (γ * h / R) := by
  have hg : p.factor ^ k - 1 = (∑ i ∈ Finset.range k, p.factor ^ i) * (p.factor - 1) :=
    (geom_sum_mul p.factor k).symm
  rw [abs_sub_comm, hg, abs_mul, hp.abs_factor_sub_one]
  refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (hp.gh_nonneg hR) hR.le)
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg p.factor_pos.le i)]
  calc ∑ i ∈ Finset.range k, p.factor ^ i ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) ^ k :=
        Finset.sum_le_sum fun i hi => (hp.pow_factor_le hγh i).trans
          (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hi).le)
    _ = k * 2 ^ k := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem norm_dil_sub_le (hp : IsAdm x₀ R σ γ h p) (hR : 0 < R) {x : Fin n → ℝ}
    (hx : ‖x - x₀‖ ≤ R) :
    ‖(p.center + p.factor • (x - p.center)) - x‖ ≤ γ * h := by
  rw [hp.center_eq]
  have e : x₀ + p.factor • (x - x₀) - x = (p.factor - 1) • (x - x₀) := by
    rw [sub_smul, one_smul]; abel
  rw [e, norm_smul, Real.norm_eq_abs, hp.abs_factor_sub_one]
  calc γ * h / R * ‖x - x₀‖ ≤ γ * h / R * R :=
        mul_le_mul_of_nonneg_left hx (div_nonneg (hp.gh_nonneg hR) hR.le)
    _ = γ * h := by field_simp

theorem norm_sub_le_of_dist_le (hp : IsAdm x₀ R σ γ h p) (hR : 0 < R) (hσ1 : σ ≤ 1)
    {x : Fin n → ℝ} (hx : ‖x - x₀‖ ≤ R) {t : Fin n → ℝ}
    (ht : dist t (p.center + p.factor • (x - p.center)) ≤ p.bump.rOut) :
    ‖t - x‖ ≤ 2 * (γ * h) := by
  have h1 := hp.norm_dil_sub_le hR hx
  have h2 : dist t (p.center + p.factor • (x - p.center)) ≤ γ * h := by
    rw [hp.rOut_eq] at ht
    have := hp.gh_nonneg hR
    nlinarith
  rw [← dist_eq_norm]
  calc dist t x ≤ dist t (p.center + p.factor • (x - p.center)) +
        dist (p.center + p.factor • (x - p.center)) x := dist_triangle _ _ _
    _ ≤ γ * h + γ * h := add_le_add h2 (by rw [dist_eq_norm]; exact h1)
    _ = 2 * (γ * h) := by ring

end IsAdm

theorem closedInterior_subset_cthickening {M : SimplicialMesh n} {γ : ℝ}
    (hh : 0 < M.meshSize) (hγ2 : γ ≤ 1 / 2) {T T' : Affine.Simplex ℝ (Fin n → ℝ) n}
    {x t : Fin n → ℝ}
    (hxT : x ∈ T.closedInterior) (htT' : t ∈ T'.closedInterior) (hT' : T' ∈ M.simplices)
    (hxt : ‖t - x‖ ≤ 2 * (γ * M.meshSize)) :
    T'.closedInterior ⊆ Metric.cthickening (2 * M.meshSize) T.closedInterior := by
  intro y hy
  have hdy : ‖y - t‖ ≤ M.meshSize := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem T'.isCompact_closedInterior.isBounded hy htT').trans
      (M.diam_le_meshSize hT')
  refine Metric.mem_cthickening_of_dist_le y x _ _ hxT ?_
  rw [dist_eq_norm]
  calc ‖y - x‖ = ‖(y - t) + (t - x)‖ := by congr 1; abel
    _ ≤ ‖y - t‖ + ‖t - x‖ := norm_add_le _ _
    _ ≤ M.meshSize + 2 * (γ * M.meshSize) := add_le_add hdy hxt
    _ ≤ 2 * M.meshSize := by nlinarith

end Params

/-! ### Paths from face points to the samples of the smoother -/

section Paths

variable {Ω : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {s₀ R σ γ h : ℝ}
  {p : SmoothingParam (Fin n → ℝ)}

theorem path_of_isMaximal (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) (hp : p.IsMaximal x₀ s₀)
    {x : Fin n → ℝ} (hx : x ∈ closure Ω) {t : Fin n → ℝ}
    (ht : dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut) :
    segment ℝ x (p.center + p.factor • (x - p.center)) ⊆ closure Ω ∧
      segment ℝ (p.center + p.factor • (x - p.center)) t ⊆ closure Ω := by
  rw [hp.center_eq] at ht ⊢
  refine ⟨hstar.segment_dil_subset hs₀ hx p.half_le_factor hp.factor_lt_one.le, ?_⟩
  have hball := closedBall_dil_subset_of_starBall hstar p.half_le_factor hp.factor_lt_one
    hp.rOut_lt hx
  refine ((convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self
    p.bump.rOut_pos.le) (Metric.mem_closedBall.2 ht.le)).trans (hball.trans subset_closure)

theorem path_of_isMinimal (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) (hR : 0 < R)
    (hp : p.IsMinimal x₀ s₀) (hpA : IsAdm x₀ R σ γ h p) (hγh : γ * h / R < 1)
    (hσ : σ ≤ s₀ / (8 * R)) {x : Fin n → ℝ} {t : Fin n → ℝ} (htΩ : t ∈ Ω)
    (ht : dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut) :
    segment ℝ x (x₀ + p.factor⁻¹ • (t - x₀)) ⊆ closure Ω ∧
      segment ℝ (x₀ + p.factor⁻¹ • (t - x₀)) t ⊆ closure Ω ∧
      ‖x₀ + p.factor⁻¹ • (t - x₀) - x‖ ≤ p.bump.rOut := by
  rw [hp.center_eq] at ht
  have hc1 := hp.one_lt_factor
  have hc0 : 0 < p.factor := p.factor_pos
  have hc2 := hpA.factor_le_two hγh.le
  set tt := x₀ + p.factor⁻¹ • (t - x₀)
  have he : tt - x = p.factor⁻¹ • (t - (x₀ + p.factor • (x - x₀))) := by
    simp only [tt, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
    abel
  have hnorm : ‖tt - x‖ ≤ p.bump.rOut := by
    rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc0.le), ← dist_eq_norm]
    calc p.factor⁻¹ * dist t (x₀ + p.factor • (x - x₀)) ≤ 1 * p.bump.rOut :=
          mul_le_mul (inv_le_one_of_one_le₀ hc1.le) ht.le dist_nonneg zero_le_one
      _ = p.bump.rOut := one_mul _
  -- the ball around `tt` of radius `rOut` lies in `Ω`
  have hci2 : 1 / 2 ≤ p.factor⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) hc0]; linarith
  have hci1 : p.factor⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc1
  have hr : p.bump.rOut < s₀ * (1 - p.factor⁻¹) / 4 := by
    rw [hpA.rOut_eq]
    have hgh := hpA.abs_factor_sub_one
    rw [abs_of_pos (by linarith)] at hgh
    have h1 : 1 - p.factor⁻¹ = (p.factor - 1) / p.factor := by field_simp
    rw [h1, hgh]
    have hgh0 : 0 < γ * h := by
      have : 0 < γ * h / R := by rw [← hgh]; linarith
      exact (div_pos_iff.1 this).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_lt.2 hR.le)
    have : γ * h * σ ≤ γ * h * (s₀ / (8 * R)) := mul_le_mul_of_nonneg_left hσ hgh0.le
    have h2 : s₀ * (γ * h / R) / 8 < s₀ * (γ * h / R / p.factor) / 4 := by
      have : γ * h / R / 2 < γ * h / R / p.factor :=
        div_lt_div_of_pos_left (by positivity) hc0 (by linarith)
      nlinarith
    have h3 : γ * h * (s₀ / (8 * R)) = s₀ * (γ * h / R) / 8 := by field_simp
    linarith
  have hball := closedBall_dil_subset_of_starBall hstar hci2 hci1 hr (subset_closure htΩ)
  refine ⟨?_, ?_, hnorm⟩
  · refine ((convex_closedBall _ _).segment_subset ?_ (Metric.mem_closedBall_self
      p.bump.rOut_pos.le)).trans (hball.trans subset_closure)
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]; exact hnorm
  · have hseg := hstar t htΩ x₀ (Metric.mem_ball_self hs₀)
    have htt : tt ∈ segment ℝ x₀ t := by
      rw [segment_eq_image_lineMap]
      exact ⟨p.factor⁻¹, ⟨inv_nonneg.2 hc0.le, hci1.le⟩, by
        simp [tt, AffineMap.lineMap_apply_module']; abel⟩
    exact ((convex_segment x₀ t).segment_subset htt (right_mem_segment ℝ x₀ t)).trans
      (hseg.trans subset_closure)

theorem norm_sub_le_of_mem_segment {x a b q : Fin n → ℝ} {r : ℝ} (ha : ‖a - x‖ ≤ r)
    (hb : ‖b - x‖ ≤ r) (hq : q ∈ segment ℝ a b) : ‖q - x‖ ≤ r := by
  have := (convex_closedBall x r).segment_subset (by rwa [Metric.mem_closedBall, dist_eq_norm])
    (by rwa [Metric.mem_closedBall, dist_eq_norm]) hq
  rwa [Metric.mem_closedBall, dist_eq_norm] at this

end Paths

/-! ### The uniform `L²` bound of the smoothed interpolants -/

section Bound

/-- Shape regularity and quasi-uniformity of a mesh, with a positive mesh size. -/
structure MeshData (M : SimplicialMesh n) (C c q : ℝ) : Prop where
  shape : IsShapeRegular (M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) C c
  quasi : IsQuasiUniform M q
  meshSize_pos : 0 < M.meshSize

/-- The overlap constant `6ⁿ n! / (c qⁿ)`. -/
def covConst (n : ℕ) (c q : ℝ) : ℝ := 6 ^ n * n.factorial / (c * q ^ n)

open Classical in
theorem sum_locMass_le {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) (hc : 0 < c)
    (hq : 0 < q) (hΩ : MeasurableSet M.domain) {k : ℤ} (x : L2F ℝ M.domain (formIdx n k)) :
    ∑ T ∈ M.simplices, locMass (2 * M.meshSize) x T ≤ covConst n c q * ‖x‖ ^ 2 := by
  set h := M.meshSize
  have hh := hM.meshSize_pos
  set F : (Fin n → ℝ) → ℝ := fun t => ∑ s : formIdx n k,
    (M.domain.indicator ((x s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t) ^ 2
  have hF : Integrable F := integrable_finsetSum _ fun s _ => integrable_sq_indicator hΩ _
  have hF0 : ∀ t, 0 ≤ F t := fun t => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∀ T : Affine.Simplex ℝ (Fin n → ℝ) n, locMass (2 * h) x T =
      ∫ t in Metric.cthickening (2 * h) T.closedInterior, F t := fun T => by
    rw [locMass, integral_finsetSum _ fun s _ => (integrable_sq_indicator hΩ _).integrableOn]
  simp_rw [h1]
  have hK : ∀ t, ((M.simplices.filter fun T : Affine.Simplex ℝ (Fin n → ℝ) n =>
      t ∈ Metric.cthickening (2 * h) T.closedInterior).card : ℝ) ≤ covConst n c q := by
    intro t
    refine (card_filter_mem_cthickening_le M hM.shape hc hq hM.quasi hh (by positivity) t).trans
      (le_of_eq ?_)
    rw [covConst, show 2 * (2 * h + h) = 6 * h by ring, mul_pow, mul_pow]
    field_simp
    rfl
  refine (sum_integral_le_of_card_le M.simplices _
    (fun T => Metric.isClosed_cthickening.measurableSet)
    hK hF hF0).trans (le_of_eq ?_)
  rw [integral_finsetSum _ fun s _ => integrable_sq_indicator hΩ _, PiLp.norm_sq_eq_of_L2]
  simp_rw [integral_sq_indicator hΩ]

variable {x₀ : Fin n → ℝ} {R σ γ : ℝ}

theorem IsAdm.abs_smoothForm_le_locMass {M : SimplicialMesh n} {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hh : 0 < M.meshSize) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hγh : γ * M.meshSize / R ≤ 1) (hΩ : MeasurableSet M.domain) {k : ℕ}
    (x : L2F ℝ M.domain (formIdx n k)) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) :
    ∀ y ∈ T.closedInterior, ∀ s, |(smoothForm p hΩ k x : FormField n) y s| ≤
      2 ^ k * √((1 / (γ * M.meshSize * σ)) ^ n * locMass (2 * M.meshSize) x T) := by
  intro y hy s
  have hMρ : 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn) =
      (1 / (γ * M.meshSize * σ)) ^ n := by
    rw [hp.rIn_eq, volume_real_closedBall_zero (by positivity), one_div_pow]
    congr 2; ring
  refine (abs_smoothForm_le hΩ p k x y s).trans (mul_le_mul (hp.pow_factor_le hγh k)
    ?_ (Real.sqrt_nonneg _) (by positivity))
  rw [hMρ]
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s' _ => ?_)
    (by positivity))
  refine setIntegral_mono_set (integrable_sq_indicator hΩ _).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun t ht => ?_)
  have hyc : y ∈ closure M.domain := M.closedInterior_subset_closure hT hy
  have h1 := hp.norm_sub_le_of_dist_le hR hσ1 (hRx y hyc) (Metric.mem_closedBall.1 ht)
  refine Metric.mem_cthickening_of_dist_le t y _ _ hy ?_
  rw [dist_eq_norm]
  nlinarith

theorem sum_integral_sq_le_of_abs_le {M : SimplicialMesh n} {k : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) {z : FormField n}
    (hzc : Continuous z) {K : ℝ} (hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ K) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2 ≤
      2 ^ n * ((2 * M.meshSize) ^ n * K ^ 2) := by
  have hTh : diam T ≤ M.meshSize := M.diam_le_meshSize hT
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, (2 * M.meshSize) ^ n * K ^ 2 := Finset.sum_le_sum fun s _ =>
        (integral_closedInterior_le (f := fun y => (z y s.1) ^ 2) (A := K ^ 2)
          (((continuous_apply s.1).comp hzc).pow 2)
          (fun y hy => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hzb y hy s.1) 2)
          (fun y => sq_nonneg _)).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
            (by linarith [diam_nonneg T]) (by linarith) n) (sq_nonneg _))
    _ = Fintype.card (formIdx n k) * ((2 * M.meshSize) ^ n * K ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * ((2 * M.meshSize) ^ n * K ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _)
          (mul_nonneg (pow_nonneg (by linarith [diam_nonneg T]) n) (sq_nonneg _))

theorem norm_sq_glue_le_locMass (E : LocalElement n) {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hc : 0 < c) (hq : 0 < q) (hΩ : MeasurableSet M.domain) {k : ℕ}
    (x : L2F ℝ M.domain (formIdx n k)) (u : E.Piecewise M k) {K : ℝ} (hK : 0 ≤ K)
    (hloc : ∀ T (hT : T ∈ M.simplices), ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((u ⟨T, hT⟩ : E.space T k) : FormField n) y s.1) ^ 2 ≤ K * locMass (2 * M.meshSize) x T) :
    ‖E.glue M k u‖ ^ 2 ≤ K * (covConst n c q * ‖x‖ ^ 2) := by
  refine (norm_sq_glue_le E M u _ hloc).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_locMass_le hM hc hq hΩ x) hK

theorem sum_integral_sq_interp_le {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    [NeZero n] {k : ℕ} {B : ℝ}
    (hB : ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ {z : FormField n}, z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
        (∀ g ⊆ vertexSet T, g.card = k + 1 →
          |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
        ∀ x ∈ T.closedInterior, ∀ s, diam T ^ k * |z x s| ≤ B * D)
    (hR : 0 < R) (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm x₀ R σ γ M.meshSize p) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hγh : γ * M.meshSize / R ≤ 1)
    (hΩ : MeasurableSet M.domain) (x : L2F ℝ M.domain (formIdx n k))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((whitneyElement n).globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) :
          (whitneyElement n).Piecewise M k) ⟨T, hT⟩ : (whitneyElement n).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (2 / (γ * σ)) ^ n * locMass (2 * M.meshSize) x T := by
  set h := M.meshSize
  have hh : 0 < h := hM.meshSize_pos
  have hT0 : 0 < diam T := diam_pos T
  set z : FormField n := ((((whitneyElement n).globalInterp M k
    (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) :
      (whitneyElement n).Piecewise M k) ⟨T, hT⟩ : (whitneyElement n).space T k) : FormField n)
  have hz : z ∈ p1MinusForms n k := mem_p1MinusForms_of_space _
  set L := locMass (2 * h) x T
  have hL := locMass_nonneg (2 * h) x T
  set A := 2 ^ k * √((1 / (γ * h * σ)) ^ n * L)
  have hA0 : 0 ≤ A := by positivity
  -- the face integrals of `z` are `O(h_Tᵏ A)`, hence `|z| ≤ B 2ⁿ A` on `T`
  have hdof : ∀ g ⊆ vertexSet T, g.card = k + 1 →
      |simplexIntegral (faceEnum g (k + 1)) z| ≤ 2 ^ n * diam T ^ k * A := by
    intro g hgT hg
    rw [simplexIntegral_globalInterp k _ ⟨T, hT⟩ hgT hg]
    exact abs_simplexIntegral_face_le' hgT hg hA0
      (hp.abs_smoothForm_le_locMass hh hR hRx hγ hγ1 hσ hσ1 hγh hΩ x hT)
  have hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ B * 2 ^ n * A := fun y hy s =>
    le_of_mul_le_mul_left ((hB hM.shape T hT hT0 hz (by positivity) hdof y hy s).trans
      (le_of_eq (by ring))) (pow_pos hT0 k)
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ 2 ^ n * ((2 * h) ^ n * (B * 2 ^ n * A) ^ 2) :=
        sum_integral_sq_le_of_abs_le hT (isAffineField_of_mem_p1MinusForms hz).continuous hzb
    _ = 2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (2 * h * (1 / (γ * h * σ))) ^ n * L := by
        rw [mul_pow (B * 2 ^ n) A, mul_pow (2 ^ k), Real.sq_sqrt (by positivity), mul_pow (2 * h)]
        ring
    _ = 2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (2 / (γ * σ)) ^ n * L := by
        rw [show 2 * h * (1 / (γ * h * σ)) = 2 / (γ * σ) by field_simp]

/-- The smoothed interpolants on quasi-uniform shape-regular meshes with `cl Ω ⊆ B̄(x₀, R)` are
bounded in `L²`, uniformly in the mesh. -/
theorem exists_norm_smoothedInterp_le [NeZero n] {C c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ K, 0 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩ : MeasurableSet M.domain),
      0 < R → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) → γ * M.meshSize / R ≤ 1 →
      ∀ (p : SmoothingParam (Fin n → ℝ)), IsAdm x₀ R σ γ M.meshSize p →
      ∀ (k : ℕ) (x : L2F ℝ M.domain (formIdx n k)),
        ‖(whitneyElement n).smoothedInterp M p hΩ k x‖ ≤ K * ‖x‖ := by
  choose B hB0 hB using fun k : ℕ => exists_dof_bound_p1MinusForms (n := n) k (C := C) (c := c)
  have hG : ∀ k, 0 ≤ 2 ^ n * (B k * 2 ^ n * 2 ^ k) ^ 2 * (2 / (γ * σ)) ^ n * covConst n c q :=
    fun k => by have := hB0 k; simp only [covConst]; positivity
  refine ⟨_, Real.sqrt_nonneg _, fun M hM hΩ hR hRx hγh p hp k x =>
    norm_le_sqrt_sum_of_sq_le hG fun _ => ?_⟩
  rw [(whitneyElement n).smoothedInterp_natCast, mul_assoc]
  exact norm_sq_glue_le_locMass _ hM hc hq hΩ x _ (by have := hB0 k; positivity)
    fun T hT => sum_integral_sq_interp_le hM (hB k) hR hRx hp hγ hγ1 hσ hσ1 hγh hΩ x hT

end Bound

/-! ### Closeness of the smoothed interpolants to the identity on `Vₕ` -/

section Close

/-- The local inverse estimates on all simplices of `M`, in terms of the mesh size. -/
def InvBoundM (M : SimplicialMesh n) (k : ℕ) (A : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∀ z ∈ p1MinusForms n k,
    (∀ x ∈ T.closedInterior, ∀ s, √M.meshSize ^ n * |z x s| ≤
      A * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2)) ∧
    (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
      √M.meshSize ^ n * M.meshSize * |z x s - z x' s| ≤
        A * ‖x - x'‖ * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2))

theorem MeshData.q_le_one {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) :
    q ≤ 1 := by
  have hh := hM.meshSize_pos
  obtain ⟨T, hT⟩ : M.simplices.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : M.meshSize ≤ 0 := M.meshSize_le le_rfl fun T hT => by simp [hne] at hT
    linarith
  have h1 := hM.quasi T hT
  have h2 := M.diam_le_meshSize hT
  by_contra h
  push Not at h
  nlinarith

theorem MeshData.diam_pos {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    0 < diam T :=
  lt_of_lt_of_le (mul_pos hq hM.meshSize_pos) (hM.quasi T hT)

theorem invBoundM_of {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) (hq : 0 < q)
    {k : ℕ} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ u ∈ p1MinusForms n k,
        (∀ x ∈ T.closedInterior, ∀ s, √(diam T) ^ n * |u x s| ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
          √(diam T) ^ n * diam T * |u x s - u x' s| ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u))) :
    InvBoundM M k (A / √q ^ n / q) := by
  intro T hT z hz
  have hh := hM.meshSize_pos
  have hq1 := hM.q_le_one
  have hTd := hM.diam_pos hq hT
  obtain ⟨h1, h2⟩ := hA hM.shape T hT hTd z hz
  simp only [formL2Sq] at h1 h2
  set F := ∑ s, ∫ x in T.closedInterior, (z x s) ^ 2
  have hqh : q * M.meshSize ≤ diam T := hM.quasi T hT
  have hsq : √M.meshSize ^ n * √q ^ n ≤ √(diam T) ^ n := by
    rw [← mul_pow, ← Real.sqrt_mul hh.le]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) n
  have hsqq : 0 < √q ^ n := pow_pos (Real.sqrt_pos.2 hq) n
  have hF : 0 ≤ √F := Real.sqrt_nonneg _
  constructor
  · intro x hx s
    have := h1 x hx s
    have hk : √M.meshSize ^ n * |z x s| ≤ A / √q ^ n * √F := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsqq]
      calc √M.meshSize ^ n * |z x s| * √q ^ n = (√M.meshSize ^ n * √q ^ n) * |z x s| := by ring
        _ ≤ √(diam T) ^ n * |z x s| := mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
        _ ≤ _ := this
    refine hk.trans (mul_le_mul_of_nonneg_right ?_ hF)
    exact le_div_self (by positivity) hq hq1
  · intro x hx x' hx' s
    have := h2 x hx x' hx' s
    rw [div_div]
    rw [show A / (√q ^ n * q) * ‖x - x'‖ * √F =
      ‖x - x'‖ * A * √F / (√q ^ n * q) by ring]
    rw [le_div_iff₀ (by positivity)]
    calc √M.meshSize ^ n * M.meshSize * |z x s - z x' s| * (√q ^ n * q)
        = (√M.meshSize ^ n * √q ^ n) * (q * M.meshSize) * |z x s - z x' s| := by ring
      _ ≤ √(diam T) ^ n * diam T * |z x s - z x' s| := by
          gcongr
      _ ≤ A * ‖x - x'‖ * √F := this
      _ = ‖x - x'‖ * A * √F := by ring

variable {x₀ : Fin n → ℝ} {R σ γ : ℝ}

/-- The geometric condition: near the points of a face `g`, every sampled simplex contains `g`. -/
def GeomOK (M : SimplicialMesh n) (p : SmoothingParam (Fin n → ℝ)) (θ : ℝ) (k : ℕ) : Prop :=
  ∀ (T : M.simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → g.card = k + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex k, ξ ∉ nearBdry k θ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (faceEnum g (k + 1)) ξ - p.center)) <
        p.bump.rOut → ∀ T' : M.simplices,
        t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
        g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)

/-- The sampling condition: samples outside `Ω` near a `k`-face `g` force its integral to vanish. -/
def SampleOK {M : SimplicialMesh n} {k : ℕ} (p : SmoothingParam (Fin n → ℝ)) (θ : ℝ)
    (u : (whitneyElement n).Piecewise M k) : Prop :=
  ∀ (T : M.simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → g.card = k + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex k, ξ ∉ nearBdry k θ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (faceEnum g (k + 1)) ξ - p.center)) <
        p.bump.rOut → t ∉ M.domain →
        simplexIntegral (faceEnum g (k + 1))
          ((u T : (whitneyElement n).space T k) : FormField n) = 0

open Classical in
theorem sqrt_mul_abs_integrand_le {M : SimplicialMesh n} (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundM M k A) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ}
    (hgeom : GeomOK M p θ k) {u : (whitneyElement n).Piecewise M k}
    (hu : u ∈ (whitneyElement n).globalSpace M k) (hs : SampleOK p θ u) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hg : g.card = k + 1) {ξ : Fin k → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex k) :
    √M.meshSize ^ n * |∑ s, (((u T : (whitneyElement n).space T k) : FormField n)
        (simplexMap (faceEnum g (k + 1)) ξ) s -
      (smoothForm p hΩ k ((whitneyElement n).glue M k u) : FormField n)
        (simplexMap (faceEnum g (k + 1)) ξ) s) *
          wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ| ≤
      (∑ s, |wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ|) * A *
        √(locMass (2 * M.meshSize) ((whitneyElement n).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        2 ^ (k + 1) * (if ξ ∈ nearBdry k θ then 1 else (k + 1) * (2 * γ)) := by
  set h := M.meshSize
  have hγ1 : γ ≤ 1 := by linarith
  have hγh : γ * h / R ≤ 1 := by
    rw [div_le_one hR]; nlinarith
  set q := faceEnum g (k + 1)
  set x := simplexMap q ξ
  set uT : FormField n := ((u T : (whitneyElement n).space T k) : FormField n)
  set L := locMass (2 * h) ((whitneyElement n).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_faceEnum_mem hgT hg hξ
  have hxc : x ∈ closure M.domain := M.closedInterior_subset_closure T.2 hxT
  -- the local fields near `x` obey the inverse estimates against the local mass of `T`
  have hinv : ∀ T' : M.simplices, (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
      (∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * |((u T' : (whitneyElement n).space T' k) : FormField n) y s| ≤ A * √L) ∧
      ∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        ∀ y' ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * h * |((u T' : (whitneyElement n).space T' k) : FormField n) y s -
          ((u T' : (whitneyElement n).space T' k) : FormField n) y' s| ≤ A * ‖y - y'‖ * √L := by
    intro T' hsub
    have hL' := Real.sqrt_le_sqrt (sum_integral_sq_le_of_subset (whitneyElement n) hΩ hint u T'
      hsub)
    obtain ⟨h1, h2⟩ := hA T' T'.2 _ (mem_p1MinusForms_of_space (u T'))
    exact ⟨fun y hy s => (h1 y hy s).trans (mul_le_mul_of_nonneg_left hL' hA0),
      fun y hy y' hy' s => (h2 y hy y' hy' s).trans
        (mul_le_mul_of_nonneg_left hL' (by positivity))⟩
  refine sqrt_mul_abs_sum_sub_smoothForm_le hΩ p _ x (uT x) _ (ξ ∈ nearBdry k θ)
    (pow_pos (Real.sqrt_pos.2 hh) n) hA0 (by positivity) (hp.pow_factor_le hγh k)
    ((hp.abs_one_sub_pow_le hR hγh k).trans (mul_le_mul_of_nonneg_left
      (by rw [div_le_iff₀ hR]; nlinarith) (by positivity)))
    (fun s => (hinv T (Metric.self_subset_cthickening _)).1 x hxT s) ?_ ?_
  · filter_upwards [ae_extField_glue_eq (whitneyElement n) u hΩ] with t ht hdist htΩ
    obtain ⟨T', htT', hext⟩ := ht htΩ
    set u' : FormField n := ((u T' : (whitneyElement n).space T' k) : FormField n)
    have htT'c : t ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset htT'
    have hxt' : ‖t - x‖ ≤ 2 * (γ * h) := hp.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) hdist.le
    obtain ⟨hb1, hb2⟩ := hinv T' (closedInterior_subset_cthickening hh hγ2 hxT htT'c T'.2 hxt')
    refine ⟨u', hext, fun s => hb1 t htT'c s, fun hbad => ?_⟩
    have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
      hgeom T g hgT hg ξ hξ hbad t hdist T' htT'
    have hxT' := simplexMap_faceEnum_mem hgT' hg hξ
    refine ⟨?_, fun s => hb1 x hxT' s, fun s => ?_⟩
    · rw [sum_mul_minor_eq (mem_p1MinusForms_of_space (u T)) q ξ,
        sum_mul_minor_eq (mem_p1MinusForms_of_space (u T')) q ξ,
        simplexIntegral_eq_of_mem_globalSpace hu T T' hgT hgT' hg]
    · refine le_of_mul_le_mul_right ?_ hh
      calc √h ^ n * |u' x s - u' t s| * h = √h ^ n * h * |u' x s - u' t s| := by ring
        _ ≤ A * ‖x - t‖ * √L := hb2 x hxT' t htT'c s
        _ ≤ A * (2 * (γ * h)) * √L := by rw [norm_sub_rev]; gcongr
        _ = 2 * γ * (A * √L) * h := by ring
  · intro hbad t hdist htΩ
    rw [sum_mul_minor_eq (mem_p1MinusForms_of_space (u T)) q ξ]
    change ↑k.factorial * simplexIntegral q uT = 0
    rw [hs T g hgT hg ξ hξ hbad t hdist htΩ, mul_zero]

theorem sqrt_mul_abs_dof_err_le {M : SimplicialMesh n} (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundM M k A) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : GeomOK M p θ k) {u : (whitneyElement n).Piecewise M k}
    (hu : u ∈ (whitneyElement n).globalSpace M k) (hs : SampleOK p θ u) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hg : g.card = k + 1) :
    √M.meshSize ^ n * |simplexIntegral (faceEnum g (k + 1))
        ((u T : (whitneyElement n).space T k) : FormField n) -
      simplexIntegral (faceEnum g (k + 1))
        (smoothForm p hΩ k ((whitneyElement n).glue M k u) : FormField n)| ≤
      2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A * (γ + θ) * M.meshSize ^ k *
        √(locMass (2 * M.meshSize) ((whitneyElement n).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  classical
  set h := M.meshSize
  set q := faceEnum g (k + 1)
  set uT : FormField n := ((u T : (whitneyElement n).space T k) : FormField n)
  set w : FormField n := (smoothForm p hΩ k ((whitneyElement n).glue M k u) : FormField n)
  set m : Finset (Fin n) → ℝ := fun s => wedgeProd (simplexMatrix q) s univ
  set L := locMass (2 * h) ((whitneyElement n).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hMm : ∑ s, |m s| ≤ 2 ^ n * (k.factorial * h ^ k) :=
    (sum_abs_minor_face_le hgT hg).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (diam_nonneg _) (M.diam_le_meshSize T.2) k) (by positivity))
      (by positivity))
  have huc : Continuous uT :=
    (isAffineField_of_mem_p1MinusForms (mem_p1MinusForms_of_space _)).continuous
  have hwc : Continuous w := (mem_c1Forms.1 (smoothForm p hΩ k
    ((whitneyElement n).glue M k u)).2).continuous
  set F : (Fin k → ℝ) → ℝ := fun ξ => ∑ s, (uT (simplexMap q ξ) s - w (simplexMap q ξ) s) * m s
  have hFc : Continuous F := continuous_finsetSum _ fun s _ =>
    ((((continuous_apply s).comp (huc.comp (continuous_simplexMap q))).sub
      ((continuous_apply s).comp (hwc.comp (continuous_simplexMap q)))).mul continuous_const)
  have herr : simplexIntegral q uT - simplexIntegral q w =
      ∫ ξ in FiniteElement.refSimplex k, F ξ := by
    rw [← simplexIntegral_sub huc.continuousOn hwc.continuousOn, simplexIntegral_def]
    rfl
  set c := 2 ^ n * (k.factorial * h ^ k) * A * √L * 2 ^ (k + 1)
  have hc0 : 0 ≤ c := by positivity
  rw [herr]
  refine (mul_abs_integral_refSimplex_le hFc (pow_nonneg (Real.sqrt_nonneg _) n) hc0
    (by positivity) hθ0 hθ1 fun ξ hξ =>
      (sqrt_mul_abs_integrand_le hΩ hint hA0 hA hp hR hRx hhR hh hγ hγ2 hσ1 hgeom hu hs T
        hgT hg hξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMm hA0) (Real.sqrt_nonneg _)) (by positivity))
        (by split_ifs <;> positivity))).trans ?_
  have : 0 ≤ c * ((k + 1) * θ) := by positivity
  calc c * ((k + 1) * (2 * γ) + (k + 1) * θ) ≤
        c * ((k + 1) * (2 * γ)) + 2 * (c * ((k + 1) * θ)) := by linarith
    _ = _ := by simp only [c]; ring

theorem sum_integral_sq_sub_interp_le {M : SimplicialMesh n} [NeZero n] {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A B : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundM M k A)
    (hB : ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ {z : FormField n}, z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
        (∀ g ⊆ vertexSet T, g.card = k + 1 →
          |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
        ∀ x ∈ T.closedInterior, ∀ s, diam T ^ k * |z x s| ≤ B * D)
    {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : GeomOK M p θ k) {u : (whitneyElement n).Piecewise M k}
    (hu : u ∈ (whitneyElement n).globalSpace M k) (hs : SampleOK p θ u) (T : M.simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (whitneyElement n).space T k) : FormField n) -
        ((((whitneyElement n).globalInterp M k
          (Submodule.inclusion c1Forms_le_contForms
            (smoothForm p hΩ k ((whitneyElement n).glue M k u))) :
            (whitneyElement n).Piecewise M k) T : (whitneyElement n).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      4 ^ n * (B * (2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2 *
        locMass (2 * M.meshSize) ((whitneyElement n).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := M.meshSize
  have hh : 0 < h := hM.meshSize_pos
  set w := smoothForm p hΩ k ((whitneyElement n).glue M k u)
  set z : FormField n := ((u T : (whitneyElement n).space T k) : FormField n) -
    ((((whitneyElement n).globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) :
      (whitneyElement n).Piecewise M k) T : (whitneyElement n).space T k) : FormField n)
  have hz : z ∈ p1MinusForms n k := Submodule.sub_mem _ (mem_p1MinusForms_of_space _)
    (mem_p1MinusForms_of_space _)
  set L := locMass (2 * h) ((whitneyElement n).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _ _
  set C₁ := 2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A
  have hC₁ : 0 ≤ C₁ := by positivity
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hγθ : 0 ≤ γ + θ := by linarith
  set D := C₁ * (γ + θ) * h ^ k * √L / √h ^ n
  have hD0 : 0 ≤ D := by positivity
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), g.card = k + 1 →
      |simplexIntegral (faceEnum g (k + 1)) z| ≤ D := by
    intro g hgT hg
    have hc1 : Continuous ((u T : (whitneyElement n).space T k) : FormField n) :=
      (isAffineField_of_mem_p1MinusForms (mem_p1MinusForms_of_space _)).continuous
    have hc2 : Continuous ((((whitneyElement n).globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms w) : (whitneyElement n).Piecewise M k) T :
          (whitneyElement n).space T k) : FormField n) :=
      (isAffineField_of_mem_p1MinusForms (mem_p1MinusForms_of_space _)).continuous
    rw [simplexIntegral_sub hc1.continuousOn hc2.continuousOn,
      simplexIntegral_globalInterp k _ T hgT hg, le_div_iff₀ hsq, mul_comm]
    exact sqrt_mul_abs_dof_err_le hΩ hint hA0 hA hp hR hRx hhR hh hγ hγ2 hσ1 hθ0 hθ1 hgeom hu hs
      T hgT hg
  have hTd := hM.diam_pos hq T.2
  have hqh : q * h ≤ diam (T : Affine.Simplex ℝ (Fin n → ℝ) n) := hM.quasi T T.2
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * (C₁ * (γ + θ) / q ^ k) * √L / √h ^ n := by
    intro y hy s
    have h1 := hB hM.shape T T.2 hTd hz hD0 hdof y hy s
    have hqk : 0 < (q * h) ^ k := pow_pos (mul_pos hq hh) k
    have h2 : (q * h) ^ k * |z y s| ≤ B * D :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hqh k) (abs_nonneg _)).trans h1
    refine le_of_mul_le_mul_left (h2.trans (le_of_eq ?_)) hqk
    simp only [D]; field_simp; ring
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (z y s.1) ^ 2
      ≤ 2 ^ n * ((2 * h) ^ n * (B * (C₁ * (γ + θ) / q ^ k) * √L / √h ^ n) ^ 2) :=
        sum_integral_sq_le_of_abs_le T.2 (isAffineField_of_mem_p1MinusForms hz).continuous hzb
    _ = 4 ^ n * (B * C₁ * (γ + θ) / q ^ k) ^ 2 * (√L) ^ 2 := by
        rw [mul_pow 2 h, hhn, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by
          rw [← mul_pow]; norm_num]
        field_simp
    _ = 4 ^ n * (B * C₁ * (γ + θ) / q ^ k) ^ 2 * L := by rw [Real.sq_sqrt hL0]

theorem norm_sq_sub_smoothedInterp_le {M : SimplicialMesh n} [NeZero n] {C c q : ℝ}
    (hM : MeshData M C c q) (hc : 0 < c) (hq : 0 < q) (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A B : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundM M k A)
    (hB : ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ {z : FormField n}, z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
        (∀ g ⊆ vertexSet T, g.card = k + 1 →
          |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
        ∀ x ∈ T.closedInterior, ∀ s, diam T ^ k * |z x s| ≤ B * D)
    {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : GeomOK M p θ k) {u : (whitneyElement n).Piecewise M k}
    (hu : u ∈ (whitneyElement n).globalSpace M k) (hs : SampleOK p θ u) :
    ‖(whitneyElement n).glue M k u - (whitneyElement n).smoothedInterp M p hΩ k
        ((whitneyElement n).glue M k u)‖ ^ 2 ≤
      4 ^ n * (B * (2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2 *
        (covConst n c q * ‖(whitneyElement n).glue M k u‖ ^ 2) := by
  set v := (whitneyElement n).glue M k u
  have hQ := (whitneyElement n).smoothedInterp_natCast M p hΩ k v
  set Pw := (whitneyElement n).globalInterp M k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p hΩ k v))
  set d : (whitneyElement n).Piecewise M k := u - (Pw : (whitneyElement n).Piecewise M k)
  have hsub : v - (whitneyElement n).smoothedInterp M p hΩ k v = (whitneyElement n).glue M k d := by
    rw [hQ, map_sub]
  rw [hsub]
  exact norm_sq_glue_le_locMass _ hM hc hq hΩ v d (by positivity) fun T hT =>
    sum_integral_sq_sub_interp_le hM hq hΩ hint hA0 hA hB hp hR hRx hhR hγ hγ2 hσ1 hθ0 hθ1
      hgeom hu hs ⟨T, hT⟩

end Close

/-! ### The geometric and sampling conditions for both families -/

section Families

variable {x₀ : Fin n → ℝ} {s₀ R σ γ : ℝ}

theorem coordLip_of {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) (hq : 0 < q)
    (hC : 0 ≤ C) : StarGeom.CoordLip M (n * ((n + 1) * (C / (q * M.meshSize)))) := by
  intro T hT i y y'
  refine (abs_coord_sub_le T i y y').trans ?_
  obtain ⟨-, hBs, -⟩ := hM.shape T hT
  have hT0 := hM.diam_pos hq hT
  have h1 : ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ C / (q * M.meshSize) :=
    hBs.trans (div_le_div_of_nonneg_left hC (mul_pos hq hM.meshSize_pos) (hM.quasi T hT))
  gcongr

theorem isFacePoint_of_notMem_nearBdry {M : SimplicialMesh n} {k : ℕ} {g : Finset (Fin n → ℝ)}
    (hg : g.card = k + 1) {θ : ℝ} {ξ : Fin k → ℝ} (hξ : ξ ∉ nearBdry k θ) :
    StarGeom.IsFacePoint M g θ (simplexMap (faceEnum g (k + 1)) ξ) := by
  rw [simplexMap_eq_sum]
  refine StarGeom.isFacePoint_sum_smul (injective_faceEnum hg) (range_faceEnum hg)
    (fun a => ?_) (sum_refBary ξ)
  by_contra hlt; push Not at hlt; exact hξ ⟨a, hlt⟩

theorem coord_near {M : SimplicialMesh n} {C q : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) {x y : Fin n → ℝ}
    (hy : ‖y - x‖ ≤ 2 * (γ * M.meshSize)) :
    n * ((n + 1) * (C / (q * M.meshSize))) * ‖y - x‖ < θ := by
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy (by positivity)) (lt_of_eq_of_lt ?_ hθ)
  field_simp

theorem subset_vertexSet_of_isMaximal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) {T T' : M.simplices} {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) {x : Fin n → ℝ}
    (hx : StarGeom.IsFacePoint M g θ x)
    (hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior) {t : Fin n → ℝ}
    (ht : dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut)
    (htT' : t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior) :
    g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  have hh := hM.meshSize_pos
  have hxc := M.closedInterior_subset_closure T.2 hxT
  obtain ⟨h1, h2⟩ := path_of_isMaximal hstar hs₀ hp hxc ht
  have hgh := hpA.gh_nonneg hR
  have hŷ : ‖(p.center + p.factor • (x - p.center)) - x‖ ≤ 2 * (γ * M.meshSize) :=
    (hpA.norm_dil_sub_le hR (hRx x hxc)).trans (by linarith)
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have hxx : ‖x - x‖ ≤ 2 * (γ * M.meshSize) := by rw [sub_self, norm_zero]; positivity
  exact StarGeom.subset_vertexSet_of_segments (coordLip_of hM hq hC) hx
    (StarGeom.mem_starSet.2 ⟨T, T.2, hgT, hxT⟩) h1
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hxx hŷ hy)) h2
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hŷ ht' hy)) T'.2 htT'

theorem subset_vertexSet_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMinimal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hσ : σ ≤ s₀ / (8 * R))
    (hγ : 0 < γ) (hγh : γ * M.meshSize / R < 1) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) {T T' : M.simplices} {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) {x : Fin n → ℝ}
    (hx : StarGeom.IsFacePoint M g θ x)
    (hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior) {t : Fin n → ℝ}
    (ht : dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut)
    (htT' : t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior) :
    g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  have hh := hM.meshSize_pos
  have hxc := M.closedInterior_subset_closure T.2 hxT
  obtain ⟨h1, h2, h3⟩ := path_of_isMinimal hstar hs₀ hR hp hpA hγh hσ (hint T' T'.2 htT') ht
  have hgh := hpA.gh_nonneg hR
  have htt : ‖x₀ + p.factor⁻¹ • (t - x₀) - x‖ ≤ 2 * (γ * M.meshSize) := by
    refine h3.trans ?_
    rw [hpA.rOut_eq]; nlinarith
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have hxx : ‖x - x‖ ≤ 2 * (γ * M.meshSize) := by rw [sub_self, norm_zero]; positivity
  exact StarGeom.subset_vertexSet_of_segments (coordLip_of hM hq hC) hx
    (StarGeom.mem_starSet.2 ⟨T, T.2, hgT, hxT⟩) h1
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hxx htt hy)) h2
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment htt ht' hy)) T'.2 htT'

theorem geomOK_of_isMaximal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀) (hs₀ : 0 < s₀)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) (k : ℕ) : GeomOK M p θ k := by
  intro T g hgT hg ξ hξ hξb _ ht _ htT'
  exact subset_vertexSet_of_isMaximal hM hq hC hstar hs₀ hp hpA hR hRx hσ1 hγ hθ hgT
    (isFacePoint_of_notMem_nearBdry hg hξb) (simplexMap_faceEnum_mem hgT hg hξ) ht htT'

theorem geomOK_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀) (hs₀ : 0 < s₀)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMinimal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hσ : σ ≤ s₀ / (8 * R))
    (hγ : 0 < γ) (hγh : γ * M.meshSize / R < 1) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) (k : ℕ) : GeomOK M p θ k := by
  intro T g hgT hg ξ hξ hξb _ ht _ htT'
  exact subset_vertexSet_of_isMinimal hM hq hC hstar hs₀ hint hp hpA hR hRx hσ1 hσ hγ hγh hθ hgT
    (isFacePoint_of_notMem_nearBdry hg hξb) (simplexMap_faceEnum_mem hgT hg hξ) ht htT'

theorem sampleOK_of_isMaximal {M : SimplicialMesh n} (hstar : StarBall M.domain x₀ s₀)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀) {θ : ℝ} {k : ℕ}
    (u : (whitneyElement n).Piecewise M k) : SampleOK p θ u := by
  intro T g hgT hg ξ hξ _ t ht htΩ
  exfalso
  have hxT := simplexMap_faceEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have := closedBall_dil_subset_of_starBall hstar p.half_le_factor hp.factor_lt_one hp.rOut_lt hxc
  rw [← hp.center_eq] at this
  exact htΩ (this (Metric.mem_closedBall.2 ht.le))

theorem sampleOK_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) {p : SmoothingParam (Fin n → ℝ)}
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) {k : ℕ}
    {u : (whitneyElement n).Piecewise M k} (hu : u ∈ (whitneyElement n).globalSpace₀ M k) :
    SampleOK p θ u := by
  classical
  intro T g hgT hg ξ hξ hξb t ht htΩ
  have hh := hM.meshSize_pos
  set x := simplexMap (faceEnum g (k + 1)) ξ
  have hx := isFacePoint_of_notMem_nearBdry (M := M) hg hξb
  have hxT := simplexMap_faceEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have htc : t ∉ interior (closure M.domain) := fun h' =>
    htΩ (hstar.interior_closure_subset hs₀ h')
  obtain ⟨F, hF, hgF⟩ := StarGeom.exists_isBoundaryFacet_of_near (by positivity)
    (coordLip_of hM hq hC) hx T.2 hgT hxT htc (coord_near hq hC hh hγ hθ ht')
  obtain ⟨-, T'', hT'', hFT''⟩ := hF.1
  have h0 := hu.2 ⟨T'', hT''⟩ F hF hFT'' g hgF (⟨(), hg⟩ : WhitneyDofIdx g k)
  rw [simplexIntegral_localDof ⟨T'', hT''⟩ hg] at h0
  rw [simplexIntegral_eq_of_mem_globalSpace hu.1 T ⟨T'', hT''⟩ hgT (hgF.trans hFT'') hg]
  exact h0

end Families

/-! ### The smoothing scale and the smoothed-projection estimates -/

section Estimates

variable {x₀ : Fin n → ℝ}

variable (n) in
theorem exists_gamma [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hq : 0 < q) :
    ∃ γ₀ K₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 4 ∧ 2 * (n * ((n + 1) * C)) / q < K₀ ∧
      ∀ γ, 0 < γ → γ ≤ γ₀ →
      ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩ : MeasurableSet M.domain),
      (∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) →
      ∀ {R σ : ℝ}, 0 < R → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) → M.meshSize ≤ 2 * R →
      σ ≤ 1 → ∀ (p : SmoothingParam (Fin n → ℝ)), IsAdm x₀ R σ γ M.meshSize p →
      ∀ (k : ℕ), GeomOK M p (K₀ * γ) k → ∀ u ∈ (whitneyElement n).globalSpace M k,
        SampleOK p (K₀ * γ) u →
        ‖(whitneyElement n).glue M k u - (whitneyElement n).smoothedInterp M p hΩ k
          ((whitneyElement n).glue M k u)‖ ≤ 1 / 2 * ‖(whitneyElement n).glue M k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_inverse_bound_p1MinusForms (n := n) k hC hc
  choose B hB0 hB using fun k : ℕ => exists_dof_bound_p1MinusForms (n := n) k (C := C) (c := c)
  set K₀ : ℝ := 2 * (n * ((n + 1) * C)) / q + 1
  have hK₀ : 1 ≤ K₀ := by simp only [K₀]; have : 0 ≤ 2 * (n * ((n + 1) * C)) / q := by positivity
                          linarith
  set A' : ℕ → ℝ := fun k => A k / √q ^ n / q
  have hA'0 : ∀ k, 0 ≤ A' k := fun k => by have := hA0 k; simp only [A']; positivity
  set x : ℕ → ℝ := fun k =>
    B k * (2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A' k) * (1 + K₀) / q ^ k
  have hx0 : ∀ k, 0 ≤ x k := fun k => by
    have := hB0 k; have := hA'0 k; simp only [x]; positivity
  set S := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hx0 k
  set Kc : ℝ := max 1 (4 ^ n * covConst n c q)
  have hKc : 1 ≤ Kc := le_max_left _ _
  set γ₁ := 1 / (2 * (1 + S * Kc))
  have hpos : 0 < 1 + S * Kc := by nlinarith
  have hγ₁ : 0 < γ₁ := by positivity
  set γ₀ := min (min (1 / 4) (1 / K₀)) γ₁
  refine ⟨γ₀, K₀, lt_min (lt_min (by norm_num) (by positivity)) hγ₁,
    (min_le_left _ _).trans (min_le_left _ _), lt_add_one _, fun γ hγ hγγ₀ => ?_⟩
  have hγ4 : γ ≤ 1 / 4 := hγγ₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγK : γ ≤ 1 / K₀ := hγγ₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγγ₀ : γ ≤ γ₁ := hγγ₀.trans (min_le_right _ _)
  intro M hM hΩ hint R σ hR hRx hhR hσ1 p hp k hgeom u hu hs
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := M.domain) hk
    rw [Subsingleton.elim ((whitneyElement n).glue M k u) 0]; simp
  push Not at hk
  have hInv := invBoundM_of hM hq (hA0 k) (hA k)
  have hθ0 : 0 ≤ K₀ * γ := by positivity
  have hθ1 : K₀ * γ ≤ 1 := by
    calc K₀ * γ ≤ K₀ * (1 / K₀) := mul_le_mul_of_nonneg_left hγK (by linarith)
      _ = 1 := by field_simp
  have h := norm_sq_sub_smoothedInterp_le hM hc hq hΩ hint (hA'0 k) hInv (hB k) hp hR hRx hhR hγ
    (by linarith) hσ1 hθ0 hθ1 hgeom hu hs
  have hxk : x k ≤ S := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  have he : B k * (2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A' k) * (γ + K₀ * γ) /
      q ^ k = x k * γ := by simp only [x]; ring
  rw [he] at h
  have hq1 : 4 ^ n * (x k * γ) ^ 2 * covConst n c q ≤ 1 / 4 := by
    have h1 : 4 ^ n * (x k * γ) ^ 2 * covConst n c q ≤ Kc * (x k * γ₁) ^ 2 := by
      have hcov : 0 ≤ covConst n c q := by unfold covConst; positivity
      calc 4 ^ n * (x k * γ) ^ 2 * covConst n c q = (4 ^ n * covConst n c q) * (x k * γ) ^ 2 := by
            ring
        _ ≤ Kc * (x k * γ₁) ^ 2 := mul_le_mul (le_max_right _ _)
            (pow_le_pow_left₀ (by have := hx0 k; positivity)
              (mul_le_mul_of_nonneg_left hγγ₀ (hx0 k)) 2) (sq_nonneg _) (by linarith)
    exact h1.trans (sq_le_quarter hS hKc (hx0 k) hxk)
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 4 ^ n * (x k * γ) ^ 2 * (covConst n c q * ‖(whitneyElement n).glue M k u‖ ^ 2)
      = (4 ^ n * (x k * γ) ^ 2 * covConst n c q) * ‖(whitneyElement n).glue M k u‖ ^ 2 := by ring
    _ ≤ 1 / 4 * ‖(whitneyElement n).glue M k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq1 (sq_nonneg _)
    _ = (1 / 2 * ‖(whitneyElement n).glue M k u‖) ^ 2 := by ring

theorem meshSize_le_two_mul {M : SimplicialMesh n} {R : ℝ} (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) : M.meshSize ≤ 2 * R := by
  refine M.meshSize_le (by positivity) fun T hT => ?_
  have hsub : T.closedInterior ⊆ Metric.closedBall x₀ R := fun y hy => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hRx y (M.closedInterior_subset_closure hT hy)
  exact (Metric.diam_mono hsub Metric.isBounded_closedBall).trans (Metric.diam_closedBall hR.le)

theorem interior_subset_domain {M : SimplicialMesh n} {s₀ : ℝ} (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain := fun _T hT =>
  (interior_mono (M.closedInterior_subset_closure hT)).trans (hstar.interior_closure_subset hs₀)

theorem isBounded_domain_of {M : SimplicialMesh n} {R : ℝ}
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) : Bornology.IsBounded M.domain :=
  (Metric.isBounded_closedBall (x := x₀) (r := R)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hRx y (subset_closure hy)

/-- The bump-radius ratio `σ = min 1 (s₀ / (8 R))`. -/
def sigmaOf (s₀ R : ℝ) : ℝ := min 1 (s₀ / (8 * R))

theorem sigmaOf_pos {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) : 0 < sigmaOf s₀ R :=
  lt_min one_pos (by positivity)

theorem sigmaOf_le_one (s₀ R : ℝ) : sigmaOf s₀ R ≤ 1 := min_le_left _ _

theorem sigmaOf_le (s₀ R : ℝ) : sigmaOf s₀ R ≤ s₀ / (8 * R) := min_le_right _ _

theorem sigmaOf_lt {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) : sigmaOf s₀ R < s₀ / (4 * R) :=
  (sigmaOf_le s₀ R).trans_lt (div_lt_div_of_pos_left hs₀ (by positivity) (by linarith))

/-- Uniformly bounded smoothed cochain projections onto the Whitney complexes of quasi-uniform
shape-regular meshes, in `L²` and every graph norm. [AFW2010], §5.5; [ChristiansenWinther2008] -/
theorem exists_uniform_cochainProjection [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hq : 0 < q) {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩo : IsOpen M.domain),
      StarBall M.domain x₀ s₀ → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) →
      ∃ π : ((whitneyElement n).subcomplex M hΩo).CochainProjection,
        (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨γ, K₀, hγ, hγ4, hK₀, hclose⟩ := exists_gamma n (x₀ := x₀) hC hc hq
  have hθ : 2 * (n * ((n + 1) * C)) / q * γ < K₀ * γ := mul_lt_mul_of_pos_right hK₀ hγ
  replace hclose := hclose γ hγ le_rfl
  set σ := sigmaOf s₀ R
  obtain ⟨K', hK'0, hbound⟩ := exists_norm_smoothedInterp_le (x₀ := x₀) (R := R) hc hq hγ
    (by linarith) (sigmaOf_pos hs₀ hR) (sigmaOf_le_one s₀ R)
  refine ⟨max 1 (2 * K'), le_max_left _ _, fun M hM hΩo hstar hRx => ?_⟩
  set h := M.meshSize
  have hh := hM.meshSize_pos
  have hhR := meshSize_le_two_mul hR hRx
  have hγh2 : γ * h / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hR]; nlinarith
  have hpos : 0 < γ * h * σ := by have := sigmaOf_pos hs₀ hR; positivity
  have hnn : 0 ≤ γ * h / R := by positivity
  set p := pMax x₀ R σ γ h hpos hγh2
  have hp : p.IsMaximal x₀ s₀ := pMax_isMaximal hR hpos hγh2 (by positivity) (sigmaOf_lt hs₀ hR)
  have hpA : IsAdm x₀ R σ γ h p := pMax_isAdm hpos hγh2 hnn
  have hint := interior_subset_domain hstar hs₀
  set Q := (whitneyElement n).smoothedCommutingMap M p hΩo hstar hp
  have hQ : ∀ i, Q.Q i = (whitneyElement n).smoothedInterp M p hΩo.measurableSet i := fun i => rfl
  have hQb : ∀ i x, ‖Q.Q i x‖ ≤ K' * ‖x‖ := by
    intro i x
    rw [hQ]
    rcases i with k | k
    · exact hbound M hM hΩo.measurableSet hR hRx (by linarith) p hpA k x
    · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hQc : ∀ i, ∀ v ∈ ((whitneyElement n).subcomplex M hΩo).V i,
      ‖v - Q.Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro i v hv
    rw [hQ]
    rcases i with k | k
    · obtain ⟨u, rfl⟩ := hv
      exact hclose M hM hΩo.measurableSet hint hR hRx hhR (sigmaOf_le_one s₀ R) p hpA k
        (geomOK_of_isMaximal hM hq hC hstar hs₀ hp hpA hR hRx (sigmaOf_le_one s₀ R) hγ hθ k)
        u.1 u.2 (sampleOK_of_isMaximal hstar hp u.1)
    · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hb : ∀ i x, ‖(Q.toCochainProjection (θ := 1 / 2) (by norm_num) hQc).π i x‖ ≤
      max 1 (2 * K') * ‖x‖ := fun i x =>
    (Q.norm_toCochainProjection_le_two_mul hQc (hQb i) x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  exact ⟨_, hb, fun i j => (Q.toCochainProjection _ hQc).isGraphBounded_of_norm_le (hb i) (hb j)⟩

theorem exists_uniform_cochainProjectionMin [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hq : 0 < q) {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩo : IsOpen M.domain),
      ∀ (hstar : StarBall M.domain x₀ s₀), (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) →
      ∃ π : ((whitneyElement n).subcomplexMin M hΩo x₀
          (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)).CochainProjection,
        (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨γ, K₀, hγ, hγ4, hK₀, hclose⟩ := exists_gamma n (x₀ := x₀) hC hc hq
  have hθ : 2 * (n * ((n + 1) * C)) / q * γ < K₀ * γ := mul_lt_mul_of_pos_right hK₀ hγ
  replace hclose := hclose γ hγ le_rfl
  set σ := sigmaOf s₀ R
  obtain ⟨K', hK'0, hbound⟩ := exists_norm_smoothedInterp_le (x₀ := x₀) (R := R) hc hq hγ
    (by linarith) (sigmaOf_pos hs₀ hR) (sigmaOf_le_one s₀ R)
  refine ⟨max 1 (2 * K'), le_max_left _ _, fun M hM hΩo hstar hRx => ?_⟩
  set h := M.meshSize
  have hh := hM.meshSize_pos
  have hhR := meshSize_le_two_mul hR hRx
  have hγh1 : γ * h / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hR]; nlinarith
  have hpos : 0 < γ * h * σ := by have := sigmaOf_pos hs₀ hR; positivity
  have hnn : 0 ≤ γ * h / R := by positivity
  set p := pMin x₀ R σ γ h hpos hnn
  have hp : p.IsMinimal x₀ s₀ := pMin_isMinimal hR hpos hnn (by positivity) (sigmaOf_lt hs₀ hR)
  have hpA : IsAdm x₀ R σ γ h p := pMin_isAdm hpos hnn
  have hint := interior_subset_domain hstar hs₀
  have hb := isBounded_domain_of hRx
  set Q := (whitneyElement n).smoothedCommutingMapMin M p hΩo hb hstar hp x₀
    (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)
  have hQ : ∀ i, Q.Q i = (whitneyElement n).smoothedInterp M p hΩo.measurableSet i := fun i => rfl
  have hQb : ∀ i x, ‖Q.Q i x‖ ≤ K' * ‖x‖ := by
    intro i x
    rw [hQ]
    rcases i with k | k
    · exact hbound M hM hΩo.measurableSet hR hRx (by linarith) p hpA k x
    · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hQc : ∀ i, ∀ v ∈ ((whitneyElement n).subcomplexMin M hΩo x₀
      (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)).V i,
      ‖v - Q.Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro i v hv
    rw [hQ]
    rcases i with k | k
    · obtain ⟨u, rfl⟩ := hv
      exact hclose M hM hΩo.measurableSet hint hR hRx hhR (sigmaOf_le_one s₀ R) p hpA k
        (geomOK_of_isMinimal hM hq hC hstar hs₀ hint hp hpA hR hRx (sigmaOf_le_one s₀ R)
          (sigmaOf_le s₀ R) hγ (by linarith) hθ k)
        u.1 ((whitneyElement n).globalSpace₀_le M k u.2)
        (sampleOK_of_isMinimal hM hq hC hstar hs₀ hpA hR hRx (sigmaOf_le_one s₀ R) hγ hθ u.2)
    · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hb : ∀ i x, ‖(Q.toCochainProjection (θ := 1 / 2) (by norm_num) hQc).π i x‖ ≤
      max 1 (2 * K') * ‖x‖ := fun i x =>
    (Q.norm_toCochainProjection_le_two_mul hQc (hQb i) x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  exact ⟨_, hb, fun i j => (Q.toCochainProjection _ hQc).isGraphBounded_of_norm_le (hb i) (hb j)⟩

end Estimates

end Feec.Models.StarShaped
