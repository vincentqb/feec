module

public import Feec.Models.BoundedDomain.Compactness
public import Feec.Domain.LipschitzPullback
public import Feec.Models.StarShaped.FiniteElement
public import Feec.Models.BoundedDomain.MovingTSD

/-!
# Weber compactness and a complete set of eigenvectors on star-shaped domains

Every bounded domain star-shaped with respect to a ball, in particular every ball and every bounded
open convex set, has Weber compactness, so the wave group of the grad–curl complex has a complete
set of eigenvectors there.

## Main results

* `hasWeberCompactness_of_biLipschitz`: Weber compactness passes along bi-Lipschitz maps of `ℝ³`.
* `StarDomain.eigenDense_gradCurl`: a complete set of eigenvectors on star-shaped domains.
* `eigenDense_gradCurl_ball`: a complete set of eigenvectors on every Euclidean ball.
* `coreSub_le_stationary_ball_iff`: when `K*` is stationary on a ball.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace NNReal Topology Pointwise
open Set MeasureTheory Filter LinearPMap

namespace Feec.Models.StarShaped

open Feec.Domain Feec.HilbertComplex Feec.Operator Feec.Models.BoundedDomain



/-- A Lipschitz gauge on `ℝ³`: positively homogeneous, Lipschitz, and comparable to the norm. -/
structure IsLipGauge (g : R3 → ℝ) (a b L : ℝ) : Prop where
  a_pos : 0 < a
  smul : ∀ t : ℝ, 0 ≤ t → ∀ v, g (t • v) = t * g v
  lower : ∀ v, a * ‖v‖ ≤ g v
  upper : ∀ v, g v ≤ b * ‖v‖
  lip : ∀ v w, |g v - g w| ≤ L * ‖v - w‖

namespace IsLipGauge

variable {g : R3 → ℝ} {a b L : ℝ} (hg : IsLipGauge g a b L)
include hg

theorem map_zero : g 0 = 0 := by
  have := hg.smul 0 le_rfl 0; simpa using this

theorem pos {v : R3} (hv : v ≠ 0) : 0 < g v :=
  lt_of_lt_of_le (mul_pos hg.a_pos (norm_pos_iff.2 hv)) (hg.lower v)

theorem nonneg (v : R3) : 0 ≤ g v :=
  le_trans (mul_nonneg hg.a_pos.le (norm_nonneg _)) (hg.lower v)

theorem b_pos : 0 < b := by
  have h := (hg.lower (fun _ => 1)).trans (hg.upper (fun _ => 1))
  have hn : (0 : ℝ) < ‖(fun _ => 1 : R3)‖ := norm_pos_iff.2 fun h => by
    simpa using congrFun h 0
  by_contra hb
  push Not at hb
  nlinarith [hg.a_pos]

end IsLipGauge

/-- The radial map `v ↦ (h v / g v) v`, sending the level sets of `h` to those of `g`. -/
def radial (g h : R3 → ℝ) (v : R3) : R3 := (h v / g v) • v

variable {g h : R3 → ℝ} {a b L a' b' L' : ℝ}

theorem gauge_radial (hg : IsLipGauge g a b L) (hh : IsLipGauge h a' b' L') (v : R3) :
    g (radial g h v) = h v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [radial, hh.map_zero, hg.map_zero]
  · rw [radial, hg.smul _ (div_nonneg (hh.nonneg v) (hg.nonneg v)),
      div_mul_cancel₀ _ (hg.pos hv).ne']

theorem radial_radial (hg : IsLipGauge g a b L) (hh : IsLipGauge h a' b' L') (v : R3) :
    radial h g (radial g h v) = v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [radial]
  · have hq : 0 ≤ h v / g v := div_nonneg (hh.nonneg v) (hg.nonneg v)
    have h2 : h (radial g h v) = h v / g v * h v := by rw [radial, hh.smul _ hq]
    have hgv := (hg.pos hv).ne'
    have hhv := (hh.pos hv).ne'
    rw [show radial h g (radial g h v) = (g (radial g h v) / h (radial g h v)) • radial g h v
      from rfl, gauge_radial hg hh v, h2, show radial g h v = (h v / g v) • v from rfl, smul_smul]
    have : h v / (h v / g v * h v) * (h v / g v) = 1 := by field_simp
    rw [this, one_smul]

theorem norm_radial_sub_le (hg : IsLipGauge g a b L) (hh : IsLipGauge h a' b' L') (v w : R3) :
    ‖radial g h v - radial g h w‖ ≤ (b' / a + L' / a + b' * L / a ^ 2) * ‖v - w‖ := by
  have ha := hg.a_pos
  have hb' := hh.b_pos
  have hL0 : 0 ≤ L := by
    have := (abs_nonneg _).trans (hg.lip (fun _ => 1) 0)
    have hn : (0 : ℝ) < ‖(fun _ => 1 : R3) - 0‖ := norm_pos_iff.2 fun h => by
      simpa using congrFun h 0
    exact nonneg_of_mul_nonneg_left this hn
  have hL0' : 0 ≤ L' := by
    have := (abs_nonneg _).trans (hh.lip (fun _ => 1) 0)
    have hn : (0 : ℝ) < ‖(fun _ => 1 : R3) - 0‖ := norm_pos_iff.2 fun h => by
      simpa using congrFun h 0
    exact nonneg_of_mul_nonneg_left this hn
  have hC : b' / a ≤ b' / a + L' / a + b' * L / a ^ 2 := by
    have : 0 ≤ L' / a + b' * L / a ^ 2 := by positivity
    linarith
  -- the ratio is bounded by `b' / a`
  have hq : ∀ u : R3, h u / g u * ‖u‖ ≤ b' / a * ‖u‖ := fun u => by
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · have hgu := hg.pos hu
      rw [div_mul_eq_mul_div, div_le_iff₀ hgu]
      calc h u * ‖u‖ ≤ b' * ‖u‖ * ‖u‖ := mul_le_mul_of_nonneg_right (hh.upper u) (norm_nonneg _)
        _ = b' / a * ‖u‖ * (a * ‖u‖) := by field_simp
        _ ≤ b' / a * ‖u‖ * g u := mul_le_mul_of_nonneg_left (hg.lower u) (by positivity)
  have hr0 : radial g h 0 = 0 := by simp [radial]
  rcases eq_or_ne v 0 with rfl | hv
  · rw [hr0, zero_sub, norm_neg, zero_sub, norm_neg, radial, norm_smul,
      Real.norm_of_nonneg (div_nonneg (hh.nonneg w) (hg.nonneg w))]
    exact (hq w).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  rcases eq_or_ne w 0 with rfl | hw
  · rw [hr0, sub_zero, sub_zero, radial, norm_smul,
      Real.norm_of_nonneg (div_nonneg (hh.nonneg v) (hg.nonneg v))]
    exact (hq v).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  have hgv := hg.pos hv
  have hgw := hg.pos hw
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw
  have e : radial g h v - radial g h w =
      (h w / g w) • (v - w) + (h v / g v - h w / g w) • v := by
    simp only [radial, smul_sub, sub_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (div_nonneg (hh.nonneg w) (hg.nonneg w)),
    Real.norm_eq_abs]
  -- the first term
  have t1 : h w / g w * ‖v - w‖ ≤ b' / a * ‖v - w‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [div_le_div_iff₀ hgw ha]
    calc h w * a ≤ b' * ‖w‖ * a := mul_le_mul_of_nonneg_right (hh.upper w) ha.le
      _ = b' * (a * ‖w‖) := by ring
      _ ≤ b' * g w := mul_le_mul_of_nonneg_left (hg.lower w) hb'.le
  -- the second term
  have e2 : h v / g v - h w / g w = (h v - h w) / g v + h w * (g w - g v) / (g v * g w) := by
    field_simp; ring
  have t2 : |h v / g v - h w / g w| * ‖v‖ ≤ (L' / a + b' * L / a ^ 2) * ‖v - w‖ := by
    rw [e2]
    have hA : |(h v - h w) / g v| * ‖v‖ ≤ L' / a * ‖v - w‖ := by
      rw [abs_div, abs_of_pos hgv, div_mul_eq_mul_div, div_le_iff₀ hgv]
      calc |h v - h w| * ‖v‖ ≤ L' * ‖v - w‖ * ‖v‖ :=
            mul_le_mul_of_nonneg_right (hh.lip v w) (norm_nonneg _)
        _ = L' / a * ‖v - w‖ * (a * ‖v‖) := by field_simp
        _ ≤ L' / a * ‖v - w‖ * g v :=
            mul_le_mul_of_nonneg_left (hg.lower v) (by positivity)
    have hB : |h w * (g w - g v) / (g v * g w)| * ‖v‖ ≤ b' * L / a ^ 2 * ‖v - w‖ := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hgv hgw), abs_of_nonneg (hh.nonneg w),
        div_mul_eq_mul_div, div_le_iff₀ (mul_pos hgv hgw)]
      have hl : |g w - g v| ≤ L * ‖v - w‖ := by rw [abs_sub_comm]; exact hg.lip v w
      calc h w * |g w - g v| * ‖v‖ ≤ (b' * ‖w‖) * (L * ‖v - w‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul (hh.upper w) hl (abs_nonneg _) (by positivity))
              (norm_nonneg _)
        _ = b' * L / a ^ 2 * ‖v - w‖ * ((a * ‖v‖) * (a * ‖w‖)) := by field_simp
        _ ≤ b' * L / a ^ 2 * ‖v - w‖ * (g v * g w) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul (hg.lower v) (hg.lower w) (by positivity) hgv.le
    calc |(h v - h w) / g v + h w * (g w - g v) / (g v * g w)| * ‖v‖ ≤
          (|(h v - h w) / g v| + |h w * (g w - g v) / (g v * g w)|) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) (norm_nonneg _)
      _ ≤ L' / a * ‖v - w‖ + b' * L / a ^ 2 * ‖v - w‖ := by rw [add_mul]; linarith
      _ = (L' / a + b' * L / a ^ 2) * ‖v - w‖ := by ring
  linarith



theorem IsLipGauge.L_nonneg (hg : IsLipGauge g a b L) : 0 ≤ L := by
  have := (abs_nonneg _).trans (hg.lip (fun _ => 1) 0)
  have hn : (0 : ℝ) < ‖(fun _ => 1 : R3) - 0‖ := norm_pos_iff.2 fun h => by
    simpa using congrFun h 0
  exact nonneg_of_mul_nonneg_left this hn

/-- The radial bi-Lipschitz map `y ↦ x₀ + (h / g)(y - x₀) (y - x₀)` of `ℝ³`. -/
def radialMap (x₀ : R3) (hg : IsLipGauge g a b L) (hh : IsLipGauge h a' b' L') : BiLipschitz where
  toFun y := x₀ + radial g h (y - x₀)
  invFun y := x₀ + radial h g (y - x₀)
  K := max (Real.toNNReal (b' / a + L' / a + b' * L / a ^ 2))
    (Real.toNNReal (b / a' + L / a' + b * L' / a' ^ 2))
  lipschitz := by
    have h1 := hg.a_pos; have h2 := hh.b_pos; have h3 := hg.L_nonneg; have h4 := hh.L_nonneg
    have hC : 0 ≤ b' / a + L' / a + b' * L / a ^ 2 := by positivity
    refine (LipschitzWith.of_dist_le_mul fun x y => ?_).weaken (le_max_left _ _)
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, Real.coe_toNNReal _ hC]
    have := norm_radial_sub_le hg hh (x - x₀) (y - x₀)
    rwa [sub_sub_sub_cancel_right] at this
  lipschitz_inv := by
    have h1 := hh.a_pos; have h2 := hg.b_pos; have h3 := hg.L_nonneg; have h4 := hh.L_nonneg
    have hC : 0 ≤ b / a' + L / a' + b * L' / a' ^ 2 := by positivity
    refine (LipschitzWith.of_dist_le_mul fun x y => ?_).weaken (le_max_right _ _)
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, Real.coe_toNNReal _ hC]
    have := norm_radial_sub_le hh hg (x - x₀) (y - x₀)
    rwa [sub_sub_sub_cancel_right] at this
  left_inv x := by simp [radial_radial hg hh]
  right_inv y := by simp [radial_radial hh hg]

theorem radialMap_mem_iff (x₀ : R3) (hg : IsLipGauge g a b L) (hh : IsLipGauge h a' b' L')
    (x : R3) : h (x - x₀) < 1 ↔ g ((radialMap x₀ hg hh) x - x₀) < 1 := by
  change h (x - x₀) < 1 ↔ g (x₀ + radial g h (x - x₀) - x₀) < 1
  rw [add_sub_cancel_left, gauge_radial hg hh]

theorem isLipGauge_norm : IsLipGauge (fun v : R3 => ‖v‖) 1 1 1 where
  a_pos := one_pos
  smul t ht v := by rw [norm_smul, Real.norm_of_nonneg ht]
  lower v := by rw [one_mul]
  upper v := by rw [one_mul]
  lip v w := by rw [one_mul]; exact abs_norm_sub_norm_le v w

/-- If `Φ` is a bi-Lipschitz homeomorphism of `ℝ³` with `Φ(U) = Ω` (`U`, `Ω` bounded open) and `U`
has Weber compactness, so has `Ω`. -/
theorem hasWeberCompactness_of_biLipschitz (Φ : BiLipschitz) {U Ω : Set R3} (hU : IsOpen U)
    (hΩ : IsOpen Ω) (hUb : Bornology.IsBounded U) (hΩb : Bornology.IsBounded Ω)
    (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) (hW : HasWeberCompactness U) : HasWeberCompactness Ω := by
  set T := (gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal U
  set S := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal U
  have hadj : T† = (gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal U :=
    (gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).adjoint_minimal
  have hlam : 0 < 1 / (6 * (Φ.K : ℝ) ^ 3 * (9 * (Φ.K : ℝ) ^ 2)) := by
    have := Φ.K_pos; positivity
  obtain ⟨KU, hKU, hsub⟩ := HasCompactPair.exists_isCompact_coeff (T := T) (S := S)
    ((gradOp 3 3).dense_minimal_domain hU) ((gradOp 3 3).isClosed_minimal hU)
    (ConstCoeffOp.minimal_mapsTo hU isComplexPair_grad_curl)
    (ConstCoeffOp.minimal_comp hU isComplexPair_grad_curl)
    (hasCompactBall_minimal_grad hU hUb).hasCompactPerp
    hW.hasCompactPair (Φ.coeff hU.measurableSet) hlam
    (fun v => by simpa using Φ.coeff_coercive hU.measurableSet v)
  have hfinU : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hfinΩ : volume Ω ≠ ⊤ := hΩb.measure_lt_top.ne
  set P1 := Φ.pull1 hU.measurableSet hUΩ
  set P2 := Φ.pull2 hU.measurableSet hUΩ
  set PJ := Φ.pullJ hU.measurableSet hUΩ
  set c : ℝ := max ‖P1‖ (max ‖P2‖ ‖PJ‖) + 1
  have hc : 0 < c := by positivity
  -- the compact set
  set KΩ := P1 ⁻¹' ((fun v => c • v) '' KU)
  have hemb : Topology.IsClosedEmbedding P1 := by
    refine (AddMonoidHomClass.antilipschitz_of_bound P1 (K :=
      Real.toNNReal (Real.sqrt (6 * (Φ.K : ℝ) ^ 3 * (9 * (Φ.K : ℝ) ^ 2))))
        fun u => ?_).isClosedEmbedding P1.uniformContinuous
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    exact Φ.norm_le_norm_pull1 hU.measurableSet hUΩ u
  refine ⟨KΩ, hemb.isCompact_preimage (hKU.image (continuous_const_smul c)), ?_⟩
  intro u hu hu' h1 h2 h3
  obtain ⟨hv, hcurl⟩ := Φ.pull1_mem_minimal_curl hU hΩ hUΩ ⟨u, hu⟩
  obtain ⟨hp, hdiv⟩ := Φ.piola_mem_maximal_divT hU hΩ hfinU hfinΩ hUΩ ⟨u, hu'⟩
  have hc1 : ‖P1‖ ≤ c := by simp only [c]; linarith [le_max_left ‖P1‖ (max ‖P2‖ ‖PJ‖)]
  have hc2 : ‖P2‖ ≤ c := by
    simp only [c]; linarith [le_max_left ‖P2‖ ‖PJ‖, le_max_right ‖P1‖ (max ‖P2‖ ‖PJ‖)]
  have hcJ : ‖PJ‖ ≤ c := by
    simp only [c]; linarith [le_max_right ‖P2‖ ‖PJ‖, le_max_right ‖P1‖ (max ‖P2‖ ‖PJ‖)]
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hbound : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
      [NormedSpace ℝ Y] (L : X →L[ℝ] Y) (x : X), ‖L‖ ≤ c → ‖x‖ ≤ 1 → ‖c⁻¹ • L x‖ ≤ 1 :=
    fun L x hL hx => by
      rw [norm_smul, Real.norm_of_nonneg hci.le, inv_mul_le_iff₀ hc, mul_one]
      exact (L.le_opNorm x).trans ((mul_le_mul hL hx (norm_nonneg _) hc.le).trans_eq (mul_one c))
  set v := c⁻¹ • P1 u
  have hvS : v ∈ S.domain := S.domain.smul_mem c⁻¹ hv
  have hSv : S ⟨v, hvS⟩ = c⁻¹ • P2 ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨u, hu⟩) := by
    rw [← hcurl, ← LinearPMap.map_smul]; rfl
  have he : Φ.coeff hU.measurableSet v = c⁻¹ • Φ.piola hU.measurableSet hUΩ u := by
    rw [_root_.map_smul, Φ.coeff_pull1]
  have hmemD : c⁻¹ • Φ.piola hU.measurableSet hUΩ u ∈
      ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal U).domain :=
    Submodule.smul_mem _ c⁻¹ hp
  obtain ⟨hy, ey⟩ := exists_mem_apply_eq_of_eq hadj.symm ⟨_, hmemD⟩
  have hy' : Φ.coeff hU.measurableSet v ∈ T†.domain := by rw [he]; exact hy
  have hT : T† ⟨Φ.coeff hU.measurableSet v, hy'⟩ =
      c⁻¹ • PJ ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal Ω ⟨u, hu'⟩) := by
    rw [show (⟨Φ.coeff hU.measurableSet v, hy'⟩ : T†.domain) = ⟨_, hy⟩ from Subtype.ext he, ey,
      show (⟨c⁻¹ • Φ.piola hU.measurableSet hUΩ u, hmemD⟩ :
        ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).formalAdj.maximal U).domain) =
        c⁻¹ • ⟨_, hp⟩ from rfl, LinearPMap.map_smul, hdiv]
  have hvK := hsub v hvS hy' (hbound P1 u hc1 h1) (by rw [hSv]; exact hbound P2 _ hc2 h2)
    (by rw [hT]; exact hbound PJ _ hcJ h3)
  refine ⟨v, hvK, ?_⟩
  simp only [v, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

namespace StarDomain

variable {n : ℕ} (D : StarDomain n)

/-- The domain centred at `x₀`: `{v | x₀ + v ∈ Ω}`. -/
def centred : Set (Fin n → ℝ) := {v | D.x₀ + v ∈ D.Ω}

/-- The gauge `g_Ω(v) = inf {t > 0 : x₀ + v / t ∈ Ω}` of `Ω` about `x₀`. -/
def gaugeFun (v : Fin n → ℝ) : ℝ := gauge D.centred v

theorem ball_subset_centred (hne : D.Ω.Nonempty) : Metric.ball 0 D.s₀ ⊆ D.centred := by
  intro v hv
  obtain ⟨y, hy⟩ := hne
  have hz : D.x₀ + v ∈ Metric.ball D.x₀ D.s₀ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa using hv
  exact D.starBall y hy _ hz (left_mem_segment ℝ _ _)

theorem centred_subset_closedBall : D.centred ⊆ Metric.closedBall 0 D.R := by
  intro v hv
  have := D.norm_sub_le _ (subset_closure hv)
  rw [add_sub_cancel_left] at this
  simpa using this

theorem absorbent_centred (hne : D.Ω.Nonempty) : Absorbent ℝ D.centred :=
  (absorbent_ball_zero D.s₀_pos).mono (D.ball_subset_centred hne)

theorem gaugeFun_le (hne : D.Ω.Nonempty) (v : Fin n → ℝ) : D.gaugeFun v ≤ ‖v‖ / D.s₀ := by
  rw [← gauge_ball D.s₀_pos.le v]
  exact gauge_mono (absorbent_ball_zero D.s₀_pos) (D.ball_subset_centred hne) v

theorem le_gaugeFun (hne : D.Ω.Nonempty) (v : Fin n → ℝ) : ‖v‖ / D.R ≤ D.gaugeFun v := by
  rw [← gauge_closedBall D.R_pos.le v]
  exact gauge_mono (D.absorbent_centred hne) D.centred_subset_closedBall v

theorem gaugeFun_le_add (hne : D.Ω.Nonempty) (v w : Fin n → ℝ) :
    D.gaugeFun v ≤ D.gaugeFun w + ‖v - w‖ / D.s₀ := by
  have hs := D.s₀_pos
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨b, hb0, hbt, hwb⟩ := exists_lt_of_gauge_lt (D.absorbent_centred hne)
    (show D.gaugeFun w < D.gaugeFun w + ε / 2 by linarith)
  obtain ⟨p, hp, rfl⟩ := mem_smul_set.1 hwb
  set t := b + ‖v - b • p‖ / D.s₀ + ε / 2
  have hd : 0 < t - b := by
    have : 0 ≤ ‖v - b • p‖ / D.s₀ := by positivity
    simp only [t]; linarith
  have ht : 0 < t := by linarith
  set z : Fin n → ℝ := (t - b)⁻¹ • (v - b • p)
  have hz : D.x₀ + z ∈ Metric.ball D.x₀ D.s₀ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hd.le), inv_mul_lt_iff₀ hd]
    have e : (t - b) * D.s₀ = ‖v - b • p‖ + ε / 2 * D.s₀ := by
      simp only [t]; field_simp; ring
    rw [e]; nlinarith
  have hseg := D.starBall _ hp _ hz
  have hmem : D.x₀ + t⁻¹ • v ∈ D.Ω := by
    refine hseg ⟨1 - b / t, b / t, by
      rw [sub_nonneg, div_le_one ht]; linarith, by positivity, by ring, ?_⟩
    simp only [z, smul_add, smul_smul]
    rw [show (1 - b / t) * (t - b)⁻¹ = t⁻¹ by field_simp]
    module
  have hle : D.gaugeFun v ≤ t := by
    refine gauge_le_of_mem ht.le (mem_smul_set.2 ⟨t⁻¹ • v, hmem, ?_⟩)
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  simp only [t] at hle
  linarith

theorem mem_iff_gaugeFun_lt_one (hne : D.Ω.Nonempty) (x : Fin n → ℝ) :
    x ∈ D.Ω ↔ D.gaugeFun (x - D.x₀) < 1 := by
  constructor
  · intro hx
    have hc : Continuous fun t : ℝ => D.x₀ + t • (x - D.x₀) := by fun_prop
    have hev : ∀ᶠ t in 𝓝 (1 : ℝ), D.x₀ + t • (x - D.x₀) ∈ D.Ω :=
      hc.continuousAt.preimage_mem_nhds (by simpa using D.isOpen.mem_nhds hx)
    obtain ⟨t, htΩ, ht1⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (1 : ℝ) ∈ 𝓝[>] 1)).exists
    have ht0 : 0 < t := lt_trans one_pos ht1
    have hmem : x - D.x₀ ∈ t⁻¹ • D.centred :=
      mem_smul_set.2 ⟨t • (x - D.x₀), htΩ, by rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]⟩
    exact (gauge_le_of_mem (inv_nonneg.2 ht0.le) hmem).trans_lt (inv_lt_one_of_one_lt₀ ht1)
  · intro hx
    obtain ⟨b, hb0, hb1, hmem⟩ := exists_lt_of_gauge_lt (D.absorbent_centred hne) hx
    obtain ⟨p, hp, hpx⟩ := mem_smul_set.1 hmem
    have hseg := D.starBall _ hp D.x₀ (Metric.mem_ball_self D.s₀_pos)
    have : x = (1 - b) • D.x₀ + b • (D.x₀ + p) := by
      rw [smul_add, hpx]; module
    rw [this]
    exact hseg ⟨1 - b, b, by linarith, hb0.le, by ring, rfl⟩

end StarDomain

theorem hasWeberCompactness_empty : HasWeberCompactness (∅ : Set R3) := by
  refine ⟨{0}, isCompact_singleton, fun u _ _ _ _ _ => ?_⟩
  refine PiLp.ext fun j => Lp.ext ?_
  exact (ae_restrict_iff' MeasurableSet.empty).2
    (Eventually.of_forall fun x hx => absurd hx (Set.notMem_empty x))

theorem ball_eq_openCube (x₀ : R3) :
    Metric.ball x₀ 1 = Feec.Models.Cube.Geometry.openCube (x₀ - 1) 2 := by
  ext x
  rw [Metric.mem_ball, dist_pi_lt_iff one_pos, Feec.Models.Cube.Geometry.openCube,
    Set.mem_univ_pi]
  refine forall_congr' fun i => ?_
  rw [Real.dist_eq, abs_lt, mem_Ioo, Pi.sub_apply, Pi.one_apply]
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩

section EigenDense

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

namespace StarDomain

variable (D : StarDomain 3)

theorem isLipGauge (hne : D.Ω.Nonempty) :
    IsLipGauge D.gaugeFun (1 / D.R) (1 / D.s₀) D.s₀⁻¹ where
  a_pos := one_div_pos.2 D.R_pos
  smul t ht v := by rw [gaugeFun, gauge_smul_of_nonneg ht, smul_eq_mul]; rfl
  lower v := by have := D.le_gaugeFun hne v; rwa [one_div_mul_eq_div]
  upper v := by have := D.gaugeFun_le hne v; rwa [one_div_mul_eq_div]
  lip v w := by
    have h1 := D.gaugeFun_le_add hne v w
    have h2 := D.gaugeFun_le_add hne w v
    rw [norm_sub_rev] at h2
    rw [abs_le, inv_mul_eq_div]
    constructor <;> linarith

/-- The radial bi-Lipschitz map from the cube `x₀ + (-1, 1)³` onto `Ω`. -/
def toCube (hne : D.Ω.Nonempty) : BiLipschitz :=
  radialMap D.x₀ (D.isLipGauge hne) isLipGauge_norm

theorem mem_ball_iff (hne : D.Ω.Nonempty) (x : R3) :
    x ∈ Metric.ball D.x₀ 1 ↔ D.toCube hne x ∈ D.Ω := by
  rw [Metric.mem_ball, dist_eq_norm, D.mem_iff_gaugeFun_lt_one hne]
  exact radialMap_mem_iff D.x₀ (D.isLipGauge hne) isLipGauge_norm x

theorem hasWeberCompactness : HasWeberCompactness D.Ω := by
  rcases D.Ω.eq_empty_or_nonempty with h | hne
  · rw [h]; exact hasWeberCompactness_empty
  · have hW := hasWeberCompactness_cube (D.x₀ - 1) two_pos
    rw [← ball_eq_openCube] at hW
    exact hasWeberCompactness_of_biLipschitz (D.toCube hne) Metric.isOpen_ball D.isOpen
      Metric.isBounded_ball D.isBounded (D.mem_ball_iff hne) hW

/-- On every domain star-shaped with respect to a ball, the grad–curl wave group has a dense set of
eigenvectors. -/
theorem eigenDense_gradCurl : (gradCurl ℝ D.isOpen).EigenDense :=
  eigenDense_gradCurl_of_weber D.isOpen D.isBounded D.hasWeberCompactness

end StarDomain

theorem exists_starDomain_of_convex {Ω : Set R3} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : Convex ℝ Ω) (hne : Ω.Nonempty) : ∃ D : StarDomain 3, D.Ω = Ω := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨s₀, hs₀, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  obtain ⟨R, hR⟩ := hb.closure.subset_closedBall x₀
  refine ⟨⟨Ω, hΩ, x₀, s₀, max R 1, hs₀, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun y hy z hz => hc.segment_subset (hball hz) hy, fun y hy => ?_⟩, rfl⟩
  have := hR hy
  rw [Metric.mem_closedBall, dist_eq_norm] at this
  exact this.trans (le_max_left _ _)

theorem hasWeberCompactness_convex {Ω : Set R3} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : Convex ℝ Ω) : HasWeberCompactness Ω := by
  rcases Ω.eq_empty_or_nonempty with h | hne
  · rw [h]; exact hasWeberCompactness_empty
  · obtain ⟨D, rfl⟩ := exists_starDomain_of_convex hΩ hb hc hne
    exact D.hasWeberCompactness

theorem eigenDense_gradCurl_convex {Ω : Set R3} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : Convex ℝ Ω) : (gradCurl ℝ hΩ).EigenDense :=
  eigenDense_gradCurl_of_weber hΩ hb (hasWeberCompactness_convex hΩ hb hc)

theorem isBounded_euclBall (c : R3) (r : ℝ) : Bornology.IsBounded (euclBall c r) := by
  refine (Metric.isBounded_closedBall (x := c) (r := |r|)).subset fun x hx => ?_
  rw [Metric.mem_closedBall, dist_pi_le_iff (abs_nonneg r)]
  intro i
  rw [Real.dist_eq, ← abs_abs r]
  refine sq_le_sq.1 ?_
  have : (x i - c i) ^ 2 ≤ ∑ j, (x j - c j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (x j - c j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hx' : ∑ j, (x j - c j) ^ 2 < r ^ 2 := hx
  rw [sq_abs]
  linarith

theorem convex_euclBall (c : R3) (r : ℝ) : Convex ℝ (euclBall c r) := by
  intro x hx y hy a b ha hb hab
  have hx' : ∑ i, (x i - c i) ^ 2 < r ^ 2 := hx
  have hy' : ∑ i, (y i - c i) ^ 2 < r ^ 2 := hy
  show ∑ i, ((a • x + b • y) i - c i) ^ 2 < r ^ 2
  have hpt : ∀ i, ((a • x + b • y) i - c i) ^ 2 ≤ a * (x i - c i) ^ 2 + b * (y i - c i) ^ 2 :=
    fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : a * x i + b * y i - c i = a * (x i - c i) + b * (y i - c i) := by
        linear_combination (c i) * hab
      rw [this]
      nlinarith [mul_nonneg ha hb, sq_nonneg (x i - c i - (y i - c i))]
  calc ∑ i, ((a • x + b • y) i - c i) ^ 2 ≤ ∑ i, (a * (x i - c i) ^ 2 + b * (y i - c i) ^ 2) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = a * ∑ i, (x i - c i) ^ 2 + b * ∑ i, (y i - c i) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ < r ^ 2 := by
        rcases ha.lt_or_eq with ha' | ha'
        · nlinarith
        · subst ha'; rw [zero_add] at hab; subst hab; linarith

/-- A complete set of eigenvectors on every Euclidean ball. -/
theorem eigenDense_gradCurl_ball (c : R3) (r : ℝ) :
    (gradCurl ℝ (isOpen_euclBall c r)).EigenDense :=
  eigenDense_gradCurl_convex _ (isBounded_euclBall c r) (convex_euclBall c r)

/-- On a ball, `K*` for `K = {0} × L²(TSD) × L²(TSD)` is stationary iff no nonzero `u ∈ L²(TSD)`
with `curl† curl u = ξ² u`, `ξ > 0`, has `curl u ∉ H̊(curl)`. -/
theorem coreSub_le_stationary_ball_iff (c : R3) (r : ℝ) :
    (gradCurl ℝ (isOpen_euclBall c r)).coreSub (tsd (euclBall c r)) (tsd (euclBall c r)) ≤
        (gradCurl ℝ (isOpen_euclBall c r)).stationary ↔
      ¬ ∃ ξ : ℝ, 0 < ξ ∧ ∃ v : L2F ℝ (euclBall c r) Ix, v ≠ 0 ∧ v ∈ tsd (euclBall c r) ∧
        (gradCurl ℝ (isOpen_euclBall c r)).IsEigenfield ξ v ∧
        ∀ h1 : v ∈ (gradCurl ℝ (isOpen_euclBall c r)).d₁.domain,
          ((gradCurl ℝ (isOpen_euclBall c r)).d₁ ⟨v, h1⟩ : L2F ℝ (euclBall c r) Ix) ∉
            ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal (euclBall c r)).domain := by
  rw [← not_coreSub_le_stationary_iff (isOpen_euclBall c r) (isBounded_euclBall c r)
    (eigenDense_gradCurl_ball c r), not_not]

end EigenDense

end Feec.Models.StarShaped
