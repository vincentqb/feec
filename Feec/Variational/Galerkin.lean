module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Feec.Variational.InfSup

/-!
# Petrov–Galerkin approximation: stability and quasi-optimality

Under the discrete inf-sup condition, Galerkin orthogonality gives discrete stability and the
quasi-optimality `‖u - uₕ‖ ≤ (1 + ‖B‖/γ) dist(u, K)`, with the constant `‖B‖/γ` in inner product
spaces.

## Main results

* `InfSup.norm_sub_le_infDist`: quasi-optimality.
* `InfSup.norm_sub_le_infDist_sharp`: the constant `‖B‖/γ`.
* `existsUnique_galerkin`: unique solvability on finite-dimensional spaces of equal dimension.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [D. N. Arnold, *Lecture notes on Numerical Analysis of Partial Differential Equations*][ArnoldNotes2011]
* [J. Xu, L. Zikatanov, *Some observations on Babuška and Brezzi theories*][XuZikatanov2003]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Module

@[expose] public noncomputable section

namespace Feec.Variational

variable {𝕜 X Y : Type*} [RCLike 𝕜] {σ : 𝕜 →+* 𝕜} [RingHomIsometric σ]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

section Normed

variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {B : X →L[𝕜] Y →SL[σ] 𝕜} {K : Submodule 𝕜 X} {L : Submodule 𝕜 Y} {γ : ℝ}

theorem norm_restrict_le : ‖restrict B K L‖ ≤ ‖B‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x =>
    norm_restrict_apply_le_of_eq K L x fun _ _ => rfl

namespace InfSup

theorem norm_le_of_restrict_eq (h : InfSup (restrict B K L) γ) {p : X} (hp : p ∈ K) {z : X}
    (hpz : ∀ v ∈ L, B p v = B z v) : ‖p‖ ≤ ‖B‖ / γ * ‖z‖ := by
  have h1 := (h.le ⟨p, hp⟩).trans (norm_restrict_apply_le_of_eq K L ⟨p, hp⟩ hpz)
  rw [div_mul_eq_mul_div, le_div_iff₀ h.pos, mul_comm]
  exact h1

theorem le_opNorm_of_ne_bot (h : InfSup (restrict B K L) γ) (hK : K ≠ ⊥) : γ ≤ ‖B‖ := by
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  have : Nontrivial K := ⟨⟨⟨k, hk⟩, 0, fun h0 => hk0 (congrArg Subtype.val h0)⟩⟩
  exact h.le_opNorm.trans norm_restrict_le

theorem norm_sub_le_of_orthogonal (h : InfSup (restrict B K L) γ) {u uh : X} (huh : uh ∈ K)
    (horth : ∀ v ∈ L, B (u - uh) v = 0) {w : X} (hw : w ∈ K) :
    ‖u - uh‖ ≤ (1 + ‖B‖ / γ) * ‖u - w‖ := by
  have h1 : ‖w - uh‖ ≤ ‖B‖ / γ * ‖w - u‖ :=
    h.norm_le_of_restrict_eq (K.sub_mem hw huh) fun v hv => by
      have : w - uh = (w - u) + (u - uh) := by abel
      rw [this, map_add, add_apply, horth v hv, add_zero]
  rw [norm_sub_rev w u] at h1
  calc ‖u - uh‖ = ‖(u - w) + (w - uh)‖ := by congr 1; abel
    _ ≤ ‖u - w‖ + ‖w - uh‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- **Quasi-optimality**, best-approximation form: `‖u - uₕ‖ ≤ (1 + ‖B‖/γ) dist(u, K)`.
[QuennevilleBelair2015], Thm 4.10 (adapted) -/
theorem norm_sub_le_infDist (h : InfSup (restrict B K L) γ) {u uh : X} (huh : uh ∈ K)
    (horth : ∀ v ∈ L, B (u - uh) v = 0) :
    ‖u - uh‖ ≤ (1 + ‖B‖ / γ) * Metric.infDist u K := by
  have hC : 0 < 1 + ‖B‖ / γ := by have := h.pos; positivity
  rw [← div_le_iff₀' hC]
  refine (Metric.le_infDist ⟨0, K.zero_mem⟩).2 fun w hw => ?_
  rw [div_le_iff₀' hC, dist_eq_norm]
  exact h.norm_sub_le_of_orthogonal huh horth hw

end InfSup

end Normed

section Inner

variable [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  {B : X →L[𝕜] Y →SL[σ] 𝕜} {K : Submodule 𝕜 X} {L : Submodule 𝕜 Y} {γ : ℝ}

theorem norm_smul_add_smul_eq (a b : X) :
    ‖((‖b‖ ^ 2 : ℝ) : 𝕜) • a + ((‖a‖ ^ 2 : ℝ) : 𝕜) • b‖ = ‖a‖ * ‖b‖ * ‖a + b‖ := by
  have hsq : ‖((‖b‖ ^ 2 : ℝ) : 𝕜) • a + ((‖a‖ ^ 2 : ℝ) : 𝕜) • b‖ ^ 2
      = (‖a‖ * ‖b‖ * ‖a + b‖) ^ 2 := by
    rw [@norm_add_sq 𝕜, mul_pow, @norm_add_sq 𝕜 _ _ _ _ a b, inner_smul_real_left, inner_smul_real_right,
      norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    simp only [RCLike.smul_re]
    ring
  have h1 := norm_nonneg (((‖b‖ ^ 2 : ℝ) : 𝕜) • a + ((‖a‖ ^ 2 : ℝ) : 𝕜) • b)
  have h2 : 0 ≤ ‖a‖ * ‖b‖ * ‖a + b‖ := by positivity
  nlinarith [sq_nonneg (‖((‖b‖ ^ 2 : ℝ) : 𝕜) • a + ((‖a‖ ^ 2 : ℝ) : 𝕜) • b‖ - ‖a‖ * ‖b‖ * ‖a + b‖),
    sq_nonneg (‖((‖b‖ ^ 2 : ℝ) : 𝕜) • a + ((‖a‖ ^ 2 : ℝ) : 𝕜) • b‖ + ‖a‖ * ‖b‖ * ‖a + b‖)]

namespace InfSup

theorem norm_sub_le_of_orthogonal_sharp (h : InfSup (restrict B K L) γ) (hK : K ≠ ⊥)
    {u uh : X} (huh : uh ∈ K) (horth : ∀ v ∈ L, B (u - uh) v = 0) {w : X} (hw : w ∈ K) :
    ‖u - uh‖ ≤ ‖B‖ / γ * ‖u - w‖ := by
  have hC : 1 ≤ ‖B‖ / γ := by
    rw [le_div_iff₀ h.pos, one_mul]; exact h.le_opNorm_of_ne_bot hK
  set a := uh - w
  set b := u - uh
  have ha : a ∈ K := K.sub_mem huh hw
  have hab : u - w = a + b := by simp only [a, b]; abel
  rw [hab]
  rcases eq_or_ne b 0 with hb | hb
  · rw [hb, norm_zero]; have := h.pos; positivity
  rcases eq_or_ne a 0 with ha0 | ha0
  · rw [ha0, zero_add]; exact le_mul_of_one_le_left (norm_nonneg _) hC
  have hpa : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hpb : 0 < ‖b‖ := norm_pos_iff.2 hb
  have key := h.norm_le_of_restrict_eq (p := ((‖b‖ ^ 2 : ℝ) : 𝕜) • a) (K.smul_mem _ ha)
    (z := ((‖b‖ ^ 2 : ℝ) : 𝕜) • a + ((‖a‖ ^ 2 : ℝ) : 𝕜) • b) fun v hv => by
      rw [map_add, add_apply, map_smul (B : X →L[𝕜] Y →SL[σ] 𝕜) _ b,
        smul_apply, horth v hv, smul_zero, add_zero]
  rw [norm_smul_add_smul_eq, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at key
  have : ‖b‖ * (‖b‖ * ‖a‖) ≤ (‖B‖ / γ * ‖a + b‖) * (‖b‖ * ‖a‖) := by nlinarith
  exact le_of_mul_le_mul_right this (by positivity)

/-- **Sharp quasi-optimality**, best-approximation form: `‖u - uₕ‖ ≤ (‖B‖/γ) dist(u, K)`.
[QuennevilleBelair2015], Thm 4.10 (adapted); [XuZikatanov2003] -/
theorem norm_sub_le_infDist_sharp (h : InfSup (restrict B K L) γ) (hK : K ≠ ⊥) {u uh : X}
    (huh : uh ∈ K) (horth : ∀ v ∈ L, B (u - uh) v = 0) :
    ‖u - uh‖ ≤ ‖B‖ / γ * Metric.infDist u K := by
  have hC : 0 < ‖B‖ / γ := div_pos (h.pos.trans_le (h.le_opNorm_of_ne_bot hK)) h.pos
  rw [← div_le_iff₀' hC]
  refine (Metric.le_infDist ⟨0, K.zero_mem⟩).2 fun w hw => ?_
  rw [div_le_iff₀' hC, dist_eq_norm]
  exact h.norm_sub_le_of_orthogonal_sharp hK huh horth hw

end InfSup

end Inner

section Existence

variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {K : Submodule 𝕜 X} {L : Submodule 𝕜 Y} {γ : ℝ}

/-- **Discrete well-posedness** on finite-dimensional `K`, `L` of equal dimension under the
discrete inf-sup condition. [QuennevilleBelair2015], Thm 4.10; [ArnoldNotes2011] -/
theorem existsUnique_galerkin [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : finrank 𝕜 K = finrank 𝕜 L) {B : X →L[𝕜] Y →L[𝕜] 𝕜}
    (h : InfSup (restrict B K L) γ) (F : Y →L[𝕜] 𝕜) :
    ∃! uh, uh ∈ K ∧ ∀ v ∈ L, B uh v = F v := by
  let Φ : K →ₗ[𝕜] Module.Dual 𝕜 L :=
    { toFun := fun w => (B (w : X)).toLinearMap.comp L.subtype
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by ext v; simp }
  have hΦ : ∀ (w : K) (v : L), Φ w v = B w v := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    refine h.injective (ContinuousLinearMap.ext fun v => ?_)
    rw [restrict_apply, restrict_apply, ← hΦ, ← hΦ, hxy]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hdim.trans Subspace.dual_finrank_eq.symm)).1 hinj
  obtain ⟨w, hw⟩ := hsurj (F.toLinearMap.comp L.subtype)
  refine ⟨w, ⟨w.2, fun v hv => ?_⟩, ?_⟩
  · rw [← hΦ w ⟨v, hv⟩, hw]; rfl
  · rintro y ⟨hy, hyF⟩
    have : Φ ⟨y, hy⟩ = Φ w := by
      ext v
      rw [hΦ, hΦ, hyF v v.2, ← hΦ w v, hw]; rfl
    exact congrArg Subtype.val (hinj this)

end Existence

end Feec.Variational
