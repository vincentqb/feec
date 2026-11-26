module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.RCLike.Basic

/-!
# The inf-sup condition

The inf-sup condition `γ ‖x‖ ≤ ‖B x‖` of a bounded bilinear or sesquilinear form `B` between normed
spaces over `𝕜 = ℝ` or `ℂ`, its restriction to trial and test subspaces, and its proof by a test
map.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [D. N. Arnold, *Lecture notes on Numerical Analysis of Partial Differential Equations*][ArnoldNotes2011]

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Variational

variable {𝕜 X Y : Type*} [RCLike 𝕜] {σ : 𝕜 →+* 𝕜} [RingHomIsometric σ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The **inf-sup condition** `γ ‖x‖ ≤ ‖B x‖` with constant `γ > 0`. [QuennevilleBelair2015], §4.5;
[ArnoldNotes2011] -/
structure InfSup (B : X →L[𝕜] Y →SL[σ] 𝕜) (γ : ℝ) : Prop where
  pos : 0 < γ
  le : ∀ x, γ * ‖x‖ ≤ ‖B x‖

/-- `B x y = 0` for all `x` forces `y = 0`. [QuennevilleBelair2015], §4.5; [ArnoldNotes2011] -/
def SeparatingRight (B : X →L[𝕜] Y →SL[σ] 𝕜) : Prop := ∀ y, (∀ x, B x y = 0) → y = 0

/-- The restriction of `B` to a trial subspace `K` and a test subspace `L`. -/
def restrict (B : X →L[𝕜] Y →SL[σ] 𝕜) (K : Submodule 𝕜 X) (L : Submodule 𝕜 Y) :
    K →L[𝕜] L →SL[σ] 𝕜 :=
  B.bilinearComp K.subtypeL L.subtypeL

@[simp] theorem restrict_apply (B : X →L[𝕜] Y →SL[σ] 𝕜) (K : Submodule 𝕜 X)
    (L : Submodule 𝕜 Y) (x : K) (y : L) : restrict B K L x y = B x y := rfl

variable {B : X →L[𝕜] Y →SL[σ] 𝕜} {γ : ℝ}

theorem norm_restrict_apply_le_of_eq (K : Submodule 𝕜 X) (L : Submodule 𝕜 Y) (x : K) {z : X}
    (h : ∀ v ∈ L, B x v = B z v) : ‖restrict B K L x‖ ≤ ‖B‖ * ‖z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [restrict_apply, h v v.2]
  exact B.le_opNorm₂ z v

namespace InfSup

omit [RingHomIsometric σ] in
theorem mono (h : InfSup B γ) {γ' : ℝ} (hγ' : 0 < γ') (hle : γ' ≤ γ) : InfSup B γ' :=
  ⟨hγ', fun x => (mul_le_mul_of_nonneg_right hle (norm_nonneg x)).trans (h.le x)⟩

omit [RingHomIsometric σ] in
theorem norm_le_of_apply_eq (h : InfSup B γ) {x : X} {f : Y →SL[σ] 𝕜} (hx : B x = f) :
    ‖x‖ ≤ γ⁻¹ * ‖f‖ := by
  rw [le_inv_mul_iff₀ h.pos, ← hx]; exact h.le x

omit [RingHomIsometric σ] in
theorem norm_le (h : InfSup B γ) (x : X) : ‖x‖ ≤ γ⁻¹ * ‖B x‖ := h.norm_le_of_apply_eq rfl

theorem eq_zero_of_apply_eq_zero (h : InfSup B γ) {x : X} (hx : B x = 0) : x = 0 := by
  have := h.norm_le_of_apply_eq hx
  rw [norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

theorem injective (h : InfSup B γ) : Function.Injective B := fun x x' hxx' =>
  sub_eq_zero.1 (h.eq_zero_of_apply_eq_zero (by rw [map_sub, hxx', sub_self]))

theorem le_opNorm [Nontrivial X] (h : InfSup B γ) : γ ≤ ‖B‖ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  exact le_of_mul_le_mul_right ((h.le x).trans (B.le_opNorm x)) hx'

theorem of_forall_exists_norm_le_one (hγ : 0 < γ)
    (h : ∀ x, ∃ y, ‖y‖ ≤ 1 ∧ γ * ‖x‖ ≤ ‖B x y‖) : InfSup B γ := by
  refine ⟨hγ, fun x => ?_⟩
  obtain ⟨y, hy1, hy⟩ := h x
  calc γ * ‖x‖ ≤ ‖B x y‖ := hy
    _ ≤ ‖B x‖ * ‖y‖ := (B x).le_opNorm y
    _ ≤ ‖B x‖ * 1 := by gcongr
    _ = ‖B x‖ := mul_one _

theorem exists_norm_le_mul_le (h : InfSup B γ) (x : X) {t : ℝ} (ht : 0 ≤ t) :
    ∃ y : Y, ‖y‖ ≤ t ∧ γ / 2 * ‖x‖ * t ≤ ‖B x y‖ := by
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · exact ⟨0, by rwa [norm_zero], by rw [← hx]; simp⟩
  · have hlt : γ / 2 * ‖x‖ < ‖B x‖ :=
      (by nlinarith [h.pos] : γ / 2 * ‖x‖ < γ * ‖x‖).trans_le (h.le x)
    obtain ⟨z, hz1, hz⟩ := (B x).exists_lt_apply_of_lt_opNorm hlt
    refine ⟨(t : 𝕜) • z, ?_, ?_⟩
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg ht]
      nlinarith [norm_nonneg z]
    · rw [ContinuousLinearMap.map_smulₛₗ, norm_smul, RingHomIsometric.norm_map, RCLike.norm_ofReal,
        abs_of_nonneg ht]
      nlinarith

/-- **Inf-sup by a test map**: `‖T x‖ ≤ M ‖x‖` and `c ‖x‖² ≤ re B x (T x)` give the inf-sup
constant `c / M`. [QuennevilleBelair2015], Prop 4.13 -/
theorem of_testMap (T : X → Y) {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hTM : ∀ x, ‖T x‖ ≤ M * ‖x‖) (hT : ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re (B x (T x))) :
    InfSup B (c / M) := by
  refine ⟨div_pos hc hM, fun x => ?_⟩
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · rw [← hx, mul_zero]; exact norm_nonneg _
  have h1 : c * ‖x‖ ^ 2 ≤ ‖B x‖ * (M * ‖x‖) :=
    calc c * ‖x‖ ^ 2 ≤ RCLike.re (B x (T x)) := hT x
      _ ≤ ‖B x (T x)‖ := RCLike.re_le_norm _
      _ ≤ ‖B x‖ * ‖T x‖ := (B x).le_opNorm _
      _ ≤ ‖B x‖ * (M * ‖x‖) := by gcongr; exact hTM x
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  nlinarith

/-- **Inf-sup by a test map on subspaces**, for `T` mapping the trial space `K` into the test
space `L`. [QuennevilleBelair2015], Prop 4.13 -/
theorem restrict_of_testMap (K : Submodule 𝕜 X) (L : Submodule 𝕜 Y) (T : X → Y)
    (hTK : ∀ x ∈ K, T x ∈ L) {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hTM : ∀ x ∈ K, ‖T x‖ ≤ M * ‖x‖) (hT : ∀ x ∈ K, c * ‖x‖ ^ 2 ≤ RCLike.re (B x (T x))) :
    InfSup (restrict B K L) (c / M) :=
  of_testMap (fun x : K => (⟨T x, hTK x x.2⟩ : L)) hc hM (fun x => hTM x x.2)
    fun x => hT x x.2

end InfSup

end Feec.Variational
