module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.RCLike.Basic

/-!
# The inf-sup condition

For a bounded form `B : X →L[𝕜] Y →SL[σ] 𝕜` between normed spaces over `𝕜 = ℝ` or `ℂ`
(`σ = RingHom.id 𝕜` for bilinear forms, `σ = starRingEnd 𝕜` for sesquilinear ones), the
inf-sup condition with constant `γ > 0` is `γ ‖x‖ ≤ ‖B x‖ = sup_{y ≠ 0} |B x y| / ‖y‖`.

## Main definitions

* `Feec.Variational.InfSup B γ`: the inf-sup condition.
* `Feec.Variational.SeparatingRight B`: `B x y = 0` for all `x` forces `y = 0` (the "dense range"
  condition of Babuška–Nečas, on the second slot).
* `Feec.Variational.restrict B K L`: the form on a trial subspace `K` and a test subspace `L`
  (the Petrov–Galerkin form).

## Main results

* `InfSup.injective`, `InfSup.norm_le_of_apply_eq`: uniqueness and the stability bound
  `‖x‖ ≤ γ⁻¹ ‖B x‖`.
* `InfSup.le_opNorm`: `γ ≤ ‖B‖` on a nontrivial space.
* `InfSup.of_forall_exists`: the inf-sup condition from test elements.
* `InfSup.of_testMap`, `InfSup.restrict_of_testMap`: a test map `T` with `‖T x‖ ≤ M ‖x‖` and
  `c ‖x‖² ≤ re B x (T x)` gives the inf-sup constant `c / M`, on every pair of subspaces
  `K, L` with `T K ⊆ L`. This is the proof pattern of the inf-sup condition for the Hodge wave
  form and for the mixed Hodge Laplacian, at the continuous and at the discrete level.

## References

* [QuennevilleBelair2015], §4.5 (inf-sup condition), Prop 4.13 (inf-sup by a test function)
* [Babuska1971]; [BoffiBrezziFortin2013], Ch. 4; [AFW2010], §3.2; [Arnold2018], Ch. 4
-/

@[expose] public noncomputable section

namespace Feec.Variational

variable {𝕜 X Y : Type*} [RCLike 𝕜] {σ : 𝕜 →+* 𝕜} [RingHomIsometric σ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The **inf-sup condition** with constant `γ > 0`: `γ ‖x‖ ≤ ‖B x‖` for every `x`, where
`‖B x‖ = sup_{y ≠ 0} |B x y| / ‖y‖`. Thesis: §4.5 -/
structure InfSup (B : X →L[𝕜] Y →SL[σ] 𝕜) (γ : ℝ) : Prop where
  pos : 0 < γ
  le : ∀ x, γ * ‖x‖ ≤ ‖B x‖

/-- The **separation condition** on the second slot: `B x y = 0` for all `x` forces `y = 0`
(the "dense range" condition of Babuška–Nečas). Thesis: §4.5 -/
def SeparatingRight (B : X →L[𝕜] Y →SL[σ] 𝕜) : Prop := ∀ y, (∀ x, B x y = 0) → y = 0

/-- The restriction of `B` to a trial subspace `K` and a test subspace `L`. -/
def restrict (B : X →L[𝕜] Y →SL[σ] 𝕜) (K : Submodule 𝕜 X) (L : Submodule 𝕜 Y) :
    K →L[𝕜] L →SL[σ] 𝕜 :=
  B.bilinearComp K.subtypeL L.subtypeL

@[simp] theorem restrict_apply (B : X →L[𝕜] Y →SL[σ] 𝕜) (K : Submodule 𝕜 X)
    (L : Submodule 𝕜 Y) (x : K) (y : L) : restrict B K L x y = B x y := rfl

variable {B : X →L[𝕜] Y →SL[σ] 𝕜} {γ : ℝ}

/-- `‖B|_{K×L} x‖ ≤ ‖B‖ ‖z‖` as soon as `B x = B z` on the test space. -/
theorem norm_restrict_apply_le_of_eq (K : Submodule 𝕜 X) (L : Submodule 𝕜 Y) (x : K) {z : X}
    (h : ∀ v ∈ L, B x v = B z v) : ‖restrict B K L x‖ ≤ ‖B‖ * ‖z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [restrict_apply, h v v.2]
  exact B.le_opNorm₂ z v

/-- `‖B|_{K×L} x‖ ≤ ‖B‖ ‖x‖`. -/
theorem norm_restrict_apply_le (K : Submodule 𝕜 X) (L : Submodule 𝕜 Y) (x : K) :
    ‖restrict B K L x‖ ≤ ‖B‖ * ‖(x : X)‖ :=
  norm_restrict_apply_le_of_eq K L x fun _ _ => rfl

namespace InfSup

omit [RingHomIsometric σ] in
theorem mono (h : InfSup B γ) {γ' : ℝ} (hγ' : 0 < γ') (hle : γ' ≤ γ) : InfSup B γ' :=
  ⟨hγ', fun x => (mul_le_mul_of_nonneg_right hle (norm_nonneg x)).trans (h.le x)⟩

omit [RingHomIsometric σ] in
/-- Stability: `‖x‖ ≤ γ⁻¹ ‖f‖` whenever `B x = f`. -/
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

/-- On a nontrivial space, `γ ≤ ‖B‖`. -/
theorem le_opNorm [Nontrivial X] (h : InfSup B γ) : γ ≤ ‖B‖ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  exact le_of_mul_le_mul_right ((h.le x).trans (B.le_opNorm x)) hx'

/-- The inf-sup condition from test elements: if every `x` has a `y` with
`γ ‖x‖ ‖y‖ ≤ |B x y|`, then `InfSup B γ`. -/
theorem of_forall_exists (hγ : 0 < γ) (h : ∀ x, ∃ y, γ * ‖x‖ * ‖y‖ ≤ ‖B x y‖ ∧ (y = 0 → x = 0)) :
    InfSup B γ := by
  refine ⟨hγ, fun x => ?_⟩
  obtain ⟨y, hy, hy0⟩ := h x
  by_cases hy' : y = 0
  · rw [hy0 hy', norm_zero, mul_zero]; exact norm_nonneg _
  · have : 0 < ‖y‖ := norm_pos_iff.2 hy'
    exact le_of_mul_le_mul_right (hy.trans ((B x).le_opNorm y)) this

/-- The inf-sup condition in the normalized "attained" form
`∀ x, ∃ y, ‖y‖ ≤ 1 ∧ γ ‖x‖ ≤ |B x y|`. -/
theorem of_forall_exists_norm_le_one (hγ : 0 < γ)
    (h : ∀ x, ∃ y, ‖y‖ ≤ 1 ∧ γ * ‖x‖ ≤ ‖B x y‖) : InfSup B γ := by
  refine ⟨hγ, fun x => ?_⟩
  obtain ⟨y, hy1, hy⟩ := h x
  calc γ * ‖x‖ ≤ ‖B x y‖ := hy
    _ ≤ ‖B x‖ * ‖y‖ := (B x).le_opNorm y
    _ ≤ ‖B x‖ * 1 := by gcongr
    _ = ‖B x‖ := mul_one _

/-- **Inf-sup by a test map.** If `T` satisfies `‖T x‖ ≤ M ‖x‖` and `c ‖x‖² ≤ re B x (T x)`,
then `B` satisfies the inf-sup condition with constant `c / M`. `T` need not be linear.
Thesis: Prop 4.13 -/
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

/-- **Inf-sup by a test map on subspaces.** If `T` maps the trial space `K` into the test
space `L`, `‖T x‖ ≤ M ‖x‖` and `c ‖x‖² ≤ re B x (T x)` on `K`, then the restriction of `B` to
`K × L` satisfies the inf-sup condition with constant `c / M`. With `K = L = V` this is the
continuous inf-sup condition, with `K = L = Vₕ` a subcomplex its discrete counterpart with the
same constant. Thesis: Prop 4.13 -/
theorem restrict_of_testMap (K : Submodule 𝕜 X) (L : Submodule 𝕜 Y) (T : X → Y)
    (hTK : ∀ x ∈ K, T x ∈ L) {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hTM : ∀ x ∈ K, ‖T x‖ ≤ M * ‖x‖) (hT : ∀ x ∈ K, c * ‖x‖ ^ 2 ≤ RCLike.re (B x (T x))) :
    InfSup (restrict B K L) (c / M) :=
  of_testMap (fun x : K => (⟨T x, hTK x x.2⟩ : L)) hc hM (fun x => hTM x x.2)
    fun x => hT x x.2

end InfSup

end Feec.Variational
