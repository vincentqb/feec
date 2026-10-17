module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Feec.Ch4.BoxThesis

/-!
# Exponentials of skew operators with `A³ = -ω² A`, and the wave symbol of the box

Auxiliary file for the box model of `Feec.Ch4.Box`. On the mode `k` the periodic Hodge wave group
acts by `exp(t W_k)` with `W_k³ = -|ξ_k|² W_k` (`waveSymK_cube`), so
`exp(t W_k) u = u₀ + cos(|ξ_k| t) u₁ + (sin(|ξ_k| t)/|ξ_k|) W_k u` (`exp_smul_apply_eq`).

The forward-invariance results that used to live here (forward invariance of
`K = {0} × S1 × S2` forces stationarity) are now consequences of the spectral mechanism
(`Feec.Models.Cube.Parity.forward_torus_iff`: pure point spectrum of the torus wave group and the
mean ergodic theorem, `Feec.C0Group.IsIsometric.mem_invariantCore_of_forward_invariant`); the
old statements `Feec.Box.forward_iff_mem_Kmax`, `Feec.Box.forward_boxTSD_iff` and
`Feec.Box.thesisBox_forward_iff` are kept as shims in `Feec.Ch4.BoxIdent`. The Cesàro-mean
argument is deleted.

## Main results

* `exp_smul_apply_eq`: `exp(tA) u = u₀ + cos(ωt) u₁ + (sin(ωt)/ω) A u` if `A³ = -ω² A`;
  `norm_exp_smul_apply_of_skew`: `exp(tA)` is an isometry for skew `A`.
* `waveSymK_cube`: `W_k³ = -|ξ_k|² W_k`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
* [Pazy1983], §1.10 (groups and generators)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory Set Filter Topology NormedSpace

namespace Feec.Box

/-! ## Exponentials of skew operators with `A³ = -ω² A` -/

section Skew

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `exp(tA)` is an isometry for skew `A`. -/
theorem norm_exp_smul_apply_of_skew (A : E →L[ℝ] E) (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫)
    (t : ℝ) (u : E) : ‖exp (t • A) u‖ = ‖u‖ := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ⟪exp (s • A) u, exp (s • A) u⟫) 0 s := by
    intro s
    have h := (hasDerivAt_exp_smul_apply A u s).inner ℝ (hasDerivAt_exp_smul_apply A u s)
    convert h using 1
    linarith [hA (exp (s • A) u) (exp (s • A) u),
      real_inner_comm (A (exp (s • A) u)) (exp (s • A) u)]
  have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simp only [zero_smul, exp_zero, ] at this
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

omit [CompleteSpace E] in
/-- A skew `A` with `A⁴ = -ω² A²` satisfies `A³ = -ω² A`. -/
theorem cube_of_four_of_skew (A : E →L[ℝ] E) (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) {ω : ℝ}
    (h4 : ∀ x, A (A (A (A x))) = -(ω ^ 2) • A (A x)) (x : E) :
    A (A (A x)) = -(ω ^ 2) • A x := by
  set y := A (A (A x)) + (ω ^ 2) • A x
  have hy : y = A (A (A x) + (ω ^ 2) • x) := by simp [y]
  have hAy : A y = 0 := by
    simp only [y, _root_.map_add, _root_.map_smul, h4, neg_smul, neg_add_cancel]
  have h0 : ⟪y, y⟫ = 0 := by
    have e : ⟪y, y⟫ = ⟪A (A (A x) + (ω ^ 2) • x), y⟫ := by rw [← hy]
    rw [e, hA, hAy, inner_zero_right, neg_zero]
  rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at h0
  rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add]
  exact h0

/-- **The flow of `A` with `A³ = -ω² A`, `ω ≠ 0`**:
`exp(tA) u = u₀ + cos(ωt) u₁ + (sin(ωt)/ω) A u` with `u₁ = -ω⁻² A² u`, `u₀ = u - u₁`. -/
theorem exp_smul_apply_eq (A : E →L[ℝ] E) {ω : ℝ} (hω : ω ≠ 0)
    (h3 : ∀ x, A (A (A x)) = -(ω ^ 2) • A x) (t : ℝ) (u : E) :
    exp (t • A) u = (u + (ω ^ 2)⁻¹ • A (A u)) + Real.cos (ω * t) • (-(ω ^ 2)⁻¹ • A (A u)) +
      (Real.sin (ω * t) / ω) • A u := by
  set φ : ℝ → E := fun s => (u + (ω ^ 2)⁻¹ • A (A u)) +
    Real.cos (ω * s) • (-(ω ^ 2)⁻¹ • A (A u)) + (Real.sin (ω * s) / ω) • A u with hφ
  have hφd : ∀ s, HasDerivAt φ (A (φ s)) s := by
    intro s
    have hc : HasDerivAt (fun s => Real.cos (ω * s)) (-Real.sin (ω * s) * ω) s := by
      have := ((hasDerivAt_id' s).const_mul ω).cos
      convert this using 1; ring
    have hs : HasDerivAt (fun s => Real.sin (ω * s) / ω) (Real.cos (ω * s) * ω / ω) s := by
      have := (((hasDerivAt_id' s).const_mul ω).sin).div_const ω
      convert this using 1; ring
    have h := ((hasDerivAt_const s (u + (ω ^ 2)⁻¹ • A (A u))).add
      (hc.smul_const (-(ω ^ 2)⁻¹ • A (A u)))).add (hs.smul_const (A u))
    convert h using 1
    simp only [hφ, _root_.map_add, _root_.map_smul, h3, zero_add]
    have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω
    match_scalars <;> field_simp
    ring
  set ψ : ℝ → E := fun s => exp ((-s) • A) (φ s) with hψ
  have hψd : ∀ s, HasDerivAt ψ 0 s := by
    intro s
    have he : (fun s : ℝ => exp ((-s) • A)) = fun s => exp (s • (-A)) := by
      funext s; rw [neg_smul, smul_neg]
    have h1 : HasDerivAt (fun s : ℝ => exp ((-s) • A)) ((-A) * exp (s • (-A))) s := by
      rw [he]; exact hasDerivAt_exp_smul_const' (-A) s
    have h := h1.clm_apply (hφd s)
    convert h using 1
    have hc : Commute A (exp (s • (-A))) := ((Commute.refl A).neg_right.smul_right s).exp_right
    have hc' : exp (s • (-A)) (A (φ s)) = A (exp (s • (-A)) (φ s)) := by
      have := congrArg (fun T : E →L[ℝ] E => T (φ s)) hc.eq
      simpa using this.symm
    rw [show (-s) • A = s • (-A) by rw [neg_smul, smul_neg]]
    change (0 : E) = -(A (exp (s • (-A)) (φ s))) + exp (s • (-A)) (A (φ s))
    rw [hc', neg_add_cancel]
  have hψc := is_const_of_deriv_eq_zero (fun s => (hψd s).differentiableAt)
    (fun s => (hψd s).deriv) t 0
  have h0 : ψ 0 = u := by
    simp only [hψ, hφ, neg_zero, zero_smul, exp_zero, mul_zero,
      Real.cos_zero, Real.sin_zero, zero_div, one_smul]
    simp
  rw [h0] at hψc
  have := congrArg (fun v => (exp (t • A) : E →L[ℝ] E) v) hψc
  rw [← this]
  change (exp (t • A) * exp ((-t) • A)) (φ t) = φ t
  rw [exp_smul_mul_exp_neg_smul]
  rfl

end Skew

/-! ## The wave symbol of the box -/

section Forward

open Feec.Torus Feec.Constraints HilbertComplex2

/-- `W_k³ = -|ξ_k|² W_k`. -/
theorem waveSymK_cube (k : Z3) (x : Fib) :
    waveSymK k (waveSymK k (waveSymK k x)) = -(‖freq k‖ ^ 2) • waveSymK k x :=
  cube_of_four_of_skew (waveSymK k) (waveSym_skew (freq k)) (waveSym_four (freq k)) x

end Forward

end Feec.Box
