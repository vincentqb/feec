module

public import Feec.Operator.Resolvent
public import Feec.ForMathlib.LinearPMap.Reducing

/-!
# Crank–Nicolson as a Cayley transform

For the evolution `u' = A u` with `A : E →ₗ.[𝕜] E` on a Hilbert space and half time step
`s = Δt / 2`, a Crank–Nicolson step `u ↦ u'` is `u' - u = s A (u' + u)` with `u' + u ∈ D(A)`
(`IsCNStep`). It is given by the Cayley transform
`cayley A s = (1 + s A)(1 - s A)⁻¹ = 2 s⁻¹ R(s⁻¹) - 1`, `R(z) = (z - A)⁻¹`.

## Main results

* `isCNStep_cayley`: the Cayley transform performs a CN step whenever `R(s⁻¹)` exists, e.g. for
  every `s ≠ 0` if `A` is skew-adjoint (`IsSkewAdjoint.isCNStep_cayley`), and for `s > 0` if `A`
  is m-dissipative.
* `IsCNStep.unique`: CN steps are unique for dissipative `A` and `s ≥ 0`, and for skew-symmetric
  `A` and every `s` (`IsCNStep.unique_of_isSkewSymmetric`).
* `IsCNStep.norm_eq`, `IsCNStep.norm_le`: exact energy conservation for skew-symmetric `A`,
  contraction for dissipative `A`; `norm_cayley_apply`, `norm_cayley_pow_apply`: the Cayley
  transform of a skew-adjoint operator is an isometry, and so are the CN iterates.
* `IsCNStep.mem_of_isReducing`: **discrete constraint propagation**: a CN step from a point of a
  reducing subspace `K` stays in `K` (dissipative `A`, `s ≥ 0`), hence so does every CN iterate.

These hold in any Hilbert space, so they cover finite element spaces (bounded `A`) and the
continuous problem (unbounded skew-adjoint `A`) at once.

## References

* [QuennevilleBelair2015], Ch. 7 (Crank–Nicolson for the EB system), Prop 4.18 (constraint
  propagation, here at the discrete level)
* [Arnold2018], Ch. 8 (time discretization of Hodge evolution problems)
-/

open scoped InnerProductSpace
open Feec.Operator

@[expose] public noncomputable section

namespace Feec.TimeStepping

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {s : ℝ} {u u' : E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- `u'` is a **Crank–Nicolson step** from `u` for `u' = A u` with half time step `s`:
`u' + u ∈ D(A)` and `u' - u = s A (u' + u)`. Thesis: Ch. 7 -/
def IsCNStep (A : E →ₗ.[𝕜] E) (s : ℝ) (u u' : E) : Prop :=
  ∃ h : u' + u ∈ A.domain, u' - u = (s : 𝕜) • A ⟨u' + u, h⟩

/-- The **Cayley transform** `(1 + s A)(1 - s A)⁻¹ = 2 s⁻¹ R(s⁻¹) - 1`. -/
def cayley (A : E →ₗ.[𝕜] E) (s : ℝ) : E →L[𝕜] E :=
  (2 * (s : 𝕜)⁻¹) • resolvent A ((s : 𝕜)⁻¹) - 1

/-- The Cayley transform performs a CN step whenever `R(s⁻¹) = (s⁻¹ - A)⁻¹` exists.
Thesis: Ch. 7 -/
theorem isCNStep_cayley {R : E →L[𝕜] E} (hR : IsResolvent A ((s : 𝕜)⁻¹) R) (hs : s ≠ 0)
    (u : E) : IsCNStep A s u (cayley A s u) := by
  have hs' : (s : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hs
  set r := hR.toDomain u
  have hr : (s : 𝕜)⁻¹ • (r : E) - A r = u := hR.sub_apply_toDomain u
  have hc : cayley A s u + u = (2 * (s : 𝕜)⁻¹) • (r : E) := by
    simp [cayley, hR.resolvent_eq, r]
  refine ⟨hc ▸ A.domain.smul_mem _ r.2, ?_⟩
  have hA : A ⟨cayley A s u + u, hc ▸ A.domain.smul_mem _ r.2⟩ = (2 * (s : 𝕜)⁻¹) • A r := by
    rw [← A.map_smul]; congr 1; exact Subtype.ext hc
  rw [hA, smul_smul, show (s : 𝕜) * (2 * (s : 𝕜)⁻¹) = 2 by field_simp]
  have hcu : cayley A s u = (2 * (s : 𝕜)⁻¹) • (r : E) - u := eq_sub_of_add_eq hc
  rw [hcu, ← hr]
  module

/-- For skew-adjoint `A`, the Cayley transform performs a CN step for every `s ≠ 0`.
Thesis: Ch. 7 -/
theorem _root_.LinearPMap.IsSkewAdjoint.isCNStep_cayley [CompleteSpace E] (hA : A.IsSkewAdjoint)
    (hs : s ≠ 0) (u : E) : IsCNStep A s u (cayley A s u) :=
  Feec.TimeStepping.isCNStep_cayley (Operator.isResolvent_resolvent hA (by
    rw [← RCLike.ofReal_inv, RCLike.ofReal_re]; exact inv_ne_zero hs)) hs u

/-- The difference of two CN steps from the same point solves `e = s A e`. -/
private theorem exists_sub_eq {u₁ u₂ : E} (h₁ : IsCNStep A s u u₁) (h₂ : IsCNStep A s u u₂) :
    ∃ h : u₁ - u₂ ∈ A.domain, u₁ - u₂ = (s : 𝕜) • A ⟨u₁ - u₂, h⟩ := by
  obtain ⟨h₁, e₁⟩ := h₁
  obtain ⟨h₂, e₂⟩ := h₂
  have hd : u₁ - u₂ = (u₁ + u) - (u₂ + u) := by abel
  have hm : u₁ - u₂ ∈ A.domain := hd ▸ A.domain.sub_mem h₁ h₂
  refine ⟨hm, ?_⟩
  have : A ⟨u₁ - u₂, hm⟩ = A ⟨u₁ + u, h₁⟩ - A ⟨u₂ + u, h₂⟩ := by
    rw [← A.map_sub]; congr 1; exact Subtype.ext hd
  rw [this, smul_sub, ← e₁, ← e₂]; abel

/-- **Uniqueness of CN steps** for dissipative `A` and `s ≥ 0`. Thesis: Ch. 7 -/
theorem IsCNStep.unique (hA : A.IsDissipative) (hs : 0 ≤ s) {u₁ u₂ : E}
    (h₁ : IsCNStep A s u u₁) (h₂ : IsCNStep A s u u₂) : u₁ = u₂ := by
  obtain ⟨hm, he⟩ := exists_sub_eq h₁ h₂
  set e := u₁ - u₂ with he_def
  have h := hA ⟨e, hm⟩
  have h2 : ⟪e, e⟫ = ⟪(s : 𝕜) • A ⟨e, hm⟩, e⟫ := by rw [← he]
  have key : ‖e‖ ^ 2 = s * RCLike.re ⟪A ⟨e, hm⟩, e⟫ := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), h2, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul]
  have : ‖e‖ ^ 2 ≤ 0 := by rw [key]; exact mul_nonpos_of_nonneg_of_nonpos hs h
  exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg e]))

/-- **Uniqueness of CN steps** for skew-symmetric `A` and every `s`. Thesis: Ch. 7 -/
theorem IsCNStep.unique_of_isSkewSymmetric (hA : A.IsSkewSymmetric) {u₁ u₂ : E}
    (h₁ : IsCNStep A s u u₁) (h₂ : IsCNStep A s u u₂) : u₁ = u₂ := by
  rcases le_total 0 s with hs | hs
  · exact h₁.unique hA.isDissipative hs h₂
  · have hneg : (-A).IsDissipative := hA.neg.isDissipative
    have conv : ∀ {v : E}, IsCNStep A s u v → IsCNStep (-A) (-s) u v := by
      rintro v ⟨h, e⟩
      exact ⟨h, by rw [LinearPMap.neg_apply, RCLike.ofReal_neg, neg_smul_neg]; exact e⟩
    exact (conv h₁).unique hneg (neg_nonneg.2 hs) (conv h₂)

/-- `‖u'‖² - ‖u‖² = s re ⟪A v, v⟫`: the energy identity of a CN step, with
`v = u' + u`. -/
private theorem norm_sq_sub_norm_sq (h : IsCNStep A s u u') :
    ‖u'‖ ^ 2 - ‖u‖ ^ 2 = s * RCLike.re ⟪A ⟨u' + u, h.1⟩, u' + u⟫ := by
  have e := h.2
  have h1 : RCLike.re ⟪u' - u, u' + u⟫ = ‖u'‖ ^ 2 - ‖u‖ ^ 2 := by
    rw [inner_sub_left, inner_add_right, inner_add_right, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, ← inner_conj_symm u u']
    simp only [_root_.map_sub, _root_.map_add, RCLike.conj_re, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
    ring
  rw [← h1, e, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]

/-- **Energy conservation**: a CN step of a skew-symmetric operator preserves the norm.
Thesis: Ch. 7 -/
theorem IsCNStep.norm_eq (hA : A.IsSkewSymmetric) (h : IsCNStep A s u u') : ‖u'‖ = ‖u‖ := by
  have := norm_sq_sub_norm_sq h
  rw [hA.re_inner_self, mul_zero, sub_eq_zero] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-- **Contraction**: a CN step of a dissipative operator with `s ≥ 0` does not increase the
norm. -/
theorem IsCNStep.norm_le (hA : A.IsDissipative) (hs : 0 ≤ s) (h : IsCNStep A s u u') :
    ‖u'‖ ≤ ‖u‖ := by
  have := norm_sq_sub_norm_sq h
  have h0 : s * RCLike.re ⟪A ⟨u' + u, h.1⟩, u' + u⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs (hA ⟨u' + u, h.1⟩)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- The Cayley transform of a skew-adjoint operator is an isometry. Thesis: Ch. 7 -/
theorem norm_cayley_apply [CompleteSpace E] (hA : A.IsSkewAdjoint) (s : ℝ) (u : E) :
    ‖cayley A s u‖ = ‖u‖ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [cayley]
  · exact (hA.isCNStep_cayley hs u).norm_eq hA.isSkewSymmetric

/-- **Energy conservation of the CN iterates** `uⁿ = cayleyⁿ u⁰`. Thesis: Ch. 7 -/
theorem norm_cayley_pow_apply [CompleteSpace E] (hA : A.IsSkewAdjoint) (s : ℝ) (n : ℕ)
    (u : E) : ‖(cayley A s ^ n) u‖ = ‖u‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ']; exact (norm_cayley_apply hA s _).trans ih

/-- A CN sequence of a skew-symmetric operator has constant norm. Thesis: Ch. 7 -/
theorem norm_eq_of_forall_isCNStep (hA : A.IsSkewSymmetric) {U : ℕ → E}
    (hU : ∀ n, IsCNStep A s (U n) (U (n + 1))) (n : ℕ) : ‖U n‖ = ‖U 0‖ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [(hU n).norm_eq hA, ih]

/-- A CN sequence of a skew-adjoint operator is the sequence of Cayley iterates. -/
theorem eq_cayley_pow_of_forall_isCNStep [CompleteSpace E] (hA : A.IsSkewAdjoint) (hs : s ≠ 0)
    {U : ℕ → E} (hU : ∀ n, IsCNStep A s (U n) (U (n + 1))) (n : ℕ) :
    U n = (cayley A s ^ n) (U 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change U (n + 1) = cayley A s ((cayley A s ^ n) (U 0))
    rw [← ih]
    exact (hU n).unique_of_isSkewSymmetric hA.isSkewSymmetric (hA.isCNStep_cayley hs (U n))

/-- **Discrete constraint propagation**: if `K` reduces a dissipative `A` and `s ≥ 0`, a CN step
from `u ∈ K` stays in `K`. Thesis: Prop 4.18 -/
theorem IsCNStep.mem_of_isReducing (hA : A.IsDissipative) (hs : 0 ≤ s) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] (hK : A.IsReducing K) (hu : u ∈ K) (h : IsCNStep A s u u') :
    u' ∈ K := by
  obtain ⟨hv, e⟩ := h
  set v : A.domain := ⟨u' + u, hv⟩
  have hPv : K.starProjection (u' + u) = K.starProjection u' + u := by
    rw [_root_.map_add, (K.starProjection_eq_self_iff).2 hu]
  have hstep : IsCNStep A s u (K.starProjection u') := by
    refine ⟨hPv ▸ hK.proj_mem v, ?_⟩
    have hc := hK.comm v
    have : A ⟨K.starProjection u' + u, hPv ▸ hK.proj_mem v⟩ =
        K.starProjection (A v) := by
      rw [← hc]; congr 1; exact Subtype.ext hPv.symm
    rw [this, ← ContinuousLinearMap.map_smul, ← e, _root_.map_sub,
      (K.starProjection_eq_self_iff).2 hu]
  have := hstep.unique hA hs ⟨hv, e⟩
  rw [← this]
  exact K.starProjection_apply_mem _

/-- **Discrete constraint propagation along CN sequences.** Thesis: Prop 4.18 -/
theorem mem_of_forall_isCNStep (hA : A.IsDissipative) (hs : 0 ≤ s) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] (hK : A.IsReducing K) {U : ℕ → E}
    (hU : ∀ n, IsCNStep A s (U n) (U (n + 1))) (h0 : U 0 ∈ K) (n : ℕ) : U n ∈ K := by
  induction n with
  | zero => exact h0
  | succ n ih => exact (hU n).mem_of_isReducing hA hs hK ih

end Feec.TimeStepping
