module

public import Feec.Operator.Resolvent
public import Feec.ForMathlib.LinearPMap.Reducing
public import Mathlib.Analysis.InnerProductSpace.Adjoint

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

## Three-field schemes (thesis Ch. 7)

For finite-dimensional spaces `V₀ --d₀--> V₁ --d₁--> V₂` (finite element spaces with their `L²`
products), the CN step of the full system (4.14) `σ̇ = d₀* E`, `Ė = -d₀ σ - d₁* B`, `Ḃ = d₁ E`
is `IsFullCNStep`, that of the reduced system (4.15) `Ė = -d₁* B`, `Ḃ = d₁ E` is
`IsReducedCNStep`:

* `IsReducedCNStep.isFullCNStep_zero`: for `d₁ d₀ = 0` a reduced step from `d₀* E = 0`, padded
  with `σ = 0`, is a full step and keeps `d₀* E = 0` (discrete Prop 4.18);
  `IsReducedCNStep.adjoint_eq_zero_of_isFullCNStep`: the condition `d₀* E = 0` is necessary.
* `existsUnique_isFullCNStep`, `existsUnique_isReducedCNStep`, `fullCNStep`: both steps are well
  defined for every `s`; `IsFullCNStep.norm_sq_add`: energy conservation;
  `IsFullCNStep.apply_eq_of_comp_eq_zero`: `d₂ B` is conserved when `d₂ d₁ = 0`.

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

/-! ### Three-field schemes for the full and reduced systems (thesis Ch. 7) -/

section ThreeField

open LinearMap InnerProductSpace
open scoped RealInnerProductSpace

variable {V₀ V₁ V₂ : Type*}
  [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀] [FiniteDimensional ℝ V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [FiniteDimensional ℝ V₂]

/-- One **Crank–Nicolson step** with half step `s` of the full system (4.14)
`σ̇ = d₀* E`, `Ė = -d₀ σ - d₁* B`, `Ḃ = d₁ E` on finite-dimensional spaces.
See [QuennevilleBelair2015], (4.14), Ch. 7. -/
def IsFullCNStep (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (σ σ' : V₀) (E E' : V₁) (B B' : V₂) : Prop :=
  σ' - σ = s • adjoint d₀ (E' + E) ∧
  E' - E = -(s • (d₀ (σ' + σ) + adjoint d₁ (B' + B))) ∧
  B' - B = s • d₁ (E' + E)

/-- One **Crank–Nicolson step** of the reduced system (4.15) `Ė = -d₁* B`, `Ḃ = d₁ E`.
See [QuennevilleBelair2015], (4.15), Ch. 7. -/
def IsReducedCNStep (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) (E E' : V₁) (B B' : V₂) : Prop :=
  E' - E = -(s • adjoint d₁ (B' + B)) ∧ B' - B = s • d₁ (E' + E)

/-- `d₀* d₁* = 0` when `d₁ d₀ = 0`. -/
theorem adjoint_adjoint_apply_eq_zero {d₀ : V₀ →ₗ[ℝ] V₁} {d₁ : V₁ →ₗ[ℝ] V₂}
    (hd : d₁ ∘ₗ d₀ = 0) (y : V₂) : adjoint d₀ (adjoint d₁ y) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.adjoint_comp, hd]; simp

/-- **Discrete Prop 4.18** (thesis Ch. 7, l. 4289–4291, "might give equal approximations"): a
reduced CN step from `d₀* E = 0` keeps `d₀* E' = 0`, and padded with `σ = 0` it is a full CN
step. See [QuennevilleBelair2015], Prop. 4.18, Ch. 7. -/
theorem IsReducedCNStep.isFullCNStep_zero {d₀ : V₀ →ₗ[ℝ] V₁} {d₁ : V₁ →ₗ[ℝ] V₂}
    (hd : d₁ ∘ₗ d₀ = 0) {s : ℝ} {E E' : V₁} {B B' : V₂} (h : IsReducedCNStep d₁ s E E' B B')
    (hE : adjoint d₀ E = 0) : adjoint d₀ E' = 0 ∧ IsFullCNStep d₀ d₁ s 0 0 E E' B B' := by
  obtain ⟨h1, h2⟩ := h
  have hE' : adjoint d₀ E' = 0 := by
    have : adjoint d₀ (E' - E) = 0 := by
      rw [h1, map_neg, map_smul, adjoint_adjoint_apply_eq_zero hd]; simp
    simpa [map_sub, hE, sub_eq_zero] using this
  refine ⟨hE', ?_, ?_, h2⟩
  · simp [map_add, hE, hE']
  · simpa using h1

/-- The condition `d₀* E = 0` of `IsReducedCNStep.isFullCNStep_zero` is necessary (`s ≠ 0`):
otherwise the full scheme moves `σ` off `0`. See [QuennevilleBelair2015], Prop. 4.18, Ch. 7. -/
theorem IsReducedCNStep.adjoint_eq_zero_of_isFullCNStep {d₀ : V₀ →ₗ[ℝ] V₁}
    {d₁ : V₁ →ₗ[ℝ] V₂} (hd : d₁ ∘ₗ d₀ = 0) {s : ℝ} (hs : s ≠ 0) {E E' : V₁} {B B' : V₂}
    (h : IsReducedCNStep d₁ s E E' B B') (hf : IsFullCNStep d₀ d₁ s 0 0 E E' B B') :
    adjoint d₀ E = 0 := by
  have hdiff : adjoint d₀ E' = adjoint d₀ E := by
    have : adjoint d₀ (E' - E) = 0 := by
      rw [h.1, map_neg, map_smul, adjoint_adjoint_apply_eq_zero hd]; simp
    rwa [map_sub, sub_eq_zero] at this
  have hsum : s • adjoint d₀ (E' + E) = 0 := by simpa using hf.1.symm
  rw [map_add, hdiff, smul_eq_zero] at hsum
  rcases hsum with hs0 | h2
  · exact absurd hs0 hs
  · have : (2 : ℝ) • adjoint d₀ E = 0 := by rw [two_smul]; exact h2
    simpa using this

omit [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂] in
private theorem inner_sub_add_eq' {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (x y : W) : ⟪x - y, x + y⟫ = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm x y]; ring

/-- **Energy conservation of the full CN step**: `‖σ‖² + ‖E‖² + ‖B‖²` is conserved (not `‖E‖`
alone). See [QuennevilleBelair2015], Ch. 7 (Table 7.1). -/
theorem IsFullCNStep.norm_sq_add {d₀ : V₀ →ₗ[ℝ] V₁} {d₁ : V₁ →ₗ[ℝ] V₂} {s : ℝ}
    {σ σ' : V₀} {E E' : V₁} {B B' : V₂} (h : IsFullCNStep d₀ d₁ s σ σ' E E' B B') :
    ‖σ'‖ ^ 2 + ‖E'‖ ^ 2 + ‖B'‖ ^ 2 = ‖σ‖ ^ 2 + ‖E‖ ^ 2 + ‖B‖ ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : ⟪σ' - σ, σ' + σ⟫ = s * ⟪E' + E, d₀ (σ' + σ)⟫ := by
    rw [h1, real_inner_smul_left, LinearMap.adjoint_inner_left]
  have e3 : ⟪B' - B, B' + B⟫ = s * ⟪d₁ (E' + E), B' + B⟫ := by
    rw [h3, real_inner_smul_left]
  have e2 : ⟪E' - E, E' + E⟫ =
      -(s * ⟪E' + E, d₀ (σ' + σ)⟫) - s * ⟪d₁ (E' + E), B' + B⟫ := by
    rw [h2, inner_neg_left, real_inner_smul_left, inner_add_left,
      LinearMap.adjoint_inner_left, real_inner_comm (d₀ (σ' + σ)) (E' + E),
      real_inner_comm (B' + B) (d₁ (E' + E))]
    ring
  rw [inner_sub_add_eq'] at e1 e2 e3
  linarith

/-- **Uniqueness of the full CN step** (the thesis never argues solvability): the difference
`(a, b, c)` of two steps from the same state is a CN step from `0`, so its energy vanishes.
See [QuennevilleBelair2015], Ch. 7. -/
theorem IsFullCNStep.unique {d₀ : V₀ →ₗ[ℝ] V₁} {d₁ : V₁ →ₗ[ℝ] V₂} {s : ℝ} {σ σ₁ σ₂ : V₀}
    {E E₁ E₂ : V₁} {B B₁ B₂ : V₂} (h₁ : IsFullCNStep d₀ d₁ s σ σ₁ E E₁ B B₁)
    (h₂ : IsFullCNStep d₀ d₁ s σ σ₂ E E₂ B B₂) : σ₁ = σ₂ ∧ E₁ = E₂ ∧ B₁ = B₂ := by
  obtain ⟨a1, b1, c1⟩ := h₁
  obtain ⟨a2, b2, c2⟩ := h₂
  have hd : IsFullCNStep d₀ d₁ s 0 (σ₁ - σ₂) 0 (E₁ - E₂) 0 (B₁ - B₂) := by
    refine ⟨?_, ?_, ?_⟩
    · calc σ₁ - σ₂ - 0 = (σ₁ - σ) - (σ₂ - σ) := by abel
        _ = s • adjoint d₀ (E₁ + E) - s • adjoint d₀ (E₂ + E) := by rw [a1, a2]
        _ = s • adjoint d₀ (E₁ - E₂ + 0) := by
          rw [← smul_sub, ← map_sub, add_zero, add_sub_add_right_eq_sub]
    · calc E₁ - E₂ - 0 = (E₁ - E) - (E₂ - E) := by abel
        _ = -(s • (d₀ (σ₁ + σ) + adjoint d₁ (B₁ + B)))
            - -(s • (d₀ (σ₂ + σ) + adjoint d₁ (B₂ + B))) := by rw [b1, b2]
        _ = -(s • (d₀ (σ₁ - σ₂ + 0) + adjoint d₁ (B₁ - B₂ + 0))) := by
          simp only [add_zero, map_sub, map_add, smul_add, smul_sub, neg_add]; abel
    · calc B₁ - B₂ - 0 = (B₁ - B) - (B₂ - B) := by abel
        _ = s • d₁ (E₁ + E) - s • d₁ (E₂ + E) := by rw [c1, c2]
        _ = s • d₁ (E₁ - E₂ + 0) := by
          rw [← smul_sub, ← map_sub, add_zero, add_sub_add_right_eq_sub]
  have h := hd.norm_sq_add
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h
  have ha := sq_nonneg ‖σ₁ - σ₂‖
  have hb := sq_nonneg ‖E₁ - E₂‖
  have hc := sq_nonneg ‖B₁ - B₂‖
  refine ⟨?_, ?_, ?_⟩ <;> rw [← sub_eq_zero, ← norm_eq_zero] <;> nlinarith

/-- The reduced CN step is the full CN step for `d₀ = 0` with constant `σ`. -/
theorem isFullCNStep_zero_iff (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) (σ σ' : V₁) (E E' : V₁)
    (B B' : V₂) :
    IsFullCNStep (0 : V₁ →ₗ[ℝ] V₁) d₁ s σ σ' E E' B B' ↔
      σ' = σ ∧ IsReducedCNStep d₁ s E E' B B' := by
  simp [IsFullCNStep, IsReducedCNStep, sub_eq_zero]

/-- Uniqueness of the reduced CN step. -/
theorem IsReducedCNStep.unique {d₁ : V₁ →ₗ[ℝ] V₂} {s : ℝ} {E E₁ E₂ : V₁} {B B₁ B₂ : V₂}
    (h₁ : IsReducedCNStep d₁ s E E₁ B B₁) (h₂ : IsReducedCNStep d₁ s E E₂ B B₂) :
    E₁ = E₂ ∧ B₁ = B₂ :=
  (((isFullCNStep_zero_iff d₁ s 0 0 E E₁ B B₁).2 ⟨rfl, h₁⟩).unique
    ((isFullCNStep_zero_iff d₁ s 0 0 E E₂ B B₂).2 ⟨rfl, h₂⟩)).2

/-- The implicit side `x ↦ (M + sK) x` of the full CN step in operator form,
`(σ, E, B) ↦ (σ - s d₀* E, E + s (d₀ σ + d₁* B), B - s d₁ E)`; the explicit side is
`cnLHS d₀ d₁ (-s)`. -/
def cnLHS (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) :
    (V₀ × V₁ × V₂) →ₗ[ℝ] (V₀ × V₁ × V₂) where
  toFun x := (x.1 - s • adjoint d₀ x.2.1, x.2.1 + s • (d₀ x.1 + adjoint d₁ x.2.2),
    x.2.2 - s • d₁ x.2.1)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> module
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk,
      Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> module

/-- A full CN step is the linear system `(M + sK) x' = (M - sK) x`. -/
theorem isFullCNStep_iff_cnLHS (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (x x' : V₀ × V₁ × V₂) :
    IsFullCNStep d₀ d₁ s x.1 x'.1 x.2.1 x'.2.1 x.2.2 x'.2.2 ↔
      cnLHS d₀ d₁ s x' = cnLHS d₀ d₁ (-s) x := by
  obtain ⟨σ, E, B⟩ := x
  obtain ⟨σ', E', B'⟩ := x'
  simp only [IsFullCNStep, cnLHS, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq]
  have e1 : (σ' - s • adjoint d₀ E') - (σ - -s • adjoint d₀ E) =
      (σ' - σ) - s • adjoint d₀ (E' + E) := by rw [map_add]; module
  have e2 : (E' + s • (d₀ σ' + adjoint d₁ B')) - (E + -s • (d₀ σ + adjoint d₁ B)) =
      (E' - E) - -(s • (d₀ (σ' + σ) + adjoint d₁ (B' + B))) := by
    rw [map_add, map_add]; module
  have e3 : (B' - s • d₁ E') - (B - -s • d₁ E) = (B' - B) - s • d₁ (E' + E) := by
    rw [map_add]; module
  refine and_congr ?_ (and_congr ?_ ?_)
  · rw [← sub_eq_zero, ← e1, sub_eq_zero]
  · rw [← sub_eq_zero, ← e2, sub_eq_zero]
  · rw [← sub_eq_zero, ← e3, sub_eq_zero]

/-- The CN system is invertible for every `s` (the thesis never argues this): injective by
`IsFullCNStep.unique`, hence bijective in finite dimension. See [QuennevilleBelair2015], Ch. 7. -/
theorem bijective_cnLHS (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) :
    Function.Bijective (cnLHS d₀ d₁ s) := by
  have hinj : Function.Injective (cnLHS d₀ d₁ s) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := (isFullCNStep_iff_cnLHS d₀ d₁ s 0 x).2 (by rw [hx, map_zero])
    have h2 := (isFullCNStep_iff_cnLHS d₀ d₁ s 0 0).2 (by rw [map_zero, map_zero])
    obtain ⟨e1, e2, e3⟩ := h1.unique h2
    exact Prod.ext e1 (Prod.ext e2 e3)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- **The full CN step is well defined**: from every state there is exactly one next state.
See [QuennevilleBelair2015], Ch. 7. -/
theorem existsUnique_isFullCNStep (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (σ : V₀) (E : V₁) (B : V₂) :
    ∃! x' : V₀ × V₁ × V₂, IsFullCNStep d₀ d₁ s σ x'.1 E x'.2.1 B x'.2.2 := by
  obtain ⟨x', hx'⟩ := (bijective_cnLHS d₀ d₁ s).2 (cnLHS d₀ d₁ (-s) (σ, E, B))
  refine ⟨x', (isFullCNStep_iff_cnLHS d₀ d₁ s (σ, E, B) x').2 hx', fun y hy => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hy.unique ((isFullCNStep_iff_cnLHS d₀ d₁ s (σ, E, B) x').2 hx')
  exact Prod.ext e1 (Prod.ext e2 e3)

/-- The reduced CN step is well defined. See [QuennevilleBelair2015], Ch. 7. -/
theorem existsUnique_isReducedCNStep (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) (E : V₁) (B : V₂) :
    ∃! y : V₁ × V₂, IsReducedCNStep d₁ s E y.1 B y.2 := by
  obtain ⟨x', hx', -⟩ := existsUnique_isFullCNStep (0 : V₁ →ₗ[ℝ] V₁) d₁ s 0 E B
  have hr := ((isFullCNStep_zero_iff d₁ s 0 x'.1 E x'.2.1 B x'.2.2).1 hx').2
  refine ⟨(x'.2.1, x'.2.2), hr, fun y hy => ?_⟩
  obtain ⟨e1, e2⟩ := hy.unique hr
  exact Prod.ext e1 e2

/-- The full CN time-stepping map `xⁿ ↦ xⁿ⁺¹ = (M + sK)⁻¹ (M - sK) xⁿ`. -/
def fullCNStep (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) :
    (V₀ × V₁ × V₂) →ₗ[ℝ] (V₀ × V₁ × V₂) :=
  ((LinearEquiv.ofBijective (cnLHS d₀ d₁ s) (bijective_cnLHS d₀ d₁ s)).symm :
    (V₀ × V₁ × V₂) →ₗ[ℝ] (V₀ × V₁ × V₂)) ∘ₗ cnLHS d₀ d₁ (-s)

/-- `fullCNStep` performs a full CN step. -/
theorem isFullCNStep_fullCNStep (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (x : V₀ × V₁ × V₂) :
    IsFullCNStep d₀ d₁ s x.1 (fullCNStep d₀ d₁ s x).1 x.2.1 (fullCNStep d₀ d₁ s x).2.1 x.2.2
      (fullCNStep d₀ d₁ s x).2.2 := by
  rw [isFullCNStep_iff_cnLHS]
  exact (LinearEquiv.ofBijective (cnLHS d₀ d₁ s) (bijective_cnLHS d₀ d₁ s)).apply_symm_apply
    (cnLHS d₀ d₁ (-s) x)

variable {V₃ : Type*} [NormedAddCommGroup V₃] [InnerProductSpace ℝ V₃]

/-- The discrete divergence `d₂ B` is conserved by a full CN step when `d₂ d₁ = 0` (the
quantity plotted in thesis Figs 7.1–7.4). See [QuennevilleBelair2015], Ch. 7. -/
theorem IsFullCNStep.apply_eq_of_comp_eq_zero {d₀ : V₀ →ₗ[ℝ] V₁} {d₁ : V₁ →ₗ[ℝ] V₂}
    {d₂ : V₂ →ₗ[ℝ] V₃} (hd₂ : d₂ ∘ₗ d₁ = 0) {s : ℝ} {σ σ' : V₀} {E E' : V₁} {B B' : V₂}
    (h : IsFullCNStep d₀ d₁ s σ σ' E E' B B') : d₂ B' = d₂ B := by
  have : d₂ (B' - B) = 0 := by
    rw [h.2.2, map_smul, ← LinearMap.comp_apply, hd₂, LinearMap.zero_apply, smul_zero]
  rwa [map_sub, sub_eq_zero] at this

omit [FiniteDimensional ℝ V₀] in
/-- The discrete divergence `d₂ B` is conserved by a reduced CN step when `d₂ d₁ = 0`. -/
theorem IsReducedCNStep.apply_eq_of_comp_eq_zero {d₁ : V₁ →ₗ[ℝ] V₂} {d₂ : V₂ →ₗ[ℝ] V₃}
    (hd₂ : d₂ ∘ₗ d₁ = 0) {s : ℝ} {E E' : V₁} {B B' : V₂} (h : IsReducedCNStep d₁ s E E' B B') :
    d₂ B' = d₂ B := by
  have : d₂ (B' - B) = 0 := by
    rw [h.2, map_smul, ← LinearMap.comp_apply, hd₂, LinearMap.zero_apply, smul_zero]
  rwa [map_sub, sub_eq_zero] at this

end ThreeField

end Feec.TimeStepping
