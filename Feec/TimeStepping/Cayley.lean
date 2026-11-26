module

public import Feec.Operator.Resolvent
public import Feec.ForMathlib.LinearPMap.Reducing
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Crank–Nicolson as a Cayley transform

Crank–Nicolson steps `u' - u = s A (u' + u)` and the Cayley transform `(1 + s A)(1 - s A)⁻¹`:
energy, constraint propagation, the three-field Einstein–Bianchi schemes, prescribed boundary DOFs.

## Main results

* `isCNStep_cayley`: the Cayley transform performs a CN step whenever `(s⁻¹ - A)⁻¹` exists.
* `IsCNStep.mem_of_isReducing`: CN steps with `s ≥ 0` keep reducing subspaces of a dissipative
  operator.
* `IsReducedCNStep.isFullCNStep_zero`: for `d₁ d₀ = 0`, reduced steps from `d₀* E = 0` are full
  steps.
* `existsUnique_isFullCNStep`: the full CN step is well defined.
* `existsUnique_isDirichletCNStep`: the step with prescribed boundary DOFs is well defined if
  `s ⟪A w, w⟫ ≤ 0` on `V₀`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7, Prop 4.18

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Feec.Operator

@[expose] public noncomputable section

namespace Feec.TimeStepping

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {s : ℝ} {u u' : E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem re_inner_sub_add (x y : E) : RCLike.re ⟪x - y, x + y⟫ = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  rw [inner_sub_left, inner_add_right, inner_add_right, _root_.map_sub, _root_.map_add,
    _root_.map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq, inner_re_symm y x]
  ring

/-- A Crank–Nicolson step `u ↦ u'` with half step `s`: `u' - u = s A (u' + u)`, `u' + u ∈ D(A)`. -/
def IsCNStep (A : E →ₗ.[𝕜] E) (s : ℝ) (u u' : E) : Prop :=
  ∃ h : u' + u ∈ A.domain, u' - u = (s : 𝕜) • A ⟨u' + u, h⟩

/-- The **Cayley transform** `(1 + s A)(1 - s A)⁻¹ = 2 s⁻¹ R(s⁻¹) - 1`. -/
def cayley (A : E →ₗ.[𝕜] E) (s : ℝ) : E →L[𝕜] E :=
  (2 * (s : 𝕜)⁻¹) • resolvent A ((s : 𝕜)⁻¹) - 1

theorem cayley_eq_two_mul_sub_one (A : E →ₗ.[𝕜] E) (s : ℝ) :
    cayley A s = 2 * ((s : 𝕜)⁻¹ • resolvent A ((s : 𝕜)⁻¹)) - 1 := by
  rw [cayley, two_mul ((s : 𝕜)⁻¹ • _), two_mul (s : 𝕜)⁻¹, add_smul]

/-- The Cayley transform performs a CN step whenever `R(s⁻¹) = (s⁻¹ - A)⁻¹` exists.
[QuennevilleBelair2015], Ch. 7 -/
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

theorem _root_.LinearPMap.IsSkewAdjoint.isCNStep_cayley [CompleteSpace E] (hA : A.IsSkewAdjoint)
    (hs : s ≠ 0) (u : E) : IsCNStep A s u (cayley A s u) :=
  Feec.TimeStepping.isCNStep_cayley (Operator.isResolvent_resolvent hA (by
    rw [← RCLike.ofReal_inv, RCLike.ofReal_re]; exact inv_ne_zero hs)) hs u

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

theorem IsCNStep.unique_of_isSkewSymmetric (hA : A.IsSkewSymmetric) {u₁ u₂ : E}
    (h₁ : IsCNStep A s u u₁) (h₂ : IsCNStep A s u u₂) : u₁ = u₂ := by
  rcases le_total 0 s with hs | hs
  · exact h₁.unique hA.isDissipative hs h₂
  · have hneg : (-A).IsDissipative := hA.neg.isDissipative
    have conv : ∀ {v : E}, IsCNStep A s u v → IsCNStep (-A) (-s) u v := by
      rintro v ⟨h, e⟩
      exact ⟨h, by rw [LinearPMap.neg_apply, RCLike.ofReal_neg, neg_smul_neg]; exact e⟩
    exact (conv h₁).unique hneg (neg_nonneg.2 hs) (conv h₂)

private theorem norm_sq_sub_norm_sq (h : IsCNStep A s u u') :
    ‖u'‖ ^ 2 - ‖u‖ ^ 2 = s * RCLike.re ⟪A ⟨u' + u, h.1⟩, u' + u⟫ := by
  rw [← re_inner_sub_add (𝕜 := 𝕜), h.2, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]

theorem IsCNStep.norm_eq (hA : A.IsSkewSymmetric) (h : IsCNStep A s u u') : ‖u'‖ = ‖u‖ := by
  have := norm_sq_sub_norm_sq h
  rw [hA.re_inner_self, mul_zero, sub_eq_zero] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

theorem IsCNStep.norm_le (hA : A.IsDissipative) (hs : 0 ≤ s) (h : IsCNStep A s u u') :
    ‖u'‖ ≤ ‖u‖ := by
  have := norm_sq_sub_norm_sq h
  have h0 : s * RCLike.re ⟪A ⟨u' + u, h.1⟩, u' + u⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs (hA ⟨u' + u, h.1⟩)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

theorem norm_cayley_apply [CompleteSpace E] (hA : A.IsSkewAdjoint) (s : ℝ) (u : E) :
    ‖cayley A s u‖ = ‖u‖ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [cayley]
  · exact (hA.isCNStep_cayley hs u).norm_eq hA.isSkewSymmetric

theorem norm_cayley_pow_apply [CompleteSpace E] (hA : A.IsSkewAdjoint) (s : ℝ) (n : ℕ)
    (u : E) : ‖(cayley A s ^ n) u‖ = ‖u‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ']; exact (norm_cayley_apply hA s _).trans ih

theorem norm_eq_of_forall_isCNStep (hA : A.IsSkewSymmetric) {U : ℕ → E}
    (hU : ∀ n, IsCNStep A s (U n) (U (n + 1))) (n : ℕ) : ‖U n‖ = ‖U 0‖ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [(hU n).norm_eq hA, ih]

/-- **Discrete constraint propagation**: if `K` reduces a dissipative `A` and `s ≥ 0`, a CN step
from `u ∈ K` stays in `K`. [QuennevilleBelair2015], Prop 4.18 (adapted) -/
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

theorem mem_of_forall_isCNStep (hA : A.IsDissipative) (hs : 0 ≤ s) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] (hK : A.IsReducing K) {U : ℕ → E}
    (hU : ∀ n, IsCNStep A s (U n) (U (n + 1))) (h0 : U 0 ∈ K) (n : ℕ) : U n ∈ K := by
  induction n with
  | zero => exact h0
  | succ n ih => exact (hU n).mem_of_isReducing hA hs hK ih

/-! ### Linearity of CN steps and eigenvectors -/

theorem IsCNStep.add {u₁ u₁' u₂ u₂' : E} (h₁ : IsCNStep A s u₁ u₁') (h₂ : IsCNStep A s u₂ u₂') :
    IsCNStep A s (u₁ + u₂) (u₁' + u₂') := by
  obtain ⟨hd₁, e₁⟩ := h₁
  obtain ⟨hd₂, e₂⟩ := h₂
  have hd : u₁' + u₂' + (u₁ + u₂) = (u₁' + u₁) + (u₂' + u₂) := by abel
  refine ⟨hd ▸ A.domain.add_mem hd₁ hd₂, ?_⟩
  have hv : (⟨u₁' + u₂' + (u₁ + u₂), hd ▸ A.domain.add_mem hd₁ hd₂⟩ : A.domain) =
      ⟨u₁' + u₁, hd₁⟩ + ⟨u₂' + u₂, hd₂⟩ := Subtype.ext hd
  rw [hv, LinearPMap.map_add, smul_add, ← e₁, ← e₂]
  abel

theorem IsCNStep.smul (c : 𝕜) (h : IsCNStep A s u u') : IsCNStep A s (c • u) (c • u') := by
  obtain ⟨hd, e⟩ := h
  have hd' : c • u' + c • u = c • (u' + u) := (smul_add c u' u).symm
  refine ⟨hd' ▸ A.domain.smul_mem c hd, ?_⟩
  have hv : (⟨c • u' + c • u, hd' ▸ A.domain.smul_mem c hd⟩ : A.domain) = c • ⟨u' + u, hd⟩ :=
    Subtype.ext hd'
  rw [hv, LinearPMap.map_smul, smul_comm, ← e, smul_sub]

theorem isCNStep_of_eigen {μ : 𝕜} (hu : u ∈ A.domain) (hAu : A ⟨u, hu⟩ = μ • u)
    (hμ : 1 - (s : 𝕜) * μ ≠ 0) :
    IsCNStep A s u (((1 + (s : 𝕜) * μ) / (1 - (s : 𝕜) * μ)) • u) := by
  set l : 𝕜 := (1 + (s : 𝕜) * μ) / (1 - (s : 𝕜) * μ)
  have hd : l • u + u = (l + 1) • u := by rw [add_smul, one_smul]
  refine ⟨hd ▸ A.domain.smul_mem (l + 1) hu, ?_⟩
  have hv : (⟨l • u + u, hd ▸ A.domain.smul_mem (l + 1) hu⟩ : A.domain) = (l + 1) • ⟨u, hu⟩ :=
    Subtype.ext hd
  rw [hv, LinearPMap.map_smul, hAu, smul_smul, smul_smul]
  conv_lhs => rw [← one_smul 𝕜 u, smul_smul, mul_one, ← sub_smul]
  congr 1
  have hl : l * (1 - (s : 𝕜) * μ) = 1 + (s : 𝕜) * μ := div_mul_cancel₀ _ hμ
  linear_combination hl

omit [InnerProductSpace 𝕜 E] in
theorem norm_amplification_eq_one (s θ : ℝ) :
    ‖(1 + (s : ℂ) * (Complex.I * θ)) / (1 - (s : ℂ) * (Complex.I * θ))‖ = 1 := by
  have h1 : (1 + (s : ℂ) * (Complex.I * θ)) = ⟨1, s * θ⟩ := by apply Complex.ext <;> simp
  have h2 : (1 - (s : ℂ) * (Complex.I * θ)) = ⟨1, -(s * θ)⟩ := by apply Complex.ext <;> simp
  have hne : (⟨1, -(s * θ)⟩ : ℂ) ≠ 0 := fun h => by simpa using congrArg Complex.re h
  rw [h1, h2, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 hne), Complex.norm_def,
    Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]

omit [InnerProductSpace 𝕜 E] in
theorem amplification_eq_exp (s θ : ℝ) :
    (1 + (s : ℂ) * (Complex.I * θ)) / (1 - (s : ℂ) * (Complex.I * θ)) =
      Complex.exp (((2 * Real.arctan (s * θ) : ℝ) : ℂ) * Complex.I) := by
  set x := s * θ with hx
  set a := Real.arctan x
  have hc : Real.cos a ^ 2 * (1 + x ^ 2) = 1 := by
    rw [Real.cos_arctan, div_pow, Real.sq_sqrt (by positivity), one_pow]
    field_simp
  have hs : Real.sin a = x * Real.cos a := by
    rw [Real.sin_arctan, Real.cos_arctan]; ring
  have hne : (1 - (s : ℂ) * (Complex.I * θ)) ≠ 0 := by
    intro h
    simpa using congrArg Complex.re h
  have he : Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I) =
      ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I) ^ 2 := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [div_eq_iff hne, he, hs]
  have hc' : (Real.cos a : ℂ) ^ 2 * (1 + (x : ℂ) ^ 2) = 1 := by exact_mod_cast hc
  rw [hx] at hc'
  push_cast at hc' ⊢
  rw [hx]; push_cast
  linear_combination (-(1 + (s : ℂ) * (Complex.I * θ))) * hc' +
    (1 + (s : ℂ) * (Complex.I * θ)) * Complex.cos a ^ 2 * ((s : ℂ) * θ) ^ 2 * Complex.I_sq

theorem two_mul_arctan_ne_two_mul {x : ℝ} (hx : x ≠ 0) : 2 * Real.arctan x ≠ 2 * x := by
  intro h
  have h' : Real.arctan x = x := by linarith
  rcases hx.lt_or_gt with hlt | hlt
  · exact (Real.self_lt_arctan hlt).ne' h'
  · exact (Real.arctan_lt_self hlt).ne h'

/-! ### Three-field schemes for the full and reduced systems (thesis Ch. 7) -/

section ThreeField

open LinearMap InnerProductSpace
open scoped RealInnerProductSpace

variable {V₀ V₁ V₂ : Type*}
  [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀] [FiniteDimensional ℝ V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [FiniteDimensional ℝ V₂]

/-- A CN step of the full system (4.14) `σ̇ = d₀* E`, `Ė = -d₀ σ - d₁* B`, `Ḃ = d₁ E`. -/
def IsFullCNStep (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (σ σ' : V₀) (E E' : V₁) (B B' : V₂) : Prop :=
  σ' - σ = s • adjoint d₀ (E' + E) ∧
  E' - E = -(s • (d₀ (σ' + σ) + adjoint d₁ (B' + B))) ∧
  B' - B = s • d₁ (E' + E)

/-- A Crank–Nicolson step of the reduced system (4.15) `Ė = -d₁* B`, `Ḃ = d₁ E`. -/
def IsReducedCNStep (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) (E E' : V₁) (B B' : V₂) : Prop :=
  E' - E = -(s • adjoint d₁ (B' + B)) ∧ B' - B = s • d₁ (E' + E)

theorem adjoint_adjoint_apply_eq_zero {d₀ : V₀ →ₗ[ℝ] V₁} {d₁ : V₁ →ₗ[ℝ] V₂}
    (hd : d₁ ∘ₗ d₀ = 0) (y : V₂) : adjoint d₀ (adjoint d₁ y) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.adjoint_comp, hd]; simp

/-- **Constraint propagation, reduced system** ([QuennevilleBelair2015], Prop 4.18 (adapted)):
for `d₁ d₀ = 0`, a reduced CN step from `d₀* E = 0` keeps `d₀* E' = 0`, and with `σ = 0` it is a
full step. -/
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
private theorem real_inner_sub_add {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (x y : W) : ⟪x - y, x + y⟫ = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  simpa using re_inner_sub_add (𝕜 := ℝ) x y

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
  rw [real_inner_sub_add] at e1 e2 e3
  linarith

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

theorem isFullCNStep_zero_iff (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ) (σ σ' : V₁) (E E' : V₁)
    (B B' : V₂) :
    IsFullCNStep (0 : V₁ →ₗ[ℝ] V₁) d₁ s σ σ' E E' B B' ↔
      σ' = σ ∧ IsReducedCNStep d₁ s E E' B B' := by
  simp [IsFullCNStep, IsReducedCNStep, sub_eq_zero]

theorem IsReducedCNStep.unique {d₁ : V₁ →ₗ[ℝ] V₂} {s : ℝ} {E E₁ E₂ : V₁} {B B₁ B₂ : V₂}
    (h₁ : IsReducedCNStep d₁ s E E₁ B B₁) (h₂ : IsReducedCNStep d₁ s E E₂ B B₂) :
    E₁ = E₂ ∧ B₁ = B₂ :=
  (((isFullCNStep_zero_iff d₁ s 0 0 E E₁ B B₁).2 ⟨rfl, h₁⟩).unique
    ((isFullCNStep_zero_iff d₁ s 0 0 E E₂ B B₂).2 ⟨rfl, h₂⟩)).2

/-- The implicit side `x ↦ (M + sK) x` of the full CN step, in operator form. -/
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
[QuennevilleBelair2015], Ch. 7 -/
theorem existsUnique_isFullCNStep (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (σ : V₀) (E : V₁) (B : V₂) :
    ∃! x' : V₀ × V₁ × V₂, IsFullCNStep d₀ d₁ s σ x'.1 E x'.2.1 B x'.2.2 := by
  obtain ⟨x', hx'⟩ := (bijective_cnLHS d₀ d₁ s).2 (cnLHS d₀ d₁ (-s) (σ, E, B))
  refine ⟨x', (isFullCNStep_iff_cnLHS d₀ d₁ s (σ, E, B) x').2 hx', fun y hy => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hy.unique ((isFullCNStep_iff_cnLHS d₀ d₁ s (σ, E, B) x').2 hx')
  exact Prod.ext e1 (Prod.ext e2 e3)

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

theorem isFullCNStep_fullCNStep (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂) (s : ℝ)
    (x : V₀ × V₁ × V₂) :
    IsFullCNStep d₀ d₁ s x.1 (fullCNStep d₀ d₁ s x).1 x.2.1 (fullCNStep d₀ d₁ s x).2.1 x.2.2
      (fullCNStep d₀ d₁ s x).2.2 := by
  rw [isFullCNStep_iff_cnLHS]
  exact (LinearEquiv.ofBijective (cnLHS d₀ d₁ s) (bijective_cnLHS d₀ d₁ s)).apply_symm_apply
    (cnLHS d₀ d₁ (-s) x)

variable {V₃ : Type*} [NormedAddCommGroup V₃] [InnerProductSpace ℝ V₃]

theorem IsFullCNStep.apply_eq_of_comp_eq_zero {d₀ : V₀ →ₗ[ℝ] V₁} {d₁ : V₁ →ₗ[ℝ] V₂}
    {d₂ : V₂ →ₗ[ℝ] V₃} (hd₂ : d₂ ∘ₗ d₁ = 0) {s : ℝ} {σ σ' : V₀} {E E' : V₁} {B B' : V₂}
    (h : IsFullCNStep d₀ d₁ s σ σ' E E' B B') : d₂ B' = d₂ B := by
  have : d₂ (B' - B) = 0 := by
    rw [h.2.2, map_smul, ← LinearMap.comp_apply, hd₂, LinearMap.zero_apply, smul_zero]
  rwa [map_sub, sub_eq_zero] at this

omit [FiniteDimensional ℝ V₀] in
theorem IsReducedCNStep.apply_eq_of_comp_eq_zero {d₁ : V₁ →ₗ[ℝ] V₂} {d₂ : V₂ →ₗ[ℝ] V₃}
    (hd₂ : d₂ ∘ₗ d₁ = 0) {s : ℝ} {E E' : V₁} {B B' : V₂} (h : IsReducedCNStep d₁ s E E' B B') :
    d₂ B' = d₂ B := by
  have : d₂ (B' - B) = 0 := by
    rw [h.2, map_smul, ← LinearMap.comp_apply, hd₂, LinearMap.zero_apply, smul_zero]
  rwa [map_sub, sub_eq_zero] at this

end ThreeField

/-! ### Crank–Nicolson with inhomogeneous Dirichlet degrees of freedom -/

section DirichletCN

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {V₀ : Submodule ℝ V} {A : V →ₗ[ℝ] V} {s : ℝ}

/-- A CN step with prescribed boundary DOFs `g'` and load `f`, tested against `V₀`. -/
def IsDirichletCNStep (V₀ : Submodule ℝ V) (A : V →ₗ[ℝ] V) (s : ℝ) (f g' u u' : V) : Prop :=
  u' - g' ∈ V₀ ∧ ∀ v ∈ V₀, ⟪u' - u, v⟫ = s * ⟪A (u' + u), v⟫ + ⟪f, v⟫

omit [FiniteDimensional ℝ V] in
theorem eq_zero_of_forall_inner_eq (hA : ∀ w ∈ V₀, s * ⟪A w, w⟫ ≤ 0) {w : V} (hw : w ∈ V₀)
    (h : ∀ v ∈ V₀, ⟪w, v⟫ = s * ⟪A w, v⟫) : w = 0 := by
  have h1 := h w hw
  have h2 := hA w hw
  exact real_inner_self_nonpos.1 (h1 ▸ h2)

omit [FiniteDimensional ℝ V] in
theorem IsDirichletCNStep.unique (hA : ∀ w ∈ V₀, s * ⟪A w, w⟫ ≤ 0) {f g' u u₁ u₂ : V}
    (h₁ : IsDirichletCNStep V₀ A s f g' u u₁) (h₂ : IsDirichletCNStep V₀ A s f g' u u₂) :
    u₁ = u₂ := by
  have hw : u₁ - u₂ ∈ V₀ := by
    have := V₀.sub_mem h₁.1 h₂.1
    rwa [sub_sub_sub_cancel_right] at this
  have := eq_zero_of_forall_inner_eq hA hw fun v hv => by
    have e1 := h₁.2 v hv
    have e2 := h₂.2 v hv
    have i1 : ⟪u₁ - u₂, v⟫ = ⟪u₁ - u, v⟫ - ⟪u₂ - u, v⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have i2 : A (u₁ - u₂) = A (u₁ + u) - A (u₂ + u) := by
      rw [← map_sub]; congr 1; abel
    rw [i1, i2, e1, e2, inner_sub_left]
    ring
  exact sub_eq_zero.1 this

/-- **Well-posedness of the CN scheme with inhomogeneous Dirichlet DOFs**: for every `u`, `g'` and
`f` there is exactly one step `u'`, provided `s ⟪A w, w⟫ ≤ 0` on `V₀`. -/
theorem existsUnique_isDirichletCNStep (hA : ∀ w ∈ V₀, s * ⟪A w, w⟫ ≤ 0) (f g' u : V) :
    ∃! u', IsDirichletCNStep V₀ A s f g' u u' := by
  set Φ : V₀ →ₗ[ℝ] V₀ := V₀.orthogonalProjectionOnto.toLinearMap ∘ₗ
    (LinearMap.id - s • A) ∘ₗ V₀.subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw0 : (w : V) = 0 := eq_zero_of_forall_inner_eq hA w.2 fun v hv => by
      have := congrArg (fun z : V₀ => ⟪(z : V), v⟫) hw
      simp only [Φ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_subtype,
        LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, ZeroMemClass.coe_zero,
        inner_zero_left] at this
      have e := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := V₀) ⟨v, hv⟩
        ((w : V) - s • A w)
      rw [Submodule.coe_inner] at e
      simp only at e
      rw [e, inner_sub_left, real_inner_smul_left] at this
      linarith
    exact Subtype.ext hw0
  have hsurj : Function.Surjective Φ := LinearMap.injective_iff_surjective.1 hinj
  set r : V := u - g' + s • A (g' + u) + f
  obtain ⟨w, hw⟩ := hsurj (V₀.orthogonalProjectionOnto r)
  refine ⟨g' + w, ⟨by simp, fun v hv => ?_⟩, fun u'' h => h.unique hA ⟨by simp, fun v hv => ?_⟩⟩
  · have := congrArg (fun z : V₀ => ⟪(z : V), v⟫) hw
    simp only [Φ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_subtype,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply] at this
    have e1 := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := V₀) ⟨v, hv⟩
      ((w : V) - s • A w)
    have e2 := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := V₀) ⟨v, hv⟩ r
    rw [Submodule.coe_inner] at e1 e2
    simp only at e1 e2
    rw [e1, e2] at this
    simp only [r, inner_sub_left, inner_add_left, real_inner_smul_left, map_add] at this ⊢
    linarith
  · -- `g' + w` is itself a step, so `h.unique` applies
    have := congrArg (fun z : V₀ => ⟪(z : V), v⟫) hw
    simp only [Φ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_subtype,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply] at this
    have e1 := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := V₀) ⟨v, hv⟩
      ((w : V) - s • A w)
    have e2 := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := V₀) ⟨v, hv⟩ r
    rw [Submodule.coe_inner] at e1 e2
    simp only at e1 e2
    rw [e1, e2] at this
    simp only [r, inner_sub_left, inner_add_left, real_inner_smul_left, map_add] at this ⊢
    linarith

omit [FiniteDimensional ℝ V] in
theorem IsDirichletCNStep.norm_sub_le (hA : ∀ w ∈ V₀, s * ⟪A w, w⟫ ≤ 0) {f g' u u' ũ ũ' τ : V}
    (h : IsDirichletCNStep V₀ A s f g' u u') (hũ' : ũ' - g' ∈ V₀) (hu : u - ũ ∈ V₀)
    (hτ : ∀ v ∈ V₀, ⟪ũ' - ũ, v⟫ = s * ⟪A (ũ' + ũ), v⟫ + ⟪f, v⟫ + ⟪τ, v⟫) :
    ‖u' - ũ'‖ ≤ ‖u - ũ‖ + ‖τ‖ := by
  set e := u - ũ
  set e' := u' - ũ'
  have he' : e' ∈ V₀ := by
    have := V₀.sub_mem h.1 hũ'
    rwa [sub_sub_sub_cancel_right] at this
  have hw : e' + e ∈ V₀ := V₀.add_mem he' hu
  have key : ⟪e' - e, e' + e⟫ = s * ⟪A (e' + e), e' + e⟫ - ⟪τ, e' + e⟫ := by
    have e1 := h.2 _ hw
    have e2 := hτ _ hw
    have : e' - e = (u' - u) - (ũ' - ũ) := by simp only [e, e']; abel
    rw [this, inner_sub_left, e1, e2, show e' + e = (u' + u) - (ũ' + ũ) by simp only [e, e']; abel,
      map_sub, inner_sub_left]
    ring
  have hsq : ⟪e' - e, e' + e⟫ = ‖e'‖ ^ 2 - ‖e‖ ^ 2 := real_inner_sub_add e' e
  have hτb : -⟪τ, e' + e⟫ ≤ ‖τ‖ * (‖e'‖ + ‖e‖) := by
    have := abs_real_inner_le_norm τ (e' + e)
    have := norm_add_le e' e
    nlinarith [abs_le.1 (abs_real_inner_le_norm τ (e' + e)), norm_nonneg τ]
  have h1 : ‖e'‖ ^ 2 - ‖e‖ ^ 2 ≤ ‖τ‖ * (‖e'‖ + ‖e‖) := by
    have := hA _ hw
    linarith
  have ha := norm_nonneg e'
  have hb := norm_nonneg e
  have hc := norm_nonneg τ
  nlinarith

omit [FiniteDimensional ℝ V] in
theorem norm_sub_le_sum_of_isDirichletCNStep (hA : ∀ w ∈ V₀, s * ⟪A w, w⟫ ≤ 0)
    {f g u ũ τ : ℕ → V} (h : ∀ n, IsDirichletCNStep V₀ A s (f n) (g (n + 1)) (u n) (u (n + 1)))
    (hũ : ∀ n, ũ (n + 1) - g (n + 1) ∈ V₀) (h0 : u 0 - ũ 0 ∈ V₀)
    (hτ : ∀ n, ∀ v ∈ V₀, ⟪ũ (n + 1) - ũ n, v⟫ =
      s * ⟪A (ũ (n + 1) + ũ n), v⟫ + ⟪f n, v⟫ + ⟪τ n, v⟫) (N : ℕ) :
    ‖u N - ũ N‖ ≤ ‖u 0 - ũ 0‖ + ∑ n ∈ Finset.range N, ‖τ n‖ := by
  have hmem : ∀ n, u n - ũ n ∈ V₀ := fun n => by
    cases n with
    | zero => exact h0
    | succ n =>
      have := V₀.sub_mem (h n).1 (hũ n)
      rwa [sub_sub_sub_cancel_right] at this
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := (h N).norm_sub_le hA (hũ N) (hmem N) (hτ N)
    linarith

omit [FiniteDimensional ℝ V] in
theorem norm_residual_le_of_isDirichletCNStep {W : Type*} [SeminormedAddCommGroup W]
    [NormedSpace ℝ W] (c : V →ₗ[ℝ] W) {C : ℝ} (hc : ∀ x, ‖c x‖ ≤ C * ‖x‖) (hC : 0 ≤ C)
    (hA : ∀ w ∈ V₀, s * ⟪A w, w⟫ ≤ 0)
    {f g u ũ τ : ℕ → V} (h : ∀ n, IsDirichletCNStep V₀ A s (f n) (g (n + 1)) (u n) (u (n + 1)))
    (hũ : ∀ n, ũ (n + 1) - g (n + 1) ∈ V₀) (h0 : u 0 - ũ 0 ∈ V₀)
    (hτ : ∀ n, ∀ v ∈ V₀, ⟪ũ (n + 1) - ũ n, v⟫ =
      s * ⟪A (ũ (n + 1) + ũ n), v⟫ + ⟪f n, v⟫ + ⟪τ n, v⟫) (N : ℕ) :
    ‖c (u N)‖ ≤ ‖c (ũ N)‖ + C * (‖u 0 - ũ 0‖ + ∑ n ∈ Finset.range N, ‖τ n‖) := by
  have e : c (u N) = c (ũ N) + c (u N - ũ N) := by rw [map_sub]; abel
  rw [e]
  have h1 := (hc (u N - ũ N)).trans (mul_le_mul_of_nonneg_left
    (norm_sub_le_sum_of_isDirichletCNStep hA h hũ h0 hτ N) hC)
  linarith [norm_add_le (c (ũ N)) (c (u N - ũ N))]

end DirichletCN

end Feec.TimeStepping
