module

public import Feec.TimeStepping.Cayley
public import Feec.Semigroup.DissipativeInvariance

/-!
# θ-schemes through resolvents, and products of them

For the evolution `u' = A u`, `A : E →ₗ.[𝕜] E` on a Hilbert space, a time step `τ` and `θ : 𝕜`,
a **θ-step** `u ↦ u'` is `u' - u = τ A (θ u' + (1 - θ) u)` with `θ u' + (1 - θ) u ∈ D(A)`
(`IsThetaStep`): the one-step scheme of the rational function
`r_θ(z) = (1 + (1 - θ) z) / (1 - θ z)`, `r_θ(τ A) = θ⁻¹ (1 - θ τ A)⁻¹ - (1 - θ) / θ`, defined
through the resolvent `R(z) = (z - A)⁻¹` at `z = (θ τ)⁻¹` (`thetaStep`) for every possibly
unbounded `A`. `θ = 1` is implicit Euler (`thetaStep_one`), `θ = 1/2` is Crank–Nicolson:
**`cayley_eq_thetaStep`**: the Cayley transform `cayley A s` of `Feec.TimeStepping.Cayley` is
`thetaStep A (1/2) (2 s)` (`cayley_half_eq_thetaStep`: Crank–Nicolson with step `τ` is
`r_{1/2}(τ A)`), and `isCNStep_iff_isThetaStep`; the `fem4gr` step without boundary degrees of
freedom is the CN step (`isDirichletCNStep_top_iff`). The Crank–Nicolson results of
`Feec.TimeStepping.Cayley` (`IsCNStep.norm_le`, `IsCNStep.norm_eq`, `IsCNStep.mem_of_isReducing`,
`norm_cayley_apply`) are the `θ = 1/2` cases of `IsThetaStep.norm_le`, `IsThetaStep.norm_eq`,
`thetaStep_mem_of_isReducing` and `norm_thetaStep_apply_eq` through these bridges; they stay in
`Cayley`, which this file imports (and which the `fem4gr` three-field schemes use).

## Main results

* `IsThetaStep.norm_sq_eq`: the **discrete energy identity**
  `‖u'‖² = ‖u‖² + 2 τ re ⟪A w, w⟫ - (2 re θ - 1) ‖u' - u‖²`, `w = θ u' + (1 - θ) u`;
* `IsThetaStep.norm_le`: **unconditional stability**, `‖u'‖ ≤ ‖u‖` for dissipative `A`,
  `re θ ≥ 1/2` (A-stability of `r_θ`), `τ ≥ 0`; `IsThetaStep.norm_eq`: energy conservation for
  skew-symmetric `A` and `re θ = 1/2`;
* `LinearPMap.IsMDissipative.isResolvent_of_re_pos`: an m-dissipative operator has a resolvent
  at every `z` with `re z > 0` (so `thetaStep` is a θ-step for every `re θ > 0`, `τ > 0`,
  `isThetaStep_thetaStep_of_isMDissipative`);
* `norm_thetaStep_le`: `‖r_θ(τ A)‖ ≤ 1` for m-dissipative `A`, `re θ ≥ 1/2`, `τ > 0`, **uniformly
  in `A`**: the constant does not see `A`, so it applies to every discrete generator `Lₕ` at
  once; `norm_thetaStep_apply_eq`: `r_θ(τ A)` is an isometry for skew-adjoint `A`, `re θ = 1/2`
  and every `τ ≠ 0` (generalizing `norm_cayley_apply`);
* **discrete constraint propagation**: `thetaStep_mem` (a subspace invariant under the resolvent
  `R((θ τ)⁻¹)` is invariant under the step), `IsResolvent.apply_mem_of_isReducing` and
  `thetaStep_mem_of_isReducing` (reducing subspaces, every `re θ > 0`), and
  `thetaStep_mem_of_keeps` (real `θ > 0`: a closed subspace kept by the exact semigroup is kept
  by the scheme, through the resolvent criterion `IsMDissipative.invariant_iff_resolvent`);
* **products of θ-substeps** `splitStep σ τ = ∏ᵢ r_{θᵢ}(cᵢ τ Aᵢ)`: with one operator these are the
  rational schemes `r = ∏ᵢ r_{θᵢ}(cᵢ ·)` (for instance the order-four Padé scheme
  `(1 + z/2 + z²/12)/(1 - z/2 + z²/12) = r_θ(z/2) r_θ̄(z/2)`, `θ = (1 + i/√3)/2`, over `ℂ`); with
  several, operator splittings (Lie, Strang). `norm_splitStep_le`: they are contractions when every
  `Aᵢ` is m-dissipative, `re θᵢ ≥ 1/2` and `cᵢ > 0`; `splitStep_mem_of_isReducing`: they keep a
  subspace reducing every `Aᵢ`.

On a Hilbert space, A-stability of a real rational `r` (`|r| ≤ 1` on `re z ≤ 0`) gives
`‖r(τ A)‖ ≤ 1` for every m-dissipative `A` by von Neumann's inequality for the contraction
`(1 + A)(1 - A)⁻¹` (cf. [CrouzeixLarssonPiskarevThomee1993]): this is
`Feec.TimeStepping.RationalScheme.norm_step_le` (`Feec.TimeStepping.Rational`); the product form
above is the part of it obtained from the energy identity of each factor.

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7
  (single step methods, `A`-stability), Ch. 9 (rational approximations through resolvents)
* [M. Crouzeix, S. Larsson, S. Piskarev, V. Thomée, *The stability of rational approximations of analytic semigroups*][CrouzeixLarssonPiskarevThomee1993]
  (stability of A-stable rational approximations of semigroups)
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996],
  §IV.3 (A-stability, Padé approximations of the exponential)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4 (resolvents of m-dissipative operators)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.18 (constraint propagation, here at the discrete level)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Feec.Operator

@[expose] public noncomputable section

namespace Feec.TimeStepping

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {θ : 𝕜} {τ s : ℝ} {u u' : E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Resolvents off the real axis -/

/-- **Resolvents in the right half-plane**: an m-dissipative `A` has a resolvent at every `z`
with `re z > 0`: `z - A = (1 - (μ - z) R(μ)) (μ - A)` with `μ = |z|² / re z`, and
`‖(μ - z) R(μ)‖ ≤ |μ - z| / μ < 1`. [Pazy1983], §1.4 -/
theorem _root_.LinearPMap.IsMDissipative.isResolvent_of_re_pos [CompleteSpace E]
    (hA : A.IsMDissipative) {z : 𝕜} (hz : 0 < RCLike.re z) :
    IsResolvent A z (resolvent A z) := by
  set μ : ℝ := ‖z‖ ^ 2 / RCLike.re z
  have hμz : μ * RCLike.re z = ‖z‖ ^ 2 := div_mul_cancel₀ _ hz.ne'
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => by simp [h] at hz
  have hμ : 0 < μ := div_pos (by positivity) hz
  have hRμ := hA.isResolvent hμ
  set R := resolvent A (μ : 𝕜)
  set T : E →L[𝕜] E := ((μ : 𝕜) - z) • R
  have hT : ‖T‖ < 1 := by
    have h1 : ‖R‖ ≤ μ⁻¹ := hA.norm_resolvent_le hμ
    have hsq : ‖(μ : 𝕜) - z‖ ^ 2 = μ ^ 2 - ‖z‖ ^ 2 := by
      have h2 := RCLike.norm_sq_eq_def (z := z)
      rw [RCLike.norm_sq_eq_def]
      simp only [_root_.map_sub, RCLike.ofReal_re, RCLike.ofReal_im]
      linear_combination (-2) * hμz - h2
    have hlt : ‖(μ : 𝕜) - z‖ < μ := by
      have : ‖(μ : 𝕜) - z‖ ^ 2 < μ ^ 2 := by rw [hsq]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hμ.le this
    calc ‖T‖ ≤ ‖(μ : 𝕜) - z‖ * μ⁻¹ := by rw [norm_smul]; gcongr
      _ < μ * μ⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hμ.ne'
  set U := Units.oneSub T hT
  have hU : ∀ y, (↑U⁻¹ : E →L[𝕜] E) y - T ((↑U⁻¹ : E →L[𝕜] E) y) = y := fun y => by
    have h := congrArg (fun C : E →L[𝕜] E => C y) U.mul_inv
    simpa [U, Units.val_oneSub] using h
  have hU' : ∀ y, (↑U⁻¹ : E →L[𝕜] E) (y - T y) = y := fun y => by
    have h := congrArg (fun C : E →L[𝕜] E => C y) U.inv_mul
    simpa [U, Units.val_oneSub] using h
  have hR' : IsResolvent A z (R * ↑U⁻¹) :=
    { mem_domain := fun y => hRμ.mem_domain _
      sub_apply := fun y => by
        have h := hRμ.apply_resolvent ((↑U⁻¹ : E →L[𝕜] E) y)
        change z • R ((↑U⁻¹ : E →L[𝕜] E) y) - A (hRμ.toDomain ((↑U⁻¹ : E →L[𝕜] E) y)) = y
        rw [h]
        conv_rhs => rw [← hU y]
        simp only [T, _root_.smul_apply]
        module
      apply_sub := fun x => by
        have e : z • (x : E) - A x =
            ((μ : 𝕜) • (x : E) - A x) - T ((μ : 𝕜) • (x : E) - A x) := by
          simp only [T, _root_.smul_apply]
          rw [hRμ.apply_sub]
          module
        change R ((↑U⁻¹ : E →L[𝕜] E) _) = _
        rw [e, hU', hRμ.apply_sub] }
  exact hR'.isResolvent_resolvent

/-! ### θ-steps -/

/-- `u'` is a **θ-step** from `u` for `u' = A u` with time step `τ`: `θ u' + (1 - θ) u ∈ D(A)`
and `u' - u = τ A (θ u' + (1 - θ) u)`. [Thomee2006], Ch. 7 -/
def IsThetaStep (A : E →ₗ.[𝕜] E) (θ : 𝕜) (τ : ℝ) (u u' : E) : Prop :=
  ∃ h : θ • u' + (1 - θ) • u ∈ A.domain, u' - u = (τ : 𝕜) • A ⟨θ • u' + (1 - θ) • u, h⟩

/-- The **θ-scheme** `r_θ(τ A) = (1 + (1 - θ) τ A)(1 - θ τ A)⁻¹ = (θ² τ)⁻¹ R((θ τ)⁻¹) - (1 - θ)/θ`
of `r_θ(z) = (1 + (1 - θ) z) / (1 - θ z)`, through the resolvent `R(z) = (z - A)⁻¹`.
[Thomee2006], Ch. 7 -/
def thetaStep (A : E →ₗ.[𝕜] E) (θ : 𝕜) (τ : ℝ) : E →L[𝕜] E :=
  (θ ^ 2 * (τ : 𝕜))⁻¹ • resolvent A (θ * (τ : 𝕜))⁻¹ - ((1 - θ) / θ) • 1

/-- **Crank–Nicolson is the θ-scheme with `θ = 1/2`**: the Cayley transform with half step `s`
is `r_{1/2}(2 s A)`. -/
theorem cayley_eq_thetaStep (A : E →ₗ.[𝕜] E) (s : ℝ) :
    cayley A s = thetaStep A (1 / 2) (2 * s) := by
  unfold cayley thetaStep
  push_cast
  congr 2
  · ring
  · ring_nf
  · norm_num

/-- Crank–Nicolson with time step `τ` (half step `τ/2`) is `r_{1/2}(τ A)`. -/
theorem cayley_half_eq_thetaStep (A : E →ₗ.[𝕜] E) (τ : ℝ) :
    cayley A (τ / 2) = thetaStep A ((1 / 2 : ℝ) : 𝕜) τ := by
  rw [cayley_eq_thetaStep, show 2 * (τ / 2) = τ by ring]
  congr 1; push_cast; ring

/-- **Implicit Euler is the θ-scheme with `θ = 1`**: `r_1(τ A) = (1 - τ A)⁻¹ = τ⁻¹ R(τ⁻¹)`. -/
theorem thetaStep_one (A : E →ₗ.[𝕜] E) (τ : ℝ) :
    thetaStep A 1 τ = ((τ : 𝕜))⁻¹ • resolvent A ((τ : 𝕜))⁻¹ := by
  simp [thetaStep]

/-- A CN step with half step `s` is a θ-step with `θ = 1/2`, `τ = 2 s`. -/
theorem isCNStep_iff_isThetaStep :
    IsCNStep A s u u' ↔ IsThetaStep A (1 / 2) (2 * s) u u' := by
  have hw : (1 / 2 : 𝕜) • u' + (1 - 1 / 2 : 𝕜) • u = (1 / 2 : 𝕜) • (u' + u) := by module
  constructor
  · rintro ⟨h, e⟩
    have hm : (1 / 2 : 𝕜) • u' + (1 - 1 / 2 : 𝕜) • u ∈ A.domain := hw ▸ A.domain.smul_mem _ h
    refine ⟨hm, ?_⟩
    have : A ⟨_, hm⟩ = (1 / 2 : 𝕜) • A ⟨u' + u, h⟩ := by
      rw [← A.map_smul]; congr 1; exact Subtype.ext hw
    rw [this, smul_smul, e]; push_cast; congr 1; ring
  · rintro ⟨hm, e⟩
    have h : u' + u ∈ A.domain := by
      have := A.domain.smul_mem (2 : 𝕜) hm
      rwa [hw, smul_smul, show (2 : 𝕜) * (1 / 2) = 1 by norm_num, one_smul] at this
    refine ⟨h, ?_⟩
    have : A ⟨_, hm⟩ = (1 / 2 : 𝕜) • A ⟨u' + u, h⟩ := by
      rw [← A.map_smul]; congr 1; exact Subtype.ext hw
    rw [e, this, smul_smul]; push_cast; congr 1; ring

omit [InnerProductSpace 𝕜 E] in
open scoped RealInnerProductSpace in
/-- **The `fem4gr` step without boundary degrees of freedom is Crank–Nicolson**: with `V₀ = ⊤`
and no load, the Dirichlet CN step `IsDirichletCNStep` is the CN step of `A` (hence the θ-step
with `θ = 1/2`, `isCNStep_iff_isThetaStep`). -/
theorem isDirichletCNStep_top_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {A : V →ₗ[ℝ] V} {g' w w' : V} :
    IsDirichletCNStep ⊤ A s 0 g' w w' ↔ IsCNStep (A.toPMap ⊤) s w w' := by
  constructor
  · rintro ⟨_, h⟩
    refine ⟨trivial, ext_inner_right ℝ fun v => ?_⟩
    rw [h v trivial, inner_zero_left, add_zero, real_inner_smul_left]
    rfl
  · rintro ⟨_, h⟩
    refine ⟨trivial, fun v _ => ?_⟩
    rw [h, inner_zero_left, add_zero, RCLike.ofReal_real_eq_id, id, real_inner_smul_left]
    rfl

/-- `r_θ(τ A) u` is a θ-step from `u` whenever `R((θ τ)⁻¹)` exists (`θ ≠ 0`, `τ ≠ 0`).
[Thomee2006], Ch. 7 -/
theorem isThetaStep_thetaStep {R : E →L[𝕜] E} (hR : IsResolvent A (θ * (τ : 𝕜))⁻¹ R)
    (hθ : θ ≠ 0) (hτ : τ ≠ 0) (u : E) : IsThetaStep A θ τ u (thetaStep A θ τ u) := by
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ
  set r := hR.toDomain u
  have hr : (θ * (τ : 𝕜))⁻¹ • (r : E) - A r = u := hR.sub_apply_toDomain u
  have hw : θ • thetaStep A θ τ u + (1 - θ) • u = (θ * (τ : 𝕜))⁻¹ • (r : E) := by
    simp only [thetaStep, hR.resolvent_eq, _root_.sub_apply,
      _root_.smul_apply, one_apply_eq_self, smul_sub, smul_smul, r,
      IsResolvent.coe_toDomain]
    rw [show θ * (θ ^ 2 * (τ : 𝕜))⁻¹ = (θ * (τ : 𝕜))⁻¹ by field_simp,
      show θ * ((1 - θ) / θ) = 1 - θ by field_simp]
    abel
  refine ⟨hw ▸ A.domain.smul_mem _ r.2, ?_⟩
  have hA : A ⟨_, hw ▸ A.domain.smul_mem _ r.2⟩ = (θ * (τ : 𝕜))⁻¹ • A r := by
    rw [← A.map_smul]; congr 1; exact Subtype.ext hw
  rw [hA, smul_smul, show (τ : 𝕜) * (θ * (τ : 𝕜))⁻¹ = θ⁻¹ by field_simp]
  have e : A r = (θ * (τ : 𝕜))⁻¹ • (r : E) - u := by rw [← hr]; abel
  rw [e]
  simp only [thetaStep, hR.resolvent_eq, _root_.sub_apply,
    _root_.smul_apply, one_apply_eq_self, r, IsResolvent.coe_toDomain]
  rw [smul_sub, smul_smul, show θ⁻¹ * (θ * (τ : 𝕜))⁻¹ = (θ ^ 2 * (τ : 𝕜))⁻¹ by field_simp]
  have : ((1 - θ) / θ) • u + u = θ⁻¹ • u := by
    rw [← one_smul 𝕜 u, smul_smul, ← add_smul, mul_one, one_smul]
    congr 1; field_simp; ring
  rw [← this]; abel

/-- `‖w + (1 - θ) d‖² = ‖w - θ d‖² + 2 re ⟪w, d⟫ - (2 re θ - 1) ‖d‖²`. -/
private theorem norm_sq_add_smul (w d : E) (θ : 𝕜) :
    ‖w + (1 - θ) • d‖ ^ 2 =
      ‖w - θ • d‖ ^ 2 + 2 * RCLike.re ⟪w, d⟫ - (2 * RCLike.re θ - 1) * ‖d‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜), inner_smul_right, inner_smul_right, norm_smul,
    norm_smul, mul_pow, mul_pow]
  have h1 : ‖(1 : 𝕜) - θ‖ ^ 2 = 1 - 2 * RCLike.re θ + ‖θ‖ ^ 2 := by
    rw [RCLike.norm_sq_eq_def, RCLike.norm_sq_eq_def]
    simp only [_root_.map_sub, RCLike.one_re, RCLike.one_im]
    ring
  have h2 : RCLike.re ((1 - θ) * ⟪w, d⟫) = RCLike.re ⟪w, d⟫ - RCLike.re (θ * ⟪w, d⟫) := by
    rw [sub_mul, one_mul, _root_.map_sub]
  rw [h1, h2]
  ring

/-- **The discrete energy identity of a θ-step**: with `w = θ u' + (1 - θ) u`,
`‖u'‖² = ‖u‖² + 2 τ re ⟪A w, w⟫ - (2 re θ - 1) ‖u' - u‖²`: the dissipation of `A` plus the
numerical dissipation `(2 re θ - 1) ‖u' - u‖²` of the scheme. [Thomee2006], Ch. 7 -/
theorem IsThetaStep.norm_sq_eq (h : IsThetaStep A θ τ u u') :
    ‖u'‖ ^ 2 = ‖u‖ ^ 2 + 2 * τ * RCLike.re ⟪A ⟨_, h.1⟩, θ • u' + (1 - θ) • u⟫ -
      (2 * RCLike.re θ - 1) * ‖u' - u‖ ^ 2 := by
  obtain ⟨hm, e⟩ := h
  set w := θ • u' + (1 - θ) • u
  have h1 : u' = w + (1 - θ) • (u' - u) := by simp only [w]; module
  have h2 : u = w - θ • (u' - u) := by simp only [w]; module
  have h3 := norm_sq_add_smul w (u' - u) θ
  rw [← h1, ← h2] at h3
  rw [h3]
  have : RCLike.re ⟪w, u' - u⟫ = τ * RCLike.re ⟪A ⟨w, hm⟩, w⟫ := by
    rw [e, inner_smul_right, RCLike.re_ofReal_mul, inner_re_symm]
  rw [this]; ring

/-- **Unconditional stability of the θ-scheme** (A-stability, `re θ ≥ 1/2`): a θ-step of a
dissipative operator with `τ ≥ 0` does not increase the norm. [Thomee2006], Ch. 7 -/
theorem IsThetaStep.norm_le (hA : A.IsDissipative) (hθ : 1 / 2 ≤ RCLike.re θ) (hτ : 0 ≤ τ)
    (h : IsThetaStep A θ τ u u') : ‖u'‖ ≤ ‖u‖ := by
  have e := h.norm_sq_eq
  have h1 : τ * RCLike.re ⟪A ⟨_, h.1⟩, θ • u' + (1 - θ) • u⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hτ (hA _)
  have h2 : 0 ≤ (2 * RCLike.re θ - 1) * ‖u' - u‖ ^ 2 := by
    apply mul_nonneg <;> [linarith; positivity]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- **Energy conservation of the θ-scheme** for skew-symmetric `A` and `re θ = 1/2` (every
`τ`). [Thomee2006], Ch. 7 -/
theorem IsThetaStep.norm_eq (hA : A.IsSkewSymmetric) (hθ : RCLike.re θ = 1 / 2)
    (h : IsThetaStep A θ τ u u') : ‖u'‖ = ‖u‖ := by
  have e := h.norm_sq_eq
  rw [hA.re_inner_self, hθ] at e
  have : ‖u'‖ ^ 2 = ‖u‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-- `re (θ τ)⁻¹ > 0` for `re θ > 0`, `τ > 0`. -/
theorem re_inv_mul_pos (hθ : 0 < RCLike.re θ) (hτ : 0 < τ) :
    0 < RCLike.re (θ * (τ : 𝕜))⁻¹ := by
  have hne : θ * (τ : 𝕜) ≠ 0 :=
    mul_ne_zero (fun h => by simp [h] at hθ) (RCLike.ofReal_ne_zero.2 hτ.ne')
  rw [RCLike.inv_re, RCLike.re_mul_ofReal]
  exact div_pos (mul_pos hθ hτ) (RCLike.normSq_pos.2 hne)

variable [CompleteSpace E]

/-- For m-dissipative `A`, `re θ > 0` and `τ > 0`, `r_θ(τ A) u` is a θ-step. -/
theorem isThetaStep_thetaStep_of_isMDissipative (hA : A.IsMDissipative) (hθ : 0 < RCLike.re θ)
    (hτ : 0 < τ) (u : E) : IsThetaStep A θ τ u (thetaStep A θ τ u) :=
  isThetaStep_thetaStep (hA.isResolvent_of_re_pos (re_inv_mul_pos hθ hτ))
    (fun h => by simp [h] at hθ) hτ.ne' u

/-- **Stability uniformly in the generator**: `‖r_θ(τ A) u‖ ≤ ‖u‖` for every m-dissipative `A`,
`re θ ≥ 1/2` and `τ > 0`. [Thomee2006], Ch. 7; [CrouzeixLarssonPiskarevThomee1993] -/
theorem norm_thetaStep_apply_le (hA : A.IsMDissipative) (hθ : 1 / 2 ≤ RCLike.re θ)
    (hτ : 0 < τ) (u : E) : ‖thetaStep A θ τ u‖ ≤ ‖u‖ :=
  (isThetaStep_thetaStep_of_isMDissipative hA (by linarith) hτ u).norm_le hA.dissipative hθ
    hτ.le

/-- `‖r_θ(τ A)‖ ≤ 1` for every m-dissipative `A`, `re θ ≥ 1/2`, `τ > 0`. -/
theorem norm_thetaStep_le (hA : A.IsMDissipative) (hθ : 1 / 2 ≤ RCLike.re θ) (hτ : 0 < τ) :
    ‖thetaStep A θ τ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_thetaStep_apply_le hA hθ hτ u

/-! ### The Cayley transform of an m-dissipative operator -/

private theorem re_half : RCLike.re (1 / 2 : 𝕜) = 1 / 2 := by
  rw [show (1 / 2 : 𝕜) = ((1 / 2 : ℝ) : 𝕜) by push_cast; ring, RCLike.ofReal_re]

/-- For m-dissipative `A` and `s > 0`, `cayley A s u` is the CN step from `u`. -/
theorem _root_.LinearPMap.IsMDissipative.isCNStep_cayley (hA : A.IsMDissipative) (hs : 0 < s)
    (u : E) : IsCNStep A s u (cayley A s u) := by
  rw [isCNStep_iff_isThetaStep, cayley_eq_thetaStep]
  exact isThetaStep_thetaStep_of_isMDissipative hA (by rw [re_half]; norm_num) (by linarith) u

/-- **The Cayley transform of an m-dissipative operator is a contraction**: `‖cayley A s‖ ≤ 1`
for `s > 0`. -/
theorem norm_cayley_le (hA : A.IsMDissipative) (hs : 0 < s) : ‖cayley A s‖ ≤ 1 := by
  rw [cayley_eq_thetaStep]
  exact norm_thetaStep_le hA (by rw [re_half]) (by linarith)

/-- **The Cayley transform maps `x - s A x` to `x + s A x`** for m-dissipative `A`, `s > 0`. -/
theorem cayley_sub_smul (hA : A.IsMDissipative) (hs : 0 < s) (x : A.domain) :
    cayley A s ((x : E) - (s : 𝕜) • A x) = x + (s : 𝕜) • A x := by
  have h2 : (x : E) + (s : 𝕜) • A x + ((x : E) - (s : 𝕜) • A x) = (2 : 𝕜) • (x : E) := by
    module
  have hm : (x : E) + (s : 𝕜) • A x + ((x : E) - (s : 𝕜) • A x) ∈ A.domain :=
    h2 ▸ A.domain.smul_mem _ x.2
  have hstep : IsCNStep A s ((x : E) - (s : 𝕜) • A x) (x + (s : 𝕜) • A x) := by
    refine ⟨hm, ?_⟩
    have : A ⟨_, hm⟩ = (2 : 𝕜) • A x :=
      (congrArg A (Subtype.ext h2 : (⟨_, hm⟩ : A.domain) = (2 : 𝕜) • x)).trans (A.map_smul _ _)
    rw [this]; module
  exact (hA.isCNStep_cayley hs _).unique hA.dissipative hs.le hstep

/-- **The Cayley transform is the only operator mapping `x - s A x` to `x + s A x`**, for
m-dissipative `A` and `s > 0` (`1 - s A` is onto). -/
theorem eq_cayley_of_apply_sub_smul (hA : A.IsMDissipative) (hs : 0 < s) {T : E →L[𝕜] E}
    (hT : ∀ x : A.domain, T ((x : E) - (s : 𝕜) • A x) = x + (s : 𝕜) • A x) : T = cayley A s := by
  ext u
  obtain ⟨hw, e⟩ := hA.isCNStep_cayley hs u
  set x : A.domain := (2 : 𝕜)⁻¹ • ⟨_, hw⟩
  have hAx : A x = (2 : 𝕜)⁻¹ • A ⟨_, hw⟩ := A.map_smul _ _
  have hx : (x : E) = (2 : 𝕜)⁻¹ • (cayley A s u + u) := rfl
  have h1 : (x : E) - (s : 𝕜) • A x = u := by
    rw [hAx, hx, smul_comm, ← e]; module
  have h2 : (x : E) + (s : 𝕜) • A x = cayley A s u := by
    rw [hAx, hx, smul_comm, ← e]; module
  rw [← h1, hT, h2, h1]

/-- **The θ-scheme with `re θ = 1/2` is an isometry** for skew-adjoint `A` and every `τ ≠ 0`
(both time directions); for `θ = 1/2` this is `norm_cayley_apply`. -/
theorem norm_thetaStep_apply_eq (hA : A.IsSkewAdjoint) (hθ : RCLike.re θ = 1 / 2) (hτ : τ ≠ 0)
    (u : E) : ‖thetaStep A θ τ u‖ = ‖u‖ := by
  have hθ0 : θ ≠ 0 := fun h => by simp [h] at hθ
  have hne : θ * (τ : 𝕜) ≠ 0 := mul_ne_zero hθ0 (RCLike.ofReal_ne_zero.2 hτ)
  have hre : RCLike.re (θ * (τ : 𝕜))⁻¹ ≠ 0 := by
    rw [RCLike.inv_re, RCLike.re_mul_ofReal, hθ]
    exact div_ne_zero (mul_ne_zero (by norm_num) hτ) (RCLike.normSq_pos.2 hne).ne'
  exact (isThetaStep_thetaStep (Operator.isResolvent_resolvent hA hre) hθ0 hτ u).norm_eq
    hA.isSkewSymmetric hθ

/-! ### Discrete constraint propagation -/

omit [CompleteSpace E] in
/-- **A subspace invariant under the resolvent is invariant under the θ-scheme.** -/
theorem thetaStep_mem {K : Submodule 𝕜 E} (hK : ∀ y ∈ K, resolvent A (θ * (τ : 𝕜))⁻¹ y ∈ K)
    (hu : u ∈ K) : thetaStep A θ τ u ∈ K := by
  simp only [thetaStep, _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self]
  exact K.sub_mem (K.smul_mem _ (hK u hu)) (K.smul_mem _ hu)

omit [CompleteSpace E] in
/-- **Resolvents keep reducing subspaces**: if `K` reduces `A`, `R K ⊆ K` for every resolvent
`R` of `A` (`P_K R y` solves `(z - A) x = P_K y`). -/
theorem _root_.Feec.Operator.IsResolvent.apply_mem_of_isReducing {z : 𝕜} {R : E →L[𝕜] E}
    (hR : IsResolvent A z R) {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (hK : A.IsReducing K) {y : E} (hy : y ∈ K) : R y ∈ K := by
  set x := hR.toDomain y
  have key : z • (x : E) - A x = y := hR.sub_apply_toDomain y
  have hPx : z • K.starProjection (x : E) - A ⟨_, hK.proj_mem x⟩ = y := by
    rw [hK.comm x, ← ContinuousLinearMap.map_smul, ← _root_.map_sub, key,
      (K.starProjection_eq_self_iff).2 hy]
  have h2 : R (z • K.starProjection (x : E) - A ⟨_, hK.proj_mem x⟩) = K.starProjection x :=
    hR.apply_sub ⟨_, hK.proj_mem x⟩
  rw [hPx] at h2
  rw [h2]
  exact K.starProjection_apply_mem _

/-- **Discrete constraint propagation for reducing subspaces**: if `K` reduces the m-dissipative
`A`, `r_θ(τ A) K ⊆ K` (`re θ > 0`, `τ > 0`); for `θ = 1/2` cf. `IsCNStep.mem_of_isReducing`.
[QuennevilleBelair2015], Prop 4.18 -/
theorem thetaStep_mem_of_isReducing (hA : A.IsMDissipative) (hθ : 0 < RCLike.re θ) (hτ : 0 < τ)
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] (hK : A.IsReducing K) (hu : u ∈ K) :
    thetaStep A θ τ u ∈ K :=
  thetaStep_mem (fun _ hy =>
    (hA.isResolvent_of_re_pos (re_inv_mul_pos hθ hτ)).apply_mem_of_isReducing hK hy) hu

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Discrete constraint propagation for kept subspaces** (real `θ > 0`, `τ > 0`): a closed
subspace kept by the exact semigroup, `S(t) K ⊆ K` for `t ≥ 0`, is kept by the θ-scheme (the
resolvents keep `K`, `IsMDissipative.invariant_iff_resolvent`). [QuennevilleBelair2015],
Prop 4.18 -/
theorem thetaStep_mem_of_keeps (hA : A.IsMDissipative) {K : Submodule 𝕜 E}
    (hKc : IsClosed (K : Set E)) (hK : ∀ t, 0 ≤ t → ∀ x ∈ K, hA.semigroup.S t x ∈ K) {θ : ℝ}
    (hθ : 0 < θ) (hτ : 0 < τ) (hu : u ∈ K) : thetaStep A (θ : 𝕜) τ u ∈ K := by
  refine thetaStep_mem (fun y hy => ?_) hu
  have := (hA.invariant_iff_resolvent hKc).1 hK (θ * τ)⁻¹ (by positivity) y hy
  simpa using this

/-! ### Products of θ-substeps: composite rational schemes and splittings -/

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] in
/-- A **product of θ-substeps** `∏ᵢ r_{θᵢ}(cᵢ τ Aᵢ)` for a list `σ` of triples `(Aᵢ, θᵢ, cᵢ)`
(the first entry is applied last): with one operator, the rational scheme
`r(z) = ∏ᵢ r_{θᵢ}(cᵢ z)`; with several, an operator splitting (Lie: `[(A₂, 1, 1), (A₁, 1, 1)]`;
Strang–Crank–Nicolson: `[(A₁, 1/2, 1/2), (A₂, 1/2, 1), (A₁, 1/2, 1/2)]`). [HairerWanner1996],
§IV.3; [Thomee2006], Ch. 9 -/
def splitStep (σ : List ((E →ₗ.[𝕜] E) × 𝕜 × ℝ)) (τ : ℝ) : E →L[𝕜] E :=
  (σ.map fun p => thetaStep p.1 p.2.1 (p.2.2 * τ)).prod

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **Products of A-stable θ-substeps of m-dissipative operators are contractions**:
`‖∏ᵢ r_{θᵢ}(cᵢ τ Aᵢ)‖ ≤ 1` when every `Aᵢ` is m-dissipative, `re θᵢ ≥ 1/2`, `cᵢ > 0`, `τ > 0`. -/
theorem norm_splitStep_le {σ : List ((E →ₗ.[𝕜] E) × 𝕜 × ℝ)}
    (hσ : ∀ p ∈ σ, p.1.IsMDissipative ∧ 1 / 2 ≤ RCLike.re p.2.1 ∧ 0 < p.2.2) (hτ : 0 < τ) :
    ‖splitStep σ τ‖ ≤ 1 := by
  induction σ with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons p σ ih =>
    have hp := hσ p (List.mem_cons_self ..)
    simp only [splitStep, List.map_cons, List.prod_cons] at ih ⊢
    refine (norm_mul_le _ _).trans ?_
    have h1 := norm_thetaStep_le hp.1 hp.2.1 (mul_pos hp.2.2 hτ)
    have h2 := ih fun q hq => hσ q (List.mem_cons_of_mem _ hq)
    nlinarith [norm_nonneg (thetaStep p.1 p.2.1 (p.2.2 * τ)),
      norm_nonneg (σ.map fun p => thetaStep p.1 p.2.1 (p.2.2 * τ)).prod]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **Products of θ-substeps keep a subspace reducing every substep's operator**. -/
theorem splitStep_mem_of_isReducing {σ : List ((E →ₗ.[𝕜] E) × 𝕜 × ℝ)}
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (hσ : ∀ p ∈ σ, p.1.IsMDissipative ∧ 0 < RCLike.re p.2.1 ∧ 0 < p.2.2 ∧ p.1.IsReducing K)
    (hτ : 0 < τ) (hu : u ∈ K) : splitStep σ τ u ∈ K := by
  induction σ generalizing u with
  | nil => simpa [splitStep] using hu
  | cons p σ ih =>
    have hp := hσ p (List.mem_cons_self ..)
    simp only [splitStep, List.map_cons, List.prod_cons] at ih ⊢
    exact thetaStep_mem_of_isReducing hp.1 hp.2.1 (mul_pos hp.2.2.1 hτ) hp.2.2.2
      (ih (fun q hq => hσ q (List.mem_cons_of_mem _ hq)) hu)

end Feec.TimeStepping
