module

public import Solution.Bridge

/-!
# Von Neumann's inequality and A-stable time stepping (solution)

The theorems of `Challenge.lean`, proved from `Feec` through the bridge `Solution.Bridge`, which
passes from the real bounds of `Feec` to the suprema in `[0, ∞]` (`VonNeumann.enorm_le_iSup`,
`VonNeumann.enorm_pow_le_iSup_pow`): von Neumann's inequality from
`ContinuousLinearMap.norm_aeval_le_of_norm_le_one`, its rational form from
`ContinuousLinearMap.norm_aeval_mul_inverse_le`, the real dissipative forms from
`Feec.TimeStepping.RationalScheme.isUnit_aeval_den`,
`Feec.TimeStepping.RationalScheme.norm_apply_le` (bounded `A`),
`Feec.TimeStepping.RationalScheme.isUnit_resolventEval_den`,
`Feec.TimeStepping.RationalScheme.norm_step_le` and
`Feec.TimeStepping.RationalScheme.step_eq_resolventEval` (m-dissipative `A`; the resolvent from
`Feec.TimeStepping.apply_sub_smul_eq_iff`), the Cayley transform from
`Feec.TimeStepping.norm_cayley_le`, `Feec.TimeStepping.cayley_sub_smul` and
`Feec.TimeStepping.eq_cayley_of_apply_sub_smul`, the complex-coefficient forms from
`Feec.TimeStepping.norm_resolventEval_mul_inverse_le` and
`Feec.TimeStepping.norm_aeval_mul_inverse_le_of_dissipative`, and the error bounds from
`Feec.TimeStepping.norm_aeval_mul_inverse_pow_sub_exp_le` with the order from
`Feec.TimeStepping.X_pow_dvd_sub_mul_expTaylor` (complex coefficients) and
`Feec.TimeStepping.RationalScheme.norm_apply_pow_sub_exp_le` with
`Feec.TimeStepping.RationalScheme.hasOrder_of_isBigO` (real coefficients); for m-dissipative `A`,
the error bounds from `Feec.TimeStepping.norm_resolventEval_mul_inverse_pow_sub_semigroup_le`
(complex coefficients) and `Feec.TimeStepping.RationalScheme.norm_step_pow_sub_semigroup_le`
(real coefficients), the semigroup from `LinearPMap.IsMDissipative.semigroup` through
`VonNeumann.isStrongSolution_semigroup` and `VonNeumann.eqOn_semigroup_of_isStrongSolution`;
for quasi-contractive `A`, from `Feec.TimeStepping.RationalScheme.exists_norm_step_pow_sub_le` with
the semigroup `e^{ωt} S_{A-ω}(t)`; on Banach spaces, from
`Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le`.

## References

* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.11
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983], §1.4
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7–9

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Polynomial Asymptotics Feec.TimeStepping

@[expose] public noncomputable section

namespace VonNeumann

/-- **Von Neumann's inequality** ([VonNeumann1951]). For a contraction `T` of a complex inner
product space `E`, not necessarily complete, and a complex polynomial `p`,
`‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|`. -/
theorem inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T : E →L[ℂ] E}
    (hT : ‖T‖ ≤ 1) (p : ℂ[X]) :
    ‖aeval T p‖ₑ ≤ ⨆ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖p.eval ζ‖ₑ := by
  rw [iSup_subtype']
  exact enorm_le_iSup _ _ fun C hC =>
    ContinuousLinearMap.norm_aeval_le_of_norm_le_one hT fun ζ hζ =>
      hC ⟨ζ, mem_sphere_zero_iff_norm.2 hζ⟩

/-- **Von Neumann's inequality for rational functions** ([VonNeumann1951]). For a contraction
`T` of a complex Hilbert space `E` and complex polynomials `p`, `q` with `q` free of zeros in the
closed unit disc, `q(T)` is invertible and `‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1} |p(ζ)/q(ζ)|`. -/
theorem inequality_rational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) (p q : ℂ[X])
    (hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0) :
    IsUnit (aeval T q) ∧
      ‖aeval T p * Ring.inverse (aeval T q)‖ₑ ≤
        ⨆ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖p.eval ζ / q.eval ζ‖ₑ := by
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun z => p.eval z / q.eval z) (p.continuous.continuousOn.div q.continuous.continuousOn
      fun z hz => hq z (mem_sphere_zero_iff_norm.1 hz).le)
  refine ⟨(ContinuousLinearMap.norm_aeval_mul_inverse_le hT hq
    fun ζ hζ _ => hK ζ (mem_sphere_zero_iff_norm.2 hζ)).1, ?_⟩
  rw [iSup_subtype']
  exact enorm_le_iSup _ _ fun C hC =>
    (ContinuousLinearMap.norm_aeval_mul_inverse_le hT hq
      fun ζ hζ _ => hC ⟨ζ, mem_sphere_zero_iff_norm.2 hζ⟩).2

/-- **Von Neumann's theorem for dissipative operators** ([HairerWanner1996], §IV.11). Let
`r = p/q` be a complex rational function without poles in the closed left half-plane. For every
bounded dissipative operator `A` of a complex Hilbert space and every `τ ≥ 0`, `q(τA)` is
invertible and `r(τA) = p(τA) q(τA)⁻¹` satisfies `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every `n`. -/
theorem inequality_dissipative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →L[ℂ] E} (hA : ∀ x, (⟪A x, x⟫_ℂ).re ≤ 0) (p q : ℂ[X])
    (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsUnit (aeval ((τ : ℂ) • A) q) ∧ ∀ n : ℕ,
      ‖(aeval ((τ : ℂ) • A) p * Ring.inverse (aeval ((τ : ℂ) • A) q)) ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ₑ) ^ n := by
  have hL := RationalScheme.dissipative_smul (𝕜 := ℂ) hA hτ
  exact ⟨(norm_aeval_mul_inverse_le_of_dissipative hL (p := 0) (K := 0) (by simp) hq
      (by simp)).1,
    enorm_pow_le_iSup_pow ContinuousLinearMap.norm_id_le _ _ fun C hC =>
      (norm_aeval_mul_inverse_le_of_dissipative hL
        (natDegree_le_of_norm_div_imaginary_le hq hC) hq hC).2⟩

/-- **Von Neumann's theorem for m-dissipative operators**. Let `A` be a possibly unbounded
operator of a complex Hilbert space, dissipative (`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A`
onto for some `μ > 0` (m-dissipative, [Pazy1983], §1.4), `r = p/q` a complex rational function
without poles in the closed left half-plane and bounded at infinity (`deg p ≤ deg q`), `N = deg q`
and `τ > 0`. Exactly one bounded
operator `S` satisfies `S (x - τAx) = x` on the domain, the resolvent `(1 - τA)⁻¹`;
`Q(S) = ∑_{k ≤ N} qₖ (S - 1)ᵏ S^{N-k}` is invertible, and `r(τA) = P(S) Q(S)⁻¹`,
`P(S) = ∑_{k ≤ N} pₖ (S - 1)ᵏ S^{N-k}`, satisfies `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every
`n`. -/
theorem inequality_mdissipative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →ₗ.[ℂ] E} (hA : ∀ x : A.domain, (⟪A x, (x : E)⟫_ℂ).re ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : ℂ) • (x : E) - A x = y)
    (p q : ℂ[X]) (hpq : p.natDegree ≤ q.natDegree) (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ S : E →L[ℂ] E,
      (∀ T : E →L[ℂ] E, (∀ x : A.domain, T ((x : E) - (τ : ℂ) • A x) = x) ↔ T = S) ∧
      let P := ∑ k ∈ Finset.range (q.natDegree + 1),
        p.coeff k • ((S - 1) ^ k * S ^ (q.natDegree - k))
      let Q := ∑ k ∈ Finset.range (q.natDegree + 1),
        q.coeff k • ((S - 1) ^ k * S ^ (q.natDegree - k))
      IsUnit Q ∧ ∀ n : ℕ, ‖(P * Ring.inverse Q) ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ₑ) ^ n := by
  have hAm : A.IsMDissipative := ⟨hA, hA'⟩
  refine ⟨(τ : ℂ)⁻¹ • Feec.Operator.resolvent A (τ : ℂ)⁻¹, apply_sub_smul_eq_iff hAm hτ, ?_⟩
  exact ⟨(norm_resolventEval_mul_inverse_le hAm hτ (p := 0) (K := 0) (by simp) hq
      (by simp)).1,
    enorm_pow_le_iSup_pow ContinuousLinearMap.norm_id_le _ _ fun C hC =>
      (norm_resolventEval_mul_inverse_le hAm hτ hpq hq hC).2⟩

/-- **A-stable schemes are unconditionally stable** ([HairerWanner1996], §IV.11). Let
`r = p/q` be a real rational function without poles in the closed left half-plane. For every
bounded dissipative operator `A` of a Hilbert space over `𝕜 = ℝ` or `ℂ` and every `τ ≥ 0`,
`q(τA)` is invertible and `r(τA) = p(τA) q(τA)⁻¹` satisfies `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for
every `n`. -/
theorem inequality_dissipative_real {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →L[𝕜] E}
    (hA : ∀ x, RCLike.re ⟪A x, x⟫_𝕜 ≤ 0) (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    IsUnit (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜))) ∧ ∀ n : ℕ,
      ‖(aeval ((τ : 𝕜) • A) (p.map (algebraMap ℝ 𝕜)) *
          Ring.inverse (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜)))) ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ₑ) ^ n := by
  have hτA := RationalScheme.dissipative_smul hA hτ
  refine ⟨(RationalScheme.ofBounded 0 q hq (C := 0) (by simp)).isUnit_aeval_den hτA,
    enorm_pow_le_iSup_pow ContinuousLinearMap.norm_id_le _ _ fun C hC => ?_⟩
  rw [← apply_ofBounded hq hC]
  exact ((RationalScheme.ofBounded p q hq hC).norm_apply_le hτA).trans
    (RationalScheme.supNorm_ofBounded_le hq hC)

/-- **A-stable schemes are unconditionally stable, for m-dissipative operators**: the real form
of `VonNeumann.inequality_mdissipative`, over `𝕜 = ℝ` or `ℂ`. Let `A` be a
possibly unbounded operator of a Hilbert space over `𝕜`, dissipative
(`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A` onto for some `μ > 0` (m-dissipative,
[Pazy1983], §1.4), `r = p/q` a real rational function without poles in the closed left
half-plane and bounded at infinity (`deg p ≤ deg q`), `N = deg q` and `τ > 0`. Exactly one
bounded operator `S` satisfies `S (x - τAx) = x` on the domain, the resolvent `(1 - τA)⁻¹`;
`Q(S) = ∑_{k ≤ N} qₖ (S - 1)ᵏ S^{N-k}` is invertible, and `r(τA) = P(S) Q(S)⁻¹`,
`P(S) = ∑_{k ≤ N} pₖ (S - 1)ᵏ S^{N-k}`, satisfies `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every `n`. -/
theorem inequality_mdissipative_real {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y)
    (p q : ℝ[X]) (_hpq : p.natDegree ≤ q.natDegree) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ S : E →L[𝕜] E,
      (∀ T : E →L[𝕜] E, (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x) ↔ T = S) ∧
      let P := ∑ k ∈ Finset.range (q.natDegree + 1),
        (p.coeff k : 𝕜) • ((S - 1) ^ k * S ^ (q.natDegree - k))
      let Q := ∑ k ∈ Finset.range (q.natDegree + 1),
        (q.coeff k : 𝕜) • ((S - 1) ^ k * S ^ (q.natDegree - k))
      IsUnit Q ∧ ∀ n : ℕ, ‖(P * Ring.inverse Q) ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ₑ) ^ n := by
  have hAm : A.IsMDissipative := ⟨hA, hA'⟩
  refine ⟨(τ : 𝕜)⁻¹ • Feec.Operator.resolvent A (τ : 𝕜)⁻¹, apply_sub_smul_eq_iff hAm hτ, ?_⟩
  intro P Q
  rw [show P = _ from (resolventEval_map _ p _).symm,
    show Q = _ from (resolventEval_map _ q _).symm]
  refine ⟨(RationalScheme.ofBounded 0 q hq (C := 0) (by simp)).isUnit_resolventEval_den hAm hτ,
    enorm_pow_le_iSup_pow ContinuousLinearMap.norm_id_le _ _ fun C hC => ?_⟩
  have h := ((RationalScheme.ofBounded p q hq hC).norm_step_le hAm hτ).2
  rw [RationalScheme.step_eq_resolventEval] at h
  exact h.trans (RationalScheme.supNorm_ofBounded_le hq hC)

/-- **The Cayley transform of an m-dissipative operator is a contraction**. Let `A` be a
possibly unbounded operator of a Hilbert space over `𝕜 = ℝ` or `ℂ`, dissipative
(`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A` onto for some `μ > 0` (m-dissipative,
[Pazy1983], §1.4). For every `τ > 0`, exactly one bounded operator `T` satisfies
`T (x - τAx) = x + τAx` for all `x` in the domain, the Cayley transform
`C_τ = (1 + τA)(1 - τA)⁻¹`, and `‖C_τ‖ ≤ 1`. -/
theorem cayley_contraction {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y) {τ : ℝ}
    (hτ : 0 < τ) :
    ∃ Cτ : E →L[𝕜] E, ‖Cτ‖ ≤ 1 ∧ ∀ T : E →L[𝕜] E,
      (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x + (τ : 𝕜) • A x) ↔ T = Cτ := by
  have hAm : A.IsMDissipative := ⟨hA, hA'⟩
  exact ⟨cayley A τ, norm_cayley_le hAm hτ, fun T =>
    ⟨eq_cayley_of_apply_sub_smul hAm hτ, fun h => h ▸ cayley_sub_smul hAm hτ⟩⟩

/-- **The error of an A-stable scheme of order `m`** ([BrennerThomee1979]). Let `r = p/q` be a
complex rational function without poles in the closed left half-plane, A-stable
(`|r(iy)| ≤ 1`), of order `m` (`r(z) - e^z = O(z^{m+1})` at `0`). There is a constant `K` such
that, for every bounded dissipative operator `A` of a complex Hilbert space, every `τ ≥ 0`, `n`
and `x`, `‖r(τA)ⁿ x - e^{nτA} x‖ ≤ K nτ τᵐ ‖A^{m+1} x‖`. -/
theorem error_bound (p q : ℂ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0)
    (hr : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ 1) {m : ℕ}
    (hm : (fun z : ℂ => p.eval z / q.eval z - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1)) :
    ∃ K : ℝ, ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (A : E →L[ℂ] E), (∀ x, (⟪A x, x⟫_ℂ).re ≤ 0) → ∀ τ : ℝ, 0 ≤ τ → ∀ (n : ℕ) (x : E),
        ‖((aeval ((τ : ℂ) • A) p * Ring.inverse (aeval ((τ : ℂ) • A) q)) ^ n) x -
            NormedSpace.exp (((n * τ : ℝ) : ℂ) • A) x‖ ≤
          K * (n * τ) * τ ^ m * ‖(A ^ (m + 1)) x‖ := by
  refine ⟨(⨆ y : ℝ, ‖((p - q * (expTaylor m).map (algebraMap ℝ ℂ)) /ₘ X ^ (m + 1)).eval
      (y * Complex.I) / q.eval (y * Complex.I)‖) + 1 / (m + 1).factorial, ?_⟩
  intro E _ _ _ A hA τ hτ n x
  exact norm_aeval_mul_inverse_pow_sub_exp_le hA hq hr
    (X_pow_dvd_sub_mul_expTaylor (hq 0 (by simp)) hm) hτ n x

/-- **The error of an A-stable scheme of order `m`, real coefficients** ([BrennerThomee1979]).
Let `r = p/q` be a real rational function without poles in the closed left half-plane, A-stable
(`|r(iy)| ≤ 1`), of order `m` (`r(z) - e^z = O(z^{m+1})` at `0`). There is a constant `K` such
that, for every bounded dissipative operator `A` of a Hilbert space over `𝕜 = ℝ` or `ℂ`, every
`τ ≥ 0`, `n` and `x`, `‖r(τA)ⁿ x - e^{nτA} x‖ ≤ K nτ τᵐ ‖A^{m+1} x‖`. -/
theorem error_bound_real (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    (hr : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ 1) {m : ℕ}
    (hm : (fun z : ℂ => aeval z p / aeval z q - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1)) :
    ∃ K : ℝ, ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
      [CompleteSpace E] (A : E →L[𝕜] E), (∀ x, RCLike.re ⟪A x, x⟫_𝕜 ≤ 0) →
      ∀ τ : ℝ, 0 ≤ τ → ∀ (n : ℕ) (x : E),
        ‖((aeval ((τ : 𝕜) • A) (p.map (algebraMap ℝ 𝕜)) *
              Ring.inverse (aeval ((τ : 𝕜) • A) (q.map (algebraMap ℝ 𝕜)))) ^ n) x -
            NormedSpace.exp (((n * τ : ℝ) : 𝕜) • A) x‖ ≤
          K * (n * τ) * τ ^ m * ‖(A ^ (m + 1)) x‖ := by
  set r := RationalScheme.ofBounded p q hq hr
  refine ⟨(r.remainder m).supNorm + 1 / (m + 1).factorial, ?_⟩
  intro 𝕜 E _ _ _ _ A hA τ hτ n x
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact r.norm_apply_pow_sub_exp_le hA hr (r.hasOrder_of_isBigO hm) hτ n x

/-- **The error of an A-stable scheme of order `m` for m-dissipative operators**
([BrennerThomee1979]). Let `r = p/q` be a complex rational function without poles
in the closed left half-plane, A-stable (`|r(iy)| ≤ 1`), of order `m`
(`r(z) - e^z = O(z^{m+1})` at `0`). There is a constant `K` such that for every possibly
unbounded operator `A` of a complex Hilbert space, dissipative with `μ - A` onto for some
`μ > 0` (m-dissipative, [Pazy1983], §1.4): there is a family `S` of bounded operators, `S 0 = 1`,
whose orbits `t ↦ S t x` from `x ∈ D(A)` are strong solutions of `u' = A u`, and the only ones
(the semigroup `e^{tA}`), such that for every `τ > 0`, with the resolvent `R = (1 - τA)⁻¹` (the
only bounded operator mapping `x - τAx` to `x`) and `r(τA) = P(R) Q(R)⁻¹` as in
`VonNeumann.inequality_mdissipative`, `‖r(τA)ⁿ x - e^{nτA} x‖ ≤ K nτ τᵐ ‖A^{m+1} x‖` for every
`n` and `x ∈ D(A^{m+1})` (a chain `u 0 = x, …, u (m + 1) = A^{m+1} x` in the graph of `A`). -/
theorem error_bound_mdissipative (p q : ℂ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0)
    (hr : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ 1) {m : ℕ}
    (hm : (fun z : ℂ => p.eval z / q.eval z - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1)) :
    ∃ K : ℝ, ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (A : E →ₗ.[ℂ] E), (∀ x : A.domain, (⟪A x, (x : E)⟫_ℂ).re ≤ 0) →
      (∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : ℂ) • (x : E) - A x = y) →
      ∃ S : ℝ → E →L[ℂ] E, S 0 = 1 ∧
        (∀ (x : A.domain) (T : ℝ), IsStrongSolution A (Set.Icc 0 T) fun t => S t x) ∧
        (∀ (x : A.domain) (T : ℝ) (u : ℝ → E), u 0 = x → IsStrongSolution A (Set.Icc 0 T) u →
          Set.EqOn u (fun t => S t x) (Set.Icc 0 T)) ∧
        ∀ τ : ℝ, 0 < τ → ∃ R : E →L[ℂ] E,
          (∀ T : E →L[ℂ] E, (∀ x : A.domain, T ((x : E) - (τ : ℂ) • A x) = x) ↔ T = R) ∧
          let P := ∑ k ∈ Finset.range (q.natDegree + 1),
            p.coeff k • ((R - 1) ^ k * R ^ (q.natDegree - k))
          let Q := ∑ k ∈ Finset.range (q.natDegree + 1),
            q.coeff k • ((R - 1) ^ k * R ^ (q.natDegree - k))
          ∀ (n : ℕ) (u : ℕ → E), (∀ j < m + 1, (u j, u (j + 1)) ∈ A.graph) →
            ‖((P * Ring.inverse Q) ^ n) (u 0) - S (n * τ) (u 0)‖ ≤
              K * (n * τ) * τ ^ m * ‖u (m + 1)‖ := by
  have hm' := X_pow_dvd_sub_mul_expTaylor (hq 0 (by simp)) hm
  refine ⟨(⨆ y : ℝ, ‖((p - q * (expTaylor m).map (algebraMap ℝ ℂ)) /ₘ X ^ (m + 1)).eval
      (y * Complex.I) / q.eval (y * Complex.I)‖) + 1 / (m + 1).factorial, ?_⟩
  intro E _ _ _ A hA hA'
  have hAm : A.IsMDissipative := ⟨hA, hA'⟩
  refine ⟨hAm.semigroup.S, hAm.semigroup.map_zero, isStrongSolution_semigroup hAm,
    eqOn_semigroup_of_isStrongSolution hAm, fun τ hτ =>
      ⟨(τ : ℂ)⁻¹ • Feec.Operator.resolvent A (τ : ℂ)⁻¹, apply_sub_smul_eq_iff hAm hτ, ?_⟩⟩
  intro P Q n u hu
  exact norm_resolventEval_mul_inverse_pow_sub_semigroup_le hAm hq hr hm' hτ n hu

/-- **The error of an A-stable scheme of order `m` for m-dissipative operators, real
coefficients** ([BrennerThomee1979]): the real form of
`VonNeumann.error_bound_mdissipative`, over `𝕜 = ℝ` or `ℂ`. Let `r = p/q` be a real rational
function without poles in the closed left half-plane, A-stable (`|r(iy)| ≤ 1`), of order `m`
(`r(z) - e^z = O(z^{m+1})` at `0`). There is a constant `K` such that for every m-dissipative,
possibly unbounded, operator `A` of a Hilbert space over `𝕜`, with its semigroup `S` (as in
`VonNeumann.error_bound_mdissipative`), every `τ > 0` and `r(τA) = P(R) Q(R)⁻¹` at the resolvent
`R = (1 - τA)⁻¹`, `‖r(τA)ⁿ x - e^{nτA} x‖ ≤ K nτ τᵐ ‖A^{m+1} x‖` for every `n` and
`x ∈ D(A^{m+1})`. -/
theorem error_bound_mdissipative_real (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    (hr : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ 1) {m : ℕ}
    (hm : (fun z : ℂ => aeval z p / aeval z q - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1)) :
    ∃ K : ℝ, ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
      [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (A : E →ₗ.[𝕜] E),
      (∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0) →
      (∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y) →
      ∃ S : ℝ → E →L[𝕜] E, S 0 = 1 ∧
        (∀ (x : A.domain) (T : ℝ), IsStrongSolution A (Set.Icc 0 T) fun t => S t x) ∧
        (∀ (x : A.domain) (T : ℝ) (u : ℝ → E), u 0 = x → IsStrongSolution A (Set.Icc 0 T) u →
          Set.EqOn u (fun t => S t x) (Set.Icc 0 T)) ∧
        ∀ τ : ℝ, 0 < τ → ∃ R : E →L[𝕜] E,
          (∀ T : E →L[𝕜] E, (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x) ↔ T = R) ∧
          let P := ∑ k ∈ Finset.range (q.natDegree + 1),
            (p.coeff k : 𝕜) • ((R - 1) ^ k * R ^ (q.natDegree - k))
          let Q := ∑ k ∈ Finset.range (q.natDegree + 1),
            (q.coeff k : 𝕜) • ((R - 1) ^ k * R ^ (q.natDegree - k))
          ∀ (n : ℕ) (u : ℕ → E), (∀ j < m + 1, (u j, u (j + 1)) ∈ A.graph) →
            ‖((P * Ring.inverse Q) ^ n) (u 0) - S (n * τ) (u 0)‖ ≤
              K * (n * τ) * τ ^ m * ‖u (m + 1)‖ := by
  set r := RationalScheme.ofBounded p q hq hr
  refine ⟨(r.remainder m).supNorm + 1 / (m + 1).factorial, ?_⟩
  intro 𝕜 E _ _ _ _ _ _ A hA hA'
  have hAm : A.IsMDissipative := ⟨hA, hA'⟩
  refine ⟨hAm.semigroup.S, hAm.semigroup.map_zero, isStrongSolution_semigroup hAm,
    eqOn_semigroup_of_isStrongSolution hAm, fun τ hτ =>
      ⟨(τ : 𝕜)⁻¹ • Feec.Operator.resolvent A (τ : 𝕜)⁻¹, apply_sub_smul_eq_iff hAm hτ, ?_⟩⟩
  intro P Q n u hu
  rw [show P = _ from (resolventEval_map _ p _).symm,
    show Q = _ from (resolventEval_map _ q _).symm]
  have h := r.norm_step_pow_sub_semigroup_le hAm hr (r.hasOrder_of_isBigO hm) hτ n hu
  rwa [RationalScheme.step_eq_resolventEval] at h

theorem error_bound_quasi_real (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0)
    (hr : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ 1) {m : ℕ}
    (hm : (fun z : ℂ => aeval z p / aeval z q - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1)) :
    ∃ c₀ K κ : ℝ, 0 < c₀ ∧ ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
      [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
      (A : E →ₗ.[𝕜] E) (ω : ℝ), 0 ≤ ω →
      (∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ ω * ‖(x : E)‖ ^ 2) →
      (∃ μ : ℝ, ω < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y) →
      ∃ S : ℝ → E →L[𝕜] E, S 0 = 1 ∧ (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ Real.exp (ω * t)) ∧
        (∀ (x : A.domain) (T : ℝ), IsStrongSolution A (Set.Icc 0 T) fun t => S t x) ∧
        (∀ (x : A.domain) (T : ℝ) (u : ℝ → E), u 0 = x → IsStrongSolution A (Set.Icc 0 T) u →
          Set.EqOn u (fun t => S t x) (Set.Icc 0 T)) ∧
        ∀ τ : ℝ, 0 < τ → ω * τ ≤ c₀ → ∃ R : E →L[𝕜] E,
          (∀ T : E →L[𝕜] E, (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x) ↔ T = R) ∧
          let P := ∑ k ∈ Finset.range (q.natDegree + 1),
            (p.coeff k : 𝕜) • ((R - 1) ^ k * R ^ (q.natDegree - k))
          let Q := ∑ k ∈ Finset.range (q.natDegree + 1),
            (q.coeff k : 𝕜) • ((R - 1) ^ k * R ^ (q.natDegree - k))
          ∀ (n : ℕ) (u : ℕ → E), (∀ j < m + 1, (u j, u (j + 1)) ∈ A.graph) →
            ‖((P * Ring.inverse Q) ^ n) (u 0) - S (n * τ) (u 0)‖ ≤
              K * Real.exp (κ * ω * (n * τ)) * (n * τ) * τ ^ m * ‖u (m + 1)‖ := by
  set r := RationalScheme.ofBounded p q hq hr
  obtain ⟨c₀, hc₀, K, κ, -, -, h⟩ := r.exists_norm_step_pow_sub_le hr (r.hasOrder_of_isBigO hm)
  refine ⟨min c₀ (1 / 2), K, κ, lt_min hc₀ (by norm_num), ?_⟩
  intro 𝕜 E _ _ _ _ _ _ A ω hω hA hA'
  set B := ((-(ω : 𝕜)) • (LinearMap.id : E →ₗ[𝕜] E)) +ᵥ A
  have hB : B.IsMDissipative := by
    refine ⟨fun x => ?_, ?_⟩
    · change RCLike.re ⟪(-(ω : 𝕜)) • (x : E) + A x, (x : E)⟫_𝕜 ≤ 0
      rw [inner_add_left, map_add, inner_smul_left, ← RCLike.ofReal_neg, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
      linarith [hA x]
    · obtain ⟨μ, hμ, hs⟩ := hA'
      refine ⟨μ - ω, by linarith, fun y => ?_⟩
      obtain ⟨x, hx⟩ := hs y
      refine ⟨x, ?_⟩
      change ((μ - ω : ℝ) : 𝕜) • (x : E) - ((-(ω : 𝕜)) • (x : E) + A x) = y
      rw [← hx]; push_cast; rw [sub_smul, neg_smul]; abel
  set G := hB.semigroup.rescale ω
  have hG : G.generator = A := hB.generator_rescale_semigroup
  refine ⟨G.S, G.map_zero, fun t ht => hB.norm_rescale_semigroup_le ht,
    isStrongSolution_of_generator G hG, eqOn_of_isStrongSolution_generator G hG,
    fun τ hτ hωτ => ?_⟩
  have hz₁ : 0 < RCLike.re ((τ : 𝕜)⁻¹ - (ω : 𝕜)) := by
    rw [← RCLike.ofReal_inv, ← RCLike.ofReal_sub, RCLike.ofReal_re,
      show τ⁻¹ - ω = (1 - ω * τ) / τ by field_simp]
    exact div_pos (by linarith [min_le_right c₀ (1 / 2)]) hτ
  have hRA := (hB.isResolvent_of_re_pos hz₁).of_neg_smul_vadd.isResolvent_resolvent
  refine ⟨(τ : 𝕜)⁻¹ • Feec.Operator.resolvent A (τ : 𝕜)⁻¹,
    apply_sub_smul_eq_iff_of_isResolvent hτ hRA, ?_⟩
  intro P Q n u hu
  rw [show P = _ from (resolventEval_map _ p _).symm,
    show Q = _ from (resolventEval_map _ q _).symm]
  have h' := h hω hB G hG hτ (hωτ.trans (min_le_left _ _)) n hu
  rwa [RationalScheme.step_eq_resolventEval] at h'

theorem error_bound_banach_real (p q : ℝ[X]) (hpq : p.natDegree ≤ q.natDegree)
    (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {m : ℕ}
    (hm : (fun z : ℂ => aeval z p / aeval z q - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1))
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (hS0 : S 0 = 1)
    (hSadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hSc : ∀ x : E, ContinuousOn (fun t => S t x) (Set.Ici 0)) {τ : ℝ} (hτ : 0 ≤ τ)
    (R : E →L[𝕜] E)
    (hR : ∀ x y : E, HasDerivWithinAt (fun t => S t x) y (Set.Ici 0) 0 → R (x - (τ : 𝕜) • y) = x)
    (hRi : Function.Injective R) :
    let P := ∑ k ∈ Finset.range (q.natDegree + 1),
      (p.coeff k : 𝕜) • ((R - 1) ^ k * R ^ (q.natDegree - k))
    let Q := ∑ k ∈ Finset.range (q.natDegree + 1),
      (q.coeff k : 𝕜) • ((R - 1) ^ k * R ^ (q.natDegree - k))
    let ρ : ℝ[X] := (p - q * ∑ j ∈ Finset.range (m + 1), C (1 / (j.factorial : ℝ)) * X ^ j) /ₘ
      X ^ (m + 1)
    let Pρ := ∑ k ∈ Finset.range (q.natDegree + 1),
      (ρ.coeff k : 𝕜) • ((R - 1) ^ k * R ^ (q.natDegree - k))
    IsUnit Q → ∀ (n : ℕ) (Ms M K₀ : ℝ), (∀ k ≤ n, ‖(P * Ring.inverse Q) ^ k‖ ≤ Ms) →
      (∀ t ∈ Set.Icc 0 (n * τ), ‖S t‖ ≤ M) → ‖Pρ * Ring.inverse Q‖ ≤ K₀ →
      ∀ u : ℕ → E, (∀ j < m + 1, HasDerivWithinAt (fun t => S t (u j)) (u (j + 1)) (Set.Ici 0) 0) →
        ‖((P * Ring.inverse Q) ^ n) (u 0) - S (n * τ) (u 0)‖ ≤
          Ms * (K₀ + M / (m + 1).factorial) * M * (n * τ) * τ ^ m * ‖u (m + 1)‖ := by
  intro P Q ρ Pρ hQ n Ms M K₀ hst hS hρ u hu
  set r : RationalScheme := ⟨p, q, hpq, hq⟩
  set G : Feec.C0Semigroup 𝕜 E := ⟨S, hS0, hSadd, hSc⟩
  have hP : r.resolventStep R = P * Ring.inverse Q := by
    show resolventEval q.natDegree (p.map (algebraMap ℝ 𝕜)) R *
      Ring.inverse (resolventEval q.natDegree (q.map (algebraMap ℝ 𝕜)) R) = _
    rw [resolventEval_map, resolventEval_map]
  have hPρ : (r.remainder m).resolventStep R = Pρ * Ring.inverse Q := by
    show resolventEval q.natDegree (ρ.map (algebraMap ℝ 𝕜)) R *
      Ring.inverse (resolventEval q.natDegree (q.map (algebraMap ℝ 𝕜)) R) = _
    rw [resolventEval_map, resolventEval_map]
  have hQ' : IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R) := by
    show IsUnit (resolventEval q.natDegree (q.map (algebraMap ℝ 𝕜)) R)
    rw [resolventEval_map]; exact hQ
  have h := r.norm_resolventStep_pow_sub_S_le G (r.hasOrder_of_isBigO hm) hτ
    (fun x y hxy => hR x y ((mem_graph_generator_iff G).1 hxy)) hRi hQ'
    (hP ▸ hst) hS (hPρ ▸ hρ) (fun j hj => (mem_graph_generator_iff G).2 (hu j hj))
  rwa [hP] at h

end VonNeumann
