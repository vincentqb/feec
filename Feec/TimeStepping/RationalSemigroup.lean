module

public import Feec.TimeStepping.RationalBanach

/-!
# Rational approximations of semigroups with unbounded generators

Let `A` be an m-dissipative, possibly unbounded, operator of a Hilbert space over `𝕜 = ℝ` or `ℂ`,
`S(t)` the contraction semigroup it generates (Lumer–Phillips,
`LinearPMap.IsMDissipative.semigroup`), and `r` an A-stable rational scheme of order `p`. Then
**Brenner–Thomée's error bound** holds with the constant of the bounded case
([BrennerThomee1979]; [Thomee2006], Ch. 9):

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K nτ τᵖ ‖A^{p+1} x‖`, `K = sup_y |ρ(iy)| + 1/(p+1)!`,

for every `τ > 0`, `n` and `x ∈ D(A^{p+1})`, with `r(τA)` the operator of `Feec.TimeStepping.Rational`
(through the Cayley transform, equivalently the resolvent). `x ∈ D(A^k)` with `Aᵏ x = y` is a
chain `u₀ = x, …, u_k = y` with `(u_j, u_{j+1})` in the graph of `A`.

## Main results

* **`RationalScheme.norm_step_pow_sub_semigroup_le`**: real `r`, Hilbert spaces over `𝕜`;
* **`norm_resolventEval_mul_inverse_pow_sub_semigroup_le`**: complex `r = p/q` on complex Hilbert
  spaces, `r(τA) = P(R) Q(R)⁻¹` at the resolvent `R = (1 - τA)⁻¹`;
* **`norm_thetaStep_pow_sub_semigroup_le`** (θ-schemes, `θ ≥ 1/2`: `K = θ + 1/2`, order `1`) and
  **`norm_cayley_pow_sub_semigroup_le`** (Crank–Nicolson: `K = 5/12`, order `2`).

## Proof

For real `r`, directly from Brenner–Thomée on Banach spaces
(`Feec.TimeStepping.RationalScheme.norm_step_pow_sub_S_le`): von Neumann's inequality gives the
stability `‖r(τA)‖ ≤ 1`, the remainder bound `‖ρ(τA)‖ ≤ sup_y |ρ(iy)|` and the invertibility of
`Q(R)` (`RationalScheme.norm_step_le`, `RationalScheme.isUnit_resolventEval_den`), and `S` is a
contraction semigroup.

For complex `r`, the θ-schemes and Crank–Nicolson, through the Yosida approximations
`A_m = c_m A (c_m - A)⁻¹` (`Feec.LumerPhillips.yosida`), bounded
and dissipative: the bounded theorem holds for each
`A_m` with the same constant, `A_m^k x = J_mᵏ Aᵏ x` on `D(Aᵏ)` with the contractions
`J_m = c_m (c_m - A)⁻¹` (`Feec.LumerPhillips.yosida_pow_apply`), and both sides converge: `exp(t A_m) x → S(t) x` by
construction of `S`, and `r(τ A_m) → r(τ A)` strongly. For the latter, the resolvents converge
strongly (`Feec.LumerPhillips.tendsto_resolvent_yosida`: `(z - A_m)⁻¹ y - (z - A)⁻¹ y = (z - A_m)⁻¹ (A_m x - A x)` at
`x = (z - A)⁻¹ y`), hence the Cayley transforms; polynomials in uniformly bounded, strongly
convergent operators converge strongly (`ContinuousLinearMap.tendsto_aeval_apply`), and so do
the inverses `q̃(C_m)⁻¹` (`ContinuousLinearMap.tendsto_inverse_apply`), uniformly bounded by
von Neumann's inequality for `1/q̃` (`ContinuousLinearMap.exists_norm_inverse_aeval_le`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7, 9
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.3 (the Yosida approximation), §1.4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Filter Polynomial LinearPMap Feec.Operator Feec.LumerPhillips NormedSpace

@[expose] public noncomputable section

namespace Feec.LumerPhillips

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →ₗ.[𝕜] E}

/-- The Yosida approximation `A_m`, everywhere defined, is m-dissipative. -/
theorem isMDissipative_yosida (hA : A.IsMDissipative) (m : ℕ) :
    ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤).IsMDissipative :=
  (yosida A m).isMDissipative_toPMap_top (re_inner_yosida_le hA m)

/-- **The resolvents of the Yosida approximations converge strongly**: for `re z > 0`,
`(z - A_m)⁻¹ y → (z - A)⁻¹ y`, since `(z - A_m)⁻¹ y - x = (z - A_m)⁻¹ (A_m x - A x)` at
`x = (z - A)⁻¹ y ∈ D(A)`, `‖(z - A_m)⁻¹‖ ≤ 1/re z` and `A_m x → A x`. -/
theorem tendsto_resolvent_yosida (hA : A.IsMDissipative) {z : 𝕜} (hz : 0 < RCLike.re z)
    (y : E) :
    Tendsto (fun m => resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z y) atTop
      (𝓝 (resolvent A z y)) := by
  have hR := hA.isResolvent_of_re_pos hz
  set x : A.domain := hR.toDomain y
  have hRm : ∀ m, IsResolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z
      (resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z) := fun m =>
    (isMDissipative_yosida hA m).isResolvent_of_re_pos hz
  have e : ∀ m, resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z y - resolvent A z y =
      resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z (yosida A m x - A x) := fun m => by
    have h1 : resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z (z • (x : E) - yosida A m x) =
        x := (hRm m).apply_sub ⟨(x : E), trivial⟩
    have h2 : z • (x : E) - A x = y := hR.sub_apply_toDomain y
    calc _ = resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z y -
          resolvent ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) z (z • (x : E) - yosida A m x) := by
          rw [h1]; rfl
      _ = _ := by rw [← _root_.map_sub]; congr 1; rw [← h2]; abel
  have hA' := (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_yosida hA x)).const_mul
    (RCLike.re z)⁻¹
  rw [mul_zero] at hA'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hA'
  rw [e]
  exact ((Operator.resolvent _ z).le_opNorm _).trans (mul_le_mul_of_nonneg_right
    ((hRm m).norm_le_of_isDissipative (isMDissipative_yosida hA m).dissipative hz)
    (norm_nonneg _))

end Feec.LumerPhillips

namespace Feec.TimeStepping

/-! ### The Yosida approximations -/

section Yosida

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →ₗ.[𝕜] E}

/-- The Cayley transforms of the Yosida approximations converge strongly. -/
theorem tendsto_cayley_yosida (hA : A.IsMDissipative) {τ : ℝ} (hτ : 0 < τ) (y : E) :
    Tendsto (fun m => cayley ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) τ y) atTop
      (𝓝 (cayley A τ y)) := by
  have hz : 0 < RCLike.re ((τ : 𝕜)⁻¹) := by
    rw [← RCLike.ofReal_inv, RCLike.ofReal_re]; positivity
  simp only [cayley, _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self]
  exact ((tendsto_resolvent_yosida hA hz y).const_smul _).sub_const _

/-- The θ-steps of the Yosida approximations converge strongly (`re θ > 0`, `τ > 0`). -/
theorem tendsto_thetaStep_yosida (hA : A.IsMDissipative) {θ : 𝕜} (hθ : 0 < RCLike.re θ)
    {τ : ℝ} (hτ : 0 < τ) (y : E) :
    Tendsto (fun m => thetaStep ((yosida A m : E →ₗ[𝕜] E).toPMap ⊤) θ τ y) atTop
      (𝓝 (thetaStep A θ τ y)) := by
  simp only [thetaStep, _root_.sub_apply, _root_.smul_apply]
  exact ((tendsto_resolvent_yosida hA (re_inv_mul_pos hθ hτ) y).const_smul _).sub_const _

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Error bounds pass to the limit of the Yosida approximations**: if `Pₘ → P` strongly with
`‖Pₘ‖ ≤ 1`, and `‖Pₘⁿ u₀ - exp(t A_m) u₀‖ ≤ C ‖A_mᵏ u₀‖` for every `m`, then
`‖Pⁿ u₀ - S(t) u₀‖ ≤ C ‖Aᵏ u₀‖` for the Lumer–Phillips semigroup `S` and `u₀ ∈ D(Aᵏ)`. -/
theorem norm_pow_apply_sub_semigroup_le (hA : A.IsMDissipative) {P : E →L[𝕜] E}
    {Pm : ℕ → E →L[𝕜] E} (hPm : ∀ m, ‖Pm m‖ ≤ 1)
    (hP : ∀ y, Tendsto (fun m => Pm m y) atTop (𝓝 (P y))) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    {u : ℕ → E} (hu : ∀ j < k, (u j, u (j + 1)) ∈ A.graph) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ m, ‖(Pm m ^ n) (u 0) - exp ((t : 𝕜) • yosida A m) (u 0)‖ ≤
      C * ‖(yosida A m ^ k) (u 0)‖) :
    ‖(P ^ n) (u 0) - hA.semigroup.S t (u 0)‖ ≤ C * ‖u k‖ :=
  le_of_tendsto' ((ContinuousLinearMap.tendsto_pow_apply hPm hP n (u 0)).sub
    (tendsto_approxS hA ht (u 0))).norm
    fun m => (hb m).trans (mul_le_mul_of_nonneg_left (norm_yosida_pow_apply_le hA m hu) hC)

end Yosida

/-! ### Brenner–Thomée for unbounded generators -/

section Unbounded

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →ₗ.[𝕜] E}

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Brenner–Thomée for unbounded generators**: for an A-stable rational scheme `r` of order `p`,
every m-dissipative `A` with semigroup `S`, `τ > 0`, `n` and `u₀ ∈ D(A^{p+1})` (a chain
`u₀, …, u_{p+1}` in the graph of `A`, `A^{p+1} u₀ = u_{p+1}`),
`‖r(τA)ⁿ u₀ - S(nτ) u₀‖ ≤ K nτ τᵖ ‖A^{p+1} u₀‖` with `K = sup_y |ρ(iy)| + 1/(p+1)!` (`ρ` the
remainder), the constant of the bounded case. [BrennerThomee1979]; [Thomee2006], Ch. 9 -/
theorem RationalScheme.norm_step_pow_sub_semigroup_le (r : RationalScheme) (hA : A.IsMDissipative)
    (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ A.graph) :
    ‖(r.step A τ ^ n) (u 0) - hA.semigroup.S (n * τ) (u 0)‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  have hτinv : 0 < RCLike.re ((τ : 𝕜)⁻¹) := by
    rw [← RCLike.ofReal_inv, RCLike.ofReal_re]; positivity
  have h := r.norm_step_pow_sub_S_le hA.semigroup hA.generator_semigroup hp hτ (n := n)
    (hA.isResolvent_of_re_pos hτinv) (r.isUnit_resolventEval_den hA hτ)
    (fun k _ => norm_pow_le_one (r.norm_step_le_one hA hτ hr) k)
    (fun t ht => hA.isContraction_semigroup t ht.1) ((r.remainder p).norm_step_le hA hτ).2 hu
  simpa using h

/-- **Brenner–Thomée for the θ-schemes** (`θ ≥ 1/2`): for every m-dissipative `A`, `τ > 0`, `n`
and `u₀ ∈ D(A²)`, `‖r_θ(τA)ⁿ u₀ - S(nτ) u₀‖ ≤ (θ + 1/2) nτ τ ‖A² u₀‖`; `θ = 1` is implicit
Euler. [Thomee2006], Ch. 7 -/
theorem norm_thetaStep_pow_sub_semigroup_le (hA : A.IsMDissipative) {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E} (hu : ∀ j < 2, (u j, u (j + 1)) ∈ A.graph) :
    ‖(thetaStep A θ τ ^ n) (u 0) - hA.semigroup.S (n * τ) (u 0)‖ ≤
      (θ + 1 / 2) * (n * τ) * τ * ‖u 2‖ := by
  have hθ' : 1 / 2 ≤ RCLike.re (θ : 𝕜) := by rwa [RCLike.ofReal_re]
  exact norm_pow_apply_sub_semigroup_le hA
    (fun m => norm_thetaStep_le (isMDissipative_yosida hA m) hθ' hτ)
    (tendsto_thetaStep_yosida hA (by linarith) hτ) n (by positivity) hu (by positivity)
    fun m => norm_thetaStep_pow_sub_exp_le (re_inner_yosida_le hA m) hθ hτ n (u 0)

/-- **Brenner–Thomée for Crank–Nicolson** (the Cayley transform with half step `τ/2`): for every
m-dissipative `A`, `τ > 0`, `n` and `u₀ ∈ D(A³)`,
`‖C_{τ/2}ⁿ u₀ - S(nτ) u₀‖ ≤ 5/12 nτ τ² ‖A³ u₀‖`. [BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_cayley_pow_sub_semigroup_le (hA : A.IsMDissipative) {τ : ℝ} (hτ : 0 < τ) (n : ℕ)
    {u : ℕ → E} (hu : ∀ j < 3, (u j, u (j + 1)) ∈ A.graph) :
    ‖(cayley A (τ / 2) ^ n) (u 0) - hA.semigroup.S (n * τ) (u 0)‖ ≤
      5 / 12 * (n * τ) * τ ^ 2 * ‖u 3‖ :=
  norm_pow_apply_sub_semigroup_le hA (fun m => norm_cayley_le (isMDissipative_yosida hA m)
    (half_pos hτ)) (tendsto_cayley_yosida hA (half_pos hτ)) n (by positivity) hu (by positivity)
    fun m => norm_cayley_pow_sub_exp_le (re_inner_yosida_le hA m) hτ n (u 0)

end Unbounded

/-! ### Complex coefficients -/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E}

/-- **Brenner–Thomée for unbounded generators, complex coefficients**: let `r = p/q` be complex,
without poles for `re z ≤ 0`, A-stable (`|r(iy)| ≤ 1`) and of order `m`
(`X^{m+1} ∣ p - q Tₘ`). For every m-dissipative `A` of a complex Hilbert space with semigroup
`S`, `τ > 0`, `n` and `u₀ ∈ D(A^{m+1})` (a chain in the graph of `A`), with
`r(τA) = P(R) Q(R)⁻¹` at the resolvent `R = (1 - τA)⁻¹` (`resolventEval`, `N = deg q`),
`‖r(τA)ⁿ u₀ - S(nτ) u₀‖ ≤ K nτ τᵐ ‖A^{m+1} u₀‖` with `K = sup_y |ρ(iy)/q(iy)| + 1/(m+1)!`,
`ρ = (p - q Tₘ)/X^{m+1}`. [BrennerThomee1979] -/
theorem norm_resolventEval_mul_inverse_pow_sub_semigroup_le (hA : A.IsMDissipative) {p q : ℂ[X]}
    (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0)
    (hr : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ 1) {m : ℕ}
    (hm : X ^ (m + 1) ∣ p - q * (expTaylor m).map (algebraMap ℝ ℂ)) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) {u : ℕ → E} (hu : ∀ j < m + 1, (u j, u (j + 1)) ∈ A.graph) :
    ‖((resolventEval q.natDegree p ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹) *
          Ring.inverse (resolventEval q.natDegree q ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹))) ^ n)
          (u 0) - hA.semigroup.S (n * τ) (u 0)‖ ≤
      ((⨆ y : ℝ, ‖((p - q * (expTaylor m).map (algebraMap ℝ ℂ)) /ₘ X ^ (m + 1)).eval
          (y * Complex.I) / q.eval (y * Complex.I)‖) + 1 / (m + 1).factorial) *
        (n * τ) * τ ^ m * ‖u (m + 1)‖ := by
  set N := q.natDegree
  have hpq := natDegree_le_of_norm_div_imaginary_le hq hr
  -- the Cayley form, at `A` and at its Yosida approximations
  set F : (E →ₗ.[ℂ] E) → E →L[ℂ] E := fun B =>
    aeval (cayley B τ) (cayleyPoly N p) * Ring.inverse (aeval (cayley B τ) (cayleyPoly N q))
  have hF : ∀ k, F ((yosida A k : E →ₗ[ℂ] E).toPMap ⊤) =
      aeval ((τ : ℂ) • yosida A k) p * Ring.inverse (aeval ((τ : ℂ) • yosida A k) q) := fun k =>
    aeval_cayley_mul_inverse (re_inner_yosida_le hA k) hτ hpq le_rfl
  -- `q̃` has no zero in the closed disc, so `‖q̃(C)⁻¹‖` is bounded uniformly in the contraction `C`
  obtain ⟨M, hinv⟩ := ContinuousLinearMap.exists_norm_inverse_aeval_le (E := E)
    (q := cayleyPoly N q) fun w hw => eval_cayleyPoly_ne_zero hq hw
  have hCk : ∀ k, ‖cayley ((yosida A k : E →ₗ[ℂ] E).toPMap ⊤) τ‖ ≤ 1 := fun k =>
    norm_cayley_le (isMDissipative_yosida hA k) hτ
  rw [show resolventEval N p ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹) *
      Ring.inverse (resolventEval N q ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹)) = F A from
    resolventEval_mul_inverse_eq A τ N p q]
  have hb := bddAbove_norm_div_imaginary (p := (p - q * (expTaylor m).map (algebraMap ℝ ℂ)) /ₘ
    X ^ (m + 1)) (q := q) (by
      rw [natDegree_divByMonic _ (monic_X_pow _), natDegree_X_pow]
      have h1 := natDegree_sub_le p (q * (expTaylor m).map (algebraMap ℝ ℂ))
      have h2 := natDegree_mul_le (p := q) (q := (expTaylor m).map (algebraMap ℝ ℂ))
      have h3 : ((expTaylor m).map (algebraMap ℝ ℂ)).natDegree ≤ m :=
        natDegree_map_le.trans (RationalScheme.natDegree_expTaylor_le m)
      omega) hq
  refine norm_pow_apply_sub_semigroup_le hA (Pm := fun k => F ((yosida A k : E →ₗ[ℂ] E).toPMap ⊤))
    (fun k => ?_) (ContinuousLinearMap.tendsto_aeval_mul_inverse_apply hCk
      (tendsto_cayley_yosida hA hτ) _ _ (fun k => (hinv _ (hCk k)).1)
      (hinv _ (norm_cayley_le hA hτ)).1 (fun k => (hinv _ (hCk k)).2))
    n (by positivity) hu (by positivity [(norm_nonneg _).trans (le_ciSup hb 0)]) fun k => ?_
  · rw [hF]
    exact (norm_aeval_mul_inverse_le_of_dissipative
      (RationalScheme.dissipative_smul (re_inner_yosida_le hA k) hτ.le) hpq hq hr).2
  · rw [hF]
    exact norm_aeval_mul_inverse_pow_sub_exp_le (re_inner_yosida_le hA k) hq hr hm hτ.le n (u 0)

end Complex

end Feec.TimeStepping
