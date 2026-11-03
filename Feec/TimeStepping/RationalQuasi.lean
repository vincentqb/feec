module

public import Feec.TimeStepping.RationalHilleYosida
public import Feec.Semigroup.Rescale
public import Feec.Semigroup.Spectral

/-!
# Rational approximations of quasi-contractive semigroups

Let `A` be an operator of a Hilbert space over `𝕜 = ℝ` or `ℂ` with `A - ω` m-dissipative,
`ω ≥ 0`: `A` generates a semigroup with `‖S(t)‖ ≤ e^{ωt}` (for instance `L + B` for an
m-dissipative `L` and every bounded `B`, with `ω = ‖B‖`). For an A-stable rational scheme `r`
of order `p` there are `c₀ > 0`, `K` and `κ`, depending only on `r`, such that **Brenner–Thomée's
error bound holds with exponential growth** ([BrennerThomee1979]; [Thomee2006], Ch. 9):

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K e^{κωnτ} nτ τᵖ ‖A^{p+1} x‖`  for `ωτ ≤ c₀`, `x ∈ D(A^{p+1})`

(`RationalScheme.exists_norm_step_pow_sub_le`), with `r(τA)` the operator
`Feec.TimeStepping.RationalScheme.step` (`P(R) Q(R)⁻¹` at the resolvent `R = (1 - τA)⁻¹`).

## The shift argument

With `B = A - ω` and `c = ωτ`, `τA = τB + c`, so `r(τA) = r_c(τB)` for the **shifted scheme**
`r_c(z) = r(z + c)` (`RationalScheme.shift`, a rational scheme as long as `r` has no pole with
`re z ≤ c`). In the resolvent form this is an identity between `X = (1 - τA)⁻¹` and
`Y = (1 - τB)⁻¹`: `X = Y (1 - cY)⁻¹` by the resolvent identity, and
`sᴺ f(1 - 1/s)` at `s = Y (1 - cY)⁻¹` is `(1 - cY)^{-N}` times `sᴺ f(1 - 1/s + c)` at `Y`
(`resolventEval_mul_eq_pow_mul`). Von Neumann's inequality for the m-dissipative `B` then bounds
`‖r(τA)‖ ≤ sup_y |r(iy + c)| ≤ 1 + K₁ c` (`r` is Lipschitz on the half-plane `re z ≤ c₀`, its
derivative being bounded there, `exists_norm_div_le_of_isClosed`) and the remainder
`‖ρ(τA)‖ ≤ sup_{re z ≤ c₀} |ρ(z)|`; these are the stability and remainder hypotheses of
Brenner–Thomée on Banach spaces (`RationalScheme.norm_resolventStep_pow_sub_S_le`), and
`‖r(τA)ᵏ‖ ≤ e^{K₁ ωτ k}`; the invertibility of `Q(X)` holds for every semigroup with
`‖S(t)‖ ≤ e^{ωt}` and `r` without poles in `re z ≤ ωτ`, by the Hille–Yosida estimates
(`RationalScheme.isUnit_resolventEval_den_of_generator`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 9
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.5, §3.1 (quasi-contractive semigroups, bounded perturbations)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter Polynomial Finset Feec.Operator LinearPMap

@[expose] public noncomputable section

namespace Feec.TimeStepping

namespace RationalScheme

variable (r : RationalScheme)

theorem eval_eq (z : ℂ) :
    r.eval z = (r.num.map (algebraMap ℝ ℂ)).eval z / (r.den.map (algebraMap ℝ ℂ)).eval z := by
  rw [eval, eval_map_algebraMap, eval_map_algebraMap]

/-- **`r` is Lipschitz to the right of the imaginary axis**: if `r` has no pole on `re z ≤ c₀`,
then `|r(iy + c)| ≤ |r(iy)| + K c` for `0 ≤ c ≤ c₀` (the derivative
`r' = (n' d - n d')/d²` is bounded on the closed half-plane). -/
theorem exists_norm_eval_add_le {c₀ : ℝ} (hc₀ : ∀ z : ℂ, z.re ≤ c₀ → aeval z r.den ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : ℝ) {c : ℝ}, 0 ≤ c → c ≤ c₀ →
      ‖r.eval (y * Complex.I + c)‖ ≤ ‖r.eval (y * Complex.I)‖ + K * c := by
  set p := r.num.map (algebraMap ℝ ℂ)
  set q := r.den.map (algebraMap ℝ ℂ)
  set F : Set ℂ := {z | z.re ≤ c₀}
  have hF : IsClosed F := isClosed_le Complex.continuous_re continuous_const
  have hqF : ∀ z ∈ F, q.eval z ≠ 0 := fun z hz => by
    rw [eval_map_algebraMap]; exact hc₀ z hz
  have hpN : p.natDegree ≤ q.natDegree := by
    simpa only [p, q, natDegree_map] using r.natDegree_num_le
  have hdeg : (derivative p * q - p * derivative q).natDegree ≤ (q ^ 2).natDegree := by
    rw [natDegree_pow]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_mul_le.trans (by have := natDegree_derivative_le p; omega)
    · exact natDegree_mul_le.trans (by have := natDegree_derivative_le q; omega)
  obtain ⟨K, hK⟩ := exists_norm_div_le_of_isClosed hdeg hF fun z hz => by
    rw [eval_pow]; exact pow_ne_zero _ (hqF z hz)
  refine ⟨max K 0, le_max_right _ _, fun y c hc hcc => ?_⟩
  set g : ℝ → ℂ := fun s => p.eval (y * Complex.I + s) / q.eval (y * Complex.I + s)
  set g' : ℝ → ℂ := fun s => (derivative p * q - p * derivative q).eval (y * Complex.I + s) /
    (q ^ 2).eval (y * Complex.I + s)
  have hmem : ∀ s : ℝ, s ≤ c₀ → y * Complex.I + s ∈ F := fun s hs => by simp [F, hs]
  have hd : ∀ s ∈ Icc 0 c, HasDerivWithinAt g (g' s) (Icc 0 c) s := fun s hs => by
    have hz := hqF _ (hmem s (hs.2.trans hcc))
    have h1 := ((p.hasDerivAt (y * Complex.I + s)).div (q.hasDerivAt (y * Complex.I + s)) hz)
    have h2 := (HasDerivAt.comp_const_add (y * Complex.I) (s : ℂ) h1).comp_ofReal
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    simp only [g', eval_sub, eval_mul, eval_pow]
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun s hs => (hK _ (hmem s (hs.2.le.trans hcc))).trans (le_max_left K 0)) c ⟨hc, le_rfl⟩
  have e1 : r.eval (y * Complex.I + c) = g c := by rw [eval_eq]
  have e0 : r.eval (y * Complex.I) = g 0 := by
    simp only [g, Complex.ofReal_zero, add_zero]; exact r.eval_eq _
  rw [e1, e0]
  calc ‖g c‖ ≤ ‖g 0‖ + ‖g c - g 0‖ := norm_le_insert' _ _
    _ ≤ ‖g 0‖ + max K 0 * c := by simpa using add_le_add_left hb ‖g 0‖

/-! ### The shifted scheme `r(z + c)` -/

/-- **The shifted scheme** `r_c(z) = r(z + c)`, when `r` has no pole on `re z ≤ c`. -/
def shift (c : ℝ) (hc : ∀ z : ℂ, z.re ≤ c → aeval z r.den ≠ 0) : RationalScheme where
  num := r.num.comp (X + C c)
  den := r.den.comp (X + C c)
  natDegree_num_le := by
    rw [natDegree_comp, natDegree_comp, natDegree_X_add_C, mul_one, mul_one]
    exact r.natDegree_num_le
  aeval_den_ne_zero z hz := by
    rw [aeval_comp]
    simpa using hc _ (by simpa using hz)

theorem eval_shift {c : ℝ} (hc : ∀ z : ℂ, z.re ≤ c → aeval z r.den ≠ 0) (z : ℂ) :
    (r.shift c hc).eval z = r.eval (z + c) := by
  simp [eval, shift, aeval_comp]

theorem natDegree_den_shift {c : ℝ} (hc : ∀ z : ℂ, z.re ≤ c → aeval z r.den ≠ 0) :
    (r.shift c hc).den.natDegree = r.den.natDegree := by
  rw [shift, natDegree_comp, natDegree_X_add_C, mul_one]

end RationalScheme

/-! ### The resolvent form under a shift -/

section ShiftEval

variable {𝕜 A : Type*} [Field 𝕜] [Infinite 𝕜] [Ring A] [Algebra 𝕜 A]

/-- `Σₖ fₖ (s - 1 + c s)ᵏ s^{N-k}` is `sᴺ f(1 - 1/s + c)`, the resolvent form of `f(z + c)`. -/
theorem sum_coeff_smul_shift_eq {N : ℕ} {f : 𝕜[X]} (hf : f.natDegree ≤ N) (c : 𝕜) (Y : A) :
    ∑ k ∈ range (N + 1), f.coeff k • ((Y - 1 + c • Y) ^ k * Y ^ (N - k)) =
      resolventEval N (f.comp (X + C c)) Y := by
  have hfc : (f.comp (X + C c)).natDegree ≤ N := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]; exact hf
  have key : ∑ k ∈ range (N + 1), f.coeff k • (((X : 𝕜[X]) - 1 + c • X) ^ k * X ^ (N - k)) =
      resolventEval N (f.comp (X + C c)) X := by
    refine eq_of_infinite_eval_eq _ _ (((Set.infinite_univ (α := 𝕜)).sdiff
      (Set.finite_singleton 0)).mono fun x hx => ?_)
    have hx : x ≠ 0 := hx.2
    simp only [Set.mem_ofPred_eq, eval_resolventEval_X hfc hx, eval_comp, eval_add, eval_X,
      eval_C, eval_finsetSum, eval_smul, eval_mul, eval_pow, eval_sub, eval_one, smul_eq_mul]
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hf), mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [show x ^ N = x ^ (N - k) * x ^ k by rw [← pow_add, Nat.sub_add_cancel hk'],
      show x - 1 + c * x = x * (1 - x⁻¹ + c) by field_simp, mul_pow]
    ring
  have := congrArg (Polynomial.aeval Y) key
  simpa only [map_sum, _root_.map_smul, map_mul, map_pow, _root_.map_sub, _root_.map_add, map_one,
    aeval_X, map_resolventEval] using this

/-- **The resolvent form under a shift**: if `(1 - cY) U = 1` and `Y U = U Y`, then
`sᴺ f(1 - 1/s)` at `s = Y U` is `Uᴺ` times `sᴺ f(1 - 1/s + c)` at `Y` (`deg f ≤ N`): at
`Y = (1 - τB)⁻¹`, `Y U = (1 - τ(B + c/τ))⁻¹`. -/
theorem resolventEval_mul_eq_pow_mul {Y U : A} {c : 𝕜} (hU : (1 - c • Y) * U = 1)
    (hYU : Commute Y U) {N : ℕ} {f : 𝕜[X]} (hf : f.natDegree ≤ N) :
    resolventEval N f (Y * U) = U ^ N * resolventEval N (f.comp (X + C c)) Y := by
  rw [← sum_coeff_smul_shift_eq hf c Y, resolventEval, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
  set W := Y - 1 + c • Y
  have hW : Y * U - 1 = W * U := by
    calc Y * U - 1 = Y * U - (1 - c • Y) * U := by rw [hU]
      _ = W * U := by simp only [W, sub_mul, add_mul, one_mul, smul_mul_assoc]; abel
  have hWU : Commute W U := (hYU.sub_left (Commute.one_left U)).add_left (hYU.smul_left c)
  have hWY : Commute W Y :=
    ((Commute.refl Y).sub_left (Commute.one_left Y)).add_left ((Commute.refl Y).smul_left c)
  rw [hW, hWU.mul_pow, hYU.mul_pow, mul_smul_comm]
  congr 1
  calc W ^ k * U ^ k * (Y ^ (N - k) * U ^ (N - k))
      = W ^ k * Y ^ (N - k) * (U ^ k * U ^ (N - k)) := by
        rw [mul_assoc, ← mul_assoc (U ^ k), ((hYU.pow_pow (N - k) k).eq).symm]; noncomm_ring
    _ = U ^ N * (W ^ k * Y ^ (N - k)) := by
        rw [← pow_add, Nat.add_sub_cancel' hk']
        exact (((hWU.pow_pow k N).mul_left (hYU.pow_pow (N - k) N))).eq

end ShiftEval

namespace RationalScheme

variable (r : RationalScheme)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **`r(τA) = r_c(τB)` in the resolvent form**: if `(1 - cY) U = 1`, `U` invertible and
commuting with `Y`, then `r` at `Y U` is the shifted scheme `r_c` at `Y`. -/
theorem resolventStep_mul_eq_shift {Y U : E →L[𝕜] E} {c : ℝ}
    (hc : ∀ z : ℂ, z.re ≤ c → aeval z r.den ≠ 0) (hU : (1 - (c : 𝕜) • Y) * U = 1)
    (hUu : IsUnit U) (hYU : Commute Y U) :
    r.resolventStep (Y * U) = (r.shift c hc).resolventStep Y := by
  have hmap : ∀ f : ℝ[X], (f.comp (X + C c)).map (algebraMap ℝ 𝕜) =
      (f.map (algebraMap ℝ 𝕜)).comp (X + C (c : 𝕜)) := fun f => by
    rw [Polynomial.map_comp]; simp
  have hN := r.natDegree_den_shift hc
  have hn := resolventEval_mul_eq_pow_mul hU hYU
    (natDegree_map_le.trans r.natDegree_num_le : (r.num.map (algebraMap ℝ 𝕜)).natDegree ≤ _)
  have hd := resolventEval_mul_eq_pow_mul hU hYU
    (natDegree_map_le.trans le_rfl : (r.den.map (algebraMap ℝ 𝕜)).natDegree ≤ r.den.natDegree)
  have hcomm : ∀ g : 𝕜[X], Commute (U ^ r.den.natDegree) (resolventEval r.den.natDegree g Y) :=
    fun g => by
      have h := map_resolventEval (Polynomial.aeval Y) r.den.natDegree g X
      rw [aeval_X] at h
      rw [← h]
      exact (commute_aeval (hYU.pow_right _) _).symm
  rw [resolventStep, resolventStep, hN, hn, hd]
  simp only [shift, hmap]
  exact Ring.mul_inverse_mul_of_commute (hUu.pow _) (hcomm _) (hcomm _)

/-! ### Quasi-contractive semigroups on Hilbert spaces -/

section Quasi

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Brenner–Thomée for quasi-contractive semigroups, with explicit constants**: let `r` be
A-stable of order `p`, without poles on `re z ≤ c₀ ≤ 1/2`, `|r(iy + c)| ≤ |r(iy)| + K₁ c` and
`|ρ(z)| ≤ Kρ` on `re z ≤ c₀` (`ρ` the remainder). For `A` with `A - ω` m-dissipative (`ω ≥ 0`),
every semigroup `G` generated by `A` (so `‖S(t)‖ ≤ e^{ωt}`), `τ > 0` with `ωτ ≤ c₀`, `n` and
`x ∈ D(A^{p+1})`: `‖r(τA)ⁿ x - S(nτ) x‖ ≤ (Kρ + 1/(p+1)!) e^{(K₁+2)ωnτ} nτ τᵖ ‖A^{p+1} x‖`. -/
theorem norm_step_pow_sub_le_of_shift (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {c₀ K₁ Kρ : ℝ} (hc₀ : ∀ z : ℂ, z.re ≤ c₀ → aeval z r.den ≠ 0)
    (hc₀2 : c₀ ≤ 1 / 2) (hK₁ : 0 ≤ K₁)
    (hlip : ∀ (y : ℝ) {c : ℝ}, 0 ≤ c → c ≤ c₀ →
      ‖r.eval (y * Complex.I + c)‖ ≤ ‖r.eval (y * Complex.I)‖ + K₁ * c)
    (hρ : ∀ z : ℂ, z.re ≤ c₀ → ‖(r.remainder p).eval z‖ ≤ Kρ) {A : E →ₗ.[𝕜] E} {ω : ℝ}
    (hω : 0 ≤ ω) (hB : (((-(ω : 𝕜)) • (LinearMap.id : E →ₗ[𝕜] E)) +ᵥ A).IsMDissipative)
    (G : C0Semigroup 𝕜 E) (hG : G.generator = A) {τ : ℝ} (hτ : 0 < τ) (hωτ : ω * τ ≤ c₀)
    (n : ℕ) {u : ℕ → E} (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ A.graph) :
    ‖(r.step A τ ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      (Kρ + 1 / (p + 1).factorial) * Real.exp ((K₁ + 2) * ω * (n * τ)) * (n * τ) * τ ^ p *
        ‖u (p + 1)‖ := by
  set c := ω * τ
  have hc : 0 ≤ c := mul_nonneg hω hτ.le
  have hcF : ∀ z : ℂ, z.re ≤ c → aeval z r.den ≠ 0 := fun z hz => hc₀ z (hz.trans hωτ)
  set B := ((-(ω : 𝕜)) • (LinearMap.id : E →ₗ[𝕜] E)) +ᵥ A
  -- the resolvents `X = (1 - τA)⁻¹` and `Y = (1 - τB)⁻¹`
  have hτinv : 0 < RCLike.re ((τ : 𝕜)⁻¹) := by
    rw [← RCLike.ofReal_inv, RCLike.ofReal_re]; positivity
  have hz₁ : 0 < RCLike.re ((τ : 𝕜)⁻¹ - (ω : 𝕜)) := by
    rw [← RCLike.ofReal_inv, ← RCLike.ofReal_sub, RCLike.ofReal_re,
      show τ⁻¹ - ω = (1 - ω * τ) / τ by field_simp]
    exact div_pos (by linarith) hτ
  have hR₁ := hB.isResolvent_of_re_pos hz₁
  have hRA : IsResolvent A (τ : 𝕜)⁻¹ (resolvent B ((τ : 𝕜)⁻¹ - ω)) := hR₁.of_neg_smul_vadd
  have hR₂ := hB.isResolvent_of_re_pos hτinv
  set R₁ := resolvent B ((τ : 𝕜)⁻¹ - ω)
  set R₂ := resolvent B (τ : 𝕜)⁻¹
  set X := (τ : 𝕜)⁻¹ • resolvent A (τ : 𝕜)⁻¹
  have hXR : X = (τ : 𝕜)⁻¹ • R₁ := by simp only [X, hRA.resolvent_eq]
  set Y := (τ : 𝕜)⁻¹ • R₂
  have hτ0 : (τ : 𝕜) ≠ 0 := by exact_mod_cast hτ.ne'
  have hXY : X * (1 - (c : 𝕜) • Y) = Y := by
    have h := hR₁.sub_eq hR₂
    rw [sub_sub_cancel] at h
    have h' : R₁ - (ω : 𝕜) • (R₁ * R₂) = R₂ := by rw [← h]; abel
    calc X * (1 - (c : 𝕜) • Y)
        = (τ : 𝕜)⁻¹ • R₁ - ((c : 𝕜) * ((τ : 𝕜)⁻¹ * (τ : 𝕜)⁻¹)) • (R₁ * R₂) := by
          rw [hXR, mul_sub, mul_one, mul_smul_comm, smul_mul_smul_comm, smul_smul]
      _ = (τ : 𝕜)⁻¹ • (R₁ - (ω : 𝕜) • (R₁ * R₂)) := by
          rw [smul_sub, smul_smul]; congr 2; simp only [c]; push_cast; field_simp
      _ = Y := by rw [h']
  have hYn : ‖Y‖ ≤ 1 := by
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hτ]
    have := hR₂.norm_le_of_isDissipative hB.dissipative hτinv
    rw [← RCLike.ofReal_inv, RCLike.ofReal_re, inv_inv] at this
    calc τ⁻¹ * ‖R₂‖ ≤ τ⁻¹ * τ := by gcongr
      _ = 1 := inv_mul_cancel₀ hτ.ne'
  have hcY : ‖(c : 𝕜) • Y‖ < 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hc]
    calc c * ‖Y‖ ≤ c * 1 := by gcongr
      _ < 1 := by linarith
  set V := Units.oneSub ((c : 𝕜) • Y) hcY
  set U : E →L[𝕜] E := ↑V⁻¹
  have hU : (1 - (c : 𝕜) • Y) * U = 1 := by
    rw [← Units.val_oneSub _ hcY]; exact V.mul_inv
  have hYU : Commute Y U := by
    have : Commute Y ↑V := by
      rw [Units.val_oneSub]
      exact (Commute.one_right Y).sub_right ((Commute.refl Y).smul_right _)
    exact this.units_inv_right
  have hXeq : X = Y * U := by rw [← hXY, mul_assoc, hU, mul_one]
  -- the shifted schemes at `Y`: von Neumann's inequality for `B`
  have hsr := r.resolventStep_mul_eq_shift hcF hU V⁻¹.isUnit hYU
  have hcFρ : ∀ z : ℂ, z.re ≤ c → aeval z (r.remainder p).den ≠ 0 := hcF
  have hsρ := (r.remainder p).resolventStep_mul_eq_shift hcFρ hU V⁻¹.isUnit hYU
  have hstepB : ∀ s : RationalScheme, s.resolventStep Y = s.step B τ := fun s =>
    (s.step_eq_resolventStep B τ).symm
  have hP : ‖r.resolventStep X‖ ≤ Real.exp (K₁ * c) := by
    rw [hXeq, hsr, hstepB]
    refine ((r.shift c hcF).norm_step_le hB hτ).2.trans ((ciSup_le (c := 1 + K₁ * c)
      fun y => ?_).trans
      (by linarith [Real.add_one_le_exp (K₁ * c)]))
    rw [eval_shift]
    linarith [hlip y hc hωτ, hr y]
  have hst : ∀ k ≤ n, ‖r.resolventStep X ^ k‖ ≤ Real.exp (K₁ * ω * (n * τ)) := fun k hk => by
    refine (norm_pow_le_pow hP k).trans ?_
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    calc (k : ℝ) * (K₁ * c) = K₁ * ω * (k * τ) := by simp only [c]; ring
      _ ≤ K₁ * ω * (n * τ) := by gcongr
  have hρ' : ‖(r.remainder p).resolventStep X‖ ≤ Kρ := by
    rw [hXeq, hsρ, hstepB]
    refine (((r.remainder p).shift c hcFρ).norm_step_le hB hτ).2.trans (ciSup_le fun y => ?_)
    rw [eval_shift]
    exact hρ _ (by simpa using hωτ)
  have hQ : IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) X) :=
    r.isUnit_resolventEval_den_of_generator G (M := 1)
      (fun t ht => (one_mul (Real.exp (ω * t))).symm ▸ hB.norm_S_le_of_generator_eq hG ht) hτ
      (by linarith) hcF fun x y hxy => by
        rw [hXR]; exact hRA.inv_smul_apply_sub hτ.ne' (hG ▸ hxy)
  have hS : ∀ t ∈ Icc 0 (n * τ), ‖G.S t‖ ≤ Real.exp (ω * (n * τ)) := fun t ht =>
    (hB.norm_S_le_of_generator_eq hG ht.1).trans
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hω))
  have hstep : ∀ s : RationalScheme, s.step A τ = s.resolventStep X := fun s =>
    s.step_eq_resolventStep A τ
  rw [hXR] at hQ
  have hmain := r.norm_step_pow_sub_S_le G hG hp hτ hRA hQ (fun k hk => hstep r ▸ hst k hk) hS
    (hstep _ ▸ hρ') hu
  refine hmain.trans ?_
  set M := Real.exp (ω * (n * τ))
  set Ms := Real.exp (K₁ * ω * (n * τ))
  have hM1 : 1 ≤ M := Real.one_le_exp (by positivity)
  have hKρ : 0 ≤ Kρ := (norm_nonneg _).trans hρ'
  have hf : (0 : ℝ) < (p + 1).factorial := by positivity
  have he : Real.exp ((K₁ + 2) * ω * (n * τ)) = Ms * M * M := by
    simp only [Ms, M, ← Real.exp_add]; congr 1; ring
  have hk : Ms * (Kρ + M / (p + 1).factorial) * M ≤
      (Kρ + 1 / (p + 1).factorial) * Real.exp ((K₁ + 2) * ω * (n * τ)) := by
    rw [he]
    have h1 : Kρ + M / (p + 1).factorial ≤ (Kρ + 1 / (p + 1).factorial) * M := by
      rw [add_mul, div_mul_eq_mul_div, one_mul]
      gcongr
      exact le_mul_of_one_le_right hKρ hM1
    have hMs : 0 ≤ Ms := (Real.exp_pos _).le
    calc Ms * (Kρ + M / (p + 1).factorial) * M ≤ Ms * ((Kρ + 1 / (p + 1).factorial) * M) * M := by
          gcongr
      _ = _ := by ring
  have hnn : 0 ≤ (n * τ) * τ ^ p * ‖u (p + 1)‖ := by positivity
  calc Ms * (Kρ + M / (p + 1).factorial) * M * (n * τ) * τ ^ p * ‖u (p + 1)‖
      = (Ms * (Kρ + M / (p + 1).factorial) * M) * ((n * τ) * τ ^ p * ‖u (p + 1)‖) := by ring
    _ ≤ ((Kρ + 1 / (p + 1).factorial) * Real.exp ((K₁ + 2) * ω * (n * τ))) *
        ((n * τ) * τ ^ p * ‖u (p + 1)‖) := mul_le_mul_of_nonneg_right hk hnn
    _ = _ := by ring

/-- **Brenner–Thomée for quasi-contractive semigroups**: for an A-stable rational scheme `r` of
order `p` there are `c₀ > 0`, `K ≥ 0` and `κ ≥ 0`, depending only on `r`, such that for every
Hilbert space over `𝕜`, every `A` with `A - ω` m-dissipative (`ω ≥ 0`), every semigroup `G`
generated by `A`, every `τ > 0` with `ωτ ≤ c₀`, every `n` and every
`x ∈ D(A^{p+1})` (a chain `u` in the graph of `A`),
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ K e^{κωnτ} nτ τᵖ ‖A^{p+1} x‖`. [BrennerThomee1979]; [Thomee2006], Ch. 9 -/
theorem exists_norm_step_pow_sub_le (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K κ : ℝ, 0 ≤ K ∧ 0 ≤ κ ∧
      ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E} {ω : ℝ}, 0 ≤ ω →
        (((-(ω : 𝕜)) • (LinearMap.id : E →ₗ[𝕜] E)) +ᵥ A).IsMDissipative →
        ∀ G : C0Semigroup 𝕜 E, G.generator = A → ∀ {τ : ℝ}, 0 < τ → ω * τ ≤ c₀ → ∀ (n : ℕ) {u : ℕ → E},
          (∀ j < p + 1, (u j, u (j + 1)) ∈ A.graph) →
          ‖(r.step A τ ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
            K * Real.exp (κ * ω * (n * τ)) * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  obtain ⟨c₀, hc₀, hc₀2, hden⟩ := r.exists_den_ne_zero
  obtain ⟨K₁, hK₁, hlip⟩ := r.exists_norm_eval_add_le hden
  obtain ⟨Kρ, hKρ⟩ := exists_norm_div_le_of_isClosed
    (p := (r.remainder p).num.map (algebraMap ℝ ℂ)) (q := (r.remainder p).den.map (algebraMap ℝ ℂ))
    (by simpa only [natDegree_map] using (r.remainder p).natDegree_num_le)
    (isClosed_le Complex.continuous_re continuous_const) fun z (hz : z.re ≤ c₀) => by
      rw [eval_map_algebraMap]; exact hden z hz
  refine ⟨c₀, hc₀, max Kρ 0 + 1 / (p + 1).factorial, K₁ + 2,
    add_nonneg (le_max_right _ _) (by positivity), by linarith,
    fun hω hB G hG τ hτ hωτ n u hu => ?_⟩
  exact r.norm_step_pow_sub_le_of_shift hr hp hden hc₀2 hK₁ hlip
    (fun z hz => (r.remainder p).eval_eq z ▸ (hKρ z hz).trans (le_max_left _ _)) hω hB G hG hτ hωτ n
    hu

end Quasi

end RationalScheme

end Feec.TimeStepping
