module

public import Feec.TimeStepping.RationalBanach
public import Feec.Semigroup.HilleYosida
public import Feec.Semigroup.Complexification

/-!
# Rational schemes on Banach spaces from the Hille–Yosida estimates

Let `G` be a strongly continuous semigroup on a Banach space `E` over `𝕜 = ℝ` or `ℂ`, with
generator `A` and `‖S(t)‖ ≤ M e^{ωt}`, and let `R = (1 - τA)⁻¹`, `τ > 0`, `ωτ < 1`. For a real
polynomial `d` of degree `N` without roots in `re z ≤ ωτ`, the operator `Q(R) = Rᴺ d(1 - R⁻¹)`
(`resolventEval`; `d(τA)` up to `R^N`) is invertible, with

  `‖Q(R)⁻¹‖ ≤ |d_N|⁻¹ ∏_{d(ζ) = 0} (1 + |1 - ζ| M / (re ζ - ωτ))`

(`isUnit_resolventEval_of_generator`). Over `ℂ`, `Q(R) = d_N ∏ ((1 - ζ) R - 1)` over the roots
`ζ` of `d`, and `(1 - ζ) R - 1 = R (τA - ζ)` has the inverse `-1 - (1 - ζ)(ζ - τA)⁻¹`; the
Hille–Yosida estimate at `ζ/τ`, `re ζ/τ > ω`, bounds it by `1 + |1 - ζ| M/(re ζ - ωτ)`
(`Feec.C0Semigroup.norm_resolvent_pow_le`). Over `ℝ` the roots are complex: the argument runs on
the complexification of `E` and of `G` (`NormedComplexification`, `C0Semigroup.complexification`),
and invertibility and the bound come back because `T` is invertible when `T_ℂ` is, with
`‖T_ℂ⁻¹‖ = ‖T⁻¹‖`.

For a rational scheme `r` (whose poles lie in `re z > 0`) this discharges two hypotheses of
Brenner–Thomée on Banach spaces (`RationalScheme.norm_resolventStep_pow_sub_S_le`): `Q(R)` is
invertible, and the remainder `ρ = (r - Tₚ)/z^{p+1}` is bounded, `‖ρ(τA)‖ ≤ K₀` uniformly in
`ωτ ≤ c` with `c > 0` and `K₀` depending only on `r`, `p` and `M`
(`RationalScheme.exists_norm_remainder_resolventStep_le`); A-stability is not needed. What
remains is the **stability** `‖r(τA)ⁿ‖ ≤ Mₛ`
(`RationalScheme.exists_norm_resolventStep_pow_sub_S_le`). It is not automatic on Banach spaces,
even for A-stable `r` (for bounded semigroups Brenner and Thomée bound `‖r(τA)ⁿ‖` by `C √n`,
[BrennerThomee1979]); it holds for **backward Euler** `r = 1/(1 - z)`, for which `r(τA) = R`
(`RationalScheme.resolventStep_theta_one`) and the Hille–Yosida estimates `‖Rᵏ‖ ≤ M/(1 - ωτ)ᵏ`
give it (`norm_pow_le_of_generator`). Backward Euler therefore has the error
bound with no hypothesis beyond the growth bound of the semigroup
(`RationalScheme.norm_backwardEuler_pow_sub_S_le`):

  `‖Rⁿ x - S(nτ) x‖ ≤ (M/(1 - ωτ)ⁿ) (M/(1 - ωτ) + M e^{ωnτ}/2) M e^{ωnτ} nτ τ ‖A² x‖`.

The same estimates give stability for every positive combination `r = Σ c_k (1 - bz)^{-k}`,
`b > 0`, `c_k ≥ 0`, of powers of one resolvent; this is not formalized, since such `r` are
absolutely monotone on `z < 1/b` and positivity-preserving rational approximations of `e^z`
have order at most `1` ([BolleyCrouzeix1978], as recalled; the paper was not consulted), so they
add no order beyond backward Euler.

## Main results

* `isUnit_resolventEval_of_generator`: `Q(R)` invertible, with the bound above;
* `RationalScheme.norm_resolventStep_le_of_generator`: `‖r(τA)‖` bounded by the coefficients of
  `r`, the roots of its denominator and `M` (for every rational scheme; with `r = ρ`, the
  remainder bound);
* `RationalScheme.exists_norm_remainder_resolventStep_le`: the uniform remainder bound;
* `RationalScheme.exists_norm_resolventStep_pow_sub_S_le`: **Brenner–Thomée on Banach spaces with
  only the stability assumed**;
* `norm_pow_le_of_generator`, `RationalScheme.norm_backwardEuler_pow_sub_S_le`: **backward Euler
  on Banach spaces**, stability and error.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 9
* [C. Bolley, M. Crouzeix, *Conservation de la positivité lors de la discrétisation des problèmes d'évolution paraboliques*][BolleyCrouzeix1978]
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.5 (the Hille–Yosida estimates)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Finset Polynomial Feec.Operator Complexification

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### Linear factors of `sᴺ d(1 - 1/s)` -/

section Factor

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem resolventEval_X_sub_C (ζ : ℂ) (S : A) :
    resolventEval 1 (X - C ζ) S = (1 - ζ) • S - 1 := by
  rw [resolventEval, sum_range_succ, sum_range_one]
  have h0 : (X - C ζ).coeff 0 = -ζ := by simp
  have h1 : (X - C ζ).coeff 1 = 1 := by simp
  rw [h0, h1]
  simp only [pow_zero, one_mul, Nat.sub_zero, pow_one, Nat.sub_self, mul_one, one_smul, neg_smul,
    sub_smul]
  abel

theorem resolventEval_C_mul (N : ℕ) (a : ℂ) (f : ℂ[X]) (S : A) :
    resolventEval N (C a * f) S = a • resolventEval N f S := by
  simp only [resolventEval, coeff_C_mul, mul_smul, smul_sum]

theorem natDegree_list_prod_X_sub_C_le (L : List ℂ) :
    (L.map fun ζ => X - C ζ).prod.natDegree ≤ L.length := by
  induction L with
  | nil => simp
  | cons ζ L ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons]
    exact natDegree_mul_le.trans (by have := natDegree_X_sub_C_le ζ; omega)

/-- **`sᴺ d(1 - 1/s)` factors over the roots**: for `d = ∏ (X - ζ)`,
`sᴺ d(1 - 1/s) = ∏ ((1 - ζ) s - 1)`. -/
theorem resolventEval_list_prod (L : List ℂ) (S : A) :
    resolventEval L.length (L.map fun ζ => X - C ζ).prod S =
      (L.map fun ζ => (1 - ζ) • S - 1).prod := by
  induction L with
  | nil => simpa using resolventEval_one (𝕜 := ℂ) 0 S
  | cons ζ L ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, add_comm,
      resolventEval_mul (natDegree_X_sub_C_le ζ) (natDegree_list_prod_X_sub_C_le L),
      resolventEval_X_sub_C, ih, List.map_cons, List.prod_cons]

/-- **The inverse of a linear factor**: if `T - W = (ζ - 1) T W` and `T W = W T`, then
`(1 - ζ) T - 1` has the inverse `-1 - (1 - ζ) W` (for `T = (1 - τA)⁻¹`, `W = (ζ - τA)⁻¹`). -/
theorem mul_neg_one_sub_smul {T W : A} {ζ : ℂ} (h : T - W = (ζ - 1) • (T * W)) (hc : Commute T W) :
    ((1 - ζ) • T - 1) * (-1 - (1 - ζ) • W) = 1 ∧ (-1 - (1 - ζ) • W) * ((1 - ζ) • T - 1) = 1 := by
  have h' : (1 - ζ) • (T * W) = W - T := by
    rw [show (1 - ζ) = -(ζ - 1) by ring, neg_smul, ← h]; abel
  have h'' : (1 - ζ) • (W * T) = W - T := by rw [← hc.eq]; exact h'
  constructor
  · calc ((1 - ζ) • T - 1) * (-1 - (1 - ζ) • W)
        = 1 - (1 - ζ) • T + (1 - ζ) • W - (1 - ζ) • ((1 - ζ) • (T * W)) := by
          simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_neg, mul_one, one_mul,
            smul_smul]
          module
      _ = 1 := by rw [h']; module
  · calc (-1 - (1 - ζ) • W) * ((1 - ζ) • T - 1)
        = 1 - (1 - ζ) • T + (1 - ζ) • W - (1 - ζ) • ((1 - ζ) • (W * T)) := by
          simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
            neg_mul, smul_smul]
          module
      _ = 1 := by rw [h'']; module

end Factor

/-! ### `‖sᴺ f(1 - 1/s)‖` -/

section Norm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `‖sᴺ f(1 - 1/s)‖ ≤ (∑ₖ ‖fₖ‖) (‖S‖ + 1)ᴺ` at a bounded operator `S`. -/
theorem norm_resolventEval_le (N : ℕ) (f : 𝕜[X]) (S : E →L[𝕜] E) :
    ‖resolventEval N f S‖ ≤ (∑ k ∈ range (N + 1), ‖f.coeff k‖) * (‖S‖ + 1) ^ N := by
  rw [resolventEval, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
  have hk' : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : ‖S - 1‖ ≤ ‖S‖ + 1 :=
    (norm_sub_le _ _).trans (add_le_add_right ContinuousLinearMap.norm_id_le _)
  calc ‖(S - 1) ^ k * S ^ (N - k)‖ ≤ ‖(S - 1) ^ k‖ * ‖S ^ (N - k)‖ := norm_mul_le _ _
    _ ≤ (‖S‖ + 1) ^ k * (‖S‖ + 1) ^ (N - k) :=
      mul_le_mul (norm_pow_le_pow h1 k) (norm_pow_le_pow (by linarith) (N - k)) (norm_nonneg _)
        (by positivity)
    _ = (‖S‖ + 1) ^ N := by rw [← pow_add, Nat.add_sub_cancel' hk']

end Norm

private theorem lt_inv_of_mul_lt {τ ω : ℝ} (hτ : 0 < τ) (h : ω * τ < 1) : ω < τ⁻¹ := by
  rw [← one_div]; exact (lt_div_iff₀ hτ).2 h

/-! ### Complex Banach spaces -/

section Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- `B L = 1 = L B` and `‖B‖ ≤ ∏ b` for a list of invertible operators with bounded inverses. -/
private theorem exists_inverse_list_prod (L : List ℂ) (f : ℂ → F →L[ℂ] F) (b : ℂ → ℝ)
    (h : ∀ ζ ∈ L, 0 ≤ b ζ ∧ ∃ g, g * f ζ = 1 ∧ f ζ * g = 1 ∧ ‖g‖ ≤ b ζ) :
    ∃ B, B * (L.map f).prod = 1 ∧ (L.map f).prod * B = 1 ∧ ‖B‖ ≤ (L.map b).prod := by
  induction L with
  | nil =>
    refine ⟨1, by simp, by simp, ?_⟩
    rw [List.map_nil, List.prod_nil]
    exact ContinuousLinearMap.norm_id_le
  | cons ζ L ih =>
    obtain ⟨B, h1, h2, h3⟩ := ih fun ζ' hζ' => h ζ' (List.mem_cons_of_mem _ hζ')
    obtain ⟨hb, g, hg1, hg2, hg3⟩ := h ζ List.mem_cons_self
    have hL : 0 ≤ (L.map b).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨ζ', hζ', rfl⟩ := List.mem_map.1 hx
        exact (h ζ' (List.mem_cons_of_mem _ hζ')).1
    refine ⟨B * g, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, mul_assoc, ← mul_assoc g, hg1, one_mul, h1]
    · rw [List.map_cons, List.prod_cons, mul_assoc, ← mul_assoc _ B, h2, one_mul, hg2]
    · rw [List.map_cons, List.prod_cons, mul_comm (b ζ)]
      exact (norm_mul_le _ _).trans (mul_le_mul h3 hg3 (norm_nonneg _) hL)

/-- **Invertibility of `sᴺ d(1 - 1/s)` at `(1 - τA)⁻¹` on complex Banach spaces.** -/
private theorem isUnit_resolventEval_complex (H : Feec.C0Semigroup ℂ F) {M ω τ : ℝ}
    (hS : ∀ t, 0 ≤ t → ‖H.S t‖ ≤ M * Real.exp (ω * t)) (hτ : 0 < τ) (hτω : ω * τ < 1)
    {d : ℝ[X]} (hd : ∀ z : ℂ, z.re ≤ ω * τ → aeval z d ≠ 0) :
    IsUnit (resolventEval d.natDegree (d.map (algebraMap ℝ ℂ))
        ((τ : ℂ)⁻¹ • resolvent H.generator (τ : ℂ)⁻¹)) ∧
      ‖Ring.inverse (resolventEval d.natDegree (d.map (algebraMap ℝ ℂ))
        ((τ : ℂ)⁻¹ • resolvent H.generator (τ : ℂ)⁻¹))‖ ≤
        |d.leadingCoeff|⁻¹ * ((d.map (algebraMap ℝ ℂ)).roots.map
          fun ζ => 1 + ‖1 - ζ‖ * (M / (ζ.re - ω * τ))).prod := by
  set q := d.map (algebraMap ℝ ℂ)
  set T := (τ : ℂ)⁻¹ • resolvent H.generator (τ : ℂ)⁻¹
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hd0 : d ≠ 0 := fun h => hd (ω * τ : ℝ) (by simp) (by simp [h])
  have hq0 : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).2 hd0
  have hlc : q.leadingCoeff = (d.leadingCoeff : ℂ) := leadingCoeff_map _
  have hlc0 : (d.leadingCoeff : ℂ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.2 hd0
  set L := q.roots.toList
  have hLq : (L : Multiset ℂ) = q.roots := Multiset.coe_toList _
  have hlen : L.length = d.natDegree := by
    rw [← Multiset.coe_card, hLq, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
  have hfac : q = C (d.leadingCoeff : ℂ) * (L.map fun ζ => X - C ζ).prod := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := q))]
    rw [hlc, ← hLq, Multiset.map_coe, Multiset.prod_coe]
  have hQ : resolventEval d.natDegree q T =
      (d.leadingCoeff : ℂ) • (L.map fun ζ => (1 - ζ) • T - 1).prod := by
    conv_lhs => rw [hfac]
    rw [resolventEval_C_mul, ← hlen, resolventEval_list_prod]
  -- the resolvent at `1/τ`
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hS 0 le_rfl)
  have hω1 : ω < τ⁻¹ := lt_inv_of_mul_lt hτ hτω
  have hR1 : IsResolvent H.generator (τ : ℂ)⁻¹ (resolvent H.generator (τ : ℂ)⁻¹) :=
    H.isResolvent_resolvent hS
      (by rwa [← Complex.ofReal_inv, RCLike.re_to_complex, Complex.ofReal_re])
  -- the factors `(1 - ζ) X - 1`
  have hfac' : ∀ ζ ∈ L, 0 ≤ 1 + ‖1 - ζ‖ * (M / (ζ.re - ω * τ)) ∧ ∃ g : F →L[ℂ] F,
      g * ((1 - ζ) • T - 1) = 1 ∧ ((1 - ζ) • T - 1) * g = 1 ∧
        ‖g‖ ≤ 1 + ‖1 - ζ‖ * (M / (ζ.re - ω * τ)) := fun ζ hζ => by
    have hζre : ω * τ < ζ.re := by
      by_contra h
      rw [Multiset.mem_toList, mem_roots hq0, IsRoot, eval_map_algebraMap] at hζ
      exact hd ζ (not_lt.1 h) hζ
    set w : ℂ := ζ * ((τ⁻¹ : ℝ) : ℂ)
    have hwre : w.re = ζ.re * τ⁻¹ := Complex.re_mul_ofReal _ _
    have hw : ω < w.re := by
      rw [hwre]
      have := (div_lt_div_iff_of_pos_right hτ).2 hζre
      rwa [mul_div_cancel_right₀ _ hτ.ne', div_eq_mul_inv] at this
    have hRw := H.isResolvent_resolvent hS (z := w) hw
    set W := (τ : ℂ)⁻¹ • resolvent H.generator w
    have hrel : T - W = (ζ - 1) • (T * W) := by
      simp only [T, W, ← smul_sub, hR1.sub_eq hRw, smul_mul_smul_comm, smul_smul]
      congr 1
      simp only [w]
      push_cast
      field_simp
    have hc : Commute T W := ((hR1.commute hRw).smul_left _).smul_right _
    have hden : 0 < ζ.re - ω * τ := sub_pos.2 hζre
    have hWn : ‖W‖ ≤ M / (ζ.re - ω * τ) := by
      have h1 := H.norm_resolvent_pow_le hS (z := w) hw 1
      rw [pow_one, pow_one] at h1
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hτ.le]
      calc τ⁻¹ * ‖resolvent H.generator w‖ ≤ τ⁻¹ * (M / (w.re - ω)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hτ.le)
        _ = M / (ζ.re - ω * τ) := by
            rw [hwre]
            have : ζ.re * τ⁻¹ - ω = (ζ.re - ω * τ) / τ := by field_simp
            rw [this]
            field_simp
    have hb : 0 ≤ M / (ζ.re - ω * τ) := div_nonneg hM hden.le
    obtain ⟨h1, h2⟩ := mul_neg_one_sub_smul hrel hc
    refine ⟨by positivity, -1 - (1 - ζ) • W, h2, h1, ?_⟩
    calc ‖-1 - (1 - ζ) • W‖ ≤ ‖(-1 : F →L[ℂ] F)‖ + ‖(1 - ζ) • W‖ := norm_sub_le _ _
      _ ≤ 1 + ‖1 - ζ‖ * (M / (ζ.re - ω * τ)) := by
        rw [norm_neg, norm_smul]
        exact add_le_add ContinuousLinearMap.norm_id_le
          (mul_le_mul_of_nonneg_left hWn (norm_nonneg _))
  obtain ⟨B, hB1, hB2, hB3⟩ := exists_inverse_list_prod L _ _ hfac'
  set P := (L.map fun ζ => (1 - ζ) • T - 1).prod
  have hu1 : (d.leadingCoeff : ℂ) • P * ((d.leadingCoeff : ℂ)⁻¹ • B) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hlc0, one_smul, hB2]
  have hu2 : (d.leadingCoeff : ℂ)⁻¹ • B * ((d.leadingCoeff : ℂ) • P) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hlc0, one_smul, hB1]
  rw [hQ]
  refine ⟨⟨⟨_, _, hu1, hu2⟩, rfl⟩, ?_⟩
  rw [show (d.leadingCoeff : ℂ) • P = ((⟨_, _, hu1, hu2⟩ : (F →L[ℂ] F)ˣ) : F →L[ℂ] F) from rfl,
    Ring.inverse_unit]
  change ‖(d.leadingCoeff : ℂ)⁻¹ • B‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← hLq, Multiset.map_coe,
    Multiset.prod_coe]
  exact mul_le_mul_of_nonneg_left hB3 (inv_nonneg.2 (abs_nonneg _))

end Complex

/-! ### Banach spaces over `𝕜 = ℝ` or `ℂ` -/

section Banach

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : Feec.C0Semigroup 𝕜 E)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- Complexification commutes with `sᴺ f(1 - 1/s)` for real `f`. -/
theorem map_resolventEval_map {n : ComplexificationNorm} [NormCore n 𝕜 E] (N : ℕ) (f : ℝ[X])
    (S : E →L[𝕜] E) :
    map (n := n) (resolventEval N (f.map (algebraMap ℝ 𝕜)) S) =
      resolventEval N (f.map (algebraMap ℝ ℂ)) (map (n := n) S) := by
  rw [← mapHom_apply, resolventEval, resolventEval, map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_map, coeff_map, RCLike.algebraMap_eq_ofReal, Complex.coe_algebraMap, mapHom_apply,
    map_ofReal_smul, ← mapHom_apply, map_mul, map_pow, map_pow, map_sub, map_one, mapHom_apply]

/-- **`(1 - τA)⁻¹` is the resolvent**: `R = τ⁻¹ (τ⁻¹ - A)⁻¹` for `R (x - τ A x) = x` on `D(A)`,
`τ > 0`, `ωτ < 1`, when `‖S(t)‖ ≤ M e^{ωt}`. -/
theorem eq_inv_smul_resolvent_of_generator {M ω τ : ℝ}
    (hS : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) (hτ : 0 < τ) (hωτ : ω * τ < 1)
    {R : E →L[𝕜] E} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    R = (τ : 𝕜)⁻¹ • resolvent G.generator (τ : 𝕜)⁻¹ := by
  have h := G.isResolvent_resolvent_ofReal hS (lt_inv_of_mul_lt hτ hωτ)
  rw [RCLike.ofReal_inv] at h
  exact h.eq_inv_smul_of_apply_sub hτ.ne' hR

/-- **Backward Euler is stable on Banach spaces**: `‖Rᵏ‖ ≤ M/(1 - ωτ)ᵏ` for
`R = (1 - τA)⁻¹`, from the Hille–Yosida estimates. [Pazy1983], §1.5 -/
theorem norm_pow_le_of_generator {M ω τ : ℝ}
    (hS : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) (hτ : 0 < τ) (hωτ : ω * τ < 1)
    {R : E →L[𝕜] E} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (k : ℕ) :
    ‖R ^ k‖ ≤ M / (1 - ω * τ) ^ k := by
  have h := G.norm_resolvent_ofReal_pow_le hS (lt_inv_of_mul_lt hτ hωτ) k
  rw [RCLike.ofReal_inv] at h
  rw [eq_inv_smul_resolvent_of_generator G hS hτ hωτ hR, smul_pow, norm_smul, norm_pow, norm_inv,
    RCLike.norm_ofReal, abs_of_pos hτ]
  calc τ⁻¹ ^ k * ‖resolvent G.generator (τ : 𝕜)⁻¹ ^ k‖ ≤ τ⁻¹ ^ k * (M / (τ⁻¹ - ω) ^ k) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = M / (1 - ω * τ) ^ k := by
        rw [show 1 - ω * τ = τ * (τ⁻¹ - ω) by field_simp, mul_pow, inv_pow]
        field_simp

/-- `(1 - τA)⁻¹` is injective. -/
theorem injective_of_generator {M ω τ : ℝ}
    (hS : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) (hτ : 0 < τ) (hωτ : ω * τ < 1)
    {R : E →L[𝕜] E} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    Function.Injective R := by
  rw [eq_inv_smul_resolvent_of_generator G hS hτ hωτ hR]
  have h := G.isResolvent_resolvent_ofReal hS (lt_inv_of_mul_lt hτ hωτ)
  rw [RCLike.ofReal_inv] at h
  have hτ' : ((τ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hτ.ne')
  exact fun a b hab => h.injective (smul_right_injective E hτ' hab)

/-- **`sᴺ d(1 - 1/s)` at `(1 - τA)⁻¹` is invertible on Banach spaces**: for `‖S(t)‖ ≤ M e^{ωt}`,
`τ > 0`, `ωτ < 1`, `R (x - τ A x) = x` on `D(A)`, and a real polynomial `d` of degree `N`
without roots in `re z ≤ ωτ`, `Q(R) = Rᴺ d(1 - R⁻¹)` is invertible with
`‖Q(R)⁻¹‖ ≤ |d_N|⁻¹ ∏_{d(ζ)=0} (1 + |1 - ζ| M/(re ζ - ωτ))` (roots with multiplicity). Over
`ℂ`, `Q(R) = d_N ∏ ((1 - ζ) R - 1)` with `((1 - ζ) R - 1)⁻¹ = -1 - (1 - ζ)(ζ - τA)⁻¹`; over `ℝ`
on the complexification. [Pazy1983], §1.5 -/
theorem isUnit_resolventEval_of_generator {M ω τ : ℝ}
    (hS : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) (hτ : 0 < τ) (hωτ : ω * τ < 1)
    {d : ℝ[X]} (hd : ∀ z : ℂ, z.re ≤ ω * τ → aeval z d ≠ 0) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    IsUnit (resolventEval d.natDegree (d.map (algebraMap ℝ 𝕜)) R) ∧
      ‖Ring.inverse (resolventEval d.natDegree (d.map (algebraMap ℝ 𝕜)) R)‖ ≤
        |d.leadingCoeff|⁻¹ * ((d.map (algebraMap ℝ ℂ)).roots.map
          fun ζ => 1 + ‖1 - ζ‖ * (M / (ζ.re - ω * τ))).prod := by
  set H := G.complexification
  have hSH : ∀ t, 0 ≤ t → ‖H.S t‖ ≤ M * Real.exp (ω * t) := fun t ht =>
    (G.norm_complexification_S t).trans_le (hS t ht)
  obtain ⟨hu, hb⟩ := isUnit_resolventEval_complex H hSH hτ hωτ hd
  have hmapR : map (n := .taylor) R = (τ : ℂ)⁻¹ • resolvent H.generator (τ : ℂ)⁻¹ :=
    eq_inv_smul_resolvent_of_generator H hSH hτ hωτ fun p q h => G.map_apply_sub_smul hR h
  have hQ : map (n := .taylor) (resolventEval d.natDegree (d.map (algebraMap ℝ 𝕜)) R) =
      resolventEval d.natDegree (d.map (algebraMap ℝ ℂ))
        ((τ : ℂ)⁻¹ • resolvent H.generator (τ : ℂ)⁻¹) := by
    rw [map_resolventEval_map, hmapR]
  have hu' := isUnit_of_isUnit_map (hQ ▸ hu)
  refine ⟨hu', ?_⟩
  rw [← Complexification.norm_map (n := .taylor), Complexification.map_ringInverse hu', hQ]
  exact hb

namespace RationalScheme

variable (r : RationalScheme)

/-- **`r(τA)` on Banach spaces is well defined**: `Q(R)` is invertible for every rational scheme
`r` without poles in `re z ≤ ωτ` (all its poles are in `re z > 0`), `‖S(t)‖ ≤ M e^{ωt}`,
`τ > 0`, `ωτ < 1`. -/
theorem isUnit_resolventEval_den_of_generator {M ω τ : ℝ}
    (hS : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) (hτ : 0 < τ) (hωτ : ω * τ < 1)
    (hden : ∀ z : ℂ, z.re ≤ ω * τ → aeval z r.den ≠ 0) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R) :=
  (isUnit_resolventEval_of_generator G hS hτ hωτ hden hR).1

/-- **`‖r(τA)‖` on Banach spaces**: for a rational scheme `r = n/d` without poles in
`re z ≤ ωτ`, `‖S(t)‖ ≤ M e^{ωt}`, `τ > 0`, `ωτ < 1`,
`‖r(τA)‖ ≤ (∑ₖ |nₖ|) (1 + M/(1 - ωτ))ᴺ |d_N|⁻¹ ∏_{d(ζ)=0} (1 + |1 - ζ| M/(re ζ - ωτ))`.
For the remainder `ρ` of `r` this is the remainder bound of Brenner–Thomée. -/
theorem norm_resolventStep_le_of_generator {M ω τ : ℝ}
    (hS : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) (hτ : 0 < τ) (hωτ : ω * τ < 1)
    (hden : ∀ z : ℂ, z.re ≤ ω * τ → aeval z r.den ≠ 0) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    ‖r.resolventStep R‖ ≤ (∑ k ∈ range (r.den.natDegree + 1), |r.num.coeff k|) *
      (M / (1 - ω * τ) + 1) ^ r.den.natDegree * (|r.den.leadingCoeff|⁻¹ *
        ((r.den.map (algebraMap ℝ ℂ)).roots.map fun ζ => 1 + ‖1 - ζ‖ * (M / (ζ.re - ω * τ))).prod) := by
  have hQ := (isUnit_resolventEval_of_generator G hS hτ hωτ hden hR).2
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hS 0 le_rfl)
  have hτω' : 0 < 1 - ω * τ := by linarith
  have hR1 : ‖R‖ ≤ M / (1 - ω * τ) := by
    simpa using norm_pow_le_of_generator G hS hτ hωτ hR 1
  have hP := norm_resolventEval_le r.den.natDegree (r.num.map (algebraMap ℝ 𝕜)) R
  simp only [coeff_map, RCLike.algebraMap_eq_ofReal, RCLike.norm_ofReal] at hP
  have hs : 0 ≤ ∑ k ∈ range (r.den.natDegree + 1), |r.num.coeff k| :=
    sum_nonneg fun _ _ => abs_nonneg _
  have hMτ : 0 ≤ M / (1 - ω * τ) := div_nonneg hM hτω'.le
  refine (norm_mul_le _ _).trans (mul_le_mul (hP.trans ?_) hQ (norm_nonneg _) (by positivity))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) hs

/-- **The remainder bound of Brenner–Thomée from the Hille–Yosida estimates**: for a rational
scheme `r` and `p`, there are `c > 0`, depending only on `r` and `p` (in the proof, on `r`
only), and for every `M` a `K₀`, depending only on `r`, `p` and `M`, such that for every strongly continuous semigroup with
`‖S(t)‖ ≤ M e^{ωt}` on a Banach space, every `τ > 0` with `ωτ ≤ c` and `R = (1 - τA)⁻¹`:
`Q(R)` is invertible and `‖ρ(τA)‖ ≤ K₀`. [BrennerThomee1979]; [Thomee2006], Ch. 9 -/
theorem exists_norm_remainder_resolventStep_le (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℝ, ∃ K₀ : ℝ, ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
      [NormedSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
      (G : Feec.C0Semigroup 𝕜 E) {ω τ : ℝ}, (∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) →
      0 < τ → ω * τ ≤ c → ∀ {R : E →L[𝕜] E},
      (∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) →
      IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R) ∧
        ‖(r.remainder p).resolventStep R‖ ≤ K₀ := by
  obtain ⟨c₀, hc₀, hc₀2, hden⟩ := r.exists_den_ne_zero
  refine ⟨c₀ / 2, by positivity, fun M => ⟨(∑ k ∈ range (r.den.natDegree + 1),
    |(r.remainder p).num.coeff k|) * (2 * M + 1) ^ r.den.natDegree * (|r.den.leadingCoeff|⁻¹ *
      ((r.den.map (algebraMap ℝ ℂ)).roots.map
        fun ζ => 1 + ‖1 - ζ‖ * (2 * M / c₀)).prod),
    fun G ω τ hS hτ hωτ R hR => ?_⟩⟩
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hS 0 le_rfl)
  have hωτ1 : ω * τ < 1 := by linarith
  have hden' : ∀ z : ℂ, z.re ≤ ω * τ → aeval z r.den ≠ 0 := fun z hz => hden z (by linarith)
  refine ⟨r.isUnit_resolventEval_den_of_generator G hS hτ hωτ1 hden' hR,
    ((r.remainder p).norm_resolventStep_le_of_generator G hS hτ hωτ1 hden' hR).trans ?_⟩
  have hroots : ∀ ζ ∈ (r.den.map (algebraMap ℝ ℂ)).roots, c₀ < ζ.re := fun ζ hζ => by
    by_contra h
    have hq0 : r.den.map (algebraMap ℝ ℂ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).2 r.den_ne_zero
    rw [mem_roots hq0, IsRoot, eval_map_algebraMap] at hζ
    exact hden ζ (not_lt.1 h) hζ
  have h1 : M / (1 - ω * τ) ≤ 2 * M := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hM (by linarith : (0 : ℝ) ≤ 1 - 2 * (ω * τ))]
  have hMτ : 0 ≤ M / (1 - ω * τ) := div_nonneg hM (by linarith)
  have hs : 0 ≤ ∑ k ∈ range (r.den.natDegree + 1), |(r.remainder p).num.coeff k| :=
    sum_nonneg fun _ _ => abs_nonneg _
  have hprod : 0 ≤ ((r.den.map (algebraMap ℝ ℂ)).roots.map
      fun ζ => 1 + ‖1 - ζ‖ * (M / (ζ.re - ω * τ))).prod :=
    Multiset.prod_nonneg fun x hx => by
      obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.1 hx
      have := hroots ζ hζ
      have : 0 ≤ M / (ζ.re - ω * τ) := div_nonneg hM (by linarith)
      positivity
  refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _)
    hs) (mul_le_mul_of_nonneg_left
      (Multiset.prod_map_le_prod_map₀ _ _ (fun ζ hζ => ?_) fun ζ hζ => ?_)
      (inv_nonneg.2 (abs_nonneg _))) (mul_nonneg (inv_nonneg.2 (abs_nonneg _)) hprod)
    (mul_nonneg hs (pow_nonneg (by linarith) _))
  · have := hroots ζ hζ
    have : 0 ≤ M / (ζ.re - ω * τ) := div_nonneg hM (by linarith)
    positivity
  · have hζ' := hroots ζ hζ
    have : M / (ζ.re - ω * τ) ≤ 2 * M / c₀ := by
      rw [div_le_div_iff₀ (by linarith) hc₀]
      nlinarith [mul_nonneg hM (sub_nonneg.2 hωτ), mul_nonneg hM (sub_pos.2 hζ').le]
    exact add_le_add_right (mul_le_mul_of_nonneg_left this (norm_nonneg _)) 1

/-- **Brenner–Thomée on Banach spaces with only the stability assumed**: for a rational scheme `r`
of order `p` there are `c > 0`, depending only on `r` and `p`, and for every `M` a `K₀`, depending
only on `r`, `p` and `M`, such that for every strongly continuous semigroup with `‖S(t)‖ ≤ M e^{ωt}`,
`ω ≥ 0`, on a Banach space, every `τ > 0` with `ωτ ≤ c` and `R = (1 - τA)⁻¹`: `Q(R)` is
invertible, `‖ρ(τA)‖ ≤ K₀` (`exists_norm_remainder_resolventStep_le`), and for `n` with
`‖r(τA)ᵏ‖ ≤ Mₛ` (`k ≤ n`) and `x ∈ D(A^{p+1})`,
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ Mₛ (K₀ + M e^{ωnτ}/(p+1)!) M e^{ωnτ} nτ τᵖ ‖A^{p+1} x‖`. The stability
does not follow from the Hille–Yosida estimates in general ([BrennerThomee1979]).
[Thomee2006], Ch. 9 -/
theorem exists_norm_resolventStep_pow_sub_S_le {p : ℕ} (hp : r.HasOrder p) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℝ, ∃ K₀ : ℝ, ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
      [NormedSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
      (G : Feec.C0Semigroup 𝕜 E) {ω τ : ℝ}, 0 ≤ ω →
      (∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) → 0 < τ → ω * τ ≤ c → ∀ {R : E →L[𝕜] E},
      (∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) →
      IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R) ∧
        ‖(r.remainder p).resolventStep R‖ ≤ K₀ ∧ ∀ {n : ℕ} {Ms : ℝ},
        (∀ k ≤ n, ‖r.resolventStep R ^ k‖ ≤ Ms) → ∀ {u : ℕ → E},
        (∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
        ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
          Ms * (K₀ + M * Real.exp (ω * (n * τ)) / (p + 1).factorial) *
            (M * Real.exp (ω * (n * τ))) * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  obtain ⟨c, hc, hK⟩ := r.exists_norm_remainder_resolventStep_le p
  refine ⟨min c (1 / 2), lt_min hc (by norm_num), fun M => ?_⟩
  obtain ⟨K₀, hK₀⟩ := hK M
  refine ⟨K₀, ?_⟩
  intro 𝕜 E _ _ _ _ _ _ G ω τ hω hS hτ hωτ R hR
  obtain ⟨hQ, hρ⟩ := hK₀ G hS hτ (hωτ.trans (min_le_left _ _)) hR
  refine ⟨hQ, hρ, fun {n Ms} hst {u} hu => ?_⟩
  have hωτ1 : ω * τ < 1 := by linarith [min_le_right c (1 / 2)]
  have hinj := injective_of_generator G hS hτ hωτ1 hR
  have hS' : ∀ t ∈ Icc 0 (n * τ), ‖G.S t‖ ≤ M * Real.exp (ω * (n * τ)) := fun t ht => by
    have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hS 0 le_rfl)
    exact (hS t ht.1).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hω)) hM)
  exact r.norm_resolventStep_pow_sub_S_le G hp hτ.le hR hinj hQ hst hS' hρ hu

/-! ### Backward Euler -/

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem resolventEval_one_eq (f : 𝕜[X]) (S : E →L[𝕜] E) :
    resolventEval 1 f S = f.coeff 0 • S + f.coeff 1 • (S - 1) := by
  simp [resolventEval, sum_range_succ]

theorem natDegree_den_theta {θ : ℝ} (hθ : 0 < θ) : (theta θ hθ).den.natDegree = 1 := by
  have hd : (1 - C θ * X : ℝ[X]) = C (-θ) * X + C 1 := by rw [C_neg, C_1]; ring
  change (1 - C θ * X : ℝ[X]).natDegree = 1
  rw [hd]; exact natDegree_linear (neg_ne_zero.2 hθ.ne')

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- At backward Euler `r = 1/(1 - z)`, `Q(R) = 1`. -/
theorem resolventEval_den_theta_one (R : E →L[𝕜] E) :
    resolventEval (theta 1 one_pos).den.natDegree ((theta 1 one_pos).den.map (algebraMap ℝ 𝕜)) R =
      1 := by
  rw [natDegree_den_theta, resolventEval_one_eq]
  simp [theta, coeff_one, coeff_X]

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **Backward Euler is the resolvent**: for `r = 1/(1 - z)`, `r(τA) = R = (1 - τA)⁻¹`. -/
theorem resolventStep_theta_one (R : E →L[𝕜] E) : (theta 1 one_pos).resolventStep R = R := by
  rw [resolventStep, resolventEval_den_theta_one, Ring.inverse_one, mul_one, natDegree_den_theta,
    resolventEval_one_eq]
  simp [theta, coeff_one]

/-- The remainder of backward Euler at order `1` is `ρ = 1/(1 - z)`. -/
theorem remainder_theta_one_num : ((theta 1 one_pos).remainder 1).num = 1 := by
  have h : (theta 1 one_pos).num - (theta 1 one_pos).den * expTaylor 1 = X ^ (1 + 1) * 1 := by
    simp [theta, expTaylor, sum_range_succ]; ring
  simp only [remainder, h, mul_divByMonic_cancel_left _ (monic_X_pow _)]

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **The remainder of backward Euler is the resolvent**: `ρ(τA) = R`. -/
theorem resolventStep_remainder_theta_one (R : E →L[𝕜] E) :
    ((theta 1 one_pos).remainder 1).resolventStep R = R := by
  rw [resolventStep, remainder_theta_one_num]
  change resolventEval (theta 1 one_pos).den.natDegree _ R *
    Ring.inverse (resolventEval (theta 1 one_pos).den.natDegree
      ((theta 1 one_pos).den.map (algebraMap ℝ 𝕜)) R) = R
  rw [resolventEval_den_theta_one, Ring.inverse_one, mul_one, Polynomial.map_one,
    resolventEval_one, natDegree_den_theta, pow_one]

/-- **Backward Euler on Banach spaces**: for a strongly continuous semigroup with
`‖S(t)‖ ≤ M e^{ωt}`, `ω ≥ 0`, `τ > 0` with `ωτ < 1`, `R = (1 - τA)⁻¹` and `x ∈ D(A²)`,
`‖Rⁿ x - S(nτ) x‖ ≤ (M/(1 - ωτ)ⁿ) (M/(1 - ωτ) + M e^{ωnτ}/2) M e^{ωnτ} nτ τ ‖A² x‖`, with no
further hypothesis: the stability `‖Rᵏ‖ ≤ M/(1 - ωτ)ᵏ` and the remainder `ρ(τA) = R` come from the
Hille–Yosida estimates. For bounded semigroups (`ω = 0`): `‖Rⁿ x - S(nτ) x‖ ≤ (3/2) M³ nτ² ‖A² x‖`.
[BrennerThomee1979]; [Pazy1983], §1.5 -/
theorem norm_backwardEuler_pow_sub_S_le {M ω τ : ℝ} (hω : 0 ≤ ω)
    (hS : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M * Real.exp (ω * t)) (hτ : 0 < τ) (hωτ : ω * τ < 1)
    {R : E →L[𝕜] E} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ)
    {u : ℕ → E} (hu : ∀ j < 2, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤ M / (1 - ω * τ) ^ n *
      (M / (1 - ω * τ) + M * Real.exp (ω * (n * τ)) / 2) * (M * Real.exp (ω * (n * τ))) *
        (n * τ) * τ * ‖u 2‖ := by
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hS 0 le_rfl)
  have h1 : 0 < 1 - ω * τ := by linarith
  have h1' : 1 - ω * τ ≤ 1 := by nlinarith
  have hst : ∀ k ≤ n, ‖(theta 1 one_pos).resolventStep R ^ k‖ ≤ M / (1 - ω * τ) ^ n :=
    fun k hk => by
      rw [resolventStep_theta_one]
      exact (norm_pow_le_of_generator G hS hτ hωτ hR k).trans
        (div_le_div_of_nonneg_left hM (pow_pos h1 _) (pow_le_pow_of_le_one h1.le h1' hk))
  have hS' : ∀ t ∈ Icc 0 (n * τ), ‖G.S t‖ ≤ M * Real.exp (ω * (n * τ)) := fun t ht =>
    (hS t ht.1).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hω)) hM)
  have hρ : ‖((theta 1 one_pos).remainder 1).resolventStep R‖ ≤ M / (1 - ω * τ) := by
    rw [resolventStep_remainder_theta_one]
    simpa using norm_pow_le_of_generator G hS hτ hωτ hR 1
  have hQ : IsUnit (resolventEval (theta 1 one_pos).den.natDegree
      ((theta 1 one_pos).den.map (algebraMap ℝ 𝕜)) R) := by
    rw [resolventEval_den_theta_one]; exact isUnit_one
  have h := (theta 1 one_pos).norm_resolventStep_pow_sub_S_le G (hasOrder_theta one_pos) hτ.le hR
    (injective_of_generator G hS hτ hωτ hR) hQ hst hS' hρ hu
  rw [resolventStep_theta_one] at h
  refine h.trans_eq ?_
  norm_num [Nat.factorial]

end RationalScheme

end Banach

end Feec.TimeStepping
