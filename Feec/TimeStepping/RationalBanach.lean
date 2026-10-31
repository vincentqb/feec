module

public import Feec.TimeStepping.Rational
public import Feec.Semigroup.Orbit

/-!
# Rational approximations of semigroups on Banach spaces

Let `G` be a strongly continuous semigroup on a Banach space `E` over `𝕜 = ℝ` or `ℂ`, with
generator `A`, and `r` a rational scheme of order `p`. With the resolvent `R = (1 - τA)⁻¹`, the
operator `r(τA)` is `P(R) Q(R)⁻¹` (`RationalScheme.resolventStep`; `P(s) = sᴺ n(1 - 1/s)`,
`Q(s) = sᴺ d(1 - 1/s)`, `Feec.TimeStepping.resolventEval`), the form that
`Feec.TimeStepping.RationalScheme.step` takes on Hilbert spaces
(`RationalScheme.step_eq_resolventStep`). On a Banach space the stability of `r(τA)` is not
automatic (von Neumann's inequality fails off Hilbert spaces) and is a hypothesis, as in
[BrennerThomee1979]. So are the invertibility of `Q(R)` and the boundedness of the remainder
`ρ(τA)`, `ρ = (r - Tₚ)/z^{p+1}`, although for A-stable `r` both follow from resolvent estimates
alone: `Q(R)` is a product of factors `R (τA - ζ)` over the poles `ζ` of `r`, and the partial
fractions of `ρ` bound `‖ρ(τA)‖` by the Hille–Yosida bounds
`‖(λ - A)^{-m}‖ ≤ M/(re λ - ω)^m` at `λ = ζ/τ`. These estimates are not formalized here. Under
the three hypotheses, **Brenner–Thomée's error bound** holds:

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ Mₛ (K₀ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖`

for `x ∈ D(A^{p+1})`, with `‖r(τA)ᵏ‖ ≤ Mₛ` (`k ≤ n`), `‖ρ(τA)‖ ≤ K₀` and `‖S(t)‖ ≤ M` on
`[0, nτ]`.

## Main results

* `resolventEval_mul`, `resolventEval_add`: `P ↦ P(s) = sᴺ f(1 - 1/s)` is additive and
  multiplicative (degrees add), proved by evaluation at the points `s ≠ 0`;
* `RationalScheme.resolventStep_apply_eq`: **the expansion `r(τA) x = Tₚ(τA) x + (τA)^{p+1} ρ(τA) x`
  on `D(A^{p+1})`**, from `n = d Tₚ + X^{p+1} ρ`, with `(R - 1) x = τ R A x` on `D(A)`;
* `RationalScheme.norm_resolventStep_sub_S_le`: consistency,
  `‖r(τA) x - S(τ) x‖ ≤ (K₀ + M/(p+1)!) τ^{p+1} ‖A^{p+1} x‖`;
* **`RationalScheme.norm_resolventStep_pow_sub_S_le`**: Brenner–Thomée on Banach spaces, from
  Taylor's formula and Lax–Richtmyer for semigroups (`C0Semigroup.norm_S_sub_taylor_le`,
  `C0Semigroup.norm_pow_apply_sub_S_le`, `Feec.TimeStepping.Convergence`);
* `RationalScheme.norm_step_pow_sub_S_le`: the same on Hilbert spaces for
  `Feec.TimeStepping.RationalScheme.step`, given a resolvent of `A` at `1/τ`.

On Hilbert spaces von Neumann's inequality discharges the three hypotheses: for contraction
semigroups directly (`Feec.TimeStepping.RationalScheme.norm_step_pow_sub_semigroup_le`), for
quasi-contractive ones after a shift (`Feec.TimeStepping.RationalQuasi`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 9
* [R. Hersh, T. Kato, *High-Accuracy Stable Difference Schemes for Well-Posed Initial-Value Problems*][HershKato1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Finset Polynomial

@[expose] public noncomputable section

namespace Feec

namespace TimeStepping

/-! ### `sᴺ f(1 - 1/s)`: additivity and multiplicativity -/

section ResolventEval

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem resolventEval_add (N : ℕ) (f g : 𝕜[X]) (S : A) :
    resolventEval N (f + g) S = resolventEval N f S + resolventEval N g S := by
  simp only [resolventEval, coeff_add, add_smul, sum_add_distrib]

/-- `sᴺ f(1 - 1/s)` commutes with algebra maps. -/
theorem map_resolventEval {B : Type*} [Ring B] [Algebra 𝕜 B] (φ : A →ₐ[𝕜] B) (N : ℕ) (f : 𝕜[X])
    (S : A) : φ (resolventEval N f S) = resolventEval N f (φ S) := by
  simp [resolventEval, map_sum, map_smul, map_mul, map_pow, map_sub, map_one]

/-- At `s ≠ 0` in the field, `sᴺ f(1 - 1/s)` is what it says. -/
theorem eval_resolventEval_X {N : ℕ} {f : 𝕜[X]} (hf : f.natDegree ≤ N) {x : 𝕜} (hx : x ≠ 0) :
    (resolventEval N f (X : 𝕜[X])).eval x = x ^ N * f.eval (1 - x⁻¹) := by
  have h := map_resolventEval (Polynomial.aeval x) N f X
  rw [aeval_X, resolventEval_eq_mul_aeval (L := 1 - x⁻¹) (by field_simp; ring)
    (Commute.all _ _) hf, coe_aeval_eq_eval] at h
  rw [h, coe_aeval_eq_eval]

theorem resolventEval_one (M : ℕ) (S : A) : resolventEval M (1 : 𝕜[X]) S = S ^ M := by
  rw [resolventEval, sum_range_succ', sum_eq_zero fun k _ => by simp [coeff_one]]
  simp

theorem resolventEval_X_pow (M : ℕ) (S : A) :
    resolventEval M ((X : 𝕜[X]) ^ M) S = (S - 1) ^ M := by
  rw [resolventEval, sum_range_succ, sum_eq_zero fun k hk => by
    simp [coeff_X_pow, show k ≠ M by have := mem_range.1 hk; omega]]
  simp

theorem commute_resolventEval (N M : ℕ) (f g : 𝕜[X]) (S : A) :
    Commute (resolventEval N f S) (resolventEval M g S) := by
  have h1 := map_resolventEval (Polynomial.aeval S) N f X
  have h2 := map_resolventEval (Polynomial.aeval S) M g X
  rw [aeval_X] at h1 h2
  rw [← h1, ← h2]
  exact (Commute.all _ _).map _

variable [Infinite 𝕜]

/-- **`sᴺ f(1 - 1/s)` is multiplicative**: for `deg f ≤ N`, `deg g ≤ M`,
`P_{fg}^{N+M} = P_f^N P_g^M` (an identity of polynomials in `s`, checked at the infinitely many
`s ≠ 0`). -/
theorem resolventEval_mul {N M : ℕ} {f g : 𝕜[X]} (hf : f.natDegree ≤ N) (hg : g.natDegree ≤ M)
    (S : A) :
    resolventEval (N + M) (f * g) S = resolventEval N f S * resolventEval M g S := by
  have key : resolventEval (N + M) (f * g) (X : 𝕜[X]) =
      resolventEval N f X * resolventEval M g X := by
    refine eq_of_infinite_eval_eq _ _ (((Set.infinite_univ (α := 𝕜)).sdiff (Set.finite_singleton 0)).mono
      fun x hx => ?_)
    have hx : x ≠ 0 := hx.2
    simp only [Set.mem_ofPred_eq, eval_mul, eval_resolventEval_X (natDegree_mul_le.trans
      (Nat.add_le_add hf hg)) hx, eval_resolventEval_X hf hx, eval_resolventEval_X hg hx]
    ring
  have := congrArg (Polynomial.aeval S) key
  rwa [map_mul, map_resolventEval, map_resolventEval, map_resolventEval, aeval_X] at this

/-- Raising the degree: `P_f^{N+M} = Sᴹ P_f^N` for `deg f ≤ N`. -/
theorem resolventEval_add_right {N : ℕ} {f : 𝕜[X]} (hf : f.natDegree ≤ N) (M : ℕ) (S : A) :
    resolventEval (N + M) f S = resolventEval N f S * S ^ M := by
  rw [← resolventEval_one (𝕜 := 𝕜) M S, ← resolventEval_mul hf (natDegree_one.le.trans (Nat.zero_le M)),
    mul_one]

end ResolventEval

/-! ### `r(τA)` through the resolvent, on Banach spaces -/

namespace RationalScheme

variable (r : RationalScheme) {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **`r(τA) = P(R) Q(R)⁻¹`** at `R = (1 - τA)⁻¹`, `P(s) = sᴺ n(1 - 1/s)`,
`Q(s) = sᴺ d(1 - 1/s)`, `N = deg d` (`resolventEval`). -/
def resolventStep (R : E →L[𝕜] E) : E →L[𝕜] E :=
  resolventEval r.den.natDegree (r.num.map (algebraMap ℝ 𝕜)) R *
    Ring.inverse (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R)

/-- On Hilbert spaces `RationalScheme.step` is the resolvent form, for every `A`. -/
theorem step_eq_resolventStep {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (A : V →ₗ.[𝕜] V) (τ : ℝ) :
    r.step A τ = r.resolventStep ((τ : 𝕜)⁻¹ • Operator.resolvent A (τ : 𝕜)⁻¹) :=
  r.step_eq_resolventEval A τ

theorem coeff_map_expTaylor (p k : ℕ) :
    ((expTaylor p).map (algebraMap ℝ 𝕜)).coeff k = if k ≤ p then (1 / k.factorial : 𝕜) else 0 := by
  rw [coeff_map, expTaylor, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_range, Nat.lt_succ_iff]
  split_ifs <;> simp

/-- **The polynomial identity behind the expansion**: for `r` of order `p`,
`R^{p+1} P(R) = Q(R) P_{Tₚ}^{p+1}(R) + (R - 1)^{p+1} P_ρ(R)` (`n = d Tₚ + X^{p+1} ρ`, degrees
`N = deg d`, `p + 1`). -/
theorem resolventEval_num_mul_pow {p : ℕ} (hp : r.HasOrder p) (R : E →L[𝕜] E) :
    resolventEval r.den.natDegree (r.num.map (algebraMap ℝ 𝕜)) R * R ^ (p + 1) =
      resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R *
          resolventEval (p + 1) ((expTaylor p).map (algebraMap ℝ 𝕜)) R +
        resolventEval (p + 1) ((X : 𝕜[X]) ^ (p + 1)) R *
          resolventEval r.den.natDegree ((r.remainder p).num.map (algebraMap ℝ 𝕜)) R := by
  set N := r.den.natDegree
  have hn : r.num.map (algebraMap ℝ 𝕜) = r.den.map (algebraMap ℝ 𝕜) *
      (expTaylor p).map (algebraMap ℝ 𝕜) + X ^ (p + 1) * (r.remainder p).num.map (algebraMap ℝ 𝕜) := by
    conv_lhs => rw [r.num_eq_add hp]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X]
  have hT : ((expTaylor p).map (algebraMap ℝ 𝕜)).natDegree ≤ p + 1 :=
    natDegree_map_le.trans ((natDegree_expTaylor_le p).trans (Nat.le_succ p))
  have hρ : ((r.remainder p).num.map (algebraMap ℝ 𝕜)).natDegree ≤ N :=
    natDegree_map_le.trans (r.remainder p).natDegree_num_le
  rw [← resolventEval_add_right (natDegree_map_le.trans r.natDegree_num_le), hn,
    resolventEval_add, resolventEval_mul (natDegree_map_le.trans le_rfl) hT, add_comm N,
    resolventEval_mul (natDegree_X_pow_le (p + 1)) hρ]

variable {A : E →ₗ.[𝕜] E} {τ : ℝ} {R : E →L[𝕜] E}

/-- `(R - 1)ʲ u₀ = τʲ Rʲ uⱼ` along a chain `u` in the graph of `A`, when `R (x - τ A x) = x`
on `D(A)`. -/
theorem sub_one_pow_apply (hR : ∀ x y, (x, y) ∈ A.graph → R (x - (τ : 𝕜) • y) = x) {k : ℕ} {u : ℕ → E}
    (hu : ∀ j < k, (u j, u (j + 1)) ∈ A.graph) :
    ∀ j ≤ k, ((R - 1) ^ j) (u 0) = (τ : 𝕜) ^ j • (R ^ j) (u j) := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (R - 1) (u j) = (τ : 𝕜) • R (u (j + 1)) := by
      have := hR _ _ (hu j (by omega))
      rw [sub_apply, one_apply_eq_self]
      nth_rw 2 [← this]
      rw [map_sub, map_smul]; abel
    have hc : Commute (R - 1) (R ^ j) := ((Commute.refl R).sub_left (Commute.one_left R)).pow_right j
    calc ((R - 1) ^ (j + 1)) (u 0) = (R - 1) (((R - 1) ^ j) (u 0)) := by
          rw [pow_succ']; rfl
      _ = (τ : 𝕜) ^ j • ((R - 1) * R ^ j) (u j) := by rw [ih (by omega), map_smul]; rfl
      _ = (τ : 𝕜) ^ j • (R ^ j) ((R - 1) (u j)) := by rw [hc.eq]; rfl
      _ = (τ : 𝕜) ^ (j + 1) • (R ^ (j + 1)) (u (j + 1)) := by
          rw [h1, map_smul, smul_smul, ← pow_succ, pow_succ]; rfl

/-- **The expansion `r(τA) u₀ = Tₚ(τA) u₀ + (τA)^{p+1} ρ(τA) u₀` on `D(A^{p+1})`**: for `r` of
order `p`, `R` injective with `R (x - τ A x) = x` on `D(A)` and `Q(R)` invertible,
`r(τA) u₀ = Σ_{j≤p} τʲ/j! uⱼ + τ^{p+1} ρ(τA) u_{p+1}` for every chain `u` in the graph of `A`. -/
theorem resolventStep_apply_eq {p : ℕ} (hp : r.HasOrder p)
    (hR : ∀ x y, (x, y) ∈ A.graph → R (x - (τ : 𝕜) • y) = x) (hinj : Function.Injective R)
    (hQ : IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R)) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ A.graph) :
    r.resolventStep R (u 0) = ∑ j ∈ range (p + 1), ((τ : 𝕜) ^ j / j.factorial) • u j +
      (τ : 𝕜) ^ (p + 1) • (r.remainder p).resolventStep R (u (p + 1)) := by
  set N := r.den.natDegree
  set P := resolventEval N (r.num.map (algebraMap ℝ 𝕜)) R
  set Q := resolventEval N (r.den.map (algebraMap ℝ 𝕜)) R
  set Pρ := resolventEval N ((r.remainder p).num.map (algebraMap ℝ 𝕜)) R
  set T := resolventEval (p + 1) ((expTaylor p).map (algebraMap ℝ 𝕜)) R
  set v := ∑ j ∈ range (p + 1), ((τ : 𝕜) ^ j / j.factorial) • u j
  have hRp : ∀ f : 𝕜[X], Commute (R ^ (p + 1)) (resolventEval N f R) := fun f => by
    rw [← resolventEval_one (𝕜 := 𝕜) (p + 1) R]; exact commute_resolventEval _ _ _ _ _
  have hsub := sub_one_pow_apply hR hu
  -- `R^{p+1} v = P_{Tₚ}(R) u₀`
  have hT : (R ^ (p + 1)) v = T (u 0) := by
    have hc : ∀ k m : ℕ, Commute ((R - 1) ^ k) (R ^ m) := fun k m =>
      ((Commute.refl R).sub_left (Commute.one_left R)).pow_pow k m
    simp only [v, T, resolventEval, map_sum, _root_.sum_apply]
    have c1 : ((expTaylor p).map (algebraMap ℝ 𝕜)).coeff (p + 1) = 0 := by
      rw [coeff_map_expTaylor]; simp
    have c2 : ∀ k ≤ p, ((expTaylor p).map (algebraMap ℝ 𝕜)).coeff k = 1 / k.factorial :=
      fun k hk => by rw [coeff_map_expTaylor]; simp [hk]
    conv_rhs => rw [sum_range_succ, c1, zero_smul, zero_apply, add_zero]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ p := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [c2 k hk', smul_apply, (hc k _).eq, mul_apply_eq_comp, hsub k (by omega)]
    simp only [map_smul]
    rw [← mul_apply_eq_comp (R ^ (p + 1 - k)), ← pow_add,
      Nat.sub_add_cancel (by omega), smul_smul, div_eq_inv_mul, one_div, mul_comm]
  -- `R^{p+1} (τ^{p+1} u_{p+1}) = (R - 1)^{p+1} u₀`
  have hX : (R ^ (p + 1)) ((τ : 𝕜) ^ (p + 1) • u (p + 1)) =
      resolventEval (p + 1) ((X : 𝕜[X]) ^ (p + 1)) R (u 0) := by
    rw [resolventEval_X_pow, hsub (p + 1) le_rfl, map_smul]
  have hinjQ : Function.Injective (R ^ (p + 1) * Q) := by
    have h1 : ∀ m : ℕ, Function.Injective ⇑(R ^ m) := fun m => by
      induction m with
      | zero => exact Function.injective_id
      | succ m ih =>
        intro a b hab
        rw [pow_succ, mul_apply_eq_comp, mul_apply_eq_comp] at hab
        exact hinj (ih hab)
    have h2 : Function.Injective Q := by
      obtain ⟨U, hU⟩ := hQ
      intro a b hab
      have := congrArg (↑U⁻¹ : E →L[𝕜] E) hab
      rwa [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← hU,
        Units.inv_mul, one_apply_eq_self, one_apply_eq_self] at this
    intro a b hab
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at hab
    exact h2 (h1 _ hab)
  apply hinjQ
  have hQP : Q * (P * Ring.inverse Q) = P := by
    rw [← mul_assoc, (commute_resolventEval N N _ _ R).eq, Ring.mul_inverse_cancel_right _ _ hQ]
  have hQρ : Q * (Pρ * Ring.inverse Q) = Pρ := by
    rw [← mul_assoc, (commute_resolventEval N N _ _ R).eq, Ring.mul_inverse_cancel_right _ _ hQ]
  have key := congrArg (fun L : E →L[𝕜] E => L (u 0)) (r.resolventEval_num_mul_pow hp R)
  simp only [mul_apply_eq_comp] at key
  calc (R ^ (p + 1) * Q) (r.resolventStep R (u 0))
      = (R ^ (p + 1) * (Q * (P * Ring.inverse Q))) (u 0) := rfl
    _ = (P * R ^ (p + 1)) (u 0) := by rw [hQP, (hRp _).eq]
    _ = Q (T (u 0)) + resolventEval (p + 1) ((X : 𝕜[X]) ^ (p + 1)) R (Pρ (u 0)) := key
    _ = Q ((R ^ (p + 1)) v) + Pρ ((R ^ (p + 1)) ((τ : 𝕜) ^ (p + 1) • u (p + 1))) := by
      rw [hT, hX]
      congr 1
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, (commute_resolventEval (p + 1) N _ _ R).eq]
    _ = (R ^ (p + 1) * Q) (v + (τ : 𝕜) ^ (p + 1) • (r.remainder p).resolventStep R (u (p + 1))) := by
      have h1 : (R ^ (p + 1) * Q) v = Q ((R ^ (p + 1)) v) := by
        rw [← mul_apply_eq_comp Q, ← (hRp _).eq]
      have h2 : (R ^ (p + 1) * Q) ((τ : 𝕜) ^ (p + 1) • (r.remainder p).resolventStep R (u (p + 1))) =
          Pρ ((R ^ (p + 1)) ((τ : 𝕜) ^ (p + 1) • u (p + 1))) := by
        rw [map_smul, map_smul, map_smul]
        congr 1
        change (R ^ (p + 1) * (Q * (Pρ * Ring.inverse Q))) (u (p + 1)) = _
        rw [hQρ, (hRp _).eq]; rfl
      rw [map_add, h1, h2]

/-! ### Brenner–Thomée on Banach spaces -/

section Semigroup

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E)

/-- **Consistency on a Banach space**: for `r` of order `p`, the resolvent `R = (1 - τA)⁻¹` of
the generator (`R (x - τ A x) = x` on `D(A)`, `R` injective), `Q(R)` invertible, `‖ρ(τA)‖ ≤ K₀`
and `‖S(t)‖ ≤ M` on `[0, τ]`: `‖r(τA) u₀ - S(τ) u₀‖ ≤ (K₀ + M/(p+1)!) τ^{p+1} ‖A^{p+1} u₀‖` on
`D(A^{p+1})`. [BrennerThomee1979] -/
theorem norm_resolventStep_sub_S_le {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 ≤ τ)
    {R : E →L[𝕜] E} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x)
    (hinj : Function.Injective R)
    (hQ : IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R)) {M K₀ : ℝ}
    (hS : ∀ t ∈ Icc 0 τ, ‖G.S t‖ ≤ M) (hρ : ‖(r.remainder p).resolventStep R‖ ≤ K₀)
    {u : ℕ → E} (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖r.resolventStep R (u 0) - G.S τ (u 0)‖ ≤
      (K₀ + M / (p + 1).factorial) * τ ^ (p + 1) * ‖u (p + 1)‖ := by
  have hT := G.norm_S_sub_taylor_le hS (p + 1) hu ⟨hτ, le_rfl⟩
  have hsum : ∑ j ∈ range (p + 1), ((τ : 𝕜) ^ j / j.factorial) • u j =
      ∑ j ∈ range (p + 1), (τ ^ j / j.factorial) • u j :=
    sum_congr rfl fun j _ => by rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]; push_cast; rfl
  rw [r.resolventStep_apply_eq hp hR hinj hQ hu, hsum]
  have hρu : ‖(τ : 𝕜) ^ (p + 1) • (r.remainder p).resolventStep R (u (p + 1))‖ ≤
      K₀ * τ ^ (p + 1) * ‖u (p + 1)‖ := by
    rw [norm_smul, norm_pow, RCLike.norm_ofReal, abs_of_nonneg hτ]
    have := ((r.remainder p).resolventStep R).le_opNorm (u (p + 1))
    have h2 : ‖(r.remainder p).resolventStep R (u (p + 1))‖ ≤ K₀ * ‖u (p + 1)‖ :=
      this.trans (mul_le_mul_of_nonneg_right hρ (norm_nonneg _))
    calc τ ^ (p + 1) * ‖(r.remainder p).resolventStep R (u (p + 1))‖
        ≤ τ ^ (p + 1) * (K₀ * ‖u (p + 1)‖) := by gcongr
      _ = _ := by ring
  calc ‖∑ j ∈ range (p + 1), (τ ^ j / j.factorial) • u j +
        (τ : 𝕜) ^ (p + 1) • (r.remainder p).resolventStep R (u (p + 1)) - G.S τ (u 0)‖
      = ‖(τ : 𝕜) ^ (p + 1) • (r.remainder p).resolventStep R (u (p + 1)) -
          (G.S τ (u 0) - ∑ j ∈ range (p + 1), (τ ^ j / j.factorial) • u j)‖ := by
        congr 1; abel
    _ ≤ K₀ * τ ^ (p + 1) * ‖u (p + 1)‖ + M * (τ ^ (p + 1) / (p + 1).factorial) * ‖u (p + 1)‖ :=
        (norm_sub_le _ _).trans (add_le_add hρu hT)
    _ = _ := by ring

/-- **Brenner–Thomée on Banach spaces**: let `G` be a strongly continuous semigroup with
generator `A` on a Banach space, `‖S(t)‖ ≤ M` on `[0, nτ]`, `r` a rational scheme of order `p`,
`R = (1 - τA)⁻¹` the resolvent (`R (x - τ A x) = x` on `D(A)`, `R` injective), `Q(R)` invertible,
`r(τA) = P(R) Q(R)⁻¹` **stable**, `‖r(τA)ᵏ‖ ≤ Mₛ` for `k ≤ n`, and the remainder bounded,
`‖ρ(τA)‖ ≤ K₀`. Then for `x ∈ D(A^{p+1})` (a chain `u` in the graph of `A`),
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ Mₛ (K₀ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖`. On Hilbert spaces von Neumann's
inequality gives `Mₛ = 1` and `K₀ = sup_y |ρ(iy)|` for contraction semigroups
(`Feec.TimeStepping.RationalScheme.norm_step_pow_sub_semigroup_le`), and exponential bounds for
quasi-contractive ones (`Feec.TimeStepping.RationalScheme.exists_norm_step_pow_sub_le`).
[BrennerThomee1979]; [Thomee2006], Ch. 9 -/
theorem norm_resolventStep_pow_sub_S_le {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 ≤ τ)
    {R : E →L[𝕜] E} (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x)
    (hinj : Function.Injective R)
    (hQ : IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R)) {n : ℕ}
    {Ms M K₀ : ℝ} (hst : ∀ k ≤ n, ‖r.resolventStep R ^ k‖ ≤ Ms)
    (hS : ∀ t ∈ Icc 0 (n * τ), ‖G.S t‖ ≤ M) (hρ : ‖(r.remainder p).resolventStep R‖ ≤ K₀)
    {u : ℕ → E} (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      Ms * (K₀ + M / (p + 1).factorial) * M * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hM : 0 ≤ M := (norm_nonneg _).trans (hS 0 ⟨le_rfl, by positivity⟩)
  have hK : 0 ≤ K₀ + M / (p + 1).factorial :=
    add_nonneg ((norm_nonneg _).trans hρ) (by positivity)
  have hS1 : ∀ t ∈ Icc 0 τ, ‖G.S t‖ ≤ M := fun t ht => hS t ⟨ht.1, ht.2.trans
    (le_mul_of_one_le_left hτ (by exact_mod_cast hn))⟩
  exact G.norm_pow_apply_sub_S_le hτ hK hst hS
    (fun v hv => r.norm_resolventStep_sub_S_le G hp hτ hR hinj hQ hS1 hρ hv) hu

/-- **Brenner–Thomée on Hilbert spaces, in the `step` form**: for `G` generated by `A`, `τ > 0`,
`R` a resolvent of `A` at `1/τ` (so `(1/τ) R = (1 - τA)⁻¹`), `Q((1/τ) R)` invertible,
`‖r(τA)ᵏ‖ ≤ Mₛ` for `k ≤ n`, `‖ρ(τA)‖ ≤ K₀` and `‖S(t)‖ ≤ M` on `[0, nτ]`:
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ Mₛ (K₀ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖` on `D(A^{p+1})`. -/
theorem norm_step_pow_sub_S_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] (G : C0Semigroup 𝕜 V) {A : V →ₗ.[𝕜] V}
    (hG : G.generator = A) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {R : V →L[𝕜] V}
    (hR : Operator.IsResolvent A (τ : 𝕜)⁻¹ R)
    (hQ : IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) ((τ : 𝕜)⁻¹ • R)))
    {n : ℕ} {Ms M K₀ : ℝ} (hst : ∀ k ≤ n, ‖r.step A τ ^ k‖ ≤ Ms)
    (hS : ∀ t ∈ Icc 0 (n * τ), ‖G.S t‖ ≤ M) (hρ : ‖(r.remainder p).step A τ‖ ≤ K₀)
    {u : ℕ → V} (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ A.graph) :
    ‖(r.step A τ ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      Ms * (K₀ + M / (p + 1).factorial) * M * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  subst hG
  have hτ0 : (τ : 𝕜) ≠ 0 := by exact_mod_cast hτ.ne'
  have hX : ∀ s : RationalScheme, s.step G.generator τ = s.resolventStep ((τ : 𝕜)⁻¹ • R) :=
    fun s => by rw [s.step_eq_resolventStep, hR.resolvent_eq]
  rw [hX] at hst hρ ⊢
  refine r.norm_resolventStep_pow_sub_S_le G hp hτ.le (fun x y hxy => ?_) (fun a b hab => ?_) hQ
    hst hS hρ hu
  · obtain ⟨hx, rfl⟩ := LinearPMap.mem_graph_iff_exists.1 hxy
    rw [_root_.smul_apply, ← _root_.map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hτ0, one_smul]
    exact hR.apply_sub ⟨x, hx⟩
  · exact hR.injective (smul_right_injective V (inv_ne_zero hτ0) hab)

end Semigroup

end RationalScheme

end TimeStepping

end Feec
