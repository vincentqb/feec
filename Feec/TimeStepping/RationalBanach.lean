module

public import Feec.TimeStepping.Rational
public import Feec.Semigroup.Orbit

/-!
# Rational approximations of semigroups on Banach spaces

On Banach spaces, the scheme `r(τA) = P(R) Q(R)⁻¹`, `R = (1 - τA)⁻¹`, satisfies Brenner–Thomée's
error bound when its powers and its remainder are bounded and `Q(R)` is invertible.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 9

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

theorem map_resolventEval {B : Type*} [Ring B] [Algebra 𝕜 B] (φ : A →ₐ[𝕜] B) (N : ℕ) (f : 𝕜[X])
    (S : A) : φ (resolventEval N f S) = resolventEval N f (φ S) := by
  simp [resolventEval, map_sum, map_smul, map_mul, map_pow, map_sub, map_one]

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

theorem resolventEval_add_right {N : ℕ} {f : 𝕜[X]} (hf : f.natDegree ≤ N) (M : ℕ) (S : A) :
    resolventEval (N + M) f S = resolventEval N f S * S ^ M := by
  rw [← resolventEval_one (𝕜 := 𝕜) M S, ← resolventEval_mul hf (natDegree_one.le.trans (Nat.zero_le M)),
    mul_one]

end ResolventEval

/-! ### `r(τA)` through the resolvent, on Banach spaces -/

namespace RationalScheme

variable (r : RationalScheme) {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `r(τA) = P(R) Q(R)⁻¹` at `R = (1 - τA)⁻¹`, `P(s) = sᴺ n(1 - 1/s)`, `Q(s) = sᴺ d(1 - 1/s)`. -/
def resolventStep (R : E →L[𝕜] E) : E →L[𝕜] E :=
  resolventEval r.den.natDegree (r.num.map (algebraMap ℝ 𝕜)) R *
    Ring.inverse (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R)

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
    have h2 : ‖(r.remainder p).resolventStep R (u (p + 1))‖ ≤ K₀ * ‖u (p + 1)‖ :=
      ((r.remainder p).resolventStep R).le_of_opNorm_le hρ _
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

/-- **Brenner–Thomée on Banach spaces** ([BrennerThomee1979]; [Thomee2006], Ch. 9): for `r` of
order `p`, `τ ≥ 0` and `Q(R)` invertible, if `‖r(τA)ᵏ‖ ≤ Mₛ` for `k ≤ n`, `‖ρ(τA)‖ ≤ K₀` and
`‖S(t)‖ ≤ M` on `[0, nτ]`, then `‖r(τA)ⁿ x - S(nτ) x‖ ≤ Mₛ (K₀ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖`. -/
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
  exact r.norm_resolventStep_pow_sub_S_le G hp hτ.le
    (fun x y hxy => hR.inv_smul_apply_sub hτ.ne' hxy)
    (fun a b hab => hR.injective (smul_right_injective V (inv_ne_zero hτ0) hab)) hQ hst hS hρ hu

end Semigroup

end RationalScheme

end TimeStepping

end Feec
