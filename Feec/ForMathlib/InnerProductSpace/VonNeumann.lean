module

public import Feec.ForMathlib.InnerProductSpace.Complexification
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Von Neumann's inequality

**Von Neumann's inequality** ([VonNeumann1951]): for a contraction `T` (`‖T‖ ≤ 1`) of a complex
inner product space and a polynomial `p`, `‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|`
(`ContinuousLinearMap.norm_aeval_le_of_norm_le_one`). The proof is the Poisson-kernel proof with
the circle replaced by the `M`-th roots of unity `ωᵐ` (`M` odd): for a strict contraction `S`,
`Yₘ = ∑_{k<N} ω^{-mk} Sᵏ` and the positive semidefinite form `B(u, v) = ⟪u, v⟫ - ⟪S u, S v⟫`,
the average `M⁻¹ ∑ₘ ωᵐⁿ B(Yₘ x, Yₘ y)` telescopes to `⟪x, Sⁿ y⟫ - ⟪S^{N-n} x, S^N y⟫`
(`sum_pow_mul_formB`, exact once `M > N + deg p`), and `|B(u, v)| ≤ (B(u, u) + B(v, v))/2`
(`norm_formB_le`) gives `|⟪x, p(S) y⟫| ≤ C (‖x‖² + ‖y‖²)/2 + O(‖S‖^{N - deg p})`; let `N → ∞`,
then `S = ρ T`, `ρ → 1`. No completeness is used. The odd `M` keeps `-1` out of the sample points,
so the bound on the circle may omit `-1` (`norm_aeval_le_of_forall_ne_neg_one`).

**Rational functions** (`norm_aeval_mul_inverse_le`, `E` complete): if `q` has no zero in the
closed unit disc, `q(T)` is invertible and `‖p(T) q(T)⁻¹‖ ≤ sup_{|ζ| = 1, ζ ≠ -1} |p(ζ)/q(ζ)|`.
Factor `q = c ∏ (X - b)`, `|b| > 1`; the polynomials `sₙ = c⁻¹ ∏ (-b⁻¹) ∑_{k<n} (X/b)ᵏ` satisfy
`q sₙ = ∏ (1 - (X/b)ⁿ) → 1` uniformly on the closed disc and in operator norm at `T`, so
`p sₙ → p/q` and von Neumann's inequality for `p sₙ` passes to the limit.

**Real coefficients over `𝕜 = ℝ` or `ℂ`** (`norm_aeval_map_mul_inverse_le`): for real polynomials
`p`, `q` and a contraction of a Hilbert space over `𝕜`, the same bound, through the
complexification (`Complexification`).

## References

* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [P. R. Halmos, *Finite-Dimensional Vector Spaces*][Halmos1974], §77 (complexification)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Polynomial Finset Filter Topology

namespace ContinuousLinearMap

section Polynomial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The form `B(u, v) = ⟪u, v⟫ - ⟪S u, S v⟫` of a contraction `S`. -/
private def formB (S : E →L[ℂ] E) (u v : E) : ℂ := ⟪u, v⟫ - ⟪S u, S v⟫

private theorem norm_apply_le_of_norm_le_one {S : E →L[ℂ] E} (hS : ‖S‖ ≤ 1) (u : E) :
    ‖S u‖ ≤ ‖u‖ :=
  (S.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hS (norm_nonneg u))

private theorem norm_pow_apply_le (S : E →L[ℂ] E) (k : ℕ) (u : E) :
    ‖(S ^ k) u‖ ≤ ‖S‖ ^ k * ‖u‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc ‖(S ^ (k + 1)) u‖ = ‖S ((S ^ k) u)‖ := by rw [pow_succ']; rfl
      _ ≤ ‖S‖ * (‖S‖ ^ k * ‖u‖) :=
        (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
      _ = ‖S‖ ^ (k + 1) * ‖u‖ := by ring

/-- `B(u, u) = ‖u‖² - ‖S u‖²`. -/
private theorem formB_self (S : E →L[ℂ] E) (u : E) :
    formB S u u = ((‖u‖ ^ 2 - ‖S u‖ ^ 2 : ℝ) : ℂ) := by
  simp only [formB, inner_self_eq_norm_sq_to_K]; push_cast; rfl

/-- **The form of a contraction is positive semidefinite**:
`|B(u, v)| ≤ (B(u, u) + B(v, v))/2`. -/
private theorem norm_formB_le {S : E →L[ℂ] E} (hS : ‖S‖ ≤ 1) (u v : E) :
    ‖formB S u v‖ ≤ ((‖u‖ ^ 2 - ‖S u‖ ^ 2) + (‖v‖ ^ 2 - ‖S v‖ ^ 2)) / 2 := by
  have hsq : ∀ w, ‖S w‖ ^ 2 ≤ ‖w‖ ^ 2 := fun w =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_of_norm_le_one hS w) 2
  set β := formB S u v
  rcases eq_or_ne β 0 with h | h
  · rw [h, norm_zero]; linarith [hsq u, hsq v]
  have hβ : 0 < ‖β‖ := norm_pos_iff.2 h
  set c : ℂ := conj β / (‖β‖ : ℂ)
  have hc : ‖c‖ = 1 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hβ.le,
      div_self hβ.ne']
  have hcβ : RCLike.re (c * β) = ‖β‖ := by
    have hβ0 : (‖β‖ : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
    have : c * β = (‖β‖ : ℂ) := by
      rw [div_mul_eq_mul_div, Complex.conj_mul', pow_two, mul_div_assoc, div_self hβ0, mul_one]
    rw [this]; simp
  have key := hsq (u - c • v)
  rw [map_sub, map_smul, @norm_sub_sq ℂ, @norm_sub_sq ℂ, inner_smul_right, inner_smul_right,
    norm_smul, norm_smul, hc, one_mul] at key
  have e : RCLike.re (c * ⟪u, v⟫) - RCLike.re (c * ⟪S u, S v⟫) = ‖β‖ := by
    rw [← map_sub, ← mul_sub]; exact hcβ
  nlinarith

/-- **Orthogonality of the roots of unity**: for a primitive `M`-th root `ω` and `a, b < M`,
`∑_{m<M} ωᵐᵃ conj(ωᵐᵇ) = M` if `a = b` and `0` otherwise. -/
private theorem sum_pow_mul_conj_pow {ω : ℂ} {M : ℕ} (hω : IsPrimitiveRoot ω M) {a b : ℕ}
    (ha : a < M) (hb : b < M) :
    ∑ m ∈ range M, (ω ^ m) ^ a * conj ((ω ^ m) ^ b) = if a = b then (M : ℂ) else 0 := by
  have hM : M ≠ 0 := by omega
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hM
  have e : ∀ m : ℕ, (ω ^ m) ^ a * conj ((ω ^ m) ^ b) = (ω ^ (a + (M - b))) ^ m := fun m => by
    have hz : ‖(ω ^ m) ^ b‖ = 1 := by rw [norm_pow, norm_pow, h1, one_pow, one_pow]
    have hw : (ω ^ m) ^ b * (ω ^ m) ^ (M - b) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hb.le, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one,
        one_pow]
    rw [← Complex.inv_eq_conj hz, ← eq_inv_of_mul_eq_one_right hw, ← pow_add, ← pow_mul,
      mul_comm, pow_mul]
  simp_rw [e]
  split_ifs with hab
  · subst hab
    rw [Nat.add_sub_cancel' hb.le, hω.pow_eq_one]
    simp
  · have hne : ω ^ (a + (M - b)) ≠ 1 := fun h' => by
      obtain ⟨k, hk⟩ := (hω.pow_eq_one_iff_dvd _).1 h'
      rcases k with _ | _ | k
      · omega
      · omega
      · have : 2 * M ≤ M * (k + 1 + 1) := by nlinarith
        omega
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- The averaging operator `Y = ∑_{k<N} conj(ζᵏ) Sᵏ`. -/
private def avgOp (S : E →L[ℂ] E) (ζ : ℂ) (N : ℕ) : E →L[ℂ] E :=
  ∑ k ∈ range N, conj (ζ ^ k) • S ^ k

private theorem formB_avgOp (S : E →L[ℂ] E) (ζ : ℂ) (N : ℕ) (x y : E) :
    formB S (avgOp S ζ N x) (avgOp S ζ N y) = ∑ j ∈ range N, ∑ k ∈ range N,
      ζ ^ j * conj (ζ ^ k) * formB S ((S ^ j) x) ((S ^ k) y) := by
  simp only [formB, avgOp, _root_.sum_apply, smul_apply, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Complex.conj_conj]
  conv_rhs => rw [sum_comm]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **The averaged form telescopes**: for a primitive `M`-th root `ω`, `n ≤ N` and `n + N ≤ M`,
`∑_{m<M} ωᵐⁿ B(Yₘ x, Yₘ y) = M (⟪x, Sⁿ y⟫ - ⟪S^{N-n} x, S^N y⟫)`. -/
private theorem sum_pow_mul_formB {ω : ℂ} {M N n : ℕ} (hω : IsPrimitiveRoot ω M) (hn : n ≤ N)
    (hNM : n + N ≤ M) (S : E →L[ℂ] E) (x y : E) :
    ∑ m ∈ range M, (ω ^ m) ^ n * formB S (avgOp S (ω ^ m) N x) (avgOp S (ω ^ m) N y) =
      M * (⟪x, (S ^ n) y⟫ - ⟪(S ^ (N - n)) x, (S ^ N) y⟫) := by
  have step : ∀ j ∈ range N, ∀ k ∈ range N, ∑ m ∈ range M, (ω ^ m) ^ n *
      ((ω ^ m) ^ j * conj ((ω ^ m) ^ k) * formB S ((S ^ j) x) ((S ^ k) y)) =
        formB S ((S ^ j) x) ((S ^ k) y) * if n + j = k then (M : ℂ) else 0 := by
    intro j hj k hk
    rw [← sum_pow_mul_conj_pow hω (a := n + j) (by simp at hj; omega) (by simp at hk; omega),
      mul_sum]
    refine sum_congr rfl fun m _ => ?_
    ring
  simp_rw [formB_avgOp, mul_sum]
  trans ∑ j ∈ range N, ∑ k ∈ range N,
    formB S ((S ^ j) x) ((S ^ k) y) * if n + j = k then (M : ℂ) else 0
  · rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    rw [sum_comm]
    exact sum_congr rfl fun k hk => step j hj k hk
  simp_rw [mul_ite, mul_zero, sum_ite_eq, mem_range, ← sum_filter]
  rw [show (range N).filter (fun j => n + j < N) = range (N - n) by ext j; simp; omega,
    ← sum_mul, mul_comm]
  congr 1
  have e : ∀ j, formB S ((S ^ j) x) ((S ^ (n + j)) y) =
      ⟪(S ^ j) x, (S ^ (n + j)) y⟫ - ⟪(S ^ (j + 1)) x, (S ^ (n + (j + 1))) y⟫ := fun j => by
    rw [formB, ← add_assoc, pow_succ' S j, pow_succ' S (n + j)]; rfl
  simp_rw [e]
  rw [sum_range_sub' (fun j => ⟪(S ^ j) x, (S ^ (n + j)) y⟫), pow_zero, add_zero,
    Nat.add_sub_cancel' hn]
  rfl

/-- The sample points `ωᵐ` (`M` odd) are on the circle and avoid `-1`. -/
private theorem norm_root_pow {ω : ℂ} {M : ℕ} (hω : IsPrimitiveRoot ω M) (hM : Odd M) (m : ℕ) :
    ‖ω ^ m‖ = 1 ∧ ω ^ m ≠ -1 := by
  have hM0 : M ≠ 0 := by rintro rfl; simp at hM
  refine ⟨by rw [norm_pow, hω.norm'_eq_one hM0, one_pow], fun h => ?_⟩
  have h1 : (ω ^ m) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  rw [h, hM.neg_one_pow] at h1
  norm_num at h1

/-- **The averaged estimate**: for a contraction `S`, `deg p ≤ N` and `|p| ≤ C` on the circle
(without `-1`), `|⟪x, p(S) y⟫ - ∑ₙ pₙ ⟪S^{N-n} x, S^N y⟫| ≤ C (‖x‖² + ‖y‖²)/2`. -/
private theorem norm_inner_aeval_sub_le {S : E →L[ℂ] E} (hS : ‖S‖ ≤ 1) {p : ℂ[X]} {C : ℝ}
    (hp : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ -1 → ‖p.eval ζ‖ ≤ C) {N : ℕ} (hN : p.natDegree ≤ N) (x y : E) :
    ‖⟪x, aeval S p y⟫ - ∑ n ∈ range (p.natDegree + 1),
        p.coeff n * ⟪(S ^ (N - n)) x, (S ^ N) y⟫‖ ≤ C * (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  set M := 2 * N + 1
  have hM0 : M ≠ 0 := by omega
  have hω := Complex.isPrimitiveRoot_exp M hM0
  set ω := Complex.exp (2 * Real.pi * Complex.I / M)
  have hpts := norm_root_pow hω (by simp [M]) (M := M)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hp 1 (by simp) (by norm_num))
  -- the identity
  have hid : ∑ m ∈ range M, p.eval (ω ^ m) * formB S (avgOp S (ω ^ m) N x) (avgOp S (ω ^ m) N y)
      = M * (⟪x, aeval S p y⟫ - ∑ n ∈ range (p.natDegree + 1),
        p.coeff n * ⟪(S ^ (N - n)) x, (S ^ N) y⟫) := by
    simp_rw [eval_eq_sum_range, sum_mul]
    rw [sum_comm, aeval_eq_sum_range, _root_.sum_apply, inner_sum, mul_sub, mul_sum, mul_sum,
      ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn' : n ≤ p.natDegree := by simp at hn; omega
    simp_rw [mul_assoc]
    rw [← mul_sum, sum_pow_mul_formB hω (hn'.trans hN) (by omega), smul_apply, inner_smul_right]
    ring
  -- the diagonal sums
  have hdiag : ∀ z : E, ∑ m ∈ range M, (‖avgOp S (ω ^ m) N z‖ ^ 2 -
      ‖S (avgOp S (ω ^ m) N z)‖ ^ 2) ≤ M * ‖z‖ ^ 2 := fun z => by
    have h := sum_pow_mul_formB hω (Nat.zero_le N) (by omega) S z z
    simp only [pow_zero, one_mul, formB_self, Nat.sub_zero, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K] at h
    have h' : ∑ m ∈ range M, (‖avgOp S (ω ^ m) N z‖ ^ 2 - ‖S (avgOp S (ω ^ m) N z)‖ ^ 2) =
        M * (‖z‖ ^ 2 - ‖(S ^ N) z‖ ^ 2) := by
      apply Complex.ofReal_injective; push_cast at h ⊢; exact h
    rw [h']
    nlinarith [sq_nonneg ‖(S ^ N) z‖, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hM : (0 : ℝ) < M := by positivity
  have hsum : ‖∑ m ∈ range M, p.eval (ω ^ m) *
      formB S (avgOp S (ω ^ m) N x) (avgOp S (ω ^ m) N y)‖ ≤
      C / 2 * (∑ m ∈ range M, (‖avgOp S (ω ^ m) N x‖ ^ 2 - ‖S (avgOp S (ω ^ m) N x)‖ ^ 2) +
        ∑ m ∈ range M, (‖avgOp S (ω ^ m) N y‖ ^ 2 - ‖S (avgOp S (ω ^ m) N y)‖ ^ 2)) := by
    rw [← sum_add_distrib, mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
    rw [norm_mul]
    calc _ ≤ C * (((‖avgOp S (ω ^ m) N x‖ ^ 2 - ‖S (avgOp S (ω ^ m) N x)‖ ^ 2) +
          (‖avgOp S (ω ^ m) N y‖ ^ 2 - ‖S (avgOp S (ω ^ m) N y)‖ ^ 2)) / 2) :=
          mul_le_mul (hp _ (hpts m).1 (hpts m).2) (norm_formB_le hS _ _) (norm_nonneg _) hC
      _ = _ := by ring
  rw [hid, norm_mul, Complex.norm_natCast] at hsum
  have hx := hdiag x
  have hy := hdiag y
  refine le_of_mul_le_mul_left ?_ hM
  nlinarith

/-- Von Neumann's inequality for **strict contractions**. -/
private theorem norm_aeval_le_of_norm_lt_one {S : E →L[ℂ] E} (hS : ‖S‖ < 1) {p : ℂ[X]} {C : ℝ}
    (hp : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ -1 → ‖p.eval ζ‖ ≤ C) : ‖aeval S p‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hp 1 (by simp) (by norm_num))
  set A := ∑ n ∈ range (p.natDegree + 1), ‖p.coeff n‖
  have hin : ∀ x y : E, ‖⟪x, aeval S p y⟫‖ ≤ C * (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := fun x y => by
    have hlim : Tendsto (fun N : ℕ => C * (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 + A * ‖x‖ * ‖y‖ * ‖S‖ ^ N)
        atTop (𝓝 (C * (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hS).const_mul (A * ‖x‖ * ‖y‖))
    refine ge_of_tendsto hlim (eventually_atTop.2 ⟨p.natDegree, fun N hN => ?_⟩)
    have h1 := norm_inner_aeval_sub_le hS.le hp hN x y
    have h2 : ‖∑ n ∈ range (p.natDegree + 1), p.coeff n * ⟪(S ^ (N - n)) x, (S ^ N) y⟫‖ ≤
        A * ‖x‖ * ‖y‖ * ‖S‖ ^ N := by
      refine (norm_sum_le _ _).trans ?_
      rw [sum_mul, sum_mul, sum_mul]
      refine sum_le_sum fun n _ => ?_
      rw [norm_mul, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖⟪(S ^ (N - n)) x, (S ^ N) y⟫‖ ≤ ‖(S ^ (N - n)) x‖ * ‖(S ^ N) y‖ :=
            norm_inner_le_norm _ _
        _ ≤ (‖S‖ ^ (N - n) * ‖x‖) * (‖S‖ ^ N * ‖y‖) :=
            mul_le_mul (norm_pow_apply_le _ _ _) (norm_pow_apply_le _ _ _) (norm_nonneg _)
              (by positivity)
        _ ≤ (1 * ‖x‖) * (‖S‖ ^ N * ‖y‖) := by
            gcongr; exact pow_le_one₀ (norm_nonneg _) hS.le
        _ = ‖x‖ * (‖y‖ * ‖S‖ ^ N) := by ring
    have h3 := norm_sub_norm_le ⟪x, aeval S p y⟫
      (∑ n ∈ range (p.natDegree + 1), p.coeff n * ⟪(S ^ (N - n)) x, (S ^ N) y⟫)
    linarith
  refine opNorm_le_bound _ hC fun y => ?_
  set u := aeval S p y
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, norm_zero]; positivity
  have hy : y ≠ 0 := by rintro rfl; simp [u] at hu
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h := hin (((‖y‖ / ‖u‖ : ℝ) : ℂ) • u) y
  rw [show aeval S p y = u from rfl] at h
  simp only [inner_smul_left, inner_self_eq_norm_sq_to_K, norm_mul, norm_pow,
    Complex.conj_ofReal, Complex.norm_real, RCLike.norm_ofReal, Real.norm_eq_abs, abs_norm,
    norm_smul] at h
  rw [abs_of_nonneg (by positivity), div_mul_cancel₀ _ hu'.ne'] at h
  have : ‖y‖ * ‖u‖ ≤ ‖y‖ * (C * ‖y‖) := by
    have e : ‖y‖ / ‖u‖ * ‖u‖ ^ 2 = ‖y‖ * ‖u‖ := by field_simp
    nlinarith
  exact le_of_mul_le_mul_left this hy'

/-- **Von Neumann's inequality, with the circle punctured at `-1`**: for a contraction `T` of a
complex inner product space, `‖p(T)‖ ≤ C` when `|p(ζ)| ≤ C` for `|ζ| = 1`, `ζ ≠ -1`. -/
theorem norm_aeval_le_of_forall_ne_neg_one {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) {p : ℂ[X]} {C : ℝ}
    (hp : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ -1 → ‖p.eval ζ‖ ≤ C) : ‖aeval T p‖ ≤ C := by
  have hcont : Continuous fun ρ : ℝ => aeval ((ρ : ℂ) • T) p :=
    (Polynomial.continuous_aeval p).comp (Complex.continuous_ofReal.smul continuous_const)
  have hlim : Tendsto (fun ρ : ℝ => ‖aeval ((ρ : ℂ) • T) p‖) (𝓝[<] 1) (𝓝 ‖aeval T p‖) := by
    simpa using ((hcont.tendsto 1).mono_left nhdsWithin_le_nhds).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
  refine norm_aeval_le_of_norm_lt_one ?_ hp
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.1.le]
  calc ρ * ‖T‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hT hρ.1.le
    _ < 1 := by linarith [hρ.2]

/-- **Von Neumann's inequality** ([VonNeumann1951]): for a contraction `T` of a complex inner
product space and a polynomial `p`, `‖p(T)‖ ≤ sup_{|ζ| = 1} |p(ζ)|`. -/
theorem norm_aeval_le_of_norm_le_one {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) {p : ℂ[X]} {C : ℝ}
    (hp : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖p.eval ζ‖ ≤ C) : ‖aeval T p‖ ≤ C :=
  norm_aeval_le_of_forall_ne_neg_one hT fun ζ hζ _ => hp ζ hζ

end Polynomial

section Rational

/-- `‖∏ (1 - uᵢ) - 1‖ ≤ (1 + ε)ᵏ - 1` for `k` factors with `‖uᵢ‖ ≤ ε`, in a seminormed ring with
`‖1‖ ≤ 1`. -/
private theorem norm_prod_one_sub_sub_one_le {R : Type*} [SeminormedRing R] (h1 : ‖(1 : R)‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ l : List R, (∀ u ∈ l, ‖u‖ ≤ ε) → ‖(l.map (1 - ·)).prod - 1‖ ≤ (1 + ε) ^ l.length - 1
  | [], _ => by simp
  | u :: l, hl => by
    have ih := norm_prod_one_sub_sub_one_le h1 hε l fun v hv => hl v (List.mem_cons_of_mem _ hv)
    have hu := hl u List.mem_cons_self
    rw [List.map_cons, List.prod_cons, List.length_cons]
    set P := (l.map (1 - ·)).prod
    have e : (1 - u) * P - 1 = (P - 1) - u * P := by noncomm_ring
    have hP : ‖P‖ ≤ (1 + ε) ^ l.length := by
      calc ‖P‖ = ‖1 + (P - 1)‖ := by rw [add_sub_cancel]
        _ ≤ ‖(1 : R)‖ + ‖P - 1‖ := norm_add_le _ _
        _ ≤ 1 + ((1 + ε) ^ l.length - 1) := add_le_add h1 ih
        _ = _ := by ring
    rw [e]
    calc ‖P - 1 - u * P‖ ≤ ‖P - 1‖ + ‖u‖ * ‖P‖ :=
          (norm_sub_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
      _ ≤ ((1 + ε) ^ l.length - 1) + ε * (1 + ε) ^ l.length :=
          add_le_add ih (mul_le_mul hu hP (norm_nonneg _) hε)
      _ = (1 + ε) ^ (l.length + 1) - 1 := by ring

private theorem norm_pow_le_of_norm_one_le {R : Type*} [SeminormedRing R] (h1 : ‖(1 : R)‖ ≤ 1)
    (a : R) : ∀ n : ℕ, ‖a ^ n‖ ≤ ‖a‖ ^ n
  | 0 => by simpa using h1
  | n + 1 => norm_pow_le' a n.succ_pos

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Von Neumann's inequality for rational functions**: for a contraction `T` of a complex
Hilbert space and polynomials `p`, `q` with `q` free of zeros in the closed unit disc, `q(T)` is
invertible and `‖p(T) q(T)⁻¹‖ ≤ C` whenever `|p(ζ)/q(ζ)| ≤ C` on the unit circle (`-1` may be
omitted). [VonNeumann1951] -/
theorem norm_aeval_mul_inverse_le {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) {p q : ℂ[X]}
    (hq : ∀ w : ℂ, ‖w‖ ≤ 1 → q.eval w ≠ 0) {K : ℝ}
    (hK : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ -1 → ‖p.eval ζ / q.eval ζ‖ ≤ K) :
    IsUnit (aeval T q) ∧ ‖aeval T p * Ring.inverse (aeval T q)‖ ≤ K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 1 (by simp) (by norm_num))
  have h1 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := norm_id_le
  have hq0 : q ≠ 0 := fun h => hq 0 (by simp) (by simp [h])
  set c := q.leadingCoeff
  have hc : c ≠ 0 := leadingCoeff_ne_zero.2 hq0
  set bs := q.roots.toList
  have hfac : q = C c * (bs.map fun b => X - C b).prod := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := q))
    rw [← Multiset.coe_toList q.roots, Multiset.map_coe, Multiset.prod_coe] at h
    exact h.symm
  -- the roots are outside the closed disc
  have hb : ∀ b ∈ bs, 1 < ‖b‖ := fun b hbm => by
    have : q.eval b = 0 := (mem_roots hq0).1 (Multiset.mem_toList.1 hbm)
    by_contra h
    exact hq b (not_lt.1 h) this
  have hb0 : ∀ b ∈ bs, b ≠ 0 := fun b hbm h => by
    have := hb b hbm; rw [h, norm_zero] at this; linarith
  have hsmul : ∀ b ∈ bs, ‖b⁻¹ • T‖ ≤ ‖b‖⁻¹ := fun b _ => by
    rw [norm_smul, norm_inv]; exact mul_le_of_le_one_right (by positivity) hT
  -- invertibility
  have hunit : IsUnit (aeval T q) := by
    rw [hfac, map_mul, aeval_C, map_list_prod, List.map_map]
    refine ((isUnit_iff_ne_zero.2 hc).map (algebraMap ℂ (E →L[ℂ] E))).mul
      (List.prod_isUnit fun x hx => ?_)
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hx
    have hlt : ‖b⁻¹ • T‖ < 1 := (hsmul b hbm).trans_lt (inv_lt_one_of_one_lt₀ (hb b hbm))
    have e : (aeval T ∘ fun b => X - C b) b = algebraMap ℂ (E →L[ℂ] E) (-b) * (1 - b⁻¹ • T) := by
      simp only [Function.comp_apply, map_sub, aeval_X, aeval_C, mul_sub, mul_one,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul, neg_mul,
        mul_inv_cancel₀ (hb0 b hbm), one_smul, map_neg]
      abel
    rw [e]
    exact ((isUnit_iff_ne_zero.2 (neg_ne_zero.2 (hb0 b hbm))).map _).mul
      (Units.oneSub _ hlt).isUnit
  -- the approximants `sₙ` of `1 / q`: `q sₙ = Pₙ = ∏ (1 - (X/b)ⁿ)`
  set s : ℕ → ℂ[X] := fun N =>
    C c⁻¹ * (bs.map fun b => C (-b⁻¹) * ∑ k ∈ range N, (C b⁻¹ * X) ^ k).prod
  set P : ℕ → ℂ[X] := fun N => (bs.map fun b => 1 - (C b⁻¹ * X) ^ N).prod
  have hqs : ∀ N, q * s N = P N := fun N => by
    conv_lhs => rw [hfac]
    simp only [s, P]
    rw [mul_mul_mul_comm, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul, ← List.prod_map_mul]
    congr 1
    refine List.map_congr_left fun b hbm => ?_
    have e : (X - C b) * C (-b⁻¹) = 1 - C b⁻¹ * X := by
      apply Polynomial.funext; intro w
      simp only [eval_mul, eval_sub, eval_X, eval_C, eval_one]
      field_simp [hb0 b hbm]
      ring
    rw [← mul_assoc, e, mul_comm, geom_sum_mul_neg]
  -- the size of `Pₙ - 1` on the circle and at `T`
  set ε : ℕ → ℝ := fun N => (bs.map fun b => ‖b‖⁻¹ ^ N).sum
  set δ : ℕ → ℝ := fun N => (1 + ε N) ^ bs.length - 1
  have hε0 : ∀ N, 0 ≤ ε N := fun N => List.sum_nonneg fun x hx => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; positivity
  have hεb : ∀ N, ∀ b ∈ bs, ‖b‖⁻¹ ^ N ≤ ε N := fun N b hbm =>
    List.single_le_sum (fun x hx => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; positivity) _
      (List.mem_map_of_mem hbm)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hε : Tendsto ε atTop (𝓝 0) := by
      have := tendsto_list_sum (l := bs) (f := fun b N => ‖b‖⁻¹ ^ N) (a := fun _ => 0)
        (x := atTop) fun b hbm => tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
          (inv_lt_one_of_one_lt₀ (hb b hbm))
      simpa only [List.map_const', List.sum_replicate, smul_zero] using this
    simpa [δ] using ((hε.const_add 1).pow bs.length).sub_const 1
  have hPζ : ∀ N, ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖(P N).eval ζ‖ ≤ 1 + δ N := fun N ζ hζ => by
    have e : (P N).eval ζ = ((bs.map fun b => (b⁻¹ * ζ) ^ N).map (1 - ·)).prod := by
      simp only [P, eval_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun b _ => ?_
      simp
    have := norm_prod_one_sub_sub_one_le (R := ℂ) (by simp) (hε0 N)
      (bs.map fun b => (b⁻¹ * ζ) ^ N) fun u hu => by
        obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hu
        rw [norm_pow, norm_mul, hζ, mul_one, norm_inv]; exact hεb N b hbm
    rw [List.length_map, ← e] at this
    have := norm_le_norm_sub_add ((P N).eval ζ) 1
    simp only [norm_one] at this
    linarith
  have hPT : ∀ N, ‖aeval T (P N) - 1‖ ≤ δ N := fun N => by
    have e : aeval T (P N) = ((bs.map fun b => (b⁻¹ • T) ^ N).map (1 - ·)).prod := by
      simp only [P, map_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun b _ => ?_
      simp [Algebra.algebraMap_eq_smul_one]
    have := norm_prod_one_sub_sub_one_le h1 (hε0 N) (bs.map fun b => (b⁻¹ • T) ^ N)
      fun u hu => by
        obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hu
        exact (norm_pow_le_of_norm_one_le h1 _ N).trans
          ((pow_le_pow_left₀ (norm_nonneg _) (hsmul b hbm) N).trans (hεb N b hbm))
    rwa [List.length_map, ← e] at this
  clear_value s P
  -- the limit
  set F := aeval T p * Ring.inverse (aeval T q)
  have hFD : F * aeval T q = aeval T p := by
    rw [mul_assoc, Ring.inverse_mul_cancel _ hunit, mul_one]
  have hbound : ∀ N, ‖F‖ ≤ K * (1 + δ N) + ‖F‖ * δ N := fun N => by
    have hQ : ‖aeval T (p * s N)‖ ≤ K * (1 + δ N) :=
      norm_aeval_le_of_forall_ne_neg_one hT fun ζ hζ hζ1 => by
        have hqζ : q.eval ζ ≠ 0 := hq ζ hζ.le
        have e : (p * s N).eval ζ = p.eval ζ / q.eval ζ * (P N).eval ζ := by
          rw [← hqs, eval_mul, eval_mul, div_mul_eq_mul_div, mul_div_assoc,
            mul_div_cancel_left₀ _ hqζ]
        rw [e, norm_mul]
        exact mul_le_mul (hK ζ hζ hζ1) (hPζ N ζ hζ) (norm_nonneg _) hK0
    have hdiff : ‖F - aeval T (p * s N)‖ ≤ ‖F‖ * δ N := by
      have e : F - aeval T (p * s N) = -(F * (aeval T (P N) - 1)) := by
        rw [← hqs, map_mul, map_mul, mul_sub, ← mul_assoc, hFD, mul_one, neg_sub]
      rw [e, norm_neg]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hPT N) (norm_nonneg _))
    have := norm_le_norm_sub_add F (aeval T (p * s N))
    linarith
  have hlim : Tendsto (fun N => K * (1 + δ N) + ‖F‖ * δ N) atTop (𝓝 K) := by
    simpa using ((hδ.const_add 1).const_mul K).add (hδ.const_mul ‖F‖)
  exact ⟨hunit, ge_of_tendsto' hlim hbound⟩

end Rational

section RealCoefficients

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- **Von Neumann's inequality for real rational functions over `𝕜 = ℝ` or `ℂ`**: for a
contraction `T` of a Hilbert space over `𝕜` and real polynomials `p`, `q` with `q` free of zeros
in the closed unit disc, `q(T)` is invertible and `‖p(T) q(T)⁻¹‖ ≤ C` whenever `|p(ζ)/q(ζ)| ≤ C`
on the unit circle (`-1` may be omitted); through the complexification. [VonNeumann1951];
[Halmos1974], §77 -/
theorem norm_aeval_map_mul_inverse_le {T : V →L[𝕜] V} (hT : ‖T‖ ≤ 1) {p q : ℝ[X]}
    (hq : ∀ w : ℂ, ‖w‖ ≤ 1 → aeval w q ≠ 0) {C : ℝ}
    (hC : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ -1 → ‖aeval ζ p / aeval ζ q‖ ≤ C) :
    IsUnit (aeval T (q.map (algebraMap ℝ 𝕜))) ∧
      ‖aeval T (p.map (algebraMap ℝ 𝕜)) * Ring.inverse (aeval T (q.map (algebraMap ℝ 𝕜)))‖ ≤ C := by
  have h := norm_aeval_mul_inverse_le (T := T.complexification)
    (by rwa [norm_complexification]) (p := p.map (algebraMap ℝ ℂ)) (q := q.map (algebraMap ℝ ℂ))
    (by simpa only [eval_map_algebraMap] using hq) (by simpa only [eval_map_algebraMap] using hC)
  rw [← complexification_aeval, ← complexification_aeval] at h
  have hu := isUnit_of_isUnit_complexification h.1
  refine ⟨hu, norm_le_of_norm_complexification_le ?_⟩
  rw [← complexification_ringInverse hu, ← complexification_mul] at h
  exact h.2

end RealCoefficients

end ContinuousLinearMap
