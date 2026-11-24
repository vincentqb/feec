module

public import Feec.ForMathlib.Analysis.Polynomial
public import Feec.ForMathlib.Analysis.StrongConvergence
public import Feec.ForMathlib.InnerProductSpace.VonNeumann
public import Feec.TimeStepping.Convergence

/-!
# A-stable rational schemes

A **rational scheme** (`RationalScheme`) is a real rational function `r = n/d`, bounded at
infinity (`deg n ≤ deg d`) and without poles in the closed left half-plane; it approximates the
exponential by the one-step scheme `u ↦ r(τ A) u` for `u' = A u`. It is **A-stable**
(`RationalScheme.IsAStable`) if `|r(iy)| ≤ 1` on the imaginary axis (by the maximum principle this
is the usual condition on the closed left half-plane, [HairerWanner1996], §IV.3:
`RationalScheme.isAStable_iff_forall_re_nonpos` in `Feec.TimeStepping.AStableSchemes`; only the
imaginary axis is used here), **L-stable** (`RationalScheme.IsLStable`) if moreover `r(∞) = 0`,
i.e. `deg n < deg d` (**strongly A-stable**, `RationalScheme.IsStronglyAStable`, if only
`|r(∞)| < 1`), and of **order `p`**
(`RationalScheme.HasOrder`) if `r(z) - e^z = O(z^{p+1})`, i.e. `X^{p+1}` divides `n - d Tₚ` with
`Tₚ = ∑_{j≤p} Xʲ/j!` (`expTaylor`).

**The operator `r(τ A)` for every m-dissipative `A`** (`RationalScheme.step`, possibly unbounded,
over `𝕜 = ℝ` or `ℂ`): through the Cayley transform `C = (1 + τ A)(1 - τ A)⁻¹`
(`Feec.TimeStepping.cayley`), a contraction, and the **Cayley transform of polynomials**
(`cayleyPoly`, `q̃(w) = (w + 1)ᴺ q((w - 1)/(w + 1))`), `r(τ A) = ñ(C) d̃(C)⁻¹`; the poles of
`ñ/d̃` lie outside the closed unit disc. For a bounded `L` this is `n(τ L) d(τ L)⁻¹`
(`RationalScheme.step_toPMap`, `RationalScheme.apply`), since `ñ(C) = 2ᴺ Sᴺ n(τ L)` with
`S = (1 - τ L)⁻¹` (`aeval_cayleyPoly`).

## Main results

* **`RationalScheme.norm_step_le`** (von Neumann's inequality in the half-plane): for every
  m-dissipative `A` and `τ > 0`, `‖r(τ A)‖ ≤ sup_{y ∈ ℝ} |r(iy)|` (`RationalScheme.supNorm`,
  finite: `RationalScheme.bddAbove`), uniformly in `A`; for an A-stable scheme `‖r(τ A)‖ ≤ 1`
  (`norm_step_le_one`). This is `ContinuousLinearMap.norm_aeval_map_mul_inverse_le` for the
  contraction `C`; it is a theorem for every Hilbert space, not only finite-dimensional ones.
  For bounded dissipative `L`: `isUnit_aeval_den`, `norm_apply_le`, `norm_apply_le_one`.
* **`r(τ A)` through the resolvent** (`RationalScheme.step_eq_resolventEval`): with
  `S = (1 - τ A)⁻¹` and `N = deg d`, `r(τ A) = P(S) Q(S)⁻¹` for `P(s) = sᴺ n(1 - 1/s)`,
  `Q(s) = sᴺ d(1 - 1/s)` (`resolventEval`), polynomials in the bounded `S`; `Q(S)` is invertible
  (`RationalScheme.isUnit_resolventEval_den`), and `S` is the only operator mapping `x - τ A x`
  to `x` (`apply_sub_smul_eq_iff`).
* **Complex coefficients** (`norm_resolventEval_mul_inverse_le`): for complex polynomials
  `p`, `q` with `deg p ≤ deg q`, `q` free of zeros for `re z ≤ 0`, and every m-dissipative `A`
  of a complex Hilbert space, `‖P(S) Q(S)⁻¹‖ ≤ sup_y |p(iy)/q(iy)|` (finite:
  `bddAbove_norm_div_imaginary`); for bounded `L`, `P(S) Q(S)⁻¹ = p(L) q(L)⁻¹` at
  `S = (1 - L)⁻¹` (`resolventEval_eq_aeval`), so `‖p(L) q(L)⁻¹‖ ≤ sup_y |p(iy)/q(iy)|` for bounded
  dissipative `L` (`norm_aeval_mul_inverse_le_of_dissipative`).
* **Order from the asymptotics** (`RationalScheme.hasOrder_of_isBigO`): `r(z) - e^z = O(z^{p+1})`
  at `0` gives order `p`; over `ℂ`, `X^{p+1} ∣ n - d Tₚ` (`X_pow_dvd_sub_mul_expTaylor`).
* **Consistency** (`RationalScheme.isConsistent`): a scheme of order `p` is consistent of order
  `p` with every bounded dissipative `L`, with constant
  `K = sup_y |(r(iy) - Tₚ(iy))/(iy)^{p+1}| + 1/(p+1)!`: `r = Tₚ + X^{p+1} ρ` with `ρ` the
  remainder scheme (`RationalScheme.remainder`, same denominator), whose norm at `τ L` is bounded
  by von Neumann's inequality again.
* **`RationalScheme.norm_apply_pow_sub_exp_le`** (Brenner–Thomée): at `t = n τ`,
  `‖r(τ L)ⁿ y - e^{tL} y‖ ≤ K t τᵖ ‖L^{p+1} y‖` for every bounded dissipative `L`; for complex
  coefficients `norm_aeval_mul_inverse_pow_sub_exp_le`; both through the consistency of
  `n(τL) d(τL)⁻¹` from `n = d Tₚ + X^{p+1} ρ` over `𝕜`
  (`RationalScheme.isConsistent_aeval_mul_inverse`). For unbounded m-dissipative generators,
  with the same constant: `Feec.TimeStepping.RationalScheme.norm_step_pow_sub_semigroup_le`
  (`Feec.TimeStepping.RationalSemigroup`), through the Cayley form of a bounded `L`,
  `f̃(C) g̃(C)⁻¹ = f(τ L) g(τ L)⁻¹` (`aeval_cayley_mul_inverse`), and the resolvent form
  `P(S) Q(S)⁻¹ = f̃(C) g̃(C)⁻¹` (`resolventEval_mul_inverse_eq`).
* **Discrete constraint propagation** (`RationalScheme.apply_mem_of_mapsTo`): a closed subspace
  `K` with `L K ⊆ K` is kept by `r(L)`.
* **Symmetric schemes** (`RationalScheme.IsSymmetric`, `n(z) = d(-z)`: the diagonal Padé and
  Gauss methods): `|r(iy)| = 1`, so they are A-stable (`IsSymmetric.isAStable`), but
  `|r(∞)| = 1`, so never strongly A-stable (`IsSymmetric.not_isStronglyAStable`), and
  `r(L)` is an isometry for skew `L` (`IsSymmetric.norm_apply_apply`).
* **The θ-schemes** (`RationalScheme.theta`): A-stable for `θ ≥ 1/2`, order `1`, and
  Crank–Nicolson (`θ = 1/2`) symmetric of order `2`; `r_θ(τ L)` is the θ-step
  `Feec.TimeStepping.thetaStep` (`RationalScheme.apply_theta`). For bounded dissipative `L` the
  θ-scheme is consistent of order `1` with `K = θ + 1/2` (remainder `θ/(1 - θ z)`) and
  Crank–Nicolson of order `2` with `K = 5/12` (remainder `(1/4)/(1 - z/2)`)
  (`isConsistent_thetaStep`, `isConsistent_thetaStep_half`); at `t = n τ`,
  `‖r_θ(τ L)ⁿ y - e^{tL} y‖ ≤ (θ + 1/2) t τ ‖L² y‖` for `θ ≥ 1/2`
  (`norm_thetaStep_pow_sub_exp_le`) and `‖cayley(L, τ/2)ⁿ y - e^{tL} y‖ ≤ 5/12 t τ² ‖L³ y‖`
  (`norm_cayley_pow_sub_exp_le`). The constants are not sharp: the leading error constant of
  Crank–Nicolson is `1/12` (`e^z - r_{1/2}(z) = -z³/12 + O(z⁴)`).

## References

* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996],
  §IV.3 (stability functions, A- and L-stability, Padé approximations), §IV.11 (von Neumann's
  theorem: contractivity for dissipative problems)
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7
  (consistency and global error of the θ-schemes)
* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
  (von Neumann's inequality: the contractivity of A-stable rational schemes on Hilbert spaces)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.18 (constraint propagation, here at the discrete level)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate
open scoped Topology
open Polynomial Finset Feec.Operator NormedSpace Asymptotics

@[expose] public noncomputable section

namespace Feec.TimeStepping

/-! ### The Cayley transform of polynomials -/

section CayleyPoly

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The **Cayley transform** of a polynomial `q` to degree `N`:
`q̃(w) = ∑_{k ≤ N} qₖ (w - 1)ᵏ (w + 1)^{N-k} = (w + 1)ᴺ q((w - 1)/(w + 1))`. -/
def cayleyPoly (N : ℕ) (q : R[X]) : R[X] :=
  ∑ k ∈ range (N + 1), C (q.coeff k) * (X - 1) ^ k * (X + 1) ^ (N - k)

theorem cayleyPoly_map {R' : Type*} [CommRing R'] (f : R →+* R') (N : ℕ) (q : R[X]) :
    (cayleyPoly N q).map f = cayleyPoly N (q.map f) := by
  simp [cayleyPoly, Polynomial.map_sum, coeff_map]

/-- A polynomial commutes with everything its variable commutes with. -/
theorem commute_aeval {a b : A} (h : Commute a b) (q : R[X]) : Commute (aeval a q) b := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_left _ _ _ fun i _ => (h.pow_left i).smul_left _

/-- **The Cayley transform at `2 S - 1`**: if `S (1 - L) = 1` and `S L = L S`, then
`q̃(2 S - 1) = (2 S)ᴺ q(L)` for `deg q ≤ N`. -/
theorem aeval_cayleyPoly {S L : A} (hS : S * (1 - L) = 1) (hc : Commute S L) {N : ℕ}
    {q : R[X]} (hq : q.natDegree ≤ N) :
    aeval (2 * S - 1) (cayleyPoly N q) = (2 * S) ^ N * aeval L q := by
  have hU : Commute (2 * S) L := (Commute.ofNat_left 2 L).mul_left hc
  have h1 : 2 * S - 1 - 1 = 2 * S * L := by
    calc 2 * S - 1 - 1 = 2 * (S - S * (1 - L)) := by rw [hS]; noncomm_ring
      _ = 2 * S * L := by noncomm_ring
  simp only [cayleyPoly, map_sum, map_mul, map_pow, map_sub, map_add, aeval_X, aeval_C, map_one,
    h1, sub_add_cancel]
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hq), mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [hU.mul_pow, Algebra.smul_def, mul_assoc, mul_assoc, (hU.pow_pow (N - k) k).symm.eq,
    ← mul_assoc ((2 * S) ^ k), ← pow_add, Nat.add_sub_cancel' hk', ← mul_assoc,
    Algebra.commutes, mul_assoc]

/-- The scalar Cayley transform: `q̃(w) = (w + 1)ᴺ q((w - 1)/(w + 1))` for `w ≠ -1`. -/
theorem aeval_cayleyPoly_complex {q : ℝ[X]} {N : ℕ} (hq : q.natDegree ≤ N) {w : ℂ}
    (hw : w ≠ -1) :
    aeval w (cayleyPoly N q) = (w + 1) ^ N * aeval ((w - 1) / (w + 1)) q := by
  have hw1 : w + 1 ≠ 0 := fun h => hw (eq_neg_of_add_eq_zero_left h)
  have := aeval_cayleyPoly (R := ℝ) (S := (w + 1) / 2) (L := (w - 1) / (w + 1))
    (by field_simp; ring) (Commute.all _ _) hq
  rwa [show 2 * ((w + 1) / 2) - 1 = w by ring, show 2 * ((w + 1) / 2) = w + 1 by ring] at this

/-- `q̃(-1) = q_N (-2)ᴺ`. -/
theorem aeval_neg_one_cayleyPoly (q : ℝ[X]) (N : ℕ) :
    aeval (-1 : ℂ) (cayleyPoly N q) = q.coeff N * (-2) ^ N := by
  simp only [cayleyPoly, map_sum, map_mul, map_pow, map_sub, map_add, aeval_X, aeval_C, map_one,
    sum_range_succ, Nat.sub_self, pow_zero, mul_one, neg_add_cancel]
  rw [sum_eq_zero fun k hk => by
    rw [zero_pow (by have := mem_range.1 hk; omega), mul_zero], zero_add]
  norm_num

/-- **`sᴺ f(1 - 1/s)` at `s = S`**: `∑_{k ≤ N} fₖ (S - 1)ᵏ S^{N-k}`. At the resolvent
`S = (1 - L)⁻¹` of a bounded `L` it is `f(L) Sᴺ` (`1 - S⁻¹ = L`, `resolventEval_eq_mul_aeval`);
for an unbounded `A` it gives `r(τ A)` as `P(S) Q(S)⁻¹` with `S = (1 - τ A)⁻¹` bounded
(`RationalScheme.step_eq_resolventEval`). -/
def resolventEval (N : ℕ) (f : R[X]) (S : A) : A :=
  ∑ k ∈ range (N + 1), f.coeff k • ((S - 1) ^ k * S ^ (N - k))

/-- **The Cayley transform of polynomials at `2 S - 1`**: `f̃(2 S - 1) = 2ᴺ (sᴺ f(1 - 1/s))(S)`,
from `w - 1 = 2 (s - 1)` and `w + 1 = 2 s` at `w = 2 s - 1`. -/
theorem aeval_two_mul_sub_one_cayleyPoly (S : A) (N : ℕ) (f : R[X]) :
    aeval (2 * S - 1) (cayleyPoly N f) = 2 ^ N * resolventEval N f S := by
  simp only [cayleyPoly, resolventEval, map_sum, map_mul, map_pow, map_sub, map_add, aeval_X,
    aeval_C, map_one, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have e1 : 2 * S - 1 - 1 = 2 * (S - 1) := by noncomm_ring
  have e2 : 2 * S - 1 + 1 = 2 * S := by noncomm_ring
  have h2 : (2 : A) = algebraMap R A 2 := (map_ofNat _ 2).symm
  rw [e1, e2, (Commute.ofNat_left 2 _).mul_pow, (Commute.ofNat_left 2 S).mul_pow, h2]
  simp only [← map_pow, ← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [← Nat.add_sub_cancel' hk', pow_add, Nat.add_sub_cancel_left]
  ring

/-- **At the resolvent**: if `S (1 - L) = 1` and `S L = L S`, then `sᴺ f(1 - 1/s)` at `S` is
`Sᴺ f(L)` for `deg f ≤ N` (`S - 1 = S L`). -/
theorem resolventEval_eq_mul_aeval {S L : A} (hS : S * (1 - L) = 1) (hc : Commute S L) {N : ℕ}
    {f : R[X]} (hf : f.natDegree ≤ N) : resolventEval N f S = S ^ N * aeval L f := by
  have hSL : S - 1 = S * L := by rw [← hS]; noncomm_ring
  rw [resolventEval, aeval_eq_sum_range' (Nat.lt_succ_of_le hf), mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [hSL, hc.mul_pow, mul_assoc, ← (hc.pow_pow (N - k) k).eq, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hk', mul_smul_comm]

/-- The scalar Cayley transform over `ℂ`: `q̃(w) = (w + 1)ᴺ q((w - 1)/(w + 1))` for `w ≠ -1`. -/
theorem eval_cayleyPoly {q : ℂ[X]} {N : ℕ} (hq : q.natDegree ≤ N) {w : ℂ} (hw : w ≠ -1) :
    (cayleyPoly N q).eval w = (w + 1) ^ N * q.eval ((w - 1) / (w + 1)) := by
  have hw1 : w + 1 ≠ 0 := fun h => hw (eq_neg_of_add_eq_zero_left h)
  have := aeval_cayleyPoly (R := ℂ) (S := (w + 1) / 2) (L := (w - 1) / (w + 1))
    (by field_simp; ring) (Commute.all _ _) hq
  rwa [show 2 * ((w + 1) / 2) - 1 = w by ring, show 2 * ((w + 1) / 2) = w + 1 by ring,
    coe_aeval_eq_eval, coe_aeval_eq_eval] at this

/-- `q̃(-1) = q_N (-2)ᴺ` over `ℂ`. -/
theorem eval_neg_one_cayleyPoly (q : ℂ[X]) (N : ℕ) :
    (cayleyPoly N q).eval (-1) = q.coeff N * (-2) ^ N := by
  simp only [cayleyPoly, eval_finsetSum, eval_mul, eval_pow, eval_sub, eval_add, eval_X, eval_C,
    eval_one, sum_range_succ, Nat.sub_self, pow_zero, mul_one, neg_add_cancel]
  rw [sum_eq_zero fun k hk => by
    rw [zero_pow (by have := mem_range.1 hk; omega), mul_zero], zero_add]
  norm_num

/-- `re ((w - 1)/(w + 1)) = (|w|² - 1)/|w + 1|²`. -/
theorem re_cayley_inv (w : ℂ) : ((w - 1) / (w + 1)).re = (‖w‖ ^ 2 - 1) / ‖w + 1‖ ^ 2 := by
  rw [Complex.div_re, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im,
    sub_zero, Complex.add_im, add_zero]
  ring

/-- If `q` has no zero for `re z ≤ 0`, then `q̃` (to degree `deg q`) has no zero in the closed
unit disc: `(w - 1)/(w + 1)` lies in the closed left half-plane, and `q̃(-1) = q_N (-2)ᴺ`. -/
theorem eval_cayleyPoly_ne_zero {q : ℂ[X]} (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) {w : ℂ}
    (hw : ‖w‖ ≤ 1) : (cayleyPoly q.natDegree q).eval w ≠ 0 := by
  have hq0 : q ≠ 0 := fun h => hq 0 (by simp) (by simp [h])
  rcases eq_or_ne w (-1) with rfl | hw1
  · rw [eval_neg_one_cayleyPoly, ← leadingCoeff]
    exact mul_ne_zero (leadingCoeff_ne_zero.2 hq0) (pow_ne_zero _ (by norm_num))
  have hw0 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  rw [eval_cayleyPoly le_rfl hw1]
  refine mul_ne_zero (pow_ne_zero _ hw0) (hq _ ?_)
  rw [re_cayley_inv]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg w]) (by positivity)

/-- On the unit circle (without `-1`), `p̃/q̃` is `p/q` on the imaginary axis, for
`deg p ≤ deg q`. -/
theorem eval_cayleyPoly_div {p q : ℂ[X]} (hpq : p.natDegree ≤ q.natDegree) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ -1) :
    (cayleyPoly q.natDegree p).eval ζ / (cayleyPoly q.natDegree q).eval ζ =
      p.eval (((ζ - 1) / (ζ + 1)).im * Complex.I) /
        q.eval (((ζ - 1) / (ζ + 1)).im * Complex.I) := by
  have hζ0 : ζ + 1 ≠ 0 := fun h => hζ1 (eq_neg_of_add_eq_zero_left h)
  have hre : ((ζ - 1) / (ζ + 1)).re = 0 := by rw [re_cayley_inv, hζ]; simp
  have e : ((ζ - 1) / (ζ + 1)).im * Complex.I = (ζ - 1) / (ζ + 1) := by
    conv_rhs => rw [← Complex.re_add_im ((ζ - 1) / (ζ + 1)), hre]
    simp
  rw [e, eval_cayleyPoly hpq hζ1, eval_cayleyPoly le_rfl hζ1,
    mul_div_mul_left _ _ (pow_ne_zero _ hζ0)]

/-- **A complex rational function `p/q` with `deg p ≤ deg q` is bounded on every closed set on
which `q` has no zero**: `p = O(q)` at infinity, and the rest of the set is compact. -/
theorem exists_norm_div_le_of_isClosed {p q : ℂ[X]} (hpq : p.natDegree ≤ q.natDegree)
    {F : Set ℂ} (hF : IsClosed F) (hq : ∀ z ∈ F, q.eval z ≠ 0) :
    ∃ C, ∀ z ∈ F, ‖p.eval z / q.eval z‖ ≤ C := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, fun z _ => by simp⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · exact ⟨0, fun z hz => (hq z hz (by simp)).elim⟩
  have hdeg : p.degree ≤ q.degree := by
    rw [degree_eq_natDegree hp, degree_eq_natDegree hq0]; exact_mod_cast hpq
  obtain ⟨C₁, hC₁⟩ := (isBigO_cobounded_of_degree_le hdeg).bound
  obtain ⟨S, hS, hSb⟩ := hC₁.exists_mem
  have hb : Bornology.IsBounded Sᶜ := by rw [Bornology.isBounded_def, compl_compl]; exact hS
  have hK : IsCompact (closure Sᶜ ∩ F) := Metric.isCompact_of_isClosed_isBounded
    (isClosed_closure.inter hF) (hb.closure.subset Set.inter_subset_left)
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn (f := fun z => p.eval z / q.eval z)
    ((p.continuous.continuousOn).div q.continuous.continuousOn fun z hz => hq z hz.2)
  refine ⟨max C₁ C₂, fun z hz => ?_⟩
  by_cases hzS : z ∈ S
  · have h := hSb z hzS
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 (hq z hz))]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact (hC₂ z ⟨subset_closure hzS, hz⟩).trans (le_max_right _ _)

/-- **A complex rational function `p/q` with `deg p ≤ deg q` and no pole on the closed left
half-plane is bounded on the imaginary axis** (`exists_norm_div_le_of_isClosed`). -/
theorem bddAbove_norm_div_imaginary {p q : ℂ[X]} (hpq : p.natDegree ≤ q.natDegree)
    (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) :
    BddAbove (Set.range fun y : ℝ => ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖) := by
  obtain ⟨C, hC⟩ := exists_norm_div_le_of_isClosed hpq (F := {z : ℂ | z.re ≤ 0})
    (isClosed_le Complex.continuous_re continuous_const) hq
  exact ⟨C, by rintro _ ⟨y, rfl⟩; exact hC _ (by simp)⟩

/-- A complex rational function bounded on the imaginary axis is bounded at infinity:
`deg p ≤ deg q` (`Polynomial.natDegree_le_of_norm_div_le` along `y ↦ iy`). -/
theorem natDegree_le_of_norm_div_imaginary_le {p q : ℂ[X]}
    (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) {C : ℝ}
    (hC : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ C) :
    p.natDegree ≤ q.natDegree := by
  have hl : Filter.Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) Filter.atTop
      (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    simpa using Filter.tendsto_abs_atTop_atTop
  exact Polynomial.natDegree_le_of_norm_div_le hl (C := C)
    (Filter.eventually_map.2 (.of_forall fun y => hq _ (by simp)))
    (Filter.eventually_map.2 (.of_forall hC))

end CayleyPoly

/-! ### Rational schemes -/

/-- A **rational scheme**: a real rational function `r = n/d`, bounded at infinity
(`deg n ≤ deg d`), whose denominator `d` has no zero in the closed left half-plane.
[HairerWanner1996], §IV.3 -/
@[ext] structure RationalScheme where
  /-- the numerator -/
  num : ℝ[X]
  /-- the denominator -/
  den : ℝ[X]
  natDegree_num_le : num.natDegree ≤ den.natDegree
  aeval_den_ne_zero : ∀ z : ℂ, z.re ≤ 0 → aeval z den ≠ 0

/-- The Taylor polynomial `Tₚ = ∑_{j ≤ p} Xʲ/j!` of the exponential. -/
def expTaylor (p : ℕ) : ℝ[X] := ∑ j ∈ range (p + 1), C (1 / (j.factorial : ℝ)) * X ^ j

/-- **Order from the asymptotics, complex coefficients**: if `q(0) ≠ 0` and
`p(z)/q(z) - e^z = O(z^{m+1})` at `0`, then `X^{m+1}` divides `p - q Tₘ`
(`p - q Tₘ = q (p/q - e^z) + q (e^z - Tₘ)`, `Polynomial.X_pow_dvd_of_isBigO`). [HairerWanner1996],
§IV.3 -/
theorem X_pow_dvd_sub_mul_expTaylor {p q : ℂ[X]} (hq : q.eval 0 ≠ 0) {m : ℕ}
    (h : (fun z : ℂ => p.eval z / q.eval z - Complex.exp z) =O[𝓝 0] fun z => z ^ (m + 1)) :
    X ^ (m + 1) ∣ p - q * (expTaylor m).map (algebraMap ℝ ℂ) := by
  have hd : Filter.Tendsto (fun z : ℂ => q.eval z) (𝓝 0) (𝓝 (q.eval 0)) :=
    q.continuous.tendsto 0
  have hd0 : ∀ᶠ z : ℂ in 𝓝 0, q.eval z ≠ 0 := hd.eventually_ne hq
  have hexp : (fun z : ℂ => Complex.exp z - ((expTaylor m).map (algebraMap ℝ ℂ)).eval z) =O[𝓝 0]
      fun z => z ^ (m + 1) := by
    refine IsBigO.of_bound ((m + 1).succ * ((m + 1).factorial * (m + 1 : ℕ) : ℝ)⁻¹) ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with z hz
    rw [mem_closedBall_zero_iff] at hz
    have e : ((expTaylor m).map (algebraMap ℝ ℂ)).eval z =
        ∑ j ∈ range (m + 1), z ^ j / j.factorial := by
      simp [expTaylor, div_eq_inv_mul]
    rw [e, norm_pow]
    exact (Complex.exp_bound hz (Nat.succ_pos m)).trans_eq (mul_comm _ _)
  have hsum := (hd.isBigO_one ℂ).mul h |>.add ((hd.isBigO_one ℂ).mul hexp)
  simp only [one_mul] at hsum
  refine X_pow_dvd_of_isBigO (hsum.congr' ?_ (by simp))
  filter_upwards [hd0] with z hz
  simp only [eval_sub, eval_mul]
  field_simp
  ring

namespace RationalScheme

variable (r : RationalScheme)

/-- The value `r(z) = n(z)/d(z)`. -/
def eval (z : ℂ) : ℂ := aeval z r.num / aeval z r.den

/-- **A-stability**: `|r(iy)| ≤ 1` on the imaginary axis (with no poles in the closed left
half-plane, the usual condition on `re z ≤ 0` by the maximum principle). [HairerWanner1996],
§IV.3 -/
def IsAStable : Prop := ∀ y : ℝ, ‖r.eval (y * Complex.I)‖ ≤ 1

/-- **L-stability**: A-stable with `r(∞) = 0`, i.e. `deg n < deg d`. [HairerWanner1996], §IV.3 -/
def IsLStable : Prop := r.IsAStable ∧ r.num.degree < r.den.degree

/-- **Strong A-stability**: A-stable with `|r(∞)| < 1` (`|n_N| < |d_N|`, `N = deg d`); every
L-stable scheme is strongly A-stable. [HairerWanner1996], §IV.3 -/
def IsStronglyAStable : Prop :=
  r.IsAStable ∧ |r.num.coeff r.den.natDegree| < |r.den.leadingCoeff|

/-- The supremum `sup_{y ∈ ℝ} |r(iy)|` (finite, `bddAbove`). -/
def supNorm : ℝ := ⨆ y : ℝ, ‖r.eval (y * Complex.I)‖

/-- **Order `p`**: `r(z) - e^z = O(z^{p+1})`, i.e. `X^{p+1} ∣ n - d Tₚ`. [HairerWanner1996],
§IV.3 -/
def HasOrder (p : ℕ) : Prop := X ^ (p + 1) ∣ r.num - r.den * expTaylor p

/-- The Cayley transform `ñ` of the numerator, to the degree of the denominator. -/
def cnum : ℝ[X] := cayleyPoly r.den.natDegree r.num

/-- The Cayley transform `d̃` of the denominator. -/
def cden : ℝ[X] := cayleyPoly r.den.natDegree r.den

theorem den_ne_zero : r.den ≠ 0 := fun h => r.aeval_den_ne_zero 0 (by simp) (by simp [h])

/-- L-stable schemes are strongly A-stable (`r(∞) = 0`). -/
theorem IsLStable.isStronglyAStable {r : RationalScheme} (hr : r.IsLStable) :
    r.IsStronglyAStable := by
  refine ⟨hr.1, ?_⟩
  rw [coeff_eq_zero_of_degree_lt (hr.2.trans_eq (degree_eq_natDegree r.den_ne_zero)), abs_zero]
  exact abs_pos.2 (leadingCoeff_ne_zero.2 r.den_ne_zero)

/-- `d̃` has no zero in the closed unit disc. -/
theorem aeval_cden_ne_zero {w : ℂ} (hw : ‖w‖ ≤ 1) : aeval w r.cden ≠ 0 := by
  rcases eq_or_ne w (-1) with rfl | hw1
  · rw [cden, aeval_neg_one_cayleyPoly, ← leadingCoeff]
    exact mul_ne_zero (by exact_mod_cast leadingCoeff_ne_zero.2 r.den_ne_zero)
      (pow_ne_zero _ (by norm_num))
  have hw0 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  rw [cden, aeval_cayleyPoly_complex le_rfl hw1]
  refine mul_ne_zero (pow_ne_zero _ hw0) (r.aeval_den_ne_zero _ ?_)
  rw [re_cayley_inv]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg w]) (by positivity)

/-- On the unit circle (without `-1`), `ñ/d̃` is `r` on the imaginary axis. -/
theorem eval_cayley {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ -1) :
    aeval ζ r.cnum / aeval ζ r.cden = r.eval (((ζ - 1) / (ζ + 1)).im * Complex.I) := by
  have hζ0 : ζ + 1 ≠ 0 := fun h => hζ1 (eq_neg_of_add_eq_zero_left h)
  have hre : ((ζ - 1) / (ζ + 1)).re = 0 := by rw [re_cayley_inv, hζ]; simp
  have e : ((ζ - 1) / (ζ + 1)).im * Complex.I = (ζ - 1) / (ζ + 1) := by
    conv_rhs => rw [← Complex.re_add_im ((ζ - 1) / (ζ + 1)), hre]
    simp
  rw [e, cnum, cden, aeval_cayleyPoly_complex r.natDegree_num_le hζ1,
    aeval_cayleyPoly_complex le_rfl hζ1, mul_div_mul_left _ _ (pow_ne_zero _ hζ0), eval]

/-- `r` is bounded on the imaginary axis (`bddAbove_norm_div_imaginary`). -/
theorem bddAbove : BddAbove (Set.range fun y : ℝ => ‖r.eval (y * Complex.I)‖) := by
  simpa only [eval, eval_map_algebraMap] using bddAbove_norm_div_imaginary
    (p := r.num.map (algebraMap ℝ ℂ)) (q := r.den.map (algebraMap ℝ ℂ))
    (by simpa only [natDegree_map] using r.natDegree_num_le)
    (fun z hz => by rw [eval_map_algebraMap]; exact r.aeval_den_ne_zero z hz)

/-- **A pole-free strip**: `r` has no pole on `re z ≤ c₀` for some `0 < c₀ ≤ 1/2` (the poles are
finitely many, in `re z > 0`). -/
theorem exists_den_ne_zero :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 2 ∧ ∀ z : ℂ, z.re ≤ c₀ → aeval z r.den ≠ 0 := by
  set q := r.den.map (algebraMap ℝ ℂ)
  have hq0 : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).2 r.den_ne_zero
  set s := q.roots.toFinset
  have hpos : ∀ ζ ∈ s, 0 < ζ.re := fun ζ hζ => by
    by_contra h
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap] at hζ
    exact r.aeval_den_ne_zero ζ (not_lt.1 h) hζ
  obtain ⟨c, hc, hcs⟩ : ∃ c : ℝ, 0 < c ∧ ∀ ζ ∈ s, c < ζ.re := by
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact ⟨1, one_pos, fun ζ hζ => by simp [hs] at hζ⟩
    obtain ⟨ζ₀, h0, hmin⟩ := s.exists_min_image (fun ζ => ζ.re) hs
    exact ⟨ζ₀.re / 2, by linarith [hpos ζ₀ h0], fun ζ hζ => by linarith [hmin ζ hζ, hpos ζ₀ h0]⟩
  refine ⟨min c (1 / 2), lt_min hc (by norm_num), min_le_right _ _, fun z hz h => ?_⟩
  have hzs : z ∈ s := by
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap]; exact h
  linarith [hcs z hzs, min_le_left c (1 / 2)]

theorem norm_eval_le_supNorm (y : ℝ) : ‖r.eval (y * Complex.I)‖ ≤ r.supNorm :=
  le_ciSup r.bddAbove y

theorem supNorm_nonneg : 0 ≤ r.supNorm := (norm_nonneg _).trans (r.norm_eval_le_supNorm 0)

theorem isAStable_iff : r.IsAStable ↔ r.supNorm ≤ 1 :=
  ⟨fun h => ciSup_le h, fun h y => (r.norm_eval_le_supNorm y).trans h⟩

/-! ### Rational functions bounded on the imaginary axis -/

/-- **The scheme `p/q` of a real rational function bounded on the imaginary axis**: `q` has no
zero for `re z ≤ 0` and `|p(iy)/q(iy)| ≤ C` for `y ∈ ℝ` (for `C = 1`, A-stability); then
`deg p ≤ deg q` (`Polynomial.natDegree_le_of_norm_div_le` along `y ↦ iy`). -/
def ofBounded (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {C : ℝ}
    (hC : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ C) :
    RationalScheme where
  num := p
  den := q
  natDegree_num_le := by
    simpa only [natDegree_map] using natDegree_le_of_norm_div_imaginary_le
      (p := p.map (algebraMap ℝ ℂ)) (q := q.map (algebraMap ℝ ℂ)) (C := C)
      (fun z hz => by rw [eval_map_algebraMap]; exact hq z hz)
      (fun y => by rw [eval_map_algebraMap, eval_map_algebraMap]; exact hC y)
  aeval_den_ne_zero := hq

theorem supNorm_ofBounded_le {p q : ℝ[X]} (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {C : ℝ}
    (hC : ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ C) :
    (ofBounded p q hq hC).supNorm ≤ C :=
  ciSup_le hC

/-! ### The operators `r(τ A)` -/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **`r(L) = n(L) d(L)⁻¹`** for a bounded operator `L`. -/
def apply (L : V →L[𝕜] V) : V →L[𝕜] V :=
  aeval L (r.num.map (algebraMap ℝ 𝕜)) * Ring.inverse (aeval L (r.den.map (algebraMap ℝ 𝕜)))

/-- **`r(τ A) = ñ(C) d̃(C)⁻¹`** for an m-dissipative, possibly unbounded, `A`, with the Cayley
transform `C = (1 + τ A)(1 - τ A)⁻¹`. -/
def step (A : V →ₗ.[𝕜] V) (τ : ℝ) : V →L[𝕜] V :=
  aeval (cayley A τ) (r.cnum.map (algebraMap ℝ 𝕜)) *
    Ring.inverse (aeval (cayley A τ) (r.cden.map (algebraMap ℝ 𝕜)))

variable [CompleteSpace V]

/-- **Von Neumann's inequality in the half-plane**: for every m-dissipative `A` and `τ > 0`,
`d̃(C)` is invertible and `‖r(τ A)‖ ≤ sup_y |r(iy)|`, uniformly in `A`. [VonNeumann1951];
[HairerWanner1996], §IV.11 -/
theorem norm_step_le {A : V →ₗ.[𝕜] V} (hA : A.IsMDissipative) {τ : ℝ} (hτ : 0 < τ) :
    IsUnit (aeval (cayley A τ) (r.cden.map (algebraMap ℝ 𝕜))) ∧ ‖r.step A τ‖ ≤ r.supNorm := by
  have hC : ‖cayley A τ‖ ≤ 1 := by
    rw [show τ = 2 * τ / 2 by ring, cayley_half_eq_thetaStep]
    exact norm_thetaStep_le hA (by rw [RCLike.ofReal_re]) (by linarith)
  exact ContinuousLinearMap.norm_aeval_map_mul_inverse_le hC (fun w hw => r.aeval_cden_ne_zero hw)
    fun ζ hζ hζ1 => by rw [r.eval_cayley hζ hζ1]; exact r.norm_eval_le_supNorm _

/-- An A-stable scheme is a contraction: `‖r(τ A)‖ ≤ 1`. -/
theorem norm_step_le_one {A : V →ₗ.[𝕜] V} (hA : A.IsMDissipative) {τ : ℝ} (hτ : 0 < τ)
    (hr : r.IsAStable) : ‖r.step A τ‖ ≤ 1 :=
  (r.norm_step_le hA hτ).2.trans (r.isAStable_iff.1 hr)

/-- `U n (U d)⁻¹ = n d⁻¹` for a unit `U` commuting with `n` and `d`. -/
theorem _root_.Ring.mul_inverse_mul_of_commute {M : Type*} [MonoidWithZero M] {U n d : M}
    (hU : IsUnit U) (hn : Commute U n) (hd : Commute U d) :
    U * n * Ring.inverse (U * d) = n * Ring.inverse d := by
  rw [Ring.mul_inverse_rev' hd, hn.eq, mul_assoc, ← mul_assoc U, hd.ringInverse_right.eq,
    mul_assoc, Ring.mul_inverse_cancel _ hU, mul_one]

/-- For bounded dissipative `L`, the resolvent `S = (1 - τ L)⁻¹` (`τ > 0`) inverts `1 - τ L` on
both sides, commutes with `L`, and `C = 2 S - 1`. -/
private theorem exists_cayley_eq {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {τ : ℝ}
    (hτ : 0 < τ) : ∃ S : V →L[𝕜] V, S * (1 - (τ : 𝕜) • L) = 1 ∧ (1 - (τ : 𝕜) • L) * S = 1 ∧
      Commute S L ∧ cayley ((L : V →ₗ[𝕜] V).toPMap ⊤) τ = 2 * S - 1 ∧
      S = (τ : 𝕜)⁻¹ • resolvent ((L : V →ₗ[𝕜] V).toPMap ⊤) (τ : 𝕜)⁻¹ := by
  have hA := L.isMDissipative_toPMap_top hL
  set μ : 𝕜 := (τ : 𝕜)⁻¹
  set R := resolvent ((L : V →ₗ[𝕜] V).toPMap ⊤) μ
  have hR : IsResolvent ((L : V →ₗ[𝕜] V).toPMap ⊤) μ R := by
    simp only [μ, R, ← RCLike.ofReal_inv]; exact hA.isResolvent (inv_pos.2 hτ)
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ.ne'
  have h1 : ∀ y, μ • R y - L (R y) = y := hR.sub_apply
  have h2 : ∀ y, R (μ • y - L y) = y := fun y => hR.apply_sub ⟨y, trivial⟩
  have hRL : ∀ y, R (L y) = L (R y) := fun y => by
    have := h2 y
    rw [map_sub, map_smul] at this
    exact sub_right_injective (this.trans (h1 y).symm)
  refine ⟨μ • R, ?_, ?_, ?_, ?_, rfl⟩
  · ext y
    change μ • R (y - (τ : 𝕜) • L y) = y
    have e : y - (τ : 𝕜) • L y = (τ : 𝕜) • (μ • y - L y) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hτ', one_smul]
    rw [e, map_smul, h2, smul_smul, inv_mul_cancel₀ hτ', one_smul]
  · ext y
    change μ • R y - (τ : 𝕜) • L (μ • R y) = y
    rw [map_smul, smul_smul, mul_inv_cancel₀ hτ', one_smul]
    exact h1 y
  · ext y
    change μ • R (L y) = L (μ • R y)
    rw [hRL, map_smul]
  · show (2 * μ) • R - 1 = 2 * (μ • R) - 1
    rw [two_mul (μ • R), two_mul μ, add_smul]

/-- **The Cayley form of a bounded `L`**: for `deg f, deg g ≤ N` and the Cayley transform `C` of
`L` (`τ > 0`), `f̃(C) g̃(C)⁻¹ = f(τ L) g(τ L)⁻¹` with `f̃ = cayleyPoly N f`, since
`f̃(C) = (2 S)ᴺ f(τ L)` at `S = (1 - τ L)⁻¹` (`aeval_cayleyPoly`). -/
theorem _root_.Feec.TimeStepping.aeval_cayley_mul_inverse {L : V →L[𝕜] V}
    (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {τ : ℝ} (hτ : 0 < τ) {N : ℕ} {f g : 𝕜[X]}
    (hf : f.natDegree ≤ N) (hg : g.natDegree ≤ N) :
    aeval (cayley ((L : V →ₗ[𝕜] V).toPMap ⊤) τ) (cayleyPoly N f) *
        Ring.inverse (aeval (cayley ((L : V →ₗ[𝕜] V).toPMap ⊤) τ) (cayleyPoly N g)) =
      aeval ((τ : 𝕜) • L) f * Ring.inverse (aeval ((τ : 𝕜) • L) g) := by
  obtain ⟨S, hS, hS', hSL, hC, -⟩ := exists_cayley_eq hL hτ
  have hSτ : Commute S ((τ : 𝕜) • L) := hSL.smul_right _
  have h2 : IsUnit (2 : V →L[𝕜] V) := by
    have := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : 𝕜) ≠ 0)).map (algebraMap 𝕜 (V →L[𝕜] V))
    rwa [map_ofNat] at this
  have hU : IsUnit ((2 * S) ^ N) := (h2.mul ⟨⟨S, 1 - (τ : 𝕜) • L, hS, hS'⟩, rfl⟩).pow _
  have hc : Commute ((2 * S) ^ N) ((τ : 𝕜) • L) :=
    ((Commute.ofNat_left 2 _).mul_left hSτ).pow_left _
  rw [hC, aeval_cayleyPoly hS hSτ hf, aeval_cayleyPoly hS hSτ hg]
  exact Ring.mul_inverse_mul_of_commute hU (commute_aeval hc.symm _).symm
    (commute_aeval hc.symm _).symm

/-- **For bounded `L`, `r(τ A)` is `n(τ L) d(τ L)⁻¹`**. -/
theorem step_toPMap {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {τ : ℝ} (hτ : 0 < τ) :
    r.step ((L : V →ₗ[𝕜] V).toPMap ⊤) τ = r.apply ((τ : 𝕜) • L) := by
  rw [step, apply, cnum, cden, cayleyPoly_map, cayleyPoly_map]
  exact aeval_cayley_mul_inverse hL hτ ((natDegree_map_le).trans r.natDegree_num_le)
    natDegree_map_le

omit [CompleteSpace V] in
theorem dissipative_smul {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {τ : ℝ}
    (hτ : 0 ≤ τ) (x : V) : RCLike.re ⟪((τ : 𝕜) • L) x, x⟫_𝕜 ≤ 0 := by
  rw [smul_apply, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
  exact mul_nonpos_of_nonneg_of_nonpos hτ (hL x)

theorem apply_eq_step {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) :
    r.apply L = r.step ((L : V →ₗ[𝕜] V).toPMap ⊤) 1 := by
  rw [r.step_toPMap hL one_pos]; simp

/-- **`d(L)` is invertible** for every bounded dissipative `L`. -/
theorem isUnit_aeval_den {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) :
    IsUnit (aeval L (r.den.map (algebraMap ℝ 𝕜))) := by
  obtain ⟨S, hS, -, hSL, hC, -⟩ := exists_cayley_eq hL one_pos
  simp only [RCLike.ofReal_one, one_smul] at hS
  have h := (r.norm_step_le (L.isMDissipative_toPMap_top hL) one_pos).1
  rw [hC, cden, cayleyPoly_map, aeval_cayleyPoly hS hSL natDegree_map_le] at h
  have hc : Commute ((2 * S) ^ r.den.natDegree) L :=
    ((Commute.ofNat_left 2 L).mul_left hSL).pow_left _
  exact ((commute_aeval hc.symm _).symm.isUnit_mul_iff.1 h).2

/-- **Von Neumann's inequality for bounded dissipative `L`**: `‖r(L)‖ ≤ sup_y |r(iy)|`. -/
theorem norm_apply_le {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) :
    ‖r.apply L‖ ≤ r.supNorm := by
  rw [r.apply_eq_step hL]; exact (r.norm_step_le (L.isMDissipative_toPMap_top hL) one_pos).2

/-- An A-stable scheme of a bounded dissipative `L` is a contraction. -/
theorem norm_apply_le_one {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0)
    (hr : r.IsAStable) : ‖r.apply L‖ ≤ 1 :=
  (r.norm_apply_le hL).trans (r.isAStable_iff.1 hr)

/-! ### `r(τ A)` through the resolvent -/

omit [CompleteSpace V] in
/-- **The resolvent form is the Cayley form**: with `S = (1 - τ A)⁻¹ = τ⁻¹ R(τ⁻¹)`,
`P(S) Q(S)⁻¹ = f̃(C) g̃(C)⁻¹` for `P(s) = sᴺ f(1 - 1/s)`, `Q(s) = sᴺ g(1 - 1/s)`
(`resolventEval`), `f̃ = cayleyPoly N f` and the Cayley transform `C = 2 S - 1`
(`aeval_two_mul_sub_one_cayleyPoly`). -/
theorem _root_.Feec.TimeStepping.resolventEval_mul_inverse_eq (A : V →ₗ.[𝕜] V) (τ : ℝ) (N : ℕ)
    (f g : 𝕜[X]) :
    resolventEval N f ((τ : 𝕜)⁻¹ • resolvent A (τ : 𝕜)⁻¹) *
        Ring.inverse (resolventEval N g ((τ : 𝕜)⁻¹ • resolvent A (τ : 𝕜)⁻¹)) =
      aeval (cayley A τ) (cayleyPoly N f) * Ring.inverse (aeval (cayley A τ) (cayleyPoly N g)) := by
  have h2 : IsUnit (2 : V →L[𝕜] V) := by
    have := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : 𝕜) ≠ 0)).map (algebraMap 𝕜 (V →L[𝕜] V))
    rwa [map_ofNat] at this
  have hc : ∀ x : V →L[𝕜] V, Commute ((2 : V →L[𝕜] V) ^ N) x := fun x =>
    (Commute.ofNat_left 2 x).pow_left _
  rw [cayley_eq_two_mul_sub_one, aeval_two_mul_sub_one_cayleyPoly,
    aeval_two_mul_sub_one_cayleyPoly]
  exact (Ring.mul_inverse_mul_of_commute (h2.pow _) (hc _) (hc _)).symm

omit [CompleteSpace V] in
/-- **`r(τ A)` through the resolvent**: with `S = (1 - τ A)⁻¹ = τ⁻¹ R(τ⁻¹)` and `N = deg d`,
`r(τ A) = P(S) Q(S)⁻¹` for `P(s) = sᴺ n(1 - 1/s)` and `Q(s) = sᴺ d(1 - 1/s)` (`resolventEval`),
since the Cayley transform is `C = 2 S - 1` (`aeval_two_mul_sub_one_cayleyPoly`). -/
theorem step_eq_resolventEval (A : V →ₗ.[𝕜] V) (τ : ℝ) :
    r.step A τ =
      resolventEval r.den.natDegree (r.num.map (algebraMap ℝ 𝕜))
          ((τ : 𝕜)⁻¹ • resolvent A (τ : 𝕜)⁻¹) *
        Ring.inverse (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜))
          ((τ : 𝕜)⁻¹ • resolvent A (τ : 𝕜)⁻¹)) := by
  rw [resolventEval_mul_inverse_eq, step, cnum, cden, cayleyPoly_map, cayleyPoly_map]

/-- `Q(S) = sᴺ d(1 - 1/s)` at `S = (1 - τ A)⁻¹` is invertible, for m-dissipative `A` and
`τ > 0`. -/
theorem isUnit_resolventEval_den {A : V →ₗ.[𝕜] V} (hA : A.IsMDissipative) {τ : ℝ} (hτ : 0 < τ) :
    IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜))
      ((τ : 𝕜)⁻¹ • resolvent A (τ : 𝕜)⁻¹)) := by
  have h := (r.norm_step_le hA hτ).1
  rw [cayley_eq_two_mul_sub_one, cden, cayleyPoly_map, aeval_two_mul_sub_one_cayleyPoly] at h
  exact (((Commute.ofNat_left 2 _).pow_left _).isUnit_mul_iff.1 h).2

/-! ### Consistency -/

theorem natDegree_expTaylor_le (p : ℕ) : (expTaylor p).natDegree ≤ p :=
  natDegree_sum_le_of_forall_le _ _ fun _ hj =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (mem_range.1 hj))

/-- The **remainder** `ρ = (r - Tₚ)/X^{p+1}`, with numerator `(n - d Tₚ) /ₘ X^{p+1}` and the same
denominator. -/
def remainder (p : ℕ) : RationalScheme where
  num := (r.num - r.den * expTaylor p) /ₘ X ^ (p + 1)
  den := r.den
  natDegree_num_le := by
    rw [natDegree_divByMonic _ (monic_X_pow _), natDegree_X_pow]
    have h1 := natDegree_sub_le r.num (r.den * expTaylor p)
    have h2 := natDegree_mul_le (p := r.den) (q := expTaylor p)
    have h3 := natDegree_expTaylor_le p
    have h4 := r.natDegree_num_le
    omega
  aeval_den_ne_zero := r.aeval_den_ne_zero

theorem num_eq_add {p : ℕ} (hp : r.HasOrder p) :
    r.num = r.den * expTaylor p + X ^ (p + 1) * (r.remainder p).num := by
  have h := modByMonic_add_div (r.num - r.den * expTaylor p) (X ^ (p + 1))
  rw [(modByMonic_eq_zero_iff_dvd (monic_X_pow _)).2 hp, zero_add] at h
  simp only [remainder]; rw [h]; ring

omit [CompleteSpace V] in
/-- **Order from the asymptotics**: if `r(z) - e^z = O(z^{p+1})` at `0`, then `r` has order `p`
(`X_pow_dvd_sub_mul_expTaylor`). [HairerWanner1996], §IV.3 -/
theorem hasOrder_of_isBigO {p : ℕ}
    (h : (fun z : ℂ => r.eval z - Complex.exp z) =O[𝓝 0] fun z => z ^ (p + 1)) :
    r.HasOrder p := by
  have hG := X_pow_dvd_sub_mul_expTaylor (p := r.num.map (algebraMap ℝ ℂ))
    (q := r.den.map (algebraMap ℝ ℂ))
    (by rw [eval_map_algebraMap]; exact r.aeval_den_ne_zero 0 (by simp))
    (by simpa only [eval_map_algebraMap, RationalScheme.eval] using h)
  rw [HasOrder, X_pow_dvd_iff]
  intro d hd
  have := (X_pow_dvd_iff.1 hG) d hd
  rwa [← Polynomial.map_mul, ← Polynomial.map_sub, coeff_map, Complex.coe_algebraMap,
    Complex.ofReal_eq_zero] at this

/-- **Consistency from the expansion `p = q Tₘ + X^{m+1} ρ`**, over `𝕜`: for a bounded
dissipative `L` and `τ ≥ 0` with `q(τL)` invertible and `‖ρ(τL) q(τL)⁻¹‖ ≤ K₀`, the step
`p(τL) q(τL)⁻¹ = Tₘ(τL) + (τL)^{m+1} ρ(τL) q(τL)⁻¹` is consistent of order `m` with constant
`K₀ + 1/(m+1)!`. -/
theorem isConsistent_aeval_mul_inverse [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {τ : ℝ} (hτ : 0 ≤ τ) {m : ℕ}
    {p q ρ : 𝕜[X]} (h : p = q * (expTaylor m).map (algebraMap ℝ 𝕜) + X ^ (m + 1) * ρ)
    (hq : IsUnit (aeval ((τ : 𝕜) • L) q)) {K₀ : ℝ}
    (hρ : ‖aeval ((τ : 𝕜) • L) ρ * Ring.inverse (aeval ((τ : 𝕜) • L) q)‖ ≤ K₀) :
    IsConsistent L (aeval ((τ : 𝕜) • L) p * Ring.inverse (aeval ((τ : 𝕜) • L) q)) τ m
      (K₀ + 1 / (m + 1).factorial) := by
  set T := (expTaylor m).map (algebraMap ℝ 𝕜)
  have hτL : Commute ((τ : 𝕜) • L) L := (Commute.refl L).smul_left _
  have he : aeval ((τ : 𝕜) • L) p * Ring.inverse (aeval ((τ : 𝕜) • L) q) =
      aeval ((τ : 𝕜) • L) T + ((τ : 𝕜) • L) ^ (m + 1) *
        (aeval ((τ : 𝕜) • L) ρ * Ring.inverse (aeval ((τ : 𝕜) • L) q)) := by
    rw [h, map_add, map_mul, map_mul, map_pow, aeval_X, add_mul,
      ((Commute.all q T).map (aeval ((τ : 𝕜) • L))).eq, Ring.mul_inverse_cancel_right _ _ hq,
      mul_assoc]
  have hc : Commute (aeval ((τ : 𝕜) • L) ρ * Ring.inverse (aeval ((τ : 𝕜) • L) q))
      (L ^ (m + 1)) :=
    ((commute_aeval hτL ρ).mul_left
      (commute_aeval hτL q).symm.ringInverse_right.symm).pow_right _
  refine isConsistent_of_eq hL hτ hρ fun y => ?_
  rw [he, add_apply, smul_pow, smul_mul_assoc, smul_apply, ← mul_apply_eq_comp, hc.eq,
    mul_apply_eq_comp]
  congr 1
  · simp only [T, expTaylor, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow,
      map_X, map_sum, map_mul, aeval_C, map_pow, aeval_X, _root_.sum_apply]
    refine sum_congr rfl fun j _ => ?_
    rw [smul_pow, mul_smul_comm, ← Algebra.smul_def, smul_smul, smul_apply,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    congr 1
    simp [div_eq_inv_mul, mul_comm]
  · rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]; push_cast; rfl

/-- **Consistency of an order-`p` scheme**: `r(τ L)` is consistent of order `p` with every bounded
dissipative `L`, with the constant `sup_y |ρ(iy)| + 1/(p+1)!` (`ρ` the remainder), uniformly in
`L`. [BrennerThomee1979]; [HairerWanner1996], §IV.3 -/
theorem isConsistent [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {L : V →L[𝕜] V}
    (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsConsistent L (r.apply ((τ : 𝕜) • L)) τ p
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) := by
  have hτL := dissipative_smul hL hτ
  refine isConsistent_aeval_mul_inverse hL hτ ?_ (r.isUnit_aeval_den hτL)
    ((r.remainder p).norm_apply_le hτL)
  conv_lhs => rw [r.num_eq_add hp]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X]

/-- **The Brenner–Thomée error of an A-stable scheme of order `p`**: at `t = n τ`,
`‖r(τ L)ⁿ y - e^{tL} y‖ ≤ K t τᵖ ‖L^{p+1} y‖` with `K = sup_y |ρ(iy)| + 1/(p+1)!`, for every
bounded dissipative `L`. [BrennerThomee1979] -/
theorem norm_apply_pow_sub_exp_le [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {L : V →L[𝕜] V}
    (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ}
    (hτ : 0 ≤ τ) (n : ℕ) (y : V) :
    ‖(r.apply ((τ : 𝕜) • L) ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      ((r.remainder p).supNorm + 1 / (p + 1).factorial) * (n * τ) * τ ^ p *
        ‖(L ^ (p + 1)) y‖ := by
  have := norm_pow_apply_sub_exp_le hL (M := 1) (n := n)
    (fun k _ => norm_pow_le_one (r.norm_apply_le_one (dissipative_smul hL hτ) hr) k) hτ
    (add_nonneg (r.remainder p).supNorm_nonneg (by positivity)) (r.isConsistent hL hp hτ) y
  simpa using this

/-! ### Discrete constraint propagation -/

omit [CompleteSpace V] in
/-- On an `L`-invariant subspace `K`, a polynomial in `L` acts as the polynomial in the part
`L_K` of `L` in `K`. -/
private theorem aeval_coe {L : V →L[𝕜] V} {K : Submodule 𝕜 V} (hLK : ∀ x ∈ K, L x ∈ K)
    (q : 𝕜[X]) (x : K) :
    aeval L q (x : V) = (aeval ((L.comp K.subtypeL).codRestrict K fun x => hLK x x.2) q x : K) := by
  set LK : K →L[𝕜] K := (L.comp K.subtypeL).codRestrict K fun x => hLK x x.2
  have hpow : ∀ j (x : K), (L ^ j) (x : V) = ((LK ^ j) x : K) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ', pow_succ']
      change L ((L ^ j) (x : V)) = (LK ((LK ^ j) x) : V)
      rw [ih]; rfl
  simp only [aeval_eq_sum_range, _root_.sum_apply, smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, hpow]

/-- **Discrete constraint propagation**: a closed subspace `K` with `L K ⊆ K` is kept by `r(L)`
for bounded dissipative `L` (the part of `L` in `K` is dissipative, so `d(L)` is invertible on
`K`). [QuennevilleBelair2015], Prop 4.18 -/
theorem apply_mem_of_mapsTo {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0)
    {K : Submodule 𝕜 V} (hKc : IsClosed (K : Set V)) (hLK : ∀ x ∈ K, L x ∈ K) {u : V}
    (hu : u ∈ K) : r.apply L u ∈ K := by
  have : CompleteSpace K := hKc.completeSpace_coe
  set LK : K →L[𝕜] K := (L.comp K.subtypeL).codRestrict K fun x => hLK x x.2
  have hLK' : ∀ x : K, RCLike.re ⟪LK x, x⟫_𝕜 ≤ 0 := fun x => by
    rw [Submodule.coe_inner]; exact hL x
  obtain ⟨w, hw⟩ := (r.isUnit_aeval_den hLK').exists_right_inv
  have hDv : aeval L (r.den.map (algebraMap ℝ 𝕜)) (w ⟨u, hu⟩ : V) = u := by
    rw [aeval_coe hLK, ← mul_apply_eq_comp, hw]; rfl
  have hinv : Ring.inverse (aeval L (r.den.map (algebraMap ℝ 𝕜))) u = w ⟨u, hu⟩ := by
    conv_lhs => rw [← hDv]
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ (r.isUnit_aeval_den hL),
      one_apply_eq_self]
  rw [apply, mul_apply_eq_comp, hinv, aeval_coe hLK]
  exact Submodule.coe_mem _

/-! ### Symmetric schemes -/

/-- A **symmetric** scheme, `n(z) = d(-z)`, so `r(-z) = 1/r(z)` (the diagonal Padé
approximations, Gauss methods). [HairerWanner1996], §IV.3, §IV.5 -/
def IsSymmetric : Prop := r.num = r.den.comp (-X)

/-- A symmetric scheme has `|r(iy)| = 1`. -/
theorem IsSymmetric.norm_eval {r : RationalScheme} (h : r.IsSymmetric) (y : ℝ) :
    ‖r.eval (y * Complex.I)‖ = 1 := by
  have hd : aeval ((y : ℂ) * Complex.I) r.den ≠ 0 := r.aeval_den_ne_zero _ (by simp)
  rw [eval, h, aeval_comp, map_neg, aeval_X,
    show -((y : ℂ) * Complex.I) = conj ((y : ℂ) * Complex.I) by simp, aeval_conj, norm_div,
    Complex.norm_conj, div_self (norm_ne_zero_iff.2 hd)]

theorem IsSymmetric.isAStable {r : RationalScheme} (h : r.IsSymmetric) : r.IsAStable :=
  fun y => (h.norm_eval y).le

/-- **Symmetric schemes have `|r(∞)| = 1`**: `n(z) = d(-z)` gives `n_N = (-1)ᴺ d_N`. -/
theorem IsSymmetric.abs_coeff_num {r : RationalScheme} (h : r.IsSymmetric) :
    |r.num.coeff r.den.natDegree| = |r.den.leadingCoeff| := by
  rw [h, show (-X : ℝ[X]) = C (-1) * X by simp, comp_C_mul_X_coeff, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, mul_one, leadingCoeff]

/-- Symmetric schemes (the Gauss methods, Crank–Nicolson) are not strongly A-stable. -/
theorem IsSymmetric.not_isStronglyAStable {r : RationalScheme} (h : r.IsSymmetric) :
    ¬ r.IsStronglyAStable := fun h' => (lt_irrefl _) (h.abs_coeff_num ▸ h'.2)

/-- **A symmetric scheme of a skew operator is an isometry**: `‖r(L) x‖ = ‖x‖` when
`re ⟪L x, x⟫ = 0`. -/
theorem IsSymmetric.norm_apply_apply {r : RationalScheme} (h : r.IsSymmetric) {L : V →L[𝕜] V}
    (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 = 0) (x : V) : ‖r.apply L x‖ = ‖x‖ := by
  have h1 : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0 := fun x => (hL x).le
  have h2 : ∀ x, RCLike.re ⟪(-L) x, x⟫_𝕜 ≤ 0 := fun x => by simp [inner_neg_left, hL x]
  have hcomp : ∀ q : ℝ[X], aeval (-L) ((q.comp (-X)).map (algebraMap ℝ 𝕜)) =
      aeval L (q.map (algebraMap ℝ 𝕜)) := fun q => by
    rw [Polynomial.map_comp, aeval_comp]; simp
  have hden : r.den = r.num.comp (-X) := by rw [h, comp_assoc]; simp
  have hn : IsUnit (aeval L (r.num.map (algebraMap ℝ 𝕜))) := by
    have := r.isUnit_aeval_den h2; rwa [hden, hcomp] at this
  have e1 : aeval (-L) (r.num.map (algebraMap ℝ 𝕜)) = aeval L (r.den.map (algebraMap ℝ 𝕜)) := by
    rw [h, hcomp]
  have e2 : aeval (-L) (r.den.map (algebraMap ℝ 𝕜)) = aeval L (r.num.map (algebraMap ℝ 𝕜)) := by
    rw [hden, hcomp]
  have hinv : r.apply (-L) * r.apply L = 1 := by
    rw [apply, apply, e1, e2, mul_assoc, ← mul_assoc (Ring.inverse _),
      Ring.inverse_mul_cancel _ hn, one_mul, Ring.mul_inverse_cancel _ (r.isUnit_aeval_den h1)]
  refine le_antisymm (((r.apply L).le_of_opNorm_le (r.norm_apply_le_one h1 h.isAStable) x).trans_eq
    (one_mul _)) ?_
  calc ‖x‖ = ‖r.apply (-L) (r.apply L x)‖ := by
        rw [← mul_apply_eq_comp (r.apply (-L)) (r.apply L) x, hinv, one_apply_eq_self]
    _ ≤ 1 * ‖r.apply L x‖ := (r.apply (-L)).le_of_opNorm_le (r.norm_apply_le_one h2 h.isAStable) _
    _ = ‖r.apply L x‖ := one_mul _

/-! ### The θ-schemes -/

/-- `‖1 + a i y‖ ≤ ‖1 - b i y‖` from `a² ≤ b²`. -/
theorem norm_one_add_le {a b y : ℝ} (h : a ^ 2 ≤ b ^ 2) :
    ‖(1 : ℂ) + a * (y * Complex.I)‖ ≤ ‖(1 : ℂ) - b * (y * Complex.I)‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.one_im, Complex.mul_im, zero_add, Complex.sub_re, Complex.sub_im, zero_sub]
  nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) (sub_nonneg.2 h)]

/-- **The θ-scheme** `r_θ(z) = (1 + (1 - θ) z)/(1 - θ z)`, `θ > 0` (`θ = 1`: implicit Euler,
`θ = 1/2`: Crank–Nicolson, the implicit midpoint rule). [HairerWanner1996], §IV.3 -/
def theta (θ : ℝ) (hθ : 0 < θ) : RationalScheme where
  num := 1 + C (1 - θ) * X
  den := 1 - C θ * X
  natDegree_num_le := by
    have hd : (1 - C θ * X : ℝ[X]) = C (-θ) * X + C 1 := by rw [C_neg, C_1]; ring
    rw [hd, natDegree_linear (neg_ne_zero.2 hθ.ne')]
    exact (natDegree_add_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  aeval_den_ne_zero z hz h := by
    have := congrArg Complex.re h
    simp only [map_sub, map_one, map_mul, aeval_C, aeval_X, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.zero_re, Complex.coe_algebraMap, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at this
    nlinarith

/-- The θ-scheme is A-stable for `θ ≥ 1/2`. -/
theorem isAStable_theta {θ : ℝ} (hθ : 1 / 2 ≤ θ) : (theta θ (by linarith)).IsAStable := by
  intro y
  have hd := (theta θ (by linarith)).aeval_den_ne_zero (y * Complex.I) (by simp)
  simp only [eval, theta, map_add, map_one, map_mul, aeval_C, aeval_X, map_sub,
    Complex.coe_algebraMap] at hd ⊢
  rw [norm_div, div_le_one (norm_pos_iff.2 hd)]
  have := norm_one_add_le (a := 1 - θ) (b := θ) (y := y) (by nlinarith)
  push_cast at this
  exact this

/-- The θ-scheme has order `1`. -/
theorem hasOrder_theta {θ : ℝ} (hθ : 0 < θ) : (theta θ hθ).HasOrder 1 :=
  ⟨C θ, Polynomial.funext fun x => by
    simp [theta, expTaylor, sum_range_succ]; ring⟩

/-- Crank–Nicolson (`θ = 1/2`) has order `2`. -/
theorem hasOrder_theta_half : (theta (1 / 2) (by norm_num)).HasOrder 2 :=
  ⟨C (1 / 4), Polynomial.funext fun x => by
    simp [theta, expTaylor, sum_range_succ, Nat.factorial]; ring⟩

/-- Crank–Nicolson is symmetric. -/
theorem isSymmetric_theta_half : (theta (1 / 2) (by norm_num)).IsSymmetric :=
  Polynomial.funext fun x => by
    simp only [theta, eval_comp, eval_add, eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_neg]
    ring

/-- **The θ-schemes are rational schemes**: `r_θ(τ L) = thetaStep L θ τ`
(`Feec.TimeStepping.thetaStep`) for bounded dissipative `L`, `θ > 0` and `τ > 0`. -/
theorem apply_theta {L : V →L[𝕜] V} (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {θ : ℝ}
    (hθ : 0 < θ) {τ : ℝ} (hτ : 0 < τ) :
    (theta θ hθ).apply ((τ : 𝕜) • L) = thetaStep ((L : V →ₗ[𝕜] V).toPMap ⊤) θ τ := by
  obtain ⟨S, hS, hS', -, -, hSR⟩ := exists_cayley_eq hL (mul_pos hθ hτ)
  have hθ' : (θ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hθ.ne'
  have hτ' : (τ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hτ.ne'
  have hden : aeval ((τ : 𝕜) • L) ((theta θ hθ).den.map (algebraMap ℝ 𝕜)) =
      1 - ((θ * τ : ℝ) : 𝕜) • L := by
    simp only [theta, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, map_sub, map_one, map_mul, aeval_C, aeval_X,
      ← Algebra.smul_def, RCLike.algebraMap_eq_ofReal, smul_smul]
  have hinv : Ring.inverse (aeval ((τ : 𝕜) • L) ((theta θ hθ).den.map (algebraMap ℝ 𝕜))) = S := by
    rw [hden]
    exact Ring.inverse_unit ⟨_, S, hS', hS⟩
  have hnum : aeval ((τ : 𝕜) • L) ((theta θ hθ).num.map (algebraMap ℝ 𝕜)) =
      1 + ((1 - θ : ℝ) : 𝕜) • (τ : 𝕜) • L := by
    simp only [theta, Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, map_add, map_one, map_mul, aeval_C, aeval_X,
      ← Algebra.smul_def, RCLike.algebraMap_eq_ofReal]
  have hLS : ((θ * τ : ℝ) : 𝕜) • (L * S) = S - 1 := by
    have h := hS'
    rw [sub_mul, one_mul, smul_mul_assoc] at h
    calc ((θ * τ : ℝ) : 𝕜) • (L * S) = S - (S - ((θ * τ : ℝ) : 𝕜) • (L * S)) := by abel
      _ = S - 1 := by rw [h]
  have hc : (θ : 𝕜) * (τ : 𝕜) ≠ 0 := mul_ne_zero hθ' hτ'
  have hR : resolvent ((L : V →ₗ[𝕜] V).toPMap ⊤) ((θ : 𝕜) * (τ : 𝕜))⁻¹ =
      ((θ : 𝕜) * (τ : 𝕜)) • S := by
    rw [hSR]; push_cast; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hLS' : L * S = ((θ : 𝕜) * (τ : 𝕜))⁻¹ • (S - 1) := by
    rw [← hLS]; push_cast; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [apply, hnum, hinv, thetaStep, hR, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc, hLS']
  simp only [smul_smul, smul_sub]
  push_cast
  match_scalars <;> field_simp
  ring

end RationalScheme

/-! ### Consistency and global error of the θ-schemes -/

section Theta

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {L : V →L[𝕜] V}

open RationalScheme

/-- `r_θ(τ L)` is consistent of order `p` with constant `c + 1/(p+1)!` if `n = d Tₚ + c X^{p+1}`
(`c ≥ 0`): the remainder `c/(1 - θ z)` is bounded by `c` on the imaginary axis. -/
private theorem isConsistent_thetaStep_of_eq (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {θ τ c : ℝ}
    (hθ : 0 < θ) (hτ : 0 < τ) (hc : 0 ≤ c) {p : ℕ}
    (h : (theta θ hθ).num = (theta θ hθ).den * expTaylor p + X ^ (p + 1) * C c) :
    IsConsistent L (thetaStep ((L : V →ₗ[𝕜] V).toPMap ⊤) θ τ) τ p
      (c + 1 / (p + 1).factorial) := by
  have hb : ∀ y : ℝ,
      ‖aeval (y * Complex.I) (C c) / aeval (y * Complex.I) (theta θ hθ).den‖ ≤ c := fun y => by
    have h1 := norm_one_add_le (a := 0) (b := θ) (y := y) (by simpa using sq_nonneg θ)
    simp only [theta, aeval_C, map_sub, map_one, map_mul, aeval_X, Complex.coe_algebraMap,
      norm_div, Complex.norm_real, Real.norm_of_nonneg hc] at h1 ⊢
    exact div_le_self hc (by simpa using h1)
  have hτL := dissipative_smul hL hτ.le
  rw [← apply_theta hL hθ hτ]
  refine isConsistent_aeval_mul_inverse hL hτ.le (ρ := (C c).map (algebraMap ℝ 𝕜)) ?_
    ((theta θ hθ).isUnit_aeval_den hτL)
    (((ofBounded _ _ (theta θ hθ).aeval_den_ne_zero hb).norm_apply_le hτL).trans
      (supNorm_ofBounded_le _ hb))
  rw [h]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X]

/-- **The θ-scheme is consistent of order `1`** with constant `θ + 1/2` (real `θ > 0`, `τ > 0`),
uniformly in the bounded dissipative `L`. [Thomee2006], Ch. 7 -/
theorem isConsistent_thetaStep (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {θ τ : ℝ} (hθ : 0 < θ)
    (hτ : 0 < τ) :
    IsConsistent L (thetaStep ((L : V →ₗ[𝕜] V).toPMap ⊤) θ τ) τ 1 (θ + 1 / 2) := by
  convert isConsistent_thetaStep_of_eq hL hθ hτ hθ.le (p := 1)
    (Polynomial.funext fun x => by simp [theta, expTaylor, sum_range_succ]; ring) using 1
  norm_num [Nat.factorial]

/-- **Crank–Nicolson is consistent of order `2`** with constant `5/12` (`τ > 0`), uniformly in
the bounded dissipative `L`. [Thomee2006], Ch. 7 -/
theorem isConsistent_thetaStep_half (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {τ : ℝ} (hτ : 0 < τ) :
    IsConsistent L (thetaStep ((L : V →ₗ[𝕜] V).toPMap ⊤) ((1 / 2 : ℝ) : 𝕜) τ) τ 2 (5 / 12) := by
  convert isConsistent_thetaStep_of_eq hL (θ := 1 / 2) (by norm_num) hτ (c := 1 / 4)
    (by norm_num) (p := 2) (Polynomial.funext fun x => by
      simp [theta, expTaylor, sum_range_succ, Nat.factorial]; ring) using 1
  norm_num [Nat.factorial]

/-- **The global error of the θ-scheme** (`1/2 ≤ θ`, real): at `t = n τ`,
`‖r_θ(τ L)ⁿ y - e^{tL} y‖ ≤ (θ + 1/2) t τ ‖L² y‖` for every bounded dissipative `L`.
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_thetaStep_pow_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {θ τ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hτ : 0 < τ) (n : ℕ) (y : V) :
    ‖(thetaStep ((L : V →ₗ[𝕜] V).toPMap ⊤) θ τ ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      (θ + 1 / 2) * (n * τ) * τ * ‖(L ^ 2) y‖ := by
  simpa using norm_pow_apply_sub_exp_le hL (n := n) (M := 1)
    (fun k _ => norm_thetaStep_pow_le hL (by simpa using hθ) hτ k) hτ.le (by linarith)
    (isConsistent_thetaStep hL (by linarith) hτ) y

/-- **The global error of Crank–Nicolson** (`cayley` with half step `τ/2`): at `t = n τ`,
`‖cayley(L, τ/2)ⁿ y - e^{tL} y‖ ≤ 5/12 t τ² ‖L³ y‖` for every bounded dissipative `L`.
[BrennerThomee1979]; [Thomee2006], Ch. 7 -/
theorem norm_cayley_pow_sub_exp_le (hL : ∀ x, RCLike.re ⟪L x, x⟫_𝕜 ≤ 0) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) (y : V) :
    ‖(cayley ((L : V →ₗ[𝕜] V).toPMap ⊤) (τ / 2) ^ n) y - exp (((n * τ : ℝ) : 𝕜) • L) y‖ ≤
      5 / 12 * (n * τ) * τ ^ 2 * ‖(L ^ 3) y‖ := by
  rw [cayley_half_eq_thetaStep]
  simpa using norm_pow_apply_sub_exp_le hL (n := n) (M := 1)
    (fun k _ => norm_thetaStep_pow_le hL (by rw [RCLike.ofReal_re]) hτ k) hτ.le (by norm_num)
    (isConsistent_thetaStep_half hL hτ) y

end Theta

/-! ### Complex rational functions -/

section Complex

open RationalScheme

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Von Neumann's inequality in the half-plane, complex coefficients**: for complex
polynomials `p`, `q` with `deg p ≤ deg q = N`, `q` free of zeros for `re z ≤ 0` and
`|p(iy)/q(iy)| ≤ K`, every m-dissipative `A` of a complex Hilbert space and `τ > 0`, with the
resolvent `S = (1 - τ A)⁻¹`, `Q(S) = (sᴺ q(1 - 1/s))(S)` is invertible and
`‖P(S) Q(S)⁻¹‖ ≤ K`: von Neumann's inequality for the Cayley transform `C = 2 S - 1` and
`p̃/q̃`, which has no pole in the closed unit disc. [VonNeumann1951]; [HairerWanner1996], §IV.11 -/
theorem norm_resolventEval_mul_inverse_le {A : E →ₗ.[ℂ] E} (hA : A.IsMDissipative) {τ : ℝ}
    (hτ : 0 < τ) {p q : ℂ[X]} (hpq : p.natDegree ≤ q.natDegree)
    (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) {K : ℝ}
    (hK : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ K) :
    IsUnit (resolventEval q.natDegree q ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹)) ∧
      ‖resolventEval q.natDegree p ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹) *
        Ring.inverse (resolventEval q.natDegree q ((τ : ℂ)⁻¹ • resolvent A (τ : ℂ)⁻¹))‖ ≤ K := by
  set N := q.natDegree
  have hq' : ∀ w : ℂ, ‖w‖ ≤ 1 → (cayleyPoly N q).eval w ≠ 0 := fun w hw =>
    eval_cayleyPoly_ne_zero hq hw
  have hK' : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ -1 →
      ‖(cayleyPoly N p).eval ζ / (cayleyPoly N q).eval ζ‖ ≤ K := fun ζ hζ hζ1 => by
    rw [eval_cayleyPoly_div hpq hζ hζ1]; exact hK _
  obtain ⟨hu, hn⟩ := ContinuousLinearMap.norm_aeval_mul_inverse_le (norm_cayley_le hA hτ) hq' hK'
  rw [cayley_eq_two_mul_sub_one, aeval_two_mul_sub_one_cayleyPoly] at hu hn
  rw [aeval_two_mul_sub_one_cayleyPoly] at hn
  have hc : ∀ x : E →L[ℂ] E, Commute ((2 : E →L[ℂ] E) ^ N) x := fun x =>
    (Commute.ofNat_left 2 x).pow_left _
  have h2 : IsUnit (2 : E →L[ℂ] E) := by
    have := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : ℂ) ≠ 0)).map (algebraMap ℂ (E →L[ℂ] E))
    rwa [map_ofNat] at this
  refine ⟨((hc _).isUnit_mul_iff.1 hu).2, ?_⟩
  rwa [Ring.mul_inverse_mul_of_commute (h2.pow _) (hc _) (hc _)] at hn

/-- **For bounded `L`, `P(S) Q(S)⁻¹ = p(L) q(L)⁻¹`** at the resolvent `S = (1 - L)⁻¹`, for
`deg p, deg q ≤ N`, and `Q(S)` is invertible iff `q(L)` is. -/
theorem resolventEval_eq_aeval {L : E →L[ℂ] E} (hL : ∀ x, RCLike.re ⟪L x, x⟫_ℂ ≤ 0) {N : ℕ}
    {p q : ℂ[X]} (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N) :
    (IsUnit (resolventEval N q (resolvent ((L : E →ₗ[ℂ] E).toPMap ⊤) 1)) ↔
        IsUnit (aeval L q)) ∧
      resolventEval N p (resolvent ((L : E →ₗ[ℂ] E).toPMap ⊤) 1) *
          Ring.inverse (resolventEval N q (resolvent ((L : E →ₗ[ℂ] E).toPMap ⊤) 1)) =
        aeval L p * Ring.inverse (aeval L q) := by
  obtain ⟨S, hS, hS', hSL, -, hSe⟩ := exists_cayley_eq hL one_pos
  simp only [RCLike.ofReal_one, inv_one, one_smul] at hS hS' hSe
  rw [← hSe, resolventEval_eq_mul_aeval hS hSL hp, resolventEval_eq_mul_aeval hS hSL hq]
  have hU : IsUnit (S ^ N) := (IsUnit.pow N ⟨⟨S, 1 - L, hS, hS'⟩, rfl⟩)
  have hc : ∀ f : ℂ[X], Commute (S ^ N) (aeval L f) := fun f =>
    (commute_aeval hSL.symm f).symm.pow_left N
  exact ⟨(hc q).isUnit_mul_iff.trans (and_iff_right hU),
    Ring.mul_inverse_mul_of_commute hU (hc p) (hc q)⟩


/-- **Von Neumann's theorem for bounded dissipative operators, complex coefficients**: for
complex polynomials `p`, `q` with `deg p ≤ deg q`, `q` free of zeros for `re z ≤ 0` and
`|p(iy)/q(iy)| ≤ K`, and every bounded dissipative `L` of a complex Hilbert space, `q(L)` is
invertible and `‖p(L) q(L)⁻¹‖ ≤ K` (`norm_resolventEval_mul_inverse_le`, `resolventEval_eq_aeval`).
[HairerWanner1996], §IV.11 -/
theorem norm_aeval_mul_inverse_le_of_dissipative {L : E →L[ℂ] E}
    (hL : ∀ x, RCLike.re ⟪L x, x⟫_ℂ ≤ 0) {p q : ℂ[X]} (hpq : p.natDegree ≤ q.natDegree)
    (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0) {K : ℝ}
    (hK : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ K) :
    IsUnit (aeval L q) ∧ ‖aeval L p * Ring.inverse (aeval L q)‖ ≤ K := by
  have h := norm_resolventEval_mul_inverse_le (L.isMDissipative_toPMap_top hL) one_pos hpq hq hK
  simp only [Complex.ofReal_one, inv_one, one_smul] at h
  obtain ⟨hu, he⟩ := resolventEval_eq_aeval hL hpq le_rfl
  exact ⟨hu.1 h.1, he ▸ h.2⟩

/-- **The Brenner–Thomée error, complex coefficients**: let `r = p/q` be complex, without poles
for `re z ≤ 0`, A-stable (`|r(iy)| ≤ 1`) and of order `m` (`X^{m+1} ∣ p - q Tₘ`, from
`r(z) - e^z = O(z^{m+1})` by `X_pow_dvd_sub_mul_expTaylor`). With the remainder
`ρ = (p - q Tₘ)/X^{m+1}` and `K = sup_y |ρ(iy)/q(iy)| + 1/(m+1)!`, at `t = n τ`,
`‖r(τ L)ⁿ y - e^{tL} y‖ ≤ K t τᵐ ‖L^{m+1} y‖` for every bounded dissipative `L` of a complex
Hilbert space. [BrennerThomee1979] -/
theorem norm_aeval_mul_inverse_pow_sub_exp_le {L : E →L[ℂ] E}
    (hL : ∀ x, RCLike.re ⟪L x, x⟫_ℂ ≤ 0) {p q : ℂ[X]} (hq : ∀ z : ℂ, z.re ≤ 0 → q.eval z ≠ 0)
    (hr : ∀ y : ℝ, ‖p.eval (y * Complex.I) / q.eval (y * Complex.I)‖ ≤ 1) {m : ℕ}
    (hm : X ^ (m + 1) ∣ p - q * (expTaylor m).map (algebraMap ℝ ℂ)) {τ : ℝ} (hτ : 0 ≤ τ)
    (n : ℕ) (y : E) :
    ‖((aeval ((τ : ℂ) • L) p * Ring.inverse (aeval ((τ : ℂ) • L) q)) ^ n) y -
        exp (((n * τ : ℝ) : ℂ) • L) y‖ ≤
      ((⨆ y : ℝ, ‖((p - q * (expTaylor m).map (algebraMap ℝ ℂ)) /ₘ X ^ (m + 1)).eval
          (y * Complex.I) / q.eval (y * Complex.I)‖) + 1 / (m + 1).factorial) *
        (n * τ) * τ ^ m * ‖(L ^ (m + 1)) y‖ := by
  set T := (expTaylor m).map (algebraMap ℝ ℂ)
  set ρ := (p - q * T) /ₘ X ^ (m + 1)
  have hpq := natDegree_le_of_norm_div_imaginary_le hq hr
  have hρq : ρ.natDegree ≤ q.natDegree := by
    rw [natDegree_divByMonic _ (monic_X_pow _), natDegree_X_pow]
    have h1 := natDegree_sub_le p (q * T)
    have h2 := natDegree_mul_le (p := q) (q := T)
    have h3 : T.natDegree ≤ m := natDegree_map_le.trans (natDegree_expTaylor_le m)
    omega
  have hexp : p = q * T + X ^ (m + 1) * ρ := by
    have h := modByMonic_add_div (p - q * T) (X ^ (m + 1))
    rw [(modByMonic_eq_zero_iff_dvd (monic_X_pow _)).2 hm, zero_add] at h
    linear_combination -h
  have hb := bddAbove_norm_div_imaginary hρq hq
  have hτL := dissipative_smul (𝕜 := ℂ) hL hτ
  have hc := isConsistent_aeval_mul_inverse hL hτ hexp
    (norm_aeval_mul_inverse_le_of_dissipative hτL hpq hq hr).1
    (norm_aeval_mul_inverse_le_of_dissipative hτL hρq hq fun y => le_ciSup hb y).2
  have := norm_pow_apply_sub_exp_le hL (M := 1) (n := n)
    (fun k _ => norm_pow_le_one (norm_aeval_mul_inverse_le_of_dissipative hτL hpq hq hr).2 k) hτ
    (add_nonneg ((norm_nonneg _).trans (le_ciSup hb 0)) (by positivity)) hc y
  simpa using this

end Complex

end Feec.TimeStepping
