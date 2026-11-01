module

public import Feec.TimeStepping.RationalBanach
public import Feec.Semigroup.HillePhillips

/-!
# Rational approximations of bounded semigroups: the `√n` stability bound

Let `r = n/d` be a rational scheme (`Feec.TimeStepping.RationalScheme`, no poles in
`re z ≤ 0`). In the half-line algebra (`Feec.HalfLineAlgebra`), `Q(ν) = νᴺ d(1 - 1/ν)` is
invertible (`isUnit_resolventEval_den_resolvent`: `Q` factors into `ν - sⱼ`, and `1 - 1/sⱼ` is a
pole of `r`), so `r` has a **Hille–Phillips measure** `μ_r = P(ν) Q(ν)⁻¹`
(`RationalScheme.hpMeasure`), with `μ̂_r(ξ) = r(-2πiξ)` and atom `r(∞)`. For a bounded semigroup
`‖S(t)‖ ≤ M` on a complex Banach space, `r(τA) = P(R) Q(R)⁻¹ = Φ(μ_r)`
(`hillePhillips_hpMeasure`), `R = (1 - τA)⁻¹` the Laplace transform of the semigroup. Hence

* `Q(R)` is invertible and `‖r(τA)‖ ≤ M ‖μ_r‖` for every `r` (`norm_resolventStep_le`); in
  particular the remainder `ρ(τA)` is bounded;
* **Brenner–Thomée's stability bound** `‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)` for strongly A-stable `r`
  (`IsStronglyAStable`: `|r(iy)| ≤ 1`, `|r(∞)| < 1`), from the total variation bound
  `‖μ_rⁿ‖ ≤ 1 + C_r √n` (`variation_hpMeasure_pow_le`,
  `Feec.HalfLineAlgebra.integral_norm_pow_snd_pow_four_le`);
* **the order-`p` error with the extra factor `√n`**
  (`norm_resolventStep_pow_sub_S_le_sqrt`): every hypothesis of the Banach-space
  Brenner–Thomée theorem `RationalScheme.norm_resolventStep_pow_sub_S_le` is discharged.

The bound `C √n` holds for every A-acceptable `r` in [BrennerThomee1979]; the Fourier
argument here uses `|r(∞)| < 1` (it bounds `‖gₙ‖₂` uniformly in `n`), which covers the L-stable
schemes but not the Gauss/diagonal Padé schemes (`|r(∞)| = 1`). Complex Banach spaces only: the
measure `μ_r` is complex.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [R. Hersh, T. Kato, *High-Accuracy Stable Difference Schemes for Well-Posed Initial-Value Problems*][HershKato1979]
* [E. Hille, R. S. Phillips, *Functional Analysis and Semi-Groups*][HillePhillips1957], Ch. XV
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Finset Polynomial MeasureTheory Unitization

@[expose] public noncomputable section

namespace Feec

namespace TimeStepping

/-- `sᴺ f(1 - 1/s)` at `s = 0` is `f_N (-1)ᴺ`. -/
theorem resolventEval_zero (N : ℕ) (f : ℂ[X]) :
    resolventEval N f (0 : ℂ) = f.coeff N * (-1) ^ N := by
  rw [resolventEval, sum_range_succ, sum_eq_zero fun k hk => by
    rw [zero_pow (by have := mem_range.1 hk; omega)]; simp]
  simp

/-- At an algebra homomorphism into a field, `sᴺ f(1 - 1/s)` is evaluation of the polynomial
`resolventEval N f X`. -/
theorem resolventEval_eq_eval {A : Type*} [Ring A] [Algebra ℂ A] (N : ℕ) (f : ℂ[X]) (S : A) :
    resolventEval N f S = aeval S (resolventEval N f (X : ℂ[X])) := by
  rw [map_resolventEval, aeval_X]

/-- `φ` commutes with `Ring.inverse` at units. -/
theorem map_ringInverse {A B : Type*} [Ring A] [Ring B] {F : Type*} [FunLike F A B]
    [MonoidHomClass F A B] (φ : F) {a : A} (ha : IsUnit a) :
    φ (Ring.inverse a) = Ring.inverse (φ a) := by
  obtain ⟨u, rfl⟩ := ha
  have : φ ↑u = ↑(Units.map (φ : A →* B) u) := rfl
  rw [this, Ring.inverse_unit, Ring.inverse_unit]
  rfl

namespace RationalScheme

variable (r : RationalScheme)

/-- `Q(s) = sᴺ d(1 - 1/s)` as a complex polynomial, `N = deg d`. -/
def denPoly : ℂ[X] := resolventEval r.den.natDegree (r.den.map (algebraMap ℝ ℂ)) X

theorem eval_denPoly_zero :
    r.denPoly.eval 0 = (r.den.leadingCoeff : ℂ) * (-1) ^ r.den.natDegree := by
  have := map_resolventEval (aeval (0 : ℂ)) r.den.natDegree (r.den.map (algebraMap ℝ ℂ)) X
  rw [aeval_X, resolventEval_zero, coe_aeval_eq_eval] at this
  rw [denPoly, this, coeff_map]
  rfl

theorem eval_denPoly_zero_ne_zero : r.denPoly.eval 0 ≠ 0 := by
  rw [eval_denPoly_zero]
  simp [leadingCoeff_eq_zero, r.den_ne_zero]

/-- **The roots of `Q`**: `s ≠ 0`, and `1 - 1/s` is a pole of `r`, so it has positive real
part. -/
theorem re_pos_of_isRoot {s : ℂ} (hs : r.denPoly.IsRoot s) : s ≠ 0 ∧ 0 < (1 - s⁻¹).re := by
  have hs0 : s ≠ 0 := fun h => r.eval_denPoly_zero_ne_zero (by subst h; exact hs)
  refine ⟨hs0, not_le.1 fun hre => r.aeval_den_ne_zero _ hre ?_⟩
  have h := eval_resolventEval_X (natDegree_map_le (f := algebraMap ℝ ℂ) (p := r.den)) hs0
  rw [← denPoly, hs.eq_zero, eq_comm, mul_eq_zero] at h
  rw [← eval_map_algebraMap]
  exact h.resolve_left (pow_ne_zero _ hs0)

/-- **`Q(ν)` is invertible in the half-line algebra**: `Q` factors into `s - sⱼ` over its roots, and
`ν - sⱼ` is invertible since `1 - 1/sⱼ` is a pole of `r` (`re > 0`). -/
theorem isUnit_resolventEval_den_resolvent :
    IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ ℂ)) HalfLineAlgebra.resolvent) := by
  rw [resolventEval_eq_eval, ← denPoly]
  have hQ : r.denPoly ≠ 0 := fun h => r.eval_denPoly_zero_ne_zero (by simp [h])
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (splits_iff_card_roots.1 (IsAlgClosed.splits r.denPoly)), map_mul, aeval_C,
    map_multiset_prod, Multiset.map_map]
  refine ((isUnit_iff_ne_zero.2 (leadingCoeff_ne_zero.2 hQ)).map _).mul
    (Multiset.prod_induction _ _ (fun _ _ => IsUnit.mul) isUnit_one fun a ha => ?_)
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 ha
  obtain ⟨hs0, hre⟩ := r.re_pos_of_isRoot ((mem_roots hQ).1 hs)
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C]
  rw [← neg_sub]
  exact (HalfLineAlgebra.isUnit_algebraMap_sub_resolvent hs0 hre).neg

/-- **The Hille–Phillips measure of `r`**: `μ_r = P(ν) Q(ν)⁻¹` in the half-line algebra, with
`ν = e^{-t} dt`; its Fourier–Stieltjes transform is `r(-2πiξ)` (`fourier_hpMeasure`) and
`r(τA) = Φ(μ_r)` for every bounded semigroup (`hillePhillips_hpMeasure`). -/
def hpMeasure : HalfLineAlgebra :=
  resolventEval r.den.natDegree (r.num.map (algebraMap ℝ ℂ)) HalfLineAlgebra.resolvent *
    Ring.inverse (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ ℂ))
      HalfLineAlgebra.resolvent)

/-- Algebra homomorphisms carry `μ_r` to `P(φ ν) Q(φ ν)⁻¹`. -/
theorem map_hpMeasure {B : Type*} [Ring B] [Algebra ℂ B] (φ : HalfLineAlgebra →ₐ[ℂ] B) :
    φ r.hpMeasure = resolventEval r.den.natDegree (r.num.map (algebraMap ℝ ℂ))
      (φ HalfLineAlgebra.resolvent) * Ring.inverse (resolventEval r.den.natDegree
        (r.den.map (algebraMap ℝ ℂ)) (φ HalfLineAlgebra.resolvent)) := by
  rw [hpMeasure, map_mul, map_ringInverse φ r.isUnit_resolventEval_den_resolvent,
    map_resolventEval, map_resolventEval]

/-- **`μ̂_r(ξ) = r(-2πiξ)`**. -/
theorem fourier_hpMeasure (ξ : ℝ) :
    HalfLineAlgebra.fourier ξ r.hpMeasure = r.eval (-(2 * Real.pi * ξ * Complex.I)) := by
  set s : ℂ := (1 + 2 * Real.pi * ξ * Complex.I)⁻¹
  have hs : s ≠ 0 := inv_ne_zero fun h => by
    have := congrArg Complex.re h
    simp at this
  have hz : 1 - s⁻¹ = -(2 * Real.pi * ξ * Complex.I) := by simp [s]
  have he : ∀ f : ℝ[X], f.natDegree ≤ r.den.natDegree →
      resolventEval r.den.natDegree (f.map (algebraMap ℝ ℂ)) s =
        s ^ r.den.natDegree * aeval (-(2 * Real.pi * ξ * Complex.I)) f := fun f hf => by
    rw [resolventEval_eq_eval, coe_aeval_eq_eval,
      eval_resolventEval_X (natDegree_map_le.trans hf) hs, hz, eval_map_algebraMap]
  rw [map_hpMeasure, HalfLineAlgebra.fourier_resolvent, he _ r.natDegree_num_le, he _ le_rfl,
    Ring.inverse_eq_inv', eval, mul_inv, div_eq_mul_inv]
  field_simp

/-- The atom of `μ_r` is `r(∞) = n_N / d_N`. -/
theorem fst_hpMeasure :
    r.hpMeasure.fst = (r.num.coeff r.den.natDegree / r.den.leadingCoeff : ℝ) := by
  have h := r.map_hpMeasure (fstHom ℂ HalfLineKernel)
  rw [show fstHom ℂ HalfLineKernel HalfLineAlgebra.resolvent = 0 from rfl, resolventEval_zero,
    resolventEval_zero, coeff_map, coeff_map, Ring.inverse_eq_inv'] at h
  rw [show r.hpMeasure.fst = fstHom ℂ HalfLineKernel r.hpMeasure from rfl, h]
  push_cast
  rw [leadingCoeff, mul_inv]
  have : ((-1 : ℂ) ^ r.den.natDegree) * ((-1) ^ r.den.natDegree)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  linear_combination (algebraMap ℝ ℂ (r.num.coeff r.den.natDegree) *
    (algebraMap ℝ ℂ (r.den.coeff r.den.natDegree))⁻¹) * this

/-- **Strong A-stability**: A-stable with `|r(∞)| < 1` (`|n_N| < |d_N|`, `N = deg d`); every
L-stable scheme is strongly A-stable. [HairerWanner1996], §IV.3 -/
def IsStronglyAStable : Prop :=
  r.IsAStable ∧ |r.num.coeff r.den.natDegree| < |r.den.leadingCoeff|

/-- L-stable schemes are strongly A-stable (`r(∞) = 0`). -/
theorem IsLStable.isStronglyAStable {r : RationalScheme} (hr : r.IsLStable) :
    r.IsStronglyAStable := by
  refine ⟨hr.1, ?_⟩
  rw [coeff_eq_zero_of_degree_lt (hr.2.trans_eq (degree_eq_natDegree r.den_ne_zero)), abs_zero]
  exact abs_pos.2 (leadingCoeff_ne_zero.2 r.den_ne_zero)

theorem norm_fst_hpMeasure_lt {r : RationalScheme} (hr : r.IsStronglyAStable) :
    ‖r.hpMeasure.fst‖ < 1 := by
  rw [fst_hpMeasure, Complex.norm_real, Real.norm_eq_abs, abs_div,
    div_lt_one (abs_pos.2 (leadingCoeff_ne_zero.2 r.den_ne_zero))]
  exact hr.2

theorem norm_fourier_hpMeasure_le {r : RationalScheme} (hr : r.IsAStable) (ξ : ℝ) :
    ‖HalfLineAlgebra.fourier ξ r.hpMeasure‖ ≤ 1 := by
  rw [fourier_hpMeasure]
  convert hr (-(2 * Real.pi * ξ)) using 3
  push_cast; ring

/-- **Brenner–Thomée's constant** `C_r = K^{1/4}`, `K = 4π² ‖g‖₂² ‖t g‖₂² / (1 - |r(∞)|)²` for
`μ_r = r(∞) δ₀ + g`. -/
def stabilityConst : ℝ :=
  √(√(4 * Real.pi ^ 2 * (∫ t, ‖r.hpMeasure.snd t‖ ^ 2) * (∫ t, ‖t • r.hpMeasure.snd t‖ ^ 2) /
    (1 - ‖r.hpMeasure.fst‖) ^ 2))

/-- **The total variation of `μ_rⁿ` is at most `1 + C_r √n`** for strongly A-stable `r`
(`Feec.HalfLineAlgebra.integral_norm_pow_snd_pow_four_le`). -/
theorem variation_hpMeasure_pow_le {r : RationalScheme} (hr : r.IsStronglyAStable) (n : ℕ) :
    (r.hpMeasure ^ n).variation ≤ 1 + r.stabilityConst * √n := by
  have ha := norm_fst_hpMeasure_lt hr
  have h4 := HalfLineAlgebra.integral_norm_pow_snd_pow_four_le r.hpMeasure ha
    (norm_fourier_hpMeasure_le hr.1) n
  set K := 4 * Real.pi ^ 2 * (∫ t, ‖r.hpMeasure.snd t‖ ^ 2) *
    (∫ t, ‖t • r.hpMeasure.snd t‖ ^ 2) / (1 - ‖r.hpMeasure.fst‖) ^ 2
  have hK : 0 ≤ K := by
    have : 0 < 1 - ‖r.hpMeasure.fst‖ := by linarith
    have h1 : 0 ≤ ∫ t, ‖r.hpMeasure.snd t‖ ^ 2 := integral_nonneg fun _ => by positivity
    have h2 : 0 ≤ ∫ t, ‖t • r.hpMeasure.snd t‖ ^ 2 := integral_nonneg fun _ => by positivity
    positivity
  have hI : ∫ t, ‖(r.hpMeasure ^ n).snd t‖ ≤ r.stabilityConst * √n := by
    refine (pow_le_pow_iff_left₀ (integral_nonneg fun _ => norm_nonneg _) (by
      unfold stabilityConst; positivity) (by norm_num : 4 ≠ 0)).1 ?_
    have e1 : √(√K) ^ 4 = K := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
        Real.sq_sqrt hK]
    have e2 : √(n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [mul_pow, stabilityConst, e1, e2]
    exact h4
  have hfst : (r.hpMeasure ^ n).fst = r.hpMeasure.fst ^ n :=
    map_pow (fstHom ℂ HalfLineKernel) r.hpMeasure n
  rw [HalfLineAlgebra.variation, hfst, norm_pow]
  exact add_le_add (pow_le_one₀ (norm_nonneg _) ha.le) hI

/-! ### Bounded semigroups on Banach spaces -/

section Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

/-- **`r(τA)` is the Hille–Phillips operator of `μ_r`**: `r(τA) = Φ(μ_r)` for the semigroup
`S(τ ·)`, with `R = (1 - τA)⁻¹` its Laplace transform (`C0Semigroup.laplaceResolvent`). -/
theorem hillePhillips_hpMeasure {τ : ℝ} (hτ : 0 ≤ τ) :
    (G.dilate τ hτ).hillePhillips (G.norm_dilate_S_le hM hτ) r.hpMeasure =
      r.resolventStep (G.laplaceResolvent hM τ hτ) := by
  rw [map_hpMeasure]
  rfl

/-- `Q(R)` is invertible for every rational scheme (no stability needed). -/
theorem isUnit_resolventEval_den_laplaceResolvent {τ : ℝ} (hτ : 0 ≤ τ) :
    IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ ℂ))
      (G.laplaceResolvent hM τ hτ)) := by
  have := r.isUnit_resolventEval_den_resolvent.map
    ((G.dilate τ hτ).hillePhillips (G.norm_dilate_S_le hM hτ))
  rwa [map_resolventEval] at this

/-- **The Hille–Phillips bound**: `‖r(τA)‖ ≤ M ‖μ_r‖` for every rational scheme and every
bounded semigroup, `‖S(t)‖ ≤ M`; in particular the remainder `ρ(τA)` is bounded uniformly in
`τ`. [HillePhillips1957], Ch. XV -/
theorem norm_resolventStep_le {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖r.resolventStep (G.laplaceResolvent hM τ hτ)‖ ≤ M * r.hpMeasure.variation := by
  rw [← r.hillePhillips_hpMeasure G hM hτ]
  exact (G.dilate τ hτ).norm_hillePhillips_le _ _

/-- **Brenner–Thomée's stability bound** [BrennerThomee1979]; [HershKato1979]: for a strongly
A-stable rational scheme `r` and a bounded semigroup, `‖S(t)‖ ≤ M`, on a complex Banach space,
`‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)` for all `τ ≥ 0` and `n`, with `C_r` depending only on `r`
(`RationalScheme.stabilityConst`). -/
theorem norm_resolventStep_pow_le {r : RationalScheme} (hr : r.IsStronglyAStable) {τ : ℝ}
    (hτ : 0 ≤ τ) (n : ℕ) :
    ‖r.resolventStep (G.laplaceResolvent hM τ hτ) ^ n‖ ≤ M * (1 + r.stabilityConst * √n) := by
  rw [← r.hillePhillips_hpMeasure G hM hτ, ← map_pow]
  exact ((G.dilate τ hτ).norm_hillePhillips_le _ _).trans (mul_le_mul_of_nonneg_left
    (variation_hpMeasure_pow_le hr n) ((norm_nonneg _).trans (hM 0 le_rfl)))

/-- **Brenner–Thomée's error bound for bounded semigroups on Banach spaces**: for a strongly
A-stable rational scheme `r` of order `p`, a bounded semigroup `‖S(t)‖ ≤ M` on a complex Banach
space with generator `A`, `τ > 0` and `x ∈ D(A^{p+1})` (a chain `u` in the graph of `A`),

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ M (1 + C_r √n) (M ‖μ_ρ‖ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖`,

an order-`p` bound with the extra factor `√n` of [BrennerThomee1979] (`ρ` the remainder scheme).
Every hypothesis of `RationalScheme.norm_resolventStep_pow_sub_S_le` is discharged: `R` is the
Laplace transform of the semigroup, `Q(R)` is invertible and `ρ(τA)` bounded by the
Hille–Phillips calculus, stability by `norm_resolventStep_pow_le`. -/
theorem norm_resolventStep_pow_sub_S_le_sqrt {r : RationalScheme} (hr : r.IsStronglyAStable)
    {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      M * (1 + r.stabilityConst * √n) *
        (M * (r.remainder p).hpMeasure.variation + M / (p + 1).factorial) * M * (n * τ) *
          τ ^ p * ‖u (p + 1)‖ := by
  refine r.norm_resolventStep_pow_sub_S_le G hp hτ.le
    (fun x y hxy => G.laplaceResolvent_apply_sub hM hτ.le hxy)
    (G.injective_laplaceResolvent hM hτ) (r.isUnit_resolventEval_den_laplaceResolvent G hM hτ.le)
    (fun k hk => (norm_resolventStep_pow_le G hM hr hτ.le k).trans ?_)
    (fun t ht => hM t ht.1) ((r.remainder p).norm_resolventStep_le G hM hτ.le) hu
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  have hC : 0 ≤ r.stabilityConst := Real.sqrt_nonneg _
  gcongr

end Semigroup

end RationalScheme

end TimeStepping

end Feec
