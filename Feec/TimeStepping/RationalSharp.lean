module

public import Feec.TimeStepping.RationalHillePhillips
public import Feec.Semigroup.HillePhillipsTranslate
public import Feec.ForMathlib.Algebra.GeomSum

/-!
# Brenner–Thomée's smooth-data error estimate on Banach spaces

Let `r` be an A-stable rational scheme (`|r(iy)| ≤ 1`, no poles in `re z ≤ 0`) of order `p`, and
`S` a bounded strongly continuous semigroup, `‖S(t)‖ ≤ M`, on a complex Banach space, with
generator `A`. **Brenner–Thomée's smooth-data estimate**
(`RationalScheme.norm_resolventStep_pow_sub_S_le_sharp`):

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C M nτ τᵖ ‖A^{p+1} x‖`  for `x ∈ D(A^{p+1})`, `τ > 0`, every `n`,

with `C = RationalScheme.sharpConst r p` depending only on `r` and `p`; at fixed `T = nτ`, order
`p`. This is the smooth-data case `s = p + 1` of Brenner and Thomée's estimate
`‖e^{-tA} x - rⁿ(tA/n) x‖ ≤ C M t^s/n^{sp/(p+1)} ‖Aˢ x‖` for `s ∈ ((p+1)/2, p+1]` (`-A` the
generator, `t = nτ`; at `s = p + 1`, `t^{p+1}/nᵖ = nτ τᵖ`), as stated
in [GomilkoTomilov2024], Thm 1.1(ii), after [BrennerThomee1979] (Thms 1 and 4 there, per
[GomilkoTomilov2024]; the paper itself was not consulted), for every A-stable `r`, `|r(∞)| = 1`
included (Crank–Nicolson, the Gauss methods), and without the `√n` loss of the stability bound
`‖r(τA)ⁿ‖ ≤ M (1 + C √n)` (`RationalScheme.norm_resolventStep_pow_le_of_isAStable`), which the
proof does not use. On real or complex Banach spaces, by complexification:
`RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`
(`Feec.TimeStepping.RationalHillePhillipsReal`). Less smooth data (`s < p + 1`; below
`s = (p+1)/2` the rate of [GomilkoTomilov2024], Thm 1.1(ii), is `n^{1/2-s}`, with a factor
`log (n+1)` at `s = (p+1)/2`) are not formalized. [HershKato1979] obtain `O(τᵖ)` for
`x ∈ D(A^{p+2})`, one power of `A` more (per its abstract).

The proof is the Hille–Phillips calculus extended by translations: with `μ = μ_r` the measure of
`r` (`RationalScheme.hpMeasure`) and the **consistency kernel** `h = μ_ρ - eₚ`
(`RationalScheme.consistencyKernel`; `ρ` the remainder, `eₚ` the Taylor kernel), which has no atom
(`fst_hpMeasure_remainder`),

* `r(τA) x - S(τ) x = τ^{p+1} Φ(h) A^{p+1} x` (`resolventStep_sub_S_apply`), from the expansion
  `r = Tₚ + z^{p+1} ρ` and Taylor's formula for the semigroup with integral remainder;
* `r(τA)ⁿ - S(τ)ⁿ = Σ_{j<n} r(τA)ʲ (r(τA) - S(τ)) S(τ)^{n-1-j}`, and point masses act as the
  semigroup, so `r(τA)ⁿ x - S(nτ) x = τ^{p+1} Φ(kₙ) A^{p+1} x` with Brenner–Thomée's error kernel
  `kₙ = Σ_{j<n} δ_{n-1-j} ⋆ μʲ ⋆ h` (`resolventStep_pow_sub_S_apply`);
* `‖kₙ‖₁ ≤ C n` (`Feec.HalfLineAlgebra.integral_norm_errorKernel_le`): `z^{p+1} ĥ = r(z) - e^z`
  and `|r(z)| ≤ 1` on the imaginary axis, by Carlson's inequality and Plancherel's theorem on the
  geometric sum `kₙ(· + n)̂ = e^{-z} ĥ Σ_{j<n} (e^{-z} r(z))ʲ`. Brenner and Thomée apply Carlson's
  inequality locally on a partition of unity ([GomilkoTomilov2024], §1.1); here one global Carlson
  estimate around `t = n` suffices.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024],
  Thm 1.1
* [E. Hille, R. S. Phillips, *Functional Analysis and Semi-Groups*][HillePhillips1957]
* [R. Hersh, T. Kato, *High-Accuracy Stable Difference Schemes for Well-Posed Initial-Value Problems*][HershKato1979]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Finset Polynomial MeasureTheory Unitization FourierTransform

@[expose] public noncomputable section

namespace Feec

namespace TimeStepping

namespace RationalScheme

variable (r : RationalScheme)

/-- **The expansion `r(z) = Tₚ(z) + z^{p+1} ρ(z)`** off the poles, for `r` of order `p`. -/
theorem eval_eq_add {p : ℕ} (hp : r.HasOrder p) {z : ℂ} (hz : z.re ≤ 0) :
    r.eval z = ∑ j ∈ range (p + 1), z ^ j / j.factorial + z ^ (p + 1) * (r.remainder p).eval z := by
  have hd := r.aeval_den_ne_zero z hz
  have h := congrArg (aeval z) (r.num_eq_add hp)
  simp only [map_add, map_mul, map_pow, aeval_X] at h
  have hT : aeval z (expTaylor p) = ∑ j ∈ range (p + 1), z ^ j / j.factorial := by
    simp [expTaylor, div_eq_inv_mul]
  rw [eval, eval, h, hT, show (r.remainder p).den = r.den from rfl]
  field_simp

/-- **The remainder has no atom**: `ρ(∞) = 0`, since `deg (n - d Tₚ) ≤ N + p`. -/
theorem fst_hpMeasure_remainder {p : ℕ} (hp : r.HasOrder p) :
    (r.remainder p).hpMeasure.fst = 0 := by
  rw [fst_hpMeasure]
  have hc := congrArg (coeff · (r.den.natDegree + (p + 1))) (r.num_eq_add hp)
  simp only [coeff_add, coeff_X_pow_mul] at hc
  rw [coeff_eq_zero_of_natDegree_lt (by have := r.natDegree_num_le; omega),
    coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt (by
      have := natDegree_expTaylor_le p; omega)), zero_add] at hc
  rw [show (r.remainder p).den = r.den from rfl, ← hc]
  simp

/-- **The consistency kernel** `h = μ_ρ - eₚ`: `r(τA) - S(τ) = τ^{p+1} Φ(h) A^{p+1}` on
`D(A^{p+1})` and `z^{p+1} ĥ = r(z) - e^z`. -/
def consistencyKernel (p : ℕ) : HalfLineKernel :=
  (r.remainder p).hpMeasure.snd - HalfLineKernel.taylor p

theorem symb_pow_mul_fourier_consistencyKernel {p : ℕ} (hp : r.HasOrder p) (ξ : ℝ) :
    GeomSum.symb ξ ^ (p + 1) * 𝓕 (r.consistencyKernel p : ℝ → ℂ) ξ =
      HalfLineAlgebra.fourier ξ r.hpMeasure - Complex.exp (GeomSum.symb ξ) := by
  have hz : (GeomSum.symb ξ).re ≤ 0 := by simp [GeomSum.symb]
  have hρ : 𝓕 ((r.remainder p).hpMeasure.snd : ℝ → ℂ) ξ =
      (r.remainder p).eval (GeomSum.symb ξ) := by
    have := (r.remainder p).fourier_hpMeasure ξ
    rw [HalfLineAlgebra.fourier_apply, r.fst_hpMeasure_remainder hp, zero_add] at this
    exact this
  have hsub : 𝓕 (r.consistencyKernel p : ℝ → ℂ) ξ =
      𝓕 ((r.remainder p).hpMeasure.snd : ℝ → ℂ) ξ - 𝓕 (HalfLineKernel.taylor p : ℝ → ℂ) ξ :=
    map_sub (HalfLineKernel.fourierChar ξ) _ _
  rw [hsub, mul_sub, hρ, HalfLineKernel.symb_pow_mul_fourier_taylor, fourier_hpMeasure,
    show -(2 * Real.pi * ξ * Complex.I) = GeomSum.symb ξ from rfl, r.eval_eq_add hp hz]
  ring

/-- **Brenner–Thomée's constant of the smooth-data estimate**: the constant of
`Feec.HalfLineAlgebra.integral_norm_errorKernel_le` for `μ_r` and the consistency kernel. -/
def sharpConst (p : ℕ) : ℝ :=
  HalfLineAlgebra.errorConst r.hpMeasure (r.consistencyKernel p) p

/-- **`‖kₙ‖₁ ≤ C n`** for A-stable `r` of order `p`. [BrennerThomee1979] -/
theorem integral_norm_errorKernel_le {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) (n : ℕ) :
    ∫ t, ‖HalfLineAlgebra.errorKernel r.hpMeasure (r.consistencyKernel p) n t‖ ≤
      r.sharpConst p * n :=
  HalfLineAlgebra.integral_norm_errorKernel_le _ (norm_fourier_hpMeasure_le hr) _
    (r.symb_pow_mul_fourier_consistencyKernel hp) n

/-- The constant of the smooth-data estimate is nonnegative (`‖k₁‖₁ ≤ C`). -/
theorem sharpConst_nonneg {r : RationalScheme} (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) :
    0 ≤ r.sharpConst p := by
  have h := integral_norm_errorKernel_le hr hp 1
  rw [Nat.cast_one, mul_one] at h
  exact (integral_nonneg fun t => norm_nonneg _).trans h

/-! ### Bounded semigroups on Banach spaces -/

section Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (G : C0Semigroup ℂ E) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

/-- **The consistency identity** `r(τA) x - S(τ) x = τ^{p+1} Φ_τ(h) A^{p+1} x` on `D(A^{p+1})`
(a chain `u`), `Φ_τ` the calculus of `S(τ ·)` and `h` the consistency kernel. -/
theorem resolventStep_sub_S_apply {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    r.resolventStep (G.laplaceResolvent hM τ hτ.le) (u 0) - G.S τ (u 0) =
      (τ : ℂ) ^ (p + 1) • (G.dilate τ hτ.le).hillePhillipsKernel (G.norm_dilate_S_le hM hτ.le)
        (r.consistencyKernel p) (u (p + 1)) := by
  have hρ : (r.remainder p).resolventStep (G.laplaceResolvent hM τ hτ.le) =
      (G.dilate τ hτ.le).hillePhillipsKernel (G.norm_dilate_S_le hM hτ.le)
        (r.remainder p).hpMeasure.snd := by
    rw [← (r.remainder p).hillePhillips_hpMeasure G hM hτ.le, C0Semigroup.hillePhillips_apply,
      r.fst_hpMeasure_remainder hp, _root_.map_zero, zero_add]
  rw [r.resolventStep_apply_eq hp (fun x y hxy => G.laplaceResolvent_apply_sub hM hτ.le hxy)
    (G.injective_laplaceResolvent hM hτ) (r.isUnit_resolventEval_den_laplaceResolvent G hM hτ.le)
    hu, G.S_apply_eq_sum_add_taylor hM hτ p hu, hρ]
  have hk := map_sub ((G.dilate τ hτ.le).hillePhillipsKernelHom (G.norm_dilate_S_le hM hτ.le))
    (r.remainder p).hpMeasure.snd (HalfLineKernel.taylor p)
  change _ = (τ : ℂ) ^ (p + 1) • ((G.dilate τ hτ.le).hillePhillipsKernelHom
    (G.norm_dilate_S_le hM hτ.le) ((r.remainder p).hpMeasure.snd - HalfLineKernel.taylor p))
      (u (p + 1))
  rw [hk, sub_apply, smul_sub]
  generalize (∑ j ∈ range (p + 1), ((τ : ℂ) ^ j / j.factorial) • u j) = A
  rw [add_sub_add_left_eq_sub]
  rfl

/-- **The error as the calculus of Brenner–Thomée's error kernel**:
`r(τA)ⁿ x - S(nτ) x = τ^{p+1} Φ_τ(kₙ) A^{p+1} x` on `D(A^{p+1})`, with
`kₙ = Σ_{j<n} δ_{n-1-j} ⋆ μ_rʲ ⋆ h` (`Feec.HalfLineAlgebra.errorKernel`). -/
theorem resolventStep_pow_sub_S_apply {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ)
    {u : ℕ → E} (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    (r.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) - G.S (n * τ) (u 0) =
      (τ : ℂ) ^ (p + 1) • (G.dilate τ hτ.le).hillePhillipsKernel (G.norm_dilate_S_le hM hτ.le)
        (HalfLineAlgebra.errorKernel r.hpMeasure (r.consistencyKernel p) n) (u (p + 1)) := by
  set G' := G.dilate τ hτ.le
  set hM' := G.norm_dilate_S_le hM hτ.le
  set P := r.resolventStep (G.laplaceResolvent hM τ hτ.le)
  set h := r.consistencyKernel p
  have hP : G'.hillePhillips hM' r.hpMeasure = P := r.hillePhillips_hpMeasure G hM hτ.le
  have hS : ∀ m : ℕ, G'.S m = G.S τ ^ m := fun m => G.S_mul_natCast hτ.le m
  -- each term of the telescoping sum
  have hterm : ∀ j m : ℕ, (P ^ j * (P - G.S τ) * G.S τ ^ m) (u 0) =
      (τ : ℂ) ^ (p + 1) • G'.hillePhillipsKernel hM'
        (HalfLineKernel.translate (m : ℝ) (Nat.cast_nonneg m) (r.hpMeasure ^ j * inr h).snd)
        (u (p + 1)) := by
    intro j m
    have hv : ∀ i < p + 1, ((G.S τ ^ m) (u i), (G.S τ ^ m) (u (i + 1))) ∈ G.generator.graph :=
      fun i hi => by
        rw [← G.S_mul_natCast hτ.le m]
        exact G.S_mem_graph (hu i hi) (by positivity)
    have h1 := r.resolventStep_sub_S_apply G hM hp hτ hv
    have hmul : r.hpMeasure ^ j * inr h = inr (r.hpMeasure ^ j * inr h).snd := by
      ext
      · simp
      · rfl
    calc (P ^ j * (P - G.S τ) * G.S τ ^ m) (u 0)
        = (P ^ j) (P ((G.S τ ^ m) (u 0)) - G.S τ ((G.S τ ^ m) (u 0))) := rfl
      _ = (τ : ℂ) ^ (p + 1) • (P ^ j) (G'.hillePhillipsKernel hM' h ((G.S τ ^ m) (u (p + 1)))) := by
          rw [h1, _root_.map_smul]
      _ = _ := by
          congr 1
          have e1 : G'.hillePhillipsKernel hM' (r.hpMeasure ^ j * inr h).snd =
              P ^ j * G'.hillePhillipsKernel hM' h := by
            rw [← G'.hillePhillips_inr hM', ← hmul, map_mul, map_pow, hP, G'.hillePhillips_inr]
          rw [C0Semigroup.hillePhillipsKernel_translate, e1, hS]
          rfl
  rw [show (n : ℝ) * τ = τ * n by ring, G.S_mul_natCast hτ.le n, ← sub_apply,
    pow_sub_pow_eq_sum_pow_mul_sub_mul_pow, _root_.sum_apply, sum_congr rfl fun j _ => hterm j _,
    ← smul_sum]
  congr 1
  change _ = (G'.hillePhillipsKernelHom hM' (∑ j ∈ range n, HalfLineKernel.translate _ _ _))
    (u (p + 1))
  rw [map_sum, _root_.sum_apply]
  rfl

/-- **Brenner–Thomée's smooth-data error estimate on Banach spaces**: for an A-stable rational
scheme `r` of order `p`, a bounded semigroup `‖S(t)‖ ≤ M` on a complex Banach space with
generator `A`, `τ > 0`, every `n` and `x ∈ D(A^{p+1})` (a chain `u` in the graph of `A`),

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C M nτ τᵖ ‖A^{p+1} x‖`,

`C = sharpConst r p` depending only on `r` and `p`; `r(τA) = P(R) Q(R)⁻¹` through the resolvent
`R = (1 - τA)⁻¹` (`C0Semigroup.laplaceResolvent`); over `ℝ` or `ℂ` and for every such `R`,
`norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`. [BrennerThomee1979];
[GomilkoTomilov2024], Thm 1.1(ii) -/
theorem norm_resolventStep_pow_sub_S_le_sharp {r : RationalScheme} (hr : r.IsAStable) {p : ℕ}
    (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep (G.laplaceResolvent hM τ hτ.le) ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      r.sharpConst p * M * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  rw [r.resolventStep_pow_sub_S_apply G hM hp hτ n hu, norm_smul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hτ]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  have h1 := ((G.dilate τ hτ.le).hillePhillipsKernel (G.norm_dilate_S_le hM hτ.le)
    (HalfLineAlgebra.errorKernel r.hpMeasure (r.consistencyKernel p) n)).le_opNorm (u (p + 1))
  have h2 := (G.dilate τ hτ.le).norm_hillePhillipsKernel_le (G.norm_dilate_S_le hM hτ.le)
    (HalfLineAlgebra.errorKernel r.hpMeasure (r.consistencyKernel p) n)
  have h3 := integral_norm_errorKernel_le hr hp n
  calc τ ^ (p + 1) * ‖(G.dilate τ hτ.le).hillePhillipsKernel (G.norm_dilate_S_le hM hτ.le)
        (HalfLineAlgebra.errorKernel r.hpMeasure (r.consistencyKernel p) n) (u (p + 1))‖
      ≤ τ ^ (p + 1) * (M * (r.sharpConst p * n) * ‖u (p + 1)‖) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_right (h2.trans
          (mul_le_mul_of_nonneg_left h3 hM0)) (norm_nonneg _))
    _ = _ := by ring

end Semigroup

end RationalScheme

end TimeStepping

end Feec
