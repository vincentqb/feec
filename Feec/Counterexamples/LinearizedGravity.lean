module

public import Feec.Physics.LinearizedGravity.PlaneWave

/-!
# Linearized gravity: the printed formulas of §2.8 are false

Counterexamples to statements of thesis §2.8 as printed, for gravitational plane waves in
four-dimensional Minkowski space (`Feec.Physics.LinearizedGravity.PlaneWave` proves the corrected
statements):

* `not_Hjet_eq_neg_boxJ`: Prop 2.4(b), `H = -□h̄` in Lorentz gauge, fails for a symmetric jet in
  Lorentz gauge (the corrected identity is `Feec.LinearizedGravity.Hsym_lorentz`);
* `not_isTT_gaugeAmp_printed`, `not_isTT_gaugeAmp_printed_contra`: the gauge vector printed in
  Prop 2.6 (covariant and contravariant readings) does not reach TT gauge (corrected:
  `Feec.LinearizedGravity.tt_gauge`);
* `not_accel_printed`: the accelerations printed after (2.15) are wrong (corrected:
  `Feec.LinearizedGravity.tt_accel`).

## References

* [QuennevilleBelair2015], §2.8 (Props 2.4, 2.6, (2.15))
* [Wald1984], §4.4
-/

open Finset Matrix
open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.Counterexamples.LinearizedGravity

open Feec.LinearizedGravity

/-- The thesis' gauge vector `B` (Prop 2.6) does **not** reach TT gauge: for `κ = 1` and an
admissible symmetric `A` with `A k = 0`, the transformed amplitude is not transverse.
`BPrinted` uses the covariant reading of the printed `B`; `not_isTT_gaugeAmp_printed_contra` covers
the contravariant reading.

See [QuennevilleBelair2015], Prop 2.6. -/
theorem not_isTT_gaugeAmp_printed :
    ∃ κ : ℝ, ∃ A : Matrix (Fin 4) (Fin 4) ℝ, κ ≠ 0 ∧ (∀ i j, A i j = A j i) ∧
      (∀ a, ∑ b, A a b * raise (kTT κ) b = 0) ∧ ¬ IsTT κ (gaugeAmp (kTT κ) A (BPrinted κ A)) := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, -1; 0, 0, 0, 0; 0, 0, 0, 0; -1, 0, 0, 1]
  refine ⟨1, A, one_ne_zero, fun i j => by fin_cases i <;> fin_cases j <;> rfl, fun a => by
    fin_cases a <;> simp [A, raise, kTT, Fin.sum_univ_four, Metric.minkowski4], fun h => ?_⟩
  have := h.transverse 0
  simp [A, gaugeAmp, BPrinted, kTT, dot_η4, trace_η4, η4_apply, uObs, Fin.sum_univ_four,
    Metric.minkowski4] at this
  norm_num at this

/-- The thesis' gauge vector read as **contravariant** components `B^a` (lowered to
`B_a = η_aa B^a`) also fails to reach TT gauge, on the same witness.

See [QuennevilleBelair2015], Prop 2.6. -/
theorem not_isTT_gaugeAmp_printed_contra :
    ∃ κ : ℝ, ∃ A : Matrix (Fin 4) (Fin 4) ℝ, κ ≠ 0 ∧ (∀ i j, A i j = A j i) ∧
      (∀ a, ∑ b, A a b * raise (kTT κ) b = 0) ∧
        ¬ IsTT κ (gaugeAmp (kTT κ) A (raise (BPrinted κ A))) := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, -1; 0, 0, 0, 0; 0, 0, 0, 0; -1, 0, 0, 1]
  refine ⟨1, A, one_ne_zero, fun i j => by fin_cases i <;> fin_cases j <;> rfl, fun a => by
    fin_cases a <;> simp [A, raise, kTT, Fin.sum_univ_four, Metric.minkowski4], fun h => ?_⟩
  have := h.transverse 0
  simp [A, gaugeAmp, BPrinted, raise, kTT, dot_η4, trace_η4, η4_apply, uObs, Fin.sum_univ_four,
    Metric.minkowski4] at this
  norm_num at this

/-- The thesis' accelerations `a¹ = -(κ²/2)(A₊v¹ + Aₓv²) f(k·x)` (after (2.15)) are wrong:
for `f(t) = t²`, `κ = A₊ = v¹ = 1`, `Aₓ = 0` at `x = 0` the true value is `1`, not `0`.
Thesis: §2.8, after (2.15) -/
theorem not_accel_printed :
    ¬ ∀ (κ Ap Ax : ℝ) (f : ℝ → ℝ), ContDiff ℝ 2 f → ∀ (v : Fin 4 → ℝ) (x : Fin 4 → ℝ),
      accelJ (jet2 (fun y => Matrix.of fun a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) x)
        v 1 = -(κ ^ 2 / 2) * (Ap * v 1 + Ax * v 2) * f (phaseL (kTT κ) x) := by
  intro h
  have hf : ContDiff ℝ 2 (fun t : ℝ => t ^ 2) := contDiff_id.pow 2
  have h1 := h 1 1 0 _ hf ![0, 1, 0, 0] 0
  rw [(tt_accel_fun 1 1 0 hf ![0, 1, 0, 0] 0).1] at h1
  have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t; simp
  simp [hd] at h1

/-- The thesis' Prop 2.4(b), `H = -□h̄` in Lorentz gauge, is false: a symmetric jet in
Lorentz gauge with `H₁₁ ≠ -□h̄₁₁`. Thesis: Prop 2.4 -/
theorem not_Hjet_eq_neg_boxJ :
    ∃ D : Jet2 (Fin 4) ℝ, IsSymJet2 D ∧ LorentzJet η4 η4 D ∧
      Hjet η4 η4 D 1 1 ≠ -boxJ η4 (barJ η4 η4 D) 1 1 := by
  -- `D = k ⊗ k ⊗ h` with `k = (1,0,0,0)`, `h = e₁ ⊗ e₁ - e₂ ⊗ e₂` (trace-free, `h̄ = h`).
  let h : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]
  have hs : hᵀ = h := by ext a b; fin_cases a <;> fin_cases b <;> rfl
  have hk : dot η4 ![1, 0, 0, 0] ![1, 0, 0, 0] = -1 := by
    simp [dot_η4, Fin.sum_univ_four, Metric.minkowski4]
  have htr : Metric.trRev η4 η4 h = h := by
    ext a b; rw [trRev_η4_apply]; fin_cases a <;> fin_cases b <;>
      simp [h, Fin.sum_univ_four, Metric.minkowski4]
  have hL : ∀ b, divSym η4 η4 ![1, 0, 0, 0] h b = 0 := fun b => by
    simp only [divSym, htr, mul_assoc, sum_η4]
    fin_cases b <;> simp [h, Fin.sum_univ_four, Metric.minkowski4]
  refine ⟨symbolJet ![1, 0, 0, 0] h, symbolJet_isSymJet2 _ hs,
    lorentzJet_symbolJet _ _ hL, ?_⟩
  rw [← Hsym, Hsym_lorentz η4_isSymm η4_mul_self _ hs hL, boxJ_symbolJet, hk, htr]
  simp [h, invOf_eq_inv]

end Feec.Counterexamples.LinearizedGravity

/-! ### Deprecated names -/

namespace Feec.LinearizedGravity

end Feec.LinearizedGravity
