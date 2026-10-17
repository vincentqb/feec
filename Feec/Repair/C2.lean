module

public import Feec.Ch2.Linearized
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Repair of thesis Prop 2.6 (TT gauge for plane waves): the existence statement (shim)

Strangler shim over `Feec.Physics.LinearizedGravity.PlaneWave` (`exists_ttGauge`,
`trRev_sub_gauge_eq_ttAmp`, `ttGaugeVec`, `box_ttGaugeVec`). The declarations keep their old
statements.

## References

* [QuennevilleBelair2015], §2.8, Prop 2.6; [Wald1984], §4.4
-/

@[expose] public noncomputable section

namespace Feec.Repair.C2

open Feec.Linearized Finset

/-- The antiderivative `g(t) = ∫₀ᵗ f` used to build the gauge vector of Prop 2.6. -/
abbrev antideriv (f : ℝ → ℝ) : ℝ → ℝ :=
  LinearizedGravity.antideriv f

/-- FTC: `g' = f` for continuous `f`. -/
lemma deriv_antideriv {f : ℝ → ℝ} (hf : Continuous f) : deriv (antideriv f) = f :=
  LinearizedGravity.deriv_antideriv hf

lemma differentiable_antideriv {f : ℝ → ℝ} (hf : Continuous f) :
    Differentiable ℝ (antideriv f) :=
  LinearizedGravity.differentiable_antideriv hf

/-- If `f ∈ C²` then `g = ∫₀ f ∈ C³`. -/
lemma contDiff_antideriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 3 (antideriv f) :=
  LinearizedGravity.contDiff_antideriv hf

/-- The gauge vector of Prop 2.6 (corrected): `ξ_b(z) = (Bcorr κ A)_b · g(k·z)`,
`g = ∫₀ f`. -/
abbrev ttGaugeVec (κ : ℝ) (A : Sym2) (f : ℝ → ℝ) : Fin 4 → E4 → ℝ :=
  LinearizedGravity.ttGaugeVec κ A f

lemma contDiff_ttGaugeVec (κ : ℝ) (A : Sym2) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (b : Fin 4) :
    ContDiff ℝ 3 (ttGaugeVec κ A f b) :=
  LinearizedGravity.contDiff_ttGaugeVec κ A hf b

lemma dot_kTT (κ : ℝ) : dot (kTT κ) (kTT κ) = 0 :=
  LinearizedGravity.dot_kTT κ

/-- The gauge vector of Prop 2.6 is a residual gauge: `□ξ_b = 0`. Indeed `ξ_b = B_b g(k·x)`
with `k` null, so `□ξ_b = B_b (k·k) g''(k·x) = 0`. This is the step behind the thesis' remark
that the gauge change preserves the Lorentz gauge (`∂^a(2∂_(aξ_b) − η_ab ∂·ξ) = □ξ_b`). -/
lemma box_ttGaugeVec (κ : ℝ) (A : Sym2) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (b : Fin 4)
    (x : E4) : box (ttGaugeVec κ A f b) x = 0 :=
  LinearizedGravity.box_ttGaugeVec κ A hf b x

/-- **Thesis Prop 2.6, repaired** (existence of the TT gauge for a plane wave).

Original claim [QuennevilleBelair2015, Prop 2.6]: every plane wave `h̄_ab = A_ab f(k·x)` of
Prop 2.5 with `k^a = κ(1,0,0,1)` is gauge-related, via `ξ_a = B_a g(k·x)`, `g' = f`, with the
printed `B`, to a plane wave `A'_ab f(k·x)` satisfying the TT conditions (2.12).

Defect: the printed `B` does not reach TT gauge (`thesis_gauge_fails`,
`thesis_gauge_fails_contra`); `κ ≠ 0` is implicit.

Repair: for `κ ≠ 0`, `A` symmetric with `A_ab k^b = 0` and every `f ∈ C²` there exist a
`C³` gauge vector `ξ` — explicitly `ξ = ttGaugeVec κ A f`, i.e. `ξ_b = (Bcorr κ A)_b g(k·x)`
with `g = ∫₀ f`, `B = Bcorr` being minus the printed `B` — and an amplitude `A'` such that
* `A'` satisfies the TT conditions (2.12), and `A' = ttAmp ((A₁₁ − A₂₂)/2) A₁₂`;
* `h̄ − (2∂_(a ξ_b) − η_ab ∂^c ξ_c) = A' f(k·x)` pointwise;
* the new field is again a plane-wave solution of Prop 2.5: `□h̄' = 0`, `∂^a h̄'_ab = 0`, and
  its trace reversal satisfies the vacuum linearized equation `H(trRev h̄') = 0`.

See [QuennevilleBelair2015, Prop 2.6]; cf. [Wald1984, §4.4]. -/
theorem prop_2_6 {κ : ℝ} (hκ : κ ≠ 0) {A : Sym2} (hA : ∀ i j, A i j = A j i)
    (hker : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ ξ : Fin 4 → E4 → ℝ, ξ = ttGaugeVec κ A f ∧ (∀ a, ContDiff ℝ 3 (ξ a)) ∧
      ∃ A' : Sym2, IsTT κ A' ∧ A' = ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) ∧
        (∀ y, (fun a b => A a b * f (phaseL (kTT κ) y)) - gaugeTR ξ y =
          fun a b => A' a b * f (phaseL (kTT κ) y)) ∧
        (∀ x a b, box (fun y => A' a b * f (phaseL (kTT κ) y)) x = 0) ∧
        (∀ x b, divF (fun y a b => A' a b * f (phaseL (kTT κ) y)) x b = 0) ∧
        (∀ x b d, Hfun (fun y => trRev (fun a b => A' a b * f (phaseL (kTT κ) y))) x b d = 0) :=
  LinearizedGravity.exists_ttGauge hκ hA hker hf

/-- **Thesis Prop 2.6, repaired**, stated on the metric perturbation `h = trRev h̄` (the
thesis' gauge freedom `h ↦ h − 2∂_(a ξ_b)`, (2.5)): with the gauge vector of `prop_2_6`, the
trace reversal of `h − ∂_a ξ_b − ∂_b ξ_a` is the TT plane wave
`ttAmp ((A₁₁ − A₂₂)/2) A₁₂ · f(k·x)`.

See [QuennevilleBelair2015, Prop 2.6, (2.5)]. -/
theorem prop_2_6_metric {κ : ℝ} (hκ : κ ≠ 0) {A : Sym2} (hA : ∀ i j, A i j = A j i)
    (hker : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (y : E4) :
    let ξ := ttGaugeVec κ A f
    let h : Sym2 := trRev fun a b => A a b * f (phaseL (kTT κ) y)
    trRev (fun a b => h a b - pd a (ξ b) y - pd b (ξ a) y) =
      fun a b => ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) a b * f (phaseL (kTT κ) y) :=
  LinearizedGravity.trRev_sub_gauge_eq_ttAmp hκ hA hker hf y

end Feec.Repair.C2
