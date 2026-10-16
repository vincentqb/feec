module

public import Feec.Ch2.Linearized
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Repair of thesis Prop 2.6 (TT gauge for plane waves): the existence statement

[QuennevilleBelair2015, §2.8, Prop 2.6] claims: every plane wave `h̄_ab = A_ab f(k·x)` of
Prop 2.5 with `k^a = κ(1, 0, 0, 1)` is gauge-related, via `ξ_a = B_a g(k·x)` with `g' = f` and
the printed `B`, to a plane wave `A'_ab f(k·x)` satisfying the TT conditions (2.12) with
`u = (1, 0, 0, 0)`.

Defect: the printed `B` has the wrong sign (the derivation uses `η₀₀ = +1`, `k₀ = +κ`, against
the signature (−+++)); it fails under both index readings (`Feec.Linearized.thesis_gauge_fails`,
`Feec.Linearized.thesis_gauge_fails_contra`). Also `κ ≠ 0` is used (division by `κ`) but not
stated.

Repair (this file): the existence statement itself, `prop_2_6`. For `κ ≠ 0` and every `f ∈ C²`
there is a `C³` gauge vector `ξ` (namely `ξ_b = (Bcorr κ A)_b g(k·x)` with
`g(t) = ∫₀ᵗ f`, the fundamental theorem of calculus supplying `g' = f`) and a TT amplitude
`A' = ttAmp ((A₁₁ − A₂₂)/2) A₁₂` with `h̄ − (2∂_(a ξ_b) − η_ab ∂·ξ) = A' f(k·x)`; the result is a
Lorentz-gauge solution of `□h̄' = 0`, and its trace reversal solves `H = 0`. The same gauge
change stated on `h = trRev h̄` (`h ↦ h − 2∂_(a ξ_b)`) is `prop_2_6_metric`.

The algebra is `Feec.Linearized.tt_gauge`, the field-level identity for a given antiderivative is
`Feec.Linearized.tt_gauge_fun`; this file adds the FTC step and bundles the conclusions.
-/

@[expose] public noncomputable section

namespace Feec.Repair.C2

open Feec.Linearized Finset

/-- The antiderivative `g(t) = ∫₀ᵗ f` used to build the gauge vector of Prop 2.6. -/
def antideriv (f : ℝ → ℝ) : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f s

/-- FTC: `g' = f` for continuous `f`. -/
lemma deriv_antideriv {f : ℝ → ℝ} (hf : Continuous f) : deriv (antideriv f) = f :=
  funext fun t => Continuous.deriv_integral f hf 0 t

lemma differentiable_antideriv {f : ℝ → ℝ} (hf : Continuous f) :
    Differentiable ℝ (antideriv f) := fun t =>
  (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt

/-- If `f ∈ C²` then `g = ∫₀ f ∈ C³`. -/
lemma contDiff_antideriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 3 (antideriv f) := by
  have hc : Continuous f := hf.continuous
  have := (contDiff_succ_iff_deriv (𝕜 := ℝ) (f := antideriv f) (n := 2)).mpr
    ⟨differentiable_antideriv hc, by simp, by rw [deriv_antideriv hc]; exact hf⟩
  exact this

/-- The gauge vector of Prop 2.6 (corrected): `ξ_b(z) = (Bcorr κ A)_b · g(k·z)`,
`g = ∫₀ f`. -/
def ttGaugeVec (κ : ℝ) (A : Sym2) (f : ℝ → ℝ) : Fin 4 → E4 → ℝ :=
  fun b z => Bcorr κ A b * antideriv f (phaseL (kTT κ) z)

lemma contDiff_ttGaugeVec (κ : ℝ) (A : Sym2) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (b : Fin 4) :
    ContDiff ℝ 3 (ttGaugeVec κ A f b) :=
  contDiff_const.mul ((contDiff_antideriv hf).comp (phaseL (kTT κ)).contDiff)

lemma dot_kTT (κ : ℝ) : dot (kTT κ) (kTT κ) = 0 := by
  simp [dot, kTT, Fin.sum_univ_four, η]

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
        (∀ x b d, Hfun (fun y => trRev (fun a b => A' a b * f (phaseL (kTT κ) y))) x b d = 0) := by
  have hc : Continuous f := hf.continuous
  have hTT := (tt_gauge hκ hA hker)
  have hIs : IsTT κ (ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2)) := hTT.1 ▸ hTT.2
  set A' := ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) with hA'
  obtain ⟨hbox, hdiv, hH⟩ := plane_wave (dot_kTT κ) hIs.symm hIs.lorentz hf
  refine ⟨_, rfl, contDiff_ttGaugeVec κ A hf, A', hIs, rfl, fun y => ?_, hbox, hdiv, hH⟩
  exact tt_gauge_fun hκ hA hker (differentiable_antideriv hc) (deriv_antideriv hc) y

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
      fun a b => ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) a b * f (phaseL (kTT κ) y) := by
  intro ξ h
  have hc : Continuous f := hf.continuous
  have e : (fun a b => A a b * f (phaseL (kTT κ) y)) - gaugeTR (ttGaugeVec κ A f) y =
      fun a b => ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) a b * f (phaseL (kTT κ) y) :=
    tt_gauge_fun hκ hA hker (differentiable_antideriv hc) (deriv_antideriv hc) y
  have h1 : (fun a b => h a b - pd a (ξ b) y - pd b (ξ a) y) =
      fun a b => h a b + (fun a b => -pd a (ξ b) y) a b + (fun a b => -pd a (ξ b) y) b a := by
    funext a b; ring
  rw [h1, trRev_gauge, trRev_trRev, ← e]
  funext a b
  simp only [Pi.sub_apply, gaugeTR, ξ, sum_neg_distrib, mul_neg]
  ring

end Feec.Repair.C2
