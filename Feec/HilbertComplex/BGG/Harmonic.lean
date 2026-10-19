module

public import Feec.HilbertComplex.BGG.DiscreteWave

/-!
# BGG stability and convergence modulo finite-dimensional harmonic forms

The continuous hypotheses `Feec.BGG.Stability` of [QuennevilleBelair2015], Prop 5.3, require
exactness of both rows of the BGG data (5.1) at `V⁰`, `Ṽ⁰`, `V¹` and `Ṽ¹`. With boundary
conditions on part of the boundary (the mirror conditions of `Feec.Models.Cube.MirrorBGG`), the
rows carry harmonic forms: constants in the top row at `V⁰` (no boundary condition), and the
constant forms `dxₐ` in the components of the bottom row at `Ṽ¹`. This file isolates what the
Ch. 6 convergence theory of `Feec.HilbertComplex.BGG.EllipticProjection` and
`Feec.HilbertComplex.BGG.DiscreteWave` really uses, and generalizes it to finite-dimensional (in
fact arbitrary) harmonic spaces:

* the **top row plays no role** in the Strang bound of the elliptic projection (6.4) and in the
  wave rate (the mass term of the shifted form controls `σ`), so `poinc0` and `exact1` (which fail
  on the top row of the mirror complex) are not needed;
* on the bottom row only the Poincaré inequality on `Ṽ⁰` and a **Hodge decomposition modulo a
  space `𝔥 ⊆ Ṽ¹`** of harmonic forms are used, `v = dψ + w + k`, `‖w‖ ≤ C_p ‖dv‖`, `k ∈ 𝔥`, with
  `𝔥 ⊥ dṼ⁰` and `S₁ 𝔥 = 0` (for the mirror complex `𝔥 = span{dxₐ in the component a}`, whose
  `S₁ = 2 vskw` vanishes because diagonal matrices are symmetric);
* on the discrete side, `𝔥 ⊆ Ṽₕ¹` (the harmonic forms are discrete), so the discrete exactness at
  `Ṽₕ¹` holds modulo `𝔥` (`HarmonicStability.exact_bot_h`) and the harmonic part drops out of the
  consistency error of `S₁,ₕ` (`HarmonicStability.weakConsistency_of_regularPotential_of_bound`).

The results are the Strang bound, the rate of the elliptic projection and the end-to-end `O(h)`
convergence of (6.3) (`HarmonicStability.exists_discreteSolution_norm_sub_le_rate`) under
`HarmonicStability`, which `Stability` implies with `𝔥 = ⊥` (`Stability.toHarmonicStability`).
The generalization is strict: `exists_harmonicStability_not_stability` gives data with
`HarmonicStability` and `𝔥 ≠ ⊥` for which `Stability` fails for every choice of constants.

## Main definitions

* `Feec.BGG.HarmonicStability D 𝔥 C_p C_S`: the continuous hypotheses modulo `𝔥`.

## Main results

* `Feec.BGG.Stability.toHarmonicStability`.
* `Feec.BGG.HarmonicStability.exact_bot_h`, `HarmonicStability.dt0_injective`,
  `HarmonicStability.toSegmentH_dt0_injective`.
* `Feec.BGG.HarmonicStability.weakConsistency_of_regularPotential_of_bound`: the weak consistency
  of `S₁,ₕ` from regular potentials, modulo `𝔥`.
* `Feec.BGG.HarmonicStability.strang_shiftedForm_h`, `HarmonicStability.strang_energy`,
  `HarmonicStability.strang_of_isEllipticProjection`,
  `HarmonicStability.norm_sub_embedH_ellipticProjection_le`: the Strang bound of (6.4).
* **`Feec.BGG.HarmonicStability.exists_discreteSolution_norm_sub_le_rate`**: `O(h)` convergence of
  (6.3) from the elliptic projection of the exact initial state.
* `Feec.BGG.exists_harmonicStability_not_stability`: non-vacuity and strictness.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 5.3, §6.2 ((6.3), (6.4), Prop 6.2), Thm 4.14
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3 (Hodge decomposition with harmonic forms, discrete harmonic forms)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002] (Strang lemma)
-/

open scoped RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace Feec.BGG

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]

/-- **The continuous hypotheses of the Ch. 6 convergence theory modulo harmonic forms** of the
bottom row, for BGG data `D` in the "type = domain with `W`-inner product" model:
* `poinct0`: the Poincaré inequality on `Ṽ⁰` (exactness at `Ṽ⁰`);
* `hodget1`: the Hodge decomposition on `Ṽ¹` modulo `𝔥`: `v = dψ + w + k`, `k ∈ 𝔥`,
  `‖w‖ ≤ C_p ‖dv‖`;
* `harmonic_orth`, `S1_harmonic`: `𝔥 ⊥ dṼ⁰` and `S₁ 𝔥 = 0`;
* `boundS1`: `S₁ : Ṽ¹ → W²` is bounded in the graph norm.
Nothing is assumed on the top row. With `𝔥 = ⊥` these are fields of `Stability`
(`Stability.toHarmonicStability`). See [QuennevilleBelair2015], Prop 5.3; cf. [AFW2010], §3. -/
structure HarmonicStability (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) (Hh : Submodule ℝ Vt1)
    (Cp CS : ℝ) : Prop where
  Cp_nonneg : 0 ≤ Cp
  CS_nonneg : 0 ≤ CS
  poinct0 : ∀ φ, ‖φ‖ ≤ Cp * ‖D.dt0 φ‖
  hodget1 : ∀ v, ∃ ψ w, ∃ k ∈ Hh, v = D.dt0 ψ + w + k ∧ ‖w‖ ≤ Cp * ‖D.dt1 v‖
  harmonic_orth : ∀ k ∈ Hh, ∀ ψ, ⟪k, D.dt0 ψ⟫ = 0
  S1_harmonic : ∀ k ∈ Hh, D.S1 k = 0
  boundS1 : ∀ v, ‖D.S1 v‖ ^ 2 ≤ CS ^ 2 * graphSq D.dt1 v

/-- `Stability` gives the hypotheses modulo the zero harmonic space. -/
theorem Stability.toHarmonicStability {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Cp CR CS : ℝ}
    (H : Stability D Cp CR CS) : HarmonicStability D ⊥ Cp CS where
  Cp_nonneg := H.Cp_nonneg
  CS_nonneg := H.CS_nonneg
  poinct0 := H.poinct0
  hodget1 v := by
    obtain ⟨ψ, w, hv, hw⟩ := H.hodget1 v
    exact ⟨ψ, w, 0, Submodule.zero_mem _, by rw [hv, add_zero], hw⟩
  harmonic_orth k hk ψ := by rw [(Submodule.mem_bot ℝ).1 hk, inner_zero_left]
  S1_harmonic k hk := by rw [(Submodule.mem_bot ℝ).1 hk, map_zero]
  boundS1 := H.boundS1

namespace HarmonicStability

variable {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Hh : Submodule ℝ Vt1} {Cp CS : ℝ}
  (HS : HarmonicStability D Hh Cp CS)
include HS

/-- `d` is injective on `Ṽ⁰`. -/
theorem dt0_injective : Function.Injective D.dt0 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  have := HS.poinct0 φ
  rw [hφ, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- `‖dψ‖ ≤ ‖dψ + k‖` for `k ∈ 𝔥` (`𝔥 ⊥ dṼ⁰`). -/
theorem norm_dt0_le_norm_add (ψ : Vt0) {k : Vt1} (hk : k ∈ Hh) :
    ‖D.dt0 ψ‖ ≤ ‖D.dt0 ψ + k‖ := by
  have h0 : ⟪D.dt0 ψ, k⟫ = 0 := by rw [real_inner_comm]; exact HS.harmonic_orth k hk ψ
  have e := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (D.dt0 ψ) k h0
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  nlinarith [sq_nonneg ‖k‖]

variable {Q : Discrete D}

/-- **Discrete exactness at `Ṽₕ¹` modulo the harmonic forms**: if `𝔥 ⊆ Ṽₕ¹`, every discrete
`u` with `du = 0` is `dχ + k` with `χ ∈ Ṽₕ⁰`, `k ∈ 𝔥` (the cochain projections preserve the
harmonic forms). See [AFW2010], §3.4 (discrete harmonic forms). -/
theorem exact_bot_h (hH : Hh ≤ Q.Vt1h) {u : Vt1} (hu : u ∈ Q.Vt1h) (hd : D.dt1 u = 0) :
    ∃ χ ∈ Q.Vt0h, ∃ k ∈ Hh, D.dt0 χ + k = u := by
  obtain ⟨ψ, w, k, hk, rfl, hw⟩ := HS.hodget1 u
  rw [hd, norm_zero, mul_zero] at hw
  have hw0 : w = 0 := norm_le_zero_iff.1 hw
  subst hw0
  refine ⟨Q.Pt0 ψ, Q.Pt0_mem ψ, k, hk, ?_⟩
  rw [add_zero] at hu ⊢
  have e := Q.Pt1_id _ hu
  rw [map_add, ← Q.commt0, Q.Pt1_id _ (hH hk)] at e
  exact e

/-- `d` is injective on `Ṽₕ⁰`. -/
theorem toSegmentH_dt0_injective : Function.Injective Q.toSegmentH.dt0 := fun a b hab =>
  Subtype.ext (HS.dt0_injective (by simpa [Discrete.toSegmentH, Subtype.ext_iff] using hab))

/-- `(S₁ − S₁,ₕ) k = 0` on the harmonic forms. -/
theorem S1_sub_S1h_harmonic {k : Vt1} (hk : k ∈ Hh) : (D.S1 - Q.S1h) k = 0 := by
  rw [LinearMap.sub_apply, Discrete.S1h_apply, HS.S1_harmonic k hk, map_zero, sub_zero]

open Discrete

/-- **Weak consistency of `S₁,ₕ` from regular potentials, modulo harmonic forms**: the bound of
`Feec.BGG.Discrete.weakConsistency_of_regularPotential` (with `z ∈ D(d¹*)` as a functional bound)
when the discrete exactness at `Ṽₕ¹` holds only modulo `𝔥 ⊆ Ṽₕ¹`: the harmonic part `k` of
`v − Π̃¹Ry` has `(S₁ − S₁,ₕ)k = 0` and `‖dψ‖ ≤ ‖dψ + k‖` (`𝔥 ⊥ dṼ⁰`).
See [QuennevilleBelair2015], Thm 5.5 and Prop 5.9. -/
theorem weakConsistency_of_regularPotential_of_bound {CP : ℝ}
    (hH : Hh ≤ Q.Vt1h) (B : Q.Bounded CP) {Xr : Type*} [NormedAddCommGroup Xr]
    [NormedSpace ℝ Xr] {Cinc Creg h Capp : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (Rg : Q.RegularPotential Xr Cinc Creg Capp h)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * graphSq D.dt0 ψ)
    {z : W2} {M : ℝ} (hM : 0 ≤ M) (hz : ∀ w, |⟪z, D.d1 w⟫| ≤ M * ‖w‖) :
    ∀ v ∈ Q.Vt1h, |⟪z, (D.S1 - Q.S1h) v⟫| ≤
      Capp * h * weakConsistencyConst Cp CS CP Cinc Creg ‖z‖ M *
        √(graphSq D.dt1 v) := by
  intro v hv
  have hp := HS.Cp_nonneg; have hS := HS.CS_nonneg; have hP := B.CP_nonneg
  have hι := Rg.Cinc_nonneg; have hr := Rg.Creg_nonneg
  obtain ⟨y, hy1, hy2⟩ := Rg.exists_potential v hv
  set w := Rg.R y with hw
  set G := √(graphSq D.dt1 v) with hG
  have hvG : ‖v‖ ≤ G := (Real.le_sqrt (norm_nonneg _) (graphSq_nonneg _ _)).2 (by
    unfold graphSq; nlinarith [sq_nonneg ‖D.dt1 v‖])
  have hdG : ‖D.dt1 v‖ ≤ G := (Real.le_sqrt (norm_nonneg _) (graphSq_nonneg _ _)).2 (by
    unfold graphSq; nlinarith [sq_nonneg ‖v‖])
  have hdv : D.dt1 v ∈ Q.Wt2h := Q.dt1_mem v hv
  have hdPw : D.dt1 (Q.Pt1 w) = D.dt1 v := by rw [Q.commt1, hy1, Q.Pt2_id _ hdv]
  have hker : D.dt1 (v - Q.Pt1 w) = 0 := by rw [map_sub, hdPw, sub_self]
  obtain ⟨ψ, hψ, k, hk, hψeq⟩ := HS.exact_bot_h hH (Submodule.sub_mem _ hv (Q.Pt1_mem w)) hker
  have hsplit : (D.S1 - Q.S1h) v = D.d1 (Q.S0h ψ - D.S0 ψ) +
      ((D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)) := by
    calc (D.S1 - Q.S1h) v = (D.S1 - Q.S1h) (D.dt0 ψ + k + w - (w - Q.Pt1 w)) := by
          congr 1; rw [hψeq]; abel
      _ = _ := by
          rw [map_sub, map_add, map_add, S1_sub_S1h_dt0, HS.S1_sub_S1h_harmonic hk]; abel
  have hgrad : |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫| ≤
      M * (Capp * h * √(graphSq D.dt0 ψ)) := by
    refine (hz _).trans (mul_le_mul_of_nonneg_left ?_ hM)
    rw [norm_sub_rev]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (graphSq_nonneg _ _)]; exact happ0 ψ hψ
  have hψg : √(graphSq D.dt0 ψ) ≤ √(1 + Cp ^ 2) * ‖D.dt0 ψ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (D.dt0 ψ)), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := pow_le_pow_left₀ (norm_nonneg _) (HS.poinct0 ψ) 2
    unfold graphSq; nlinarith
  have hwn : ‖w‖ ≤ Cinc * Creg * ‖D.dt1 v‖ := (Rg.norm_R_le y).trans (by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hy2 hι)
  have hPw : ‖Q.Pt1 w‖ ≤ CP * (1 + Cinc * Creg) * ‖D.dt1 v‖ := by
    have hg := B.Pt1 w
    have hgw : graphSq D.dt1 w ≤ ((1 + Cinc * Creg) * ‖D.dt1 v‖) ^ 2 := by
      unfold graphSq; rw [hy1]
      have := pow_le_pow_left₀ (norm_nonneg _) hwn 2
      nlinarith [norm_nonneg (D.dt1 v), mul_nonneg (mul_nonneg hι hr) (norm_nonneg (D.dt1 v))]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    calc ‖Q.Pt1 w‖ ^ 2 ≤ graphSq D.dt1 (Q.Pt1 w) := by
          unfold graphSq; nlinarith [sq_nonneg ‖D.dt1 (Q.Pt1 w)‖]
      _ ≤ CP ^ 2 * graphSq D.dt1 w := hg
      _ ≤ CP ^ 2 * ((1 + Cinc * Creg) * ‖D.dt1 v‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hdψ : ‖D.dt0 ψ‖ ≤ (1 + CP * (1 + Cinc * Creg)) * G := by
    refine (HS.norm_dt0_le_norm_add ψ hk).trans ?_
    rw [hψeq]
    calc ‖v - Q.Pt1 w‖ ≤ ‖v‖ + ‖Q.Pt1 w‖ := norm_sub_le _ _
      _ ≤ G + CP * (1 + Cinc * Creg) * G :=
          add_le_add hvG (hPw.trans (mul_le_mul_of_nonneg_left hdG (by positivity)))
      _ = _ := by ring
  have hx : D.dt1 (w - Q.Pt1 w) = 0 := by rw [map_sub, hdPw, hy1, sub_self]
  have hSx : ‖(D.S1 - Q.S1h) (w - Q.Pt1 w)‖ ≤ (1 + CP) * CS * (Capp * h * ‖y‖) := by
    have hS1x : ‖D.S1 (w - Q.Pt1 w)‖ ≤ CS * ‖w - Q.Pt1 w‖ := by
      have := HS.boundS1 (w - Q.Pt1 w)
      unfold graphSq at this; rw [hx, norm_zero] at this
      refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
      rw [mul_pow]; simpa using this
    rw [LinearMap.sub_apply, S1h_apply]
    calc ‖D.S1 (w - Q.Pt1 w) - Q.P2 (D.S1 (w - Q.Pt1 w))‖
        ≤ ‖D.S1 (w - Q.Pt1 w)‖ + ‖Q.P2 (D.S1 (w - Q.Pt1 w))‖ := norm_sub_le _ _
      _ ≤ ‖D.S1 (w - Q.Pt1 w)‖ + CP * ‖D.S1 (w - Q.Pt1 w)‖ := add_le_add le_rfl (B.P2 _)
      _ = (1 + CP) * ‖D.S1 (w - Q.Pt1 w)‖ := by ring
      _ ≤ (1 + CP) * (CS * ‖w - Q.Pt1 w‖) :=
          mul_le_mul_of_nonneg_left hS1x (by linarith)
      _ ≤ (1 + CP) * (CS * (Capp * h * ‖y‖)) := by
          gcongr; exact Rg.approx_Pt1 y
      _ = _ := by ring
  have hco : ‖(D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)‖ ≤
      (1 + (1 + CP) * CS) * (Capp * h) * (Creg * G) := by
    have hyG : ‖y‖ ≤ Creg * G := hy2.trans (mul_le_mul_of_nonneg_left hdG hr)
    calc _ ≤ ‖(D.S1 - Q.S1h) w‖ + ‖(D.S1 - Q.S1h) (w - Q.Pt1 w)‖ := norm_sub_le _ _
      _ ≤ Capp * h * ‖y‖ + (1 + CP) * CS * (Capp * h * ‖y‖) := add_le_add (Rg.approx_S1 y) hSx
      _ = (1 + (1 + CP) * CS) * (Capp * h) * ‖y‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hyG (by positivity)
  rw [hsplit, inner_add_right]
  calc |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫ + ⟪z, (D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)⟫|
      ≤ |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫|
        + |⟪z, (D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)⟫| := abs_add_le _ _
    _ ≤ M * (Capp * h * √(graphSq D.dt0 ψ))
        + ‖z‖ * ((1 + (1 + CP) * CS) * (Capp * h) * (Creg * G)) :=
        add_le_add hgrad ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left hco (norm_nonneg _)))
    _ ≤ M * (Capp * h * (√(1 + Cp ^ 2) * ((1 + CP * (1 + Cinc * Creg)) * G)))
        + ‖z‖ * ((1 + (1 + CP) * CS) * (Capp * h) * (Creg * G)) := by
        gcongr
        exact hψg.trans (mul_le_mul_of_nonneg_left hdψ (Real.sqrt_nonneg _))
    _ = _ := by unfold weakConsistencyConst; ring

/-- **Strang bound for the elliptic projection (6.4) modulo harmonic forms**: the bound of
`Feec.BGG.Discrete.strang_shiftedForm_h`, whose proof only uses the Poincaré inequality on `Ṽ⁰`
(through `‖ψ‖_V ≤ √(1 + C_p²) ‖dψ‖`): no exactness of the top row, none of the bottom row at
`Ṽ¹`. See [QuennevilleBelair2015], §6.2, (6.4); cf. [Ciarlet2002]. -/
theorem strang_shiftedForm_h (h54 : Q.Compatible)
    {σ : V0} {φ : Vt0} {u : Vt1} {M : W2} {ρ : Wt2} (c3 : D.d0 σ = D.S0 φ)
    (ℓ : V1 →ₗ[ℝ] ℝ) {K0 K1 : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪M, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    {σP : V0} {φP : Vt0} {uP : Vt1} {MP : W2} {ρP : Wt2}
    (hσP : σP ∈ Q.V0h) (hφP : φP ∈ Q.Vt0h) (huP : uP ∈ Q.Vt1h) (hMP : MP ∈ Q.W2h)
    (hρP : ρP ∈ Q.Wt2h) (hcons : D.d0 σP = Q.S0h φP)
    (heq : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, D.d0 τ = Q.S0h ψ → ∀ v ∈ Q.Vt1h, ∀ N ∈ Q.W2h,
      ∀ μ ∈ Q.Wt2h, Q.shiftedFormH σP φP uP MP ρP τ ψ v N μ =
        shiftedFormC D σ φ u M ρ τ ψ v N μ - ℓ (D.d0 τ - D.S0 ψ)) :
    Q.shiftedNormSq (σP - Q.P0 σ) (φP - Q.Pt0 φ) (uP - Q.Pt1 u) (MP - Q.P2 M) (ρP - Q.Pt2 ρ)
      ≤ strangConst Cp * Q.strangData σ φ u M ρ K0 K1 := by
  have hp := HS.Cp_nonneg
  -- the discrete error `e = xₚ − Πx ∈ Kₕ`
  set eσ := σP - Q.P0 σ with heσ
  set eφ := φP - Q.Pt0 φ with heφ
  set eu := uP - Q.Pt1 u with heu
  set eM := MP - Q.P2 M with heM
  set eρ := ρP - Q.Pt2 ρ with heρ
  have heσm : eσ ∈ Q.V0h := Submodule.sub_mem _ hσP (Q.P0_mem σ)
  have heφm : eφ ∈ Q.Vt0h := Submodule.sub_mem _ hφP (Q.Pt0_mem φ)
  have heum : eu ∈ Q.Vt1h := Submodule.sub_mem _ huP (Q.Pt1_mem u)
  have heMm : eM ∈ Q.W2h := Submodule.sub_mem _ hMP (Q.P2_mem M)
  have heρm : eρ ∈ Q.Wt2h := Submodule.sub_mem _ hρP (Q.Pt2_mem ρ)
  have hΓe : D.d0 eσ = Q.S0h eφ := by
    rw [heσ, heφ, map_sub, map_sub, Q.comm0, c3, hcons, S0h_apply, S0h_apply, h54]
  have hSe := S1h_dt0_eq_zero hΓe
  -- the test function
  set v := eu + D.dt0 eφ with hv
  set N := eM - Q.S1h eu with hN
  set μ := eρ - D.dt1 eu with hμ
  have hvm : v ∈ Q.Vt1h := Submodule.add_mem _ heum (Q.dt0_mem _ heφm)
  have hNm : N ∈ Q.W2h := Submodule.sub_mem _ heMm (Q.S1h_mem eu)
  have hμm : μ ∈ Q.Wt2h := Submodule.sub_mem _ heρm (Q.dt1_mem _ heum)
  have hSv : Q.S1h v = Q.S1h eu := by rw [hv, map_add, hSe, add_zero]
  have hdv : D.dt1 v = D.dt1 eu := by rw [hv, map_add, D.dt1_dt0, add_zero]
  -- the residual
  have hE := heq eσ heσm eφ heφm hΓe v hvm N hNm μ hμm
  have hres : Q.shiftedFormH eσ eφ eu eM eρ eσ eφ v N μ =
      ⟪σ - Q.P0 σ, eσ⟫ + ⟪u - Q.Pt1 u, v⟫ - ⟪u - Q.Pt1 u, D.dt0 eφ⟫ + ⟪M - Q.P2 M, N⟫
      + ⟪M - Q.P2 M, Q.S1h v⟫ + ⟪ρ - Q.Pt2 ρ, μ⟫ + ⟪ρ - Q.Pt2 ρ, D.dt1 v⟫
      + ⟪D.dt0 (φ - Q.Pt0 φ), v⟫ + ⟪M, (D.S1 - Q.S1h) v⟫ - ⟪(D.S1 - Q.S1h) u, N⟫
      - ⟪Q.S1h (u - Q.Pt1 u), N⟫ - ⟪D.dt1 (u - Q.Pt1 u), μ⟫ + ℓ ((D.S0 - Q.S0h) eφ) := by
    have hlin : Q.shiftedFormH eσ eφ eu eM eρ eσ eφ v N μ =
        Q.shiftedFormH σP φP uP MP ρP eσ eφ v N μ -
          Q.shiftedFormH (Q.P0 σ) (Q.Pt0 φ) (Q.Pt1 u) (Q.P2 M) (Q.Pt2 ρ) eσ eφ v N μ := by
      simp only [shiftedFormH, heσ, heφ, heu, heM, heρ, map_sub, inner_sub_left]; ring
    rw [hlin, hE, hΓe]
    simp only [shiftedFormC, shiftedFormH, map_sub, LinearMap.sub_apply, inner_sub_left,
      inner_sub_right]
    ring
  -- coercivity
  have hcoer := shiftedNormSq_le_shiftedFormH_test eu eM eρ hΓe
  -- term-by-term bounds
  set n2 := Q.shiftedNormSq eσ eφ eu eM eρ with hn2
  have hn0 : 0 ≤ n2 := Q.shiftedNormSq_nonneg _ _ _ _ _
  have hns : ‖eσ‖ ^ 2 + ‖eu‖ ^ 2 + ‖eM‖ ^ 2 + ‖eρ‖ ^ 2 + ‖D.dt0 eφ‖ ^ 2 + ‖Q.S1h eu‖ ^ 2
      + ‖D.dt1 eu‖ ^ 2 = n2 := rfl
  have s1 := sq_nonneg ‖eσ‖; have s2 := sq_nonneg ‖eu‖; have s3 := sq_nonneg ‖eM‖
  have s4 := sq_nonneg ‖eρ‖; have s5 := sq_nonneg ‖D.dt0 eφ‖; have s6 := sq_nonneg ‖Q.S1h eu‖
  have s7 := sq_nonneg ‖D.dt1 eu‖
  set K := 2 + Cp ^ 2 with hK
  have hK0' : 0 < K := by positivity
  have hKn : ∀ {a : ℝ}, a ≤ 2 * n2 → a ≤ K * n2 := fun h =>
    h.trans (mul_le_mul_of_nonneg_right (by nlinarith) hn0)
  have hv2 : ‖v‖ ^ 2 ≤ K * n2 := hKn (by
    have := norm_add_sq_le_two_mul eu (D.dt0 eφ); linarith)
  have hN2 : ‖N‖ ^ 2 ≤ K * n2 := hKn (by
    have := norm_sub_sq_le_two_mul eM (Q.S1h eu); linarith)
  have hμ2 : ‖μ‖ ^ 2 ≤ K * n2 := hKn (by
    have := norm_sub_sq_le_two_mul eρ (D.dt1 eu); linarith)
  have hτ2 : ‖eσ‖ ^ 2 ≤ K * n2 := hKn (by linarith)
  have hdψ2 : ‖D.dt0 eφ‖ ^ 2 ≤ K * n2 := hKn (by linarith)
  have hSv2 : ‖Q.S1h v‖ ^ 2 ≤ K * n2 := hKn (by rw [hSv]; linarith)
  have hdv2 : ‖D.dt1 v‖ ^ 2 ≤ K * n2 := hKn (by rw [hdv]; linarith)
  have hgv2 : √(Q.gnSq v) ^ 2 ≤ K * n2 := by
    rw [Real.sq_sqrt (Q.gnSq_nonneg v)]
    refine hKn ?_
    unfold gnSq; rw [hSv, hdv]
    have := norm_add_sq_le_two_mul eu (D.dt0 eφ); linarith
  have hgψ2 : √(graphSq D.dt0 eφ) ^ 2 ≤ K * n2 := by
    rw [Real.sq_sqrt (graphSq_nonneg _ _)]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (HS.poinct0 eφ) 2
    rw [mul_pow] at h2
    have := mul_le_mul_of_nonneg_left (show ‖D.dt0 eφ‖ ^ 2 ≤ n2 by linarith) (sq_nonneg Cp)
    unfold graphSq; nlinarith
  -- the data
  set rσ := ‖Q.P0 σ - σ‖
  set ru := ‖Q.Pt1 u - u‖
  set rM := ‖Q.P2 M - M‖
  set rρ := ‖Q.Pt2 ρ - ρ‖
  set rφ := ‖D.dt0 (Q.Pt0 φ - φ)‖
  set rS := ‖D.S1 u - Q.S1h u‖
  set rSu := ‖Q.S1h (Q.Pt1 u - u)‖
  set rdu := ‖D.dt1 (Q.Pt1 u - u)‖
  have b1 : ⟪σ - Q.P0 σ, eσ⟫ ≤ rσ * ‖eσ‖ := (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b2 : ⟪u - Q.Pt1 u, v⟫ ≤ ru * ‖v‖ := (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b3 : -⟪u - Q.Pt1 u, D.dt0 eφ⟫ ≤ ru * ‖D.dt0 eφ‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans_eq (by rw [norm_sub_rev])
  have b4 : ⟪M - Q.P2 M, N⟫ ≤ rM * ‖N‖ := (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b5 : ⟪M - Q.P2 M, Q.S1h v⟫ ≤ rM * ‖Q.S1h v‖ :=
    (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b6 : ⟪ρ - Q.Pt2 ρ, μ⟫ ≤ rρ * ‖μ‖ := (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b7 : ⟪ρ - Q.Pt2 ρ, D.dt1 v⟫ ≤ rρ * ‖D.dt1 v‖ :=
    (real_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  have b8 : ⟪D.dt0 (φ - Q.Pt0 φ), v⟫ ≤ rφ * ‖v‖ :=
    (real_inner_le_norm _ _).trans_eq (by rw [← norm_neg, ← map_neg, neg_sub])
  have b9 : ⟪M, (D.S1 - Q.S1h) v⟫ ≤ K1 * √(Q.gnSq v) := (le_abs_self _).trans (hK1 v hvm)
  have b10 : -⟪(D.S1 - Q.S1h) u, N⟫ ≤ rS * ‖N‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans_eq (by rw [LinearMap.sub_apply])
  have b11 : -⟪Q.S1h (u - Q.Pt1 u), N⟫ ≤ rSu * ‖N‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans_eq
      (by rw [← norm_neg, ← map_neg, neg_sub])
  have b12 : -⟪D.dt1 (u - Q.Pt1 u), μ⟫ ≤ rdu * ‖μ‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans_eq
      (by rw [← norm_neg, ← map_neg, neg_sub])
  have b13 : ℓ ((D.S0 - Q.S0h) eφ) ≤ K0 * √(graphSq D.dt0 eφ) :=
    (le_abs_self _).trans (hK0 eφ heφm)
  have hsum : (1 / 2 : ℝ) * n2 ≤ ∑ i : Fin 13,
      (![rσ, ru, ru, rM, rM, rρ, rρ, rφ, K1, rS, rSu, rdu, K0] i) *
      (![‖eσ‖, ‖v‖, ‖D.dt0 eφ‖, ‖N‖, ‖Q.S1h v‖, ‖μ‖, ‖D.dt1 v‖, ‖v‖, √(Q.gnSq v), ‖N‖, ‖N‖,
        ‖μ‖, √(graphSq D.dt0 eφ)] i) := by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    have := hres ▸ hcoer
    linarith only [this, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]
  have hNb := Finset.univ.le_mul_sum_sq_of_mul_le_sum_mul _ _ (by norm_num : (0 : ℝ) < 1 / 2)
    hK0' (fun i _ => by
      fin_cases i
      · exact hτ2
      · exact hv2
      · exact hdψ2
      · exact hN2
      · exact hSv2
      · exact hμ2
      · exact hdv2
      · exact hv2
      · exact hgv2
      · exact hN2
      · exact hN2
      · exact hμ2
      · exact hgψ2) hsum
  have hcard : ((Finset.univ : Finset (Fin 13)).card : ℝ) + 1 = 14 := by
    rw [Finset.card_univ, Fintype.card_fin]; norm_num
  rw [hcard] at hNb
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero] at hNb
  have hdata : Q.strangData σ φ u M ρ K0 K1 = rσ ^ 2 + rφ ^ 2 + (ru ^ 2 + rSu ^ 2 + rdu ^ 2)
      + rM ^ 2 + rρ ^ 2 + K0 ^ 2 + K1 ^ 2 + rS ^ 2 := rfl
  rw [strangConst, hdata, ← hK]
  have hDD : rσ ^ 2 + ru ^ 2 + ru ^ 2 + rM ^ 2 + rM ^ 2 + rρ ^ 2
      + rρ ^ 2 + rφ ^ 2 + K1 ^ 2 + rS ^ 2 + rSu ^ 2 + rdu ^ 2 + K0 ^ 2 ≤
      2 * (rσ ^ 2 + rφ ^ 2 + (ru ^ 2 + rSu ^ 2 + rdu ^ 2) + rM ^ 2 + rρ ^ 2 + K0 ^ 2 + K1 ^ 2
        + rS ^ 2) := by
    have := sq_nonneg rσ; have := sq_nonneg rφ; have := sq_nonneg rSu; have := sq_nonneg rdu
    have := sq_nonneg K0; have := sq_nonneg K1; have := sq_nonneg rS
    linarith
  have hKD := mul_le_mul_of_nonneg_left hDD (by positivity : (0 : ℝ) ≤ 14 * K / (1 / 2) ^ 2)
  have : (14 : ℝ) * K / (1 / 2) ^ 2 = 56 * K := by norm_num; ring
  rw [this] at hNb hKD
  nlinarith only [hNb, hKD]

/-- **Strang bound in the energy norm** modulo harmonic forms
(`Feec.BGG.Discrete.strang_energy`). -/
theorem strang_energy (h54 : Q.Compatible)
    {σ : V0} {φ : Vt0} {u : Vt1} {M : W2} {ρ : Wt2} (c3 : D.d0 σ = D.S0 φ)
    (ℓ : V1 →ₗ[ℝ] ℝ) {K0 K1 : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪M, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    {σP : V0} {φP : Vt0} {uP : Vt1} {MP : W2} {ρP : Wt2}
    (hσP : σP ∈ Q.V0h) (hφP : φP ∈ Q.Vt0h) (huP : uP ∈ Q.Vt1h) (hMP : MP ∈ Q.W2h)
    (hρP : ρP ∈ Q.Wt2h) (hcons : D.d0 σP = Q.S0h φP)
    (heq : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, D.d0 τ = Q.S0h ψ → ∀ v ∈ Q.Vt1h, ∀ N ∈ Q.W2h,
      ∀ μ ∈ Q.Wt2h, Q.shiftedFormH σP φP uP MP ρP τ ψ v N μ =
        shiftedFormC D σ φ u M ρ τ ψ v N μ - ℓ (D.d0 τ - D.S0 ψ)) :
    ‖σ - σP‖ ^ 2 + ‖u - uP‖ ^ 2 + ‖M - MP‖ ^ 2 + ‖ρ - ρP‖ ^ 2 ≤
      2 * (strangConst Cp + 1) * Q.strangData σ φ u M ρ K0 K1 := by
  have hS := HS.strang_shiftedForm_h h54 c3 ℓ hK0 hK1 hσP hφP huP hMP hρP hcons heq
  have e1 := norm_sub_sq_le_split σ σP (Q.P0 σ)
  have e2 := norm_sub_sq_le_split u uP (Q.Pt1 u)
  have e3 := norm_sub_sq_le_split M MP (Q.P2 M)
  have e4 := norm_sub_sq_le_split ρ ρP (Q.Pt2 ρ)
  have hgn := Q.gnSq_nonneg (Q.Pt1 u - u)
  have hgn' : ‖Q.Pt1 u - u‖ ^ 2 ≤ Q.gnSq (Q.Pt1 u - u) := by
    unfold gnSq; nlinarith [sq_nonneg ‖Q.S1h (Q.Pt1 u - u)‖, sq_nonneg ‖D.dt1 (Q.Pt1 u - u)‖]
  have hD : ‖Q.P0 σ - σ‖ ^ 2 + ‖Q.Pt1 u - u‖ ^ 2 + ‖Q.P2 M - M‖ ^ 2 + ‖Q.Pt2 ρ - ρ‖ ^ 2 ≤
      Q.strangData σ φ u M ρ K0 K1 := by
    unfold strangData
    nlinarith [sq_nonneg ‖D.dt0 (Q.Pt0 φ - φ)‖, sq_nonneg K0, sq_nonneg K1,
      sq_nonneg ‖D.S1 u - Q.S1h u‖]
  have hn : ‖σP - Q.P0 σ‖ ^ 2 + ‖uP - Q.Pt1 u‖ ^ 2 + ‖MP - Q.P2 M‖ ^ 2 + ‖ρP - Q.Pt2 ρ‖ ^ 2 ≤
      Q.shiftedNormSq (σP - Q.P0 σ) (φP - Q.Pt0 φ) (uP - Q.Pt1 u) (MP - Q.P2 M)
        (ρP - Q.Pt2 ρ) := by
    unfold shiftedNormSq
    nlinarith [sq_nonneg ‖D.dt0 (φP - Q.Pt0 φ)‖, sq_nonneg ‖Q.S1h (uP - Q.Pt1 u)‖,
      sq_nonneg ‖D.dt1 (uP - Q.Pt1 u)‖]
  nlinarith only [hS, hD, hn, e1, e2, e3, e4]

/-- **Strang bound for the elliptic projection (6.4) of a discretization**, modulo harmonic
forms (`Feec.BGG.Discrete.strang_of_isEllipticProjection`). -/
theorem strang_of_isEllipticProjection (h54 : Q.Compatible) {σ : V0} {φ : Vt0} {u : Vt1} {M : W2} {ρ : Wt2}
    (c3 : D.d0 σ = D.S0 φ) (ℓ : V1 →ₗ[ℝ] ℝ) {K0 K1 : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪M, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    {x : ((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) × Q.V1h}
    (hx : IsEllipticProjection Q.toSegmentH (Q.ellipticDataH σ φ u M ρ ℓ) 0 x) :
    Q.shiftedNormSq ((x.1.1.1 : V0) - Q.P0 σ) ((x.1.2 : Vt0) - Q.Pt0 φ)
        ((x.1.1.2.1 : Vt1) - Q.Pt1 u) ((x.1.1.2.2.1 : W2) - Q.P2 M)
        ((x.1.1.2.2.2 : Wt2) - Q.Pt2 ρ) ≤ strangConst Cp * Q.strangData σ φ u M ρ K0 K1 ∧
      ‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 + ‖ρ - x.1.1.2.2.2‖ ^ 2 ≤
        2 * (strangConst Cp + 1) * Q.strangData σ φ u M ρ K0 K1 := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨⟨⟨σP, uP, MP, ρP⟩, φP⟩, lP⟩ := x
  have hcons : D.d0 σP = Q.S0h φP := by
    have := congrArg Subtype.val h2
    simpa [toSegmentH, sub_eq_zero] using this
  have heq : ∀ τ ∈ Q.V0h, ∀ ψ ∈ Q.Vt0h, D.d0 τ = Q.S0h ψ → ∀ v ∈ Q.Vt1h, ∀ N ∈ Q.W2h,
      ∀ μ ∈ Q.Wt2h, Q.shiftedFormH σP φP uP MP ρP τ ψ v N μ =
        shiftedFormC D σ φ u M ρ τ ψ v N μ - ℓ (D.d0 τ - D.S0 ψ) := by
    intro τ hτ ψ hψ hτψ v hv N hN μ hμ
    have e := h1 ((⟨τ, hτ⟩, ⟨v, hv⟩, ⟨N, hN⟩, ⟨μ, hμ⟩), ⟨ψ, hψ⟩)
    have h0 : Q.toSegmentH.d0 ⟨τ, hτ⟩ - Q.toSegmentH.S0 ⟨ψ, hψ⟩ = 0 :=
      Subtype.ext (by simp [toSegmentH, hτψ])
    rw [h0, inner_zero_right, sub_zero, energyInner_add_discreteSkewForm_toSegmentH] at e
    exact e
  exact ⟨HS.strang_shiftedForm_h h54 c3 ℓ hK0 hK1 σP.2 φP.2 uP.2 MP.2 ρP.2 hcons heq,
    HS.strang_energy h54 c3 ℓ hK0 hK1 σP.2 φP.2 uP.2 MP.2 ρP.2 hcons heq⟩

variable {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [AddCommGroup Z]
  [Module ℝ Z]

/-- **Rate of the elliptic projection, embedded**, modulo harmonic forms
(`Feec.BGG.Discrete.norm_sub_embedH_ellipticProjection_le`). -/
theorem norm_sub_embedH_ellipticProjection_le (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h]
    [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h] {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X}
    (hιc : IsEnergyEmbedding ιc) (hdinj : Function.Injective Q.toSegmentH.dt0)
    (hB : ∀ μ, ∃ τ ψ, Q.toSegmentH.d0 τ - Q.toSegmentH.S0 ψ = μ)
    {a : V0 × Vt1 × W2 × Wt2} {φ : Vt0} (c3 : D.d0 a.1 = D.S0 φ) (ℓ₁ : V1 →ₗ[ℝ] ℝ)
    {K0 K1 c h : ℝ}
    (hK0 : ∀ ψ ∈ Q.Vt0h, |ℓ₁ ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ v ∈ Q.Vt1h, |⟪a.2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : Q.strangData a.1 φ a.2.1 a.2.2.1 a.2.2.2 K0 K1 ≤ (c * h) ^ 2) :
    ‖ιc a - Q.embedH ιc (ellipticProjection Q.toSegmentH hdinj hB
        (ellipticRhs (Q.ellipticDataH a.1 φ a.2.1 a.2.2.1 a.2.2.2 ℓ₁) 0)).1.1‖ ≤
      √(2 * (strangConst Cp + 1)) * |c| * |h| := by
  have hx := isEllipticProjection_ellipticProjection hdinj hB
    (Q.ellipticDataH a.1 φ a.2.1 a.2.2.1 a.2.2.2 ℓ₁) 0
  have hS := (HS.strang_of_isEllipticProjection h54 c3 ℓ₁ hK0 hK1 hx).2
  have hC : 0 ≤ 2 * (strangConst Cp + 1) := by unfold strangConst; positivity
  rw [embedH_apply, norm_sub_of_isEnergyEmbedding hιc, mul_assoc, ← abs_mul,
    ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_left hdata hC))

/-- **End-to-end `O(h)` convergence of the semi-discrete BGG wave system (6.3) modulo harmonic
forms**: `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate` with `Stability` replaced by
`HarmonicStability` (no hypothesis on the top row; harmonic forms `𝔥` on the bottom row). The
discrete solution starts from the elliptic projection (6.4) of the exact initial state, and
`‖ιc a(t) − ι ξₕ(t)‖ ≤ √(2(strangConst C_p + 1)) |c| |h| (2 + 2t)`.
See [QuennevilleBelair2015], §6.2, (6.3), (6.4), Prop 6.2, and Thm 4.14. -/
theorem exists_discreteSolution_norm_sub_le_rate (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h]
    [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h] (hS : Function.Surjective Q.toSegmentH.S0)
    {ιc : (V0 × Vt1 × W2 × Wt2) →L[ℝ] X} (hιc : IsEnergyEmbedding ιc) (jc : Vt0 →ₗ[ℝ] Z)
    (A Ah : (X × Z) →ₗ[ℝ] (X × Z) →ₗ[ℝ] ℝ) (Bh : (X × Z) →ₗ[ℝ] Q.V1h)
    (hA : ∀ a φ (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h),
      A (ιc a, jc φ) (Q.embedH ιc b, jc ψ) = discreteSkewForm D (a, φ)
        (((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2)), (ψ : Vt0)))
    (hAh : ∀ a φ b ψ, Ah (Q.embedH ιc a, (jc ∘ₗ Q.Vt0h.subtype) φ)
      (Q.embedH ιc b, (jc ∘ₗ Q.Vt0h.subtype) ψ) = discreteSkewForm Q.toSegmentH (a, φ) (b, ψ))
    (hBh : ∀ a ψ, Bh (Q.embedH ιc a, (jc ∘ₗ Q.Vt0h.subtype) ψ) =
      Q.toSegmentH.d0 a.1 - Q.toSegmentH.S0 ψ)
    {T : ℝ} (hT : 0 < T) {f : ℝ → Q.Vt1h} (hf : ContinuousOn f (Icc 0 T))
    (a a' : ℝ → V0 × Vt1 × W2 × Wt2) (φ φ' : ℝ → Vt0) (ℓ₁ ℓ₁' : ℝ → V1 →ₗ[ℝ] ℝ)
    (ℓ : ℝ → (X × Z) →ₗ[ℝ] ℝ)
    (hℓ : ∀ t (b : Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) (ψ : Q.Vt0h),
      ℓ t (Q.embedH ιc b, jc ψ) = ℓ₁ t (D.d0 b.1 - D.S0 ψ))
    (F : ℝ → X) (hF : ∀ t ∈ Ico 0 T, ∀ b, ⟪F t, Q.embedH ιc b⟫ = ⟪f t, b.2.1⟫)
    (hac : ContinuousOn a (Icc 0 T)) (ha'c : ContinuousOn a' (Icc 0 T))
    (hcont : ∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((Q.embedH ιc : (Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) →ₗ[ℝ] X).prodMap
          (jc ∘ₗ Q.Vt0h.subtype)),
      ⟪ιc (a' t), η.1⟫ + A (ιc (a t), jc (φ t)) η - ℓ t η = ⟪F t, η.1⟫)
    (hGc : ∀ y, ContinuousOn
      (fun s => Q.ellipticDataH (a s).1 (φ s) (a s).2.1 (a s).2.2.1 (a s).2.2.2 (ℓ₁ s) y)
      (Icc 0 T))
    (hGd : ∀ t ∈ Ico 0 T, ∀ y, HasDerivWithinAt
      (fun s => Q.ellipticDataH (a s).1 (φ s) (a s).2.1 (a s).2.2.1 (a s).2.2.2 (ℓ₁ s) y)
      (Q.ellipticDataH (a' t).1 (φ' t) (a' t).2.1 (a' t).2.2.1 (a' t).2.2.2 (ℓ₁' t) y)
      (Ici t) t)
    (hG'c : ∀ y, ContinuousOn
      (fun s => Q.ellipticDataH (a' s).1 (φ' s) (a' s).2.1 (a' s).2.2.1 (a' s).2.2.2 (ℓ₁' s) y)
      (Icc 0 T))
    {K0 K1 c h : ℝ}
    (c3 : ∀ t ∈ Icc 0 T, D.d0 (a t).1 = D.S0 (φ t))
    (c3' : ∀ t ∈ Icc 0 T, D.d0 (a' t).1 = D.S0 (φ' t))
    (hK0 : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h, |ℓ₁ t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK0' : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h, |ℓ₁' t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h, |⟪(a t).2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hK1' : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h,
      |⟪(a' t).2.2.1, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : ∀ t ∈ Icc 0 T,
      Q.strangData (a t).1 (φ t) (a t).2.1 (a t).2.2.1 (a t).2.2.2 K0 K1 ≤ (c * h) ^ 2)
    (hdata' : ∀ t ∈ Icc 0 T,
      Q.strangData (a' t).1 (φ' t) (a' t).2.1 (a' t).2.2.1 (a' t).2.2.2 K0 K1 ≤ (c * h) ^ 2) :
    ∃ s : DiscreteSolution Q.toSegmentH T f,
      Q.embedH ιc (s.σ 0, s.u 0, s.M 0, s.ρ 0) =
        Q.embedH ιc (ellipticProjection Q.toSegmentH HS.toSegmentH_dt0_injective
          (exists_sub_eq_of_surjective hS) (ellipticRhs (Q.ellipticDataH (a 0).1 (φ 0)
            (a 0).2.1 (a 0).2.2.1 (a 0).2.2.2 (ℓ₁ 0)) 0)).1.1 ∧
      ∀ t ∈ Icc 0 T, ‖ιc (a t) - Q.embedH ιc (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
        √(2 * (strangConst Cp + 1)) * |c| * |h| * (2 + 2 * t) := by
  have hdinj := HS.toSegmentH_dt0_injective (Q := Q)
  set hB := exists_sub_eq_of_surjective hS
  set ι := Q.embedH ιc
  set j := jc ∘ₗ Q.Vt0h.subtype
  set G := fun s => Q.ellipticDataH (a s).1 (φ s) (a s).2.1 (a s).2.2.1 (a s).2.2.2 (ℓ₁ s)
    with hGdef
  set G' := fun s => Q.ellipticDataH (a' s).1 (φ' s) (a' s).2.1 (a' s).2.2.1 (a' s).2.2.2
    (ℓ₁' s) with hG'def
  have hGeq : ∀ s, ellipticData ι j A (ιc (a s)) (jc (φ s)) (ℓ s) = G s := fun s =>
    ellipticData_embedH hιc jc A hA (ℓ s) (ℓ₁ s) (hℓ s) (a s) (φ s)
  have hGeqf : (fun s => ellipticData ι j A (ιc (a s)) (jc (φ s)) (ℓ s)) = G := funext hGeq
  obtain ⟨s, hinit, -, hbd⟩ := exists_discreteSolution_norm_sub_le_ellipticProjection hdinj hS ι
    (embedH_inner hιc) j A Ah Bh hAh hBh hT hf (fun t => ιc (a t)) (fun t => ιc (a' t))
    (fun t => jc (φ t)) ℓ F hF (ιc.continuous.comp_continuousOn hac)
    (ιc.continuous.comp_continuousOn ha'c) hcont G'
    (fun y => by simpa only [hGeq] using hGc y)
    (fun t ht y => by simpa only [hGeq] using hGd t ht y) hG'c
  rw [hGeqf] at hinit hbd
  set ε := √(2 * (strangConst Cp + 1)) * |c| * |h|
  have hε : 0 ≤ ε := by positivity
  set p := projectedTrajectory hdinj hB ι G
  set p' := projectedTrajectory hdinj hB ι G'
  have hp : ∀ t, p t = ι (ellipticProjection Q.toSegmentH hdinj hB (ellipticRhs (G t) 0)).1.1 :=
    fun t => rfl
  have hp' : ∀ t,
      p' t = ι (ellipticProjection Q.toSegmentH hdinj hB (ellipticRhs (G' t) 0)).1.1 :=
    fun t => rfl
  set L : (((Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) × Q.V1h) →L[ℝ] X :=
    ι.comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))
  have hpc : ContinuousOn p (Icc 0 T) :=
    L.continuous.comp_continuousOn (continuousOn_ellipticProjection hdinj hB hGc)
  have hp'c : ContinuousOn p' (Icc 0 T) :=
    L.continuous.comp_continuousOn (continuousOn_ellipticProjection hdinj hB hG'c)
  have h1 : ∀ t ∈ Icc 0 T, ‖ιc (a t) - p t‖ ≤ ε := fun t ht => by
    rw [hp]
    exact HS.norm_sub_embedH_ellipticProjection_le h54 hιc hdinj hB (c3 t ht) (ℓ₁ t)
      (hK0 t ht) (hK1 t ht) (hdata t ht)
  have h3 : ∀ t ∈ Icc 0 T, ‖p' t - ιc (a' t)‖ ≤ ε := fun t ht => by
    rw [norm_sub_rev, hp']
    exact HS.norm_sub_embedH_ellipticProjection_le h54 hιc hdinj hB (c3' t ht) (ℓ₁' t)
      (hK0' t ht) (hK1' t ht) (hdata' t ht)
  refine ⟨s, hinit, ?_⟩
  refine norm_sub_le_mul_of_ellipticProjection_L2 (ξ := fun t => ιc (a t))
    (ξ' := fun t => ιc (a' t)) (ξh := fun t => ι (s.σ t, s.u t, s.M t, s.ρ t)) (p := p)
    (p' := p') (ιc.continuous.comp_continuousOn hac) (ιc.continuous.comp_continuousOn ha'c)
    hpc hp'c (fun t ht => ?_) h1 ?_ h3
  · have hb := hbd t ht
    have : 0 ≤ ‖p 0 - ι (s.σ 0, s.u 0, s.M 0, s.ρ 0)‖ := norm_nonneg _
    linarith
  · rw [show p 0 = ι (s.σ 0, s.u 0, s.M 0, s.ρ 0) from hinit.symm, sub_self, norm_zero]
    exact hε

end HarmonicStability

/-! ### Non-vacuity and strictness -/

/-- A BGG-type segment with a constant mode on the top row and a harmonic form on the bottom
row: `V⁰ = V¹ = W² = Ṽ¹ = W̃² = ℝ`, `Ṽ⁰ = 0`, all maps zero. -/
def harmonicExampleSegment : Segment ℝ ℝ ℝ ℝ (EuclideanSpace ℝ (Fin 0)) ℝ ℝ where
  d0 := 0
  d1 := 0
  dt0 := 0
  dt1 := 0
  S0 := 0
  S1 := 0
  d1_d0 _ := rfl
  dt1_dt0 _ := rfl
  anticomm _ := by simp

/-- **`HarmonicStability` is strictly weaker than `Stability` and non-vacuous**: the data
`harmonicExampleSegment`, with the nonzero harmonic space `𝔥 = Ṽ¹ = ℝ` contained in the
discrete space of the identity discretization, satisfy `HarmonicStability` with `C_p = 1`,
`C_S = 0`, while `Stability` fails for every choice of constants (the top row has the constant
mode `d⁰ = 0` on `V⁰ = ℝ`). -/
theorem exists_harmonicStability_not_stability :
    ∃ (D : Segment ℝ ℝ ℝ ℝ (EuclideanSpace ℝ (Fin 0)) ℝ ℝ) (Hh : Submodule ℝ ℝ),
      Hh ≠ ⊥ ∧ HarmonicStability D Hh 1 0 ∧ Hh ≤ (Discrete.top D).Vt1h ∧
        ∀ Cp CR CS, ¬ Stability D Cp CR CS := by
  refine ⟨harmonicExampleSegment, ⊤, top_ne_bot, ?_, le_top, fun Cp CR CS H => ?_⟩
  · exact
      { Cp_nonneg := zero_le_one
        CS_nonneg := le_rfl
        poinct0 := fun φ => by simp [Subsingleton.elim φ 0]
        hodget1 := fun v => ⟨0, 0, v, Submodule.mem_top, by simp, by simp⟩
        harmonic_orth := fun k _ ψ => by simp [harmonicExampleSegment]
        S1_harmonic := fun k _ => rfl
        boundS1 := fun v => by simp [harmonicExampleSegment, graphSq] }
  · have h := H.poinc0 1
    simp [harmonicExampleSegment] at h
    linarith

end Feec.BGG
