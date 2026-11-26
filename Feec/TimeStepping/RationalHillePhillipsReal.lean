module

public import Feec.TimeStepping.RationalAStable
public import Feec.TimeStepping.RationalSharp
public import Feec.TimeStepping.RationalHilleYosida

/-!
# The Hille–Phillips bounds on real Banach spaces

The Hille–Phillips and Brenner–Thomée bounds for rational schemes of bounded semigroups hold on
Banach spaces over `𝕜 = ℝ` or `ℂ`, through the complexification.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [E. Hille, R. S. Phillips, *Functional Analysis and Semi-Groups*][HillePhillips1957]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Complexification

@[expose] public noncomputable section

namespace Feec

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E) {M : ℝ}
  (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

include hM

namespace C0Semigroup

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem norm_complexification_S_le (t : ℝ) (ht : 0 ≤ t) : ‖G.complexification.S t‖ ≤ M :=
  (G.norm_complexification_S t).trans_le (hM t ht)

theorem map_eq_laplaceResolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    map R = G.complexification.laplaceResolvent (G.norm_complexification_S_le hM) τ hτ.le :=
  ContinuousLinearMap.ext <| G.complexification.eq_laplaceResolvent _ hτ (R := ⇑(map R))
    fun _ _ h => G.map_apply_sub_smul hR h

theorem injective_of_apply_sub_smul {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    Function.Injective R := fun a b hab => by
  have h := G.complexification.injective_laplaceResolvent (G.norm_complexification_S_le hM) hτ
    (a₁ := Complexification.mk a 0) (a₂ := Complexification.mk b 0)
    (by rw [← G.map_eq_laplaceResolvent hM hτ hR, map_mk, map_mk, hab])
  exact congrArg re h

end C0Semigroup

namespace TimeStepping.RationalScheme

variable (r : RationalScheme)

theorem isUnit_resolventEval_den_of_resolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R) := by
  have h := r.isUnit_resolventEval_den_laplaceResolvent G.complexification
    (G.norm_complexification_S_le hM) hτ.le
  rw [← G.map_eq_laplaceResolvent hM hτ hR, ← map_resolventEval_map] at h
  exact isUnit_of_isUnit_map h

theorem map_resolventStep_of_resolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    map (r.resolventStep R) = r.resolventStep
      (G.complexification.laplaceResolvent (G.norm_complexification_S_le hM) τ hτ.le) := by
  rw [resolventStep, resolventStep, ← mapHom_apply, map_mul, mapHom_apply, mapHom_apply,
    Complexification.map_ringInverse (r.isUnit_resolventEval_den_of_resolvent G hM hτ hR),
    map_resolventEval_map, map_resolventEval_map, G.map_eq_laplaceResolvent hM hτ hR]

theorem norm_resolventStep_pow_eq_of_resolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) :
    ‖r.resolventStep R ^ n‖ = ‖r.resolventStep
      (G.complexification.laplaceResolvent (G.norm_complexification_S_le hM) τ hτ.le) ^ n‖ := by
  rw [← r.map_resolventStep_of_resolvent G hM hτ hR, ← mapHom_apply, ← map_pow, mapHom_apply,
    Complexification.norm_map]

/-- **The Hille–Phillips bound over `𝕜 = ℝ` or `ℂ`**: `‖r(τA)‖ ≤ M ‖μ_r‖` for every rational
scheme and every bounded semigroup, `‖S(t)‖ ≤ M`, `τ > 0`. [HillePhillips1957] -/
theorem norm_resolventStep_le_of_resolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    ‖r.resolventStep R‖ ≤ M * r.hpMeasure.variation := by
  rw [← Complexification.norm_map (n := .taylor), r.map_resolventStep_of_resolvent G hM hτ hR]
  exact r.norm_resolventStep_le G.complexification (G.norm_complexification_S_le hM) hτ.le

theorem norm_resolventStep_pow_le_of_resolvent {r : RationalScheme} (hr : r.IsStronglyAStable)
    {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) :
    ‖r.resolventStep R ^ n‖ ≤ M * (1 + r.stabilityConst * √n) := by
  rw [r.norm_resolventStep_pow_eq_of_resolvent G hM hτ hR]
  exact norm_resolventStep_pow_le G.complexification (G.norm_complexification_S_le hM) hr hτ.le n

/-- **Brenner–Thomée's stability bound over `𝕜 = ℝ` or `ℂ` for every A-stable `r`**: for `τ > 0`,
`‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)` with `C_r = sqrtConst r`. [BrennerThomee1979] -/
theorem norm_resolventStep_pow_le_of_resolvent_of_isAStable {r : RationalScheme}
    (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) :
    ‖r.resolventStep R ^ n‖ ≤ M * (1 + r.sqrtConst * √n) := by
  rw [r.norm_resolventStep_pow_eq_of_resolvent G hM hτ hR]
  exact norm_resolventStep_pow_le_of_isAStable G.complexification (G.norm_complexification_S_le hM)
    hr hτ.le n

private theorem norm_resolventStep_pow_sub_S_le_of_resolvent_of_stable {r : RationalScheme}
    {C : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x)
    (hstab : ∀ k : ℕ, ‖r.resolventStep R ^ k‖ ≤ M * (1 + C * √k)) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      M * (1 + C * √n) *
        (M * (r.remainder p).hpMeasure.variation + M / (p + 1).factorial) * M * (n * τ) *
          τ ^ p * ‖u (p + 1)‖ := by
  refine r.norm_resolventStep_pow_sub_S_le G hp hτ.le hR (G.injective_of_apply_sub_smul hM hτ hR)
    (r.isUnit_resolventEval_den_of_resolvent G hM hτ hR) (fun k _ => (hstab k).trans ?_)
    (fun t ht => hM t ht.1) ((r.remainder p).norm_resolventStep_le_of_resolvent G hM hτ hR) hu
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  gcongr

theorem norm_resolventStep_pow_sub_S_le_of_resolvent {r : RationalScheme}
    (hr : r.IsStronglyAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      M * (1 + r.stabilityConst * √n) *
        (M * (r.remainder p).hpMeasure.variation + M / (p + 1).factorial) * M * (n * τ) *
          τ ^ p * ‖u (p + 1)‖ :=
  norm_resolventStep_pow_sub_S_le_of_resolvent_of_stable G hM (Real.sqrt_nonneg _) hp hτ hR
    (norm_resolventStep_pow_le_of_resolvent G hM hr hτ hR) n hu

theorem norm_resolventStep_pow_sub_S_le_of_resolvent_of_isAStable {r : RationalScheme}
    (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      M * (1 + r.sqrtConst * √n) *
        (M * (r.remainder p).hpMeasure.variation + M / (p + 1).factorial) * M * (n * τ) *
          τ ^ p * ‖u (p + 1)‖ :=
  norm_resolventStep_pow_sub_S_le_of_resolvent_of_stable G hM r.sqrtConst_nonneg hp hτ hR
    (norm_resolventStep_pow_le_of_resolvent_of_isAStable G hM hr hτ hR) n hu

theorem IsSymmetric.norm_resolventStep_pow_sub_S_le_of_resolvent {r : RationalScheme}
    (h : r.IsSymmetric) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) {u : ℕ → E} :
    ¬ r.IsStronglyAStable ∧ ‖r.resolventStep R ^ n‖ ≤ M * (1 + r.sqrtConst * √n) ∧
    ((∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) →
      ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
        M * (1 + r.sqrtConst * √n) *
          (M * (r.remainder p).hpMeasure.variation + M / (p + 1).factorial) * M * (n * τ) *
            τ ^ p * ‖u (p + 1)‖) :=
  ⟨h.not_isStronglyAStable,
    norm_resolventStep_pow_le_of_resolvent_of_isAStable G hM h.isAStable hτ hR n,
    norm_resolventStep_pow_sub_S_le_of_resolvent_of_isAStable G hM h.isAStable hp hτ hR n⟩

/-- **Brenner–Thomée's smooth-data error estimate over `𝕜 = ℝ` or `ℂ`**: for A-stable `r` of order
`p` and `τ > 0`, `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C M nτ τᵖ ‖A^{p+1} x‖`, `C = sharpConst r p`.
[BrennerThomee1979] -/
theorem norm_resolventStep_pow_sub_S_le_sharp_of_resolvent {r : RationalScheme}
    (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      r.sharpConst p * M * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  have h := norm_resolventStep_pow_sub_S_le_sharp G.complexification
    (G.norm_complexification_S_le hM) hr hp hτ n (u := fun j => Complexification.mk (u j) 0)
    fun j hj => G.mk_mem_graph_complexification (hu j hj)
  rw [← r.map_resolventStep_of_resolvent G hM hτ hR, ← mapHom_apply, ← map_pow, mapHom_apply,
    C0Semigroup.complexification_S, map_mk, map_mk, map_zero, map_zero, norm_mk_zero] at h
  have e : ∀ a b : E, (Complexification.mk a 0 - Complexification.mk b 0 :
      NormedComplexification 𝕜 E) = Complexification.mk (a - b) 0 := fun a b => by
    ext <;> simp
  rwa [e, norm_mk_zero] at h

end TimeStepping.RationalScheme

end Feec
