module

public import Feec.TimeStepping.RationalAStable
public import Feec.TimeStepping.RationalSharp
public import Feec.TimeStepping.RationalHilleYosida

/-!
# The Hille–Phillips bounds on real Banach spaces

The Hille–Phillips bounds of `Feec.TimeStepping.RationalHillePhillips`,
`Feec.TimeStepping.RationalAStable` and `Feec.TimeStepping.RationalSharp` hold on complex Banach
spaces (the Hille–Phillips measure `μ_r` is complex). They reach every Banach space `E` over
`𝕜 = ℝ` or `ℂ` through the complexification `E_ℂ` with the Taylor norm (`NormedComplexification`,
`C0Semigroup.complexification`), since a rational scheme `r` has real coefficients. For a
semigroup with `‖S(t)‖ ≤ M`, `τ > 0` and `R` with `R (x - τ A x) = x` on `D(A)`:

* `R_ℂ` is the Laplace transform resolvent of the complexified semigroup, which is bounded by
  the same `M` (`C0Semigroup.map_eq_laplaceResolvent`);
* hence `Q(R)` is invertible, `R` is injective and `r(τA)_ℂ = r(τA_ℂ)`
  (`RationalScheme.map_resolventStep_of_resolvent`: complexification is a ring homomorphism,
  commutes with real polynomials in `R` and with inverses), so `‖r(τA)ⁿ‖ = ‖r(τA_ℂ)ⁿ‖`;
* the Hille–Phillips bound `‖r(τA)‖ ≤ M ‖μ_r‖` for every `r`
  (`RationalScheme.norm_resolventStep_le_of_resolvent`);
* **Brenner–Thomée's stability bound** `‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)`: for strongly A-stable `r`
  with the explicit constant `C_r = stabilityConst r`
  (`RationalScheme.norm_resolventStep_pow_le_of_resolvent`), and for every A-stable `r`,
  `|r(∞)| = 1` included, with `C_r = sqrtConst r`, which comes from compactness and is not
  explicit (`RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable`);
* the **`√n`-lossy error bound**, with the same two constants
  (`RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent`,
  `RationalScheme.norm_resolventStep_pow_sub_S_le_of_resolvent_of_isAStable`; for symmetric
  schemes, `RationalScheme.IsSymmetric.norm_resolventStep_pow_sub_S_le_of_resolvent`);
* **Brenner–Thomée's smooth-data estimate** `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C_r M nτ τᵖ ‖A^{p+1} x‖` for
  every A-stable `r` of order `p`
  (`RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`), applied to `x + i 0`
  (`C0Semigroup.mk_mem_graph_complexification`).

The `√n`-lossy error bound needs no complexified data: the Lax–Richtmyer form
`RationalScheme.norm_resolventStep_pow_sub_S_le` holds over `𝕜`, and only its hypotheses (`Q(R)`
invertible, `R` injective, stability, the remainder bound) are transferred. At fixed `T = nτ` it
is weaker by `√n` than the smooth-data estimate.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [E. Hille, R. S. Phillips, *Functional Analysis and Semi-Groups*][HillePhillips1957]
* [G. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces, polynomials and multilinear maps*][MunozSarantopoulosTonge1999]

Bibliography: [references.bib](../../docs/references.bib)
-/

open NormedComplexification

@[expose] public noncomputable section

namespace Feec

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (G : C0Semigroup 𝕜 E) {M : ℝ}
  (hM : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M)

include hM

namespace C0Semigroup

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- The complexified semigroup is bounded by the same `M`. -/
theorem norm_complexification_S_le (t : ℝ) (ht : 0 ≤ t) : ‖G.complexification.S t‖ ≤ M :=
  (G.norm_complexification_S t).trans_le (hM t ht)

/-- **`R_ℂ` is the Laplace transform resolvent of the complexified semigroup**: for `τ > 0` and
`R` with `R (x - τ A x) = x` on `D(A)`, `R_ℂ = ∫₀^∞ e^{-t} S(τt)_ℂ dt`. -/
theorem map_eq_laplaceResolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    map R = G.complexification.laplaceResolvent (G.norm_complexification_S_le hM) τ hτ.le :=
  ContinuousLinearMap.ext <| G.complexification.eq_laplaceResolvent _ hτ (R := ⇑(map R))
    fun _ _ h => G.map_apply_sub_smul hR h

/-- `R = (1 - τA)⁻¹` is injective, since `R_ℂ` is. -/
theorem injective_of_apply_sub_smul {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    Function.Injective R := fun a b hab => by
  have h := G.complexification.injective_laplaceResolvent (G.norm_complexification_S_le hM) hτ
    (a₁ := NormedComplexification.mk a 0) (a₂ := NormedComplexification.mk b 0)
    (by rw [← G.map_eq_laplaceResolvent hM hτ hR, map_mk, map_mk, hab])
  exact congrArg re h

end C0Semigroup

namespace TimeStepping.RationalScheme

variable (r : RationalScheme)

/-- **`Q(R)` is invertible**, for every rational scheme: `Q(R)_ℂ = Q(R_ℂ)` is. -/
theorem isUnit_resolventEval_den_of_resolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    IsUnit (resolventEval r.den.natDegree (r.den.map (algebraMap ℝ 𝕜)) R) := by
  have h := r.isUnit_resolventEval_den_laplaceResolvent G.complexification
    (G.norm_complexification_S_le hM) hτ.le
  rw [← G.map_eq_laplaceResolvent hM hτ hR, ← map_resolventEval_map] at h
  exact isUnit_of_isUnit_map h

/-- **Complexification commutes with the scheme**: `r(τA)_ℂ = r(τA_ℂ)`, with `R_ℂ` the Laplace
transform resolvent of the complexified semigroup. -/
theorem map_resolventStep_of_resolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    map (r.resolventStep R) = r.resolventStep
      (G.complexification.laplaceResolvent (G.norm_complexification_S_le hM) τ hτ.le) := by
  rw [resolventStep, resolventStep, ← mapHom_apply, map_mul, mapHom_apply, mapHom_apply,
    map_ringInverse (r.isUnit_resolventEval_den_of_resolvent G hM hτ hR), map_resolventEval_map,
    map_resolventEval_map, G.map_eq_laplaceResolvent hM hτ hR]

/-- `‖r(τA)ⁿ‖ = ‖r(τA_ℂ)ⁿ‖`. -/
theorem norm_resolventStep_pow_eq_of_resolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) :
    ‖r.resolventStep R ^ n‖ = ‖r.resolventStep
      (G.complexification.laplaceResolvent (G.norm_complexification_S_le hM) τ hτ.le) ^ n‖ := by
  rw [← r.map_resolventStep_of_resolvent G hM hτ hR, ← mapHom_apply, ← map_pow, mapHom_apply,
    NormedComplexification.norm_map]

/-- **The Hille–Phillips bound over `𝕜 = ℝ` or `ℂ`**: `‖r(τA)‖ ≤ M ‖μ_r‖` for every rational
scheme and every bounded semigroup, `‖S(t)‖ ≤ M`, `τ > 0`. [HillePhillips1957] -/
theorem norm_resolventStep_le_of_resolvent {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) :
    ‖r.resolventStep R‖ ≤ M * r.hpMeasure.variation := by
  rw [← NormedComplexification.norm_map, r.map_resolventStep_of_resolvent G hM hτ hR]
  exact r.norm_resolventStep_le G.complexification (G.norm_complexification_S_le hM) hτ.le

/-- **Brenner–Thomée's stability bound over `𝕜 = ℝ` or `ℂ`** [BrennerThomee1979]: for a strongly
A-stable rational scheme `r`, a bounded semigroup `‖S(t)‖ ≤ M` on a Banach space, `τ > 0` and
`R = (1 - τA)⁻¹`, `‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)` for every `n`. Every A-stable `r` is covered by
`norm_resolventStep_pow_le_of_resolvent_of_isAStable`; this form is kept for its explicit
constant `C_r = stabilityConst r` (`sqrtConst r` there comes from compactness). -/
theorem norm_resolventStep_pow_le_of_resolvent {r : RationalScheme} (hr : r.IsStronglyAStable)
    {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) :
    ‖r.resolventStep R ^ n‖ ≤ M * (1 + r.stabilityConst * √n) := by
  rw [r.norm_resolventStep_pow_eq_of_resolvent G hM hτ hR]
  exact norm_resolventStep_pow_le G.complexification (G.norm_complexification_S_le hM) hr hτ.le n

/-- **Brenner–Thomée's stability bound over `𝕜 = ℝ` or `ℂ` for every A-stable `r`**,
`|r(∞)| = 1` included: `‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)` with `C_r = sqrtConst r`. [BrennerThomee1979] -/
theorem norm_resolventStep_pow_le_of_resolvent_of_isAStable {r : RationalScheme}
    (hr : r.IsAStable) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) :
    ‖r.resolventStep R ^ n‖ ≤ M * (1 + r.sqrtConst * √n) := by
  rw [r.norm_resolventStep_pow_eq_of_resolvent G hM hτ hR]
  exact norm_resolventStep_pow_le_of_isAStable G.complexification (G.norm_complexification_S_le hM)
    hr hτ.le n

/-- The error bound from a stability bound `‖r(τA)ᵏ‖ ≤ M (1 + C √k)`, `C ≥ 0`. -/
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

/-- **The `√n`-lossy error bound over `𝕜 = ℝ` or `ℂ`**: for a strongly A-stable rational scheme
`r` of order `p`, a bounded semigroup `‖S(t)‖ ≤ M` on a Banach space with generator `A`, `τ > 0`,
`R` with `R (x - τ A x) = x` on `D(A)`, and `x ∈ D(A^{p+1})` (a chain `u` in the graph of `A`),

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ M (1 + C_r √n) (M ‖μ_ρ‖ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖`,

Brenner–Thomée's stability bound times order-`p` consistency (`ρ` the remainder scheme). At
fixed `T = nτ` the rate is `τ^{p-1/2}`, weaker by `√n` than the smooth-data estimate
`norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`. Every A-stable `r` is covered by
`norm_resolventStep_pow_sub_S_le_of_resolvent_of_isAStable`; this form is kept for its explicit
constant `C_r = stabilityConst r`. [BrennerThomee1979] -/
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

/-- **The `√n`-lossy error bound over `𝕜 = ℝ` or `ℂ` for every A-stable `r`** of order `p`,
`|r(∞)| = 1` included (Crank–Nicolson, the Gauss methods): for `τ > 0`, `R` with
`R (x - τ A x) = x` on `D(A)` and `x ∈ D(A^{p+1})`,

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ M (1 + C_r √n) (M ‖μ_ρ‖ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖`,

with `C_r = sqrtConst r`, the stability bound
`norm_resolventStep_pow_le_of_resolvent_of_isAStable` times order-`p` consistency.
[BrennerThomee1979] -/
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

/-- **Symmetric schemes over `𝕜 = ℝ` or `ℂ`** (the diagonal Padé and Gauss methods): a symmetric
scheme `r` of order `p` is not strongly A-stable, and yet, for `τ > 0` and `R` with
`R (x - τ A x) = x` on `D(A)`, `‖r(τA)ⁿ‖ ≤ M (1 + C_r √n)` and, for `x ∈ D(A^{p+1})`,
`‖r(τA)ⁿ x - S(nτ) x‖ ≤ M (1 + C_r √n) (M ‖μ_ρ‖ + M/(p+1)!) M nτ τᵖ ‖A^{p+1} x‖`, with
`C_r = sqrtConst r`. [BrennerThomee1979] -/
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

/-- **Brenner–Thomée's smooth-data error estimate over `𝕜 = ℝ` or `ℂ`**: for an A-stable rational
scheme `r` of order `p` (`|r(∞)| = 1` included), a bounded semigroup `‖S(t)‖ ≤ M` on a Banach
space with generator `A`, `τ > 0`, `R` with `R (x - τ A x) = x` on `D(A)`, every `n` and
`x ∈ D(A^{p+1})` (a chain `u` in the graph of `A`),

  `‖r(τA)ⁿ x - S(nτ) x‖ ≤ C M nτ τᵖ ‖A^{p+1} x‖`,

`C = sharpConst r p`, the constant of the complex case `norm_resolventStep_pow_sub_S_le_sharp`,
applied to `x + i 0` on the complexification. [BrennerThomee1979] -/
theorem norm_resolventStep_pow_sub_S_le_sharp_of_resolvent {r : RationalScheme}
    (hr : r.IsAStable) {p : ℕ} (hp : r.HasOrder p) {τ : ℝ} (hτ : 0 < τ) {R : E →L[𝕜] E}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x) (n : ℕ) {u : ℕ → E}
    (hu : ∀ j < p + 1, (u j, u (j + 1)) ∈ G.generator.graph) :
    ‖(r.resolventStep R ^ n) (u 0) - G.S (n * τ) (u 0)‖ ≤
      r.sharpConst p * M * (n * τ) * τ ^ p * ‖u (p + 1)‖ := by
  have h := norm_resolventStep_pow_sub_S_le_sharp G.complexification
    (G.norm_complexification_S_le hM) hr hp hτ n (u := fun j => NormedComplexification.mk (u j) 0)
    fun j hj => G.mk_mem_graph_complexification (hu j hj)
  rw [← r.map_resolventStep_of_resolvent G hM hτ hR, ← mapHom_apply, ← map_pow, mapHom_apply,
    C0Semigroup.complexification_S, map_mk, map_mk, map_zero, map_zero, norm_mk_zero] at h
  have e : ∀ a b : E, (NormedComplexification.mk a 0 - NormedComplexification.mk b 0 :
      NormedComplexification 𝕜 E) = NormedComplexification.mk (a - b) 0 := fun a b => by
    ext <;> simp
  rwa [e, norm_mk_zero] at h

end TimeStepping.RationalScheme

end Feec
