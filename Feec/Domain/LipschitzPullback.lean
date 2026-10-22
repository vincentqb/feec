module

public import Feec.Domain.WholeSpace
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Pullbacks along bi-Lipschitz maps of `ℝ³`

Let `Φ` be a bi-Lipschitz homeomorphism of `ℝ³` (`BiLipschitz`: a bijection with `Φ` and `Φ⁻¹`
`K`-Lipschitz) and `U, Ω ⊆ ℝ³` with `Φ(U) = Ω` (`x ∈ U ↔ Φ x ∈ Ω`). The `1`-form pullback carries
`H̊(curl, Ω)` into `H̊(curl, U)` and the Piola transform carries `H(div, Ω)` into `H(div, U)`, row
by row on `3 × 3` matrix fields, with the transformation rules of the exterior derivative. These
are the transport results that move Weber compactness from a cube to a domain star-shaped with
respect to a ball (`Feec.Models.StarShaped.EigenDense`).

## Lipschitz calculus

* Lipschitz maps of `ℝⁿ` send null sets to null sets (`volume_image_eq_zero_of_lipschitzWith`,
  `μH[n] = volume`). Hence almost every `x` is *good*: `Φ` is differentiable at `x` and `Φ⁻¹` at
  `Φ x` (Rademacher, `BiLipschitz.ae_good`), and there `D(Φ⁻¹)(Φ x) DΦ(x) = 1`
  (`BiLipschitz.lipJac_symm_mul_lipJac`), `1 ≤ 6 K³ |det DΦ(x)|`
  (`BiLipschitz.one_le_abs_det_lipJac`); everywhere `|det DΦ| ≤ 6 K³`.
* **Change of variables** (`BiLipschitz.integral_image`, `BiLipschitz.integrableOn_image_iff`,
  `BiLipschitz.integral_comp`): `∫_Ω g = ∫_U |det DΦ| g ∘ Φ`, from Mathlib's formula for injective
  maps differentiable on a measurable set, applied to `U ∩ {Φ differentiable}`, whose complement in
  `U` and its image are null.
* **Mollification of Lipschitz functions** (`fderiv_molli_eq_integral_lineDeriv`,
  `abs_fderiv_molli_le`, `ae_tendsto_fderiv_molli`, `eventually_isTest_molli`):
  `∂ᵥ(f ⋆ ρ_m) = (∂ᵥ f) ⋆ ρ_m` (integration by parts for Lipschitz functions), bounded by the
  Lipschitz constant, and converging almost everywhere to `∂ᵥ f` (Lebesgue differentiation).

## The pullbacks

* `pull1Fun Φ u = DΦᵀ (u_a ∘ Φ)` (the `1`-form pullback, row by row) and
  `pull2Fun Φ w = adj(DΦ) (w_a ∘ Φ) = cof(DΦ)ᵀ (w_a ∘ Φ)` (the `2`-form pullback).
* For smooth `F`, `curl (DFᵀ u ∘ F) = adj(DF) (curl u) ∘ F` (`curl_pullRow`: symmetry of second
  derivatives and a cofactor identity) and its weak form (`integral_curl_pullRow`). For Lipschitz
  `Φ` the weak form follows by mollifying `Φ` and dominated convergence
  (`integral_curl_pullFun`): `D(Φ ⋆ ρ_m) → DΦ` almost everywhere and boundedly.
* On `L²`: weighted pullbacks `u ↦ Σₖ Mᵢₖ uₖ ∘ Φ` with bounded measurable weights
  (`BiLipschitz.wpull`), in particular `pull1`, `pull2`, the Jacobian pullback `pullJ`
  (`f ↦ |det DΦ| f ∘ Φ`), the **Piola transform** `piola` (`|det DΦ| DΦ⁻¹ (u_a ∘ Φ)`) and the
  **coefficient** `coeff` (`ε = |det DΦ| DΦ⁻¹ DΦ⁻ᵀ ∈ L^∞`, with `DΦ⁻¹ := D(Φ⁻¹) ∘ Φ`).

## Main results

* **`BiLipschitz.pull1_mem_minimal_curl`**: `Φ^*` maps `D(curl_min(Ω))` into `D(curl_min(U))`
  and `curl_min (Φ^* u) = Φ^♭ (curl_min u)`. On test fields this is `integral_curl_pullFun`,
  `Φ^* u` being supported in the compact `Φ⁻¹(supp u) ⊆ U`
  (`ConstCoeffOp.mem_minimal_of_maximal_of_support_subset`); then graph closure.
* **`BiLipschitz.piola_mem_maximal_divT`**: if `div u ∈ L²(Ω)` (no boundary condition), then
  `div (P u) = |det DΦ| (div u) ∘ Φ` in `L²(U)` (`|U|, |Ω| < ∞`, divergence in the form
  `(gradᵗ)_max`): both sides become integrals over `Ω` against the Lipschitz test functions
  `φ ∘ Φ⁻¹`, for which the weak divergence still holds (`integral_maximal_divT_lipschitz`).
* **`BiLipschitz.coeff_pull1`**: `ε Φ^* = P`. **`BiLipschitz.coeff_coercive`**:
  `‖v‖² / (54 K⁵) ≤ ⟪ε v, v⟫`. **`BiLipschitz.norm_le_norm_pull1`**: `‖u‖ ≤ √(54 K⁵) ‖Φ^* u‖`.

`Φ` is assumed to be a bi-Lipschitz homeomorphism of all of `ℝ³`, as the radial maps of
star-shaped domains are. No lower bound on `|det DΦ|` is assumed: it follows from the Lipschitz
inverse.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.8 (Lipschitz functions,
  Rademacher's theorem), App. C.4 (mollifiers)
* [V. Girault, P.-A. Raviart, *Finite Element Methods for Navier–Stokes Equations*][GiraultRaviart1986],
  Ch. I, §3 (`H(curl)` and `H(div)`)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002]
  (pullbacks of differential forms, Piola transforms)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff Convolution InnerProductSpace

namespace Feec.Domain


/-! ### Lipschitz maps of `ℝⁿ` -/

section Lipschitz

variable {n : ℕ}

/-- **Lipschitz maps of `ℝⁿ` send null sets to null sets** (`μH[n] = volume`). -/
theorem volume_image_eq_zero_of_lipschitzWith {K : ℝ≥0} {f : (Fin n → ℝ) → (Fin n → ℝ)}
    (hf : LipschitzWith K f) {s : Set (Fin n → ℝ)} (hs : volume s = 0) : volume (f '' s) = 0 := by
  have h := hf.hausdorffMeasure_image_le (d := ((Fintype.card (Fin n) : ℕ) : ℝ))
    (Nat.cast_nonneg _) s
  rw [hausdorffMeasure_pi_real, hs, mul_zero] at h
  exact le_antisymm h bot_le

/-- The Jacobian matrix `(DΦ)_{ij} = ∂_j Φ_i`. -/
def lipJac (Φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix' (fderiv ℝ Φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))

theorem lipJac_apply (Φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (i j : Fin n) :
    lipJac Φ x i j = fderiv ℝ Φ x (Pi.single j 1) i := by
  simp [lipJac, LinearMap.toMatrix'_apply]

theorem det_lipJac (Φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    (lipJac Φ x).det = (fderiv ℝ Φ x).det := by
  rw [lipJac, LinearMap.det_toMatrix']

theorem abs_lipJac_le {K : ℝ≥0} {Φ : (Fin n → ℝ) → (Fin n → ℝ)} (hΦ : LipschitzWith K Φ)
    (x : Fin n → ℝ) (i j : Fin n) : |lipJac Φ x i j| ≤ K := by
  rw [lipJac_apply, ← Real.norm_eq_abs]
  refine (norm_le_pi_norm _ i).trans ?_
  refine ((fderiv ℝ Φ x).le_opNorm _).trans ?_
  have h1 : ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  calc ‖fderiv ℝ Φ x‖ * ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ ≤ K * 1 :=
        mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hΦ) h1 (norm_nonneg _) K.2
    _ = K := mul_one _

/-- **The chain rule at a point**: if `Ψ ∘ Φ = id`, `Φ` is differentiable at `x` and `Ψ` at
`Φ x`, then `DΨ(Φ x) DΦ(x) = 1`. -/
theorem lipJac_mul_lipJac_eq_one {Φ Ψ : (Fin n → ℝ) → (Fin n → ℝ)} (h : ∀ y, Ψ (Φ y) = y)
    {x : Fin n → ℝ} (hΦ : DifferentiableAt ℝ Φ x) (hΨ : DifferentiableAt ℝ Ψ (Φ x)) :
    lipJac Ψ (Φ x) * lipJac Φ x = 1 := by
  have hc : Ψ ∘ Φ = id := funext h
  have e := fderiv_comp x hΨ hΦ
  rw [hc, fderiv_id] at e
  rw [lipJac, lipJac, ← LinearMap.toMatrix'_comp]
  have : ((fderiv ℝ Ψ (Φ x) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
      (fderiv ℝ Φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) = LinearMap.id := by
    have := congrArg
      (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) e
    simpa using this.symm
  rw [this, LinearMap.toMatrix'_id]

end Lipschitz

/-! ### Mollification of Lipschitz functions -/

section Molli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- `∂_v (f ⋆ ρ)(x) = ∫ ∂_v f(t) ρ(x - t) dt` for a Lipschitz `f` (integration by parts,
`integral_lineDeriv_mul_eq`). -/
theorem fderiv_molli_eq_integral_lineDeriv {K : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith K f)
    (φ : ContDiffBump (0 : E)) (x v : E) :
    fderiv ℝ (molli φ f) x v = ∫ t, lineDeriv ℝ f t v * φ.normed volume (x - t) := by
  have hρ : IsTest (univ : Set E) (φ.normed volume) :=
    ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, subset_univ _⟩
  have hfl : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  rw [molli, fderiv_convolution_apply hρ hfl, convolution_apply_mul]
  set g : E → ℝ := fun t => φ.normed volume (x - t)
  have hgc : ContDiff ℝ ∞ g := φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hgs : HasCompactSupport g :=
    φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨D, hD⟩ := hgc.lipschitzWith_of_hasCompactSupport hgs (by simp)
  rw [hf.integral_lineDeriv_mul_eq hD hgs v]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hd : DifferentiableAt ℝ g t := hgc.differentiable (by simp) t
  simp only
  rw [hd.lineDeriv_eq_fderiv, mul_comm]
  congr 1
  have : fderiv ℝ g t = (fderiv ℝ (φ.normed volume) (x - t)).comp
      (fderiv ℝ (fun t : E => x - t) t) := by
    have h1 : DifferentiableAt ℝ (φ.normed volume) (x - t) :=
      ((φ.contDiff_normed (n := 1)).differentiable (by simp)) _
    exact fderiv_comp t h1 (by fun_prop)
  have h2 : fderiv ℝ (fun t : E => x - t) t = -ContinuousLinearMap.id ℝ E :=
    ((hasFDerivAt_id (𝕜 := ℝ) t).const_sub x).fderiv
  rw [this, h2]
  simp

/-- Translating the bump: `∫ ρ(x - t) dt = 1`. -/
theorem integral_normed_sub (φ : ContDiffBump (0 : E)) (x : E) :
    ∫ t, φ.normed volume (x - t) = 1 := by
  rw [integral_sub_left_eq_self (fun t => φ.normed volume t) volume x, φ.integral_normed]

theorem integrable_normed_sub (φ : ContDiffBump (0 : E)) (x : E) :
    Integrable (fun t => φ.normed volume (x - t)) := by
  have hc : Continuous fun t => φ.normed volume (x - t) :=
    φ.continuous_normed.comp (continuous_const.sub continuous_id)
  exact hc.integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x))

/-- **The derivatives of the mollifications of a `K`-Lipschitz function are bounded by `K`.** -/
theorem abs_fderiv_molli_le {K : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith K f)
    (φ : ContDiffBump (0 : E)) (x v : E) : |fderiv ℝ (molli φ f) x v| ≤ K * ‖v‖ := by
  rw [fderiv_molli_eq_integral_lineDeriv hf, ← Real.norm_eq_abs]
  have hb : ∀ t, ‖lineDeriv ℝ f t v * φ.normed volume (x - t)‖ ≤
      K * ‖v‖ * φ.normed volume (x - t) := fun t => by
    rw [norm_mul, Real.norm_of_nonneg (φ.nonneg_normed _)]
    exact mul_le_mul_of_nonneg_right (norm_lineDeriv_le_of_lipschitz ℝ hf) (φ.nonneg_normed _)
  refine (norm_integral_le_of_norm_le ((integrable_normed_sub φ x).const_mul _)
    (Eventually.of_forall hb)).trans_eq ?_
  rw [integral_const_mul, integral_normed_sub, mul_one]

/-- The derivative of the mollification as a convolution of the line derivative. -/
theorem fderiv_molli_eq_convolution {K : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith K f)
    (φ : ContDiffBump (0 : E)) (x v : E) :
    fderiv ℝ (molli φ f) x v = (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun t => lineDeriv ℝ f t v) x := by
  rw [fderiv_molli_eq_integral_lineDeriv hf, convolution_def,
    ← integral_sub_left_eq_self _ volume x]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [sub_sub_cancel, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

/-- **The derivatives of the mollifications converge almost everywhere** (Lebesgue
differentiation for the bounded line derivatives,
`ae_convolution_tendsto_right_of_locallyIntegrable`):
`∂_v (f ⋆ ρ_m)(x) → ∂_v f(x)` at almost every `x`. -/
theorem ae_tendsto_fderiv_molli {K : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith K f) (v : E) :
    ∀ᵐ x, Tendsto (fun m : ℕ => fderiv ℝ (molli (bumpSeq m) f) x v) atTop
      (𝓝 (fderiv ℝ f x v)) := by
  have h1 := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := fun m : ℕ => (bumpSeq m : ContDiffBump (0 : E))) (l := atTop) (K := 2)
    tendsto_bumpSeq_rOut (Eventually.of_forall fun m => by
      change 1 / ((m : ℝ) + 1) ≤ 2 * (1 / ((m : ℝ) + 2))
      rw [div_le_iff₀ (by positivity)]
      field_simp
      linarith) (hf.locallyIntegrable_lineDeriv v)
  filter_upwards [h1, hf.ae_differentiableAt (μ := volume)] with x hx hd
  rw [← hd.lineDeriv_eq_fderiv]
  simpa only [fderiv_molli_eq_convolution hf] using hx

/-- **The mollifications of a continuous function converge pointwise.** -/
theorem tendsto_molli_of_continuous {f : E → ℝ} (hf : Continuous f) (x : E) :
    Tendsto (fun m : ℕ => molli (bumpSeq m) f x) atTop (𝓝 (f x)) := by
  simp only [molli_eq_normed_convolution]
  exact ContDiffBump.convolution_tendsto_right_of_continuous tendsto_bumpSeq_rOut hf x

/-- The mollification of a bounded function is bounded. -/
theorem abs_molli_le {f : E → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) (φ : ContDiffBump (0 : E))
    (x : E) : |molli φ f x| ≤ C := by
  rw [molli_apply, ← Real.norm_eq_abs]
  have hb : ∀ t, ‖f t * φ.normed volume (x - t)‖ ≤ C * φ.normed volume (x - t) := fun t => by
    rw [norm_mul, Real.norm_of_nonneg (φ.nonneg_normed _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hf t) (φ.nonneg_normed _)
  refine (norm_integral_le_of_norm_le ((integrable_normed_sub φ x).const_mul _)
    (Eventually.of_forall hb)).trans_eq ?_
  rw [integral_const_mul, integral_normed_sub, mul_one]

/-- The support of a mollification lies in the `rOut`-neighbourhood of the support. -/
theorem support_molli_subset (φ : ContDiffBump (0 : E)) (f : E → ℝ) :
    Function.support (molli φ f) ⊆ Metric.cthickening φ.rOut (tsupport f) := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := support_convolution_subset _ hx
  rw [φ.support_normed_eq] at hw
  refine Metric.mem_cthickening_of_dist_le _ u _ _ (subset_tsupport _ hu) ?_
  rw [dist_eq_norm, add_sub_cancel_left]
  exact (mem_ball_zero_iff.1 hw).le

/-- **Mollifications of compactly supported Lipschitz functions are eventually test
functions** on every open set containing the support. -/
theorem eventually_isTest_molli {K : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith K f)
    (hfs : HasCompactSupport f) {Ω : Set E} (hΩ : IsOpen Ω) (hsub : tsupport f ⊆ Ω) :
    ∀ᶠ m : ℕ in atTop, IsTest Ω (molli (bumpSeq m) f) := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  obtain ⟨δ, hδ, hδΩ⟩ := hfs.isCompact.exists_cthickening_subset_open hΩ hsub
  filter_upwards [(tendsto_order.1 (tendsto_bumpSeq_rOut (E := E))).2 δ hδ] with m hm
  have hsupp : tsupport (molli (bumpSeq m) f) ⊆ Metric.cthickening δ (tsupport f) :=
    (closure_minimal (support_molli_subset _ f) Metric.isClosed_cthickening).trans
      (Metric.cthickening_mono hm.le _)
  exact ⟨contDiff_molli _ hf.continuous.locallyIntegrable,
    (hfs.isCompact.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans hδΩ⟩

end Molli



/-! ### The pullback of a smooth row under a smooth map -/

section SmoothPull

/-- The map `x ↦ (F₀ x, F₁ x, F₂ x)` of a triple of scalar functions. -/
def cmap (F : Fin 3 → (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun l => F l x

/-- The partial derivative `∂ᵢ F_k` of a triple of scalar functions. -/
def cd (F : Fin 3 → (Fin 3 → ℝ) → ℝ) (k i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ (F k) x (coordDir i)

/-- The Jacobian matrix `(∂ᵢ F_k)_{ki}` of a triple of scalar functions. -/
def cjac (F : Fin 3 → (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun k i => cd F k i x

/-- The `1`-form pullback of a row `u`: `(F^* u)ᵢ = Σₖ ∂ᵢ F_k · u_k ∘ F`. -/
def pullRow (F u : Fin 3 → (Fin 3 → ℝ) → ℝ) (i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  ∑ k, cd F k i x * u k (cmap F x)

variable {F u : Fin 3 → (Fin 3 → ℝ) → ℝ}

theorem contDiff_cd (hF : ∀ k, ContDiff ℝ ∞ (F k)) (k i : Fin 3) :
    ContDiff ℝ ∞ (cd F k i) :=
  contDiff_iterDeriv (hF k) [coordDir i]

theorem contDiff_pullRow (hF : ∀ k, ContDiff ℝ ∞ (F k)) (hu : ∀ k, ContDiff ℝ ∞ (u k))
    (i : Fin 3) : ContDiff ℝ ∞ (pullRow F u i) := by
  unfold pullRow
  exact ContDiff.sum fun k _ => (contDiff_cd hF k i).mul ((hu k).comp (contDiff_pi.2 hF))

theorem fderiv_comp_cmap (hF : ∀ k, ContDiff ℝ ∞ (F k)) {g : (Fin 3 → ℝ) → ℝ}
    (hg : ContDiff ℝ ∞ g) (x : Fin 3 → ℝ) (j : Fin 3) :
    fderiv ℝ (fun y => g (cmap F y)) x (coordDir j) =
      ∑ l, cd F l j x * fderiv ℝ g (cmap F x) (coordDir l) := by
  have hc : DifferentiableAt ℝ (cmap F) x := (contDiff_pi.2 hF).differentiable (by simp) x
  have hgd : DifferentiableAt ℝ g (cmap F x) := hg.differentiable (by simp) _
  rw [show (fun y => g (cmap F y)) = g ∘ cmap F from rfl, fderiv_comp x hgd hc,
    ContinuousLinearMap.comp_apply]
  have hpi : fderiv ℝ (cmap F) x (coordDir j) = fun l => cd F l j x := by
    have : cmap F = fun y l => F l y := rfl
    rw [this, fderiv_pi fun l => (hF l).differentiable (by simp) x]
    rfl
  rw [hpi]
  conv_lhs => rw [show (fun l => cd F l j x) = ∑ l, cd F l j x • coordDir l by
    ext l; simp [coordDir, Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp [map_smul, smul_eq_mul]

theorem fderiv_pullRow (hF : ∀ k, ContDiff ℝ ∞ (F k)) (hu : ∀ k, ContDiff ℝ ∞ (u k))
    (i j : Fin 3) (x : Fin 3 → ℝ) :
    fderiv ℝ (pullRow F u i) x (coordDir j) =
      ∑ k, (iterDeriv [coordDir j, coordDir i] (F k) x * u k (cmap F x) +
        cd F k i x * ∑ l, cd F l j x * fderiv ℝ (u k) (cmap F x) (coordDir l)) := by
  have hJ : ∀ k, DifferentiableAt ℝ (cd F k i) x := fun k =>
    (contDiff_cd hF k i).differentiable (by simp) x
  have hU : ∀ k, DifferentiableAt ℝ (fun y => u k (cmap F y)) x := fun k =>
    ((hu k).comp (contDiff_pi.2 hF)).differentiable (by simp) x
  have e : pullRow F u i = fun y => ∑ k, cd F k i y * u k (cmap F y) := rfl
  rw [e, fderiv_fun_sum fun k _ => (hJ k).fun_mul (hU k), _root_.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_fun_mul (hJ k) (hU k)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [fderiv_comp_cmap hF (hu k) x j]
  have : fderiv ℝ (cd F k i) x (coordDir j) =
      iterDeriv [coordDir j, coordDir i] (F k) x := rfl
  rw [this]
  ring

/-- **The curl of the pullback is the cofactor pullback of the curl**, pointwise for smooth `F`
and `u`: `curl (DFᵀ u ∘ F) = adj(DF) (curl u) ∘ F`. -/
theorem curl_pullRow (hF : ∀ k, ContDiff ℝ ∞ (F k)) (hu : ∀ k, ContDiff ℝ ∞ (u k))
    (m : Fin 3) (x : Fin 3 → ℝ) :
    fderiv ℝ (pullRow F u (m + 2)) x (coordDir (m + 1)) -
        fderiv ℝ (pullRow F u (m + 1)) x (coordDir (m + 2)) =
      ∑ p, (cjac F x).adjugate m p *
        (fderiv ℝ (u (p + 2)) (cmap F x) (coordDir (p + 1)) -
          fderiv ℝ (u (p + 1)) (cmap F x) (coordDir (p + 2))) := by
  rw [fderiv_pullRow hF hu, fderiv_pullRow hF hu]
  have hsym : ∀ k (a b : Fin 3), iterDeriv [coordDir a, coordDir b] (F k) x =
      iterDeriv [coordDir b, coordDir a] (F k) x := fun k a b => by
    rw [← iterDeriv_reverse (hF k) [coordDir b, coordDir a]]; rfl
  simp only [hsym _ (m + 1) (m + 2)]
  rw [Matrix.adjugate_fin_three]
  fin_cases m <;>
  simp [Fin.sum_univ_three, cjac] <;> ring

end SmoothPull

/-! ### The pullback of test fields along a Lipschitz map -/

section LipPull

variable {K : ℝ≥0} {Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)}

/-- The scalar components `x ↦ Φ(x)_k`. -/
def comps (Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Fin 3 → (Fin 3 → ℝ) → ℝ := fun k x => Φ x k

theorem lipschitzWith_comps (hΦ : LipschitzWith K Φ) (k : Fin 3) :
    LipschitzWith K (comps Φ k) := by
  have := (LipschitzWith.eval (α := fun _ : Fin 3 => ℝ) k).comp hΦ
  rw [one_mul] at this
  exact this

theorem cd_comps_eq_lipJac {x : Fin 3 → ℝ} (hd : DifferentiableAt ℝ Φ x) (k i : Fin 3) :
    cd (comps Φ) k i x = lipJac Φ x k i := by
  have h : HasFDerivAt (comps Φ k) ((ContinuousLinearMap.proj k).comp (fderiv ℝ Φ x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) k).hasFDerivAt.comp x
      hd.hasFDerivAt
  rw [cd, h.fderiv, lipJac_apply]
  rfl

/-- The mollified components `Φ_k ⋆ ρ_m`. -/
def molliComps (Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (m : ℕ) : Fin 3 → (Fin 3 → ℝ) → ℝ :=
  fun k => molli (bumpSeq m) (comps Φ k)

theorem contDiff_molliComps (hΦ : LipschitzWith K Φ) (m : ℕ) (k : Fin 3) :
    ContDiff ℝ ∞ (molliComps Φ m k) :=
  contDiff_molli _ (lipschitzWith_comps hΦ k).continuous.locallyIntegrable

theorem norm_coordDir_le_one (i : Fin 3) : ‖(coordDir i : Fin 3 → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
  by_cases hk : k = i
  · subst hk; simp [coordDir]
  · simp [coordDir, hk]

theorem abs_cd_molliComps_le (hΦ : LipschitzWith K Φ) (m : ℕ) (k i : Fin 3) (x : Fin 3 → ℝ) :
    |cd (molliComps Φ m) k i x| ≤ K := by
  refine (abs_fderiv_molli_le (lipschitzWith_comps hΦ k) _ x _).trans ?_
  calc (K : ℝ) * ‖(coordDir i : Fin 3 → ℝ)‖ ≤ K * 1 :=
        mul_le_mul_of_nonneg_left (norm_coordDir_le_one i) K.2
    _ = K := mul_one _

theorem tendsto_cmap_molliComps (hΦ : LipschitzWith K Φ) (x : Fin 3 → ℝ) :
    Tendsto (fun m => cmap (molliComps Φ m) x) atTop (𝓝 (Φ x)) := by
  refine tendsto_pi_nhds.2 fun k => ?_
  exact tendsto_molli_of_continuous (lipschitzWith_comps hΦ k).continuous x

theorem ae_tendsto_cjac_molliComps (hΦ : LipschitzWith K Φ) :
    ∀ᵐ x, Tendsto (fun m => cjac (molliComps Φ m) x) atTop (𝓝 (lipJac Φ x)) := by
  have h : ∀ k i : Fin 3, ∀ᵐ x, Tendsto (fun m => cd (molliComps Φ m) k i x) atTop
      (𝓝 (fderiv ℝ (comps Φ k) x (coordDir i))) := fun k i =>
    ae_tendsto_fderiv_molli (lipschitzWith_comps hΦ k) (coordDir i)
  have h' : ∀ᵐ x, ∀ k i : Fin 3, Tendsto (fun m => cd (molliComps Φ m) k i x) atTop
      (𝓝 (fderiv ℝ (comps Φ k) x (coordDir i))) := by
    simp only [ae_all_iff]; exact h
  filter_upwards [h', hΦ.ae_differentiableAt (μ := volume)] with x hx hd
  refine tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun i => ?_
  have := hx k i
  rw [show fderiv ℝ (comps Φ k) x (coordDir i) = cd (comps Φ) k i x from rfl,
    cd_comps_eq_lipJac hd] at this
  exact this

theorem abs_mul_sub_mul_le {a b c d C : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ C) (hc : |c| ≤ C)
    (hd : |d| ≤ C) : |a * b - c * d| ≤ 2 * C ^ 2 := by
  have h0 : 0 ≤ C := (abs_nonneg a).trans ha
  have h1 : |a * b| ≤ C ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul ha hb (abs_nonneg _) h0
  have h2 : |c * d| ≤ C ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hc hd (abs_nonneg _) h0
  calc |a * b - c * d| ≤ |a * b| + |c * d| := abs_sub _ _
    _ ≤ 2 * C ^ 2 := by linarith

theorem abs_adjugate_le {A : Matrix (Fin 3) (Fin 3) ℝ} {C : ℝ} (hA : ∀ k l, |A k l| ≤ C)
    (i p : Fin 3) : |A.adjugate i p| ≤ 2 * C ^ 2 := by
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases p <;> simp only [neg_add_eq_sub] <;>
    simp <;> exact abs_mul_sub_mul_le (hA _ _) (hA _ _) (hA _ _) (hA _ _)

/-- **The smooth identity in weak form**: for smooth `F` and `u` and a test field `ψ`,
`∫ (F^* u) · curl ψ = ∫ adj(DF) (curl u) ∘ F · ψ` (Green's formula and `curl_pullRow`). -/
theorem integral_curl_pullRow {F : Fin 3 → (Fin 3 → ℝ) → ℝ} (hF : ∀ k, ContDiff ℝ ∞ (F k))
    {u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    {ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ} (hψ : IsTestField (univ : Set (Fin 3 → ℝ)) ψ) :
    ∑ j : Fin 3 × Fin 3, ∫ x, (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).apply ψ j x *
        pullRow F (fun k => u (j.1, k)) j.2 x =
      ∑ j : Fin 3 × Fin 3, ∫ x, ψ j x * ∑ p, (cjac F x).adjugate j.2 p *
        (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).apply u (j.1, p) (cmap F x) := by
  set v : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ := fun j => pullRow F (fun k => u (j.1, k)) j.2
  have hv : ∀ j, ContDiff ℝ ∞ (v j) := fun j =>
    contDiff_pullRow hF (fun k => hu (j.1, k)) j.2
  have hg := (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).green_smooth hψ hv
  simp only [conj_trivial, curlOp_formalAdj_apply] at hg
  rw [hg]
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Eventually.of_forall fun x => ?_)
  obtain ⟨a, m⟩ := j
  simp only [curlOp_apply]
  rw [curl_pullRow hF (fun k => hu (a, k)) m x]

/-- Dominated convergence against a continuous compactly supported weight. -/
theorem tendsto_integral_mul_of_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {c : E → ℝ} (hc : Continuous c) (hcs : HasCompactSupport c)
    {g : ℕ → E → ℝ} {g' : E → ℝ} {B : ℝ} (hg : ∀ m, Continuous (g m))
    (hB : ∀ m x, |g m x| ≤ B) (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => g m x) atTop (𝓝 (g' x))) :
    Tendsto (fun m => ∫ x, c x * g m x ∂μ) atTop (𝓝 (∫ x, c x * g' x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => |c x| * B)
    (fun m => (hc.mul (hg m)).aestronglyMeasurable) ?_ (fun m => Eventually.of_forall
      fun x => ?_) ?_
  · exact (hc.abs.mul continuous_const).integrable_of_hasCompactSupport
      (hcs.comp_left (g := fun t : ℝ => |t|) (by simp)).mul_right
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB m x) (abs_nonneg _)
  · filter_upwards [hlim] with x hx
    exact hx.const_mul _

theorem exists_bound_field {ι : Type*} [Fintype ι] {u : ι → (Fin 3 → ℝ) → ℝ}
    (hu : ∀ j, Continuous (u j)) (hus : ∀ j, HasCompactSupport (u j)) :
    ∃ C, 0 ≤ C ∧ ∀ j y, |u j y| ≤ C := by
  choose C hC using fun j => (hus j).exists_bound_of_continuous (hu j)
  refine ⟨∑ j, |C j|, Finset.sum_nonneg fun j _ => abs_nonneg _, fun j y => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hC j y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))

/-- The `1`-form pullback of a matrix field along `Φ`, row by row:
`(Φ^* u)_{ai} = Σ_k ∂ᵢΦ_k · u_{ak} ∘ Φ`, i.e. `DΦᵀ (u_a ∘ Φ)`. -/
def pull1Fun (Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ) :
    Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ :=
  fun j x => ∑ k, lipJac Φ x k j.2 * u (j.1, k) (Φ x)

/-- The `2`-form (cofactor) pullback of a matrix field along `Φ`, row by row:
`(Φ^♭ w)_{ai} = Σ_p adj(DΦ)_{ip} · w_{ap} ∘ Φ`, i.e. `cof(DΦ)ᵀ (w_a ∘ Φ)`. -/
def pull2Fun (Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (w : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ) :
    Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ :=
  fun j x => ∑ p, (lipJac Φ x).adjugate j.2 p * w (j.1, p) (Φ x)

/-- **The weak curl of the pullback of a test field along a Lipschitz map**:
`∫ (Φ^* u) · curl ψ = ∫ (Φ^♭ curl u) · ψ` for smooth compactly supported `u` and `ψ`
(mollify `Φ`, use the smooth identity `integral_curl_pullRow`, and pass to the limit by
dominated convergence: `D(Φ ⋆ ρ_m) → DΦ` almost everywhere and boundedly). -/
theorem integral_curl_pullFun (hΦ : LipschitzWith K Φ) {u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hu : IsTestField (univ : Set (Fin 3 → ℝ)) u) {ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hψ : IsTestField (univ : Set (Fin 3 → ℝ)) ψ) :
    ∑ j : Fin 3 × Fin 3, ∫ x, (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).apply ψ j x *
        pull1Fun Φ u j x =
      ∑ j : Fin 3 × Fin 3, ∫ x, ψ j x *
        pull2Fun Φ ((curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).apply u) j x := by
  set A := (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ (Fin 3 × Fin 3) (Fin 3 × Fin 3))
  have hcu : IsTestField (univ : Set (Fin 3 → ℝ)) (A.apply u) := A.isTestField_apply hu
  have hcψ : IsTestField (univ : Set (Fin 3 → ℝ)) (A.apply ψ) := A.isTestField_apply hψ
  obtain ⟨Cu, hCu0, hCu⟩ := exists_bound_field (fun j => (hu j).continuous)
    (fun j => (hu j).hasCompactSupport)
  obtain ⟨Cw, hCw0, hCw⟩ := exists_bound_field (fun j => (hcu j).continuous)
    (fun j => (hcu j).hasCompactSupport)
  set F := molliComps Φ
  have hF : ∀ m k, ContDiff ℝ ∞ (F m k) := contDiff_molliComps hΦ
  have hJ := ae_tendsto_cjac_molliComps hΦ
  have heq : ∀ m, ∑ j : Fin 3 × Fin 3, ∫ x, A.apply ψ j x *
      pullRow (F m) (fun k => u (j.1, k)) j.2 x =
      ∑ j : Fin 3 × Fin 3, ∫ x, ψ j x * ∑ p, (cjac (F m) x).adjugate j.2 p *
        A.apply u (j.1, p) (cmap (F m) x) := fun m =>
    integral_curl_pullRow (hF m) (fun j => (hu j).contDiff) hψ
  have hL : Tendsto (fun m => ∑ j : Fin 3 × Fin 3, ∫ x, A.apply ψ j x *
      pullRow (F m) (fun k => u (j.1, k)) j.2 x) atTop
      (𝓝 (∑ j : Fin 3 × Fin 3, ∫ x, A.apply ψ j x * pull1Fun Φ u j x)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    refine tendsto_integral_mul_of_bdd (hcψ j).continuous (hcψ j).hasCompactSupport
      (B := 3 * (K * Cu)) (fun m => (contDiff_pullRow (hF m) (fun k => (hu (j.1, k)).contDiff)
        j.2).continuous) (fun m x => ?_) ?_
    · unfold pullRow
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |cd (F m) k j.2 x * u (j.1, k) (cmap (F m) x)| ≤ ∑ _k : Fin 3, (K * Cu) :=
            Finset.sum_le_sum fun k _ => by
              rw [abs_mul]
              exact mul_le_mul (abs_cd_molliComps_le hΦ m k j.2 x) (hCu _ _) (abs_nonneg _) K.2
        _ = 3 * (K * Cu) := by simp
    · filter_upwards [hJ] with x hx
      unfold pullRow pull1Fun
      refine tendsto_finsetSum _ fun k _ => Tendsto.mul ?_ ?_
      · exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hx k) j.2
      · exact ((hu (j.1, k)).continuous.tendsto _).comp (tendsto_cmap_molliComps hΦ x)
  have hR : Tendsto (fun m => ∑ j : Fin 3 × Fin 3, ∫ x, ψ j x * ∑ p, (cjac (F m) x).adjugate j.2 p *
        A.apply u (j.1, p) (cmap (F m) x)) atTop
      (𝓝 (∑ j : Fin 3 × Fin 3, ∫ x, ψ j x * pull2Fun Φ (A.apply u) j x)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    have hcj : ∀ m, Continuous fun x => cjac (F m) x := fun m =>
      continuous_pi fun k => continuous_pi fun i => (contDiff_cd (hF m) k i).continuous
    refine tendsto_integral_mul_of_bdd (hψ j).continuous (hψ j).hasCompactSupport
      (B := 3 * (2 * (K : ℝ) ^ 2 * Cw)) (fun m => ?_) (fun m x => ?_) ?_
    · refine continuous_finsetSum _ fun p _ => Continuous.mul ?_ ?_
      · exact (continuous_apply p).comp ((continuous_apply j.2).comp (hcj m).matrix_adjugate)
      · exact (hcu (j.1, p)).continuous.comp (contDiff_pi.2 (hF m)).continuous
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ p, |(cjac (F m) x).adjugate j.2 p * A.apply u (j.1, p) (cmap (F m) x)| ≤
            ∑ _p : Fin 3, (2 * (K : ℝ) ^ 2 * Cw) :=
            Finset.sum_le_sum fun p _ => by
              rw [abs_mul]
              exact mul_le_mul (abs_adjugate_le (fun k l => abs_cd_molliComps_le hΦ m k l x) _ _)
                (hCw _ _) (abs_nonneg _) (by positivity)
        _ = 3 * (2 * (K : ℝ) ^ 2 * Cw) := by simp
    · filter_upwards [hJ] with x hx
      unfold pull2Fun
      refine tendsto_finsetSum _ fun p _ => Tendsto.mul ?_ ?_
      · have := ((continuous_id.matrix_adjugate).tendsto _).comp hx
        exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 this j.2) p
      · exact ((hcu (j.1, p)).continuous.tendsto _).comp (tendsto_cmap_molliComps hΦ x)
  simp only [heq] at hL
  exact tendsto_nhds_unique hL hR

end LipPull

/-! ### Bi-Lipschitz homeomorphisms of `ℝ³` -/

/-- A **bi-Lipschitz homeomorphism** of `ℝ³`: a bijection `Φ` with inverse `Ψ`, both
`K`-Lipschitz. -/
structure BiLipschitz where
  /-- the map -/
  toFun : (Fin 3 → ℝ) → (Fin 3 → ℝ)
  /-- the inverse -/
  invFun : (Fin 3 → ℝ) → (Fin 3 → ℝ)
  /-- a common Lipschitz constant -/
  K : ℝ≥0
  lipschitz : LipschitzWith K toFun
  lipschitz_inv : LipschitzWith K invFun
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

namespace BiLipschitz

variable (Φ : BiLipschitz)

instance : CoeFun BiLipschitz fun _ => (Fin 3 → ℝ) → (Fin 3 → ℝ) := ⟨BiLipschitz.toFun⟩

/-- The inverse bi-Lipschitz map. -/
def symm : BiLipschitz where
  toFun := Φ.invFun
  invFun := Φ.toFun
  K := Φ.K
  lipschitz := Φ.lipschitz_inv
  lipschitz_inv := Φ.lipschitz
  left_inv := Φ.right_inv
  right_inv := Φ.left_inv

@[simp] theorem symm_apply_apply (x : Fin 3 → ℝ) : Φ.symm (Φ x) = x := Φ.left_inv x
@[simp] theorem apply_symm_apply (y : Fin 3 → ℝ) : Φ (Φ.symm y) = y := Φ.right_inv y
@[simp] theorem symm_symm : Φ.symm.symm = Φ := rfl

theorem injective : Function.Injective Φ := fun x y h => by
  rw [← Φ.symm_apply_apply x, ← Φ.symm_apply_apply y, h]

theorem continuous : Continuous Φ := Φ.lipschitz.continuous

theorem measurable : Measurable Φ := Φ.continuous.measurable

theorem preimage_eq_image_symm (s : Set (Fin 3 → ℝ)) : Φ ⁻¹' s = Φ.symm '' s := by
  ext x; constructor
  · intro hx; exact ⟨Φ x, hx, Φ.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩; change Φ (Φ.symm y) ∈ s; rw [Φ.apply_symm_apply]; exact hy

theorem volume_image_eq_zero {s : Set (Fin 3 → ℝ)} (hs : volume s = 0) : volume (Φ '' s) = 0 :=
  volume_image_eq_zero_of_lipschitzWith Φ.lipschitz hs

theorem volume_preimage_eq_zero {s : Set (Fin 3 → ℝ)} (hs : volume s = 0) :
    volume (Φ ⁻¹' s) = 0 := by
  rw [preimage_eq_image_symm]; exact Φ.symm.volume_image_eq_zero hs

/-- `Φ` maps null sets to null sets and back. -/
theorem quasiMeasurePreserving : QuasiMeasurePreserving Φ volume volume :=
  ⟨Φ.measurable, Measure.AbsolutelyContinuous.mk fun s _ hs => by
    rw [Measure.map_apply Φ.measurable ‹_›]; exact Φ.volume_preimage_eq_zero hs⟩

/-- Almost every point is good: `Φ` is differentiable at `x` and `Φ⁻¹` at `Φ x`. -/
theorem ae_good : ∀ᵐ x, DifferentiableAt ℝ Φ x ∧ DifferentiableAt ℝ Φ.symm (Φ x) := by
  have h1 := Φ.lipschitz.ae_differentiableAt (μ := volume)
  have h2 : ∀ᵐ x, DifferentiableAt ℝ Φ.symm (Φ x) :=
    Φ.quasiMeasurePreserving.ae (Φ.symm.lipschitz.ae_differentiableAt (μ := volume))
  filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩

theorem lipJac_symm_mul_lipJac {x : Fin 3 → ℝ} (h : DifferentiableAt ℝ Φ x ∧
    DifferentiableAt ℝ Φ.symm (Φ x)) : lipJac Φ.symm (Φ x) * lipJac Φ x = 1 :=
  lipJac_mul_lipJac_eq_one Φ.left_inv h.1 h.2

theorem lipJac_mul_lipJac_symm {x : Fin 3 → ℝ} (h : DifferentiableAt ℝ Φ x ∧
    DifferentiableAt ℝ Φ.symm (Φ x)) : lipJac Φ x * lipJac Φ.symm (Φ x) = 1 :=
  mul_eq_one_comm.1 (Φ.lipJac_symm_mul_lipJac h)

theorem abs_lipJac_le (x : Fin 3 → ℝ) (i j : Fin 3) : |lipJac Φ x i j| ≤ Φ.K :=
  Feec.Domain.abs_lipJac_le Φ.lipschitz x i j

theorem abs_det_le_of_abs_le {A : Matrix (Fin 3) (Fin 3) ℝ} {C : ℝ} (hA : ∀ i j, |A i j| ≤ C) :
    |A.det| ≤ 6 * C ^ 3 := by
  have h0 : 0 ≤ C := (abs_nonneg _).trans (hA 0 0)
  have h3 : ∀ a b c d e f : Fin 3, |A a b * A c d * A e f| ≤ C ^ 3 := fun a b c d e f => by
    rw [abs_mul, abs_mul, pow_three]
    exact mul_le_mul (mul_le_mul (hA a b) (hA c d) (abs_nonneg _) h0) (hA e f) (abs_nonneg _)
      (by positivity) |>.trans_eq (by ring)
  rw [Matrix.det_fin_three]
  have := h3 0 0 1 1 2 2; have := h3 0 0 1 2 2 1; have := h3 0 1 1 0 2 2
  have := h3 0 1 1 2 2 0; have := h3 0 2 1 0 2 1; have := h3 0 2 1 1 2 0
  calc |A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
        A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0| ≤
      |A 0 0 * A 1 1 * A 2 2| + |A 0 0 * A 1 2 * A 2 1| + |A 0 1 * A 1 0 * A 2 2| +
        |A 0 1 * A 1 2 * A 2 0| + |A 0 2 * A 1 0 * A 2 1| + |A 0 2 * A 1 1 * A 2 0| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ 6 * C ^ 3 := by linarith

/-- The Jacobian bound `JΦ = |det DΦ| ≤ 6 K³`. -/
theorem abs_det_lipJac_le (x : Fin 3 → ℝ) : |(lipJac Φ x).det| ≤ 6 * (Φ.K : ℝ) ^ 3 :=
  abs_det_le_of_abs_le (Φ.abs_lipJac_le x)

/-- At good points `1 ≤ 6 K³ |det DΦ|`. -/
theorem one_le_abs_det_lipJac {x : Fin 3 → ℝ} (h : DifferentiableAt ℝ Φ x ∧
    DifferentiableAt ℝ Φ.symm (Φ x)) : 1 ≤ 6 * (Φ.K : ℝ) ^ 3 * |(lipJac Φ x).det| := by
  have e := congrArg Matrix.det (Φ.lipJac_symm_mul_lipJac h)
  rw [Matrix.det_mul, Matrix.det_one] at e
  have e' : |(lipJac Φ.symm (Φ x)).det| * |(lipJac Φ x).det| = 1 := by rw [← abs_mul, e, abs_one]
  have := Φ.symm.abs_det_lipJac_le (Φ x)
  rw [← e']
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

/-! #### The change of variables -/

variable {U Ω : Set (Fin 3 → ℝ)}

theorem image_eq (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) : Φ '' U = Ω := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩; exact (hUΩ x).1 hx
  · intro hy; exact ⟨Φ.symm y, (hUΩ _).2 (by rw [Φ.apply_symm_apply]; exact hy),
      Φ.apply_symm_apply y⟩

/-- The good part `D = U ∩ {Φ differentiable}` of `U`. -/
def goodSet (U : Set (Fin 3 → ℝ)) : Set (Fin 3 → ℝ) := U ∩ {x | DifferentiableAt ℝ Φ x}

theorem measurableSet_goodSet (hU : MeasurableSet U) : MeasurableSet (Φ.goodSet U) :=
  hU.inter (measurableSet_of_differentiableAt ℝ Φ)

theorem goodSet_ae_eq (U : Set (Fin 3 → ℝ)) : Φ.goodSet U =ᵐ[volume] U := by
  have hnull : volume {x | ¬ DifferentiableAt ℝ Φ x} = 0 := by
    have := Φ.lipschitz.ae_differentiableAt (μ := volume)
    rwa [ae_iff] at this
  refine ae_eq_set.2 ⟨by rw [goodSet, sdiff_eq_empty.2 inter_subset_left, measure_empty], ?_⟩
  exact measure_mono_null (fun x hx => fun hd => hx.2 ⟨hx.1, hd⟩) hnull

theorem image_goodSet_ae_eq (U : Set (Fin 3 → ℝ)) : Φ '' Φ.goodSet U =ᵐ[volume] Φ '' U := by
  have hsub : Φ '' Φ.goodSet U ⊆ Φ '' U := image_mono inter_subset_left
  have hnull : volume {x | ¬ DifferentiableAt ℝ Φ x} = 0 := by
    have := Φ.lipschitz.ae_differentiableAt (μ := volume)
    rwa [ae_iff] at this
  refine ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 hsub, measure_empty], ?_⟩
  refine measure_mono_null ?_ (Φ.volume_image_eq_zero hnull)
  rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
  refine ⟨x, fun hd => hy ⟨x, ⟨hx, hd⟩, rfl⟩, rfl⟩

theorem hasFDerivWithinAt_goodSet (U : Set (Fin 3 → ℝ)) :
    ∀ x ∈ Φ.goodSet U, HasFDerivWithinAt Φ (fderiv ℝ Φ x) (Φ.goodSet U) x :=
  fun _ hx => hx.2.hasFDerivAt.hasFDerivWithinAt

/-- **Change of variables** along a bi-Lipschitz map (Bochner integral):
`∫_Ω g = ∫_U |det DΦ| g ∘ Φ` for `Ω = Φ(U)`. -/
theorem integral_image (hU : MeasurableSet U) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : (Fin 3 → ℝ) → F) :
    ∫ y in Φ '' U, g y = ∫ x in U, |(lipJac Φ x).det| • g (Φ x) := by
  rw [Measure.restrict_congr_set (Φ.image_goodSet_ae_eq U).symm,
    integral_image_eq_integral_abs_det_fderiv_smul volume (Φ.measurableSet_goodSet hU)
      (Φ.hasFDerivWithinAt_goodSet U) (Φ.injective.injOn),
    Measure.restrict_congr_set (Φ.goodSet_ae_eq U)]
  simp only [det_lipJac]

/-- **Change of variables for integrability.** -/
theorem integrableOn_image_iff (hU : MeasurableSet U) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : (Fin 3 → ℝ) → F) :
    IntegrableOn g (Φ '' U) ↔ IntegrableOn (fun x => |(lipJac Φ x).det| • g (Φ x)) U := by
  rw [IntegrableOn, Measure.restrict_congr_set (Φ.image_goodSet_ae_eq U).symm,
    ← IntegrableOn, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      (Φ.measurableSet_goodSet hU) (Φ.hasFDerivWithinAt_goodSet U) (Φ.injective.injOn),
    IntegrableOn, IntegrableOn, Measure.restrict_congr_set (Φ.goodSet_ae_eq U)]
  simp only [det_lipJac]

end BiLipschitz

/-- `‖f‖² = ∫ f²` in real `L²`. -/
theorem L2.norm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp [sq]

theorem L2.norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : MemLp g 2 μ) : ‖hg.toLp g‖ ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
  rw [L2.norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

theorem L2.integrable_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    Integrable (fun x => (f x) ^ 2) μ :=
  (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)

namespace BiLipschitz

variable (Φ : BiLipschitz) {U Ω : Set (Fin 3 → ℝ)}

/-- `Φ : (U, dx) → (Ω, dy)` maps null sets to null sets and back. -/
theorem quasiMeasurePreserving_restrict (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) :
    QuasiMeasurePreserving Φ (volume.restrict U) (volume.restrict Ω) := by
  refine ⟨Φ.measurable, Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_⟩
  rw [Measure.map_apply Φ.measurable hS, Measure.restrict_apply (Φ.measurable hS)]
  rw [Measure.restrict_apply hS] at h0
  refine measure_mono_null (fun x hx => ?_) (Φ.volume_preimage_eq_zero h0)
  exact ⟨hx.1, (hUΩ x).1 hx.2⟩

theorem ae_good_restrict (U : Set (Fin 3 → ℝ)) : ∀ᵐ x ∂volume.restrict U,
    DifferentiableAt ℝ Φ x ∧ DifferentiableAt ℝ Φ.symm (Φ x) :=
  ae_restrict_of_ae Φ.ae_good

/-- **Change of variables** `∫_Ω g = ∫_U |det DΦ| g ∘ Φ` (`Φ(U) = Ω`). -/
theorem integral_comp (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) (g : (Fin 3 → ℝ) → ℝ) :
    ∫ y in Ω, g y = ∫ x in U, |(lipJac Φ x).det| * g (Φ x) := by
  rw [← Φ.image_eq hUΩ, Φ.integral_image hU]; rfl

theorem integrableOn_comp_iff (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    (g : (Fin 3 → ℝ) → ℝ) :
    IntegrableOn g Ω ↔ IntegrableOn (fun x => |(lipJac Φ x).det| * g (Φ x)) U := by
  rw [← Φ.image_eq hUΩ, Φ.integrableOn_image_iff hU]; rfl

/-- **Composition with `Φ` is bounded on `L²`**: `f ∘ Φ ∈ L²(U)` for `f ∈ L²(Ω)`. -/
theorem memLp_comp (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) {f : (Fin 3 → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) : MemLp (fun x => f (Φ x)) 2 (volume.restrict U) := by
  have hm : AEStronglyMeasurable (fun x => f (Φ x)) (volume.restrict U) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving (Φ.quasiMeasurePreserving_restrict hUΩ)
  rw [memLp_two_iff_integrable_sq hm]
  have hi := (Φ.integrableOn_comp_iff hU hUΩ (fun y => f y ^ 2)).1
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf)
  refine (hi.const_mul (6 * (Φ.K : ℝ) ^ 3)).mono' (hm.pow 2) ?_
  filter_upwards [Φ.ae_good_restrict U] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← mul_assoc]
  exact le_mul_of_one_le_left (sq_nonneg _) (Φ.one_le_abs_det_lipJac hx)

theorem integral_comp_sq_le (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    {f : (Fin 3 → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict Ω)) :
    ∫ x in U, f (Φ x) ^ 2 ≤ 6 * (Φ.K : ℝ) ^ 3 * ∫ y in Ω, f y ^ 2 := by
  have hi := (Φ.integrableOn_comp_iff hU hUΩ (fun y => f y ^ 2)).1
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf)
  rw [Φ.integral_comp hU hUΩ, ← integral_const_mul]
  refine integral_mono_ae ((memLp_two_iff_integrable_sq
    (Φ.memLp_comp hU hUΩ hf).aestronglyMeasurable).1 (Φ.memLp_comp hU hUΩ hf)) (hi.const_mul _) ?_
  filter_upwards [Φ.ae_good_restrict U] with x hx
  rw [← mul_assoc]
  exact le_mul_of_one_le_left (sq_nonneg _) (Φ.one_le_abs_det_lipJac hx)

/-! #### Weighted pullbacks of `L²` fields -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A matrix weight on `U`: a.e. strongly measurable entries bounded by `C`. -/
structure Weight (U : Set (Fin 3 → ℝ)) (ι κ : Type*) where
  /-- the weight -/
  M : (Fin 3 → ℝ) → ι → κ → ℝ
  /-- the bound -/
  C : ℝ
  C_nonneg : 0 ≤ C
  meas : ∀ i k, AEStronglyMeasurable (fun x => M x i k) (volume.restrict U)
  bound : ∀ᵐ x ∂volume.restrict U, ∀ i k, |M x i k| ≤ C

/-- The weighted pullback of a field `u`: `(P u)ᵢ(x) = Σₖ M(x)ᵢₖ uₖ(Φ x)`. -/
def wpullFun (M : (Fin 3 → ℝ) → ι → κ → ℝ) (u : κ → (Fin 3 → ℝ) → ℝ) :
    ι → (Fin 3 → ℝ) → ℝ :=
  fun i x => ∑ k, M x i k * u k (Φ x)

variable (W : Weight U ι κ)

omit [Fintype ι] in
theorem memLp_wpullFun (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    {u : κ → (Fin 3 → ℝ) → ℝ} (hu : ∀ k, MemLp (u k) 2 (volume.restrict Ω)) (i : ι) :
    MemLp (Φ.wpullFun W.M u i) 2 (volume.restrict U) := by
  unfold wpullFun
  refine memLp_finsetSum _ fun k _ => ?_
  have hc := Φ.memLp_comp hU hUΩ (hu k)
  refine hc.of_le_mul (c := W.C) ((W.meas i k).mul hc.aestronglyMeasurable) ?_
  filter_upwards [W.bound] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hx i k) (norm_nonneg _)

omit [Fintype ι] in
/-- The pointwise Cauchy–Schwarz bound for the weighted sum. -/
theorem sq_wpullFun_le {M : (Fin 3 → ℝ) → ι → κ → ℝ} {C : ℝ} {x : Fin 3 → ℝ}
    (hx : ∀ i k, |M x i k| ≤ C) (u : κ → (Fin 3 → ℝ) → ℝ) (i : ι) :
    Φ.wpullFun M u i x ^ 2 ≤ Fintype.card κ * C ^ 2 * ∑ k, u k (Φ x) ^ 2 := by
  unfold wpullFun
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg fun (k : κ) _ => sq_nonneg (u k (Φ x)))
  have hk : ∀ k ∈ (Finset.univ : Finset κ), M x i k ^ 2 ≤ C ^ 2 := fun k _ => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i k) 2
  calc ∑ k, M x i k ^ 2 ≤ ∑ _k : κ, C ^ 2 := Finset.sum_le_sum hk
    _ = Fintype.card κ * C ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Fintype ι] in
theorem integral_sq_wpullFun_le (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    {u : κ → (Fin 3 → ℝ) → ℝ} (hu : ∀ k, MemLp (u k) 2 (volume.restrict Ω)) (i : ι) :
    ∫ x in U, Φ.wpullFun W.M u i x ^ 2 ≤
      Fintype.card κ * W.C ^ 2 * (6 * (Φ.K : ℝ) ^ 3) * ∑ k, ∫ y in Ω, u k y ^ 2 := by
  have hc : ∀ k, MemLp (fun x => u k (Φ x)) 2 (volume.restrict U) := fun k =>
    Φ.memLp_comp hU hUΩ (hu k)
  have hci : ∀ k, Integrable (fun x => u k (Φ x) ^ 2) (volume.restrict U) := fun k =>
    (memLp_two_iff_integrable_sq (hc k).aestronglyMeasurable).1 (hc k)
  calc ∫ x in U, Φ.wpullFun W.M u i x ^ 2 ≤
        ∫ x in U, Fintype.card κ * W.C ^ 2 * ∑ k, u k (Φ x) ^ 2 := by
        refine integral_mono_ae ((memLp_two_iff_integrable_sq
          (Φ.memLp_wpullFun W hU hUΩ hu i).aestronglyMeasurable).1
            (Φ.memLp_wpullFun W hU hUΩ hu i))
          ((integrable_finsetSum _ fun k _ => hci k).const_mul _) ?_
        filter_upwards [W.bound] with x hx
        exact Φ.sq_wpullFun_le hx u i
    _ = Fintype.card κ * W.C ^ 2 * ∑ k, ∫ x in U, u k (Φ x) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun k _ => hci k]
    _ ≤ Fintype.card κ * W.C ^ 2 * ∑ k, (6 * (Φ.K : ℝ) ^ 3 * ∫ y in Ω, u k y ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ =>
          Φ.integral_comp_sq_le hU hUΩ (hu k)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- **The weighted pullback** `L²(Ω; ℝ^κ) → L²(U; ℝ^ι)`, `(P u)ᵢ = Σₖ Mᵢₖ uₖ ∘ Φ`. -/
def wpull (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) :
    L2F ℝ Ω κ →L[ℝ] L2F ℝ U ι :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 fun i =>
        (Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp (u k)) i).toLp _
      map_add' := fun u v => by
        ext1 i
        refine Lp.ext ?_
        have hq := Φ.quasiMeasurePreserving_restrict hUΩ
        have hadd : ∀ᵐ x ∂volume.restrict U, ∀ k, ((u k + v k : L2 ℝ Ω) : _ → ℝ) (Φ x) =
            (u k : _ → ℝ) (Φ x) + (v k : _ → ℝ) (Φ x) := by
          rw [ae_all_iff]; intro k
          exact hq.ae_eq_comp (Lp.coeFn_add (u k) (v k))
        filter_upwards [(Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp ((u + v) k)) i).coeFn_toLp,
          (Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp (u k)) i).coeFn_toLp,
          (Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp (v k)) i).coeFn_toLp,
          Lp.coeFn_add ((Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp (u k)) i).toLp _)
            ((Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp (v k)) i).toLp _), hadd]
          with x h1 h2 h3 h4 h5
        simp only [PiLp.add_apply] at h1 h4 ⊢
        rw [h1, h4, Pi.add_apply, h2, h3]
        simp only [wpullFun, h5, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        ext1 i
        refine Lp.ext ?_
        have hq := Φ.quasiMeasurePreserving_restrict hUΩ
        have hsm : ∀ᵐ x ∂volume.restrict U, ∀ k, ((c • u k : L2 ℝ Ω) : _ → ℝ) (Φ x) =
            c * (u k : _ → ℝ) (Φ x) := by
          rw [ae_all_iff]; intro k
          exact hq.ae_eq_comp (Lp.coeFn_smul c (u k))
        filter_upwards [(Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp ((c • u) k)) i).coeFn_toLp,
          (Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp (u k)) i).coeFn_toLp,
          Lp.coeFn_smul c ((Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp (u k)) i).toLp _), hsm]
          with x h1 h2 h3 h4
        simp only [PiLp.smul_apply, RingHom.id_apply] at h1 h3 ⊢
        rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul]
        simp only [wpullFun, h4, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring }
    (Real.sqrt (Fintype.card ι * (Fintype.card κ * W.C ^ 2 * (6 * (Φ.K : ℝ) ^ 3))))
    (fun u => by
      refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_pow, Real.sq_sqrt (by positivity), PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      simp only [L2.norm_toLp_sq]
      simp only [L2.norm_sq_eq_integral]
      calc ∑ i, ∫ x in U, Φ.wpullFun W.M (fun k => (u k : _ → ℝ)) i x ^ 2 ≤
            ∑ _i : ι, Fintype.card κ * W.C ^ 2 * (6 * (Φ.K : ℝ) ^ 3) *
              ∑ k, ∫ y in Ω, (u k : _ → ℝ) y ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              Φ.integral_sq_wpullFun_le W hU hUΩ (fun k => Lp.memLp (u k)) i
        _ = Fintype.card ι * (Fintype.card κ * W.C ^ 2 * (6 * (Φ.K : ℝ) ^ 3)) *
              ∑ k, ∫ y in Ω, (u k : _ → ℝ) y ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring)

theorem coeFn_wpull (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) (u : L2F ℝ Ω κ) (i : ι) :
    ((Φ.wpull W hU hUΩ u) i : (Fin 3 → ℝ) → ℝ) =ᵐ[volume.restrict U]
      Φ.wpullFun W.M (fun k => (u k : (Fin 3 → ℝ) → ℝ)) i :=
  (Φ.memLp_wpullFun W hU hUΩ (fun k => Lp.memLp (u k)) i).coeFn_toLp

end BiLipschitz

namespace BiLipschitz

variable (Φ : BiLipschitz) {U Ω : Set (Fin 3 → ℝ)}

/-! #### Weights acting on the rows of matrix fields -/

/-- The weight acting on each row of a matrix field by the matrix `N(x)`:
`(rowW N)_{(a,i),(b,k)} = δ_{ab} N_{ik}`. -/
def rowW (N : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ) :
    (Fin 3 → ℝ) → Fin 3 × Fin 3 → Fin 3 × Fin 3 → ℝ :=
  fun x j l => if l.1 = j.1 then N x j.2 l.2 else 0

theorem wpullFun_rowW (N : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ)
    (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ) (j : Fin 3 × Fin 3) (x : Fin 3 → ℝ) :
    Φ.wpullFun (rowW N) u j x = ∑ k, N x j.2 k * u (j.1, k) (Φ x) := by
  simp [wpullFun, rowW, Fintype.sum_prod_type, ite_mul]

/-- A row weight with a.e. strongly measurable entries bounded by `C`. -/
def rowWeight (N : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hmeas : ∀ i k, AEStronglyMeasurable (fun x => N x i k) (volume.restrict U))
    (hb : ∀ᵐ x ∂volume.restrict U, ∀ i k, |N x i k| ≤ C) :
    Weight U (Fin 3 × Fin 3) (Fin 3 × Fin 3) where
  M := rowW N
  C := C
  C_nonneg := hC
  meas j l := by
    unfold rowW
    by_cases h : l.1 = j.1
    · simp only [h, ite_true]; exact hmeas _ _
    · simp only [h, ite_false]; exact aestronglyMeasurable_const
  bound := by
    filter_upwards [hb] with x hx j l
    unfold rowW
    by_cases h : l.1 = j.1
    · simp only [h, ite_true]; exact hx _ _
    · simp only [h, ite_false, abs_zero]; exact hC

theorem measurable_lipJac_apply (Ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (k i : Fin 3) :
    Measurable fun x => lipJac Ψ x k i := by
  simp only [lipJac_apply]
  exact (measurable_pi_apply k).comp (measurable_fderiv_apply_const ℝ Ψ _)

theorem measurable_adjugate_lipJac_apply (Ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (i p : Fin 3) :
    Measurable fun x => (lipJac Ψ x).adjugate i p := by
  have h := measurable_lipJac_apply Ψ
  simp only [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases p <;> simp <;> fun_prop

/-- The weight of the `1`-form pullback, `DΦᵀ` on each row. -/
def w1 (U : Set (Fin 3 → ℝ)) : Weight U (Fin 3 × Fin 3) (Fin 3 × Fin 3) :=
  rowWeight (fun x i k => lipJac Φ x k i) Φ.K Φ.K.2
    (fun i k => (measurable_lipJac_apply Φ k i).aestronglyMeasurable)
    (Eventually.of_forall fun x i k => Φ.abs_lipJac_le x k i)

/-- The weight of the `2`-form pullback, `adj(DΦ) = cof(DΦ)ᵀ` on each row. -/
def w2 (U : Set (Fin 3 → ℝ)) : Weight U (Fin 3 × Fin 3) (Fin 3 × Fin 3) :=
  rowWeight (fun x i p => (lipJac Φ x).adjugate i p) (2 * (Φ.K : ℝ) ^ 2) (by positivity)
    (fun i p => (measurable_adjugate_lipJac_apply Φ i p).aestronglyMeasurable)
    (Eventually.of_forall fun x i p => abs_adjugate_le (Φ.abs_lipJac_le x) i p)

/-- The `1`-form pullback `Φ^* : L²(Ω; ℝ³ˣ³) → L²(U; ℝ³ˣ³)`, `(Φ^* u)_a = DΦᵀ (u_a ∘ Φ)`. -/
def pull1 (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) :
    L2F ℝ Ω (Fin 3 × Fin 3) →L[ℝ] L2F ℝ U (Fin 3 × Fin 3) :=
  Φ.wpull (Φ.w1 U) hU hUΩ

/-- The `2`-form pullback `Φ^♭ : L²(Ω; ℝ³ˣ³) → L²(U; ℝ³ˣ³)`, `(Φ^♭ w)_a = adj(DΦ) (w_a ∘ Φ)`. -/
def pull2 (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) :
    L2F ℝ Ω (Fin 3 × Fin 3) →L[ℝ] L2F ℝ U (Fin 3 × Fin 3) :=
  Φ.wpull (Φ.w2 U) hU hUΩ

theorem wpullFun_w1 (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ) (j : Fin 3 × Fin 3) (x : Fin 3 → ℝ) :
    Φ.wpullFun (Φ.w1 U).M u j x = pull1Fun Φ u j x := by
  rw [show (Φ.w1 U).M = rowW (fun x i k => lipJac Φ x k i) from rfl, wpullFun_rowW]; rfl

theorem wpullFun_w2 (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ) (j : Fin 3 × Fin 3) (x : Fin 3 → ℝ) :
    Φ.wpullFun (Φ.w2 U).M u j x = pull2Fun Φ u j x := by
  rw [show (Φ.w2 U).M = rowW (fun x i p => (lipJac Φ x).adjugate i p) from rfl, wpullFun_rowW]; rfl

/-! #### Weighted pullbacks of test fields -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem coeFn_wpull_testField (W : Weight U ι κ) (hU : MeasurableSet U)
    (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) {f : κ → (Fin 3 → ℝ) → ℝ} (hf : IsTestField Ω f) (i : ι) :
    ((Φ.wpull W hU hUΩ (testField hf)) i : (Fin 3 → ℝ) → ℝ) =ᵐ[volume.restrict U]
      Φ.wpullFun W.M f i := by
  have hq := Φ.quasiMeasurePreserving_restrict hUΩ
  have h : ∀ᵐ x ∂volume.restrict U, ∀ k, ((testField hf k : L2 ℝ Ω) : _ → ℝ) (Φ x) = f k (Φ x) := by
    rw [ae_all_iff]; intro k
    exact hq.ae_eq_comp (coeFn_testField hf k)
  filter_upwards [Φ.coeFn_wpull W hU hUΩ (testField hf) i, h] with x h1 h2
  rw [h1]
  simp only [wpullFun, h2]

/-- `⟪P φ, ψ⟫_{L²(U)} = Σᵢ ∫ (P φ)ᵢ ψᵢ` over `ℝ³`, for test fields `φ` on `Ω`, `ψ` on `U`. -/
theorem inner_wpull_testField (W : Weight U ι κ) (hU : MeasurableSet U)
    (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) {f : κ → (Fin 3 → ℝ) → ℝ} (hf : IsTestField Ω f)
    {ψ : ι → (Fin 3 → ℝ) → ℝ} (hψ : IsTestField U ψ) :
    ⟪Φ.wpull W hU hUΩ (testField hf), testField hψ⟫_ℝ =
      ∑ i, ∫ x, Φ.wpullFun W.M f i x * ψ i x := by
  rw [inner_testField]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [conj_trivial]
  rw [← integral_restrict_of_eq_zero (Ω := U) fun x hx => by
    rw [(hψ i).eq_zero_of_notMem hx, mul_zero]]
  refine integral_congr_ae ?_
  filter_upwards [Φ.coeFn_wpull_testField W hU hUΩ hf i] with x hx
  rw [hx]

/-! #### The `1`-form pullback commutes with `curl` -/

/-- The row-wise curl on `ℝ³ˣ³`-valued fields over `ℝ`. -/
local notation "curl3" =>
  (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ (Fin 3 × Fin 3) (Fin 3 × Fin 3))

/-- The support of the pullback of a test field lies in the compact `Φ⁻¹(supp u) ⊆ U`. -/
theorem pullFun_eq_zero_of_notMem {u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hx : x ∉ Φ.symm '' ⋃ j, tsupport (u j)) (j : Fin 3 × Fin 3) : pull1Fun Φ u j x = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  have : Φ x ∉ tsupport (u (j.1, k)) := fun h =>
    hx ⟨Φ x, mem_iUnion.2 ⟨_, h⟩, Φ.symm_apply_apply x⟩
  rw [image_eq_zero_of_notMem_tsupport this, mul_zero]

theorem isCompact_symm_image_tsupport (hU : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    {u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ} (hu : IsTestField Ω u) :
    IsCompact (Φ.symm '' ⋃ j, tsupport (u j)) ∧ Φ.symm '' ⋃ j, tsupport (u j) ⊆ U := by
  refine ⟨(isCompact_iUnion fun j => (hu j).hasCompactSupport.isCompact).image
    Φ.symm.continuous, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 hy
  rw [hU, Φ.apply_symm_apply]
  exact (hu j).tsupport_subset hj

/-- **On test fields, `curl (Φ^* u) = Φ^♭ (curl u)` in `D(curl_min(U))`.** -/
theorem pull1_testField_mem_minimal (hU : IsOpen U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    {u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ} (hu : IsTestField Ω u) :
    (Φ.pull1 hU.measurableSet hUΩ (testField hu),
      Φ.pull2 hU.measurableSet hUΩ (testField ((curl3).isTestField_apply hu))) ∈
      ((curl3).minimal U).graph := by
  set A := (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ (Fin 3 × Fin 3) (Fin 3 × Fin 3))
  set v := Φ.pull1 hU.measurableSet hUΩ (testField hu)
  set w := Φ.pull2 hU.measurableSet hUΩ (testField (A.isTestField_apply hu))
  have huniv : IsTestField (univ : Set (Fin 3 → ℝ)) u := fun j => (hu j).mono (subset_univ _)
  have hAadj : ∀ f, A.formalAdj.apply f = A.apply f := fun f => curlOp_formalAdj_apply f
  have hweak : ∀ ψ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ, ∀ hψ : IsTestField U ψ,
      ⟪w, testField hψ⟫_ℝ = ⟪v, testField (A.formalAdj.isTestField_apply hψ)⟫_ℝ := by
    intro ψ hψ
    have hψu : IsTestField (univ : Set (Fin 3 → ℝ)) ψ := fun j => (hψ j).mono (subset_univ _)
    have e1 := Φ.inner_wpull_testField (Φ.w2 U) hU.measurableSet hUΩ (A.isTestField_apply hu) hψ
    have e2 := Φ.inner_wpull_testField (Φ.w1 U) hU.measurableSet hUΩ hu
      (A.formalAdj.isTestField_apply hψ)
    change ⟪Φ.wpull (Φ.w2 U) _ _ _, _⟫_ℝ = ⟪Φ.wpull (Φ.w1 U) _ _ _, _⟫_ℝ
    rw [e1, e2]
    simp only [wpullFun_w1, wpullFun_w2, hAadj]
    have := integral_curl_pullFun Φ.lipschitz huniv hψu
    calc ∑ i, ∫ x, pull2Fun Φ (A.apply u) i x * ψ i x =
          ∑ i, ∫ x, ψ i x * pull2Fun Φ (A.apply u) i x :=
          Finset.sum_congr rfl fun i _ =>
            integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
      _ = ∑ i, ∫ x, A.apply ψ i x * pull1Fun Φ u i x := this.symm
      _ = ∑ i, ∫ x, pull1Fun Φ u i x * A.apply ψ i x :=
          Finset.sum_congr rfl fun i _ =>
            integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hmax : v ∈ (A.maximal U).domain := (A.mem_maximal_domain_iff hU).2 ⟨w, hweak⟩
  have hval : A.maximal U ⟨v, hmax⟩ = w := A.maximal_apply_eq hU ⟨v, hmax⟩ hweak
  obtain ⟨hK, hKU⟩ := Φ.isCompact_symm_image_tsupport hUΩ hu
  obtain ⟨hmin, hmin'⟩ := A.mem_minimal_of_maximal_of_support_subset hU hK hKU ⟨v, hmax⟩
    (fun j => by
      filter_upwards [Φ.coeFn_wpull_testField (Φ.w1 U) hU.measurableSet hUΩ hu j] with x hx hxK
      change (Φ.wpull (Φ.w1 U) _ _ _ j : _ → ℝ) x = 0
      rw [hx, wpullFun_w1, Φ.pullFun_eq_zero_of_notMem hxK])
  rw [LinearPMap.mem_graph_iff]
  exact ⟨⟨v, hmin⟩, rfl, hmin'.trans hval⟩

/-- **The `1`-form pullback maps `H̊(curl, Ω)` into `H̊(curl, U)` and commutes with `curl`**:
`curl_min(Φ^* u) = Φ^♭ (curl_min u)` (`Φ` bi-Lipschitz, `Φ(U) = Ω`), by graph closure from test
fields (`pull1_testField_mem_minimal`). -/
theorem pull1_mem_minimal_curl (hU : IsOpen U) (hΩ : IsOpen Ω) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    (u : ((curl3).minimal Ω).domain) :
    ∃ h : Φ.pull1 hU.measurableSet hUΩ u ∈
        ((curl3).minimal U).domain,
      (curl3).minimal U ⟨_, h⟩ =
        Φ.pull2 hU.measurableSet hUΩ
          ((curl3).minimal Ω u) := by
  set F := Prod.map (Φ.pull1 hU.measurableSet hUΩ) (Φ.pull2 hU.measurableSet hUΩ)
  have hF : Continuous F := (Φ.pull1 _ hUΩ).continuous.prodMap (Φ.pull2 _ hUΩ).continuous
  have hm : MapsTo F ((curl3).testGraph Ω : Set _) (((curl3).minimal U).graph : Set _) := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact Φ.pull1_testField_mem_minimal hU hUΩ hφ
  have hmem := (curl3).mem_closure_minimal hΩ u
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
  have hgr : F ((u : L2F ℝ Ω (Fin 3 × Fin 3)), (curl3).minimal Ω u) ∈
      ((curl3).minimal U).graph := by
    have := map_mem_closure hF hmem hm
    rwa [((curl3).isClosed_minimal hU).closure_eq] at this
  exact ⟨LinearPMap.mem_domain_of_mem_graph hgr,
    ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph hgr)).2 hgr).symm⟩

end BiLipschitz

/-- If `A B = 1` and `|B_{ik}| ≤ C`, then `|η|² ≤ 9 C² |Aᵀ η|²`. -/
theorem sum_sq_le_of_mul_eq_one {A B : Matrix (Fin 3) (Fin 3) ℝ} (hAB : A * B = 1) {C : ℝ}
    (hB : ∀ i k, |B i k| ≤ C) (η : Fin 3 → ℝ) :
    ∑ k, η k ^ 2 ≤ 9 * C ^ 2 * ∑ i, (∑ k, A k i * η k) ^ 2 := by
  set ζ : Fin 3 → ℝ := fun i => ∑ k, A k i * η k
  have hη : ∀ k, η k = ∑ i, B i k * ζ i := fun k => by
    simp only [ζ, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ i, B i k * (A l i * η l) = (A * B) l k * η l := fun l => by
      rw [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [this, hAB, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hC2 : ∀ k, ∑ i, B i k ^ 2 ≤ 3 * C ^ 2 := fun k => by
    calc ∑ i, B i k ^ 2 ≤ ∑ _i : Fin 3, C ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB i k) 2
      _ = 3 * C ^ 2 := by simp
  have hk : ∀ k, η k ^ 2 ≤ 3 * C ^ 2 * ∑ i, ζ i ^ 2 := fun k => by
    rw [hη k]
    exact (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans
      (mul_le_mul_of_nonneg_right (hC2 k) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  calc ∑ k, η k ^ 2 ≤ ∑ _k : Fin 3, 3 * C ^ 2 * ∑ i, ζ i ^ 2 := Finset.sum_le_sum fun k _ => hk k
    _ = 9 * C ^ 2 * ∑ i, ζ i ^ 2 := by simp; ring

namespace BiLipschitz

variable (Φ : BiLipschitz) {U Ω : Set (Fin 3 → ℝ)}

/-- **The `1`-form pullback is bounded below**: `‖u‖ ≤ c ‖Φ^* u‖` with `c² = 54 K⁵`. -/
theorem norm_le_norm_pull1 (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    (u : L2F ℝ Ω (Fin 3 × Fin 3)) :
    ‖u‖ ≤ Real.sqrt (6 * (Φ.K : ℝ) ^ 3 * (9 * (Φ.K : ℝ) ^ 2)) * ‖Φ.pull1 hU hUΩ u‖ := by
  set c1 := 6 * (Φ.K : ℝ) ^ 3
  set c2 := 9 * (Φ.K : ℝ) ^ 2
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [L2.norm_sq_eq_integral]
  have hm : ∀ j, MemLp (fun x => (u j : _ → ℝ) (Φ x)) 2 (volume.restrict U) := fun j =>
    Φ.memLp_comp hU hUΩ (Lp.memLp (u j))
  have hi : ∀ j, Integrable (fun x => (u j : _ → ℝ) (Φ x) ^ 2) (volume.restrict U) := fun j =>
    (memLp_two_iff_integrable_sq (hm j).aestronglyMeasurable).1 (hm j)
  have step1 : ∀ j, ∫ y in Ω, (u j : _ → ℝ) y ^ 2 ≤ c1 * ∫ x in U, (u j : _ → ℝ) (Φ x) ^ 2 :=
    fun j => by
      rw [Φ.integral_comp hU hUΩ, ← integral_const_mul]
      refine integral_mono_ae ?_ ((hi j).const_mul _) (Eventually.of_forall fun x => ?_)
      · have := (Φ.integrableOn_comp_iff hU hUΩ (fun y => (u j : _ → ℝ) y ^ 2)).1
          (L2.integrable_sq (u j))
        exact this
      · exact mul_le_mul_of_nonneg_right (Φ.abs_det_lipJac_le x) (sq_nonneg _)
  have hp := fun j => Φ.coeFn_wpull (Φ.w1 U) hU hUΩ u j
  have step2 : ∑ j, ∫ x in U, (u j : _ → ℝ) (Φ x) ^ 2 ≤
      c2 * ∑ j, ∫ x in U, ((Φ.pull1 hU hUΩ u) j : _ → ℝ) x ^ 2 := by
    rw [← integral_finsetSum _ fun j _ => hi j, ← integral_finsetSum _ fun j _ =>
      L2.integrable_sq _, ← integral_const_mul]
    refine integral_mono_ae (integrable_finsetSum _ fun j _ => hi j)
      ((integrable_finsetSum _ fun j _ => L2.integrable_sq _).const_mul _) ?_
    have hp' : ∀ᵐ x ∂volume.restrict U, ∀ j, ((Φ.pull1 hU hUΩ u) j : _ → ℝ) x =
        pull1Fun Φ (fun j => (u j : _ → ℝ)) j x := by
      rw [ae_all_iff]; intro j
      filter_upwards [hp j] with x hx
      rw [show (Φ.pull1 hU hUΩ u) = Φ.wpull (Φ.w1 U) hU hUΩ u from rfl, hx, wpullFun_w1]
    filter_upwards [hp', Φ.ae_good_restrict U] with x hx hg
    simp only [hx, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.mul_sum]
    exact sum_sq_le_of_mul_eq_one (Φ.lipJac_mul_lipJac_symm hg) (Φ.symm.abs_lipJac_le _)
      (fun k => (u (a, k) : _ → ℝ) (Φ x))
  calc ∑ j, ∫ y in Ω, (u j : _ → ℝ) y ^ 2 ≤ ∑ j, c1 * ∫ x in U, (u j : _ → ℝ) (Φ x) ^ 2 :=
        Finset.sum_le_sum fun j _ => step1 j
    _ = c1 * ∑ j, ∫ x in U, (u j : _ → ℝ) (Φ x) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ c1 * (c2 * ∑ j, ∫ x in U, ((Φ.pull1 hU hUΩ u) j : _ → ℝ) x ^ 2) :=
        mul_le_mul_of_nonneg_left step2 hc1
    _ = _ := by ring

end BiLipschitz

/-- The row-wise `gradᵗ = -div` on `ℝ³ˣ³`-valued fields over `ℝ`. -/
local notation "divT" =>
  ConstCoeffOp.formalAdj (gradOp 3 3 : ConstCoeffOp (Fin 3 → ℝ) ℝ (Fin 3) (Fin 3 × Fin 3))

/-- Dominated convergence against an integrable weight. -/
theorem tendsto_integral_mul_of_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : Integrable g μ) {h : ℕ → α → ℝ} {h' : α → ℝ} {B : ℝ}
    (hh : ∀ m, AEStronglyMeasurable (h m) μ) (hB : ∀ m, ∀ᵐ x ∂μ, |h m x| ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => h m x) atTop (𝓝 (h' x))) :
    Tendsto (fun m => ∫ x, g x * h m x ∂μ) atTop (𝓝 (∫ x, g x * h' x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => |g x| * B)
    (fun m => hg.aestronglyMeasurable.mul (hh m)) (hg.abs.mul_const _) (fun m => ?_) ?_
  · filter_upwards [hB m] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  · filter_upwards [hlim] with x hx
    exact hx.const_mul _

theorem integrable_L2_of_finite {Ω : Set (Fin 3 → ℝ)} (hfin : volume Ω ≠ ⊤) (f : L2 ℝ Ω) :
    Integrable (f : (Fin 3 → ℝ) → ℝ) (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hfin
  exact (Lp.memLp f).integrable one_le_two

/-- **The weak divergence against Lipschitz test functions**: for `u ∈ D((gradᵗ)_max(Ω))`
(`|Ω| < ∞`) and compactly supported Lipschitz `χ` with support in `Ω`,
`Σₐ ∫_Ω (gradᵗ u)ₐ χₐ = Σ_{a,j} ∫_Ω u_{aj} ∂ⱼ χₐ` (mollify `χ`, dominated convergence). -/
theorem integral_maximal_divT_lipschitz {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)
    (hfin : volume Ω ≠ ⊤) (u : (ConstCoeffOp.maximal Ω divT).domain)
    {χ : Fin 3 → (Fin 3 → ℝ) → ℝ} {L : ℝ≥0} (hχ : ∀ a, LipschitzWith L (χ a))
    (hχs : ∀ a, HasCompactSupport (χ a)) (hχΩ : ∀ a, tsupport (χ a) ⊆ Ω) :
    ∑ a, ∫ y in Ω, (ConstCoeffOp.maximal Ω divT u a : _ → ℝ) y * χ a y =
      ∑ j : Fin 3 × Fin 3, ∫ y in Ω, ((u : L2F ℝ Ω (Fin 3 × Fin 3)) j : _ → ℝ) y *
        fderiv ℝ (χ j.1) y (coordDir j.2) := by
  set w := ConstCoeffOp.maximal Ω divT u
  set χm : ℕ → Fin 3 → (Fin 3 → ℝ) → ℝ := fun m a => molli (bumpSeq m) (χ a)
  have hev : ∀ᶠ m in atTop, IsTestField Ω (χm m) :=
    Filter.eventually_all.2 fun a => eventually_isTest_molli (hχ a) (hχs a) hΩ (hχΩ a)
  have heq : ∀ᶠ m in atTop, ∑ a, ∫ y in Ω, (w a : _ → ℝ) y * χm m a y =
      ∑ j : Fin 3 × Fin 3, ∫ y in Ω, ((u : L2F ℝ Ω (Fin 3 × Fin 3)) j : _ → ℝ) y *
        fderiv ℝ (χm m j.1) y (coordDir j.2) := by
    filter_upwards [hev] with m hm
    have h := ConstCoeffOp.maximal_inner_testField divT hΩ u hm
    rw [inner_testField, inner_testField] at h
    simp only [conj_trivial, ConstCoeffOp.formalAdj_formalAdj, gradOp_apply] at h
    exact h
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_bound_field (fun a => (hχ a).continuous) hχs
  have hL : Tendsto (fun m => ∑ a, ∫ y in Ω, (w a : _ → ℝ) y * χm m a y) atTop
      (𝓝 (∑ a, ∫ y in Ω, (w a : _ → ℝ) y * χ a y)) := by
    refine tendsto_finsetSum _ fun a _ => ?_
    refine tendsto_integral_mul_of_integrable (integrable_L2_of_finite hfin (w a)) (B := Cχ)
      (fun m => (contDiff_molli _
        (hχ a).continuous.locallyIntegrable).continuous.aestronglyMeasurable)
      (fun m => Eventually.of_forall fun y => abs_molli_le (fun y => hCχ a y) _ y)
      (Eventually.of_forall fun y => tendsto_molli_of_continuous (hχ a).continuous y)
  have hR : Tendsto (fun m => ∑ j : Fin 3 × Fin 3, ∫ y in Ω,
      ((u : L2F ℝ Ω (Fin 3 × Fin 3)) j : _ → ℝ) y * fderiv ℝ (χm m j.1) y (coordDir j.2)) atTop
      (𝓝 (∑ j : Fin 3 × Fin 3, ∫ y in Ω, ((u : L2F ℝ Ω (Fin 3 × Fin 3)) j : _ → ℝ) y *
        fderiv ℝ (χ j.1) y (coordDir j.2))) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    refine tendsto_integral_mul_of_integrable (integrable_L2_of_finite hfin _) (B := L)
      (fun m => ?_) (fun m => Eventually.of_forall fun y => ?_)
      (ae_restrict_of_ae (ae_tendsto_fderiv_molli (hχ j.1) (coordDir j.2)))
    · exact ((contDiff_molli _ (hχ j.1).continuous.locallyIntegrable).continuous_fderiv
        (by simp) |>.clm_apply continuous_const).aestronglyMeasurable
    · refine (abs_fderiv_molli_le (hχ j.1) _ y _).trans ?_
      calc (L : ℝ) * ‖(coordDir j.2 : Fin 3 → ℝ)‖ ≤ L * 1 :=
            mul_le_mul_of_nonneg_left (norm_coordDir_le_one j.2) L.2
        _ = L := mul_one _
  exact tendsto_nhds_unique_of_eventuallyEq hL hR heq

namespace BiLipschitz

variable (Φ : BiLipschitz) {U Ω : Set (Fin 3 → ℝ)}

theorem measurable_det_lipJac (Ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) :
    Measurable fun x => (lipJac Ψ x).det := by
  have h := measurable_lipJac_apply Ψ
  simp only [Matrix.det_fin_three]
  fun_prop

/-- The Jacobian weight `|det DΦ|` on vector fields. -/
def wJ (U : Set (Fin 3 → ℝ)) : Weight U (Fin 3) (Fin 3) where
  M x a b := if b = a then |(lipJac Φ x).det| else 0
  C := 6 * (Φ.K : ℝ) ^ 3
  C_nonneg := by positivity
  meas a b := by
    by_cases h : b = a
    · simp only [h, ite_true]
      exact (continuous_abs.measurable.comp (measurable_det_lipJac Φ)).aestronglyMeasurable
    · simp only [h, ite_false]; exact aestronglyMeasurable_const
  bound := Eventually.of_forall fun x a b => by
    by_cases h : b = a
    · simp only [h, ite_true, abs_abs]; exact Φ.abs_det_lipJac_le x
    · simp only [h, ite_false, abs_zero]; positivity

/-- The weight of the Piola transform, `|det DΦ| DΦ⁻¹` on each row. -/
def wP (U : Set (Fin 3 → ℝ)) : Weight U (Fin 3 × Fin 3) (Fin 3 × Fin 3) :=
  rowWeight (fun x i k => |(lipJac Φ x).det| * lipJac Φ.symm (Φ x) i k) (6 * (Φ.K : ℝ) ^ 3 * Φ.K)
    (by positivity)
    (fun i k => ((continuous_abs.measurable.comp (measurable_det_lipJac Φ)).mul
      ((measurable_lipJac_apply Φ.symm i k).comp Φ.measurable)).aestronglyMeasurable)
    (Eventually.of_forall fun x i k => by
      rw [abs_mul, abs_abs]
      exact mul_le_mul (Φ.abs_det_lipJac_le x) (Φ.symm.abs_lipJac_le _ i k) (abs_nonneg _)
        (by positivity))

/-- The Jacobian pullback `f ↦ |det DΦ| f ∘ Φ` of vector fields. -/
def pullJ (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) :
    L2F ℝ Ω (Fin 3) →L[ℝ] L2F ℝ U (Fin 3) :=
  Φ.wpull (Φ.wJ U) hU hUΩ

/-- The **Piola transform** of matrix fields, `(P u)_a = |det DΦ| DΦ⁻¹ (u_a ∘ Φ)`. -/
def piola (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) :
    L2F ℝ Ω (Fin 3 × Fin 3) →L[ℝ] L2F ℝ U (Fin 3 × Fin 3) :=
  Φ.wpull (Φ.wP U) hU hUΩ

theorem wpullFun_wJ (f : Fin 3 → (Fin 3 → ℝ) → ℝ) (a : Fin 3) (x : Fin 3 → ℝ) :
    Φ.wpullFun (Φ.wJ U).M f a x = |(lipJac Φ x).det| * f a (Φ x) := by
  simp [wpullFun, wJ, ite_mul]

theorem wpullFun_wP (u : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ) (j : Fin 3 × Fin 3)
    (x : Fin 3 → ℝ) : Φ.wpullFun (Φ.wP U).M u j x =
      ∑ k, |(lipJac Φ x).det| * lipJac Φ.symm (Φ x) j.2 k * u (j.1, k) (Φ x) := by
  rw [show (Φ.wP U).M = rowW (fun x i k => |(lipJac Φ x).det| * lipJac Φ.symm (Φ x) i k) from rfl,
    wpullFun_rowW]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `⟪P u, ψ⟫_{L²(U)} = Σᵢ ∫_U (P u)ᵢ ψᵢ`. -/
theorem inner_wpull_testField' (W : Weight U ι κ) (hU : MeasurableSet U)
    (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω) (u : L2F ℝ Ω κ) {ψ : ι → (Fin 3 → ℝ) → ℝ}
    (hψ : IsTestField U ψ) :
    ⟪Φ.wpull W hU hUΩ u, testField hψ⟫_ℝ =
      ∑ i, ∫ x in U, Φ.wpullFun W.M (fun k => (u k : (Fin 3 → ℝ) → ℝ)) i x * ψ i x := by
  rw [inner_testField]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [Φ.coeFn_wpull W hU hUΩ u i] with x hx
  rw [hx]

/-- The chain rule for a smooth `φ` composed with a Lipschitz map at a point of
differentiability. -/
theorem fderiv_comp_apply_coordDir {Ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {y : Fin 3 → ℝ} (hΨ : DifferentiableAt ℝ Ψ y) (k : Fin 3) :
    fderiv ℝ (fun y => φ (Ψ y)) y (coordDir k) =
      ∑ i, lipJac Ψ y i k * fderiv ℝ φ (Ψ y) (coordDir i) := by
  rw [show (fun y => φ (Ψ y)) = φ ∘ Ψ from rfl,
    fderiv_comp y (hφ.differentiable (by simp) _) hΨ, ContinuousLinearMap.comp_apply]
  have : fderiv ℝ Ψ y (coordDir k) = ∑ i, lipJac Ψ y i k • (coordDir i : Fin 3 → ℝ) := by
    ext l; simp [coordDir, Finset.sum_apply, Pi.single_apply, lipJac_apply]
  rw [this, map_sum]
  simp [smul_eq_mul]

/-- **The Piola transform maps `H(div, Ω)` into `H(div, U)`**:
`div (P u) = |det DΦ| (div u) ∘ Φ` (row-wise, in the form `(gradᵗ)_max`), for `Φ` bi-Lipschitz with
`Φ(U) = Ω`, `|U|, |Ω| < ∞`. Tested against `φ ∈ C_c^∞(U)`, the change of variables turns both
sides into integrals over `Ω` against the Lipschitz test functions `φ ∘ Φ⁻¹`, where the weak
divergence still applies (`integral_maximal_divT_lipschitz`); the chain rule
`∂ⱼ(φ ∘ Φ⁻¹) = Σᵢ ∂ⱼ(Φ⁻¹)ᵢ (∂ᵢ φ) ∘ Φ⁻¹` holds almost everywhere. -/
theorem piola_mem_maximal_divT (hU : IsOpen U) (hΩ : IsOpen Ω) (hfinU : volume U ≠ ⊤)
    (hfin : volume Ω ≠ ⊤) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    (u : (ConstCoeffOp.maximal Ω divT).domain) :
    ∃ h : Φ.piola hU.measurableSet hUΩ u ∈ (ConstCoeffOp.maximal U divT).domain,
      ConstCoeffOp.maximal U divT ⟨_, h⟩ =
        Φ.pullJ hU.measurableSet hUΩ (ConstCoeffOp.maximal Ω divT u) := by
  set w := ConstCoeffOp.maximal Ω divT u
  set uf : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ := fun j => ((u : L2F ℝ Ω (Fin 3 × Fin 3)) j : _ → ℝ)
  have hweak : ∀ φ : Fin 3 → (Fin 3 → ℝ) → ℝ, ∀ hφ : IsTestField U φ,
      ⟪Φ.pullJ hU.measurableSet hUΩ w, testField hφ⟫_ℝ =
        ⟪Φ.piola hU.measurableSet hUΩ u, testField ((divT).formalAdj.isTestField_apply hφ)⟫_ℝ := by
    intro φ hφ
    set χ : Fin 3 → (Fin 3 → ℝ) → ℝ := fun a y => φ a (Φ.symm y)
    choose Cφ hCφ using fun a => (hφ a).contDiff.lipschitzWith_of_hasCompactSupport
      (hφ a).hasCompactSupport (by simp)
    have hχL : ∀ a, LipschitzWith ((∑ b, Cφ b) * Φ.K) (χ a) := fun a =>
      ((hCφ a).weaken (Finset.single_le_sum (f := Cφ) (fun b _ => bot_le)
        (Finset.mem_univ a))).comp Φ.symm.lipschitz
    have hKc : ∀ a, IsCompact (Φ '' tsupport (φ a)) := fun a =>
      (hφ a).hasCompactSupport.isCompact.image Φ.continuous
    have hχ0 : ∀ a y, y ∉ Φ '' tsupport (φ a) → χ a y = 0 := fun a y hy =>
      image_eq_zero_of_notMem_tsupport (f := φ a)
        (fun h : Φ.symm y ∈ tsupport (φ a) => hy ⟨_, h, Φ.apply_symm_apply y⟩)
    have hχs : ∀ a, HasCompactSupport (χ a) := fun a => HasCompactSupport.intro (hKc a) (hχ0 a)
    have hχΩ : ∀ a, tsupport (χ a) ⊆ Ω := fun a => by
      refine (closure_minimal (fun y hy => ?_) (hKc a).isClosed).trans ?_
      · by_contra h; exact hy (hχ0 a y h)
      · rintro _ ⟨x, hx, rfl⟩; exact (hUΩ x).1 ((hφ a).tsupport_subset hx)
    have hP11 := integral_maximal_divT_lipschitz hΩ hfin u hχL hχs hχΩ
    rw [pullJ, piola, Φ.inner_wpull_testField' (Φ.wJ U), Φ.inner_wpull_testField' (Φ.wP U)]
    simp only [wpullFun_wJ, wpullFun_wP, ConstCoeffOp.formalAdj_formalAdj, gradOp_apply]
    have hL : ∀ a, ∫ x in U, |(lipJac Φ x).det| * (w a : _ → ℝ) (Φ x) * φ a x =
        ∫ y in Ω, (w a : _ → ℝ) y * χ a y := fun a => by
      rw [Φ.integral_comp hU.measurableSet hUΩ]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [χ, symm_apply_apply]; ring
    simp only [hL]
    rw [hP11]
    -- the right side
    obtain ⟨Cd, hCd0, hCd⟩ := exists_bound_field (ι := Fin 3 × Fin 3)
      (u := fun j => fun x => fderiv ℝ (φ j.1) x (coordDir j.2))
      (fun j => ((hφ j.1).contDiff.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun j => (hφ j.1).hasCompactSupport.fderiv_apply (𝕜 := ℝ) _)
    set g : Fin 3 → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ := fun a i k y =>
      lipJac Φ.symm y i k * uf (a, k) y * fderiv ℝ (φ a) (Φ.symm y) (coordDir i)
    have hgi : ∀ a i k, Integrable (g a i k) (volume.restrict Ω) := fun a i k => by
      have h1 := integrable_L2_of_finite hfin ((u : L2F ℝ Ω (Fin 3 × Fin 3)) (a, k))
      have hm : AEStronglyMeasurable (fun y => lipJac Φ.symm y i k *
          fderiv ℝ (φ a) (Φ.symm y) (coordDir i)) (volume.restrict Ω) :=
        ((measurable_lipJac_apply Φ.symm i k).mul
          ((((hφ a).contDiff.continuous_fderiv (by simp)).clm_apply
            continuous_const).measurable.comp Φ.symm.measurable)).aestronglyMeasurable
      refine (h1.bdd_mul hm (c := Φ.K * Cd) (Eventually.of_forall fun y => ?_)).congr
        (Eventually.of_forall fun y => by simp only [g]; ring)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (Φ.symm.abs_lipJac_le y i k) (hCd (a, i) _) (abs_nonneg _) Φ.K.2
    have hRj : ∀ a i, ∫ x in U,
        (∑ k, |(lipJac Φ x).det| * lipJac Φ.symm (Φ x) i k * uf (a, k) (Φ x)) *
        fderiv ℝ (φ a) x (coordDir i) = ∑ k, ∫ y in Ω, g a i k y := fun a i => by
      have hUi : ∀ k, Integrable (fun x => |(lipJac Φ x).det| * lipJac Φ.symm (Φ x) i k *
          uf (a, k) (Φ x) * fderiv ℝ (φ a) x (coordDir i)) (volume.restrict U) := fun k => by
        have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hfinU
        have h1 := (Φ.memLp_comp hU.measurableSet hUΩ (Lp.memLp
          ((u : L2F ℝ Ω (Fin 3 × Fin 3)) (a, k)))).integrable one_le_two
        have hm : AEStronglyMeasurable (fun x => |(lipJac Φ x).det| * lipJac Φ.symm (Φ x) i k *
            fderiv ℝ (φ a) x (coordDir i)) (volume.restrict U) :=
          (((continuous_abs.measurable.comp (measurable_det_lipJac Φ)).mul
            ((measurable_lipJac_apply Φ.symm i k).comp Φ.measurable)).mul
            (((hφ a).contDiff.continuous_fderiv (by simp)).clm_apply
              continuous_const).measurable).aestronglyMeasurable
        refine (h1.bdd_mul hm (c := 6 * (Φ.K : ℝ) ^ 3 * Φ.K * Cd)
          (Eventually.of_forall fun x => ?_)).congr (Eventually.of_forall fun x => by ring)
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
        exact mul_le_mul (mul_le_mul (Φ.abs_det_lipJac_le x) (Φ.symm.abs_lipJac_le _ i k)
          (abs_nonneg _) (by positivity)) (hCd (a, i) x) (abs_nonneg _) (by positivity)
      rw [show (fun x => (∑ k, |(lipJac Φ x).det| * lipJac Φ.symm (Φ x) i k * uf (a, k) (Φ x)) *
          fderiv ℝ (φ a) x (coordDir i)) =
          fun x => ∑ k, |(lipJac Φ x).det| * lipJac Φ.symm (Φ x) i k *
          uf (a, k) (Φ x) * fderiv ℝ (φ a) x (coordDir i) from funext fun x => Finset.sum_mul _ _ _,
        integral_finsetSum _ fun k _ => hUi k]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Φ.integral_comp hU.measurableSet hUΩ]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [g, symm_apply_apply]; ring
    have hLj : ∀ a k, ∫ y in Ω, uf (a, k) y * fderiv ℝ (χ a) y (coordDir k) =
        ∑ i, ∫ y in Ω, g a i k y := fun a k => by
      rw [← integral_finsetSum _ fun i _ => hgi a i k]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (Φ.symm.lipschitz.ae_differentiableAt (μ := volume))]
        with y hy
      rw [show χ a = fun y => φ a (Φ.symm y) from rfl,
        fderiv_comp_apply_coordDir (hφ a).contDiff hy, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [g]; ring
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl fun k _ => hLj a k, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (hRj a i).symm
  have hmax : Φ.piola hU.measurableSet hUΩ u ∈ (ConstCoeffOp.maximal U divT).domain :=
    ((divT).mem_maximal_domain_iff hU).2 ⟨_, hweak⟩
  exact ⟨hmax, (divT).maximal_apply_eq hU ⟨_, hmax⟩ hweak⟩

end BiLipschitz

namespace BiLipschitz

/-- The identity of `ℝ³`. -/
def refl : BiLipschitz where
  toFun := id
  invFun := id
  K := 1
  lipschitz := LipschitzWith.id
  lipschitz_inv := LipschitzWith.id
  left_inv _ := rfl
  right_inv _ := rfl

variable (Φ : BiLipschitz) {U Ω : Set (Fin 3 → ℝ)}

theorem K_pos : 0 < (Φ.K : ℝ) := by
  rcases (Φ.K.2).lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 : Φ.K = 0 := NNReal.coe_eq_zero.1 h.symm
    have hc : ∀ x y, Φ x = Φ y := fun x y => by
      have := Φ.lipschitz.dist_le_mul x y
      rw [h0, NNReal.coe_zero, zero_mul] at this
      exact dist_le_zero.1 this
    have := Φ.injective (hc 0 (fun _ => 1))
    have h1 := congrFun this 0
    simp at h1

/-- The weight of the coefficient `ε = |det DΦ| DΦ⁻¹ DΦ⁻ᵀ` on each row (`DΦ⁻¹ = D(Φ⁻¹) ∘ Φ`). -/
def wE (U : Set (Fin 3 → ℝ)) : Weight U (Fin 3 × Fin 3) (Fin 3 × Fin 3) :=
  rowWeight
    (fun x i k => |(lipJac Φ x).det| * ∑ l, lipJac Φ.symm (Φ x) i l * lipJac Φ.symm (Φ x) k l)
    (6 * (Φ.K : ℝ) ^ 3 * (3 * (Φ.K : ℝ) ^ 2)) (by positivity)
    (fun i k => ((continuous_abs.measurable.comp (measurable_det_lipJac Φ)).mul
      (Finset.measurable_sum _ fun l _ =>
        ((measurable_lipJac_apply Φ.symm i l).comp Φ.measurable).mul
          ((measurable_lipJac_apply Φ.symm k l).comp Φ.measurable))).aestronglyMeasurable)
    (Eventually.of_forall fun x i k => by
      rw [abs_mul, abs_abs]
      refine mul_le_mul (Φ.abs_det_lipJac_le x) ?_ (abs_nonneg _) (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l, |lipJac Φ.symm (Φ x) i l * lipJac Φ.symm (Φ x) k l| ≤ ∑ _l : Fin 3, (Φ.K : ℝ) ^ 2 :=
            Finset.sum_le_sum fun l _ => by
              rw [abs_mul, sq]
              exact mul_le_mul (Φ.symm.abs_lipJac_le _ i l) (Φ.symm.abs_lipJac_le _ k l)
                (abs_nonneg _)
                Φ.K.2
        _ = 3 * (Φ.K : ℝ) ^ 2 := by simp)

/-- **The coefficient** `ε = |det DΦ| DΦ⁻¹ DΦ⁻ᵀ` acting on the rows of matrix fields on `U`:
bounded, and with `ε Φ^* = P` (the Piola transform). -/
def coeff (hU : MeasurableSet U) : L2F ℝ U (Fin 3 × Fin 3) →L[ℝ] L2F ℝ U (Fin 3 × Fin 3) :=
  refl.wpull (Φ.wE U) hU (fun _ => Iff.rfl)

/-- **`ε Φ^* u = P u`**: the coefficient turns the `1`-form pullback into the Piola transform
(`|det DΦ| DΦ⁻¹ DΦ⁻ᵀ DΦᵀ = |det DΦ| DΦ⁻¹` at almost every point). -/
theorem coeff_pull1 (hU : MeasurableSet U) (hUΩ : ∀ x, x ∈ U ↔ Φ x ∈ Ω)
    (u : L2F ℝ Ω (Fin 3 × Fin 3)) :
    Φ.coeff hU (Φ.pull1 hU hUΩ u) = Φ.piola hU hUΩ u := by
  ext1 j
  refine Lp.ext ?_
  have h1 : ∀ᵐ x ∂volume.restrict U, ∀ l, ((Φ.pull1 hU hUΩ u) l : _ → ℝ) x =
      pull1Fun Φ (fun j => (u j : _ → ℝ)) l x := by
    rw [ae_all_iff]; intro l
    filter_upwards [Φ.coeFn_wpull (Φ.w1 U) hU hUΩ u l] with x hx
    rw [show (Φ.pull1 hU hUΩ u) = Φ.wpull (Φ.w1 U) hU hUΩ u from rfl, hx, wpullFun_w1]
  filter_upwards [refl.coeFn_wpull (Φ.wE U) hU (fun _ => Iff.rfl) (Φ.pull1 hU hUΩ u) j,
    Φ.coeFn_wpull (Φ.wP U) hU hUΩ u j, h1, Φ.ae_good_restrict U] with x hE hP h1 hg
  rw [show Φ.coeff hU (Φ.pull1 hU hUΩ u) = refl.wpull (Φ.wE U) hU (fun _ => Iff.rfl)
    (Φ.pull1 hU hUΩ u) from rfl, hE, show Φ.piola hU hUΩ u = Φ.wpull (Φ.wP U) hU hUΩ u from rfl,
    hP, wpullFun_wP, show (Φ.wE U).M = rowW (fun x i k => |(lipJac Φ x).det| *
      ∑ l, lipJac Φ.symm (Φ x) i l * lipJac Φ.symm (Φ x) k l) from rfl]
  simp only [wpullFun_rowW]
  rw [show refl.toFun x = x from rfl]
  simp only [h1, pull1Fun]
  have hAB := Φ.lipJac_mul_lipJac_symm hg
  set A := lipJac Φ x
  set B := lipJac Φ.symm (Φ x)
  have key : ∀ m, ∑ k, (|A.det| * ∑ l, B j.2 l * B k l) * A m k = |A.det| * B j.2 m := fun m => by
    have : ∀ l, ∑ k, A m k * B k l = (A * B) m l := fun l => (Matrix.mul_apply).symm
    calc ∑ k, (|A.det| * ∑ l, B j.2 l * B k l) * A m k =
          |A.det| * ∑ l, B j.2 l * ∑ k, A m k * B k l := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
      _ = |A.det| * B j.2 m := by
          simp only [this, hAB, Matrix.one_apply]
          simp
  calc ∑ k, (|A.det| * ∑ l, B j.2 l * B k l) * ∑ m, A m k * (u (j.1, m) : _ → ℝ) (Φ x) =
        ∑ m, (∑ k, (|A.det| * ∑ l, B j.2 l * B k l) * A m k) * (u (j.1, m) : _ → ℝ) (Φ x) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ m, |A.det| * B j.2 m * (u (j.1, m) : _ → ℝ) (Φ x) := by simp only [key]

/-- The pointwise coercivity `ξᵀ ε ξ = |det A| |Bᵀ ξ|² ≥ |ξ|² / (54 K⁵)` for `B A = 1`. -/
theorem coercive_pointwise {A B : Matrix (Fin 3) (Fin 3) ℝ} (hBA : B * A = 1) {K : ℝ}
    (hK : 0 < K) (hA : ∀ i k, |A i k| ≤ K) (hd : 1 ≤ 6 * K ^ 3 * |A.det|) (ξ : Fin 3 → ℝ) :
    1 / (6 * K ^ 3 * (9 * K ^ 2)) * ∑ i, ξ i ^ 2 ≤
      ∑ i, (∑ k, (|A.det| * ∑ l, B i l * B k l) * ξ k) * ξ i := by
  have e : ∑ i, (∑ k, (|A.det| * ∑ l, B i l * B k l) * ξ k) * ξ i =
      |A.det| * ∑ l, (∑ i, B i l * ξ i) ^ 2 := by
    simp only [Fin.sum_univ_three]; ring
  rw [e]
  have h9 := sum_sq_le_of_mul_eq_one hBA hA ξ
  have hd' : 1 / (6 * K ^ 3) ≤ |A.det| := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hS : 0 ≤ ∑ l, (∑ i, B i l * ξ i) ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  calc 1 / (6 * K ^ 3 * (9 * K ^ 2)) * ∑ i, ξ i ^ 2 =
        1 / (6 * K ^ 3) * ((∑ i, ξ i ^ 2) / (9 * K ^ 2)) := by field_simp
    _ ≤ 1 / (6 * K ^ 3) * ∑ l, (∑ i, B i l * ξ i) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_iff₀ (by positivity)]; linarith
    _ ≤ |A.det| * ∑ l, (∑ i, B i l * ξ i) ^ 2 := mul_le_mul_of_nonneg_right hd' hS

/-- **The coefficient is uniformly coercive**: `‖v‖² / (54 K⁵) ≤ ⟪ε v, v⟫`. -/
theorem coeff_coercive (hU : MeasurableSet U) (v : L2F ℝ U (Fin 3 × Fin 3)) :
    1 / (6 * (Φ.K : ℝ) ^ 3 * (9 * (Φ.K : ℝ) ^ 2)) * ‖v‖ ^ 2 ≤ ⟪Φ.coeff hU v, v⟫_ℝ := by
  set lam := 1 / (6 * (Φ.K : ℝ) ^ 3 * (9 * (Φ.K : ℝ) ^ 2))
  rw [PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
  simp only [L2.norm_sq_eq_integral, MeasureTheory.L2.inner_def]
  have hE : ∀ᵐ x ∂volume.restrict U, ∀ l, ((Φ.coeff hU v) l : _ → ℝ) x =
      ∑ k, (|(lipJac Φ x).det| * ∑ m, lipJac Φ.symm (Φ x) l.2 m * lipJac Φ.symm (Φ x) k m) *
        (v (l.1, k) : _ → ℝ) x := by
    rw [ae_all_iff]; intro l
    filter_upwards [refl.coeFn_wpull (Φ.wE U) hU (fun _ => Iff.rfl) v l] with x hx
    rw [show Φ.coeff hU v = refl.wpull (Φ.wE U) hU (fun _ => Iff.rfl) v from rfl, hx,
      show (Φ.wE U).M = rowW (fun x i k => |(lipJac Φ x).det| *
        ∑ l, lipJac Φ.symm (Φ x) i l * lipJac Φ.symm (Φ x) k l) from rfl, wpullFun_rowW]
    rfl
  rw [Finset.mul_sum, ← integral_finsetSum _ fun j _ => L2.integrable_inner (𝕜 := ℝ) _ _]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun j _ => (L2.integrable_sq _).const_mul _]
  refine integral_mono_ae (integrable_finsetSum _ fun j _ => (L2.integrable_sq _).const_mul _)
    (integrable_finsetSum _ fun j _ => L2.integrable_inner (𝕜 := ℝ) _ _) ?_
  filter_upwards [hE, Φ.ae_good_restrict U] with x hx hg
  simp only [hx, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.mul_sum]
  have := coercive_pointwise (Φ.lipJac_symm_mul_lipJac hg) Φ.K_pos (Φ.abs_lipJac_le x)
    (Φ.one_le_abs_det_lipJac hg) (fun i => (v (a, i) : _ → ℝ) x)
  refine this.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

end BiLipschitz

end Feec.Domain
