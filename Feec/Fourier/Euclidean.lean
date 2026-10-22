module

public import Mathlib.Analysis.Fourier.LpSpace
public import Feec.Fourier.ClosedRange
public import Feec.Fourier.FibreReducing

/-!
# Symbol complexes on the whole space `ℝᵈ`

A constant-coefficient complex on `ℝᵈ` is, after the `L²` Fourier transform (Plancherel), a symbol
complex over `ℝᵈ` with Lebesgue measure, with symbols `S.m i j (2πx)` (the convention
`𝓕 f (x) = ∫ e^{-2πi ⟪y, x⟫} f y dy`, under which `∂_c ↦ 2πi x_c`). This file sets up that model
for any finite index type `d`, `𝕜 = ℝ, ℂ`, and any complex shape, and proves:

* **homogeneous symbols do not have closed range** (`not_closedRangeAt`): unlike the torus
  (`Feec.Fourier.Torus.closedRangeAt_of_gap`), there is no Poincaré inequality at low
  frequencies, for every nonzero operator of positive order.

## Main definitions and results

* `Euclidean.scale x = 2πx`, `Euclidean.symbolComplex S`, `Euclidean.complex S`.
* `Euclidean.fibreReducing`.
* `Euclidean.not_closedRangeAt`, `Euclidean.not_dual_closedRangeAt`.
* `Euclidean.fourier F : L²(ℝᵈ; F) ≃ₗᵢ L²(ℝᵈ; F)`: Mathlib's Plancherel isometry, which identifies
  the model with fields on `ℝᵈ`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10–4.11 (Props 4.17, 4.19 on `ℝ³`)
* Mathlib, `Mathlib.Analysis.Fourier.LpSpace` (the `L²` Fourier transform, Plancherel)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal
open MeasureTheory LinearPMap Set

namespace Feec.Fourier.Euclidean

variable {d : Type*} [Fintype d]

/-- The frequency `2πx` of the point `x` of Fourier space. -/
def scale (x : EuclideanSpace ℝ d) : EuclideanSpace ℝ d := (2 * Real.pi) • x

theorem continuous_scale : Continuous (scale (d := d)) := continuous_const_smul _

theorem measurable_scale : Measurable (scale (d := d)) := continuous_scale.measurable

omit [Fintype d] in
@[simp] theorem scale_neg (x : EuclideanSpace ℝ d) : scale (-x) = -scale x := smul_neg _ _

/-! ### The whole-space model of a fibre complex -/

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  [∀ i, FiniteDimensional 𝕜 (E i)]

/-- The whole-space symbol complex of a continuous family of fibre complexes: symbols
`S.m i j (2πx)` on `L²(ℝᵈ)`. -/
def symbolComplex (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E) :
    SymbolComplex 𝕜 (volume : Measure (EuclideanSpace ℝ d)) c E :=
  S.toSymbolComplex _ scale measurable_scale.aemeasurable

@[simp] theorem symbolComplex_m (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E) (i j : ι)
    (x : EuclideanSpace ℝ d) : (symbolComplex S).m i j x = S.m i j (scale x) := rfl

variable [∀ i, CompleteSpace (E i)]

/-- **The Hilbert complex of a constant-coefficient complex on `ℝᵈ`** (Fourier side). -/
def complex (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E) :
    HilbertComplex 𝕜 c fun i => Lp (E i) 2 (volume : Measure (EuclideanSpace ℝ d)) :=
  (symbolComplex S).toHilbertComplex

/-- Fibre reducing subspaces with measurable fibre projections. -/
theorem fibreReducing {S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E}
    {K : ∀ i, EuclideanSpace ℝ d → Submodule 𝕜 (E i)} [∀ i ξ, (K i ξ).HasOrthogonalProjection]
    (h : S.IsFibreReducing K) (meas : ∀ i, Measurable fun ξ => (K i ξ).starProjection) :
    FibreReducing (symbolComplex S) fun i x => K i (scale x) :=
  h.toFibreReducing _ scale _ fun i => by
    have : ProperSpace (E i →L[𝕜] E i) := FiniteDimensional.proper_rclike 𝕜 _
    have : SecondCountableTopology (E i →L[𝕜] E i) := secondCountable_of_proper
    exact ((meas i).comp measurable_scale).aestronglyMeasurable

/-- **No closed range on `ℝᵈ`**: if the incoming symbol is homogeneous of positive degree and not
identically zero, the boundaries are not closed (no Poincaré inequality, by scaling to low
frequencies). -/
theorem not_closedRangeAt {S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E} {i : ι} {r : ℕ}
    (hr : 0 < r) (hS : S.IsHomogeneous (c.prev i) i r) (hne : S.m (c.prev i) i ≠ 0) :
    ¬ (complex S).ClosedRangeAt i := by
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀, S.m (c.prev i) i ξ₀ ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨v, hv⟩ : ∃ v, S.m (c.prev i) i ξ₀ v ≠ 0 := by
    by_contra h; push Not at h; exact hξ₀ (ContinuousLinearMap.ext h)
  set M := ‖S.m (c.prev i) i ξ₀‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  have hcont := S.cont (c.prev i) i
  -- a ball around `ξ₀` where `m ζ v ≠ 0` and `‖m ζ‖ ≤ M`
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ ζ ∈ Metric.ball ξ₀ δ,
      S.m (c.prev i) i ζ v ≠ 0 ∧ ‖S.m (c.prev i) i ζ‖ ≤ M := by
    have h1 : {ζ | S.m (c.prev i) i ζ v ≠ 0} ∈ nhds ξ₀ :=
      (isOpen_ne_fun (hcont.clm_apply continuous_const) continuous_const).mem_nhds hv
    have h2 : {ζ | ‖S.m (c.prev i) i ζ‖ < M} ∈ nhds ξ₀ :=
      (isOpen_lt hcont.norm continuous_const).mem_nhds (by simp [hM])
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem h1 h2)
    exact ⟨δ, hδ, fun ζ hζ => ⟨(hsub hζ).1, (hsub hζ).2.le⟩⟩
  refine (symbolComplex S).not_closedRangeAt fun ε hε => ?_
  set t := min 1 (ε / M) with ht
  have htpos : 0 < t := lt_min one_pos (div_pos hε hMpos)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htM : t ^ r * M ≤ ε := by
    have h1 : t ^ r ≤ t := pow_le_of_le_one htpos.le ht1 hr.ne'
    have h2 : t * M ≤ ε := by
      have := min_le_right 1 (ε / M)
      rw [← ht] at this
      calc t * M ≤ ε / M * M := mul_le_mul_of_nonneg_right this hMpos.le
        _ = ε := div_mul_cancel₀ _ hMpos.ne'
    nlinarith
  have h2pi : 0 < 2 * Real.pi := by positivity
  set s := Metric.ball ((t / (2 * Real.pi)) • ξ₀) (t * δ / (2 * Real.pi))
  refine ⟨s, measurableSet_ball, (Metric.measure_ball_pos _ _ (by positivity)).ne',
    measure_ball_lt_top.ne, v, fun x hx => ?_⟩
  -- `2π x = t ζ` with `ζ ∈ B(ξ₀, δ)`
  set ζ := (2 * Real.pi / t) • x
  have hx' : scale x = t • ζ := by
    simp only [scale, ζ, smul_smul]
    rw [mul_div_cancel₀ _ htpos.ne']
  have hζ : ζ ∈ Metric.ball ξ₀ δ := by
    rw [Metric.mem_ball] at hx ⊢
    have e : ζ - ξ₀ = (2 * Real.pi / t) • (x - (t / (2 * Real.pi)) • ξ₀) := by
      simp only [ζ, smul_sub, smul_smul]
      rw [div_mul_div_comm, mul_comm (2 * Real.pi) t, div_self (by positivity), one_smul]
    rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      ← dist_eq_norm]
    calc 2 * Real.pi / t * dist x ((t / (2 * Real.pi)) • ξ₀)
        < 2 * Real.pi / t * (t * δ / (2 * Real.pi)) :=
          mul_lt_mul_of_pos_left hx (by positivity)
      _ = δ := by field_simp
  obtain ⟨hζv, hζM⟩ := hball ζ hζ
  rw [symbolComplex_m, hx', hS t ζ htpos]
  refine ⟨?_, ?_⟩
  · rw [_root_.smul_apply, smul_ne_zero_iff]
    exact ⟨by exact_mod_cast (pow_pos htpos r).ne', hζv⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    calc t ^ r * ‖S.m (c.prev i) i ζ‖ ≤ t ^ r * M :=
          mul_le_mul_of_nonneg_left hζM (by positivity)
      _ ≤ ε := htM

/-! ### Plancherel -/

variable (d) in
/-- **Plancherel**: the `L²` Fourier transform `L²(ℝᵈ; F) ≃ₗᵢ L²(ℝᵈ; F)` (Mathlib's
`MeasureTheory.Lp.fourierTransformₗᵢ`), which identifies the Fourier model with fields on `ℝᵈ`. -/
def fourier (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    Lp F 2 (volume : Measure (EuclideanSpace ℝ d)) ≃ₗᵢ[ℂ]
      Lp F 2 (volume : Measure (EuclideanSpace ℝ d)) :=
  Lp.fourierTransformₗᵢ (EuclideanSpace ℝ d) F

end Feec.Fourier.Euclidean
