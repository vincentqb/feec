module

public import Feec.Fourier.Euclidean
public import Feec.Fourier.Reality
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Fourier multipliers on `ℝᵈ` are weak derivatives

The Fourier model of a constant-coefficient complex on `ℝᵈ` defines the Sobolev spaces as the
domains of multiplication operators (`Feec.Fourier.Euclidean.complex`). This file identifies
them with the weak-derivative spaces, tested against **all** Schwartz fields, in any dimension
and for any finite-dimensional fibres:

* `mem_graph_iff_weak`: for a continuous symbol `m` and any operator `D` on Schwartz fields with
  `𝓕 (D φ) = m* 𝓕 φ`, and `f, g ∈ L²`: `𝓕 f ∈ D(m)` with `m 𝓕 f = 𝓕 g` iff
  `⟪f, D φ⟫ = ⟪g, φ⟫` for every Schwartz `φ`. The converse direction tests against
  `φ = 𝓕⁻¹ (χ M₀)`, `χ ∈ C_c^∞`, and uses the fundamental lemma of the calculus of variations.
* `firstOrder A φ = Σ_k A_k ∂_k φ` (constant-coefficient first-order operators on Schwartz
  fields) and `fourier_firstOrder`: `𝓕 (Σ A_k ∂_k φ)(x) = Σ_k 2πi x_k A_k 𝓕 φ (x)`.
* `formalAdjoint S i j`, the formal adjoint `-i Σ_k m_k* ∂_k` of a first-order arrow of a family
  of fibre complexes, and **`Euclidean.mem_graph_d_iff_weak`**: for every family whose arrow
  `i → j` is linear in `ξ` (a first-order operator), the domain of `d i j` in the Fourier model
  is the weak domain, `d (𝓕 f) = 𝓕 g ⟺ ⟪f, d* φ⟫ = ⟪g, φ⟫` for all Schwartz `φ`.

## References

* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.1 (weak derivatives)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the spaces of Prop 4.17)
* Mathlib, `Mathlib.Analysis.Fourier.LpSpace` (Plancherel),
  `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`,
  `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate FourierTransform SchwartzMap ContDiff
open MeasureTheory Set Filter

namespace Feec.Fourier.Weak

variable {d : Type*} [Fintype d]
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [FiniteDimensional ℂ F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A continuous symbol applied to an `L²` field is locally integrable. -/
theorem locallyIntegrable_clm_apply {m : EuclideanSpace ℝ d → E →L[ℂ] F} (hm : Continuous m)
    (u : Lp E 2 (volume : Measure (EuclideanSpace ℝ d))) :
    LocallyIntegrable (fun x => m x (u x)) volume := by
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hm.continuousOn
  have hu : IntegrableOn u K volume :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  have : ProperSpace (E →L[ℂ] F) := FiniteDimensional.proper_rclike ℂ _
  have : SecondCountableTopology (E →L[ℂ] F) := secondCountable_of_proper
  refine Integrable.mono' (hu.norm.const_mul C)
    (Operator.aestronglyMeasurable_clm_apply hm.aestronglyMeasurable
      (Lp.aestronglyMeasurable u)).restrict ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
  exact ((m x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _))

/-- **Weak identification of Fourier multiplier domains on `ℝᵈ`.** If `D` acts on Schwartz
fields with `𝓕 (D φ) = m* 𝓕 φ`, then `𝓕 f ∈ D(m)` with `m 𝓕 f = 𝓕 g` iff `⟪f, D φ⟫ = ⟪g, φ⟫`
for every Schwartz field `φ`. -/
theorem mem_graph_iff_weak {m : EuclideanSpace ℝ d → E →L[ℂ] F} (hm : Continuous m)
    (D : 𝓢(EuclideanSpace ℝ d, F) → 𝓢(EuclideanSpace ℝ d, E))
    (hD : ∀ φ x, 𝓕 (D φ) x = ContinuousLinearMap.adjoint (m x) (𝓕 φ x))
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ d)))
    (g : Lp F 2 (volume : Measure (EuclideanSpace ℝ d))) :
    (∃ h : 𝓕 f ∈ Operator.mulDomain volume m, Operator.mulOp volume m ⟨𝓕 f, h⟩ = 𝓕 g) ↔
      ∀ φ : 𝓢(EuclideanSpace ℝ d, F), ⟪f, (D φ).toLp 2⟫_ℂ = ⟪g, φ.toLp 2⟫_ℂ := by
  set Fu := 𝓕 f
  set G := 𝓕 g
  have key : ∀ φ : 𝓢(EuclideanSpace ℝ d, F),
      ⟪f, (D φ).toLp 2⟫_ℂ = ∫ x, ⟪m x (Fu x), 𝓕 φ x⟫_ℂ := fun φ => by
    rw [← Lp.inner_fourier_eq, SchwartzMap.toLp_fourier_eq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(𝓕 (D φ)).coeFn_toLp 2 volume] with x h
    rw [h, hD, ContinuousLinearMap.adjoint_inner_right]
  have key' : ∀ φ : 𝓢(EuclideanSpace ℝ d, F),
      ⟪g, φ.toLp 2⟫_ℂ = ∫ x, ⟪G x, 𝓕 φ x⟫_ℂ := fun φ => by
    rw [← Lp.inner_fourier_eq, SchwartzMap.toLp_fourier_eq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(𝓕 φ).coeFn_toLp 2 volume] with x h
    rw [h]
  constructor
  · rintro ⟨h, hc⟩ φ
    rw [key, key']
    refine integral_congr_ae ?_
    filter_upwards [Operator.coeFn_mulOp volume m ⟨Fu, h⟩] with x h1
    rw [← hc, h1]
  · intro hw
    have hloc := locallyIntegrable_clm_apply hm Fu
    have hGloc : LocallyIntegrable (G : EuclideanSpace ℝ d → F) volume :=
      (Lp.memLp G).locallyIntegrable (by norm_num)
    have hae : (fun x => m x (Fu x)) =ᵐ[volume] (G : EuclideanSpace ℝ d → F) := by
      refine ae_eq_of_integral_contDiff_smul_eq hloc hGloc fun χ hχ hχs => ?_
      have hi1 := hloc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχs
      have hi2 := hGloc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχs
      refine ext_inner_left ℂ fun M₀ => ?_
      rw [← integral_inner hi1, ← integral_inner hi2]
      have hs : HasCompactSupport fun x => (χ x : ℂ) • M₀ :=
        (hχs.comp_left Complex.ofReal_zero).smul_right
      have hd : ContDiff ℝ ∞ fun x => (χ x : ℂ) • M₀ :=
        (Complex.ofRealCLM.contDiff.comp hχ).smul contDiff_const
      set ψ : 𝓢(EuclideanSpace ℝ d, F) := hs.toSchwartzMap hd
      have hψ : ∀ x, ψ x = (χ x : ℂ) • M₀ := fun x => rfl
      have h := hw (𝓕⁻ ψ)
      rw [key, key'] at h
      simp only [FourierTransform.fourier_fourierInv_eq, hψ] at h
      have h' := congrArg (starRingEnd ℂ) h
      rw [← integral_conj, ← integral_conj] at h'
      have e : ∀ (v : F) (x : EuclideanSpace ℝ d),
          (starRingEnd ℂ) ⟪v, (χ x : ℂ) • M₀⟫_ℂ = ⟪M₀, χ x • v⟫_ℂ := fun v x => by
        rw [inner_conj_symm, inner_smul_left, Complex.conj_ofReal,
          RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
        rfl
      simpa only [e] using h'
    have hmem : Fu ∈ Operator.mulDomain volume m := (Lp.memLp G).ae_eq hae.symm
    refine ⟨hmem, Lp.ext ?_⟩
    filter_upwards [Operator.coeFn_mulOp volume m ⟨Fu, hmem⟩, hae] with x h1 h2
    rw [h1, ← h2]

/-- **Weak identification of Fourier multiplier kernels**: `𝓕 f ∈ ker m` iff `⟪f, D φ⟫ = 0`
for every Schwartz `φ`, when `𝓕 (D φ) = m* 𝓕 φ`. -/
theorem mem_ker_iff_weak {m : EuclideanSpace ℝ d → E →L[ℂ] F} (hm : Continuous m)
    (D : 𝓢(EuclideanSpace ℝ d, F) → 𝓢(EuclideanSpace ℝ d, E))
    (hD : ∀ φ x, 𝓕 (D φ) x = ContinuousLinearMap.adjoint (m x) (𝓕 φ x))
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ d))) :
    𝓕 f ∈ (Operator.mulOp volume m).ker ↔
      ∀ φ : 𝓢(EuclideanSpace ℝ d, F), ⟪f, (D φ).toLp 2⟫_ℂ = 0 := by
  have h := mem_graph_iff_weak hm D hD f 0
  simp only [inner_zero_left] at h
  rw [← h, LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨y, hy, hy0⟩
    refine ⟨hy ▸ y.2, ?_⟩
    rw [show (𝓕 (0 : Lp F 2 (volume : Measure (EuclideanSpace ℝ d)))) = 0 from
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ d) F).map_zero, ← hy0]
    exact LinearPMap.apply_congr' _ _ _ hy
  · rintro ⟨h, hc⟩
    refine ⟨⟨_, h⟩, rfl, hc.trans ?_⟩
    exact (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ d) F).map_zero

/-! ### First-order operators on Schwartz fields -/

variable [DecidableEq d]

/-- The constant-coefficient first-order operator `Σ_k A_k ∂_k` on Schwartz fields. -/
def firstOrder (A : d → E →L[ℂ] F) (φ : 𝓢(EuclideanSpace ℝ d, E)) : 𝓢(EuclideanSpace ℝ d, F) :=
  ∑ k, SchwartzMap.postcompCLM (A k) (LineDeriv.lineDerivOp (EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ d) φ)

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [DecidableEq d] in
/-- The Fourier transform commutes with complex-linear post-composition. -/
theorem fourier_postcomp (L : E →L[ℂ] F) (ψ : 𝓢(EuclideanSpace ℝ d, E))
    (x : EuclideanSpace ℝ d) : 𝓕 (SchwartzMap.postcompCLM L ψ) x = L (𝓕 ψ x) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have : (SchwartzMap.postcompCLM L ψ : EuclideanSpace ℝ d → F) = fun y => L (ψ y) :=
    funext fun y => SchwartzMap.postcompCLM_apply L ψ y
  rw [this, Real.fourier_eq, Real.fourier_eq, ← L.integral_comp_comm]
  · congr 1; funext v; rw [Circle.smul_def, Circle.smul_def, map_smul]
  · exact (Real.fourierIntegral_convergent_iff x).2 ψ.integrable

/-! ### Pointwise linear maps -/

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [DecidableEq d] in
/-- **The `L²` Fourier transform commutes with pointwise complex-linear maps**:
`𝓕 (L ∘ f) = L ∘ 𝓕 f` (Schwartz fields, then density). -/
theorem fourier_compLp (L : E →L[ℂ] F) (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ d))) :
    𝓕 (L.compLp f) = L.compLp (𝓕 f) := by
  have hc1 : Continuous fun f : Lp E 2 (volume : Measure (EuclideanSpace ℝ d)) =>
      𝓕 (L.compLp f) :=
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ d) F).continuous.comp (L.compLpL 2 volume).continuous
  have hc2 : Continuous fun f : Lp E 2 (volume : Measure (EuclideanSpace ℝ d)) =>
      L.compLp (𝓕 f) :=
    (L.compLpL 2 volume).continuous.comp (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ d) E).continuous
  refine DenseRange.induction_on
    (SchwartzMap.denseRange_toLpCLM (F := E) (μ := (volume : Measure (EuclideanSpace ℝ d)))
      (p := 2) ENNReal.ofNat_ne_top) f (isClosed_eq hc1 hc2) ?_
  intro φ
  simp only [SchwartzMap.toLpCLM_apply]
  have h1 : L.compLp (φ.toLp 2 : Lp E 2 (volume : Measure (EuclideanSpace ℝ d))) =
      (SchwartzMap.postcompCLM L φ).toLp 2 := by
    refine Lp.ext ?_
    filter_upwards [L.coeFn_compLp (φ.toLp 2 : Lp E 2 (volume : Measure (EuclideanSpace ℝ d))),
      φ.coeFn_toLp 2 volume, (SchwartzMap.postcompCLM L φ).coeFn_toLp 2 volume] with x h1 h2 h3
    rw [h1, h2, h3, SchwartzMap.postcompCLM_apply]
  rw [h1, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  refine Lp.ext ?_
  filter_upwards [(𝓕 (SchwartzMap.postcompCLM L φ)).coeFn_toLp 2 volume,
    L.coeFn_compLp ((𝓕 φ).toLp 2 : Lp E 2 (volume : Measure (EuclideanSpace ℝ d))),
    (𝓕 φ).coeFn_toLp 2 volume] with x h1 h2 h3
  rw [h1, h2, h3, fourier_postcomp]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [DecidableEq d] in
/-- **Pointwise linear conditions transfer to the Fourier side**: `L (f x) = 0` a.e. iff
`L (𝓕 f ξ) = 0` a.e. (e.g. symmetry and trace of a matrix field). -/
theorem ae_map_eq_zero_iff_fourier (L : E →L[ℂ] F)
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ d))) :
    (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ d)), L (f x) = 0) ↔
      ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ d)), L (𝓕 f ξ) = 0 := by
  have e : ∀ g : Lp E 2 (volume : Measure (EuclideanSpace ℝ d)),
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ d)), L (g x) = 0) ↔ L.compLp g = 0 := fun g => by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h
      filter_upwards [h, L.coeFn_compLp g] with x h1 h2
      rw [h2, h1, Pi.zero_apply]
    · intro h
      filter_upwards [h, L.coeFn_compLp g] with x h1 h2
      rw [← h2, h1, Pi.zero_apply]
  rw [e, e, ← fourier_compLp]
  exact (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ d) F).map_eq_zero_iff.symm

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- **The symbol of a first-order operator**: `𝓕 (Σ A_k ∂_k φ)(x) = Σ_k 2πi x_k A_k 𝓕 φ (x)`. -/
theorem fourier_firstOrder (A : d → E →L[ℂ] F) (φ : 𝓢(EuclideanSpace ℝ d, E))
    (x : EuclideanSpace ℝ d) :
    𝓕 (firstOrder A φ) x = ∑ k, ((2 * Real.pi * x k : ℝ) * Complex.I) • A k (𝓕 φ x) := by
  have hT : ∀ k : d, (fun y : EuclideanSpace ℝ d =>
      inner ℝ y (EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ d)).HasTemperateGrowth :=
    fun k => ((innerSL ℝ).flip (EuclideanSpace.single k (1 : ℝ))).hasTemperateGrowth
  rw [firstOrder, ← SchwartzMap.fourierTransformCLM_apply ℂ, map_sum, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [SchwartzMap.fourierTransformCLM_apply, fourier_postcomp, SchwartzMap.fourier_lineDerivOp_eq,
    _root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (hT k),
    RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_smul, smul_smul]
  congr 1
  simp [EuclideanSpace.inner_single_right]
  ring


/-! ### Formal adjoints of first-order symbols -/

/-- The first-order operator `-i Σ_k m(e_k) ∂_k` on Schwartz fields, whose Fourier symbol is
`m(2πx)` when `m` is linear (`fourier_symbolOp`). -/
def symbolOp (m : EuclideanSpace ℝ d → E →L[ℂ] F) :
    𝓢(EuclideanSpace ℝ d, E) → 𝓢(EuclideanSpace ℝ d, F) :=
  firstOrder fun k => -Complex.I • m (EuclideanSpace.single k (1 : ℝ))

/-- The **formal adjoint** `-i Σ_k m(e_k)* ∂_k` of a first-order symbol. -/
def formalAdjointOp (m : EuclideanSpace ℝ d → E →L[ℂ] F) :
    𝓢(EuclideanSpace ℝ d, F) → 𝓢(EuclideanSpace ℝ d, E) :=
  firstOrder fun k => -Complex.I • ContinuousLinearMap.adjoint (m (EuclideanSpace.single k (1 : ℝ)))

/-- A symbol is **first order** (homogeneous of degree one, linear in the frequency). -/
def IsLinear (m : EuclideanSpace ℝ d → E →L[ℂ] F) : Prop :=
  ∀ ξ, m ξ = ∑ k, ((ξ k : ℝ) : ℂ) • m (EuclideanSpace.single k (1 : ℝ))

omit [Fintype d] [DecidableEq d] in
theorem scale_apply (x : EuclideanSpace ℝ d) (k : d) :
    Euclidean.scale x k = 2 * Real.pi * x k := by
  simp [Euclidean.scale]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- The Schwartz operator `-i Σ m(e_k) ∂_k` has Fourier symbol `m(2πx)`. -/
theorem fourier_symbolOp {m : EuclideanSpace ℝ d → E →L[ℂ] F} (hm : IsLinear m)
    (ψ : 𝓢(EuclideanSpace ℝ d, E)) (x : EuclideanSpace ℝ d) :
    𝓕 (symbolOp m ψ) x = m (Euclidean.scale x) (𝓕 ψ x) := by
  rw [symbolOp, fourier_firstOrder, hm (Euclidean.scale x), sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [_root_.smul_apply, _root_.smul_apply, smul_smul, scale_apply]
  congr 1
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-(2 * (Real.pi : ℂ) * (x k : ℂ))) * this

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- The formal adjoint has Fourier symbol `m(2πx)*`. -/
theorem fourier_formalAdjointOp {m : EuclideanSpace ℝ d → E →L[ℂ] F} (hm : IsLinear m)
    (φ : 𝓢(EuclideanSpace ℝ d, F)) (x : EuclideanSpace ℝ d) :
    𝓕 (formalAdjointOp m φ) x =
      ContinuousLinearMap.adjoint (m (Euclidean.scale x)) (𝓕 φ x) := by
  rw [formalAdjointOp, fourier_firstOrder, hm (Euclidean.scale x), map_sum,
    sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, _root_.smul_apply, _root_.smul_apply, smul_smul, scale_apply,
    Complex.conj_ofReal]
  congr 1
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-(2 * (Real.pi : ℂ) * (x k : ℂ))) * this

/-- **The Fourier model of a first-order constant-coefficient operator on `ℝᵈ` is its weak
realization**: `𝓕 f ∈ D(m)` with `m 𝓕 f = 𝓕 g` iff `⟪f, D* φ⟫ = ⟪g, φ⟫` for every Schwartz
field `φ`, with `D*` the formal adjoint. -/
theorem mem_graph_iff_weak_of_isLinear {m : EuclideanSpace ℝ d → E →L[ℂ] F} (hm : IsLinear m)
    (hc : Continuous m) (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ d)))
    (g : Lp F 2 (volume : Measure (EuclideanSpace ℝ d))) :
    (∃ h : 𝓕 f ∈ Operator.mulDomain volume (fun x => m (Euclidean.scale x)),
        Operator.mulOp volume (fun x => m (Euclidean.scale x)) ⟨𝓕 f, h⟩ = 𝓕 g) ↔
      ∀ φ : 𝓢(EuclideanSpace ℝ d, F),
        ⟪f, (formalAdjointOp m φ).toLp 2⟫_ℂ = ⟪g, φ.toLp 2⟫_ℂ :=
  mem_graph_iff_weak (hc.comp Euclidean.continuous_scale) (formalAdjointOp m)
    (fun φ x => fourier_formalAdjointOp hm φ x) f g

/-! ### Real fields and the Fourier transform -/

section Real

variable {ι : Type*} [Fintype ι]

end Real

end Feec.Fourier.Weak
