module

public import Feec.Ch4.Whole

/-!
# Chapter 6 on the whole space `ℝ³`: the BGG weak-symmetry system propagates TSD

The Ch. 6 method of the thesis ([QuennevilleBelair2015, §6.1, §6.3]) is the Hodge wave equation
of the BGG complex (5.1), with the symmetry of `E` imposed weakly through the multiplier `M`. On
every bounded domain with the thesis' boundary conditions it does not propagate the TSD
constraint (`Feec.Ch6.Bounded.bggComplex_verdict`). This file builds the same system on the
whole space `ℝ³`, with no boundary, and proves that there it does: TSD data stay TSD, `M` stays
`0`, and `B` stays symmetric. Together the two files locate the failure at the boundary.

## Model

As in `Feec.Ch4.Whole`: fields are modelled by their Fourier transforms (Plancherel,
`Feec.Whole.fieldFourierW`), `∂_c ↦ 2πi ξ_c`, so every operator is a multiplication operator
(`Feec.Whole.mulOp`, closed and densely defined, with the fibrewise adjoint as adjoint). The
complex (5.1) of the §6.3 application, with `S₀ = I` and `S₁ = 2 vskw` (`skwSym`, the same
normalization as `Feec.Ch6.Bounded.skwL`), is `bggWhole`:
`L²(ℝ³) ⊇ H²(ℝ³) --grad grad--> H(curl; M) --(S₁, curl)--> L²(ℝ³; V) × L²(ℝ³; M)`,
with symbols `hessSym ζ z = -z ζ ζᵀ` and `bggSym ζ M = (S₁ M, i (ζ × M_a)_a)` at `ζ = 2πξ`.
The target `L²(V) × L²(M)` is modelled as `L²(ℝ³_ξ; ℂ³ × ℂ³ˣ³)` (`L2W`, fibre `VM`).
`{0} × L²(TSD)` is the fibrewise subspace with fibre `{0} × tsd ζ` (`L2TSDB`, `mem_L2TSDB_iff`).
Scalar fields are complex-valued on the Fourier side; real fields are a special case.

## Main results

* `bggWhole` (closed, densely defined, `(S₁, curl) grad grad = 0`: Hessian symbols are symmetric
  and curl-free).
* The hypotheses of `Feec.Constraints.prop_4_17` for `S1 = L²(TSD)`, `S2 = {0} × L²(TSD)`:
  `L2TSD_le_ker_bgg` (`(grad grad)*` vanishes on TSD fibres, which are orthogonal to
  `ζ ζᵀ`), `bggW_mem_L2TSDB` (`S₁` kills symmetric fields; Lemma 3.5 for the curl),
  `adjoint_bggW_mem_L2TSD` (`(S₁, curl)* (0, B) = curl B`), and the projection hypothesis
  `projKc_mem_domL_bgg` (fibrewise: `P_ζ` commutes with the curl symbol, `S₁ P_ζ = 0`).
* **`prop_4_17_bggWhole`**: every strong solution from TSD data stays in
  `K = {0} × L²(TSD) × ({0} × L²(TSD))` and solves (4.15).
* **`bggWhole_verdict`**: for `E₀, B₀ ∈ L²(TSD) ∩ H(curl)`, existence (Stone's theorem) and
  uniqueness of a classical solution from `(0, E₀, (0, B₀))`, with `σ ≡ 0`, `u(t) ∈ L²(TSD)`,
  `(M, B)(t) = (0, B(t))`, `B(t) ∈ L²(TSD)`.

## Why the bounded-domain counterexample has no analogue here

The bounded-domain refutation pairs `E ∈ H̊(curl, M)` with the linear fields `x_a e_b`
(`Feec.Ch6.Bounded.inner_curl_skewLin`) and uses the datum `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`; neither
is square-integrable on `ℝ³`. On `ℝ³` the fibre algebra is the same as on the torus
(`Feec.Torus.proj_curlSym`), and nothing breaks.

## Thesis gap

[QuennevilleBelair2015, §6.1, §6.3] states no propagation result for the Ch. 6 system. On `ℝ³`
the natural statement (Prop 4.17 with the weak-symmetry complex) holds, by the argument of
Prop 4.17; on bounded domains with the thesis' boundary conditions it fails
(`Feec.Ch6.Bounded`).

Not formalized: the multiplier form (6.2); the identification of the Fourier multipliers with
weak derivatives beyond what `Feec.Ch4.Whole` provides; the semi-discrete method (6.5).

## References

* [QuennevilleBelair2015], Ch. 5 (§5.1, the complex (5.1)), Ch. 6 (§6.1 (6.1), §6.3, Table 6.1),
  §3.4 (Lemma 3.5), §4.10 (Props 4.16–4.18)
* [ArnoldHu2021] (the BGG construction), [AFW2007] (weakly imposed symmetry)
* [AFW2010], [BruningLesch1992] (Hilbert complexes)
* [Pazy1983], §1.10 (Stone's theorem)
* Mathlib, `Mathlib.Analysis.Fourier.LpSpace` (the `L²` Fourier transform, Plancherel)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology LinearPMap
open MeasureTheory Set Filter

namespace Feec.Ch6.Whole

open Feec.Torus hiding L2M L2V L2TSD Hcurl
open Feec.Whole Feec.HilbertComplex2 Feec.Constraints

/-! ## §1. Symbols -/

section Symbols

/-- The fibre `ℂ³ × ℂ³ˣ³` of `L²(ℝ³; V) × L²(ℝ³; M)` (the target of `(S₁, curl)`), with the
`ℓ²` product inner product. -/
abbrev VM := WithLp 2 (Vec3 × Mat3)

/-- The scalar gradient symbol `z ↦ i z ζ`. -/
def gradS (ζ : Freq) : ℂ →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => vec fun a => Complex.I * z * ζ a
      map_add' := fun z w => by ext a; simp; ring
      map_smul' := fun r z => by ext a; simp [Complex.real_smul]; ring }

theorem gradS_apply (ζ : Freq) (z : ℂ) (a : Fin 3) : gradS ζ z a = Complex.I * z * ζ a := rfl

/-- The Hessian symbol `z ↦ -z ζ ζᵀ` (`grad grad` on the Fourier side). -/
def hessSym (ζ : Freq) : ℂ →L[ℝ] Mat3 := gradSym ζ ∘L gradS ζ

theorem hessSym_eq (ζ : Freq) (z : ℂ) : hessSym ζ z = gradSym ζ (gradS ζ z) := rfl

theorem hessSym_apply (ζ : Freq) (z : ℂ) (a b : Fin 3) :
    hessSym ζ z (a, b) = -(z * ζ a * ζ b) := by
  rw [hessSym_eq, gradSym_apply, gradS_apply]
  linear_combination (z * (ζ a : ℂ) * ζ b) * Complex.I_mul_I

/-- The BGG map `S₁ = 2 vskw` on the fibre: `(S₁ M)_i = M_{i+1,i+2} - M_{i+2,i+1}`. -/
def skwSym : Mat3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => vec fun i => M (i + 1, i + 2) - M (i + 2, i + 1)
      map_add' := fun M N => by ext i; simp; ring
      map_smul' := fun r M => by ext i; simp [Complex.real_smul]; ring }

theorem skwSym_apply (M : Mat3) (i : Fin 3) : skwSym M i = M (i + 1, i + 2) - M (i + 2, i + 1) :=
  rfl

theorem skwSym_eq_zero_of_symm {M : Mat3} (hM : ∀ a b, M (a, b) = M (b, a)) : skwSym M = 0 := by
  ext i; rw [skwSym_apply, hM]; simp

theorem skwSym_hessSym (ζ : Freq) (z : ℂ) : skwSym (hessSym ζ z) = 0 :=
  skwSym_eq_zero_of_symm fun a b => by rw [hessSym_apply, hessSym_apply]; ring

theorem curlSym_hessSym (ζ : Freq) (z : ℂ) : curlSym ζ (hessSym ζ z) = 0 := curlSym_gradSym _ _

/-- The embedding `v ↦ (v, 0)`. -/
def inlV : Vec3 →L[ℝ] VM :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Vec3 Mat3).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℝ Vec3 Mat3

/-- The embedding `M ↦ (0, M)`. -/
def inrM : Mat3 →L[ℝ] VM :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Vec3 Mat3).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℝ Vec3 Mat3

/-- The projection `(v, M) ↦ v`. -/
def fstV : VM →L[ℝ] Vec3 :=
  ContinuousLinearMap.fst ℝ Vec3 Mat3 ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ Vec3 Mat3).toContinuousLinearMap

/-- The projection `(v, M) ↦ M`. -/
def sndM : VM →L[ℝ] Mat3 :=
  ContinuousLinearMap.snd ℝ Vec3 Mat3 ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ Vec3 Mat3).toContinuousLinearMap

theorem inrM_apply (M : Mat3) : inrM M = WithLp.toLp 2 (0, M) := rfl
theorem fstV_apply (w : VM) : fstV w = (WithLp.ofLp w).1 := rfl
theorem sndM_apply (w : VM) : sndM w = (WithLp.ofLp w).2 := rfl

/-- The symbol of `d1 = (S₁, curl)`: `M ↦ (S₁ M, curl_ζ M)`. -/
def bggSym (ζ : Freq) : Mat3 →L[ℝ] VM := inlV ∘L skwSym + inrM ∘L curlSym ζ

theorem bggSym_apply (ζ : Freq) (M : Mat3) :
    bggSym ζ M = WithLp.toLp 2 (skwSym M, curlSym ζ M) := by
  simp only [bggSym, inlV, inrM, _root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [← _root_.map_add, Prod.mk_add_mk, add_zero, zero_add]
  rfl

theorem bggSym_hessSym (ζ : Freq) (z : ℂ) : bggSym ζ (hessSym ζ z) = 0 := by
  rw [bggSym_apply, skwSym_hessSym, curlSym_hessSym]; rfl

theorem norm_sq_VM (w : VM) : ‖w‖ ^ 2 = ‖(WithLp.ofLp w).1‖ ^ 2 + ‖(WithLp.ofLp w).2‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, WithLp.prod_inner_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

theorem norm_snd_le (w : VM) : ‖(WithLp.ofLp w).2‖ ≤ ‖w‖ := by
  have h := norm_sq_VM w
  have := sq_nonneg ‖(WithLp.ofLp w).1‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- The adjoint symbol: `(S₁, curl)* (v, B) = S₁* v + curl B`. -/
theorem adjoint_bggSym_apply (ζ : Freq) (w : VM) :
    ContinuousLinearMap.adjoint (bggSym ζ) w =
      ContinuousLinearMap.adjoint skwSym (WithLp.ofLp w).1 + curlSym ζ (WithLp.ofLp w).2 := by
  refine ext_inner_right ℝ fun M => ?_
  have hc := ContinuousLinearMap.adjoint_inner_left (curlSym ζ) M (WithLp.ofLp w).2
  rw [adjoint_curlSym] at hc
  rw [ContinuousLinearMap.adjoint_inner_left, bggSym_apply, WithLp.prod_inner_apply,
    inner_add_left, ContinuousLinearMap.adjoint_inner_left, hc, WithLp.ofLp_toLp]

/-- On TSD fibres the Hessian symbol is orthogonal: `(grad grad)* M = 0` for `M ∈ tsd ζ`. -/
theorem adjoint_hessSym_of_mem_tsd {ζ : Freq} {M : Mat3} (hM : M ∈ tsd ζ) :
    ContinuousLinearMap.adjoint (hessSym ζ) M = 0 := by
  refine ext_inner_right ℝ fun z => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, hessSym_eq, gradSym_eq_outer,
    real_inner_comm]
  exact inner_outer_tsd hM _

theorem continuous_gradS : Continuous gradS := by
  refine continuous_clm_apply.2 fun z => continuous_of_linear (fun ξ η => ?_) (fun r ξ => ?_)
  · ext a; simp [gradS_apply]; ring
  · ext a; simp [gradS_apply, Complex.real_smul]; ring

theorem stronglyMeasurable_hessW : StronglyMeasurable fun ξ => hessSym (freqW ξ) :=
  ((continuous_gradSym.clm_comp continuous_gradS).comp continuous_freqW).stronglyMeasurable

theorem stronglyMeasurable_bggW : StronglyMeasurable fun ξ => bggSym (freqW ξ) :=
  (continuous_const.add (continuous_const.clm_comp
    (continuous_curlSym.comp continuous_freqW))).stronglyMeasurable

/-- The fibre `{0} × tsd ζ` of `{0} × L²(TSD)`. -/
def tsdB (ζ : Freq) : Submodule ℝ VM :=
  ((⊥ : Submodule ℝ Vec3).prod (tsd ζ)).comap (WithLp.linearEquiv 2 ℝ (Vec3 × Mat3)).toLinearMap

theorem mem_tsdB {ζ : Freq} {w : VM} :
    w ∈ tsdB ζ ↔ (WithLp.ofLp w).1 = 0 ∧ (WithLp.ofLp w).2 ∈ tsd ζ := by
  simp [tsdB, Submodule.mem_prod]

/-- The projection onto `{0} × tsd ζ` is `(v, M) ↦ (0, P_ζ M)`. -/
theorem starProjection_tsdB (ζ : Freq) (w : VM) :
    (tsdB ζ).starProjection w = inrM ((tsd ζ).starProjection (WithLp.ofLp w).2) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact mem_tsdB.2 ⟨rfl, Submodule.starProjection_apply_mem _ _⟩
  intro v hv
  obtain ⟨h1, h2⟩ := mem_tsdB.1 hv
  rw [WithLp.prod_inner_apply, inrM_apply, WithLp.ofLp_sub, WithLp.ofLp_toLp, Prod.fst_sub,
    Prod.snd_sub, h1, inner_zero_right, zero_add]
  exact (tsd ζ).starProjection_inner_eq_zero _ _ h2

theorem stronglyMeasurable_projTSDB :
    StronglyMeasurable fun ξ => (tsdB (freqW ξ)).starProjection := by
  have e : (fun ξ => (tsdB (freqW ξ)).starProjection) =
      fun ξ => inrM ∘L (tsd (freqW ξ)).starProjection ∘L sndM := by
    funext ξ; ext1 w; rw [starProjection_tsdB]; rfl
  rw [e]
  exact (continuous_const.clm_comp (continuous_id.clm_comp continuous_const)).comp_stronglyMeasurable
    stronglyMeasurable_projTSD

end Symbols

/-! ## §2. The complex (5.1) on `ℝ³` -/

section Complex

/-- Fourier transforms of scalar fields on `ℝ³`: `L²(ℝ³_ξ; ℂ)` (real Hilbert space). -/
abbrev L2S := Lp ℂ 2 (volume : Measure Freq)
/-- Fourier transforms of pairs `(M, B)` of a vector and a matrix field: `L²(ℝ³_ξ; ℂ³ × ℂ³ˣ³)`. -/
abbrev L2W := Lp VM 2 (volume : Measure Freq)

/-- `grad grad : H²(ℝ³) → L²(ℝ³; M)` on the Fourier side, `σ̂ ↦ -σ̂ (2πξ)(2πξ)ᵀ`. -/
def hessW : L2S →ₗ.[ℝ] L2M := mulOp volume fun ξ => hessSym (freqW ξ)

/-- `d1 = (S₁, curl) : H(curl; M) → L²(V) × L²(M)` on the Fourier side. -/
def bggW : L2M →ₗ.[ℝ] L2W := mulOp volume fun ξ => bggSym (freqW ξ)

theorem coeFn_hessW (u : hessW.domain) :
    hessW u =ᵐ[volume] fun ξ => hessSym (freqW ξ) ((u : L2S) ξ) := coeFn_mulOp _ _ u

theorem coeFn_bggW (u : bggW.domain) :
    bggW u =ᵐ[volume] fun ξ => bggSym (freqW ξ) ((u : L2M) ξ) := coeFn_mulOp _ _ u

theorem mem_adjoint_hessW_domain {A : L2M} : A ∈ hessW†.domain ↔
    MemLp (fun ξ => ContinuousLinearMap.adjoint (hessSym (freqW ξ)) (A ξ)) 2 volume :=
  mem_adjoint_mulOp_domain stronglyMeasurable_hessW

theorem coeFn_adjoint_hessW (A : hessW†.domain) : hessW† A =ᵐ[volume]
    fun ξ => ContinuousLinearMap.adjoint (hessSym (freqW ξ)) ((A : L2M) ξ) :=
  coeFn_adjoint_mulOp stronglyMeasurable_hessW A

theorem mem_adjoint_bggW_domain {ρ : L2W} : ρ ∈ bggW†.domain ↔
    MemLp (fun ξ => ContinuousLinearMap.adjoint (bggSym (freqW ξ)) (ρ ξ)) 2 volume :=
  mem_adjoint_mulOp_domain stronglyMeasurable_bggW

theorem coeFn_adjoint_bggW (ρ : bggW†.domain) : bggW† ρ =ᵐ[volume]
    fun ξ => ContinuousLinearMap.adjoint (bggSym (freqW ξ)) ((ρ : L2W) ξ) :=
  coeFn_adjoint_mulOp stronglyMeasurable_bggW ρ

/-- **The BGG complex (5.1) of the §6.3 application on `ℝ³`**,
`H²(ℝ³) --grad grad--> H(curl; M) --(S₁, curl)--> L²(ℝ³; V) × L²(ℝ³; M)`, on the Fourier side:
closed and densely defined (generic multiplier theory, `Feec.Ch4.WholeMul`), and
`(S₁, curl) grad grad = 0` (Hessians are symmetric and curl-free). -/
def bggWhole : HilbertComplex2 L2S L2M L2W where
  d0 := hessW
  d1 := bggW
  dense0 := dense_mulDomain stronglyMeasurable_hessW
  dense1 := dense_mulDomain stronglyMeasurable_bggW
  closed0 := isClosed_mulOp stronglyMeasurable_hessW
  closed1 := isClosed_mulOp stronglyMeasurable_bggW
  map_mem x := by
    change MemLp _ 2 volume
    refine (MemLp.zero (ε := VM)).ae_eq ?_
    filter_upwards [coeFn_hessW x] with ξ h
    change (0 : VM) = bggSym (freqW ξ) ((hessW x : L2M) ξ)
    rw [h, bggSym_hessSym]
  comp_zero x := by
    refine Lp.ext ?_
    filter_upwards [coeFn_bggW ⟨hessW x, _⟩, coeFn_hessW x,
      Lp.coeFn_zero VM 2 (volume : Measure Freq)] with ξ h1 h2 h3
    rw [h1, h3]
    change bggSym (freqW ξ) ((hessW x : L2M) ξ) = 0
    rw [h2, bggSym_hessSym]

/-- `{0} × L²(TSD) ⊆ L²(V) × L²(M)`: vanishing multiplier `M`, TSD magnetic field. -/
abbrev L2TSDB : Submodule ℝ L2W := fibreSub volume fun ξ => tsdB (freqW ξ)

instance : L2TSDB.HasOrthogonalProjection :=
  hasOrthogonalProjection_fibreSub _ stronglyMeasurable_projTSDB.aestronglyMeasurable

theorem coeFn_projTSDB (ρ : L2W) :
    L2TSDB.starProjection ρ =ᵐ[volume] fun ξ => (tsdB (freqW ξ)).starProjection (ρ ξ) :=
  coeFn_starProjection_fibreSub _ stronglyMeasurable_projTSDB.aestronglyMeasurable ρ

/-- `L²(TSD) ⊆ ker (grad grad)*` on `ℝ³` (`hS1` of `prop_4_17`). -/
theorem L2TSD_le_ker_bgg : L2TSD ≤ bggWhole.d0†.ker := by
  intro A hA
  change A ∈ hessW†.ker
  have hz : (fun ξ => ContinuousLinearMap.adjoint (hessSym (freqW ξ)) (A ξ)) =ᵐ[volume] 0 := by
    filter_upwards [hA] with ξ h
    exact adjoint_hessSym_of_mem_tsd h
  have hdom : A ∈ hessW†.domain :=
    mem_adjoint_hessW_domain.2 ((MemLp.zero (ε := ℂ)).ae_eq hz.symm)
  refine LinearPMap.mem_ker_iff.2 ⟨⟨A, hdom⟩, rfl, ?_⟩
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [coeFn_adjoint_hessW ⟨A, hdom⟩, hz] with ξ h1 h2
  rw [h1]; exact h2

/-- `d1 = (S₁, curl)` maps `H(curl) ∩ L²(TSD)` into `{0} × L²(TSD)` (`hd1` of `prop_4_17`):
`S₁` vanishes on symmetric fields and the curl preserves TSD (Lemma 3.5). -/
theorem bggW_mem_L2TSDB (u : bggWhole.d1.domain) (hu : (u : L2M) ∈ L2TSD) :
    bggWhole.d1 u ∈ L2TSDB := by
  change bggW u ∈ L2TSDB
  refine mem_fibreSub.2 ?_
  filter_upwards [coeFn_bggW u, hu] with ξ h1 h2
  rw [h1, bggSym_apply, mem_tsdB, WithLp.ofLp_toLp]
  exact ⟨skwSym_eq_zero_of_symm h2.1, curlSym_mem_tsd h2⟩

/-- `d1* (0, B) = curl B` maps `{0} × L²(TSD)` into `L²(TSD)` (`hd1s` of `prop_4_17`). -/
theorem adjoint_bggW_mem_L2TSD (ρ : bggWhole.d1†.domain) (hρ : (ρ : L2W) ∈ L2TSDB) :
    bggWhole.d1† ρ ∈ L2TSD := by
  refine mem_fibreSub.2 ?_
  filter_upwards [coeFn_adjoint_bggW ρ, hρ] with ξ h1 h2
  obtain ⟨h21, h22⟩ := mem_tsdB.1 h2
  rw [show ((bggWhole.d1† ρ : L2M) : Freq → Mat3) ξ = _ from h1, adjoint_bggSym_apply, h21,
    _root_.map_zero, zero_add]
  exact curlSym_mem_tsd h22

theorem norm_toLp_zero (c : Mat3) : ‖(WithLp.toLp 2 ((0 : Vec3), c) : VM)‖ = ‖c‖ := by
  have := norm_sq_VM (WithLp.toLp 2 ((0 : Vec3), c))
  rw [WithLp.ofLp_toLp, norm_zero] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [this]; ring)

/-- `(S₁, curl)` is controlled by the curl on TSD fibres after projection:
`‖(S₁, curl)(P_ζ M)‖ ≤ ‖(S₁, curl) M‖`. -/
theorem norm_bggSym_proj_le (ζ : Freq) (M : Mat3) :
    ‖bggSym ζ ((tsd ζ).starProjection M)‖ ≤ ‖bggSym ζ M‖ := by
  have hP := Submodule.starProjection_apply_mem (tsd ζ) M
  rw [bggSym_apply, skwSym_eq_zero_of_symm hP.1, norm_toLp_zero, ← proj_curlSym]
  refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
  calc ‖curlSym ζ M‖ = ‖(WithLp.ofLp (bggSym ζ M)).2‖ := by rw [bggSym_apply, WithLp.ofLp_toLp]
    _ ≤ _ := norm_snd_le _

/-- `‖(S₁, curl)* (0, P_ζ B)‖ = ‖P_ζ curl B‖ ≤ ‖(S₁, curl)* (v, B) - S₁* v‖`. -/
theorem norm_adjoint_bggSym_proj_le (ζ : Freq) (w : VM) :
    ‖ContinuousLinearMap.adjoint (bggSym ζ) ((tsdB ζ).starProjection w)‖ ≤
      ‖ContinuousLinearMap.adjoint (bggSym ζ) w - (ContinuousLinearMap.adjoint skwSym ∘L fstV) w‖ := by
  rw [starProjection_tsdB, inrM_apply, adjoint_bggSym_apply, adjoint_bggSym_apply,
    WithLp.ofLp_toLp, ContinuousLinearMap.comp_apply, fstV_apply]
  simp only [_root_.map_zero, zero_add, add_sub_cancel_left]
  rw [← proj_curlSym]
  exact Submodule.norm_starProjection_apply_le _ _

/-- **The projection hypothesis holds for the Ch. 6 complex on `ℝ³`** (`hPD` of `prop_4_17`):
`P_K D(L) ⊆ D(L)` for `K = {0} × L²(TSD) × ({0} × L²(TSD))`. -/
theorem projKc_mem_domL_bgg : ∀ x ∈ bggWhole.domL,
    projKc L2S L2TSD L2TSDB x ∈ bggWhole.domL := by
  intro x hx
  rw [Constraints.mem_domL] at hx ⊢
  rw [tot_projKc]
  obtain ⟨-, hu, hρ⟩ := hx
  refine ⟨bggWhole.d0.domain.zero_mem, ⟨?_, ?_⟩, ?_⟩
  · -- `P_TSD u ∈ D((S₁, curl))`
    have hu1 : (tot L2S L2M L2W x).2.1 ∈ bggW.domain := (Submodule.mem_inf.1 hu).1
    refine MemLp.of_le hu1 (aestronglyMeasurable_apply
      stronglyMeasurable_bggW.aestronglyMeasurable (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [coeFn_projTSD (tot L2S L2M L2W x).2.1] with ξ h
    rw [h]
    exact norm_bggSym_proj_le _ _
  · exact (LinearPMap.mem_ker_iff.1 (L2TSD_le_ker_bgg (L2TSD.starProjection_apply_mem _))).elim
      fun y hy => hy.1 ▸ y.2
  · -- `P_{TSDB} ρ ∈ D((S₁, curl)*)`
    show L2TSDB.starProjection (tot L2S L2M L2W x).2.2 ∈ bggW†.domain
    have hρ' := mem_adjoint_bggW_domain.1 (hρ : (tot L2S L2M L2W x).2.2 ∈ bggW†.domain)
    refine mem_adjoint_bggW_domain.2 ?_
    have hs : MemLp (fun ξ => (ContinuousLinearMap.adjoint skwSym ∘L fstV)
        ((tot L2S L2M L2W x).2.2 ξ)) 2 volume :=
      memLp_apply (B := fun _ => ContinuousLinearMap.adjoint skwSym ∘L fstV)
        aestronglyMeasurable_const (fun _ => le_rfl) _
    refine MemLp.of_le (hρ'.sub hs) (aestronglyMeasurable_apply
      (aestronglyMeasurable_adjoint stronglyMeasurable_bggW.aestronglyMeasurable)
      (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [coeFn_projTSDB (tot L2S L2M L2W x).2.2] with ξ h
    rw [h]
    exact norm_adjoint_bggSym_proj_le _ _

end Complex

/-! ## §3. Prop 4.17 for the Ch. 6 system on `ℝ³` -/

section Prop417

/-- The embedding `B ↦ (0, B)`, `L²(ℝ³; M) → L²(ℝ³; V) × L²(ℝ³; M)`. -/
def embB : L2M →L[ℝ] L2W :=
  bmul volume (fun _ => inrM) aestronglyMeasurable_const ‖inrM‖ fun _ => le_rfl

theorem coeFn_embB (B : L2M) : embB B =ᵐ[volume] fun ξ => inrM (B ξ) :=
  coeFn_bmul _ _ _ _ B

/-- The projection `(M, B) ↦ B`. -/
def projB : L2W →L[ℝ] L2M :=
  bmul volume (fun _ => sndM) aestronglyMeasurable_const ‖sndM‖ fun _ => le_rfl

theorem coeFn_projB (ρ : L2W) : projB ρ =ᵐ[volume] fun ξ => sndM (ρ ξ) :=
  coeFn_bmul _ _ _ _ ρ

/-- **`{0} × L²(TSD)` is what it says**: `ρ ∈ L2TSDB` iff `ρ = (0, B)` with `B ∈ L²(TSD)`. -/
theorem mem_L2TSDB_iff {ρ : L2W} : ρ ∈ L2TSDB ↔ ∃ B ∈ L2TSD, ρ = embB B := by
  constructor
  · intro hρ
    refine ⟨projB ρ, ?_, ?_⟩
    · refine mem_fibreSub.2 ?_
      filter_upwards [coeFn_projB ρ, hρ] with ξ h1 h2
      rw [h1, sndM_apply]; exact (mem_tsdB.1 h2).2
    · refine Lp.ext ?_
      filter_upwards [coeFn_embB (projB ρ), coeFn_projB ρ, hρ] with ξ h1 h2 h3
      rw [h1, h2, inrM_apply, sndM_apply, ← (mem_tsdB.1 h3).1]
  · rintro ⟨B, hB, rfl⟩
    refine mem_fibreSub.2 ?_
    filter_upwards [coeFn_embB B, hB] with ξ h1 h2
    rw [h1, inrM_apply, mem_tsdB, WithLp.ofLp_toLp]
    exact ⟨rfl, h2⟩

/-- `D(L)` for TSD data: `(0, E₀, (0, B₀)) ∈ D(L)` when `E₀, B₀ ∈ H(curl)` and `E₀ ∈ L²(TSD)`. -/
theorem ini_mem_domL_bgg {E₀ B₀ : L2M} (hE₀ : E₀ ∈ L2TSD) (hE₀c : E₀ ∈ Hcurl)
    (hB₀c : B₀ ∈ Hcurl) : ini L2S E₀ (embB B₀) ∈ bggWhole.domL := by
  rw [Constraints.mem_domL, tot_ini]
  refine ⟨bggWhole.d0.domain.zero_mem, ⟨?_, ?_⟩, ?_⟩
  · change MemLp _ 2 volume
    refine MemLp.of_le (hE₀c : MemLp (fun ξ => curlSym (freqW ξ) (E₀ ξ)) 2 volume)
      (aestronglyMeasurable_apply stronglyMeasurable_bggW.aestronglyMeasurable
        (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [hE₀] with ξ h
    rw [bggSym_apply, skwSym_eq_zero_of_symm h.1, norm_toLp_zero]
  · exact (LinearPMap.mem_ker_iff.1 (L2TSD_le_ker_bgg hE₀)).elim fun y hy => hy.1 ▸ y.2
  · refine mem_adjoint_bggW_domain.2 ((hB₀c : MemLp (fun ξ => curlSym (freqW ξ) (B₀ ξ)) 2
      volume).ae_eq ?_)
    filter_upwards [coeFn_embB B₀] with ξ h
    rw [h, inrM_apply, adjoint_bggSym_apply, WithLp.ofLp_toLp, _root_.map_zero, zero_add]

/-- **Prop 4.17 for the Ch. 6 BGG system on `ℝ³`** (every strong solution): for TSD data
`(σ, u, (M, B))(0) = (0, E₀, ρ₀)`, `E₀ ∈ L²(TSD)`, `ρ₀ ∈ {0} × L²(TSD)`, every strong solution
of the Hodge wave equation of (5.1) stays in `K = {0} × L²(TSD) × ({0} × L²(TSD))`, and
`(u, (M, B))` solves the reduced system (4.15). -/
theorem prop_4_17_bggWhole {T : ℝ} {E₀ : L2M} {ρ₀ : L2W} {U : ℝ → Tot L2S L2M L2W}
    (hE₀ : E₀ ∈ L2TSD) (hρ₀ : ρ₀ ∈ L2TSDB)
    (hU : IsStrongSolution (-bggWhole.waveOp) T (ini L2S E₀ ρ₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc L2S L2TSD L2TSDB) ∧
      IsReducedSolution bggWhole T E₀ ρ₀ (fun t => (tot L2S L2M L2W (U t)).2.1)
        (fun t => (tot L2S L2M L2W (U t)).2.2) := by
  have h1 := L2TSD_le_ker_bgg
  have h2 := projKc_mem_domL_bgg
  have h3 := bggW_mem_L2TSDB
  have h4 := adjoint_bggW_mem_L2TSD
  exact prop_4_17 h1 h2 h3 h4 hE₀ hρ₀ hU

/-- **Verdict for Ch. 6 on `ℝ³`: TSD propagates.** For `E₀, B₀ ∈ L²(TSD) ∩ H(curl)` and every
`T`, the Hodge wave equation of the BGG complex (5.1) on `ℝ³` has a solution in
`C⁰([0, T]; D(L)) ∩ C¹([0, T]; X)` from `(σ, u, (M, B))(0) = (0, E₀, (0, B₀))` (Stone's
theorem), unique among strong solutions, and for all `t ∈ [0, T]`: `σ(t) = 0`,
`u(t) ∈ L²(TSD)` (symmetric, trace-free, divergence-free: the weakly imposed symmetry of `E`
holds strongly), and `(M, B)(t) = (0, B(t))` with `B(t) ∈ L²(TSD)` (in particular `B` stays
symmetric); `(u, (M, B))` solves (4.15).

Contrast with `Feec.Ch6.Bounded.bggComplex_verdict`: on every bounded domain with the thesis'
boundary conditions, `u` leaves `L²(TSD)` and `B` loses symmetry. The mechanism is the same as
for Prop 4.17 (`Feec.Whole.prop_4_17_whole`): `P_TSD` commutes fibrewise with the curl symbol,
and here also `S₁ P_TSD = 0`; the boundary is what breaks it. -/
theorem bggWhole_verdict (T : ℝ) {E₀ B₀ : L2M} (hE₀ : E₀ ∈ L2TSD) (hB₀ : B₀ ∈ L2TSD)
    (hE₀c : E₀ ∈ Hcurl) (hB₀c : B₀ ∈ Hcurl) :
    ∃ U, IsClassicalSolution (-bggWhole.waveOp) T (ini L2S E₀ (embB B₀)) 0 U ∧
      (∀ U', IsStrongSolution (-bggWhole.waveOp) T (ini L2S E₀ (embB B₀)) 0 U' →
        EqOn U' U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (tot L2S L2M L2W (U t)).1 = 0 ∧ (tot L2S L2M L2W (U t)).2.1 ∈ L2TSD ∧
        ∃ B ∈ L2TSD, (tot L2S L2M L2W (U t)).2.2 = embB B) ∧
      IsReducedSolution bggWhole T E₀ (embB B₀) (fun t => (tot L2S L2M L2W (U t)).2.1)
        (fun t => (tot L2S L2M L2W (U t)).2.2) := by
  have h1 := L2TSD_le_ker_bgg
  have h2 := projKc_mem_domL_bgg
  have h3 := bggW_mem_L2TSDB
  have h4 := adjoint_bggW_mem_L2TSD
  have hρ₀ : embB B₀ ∈ L2TSDB := mem_L2TSDB_iff.2 ⟨B₀, hB₀, rfl⟩
  obtain ⟨U, hU, hK, hR, huniq⟩ := prop_4_17_exists_unconditional h1 h2 h3 h4 T hE₀ hρ₀
    (ini_mem_domL_bgg hE₀ hE₀c hB₀c)
  refine ⟨U, hU, huniq, fun t ht => ?_, hR⟩
  have hk : U t ∈ Kc L2S L2TSD L2TSDB := hK t ht
  have hk' := (mem_Kc (W0 := L2S) (S1 := L2TSD) (S2 := L2TSDB)).1 hk
  exact ⟨hk'.1, hk'.2.1, mem_L2TSDB_iff.1 hk'.2.2⟩

end Prop417

end Feec.Ch6.Whole
