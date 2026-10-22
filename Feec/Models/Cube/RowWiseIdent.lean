module

public import Feec.Models.Cube.Parity
public import Feec.Models.BoundedDomain.GradCurl
public import Feec.Domain.Cutoff
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# The row-wise parity model is the bounded-domain complex on the cube

`Feec.Models.Cube.Parity` models the cube `Q = (0, ½)³` with the thesis' boundary conditions by the
fields of the real torus grad–curl complex with the row-wise parities (`rowAction`). This file
proves that it **is** the bounded-domain complex `H̊¹(Q; ℝ³) → H̊(curl, Q; ℝ³ˣ³) → L²(Q; ℝ³ˣ³)`
(`Feec.Models.BoundedDomain.gradCurl` on `Q`, the minimal realizations of `grad` and `curl`):
the parity extension `J` is a **scaled embedding** (scale `8 = 2³`) of the bounded-domain complex
into the torus complex whose range is the real parity fields, and the bounded-domain complex is
the compression of the torus complex along it.

## The parity extension

For a parity vector `c ∈ {±1}³` the scalar extension `X_c f = Σ_ε sign_c(ε) · (E₀ f) ∘ R_ε`
(`E₀ = resQ†` the extension by zero from `Q` to the box) is a bounded operator
`L²(Q) → L²(𝕋³)` with `X_c Φ = ext_c Φ` on test functions (`Feec.Models.Cube.Geometry.ext`),
`(X_c f)|_Q = f`, `X_c f ∘ R_ε = sign_c(ε) X_c f` and `‖X_c f‖² = 8 ‖f‖²`. On fields, the parity
vectors of the three slots are those of the thesis' boundary conditions (`σ` odd in every
variable, `E_{ab}` even in `x_b` only, `B_{ab}` odd in `x_b` only), and on the Fourier side the
extension is `J`.

## The boundary conditions

The extension maps `H̊¹(Q)` and `H̊(curl, Q)` into the torus domains (`RowWise.J_mem_graph_grad`,
`RowWise.J_mem_graph_curl`, from the test fields by closure), and conversely a field on `Q`
whose extension lies in the torus domain satisfies the boundary condition
(`RowWise.mem_minimal_grad_of_J`, `RowWise.mem_minimal_curl_of_J`): the Fourier truncations of
the extension are trigonometric polynomials of the right parities, whose restrictions to `Q` are
smooth fields that a cut-off `χ_n` (equal to `1` at distance `≥ 1/n` from the faces) turns into
test fields; the parities bound the cut-off error near the faces.

## Only stationary data propagate on `Q`

The wave group on `Q` is the restriction of the torus wave group (`RowWise.waveGroup_J`), which
has pure point spectrum, so forward invariance of `{0} × S₁ × S₂`, `S₁, S₂ ⊆ L²(TSD)`, forces
stationarity (`RowWise.forward_iff`), and the invariant core of the thesis' constraint consists of
the data `(0, 0, B₀)` with `B₀ ∈ L²(TSD)` and `d₁† B₀ = 0` (`RowWise.mem_invariantCore_tsd_iff`).

## Main definitions

* `RowWise.X`, `RowWise.JR`, `RowWise.J` (slot by slot `J0`, `J1`, `J2`), `RowWise.Jr`;
  `RowWise.cubeComplex`; `RowWise.scaledEmbedding`; `RowWise.torusSub`.

## Main results

* `RowWise.resQ_X`, `RowWise.X_reflB`, `RowWise.norm_sq_X`, `RowWise.X_toL2`; `RowWise.range_J`,
  `RowWise.inner_J`.
* `RowWise.J_mem_graph_grad`, `RowWise.J_mem_graph_curl`, **`RowWise.mem_minimal_grad_of_J`**,
  **`RowWise.mem_minimal_curl_of_J`**.
* **`RowWise.cubeComplex_eq_compress`**: the complex on `Q` is the compression of the real torus
  grad–curl complex along `J`; `RowWise.waveGroup_J`.
* `RowWise.inj₂_mem_stationary_iff` (any short complex), **`RowWise.forward_iff`**,
  **`RowWise.mem_invariantCore_iff`**, **`RowWise.mem_invariantCore_tsd_iff`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the complex `H̊¹ → H̊(curl) → L²`, Prop 4.17)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension by reflection), §9.4 (`W₀^{1,p}`, cut-off arguments)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter LinearPMap Feec.Fourier Feec.ShortHilbertComplex

@[expose] public noncomputable section

namespace Feec.Models.Cube.RowWise

open Feec.Models.Torus.GradCurl (Space)
open Feec.Models.Cube.Geometry (Q resQ resQF ext per reflB sign)
open Feec.Fourier.TorusWeak (toL2 toL2_ae_eq IsSmooth proj)

/- Over `ℝ`, the real structure of `W3` is the one of its inner product space. -/
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

attribute [local instance] RealTorus.isScalarTower

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- `L²(𝕋³)`. -/
abbrev L2T : Type := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))

/-! ### The scalar parity extension -/

section Scalar

/-- **Extension by zero** from `Q` to the box: the adjoint of the restriction. -/
def E₀ : Domain.L2 ℂ (Q (Fin 3)) →L[ℂ] L2T := ContinuousLinearMap.adjoint resQ

/-- The reflection `f ↦ f ∘ R_ε` of `L²(𝕋³)`. -/
def reflL (ε : Fin 3 → Bool) : L2T →L[ℂ] L2T :=
  (Lp.compMeasurePreservingₗᵢ ℂ (reflB ε)
    (Geometry.measurePreserving_reflB ε)).toContinuousLinearMap

theorem coeFn_reflL (ε : Fin 3 → Bool) (f : L2T) :
    (reflL ε f : UnitAddTorus (Fin 3) → ℂ) =ᵐ[volume]
      fun x => (f : UnitAddTorus (Fin 3) → ℂ) (reflB ε x) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- **The parity extension** `X_c f = Σ_ε sign_c(ε) (E₀ f) ∘ R_ε`. -/
def X (c : Fin 3 → ℂ) : Domain.L2 ℂ (Q (Fin 3)) →L[ℂ] L2T :=
  ∑ ε : Fin 3 → Bool, sign c ε • (reflL ε).comp E₀

/-- **The extension by zero of a test function is its periodization.** -/
theorem E₀_toL2 {Φ : (Fin 3 → ℝ) → ℂ} (hΦ : Domain.IsTest (Q (Fin 3)) Φ) :
    E₀ (Domain.toL2 hΦ) = toL2 (Geometry.isSmooth_per hΦ).continuous := by
  refine ext_inner_right ℂ fun g => ?_
  rw [E₀, ContinuousLinearMap.adjoint_inner_left]
  have hc : Domain.IsTest (Q (Fin 3)) fun y => conj (Φ y) := hΦ.conjugate
  have h1 := Geometry.integral_mul_per g hc
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have e1 : (fun x => ⟪(toL2 (Geometry.isSmooth_per hΦ).continuous : UnitAddTorus (Fin 3) → ℂ) x,
      (g : UnitAddTorus (Fin 3) → ℂ) x⟫_ℂ) =ᵐ[volume]
      fun x => (g : UnitAddTorus (Fin 3) → ℂ) x * per (fun y => conj (Φ y)) x := by
    filter_upwards [toL2_ae_eq (Geometry.isSmooth_per hΦ).continuous] with x hx
    rw [hx, RCLike.inner_apply]; simp only [per]

  have e2 : (fun y => ⟪(Domain.toL2 hΦ : (Fin 3 → ℝ) → ℂ) y, (resQ g : (Fin 3 → ℝ) → ℂ) y⟫_ℂ)
      =ᵐ[volume.restrict (Q (Fin 3))] fun y => resQ g y * conj (Φ y) := by
    filter_upwards [Domain.coeFn_toL2 hΦ] with y hy
    rw [hy, RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae e1, integral_congr_ae e2, h1]

variable (Ω : Set (Fin 3 → ℝ)) in
/-- The test functions `C_c^∞(Ω; ℂ)` inside `L²(Ω; ℂ)`. -/
def testSub : Submodule ℂ (Domain.L2 ℂ Ω) where
  carrier := {u | ∃ Φ : (Fin 3 → ℝ) → ℂ, ∃ hΦ : Domain.IsTest Ω Φ, u = Domain.toL2 hΦ}
  zero_mem' := ⟨0, Domain.IsTest.zero, Domain.toL2_zero.symm⟩
  add_mem' := by
    rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, hφ.add hψ, (Domain.toL2_add hφ hψ).symm⟩
  smul_mem' := by
    rintro c _ ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, hφ.smul c, (Domain.toL2_smul c hφ).symm⟩

/-- Test functions are dense in `L²(Ω; ℂ)`. -/
theorem dense_testSub {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) :
    Dense (testSub Ω : Set (Domain.L2 ℂ Ω)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  refine Domain.L2.eq_zero_of_forall_inner_toL2 hΩ v fun g hg => ?_
  rw [← inner_conj_symm, (Submodule.mem_orthogonal _ _).1 hv _ ⟨g, hg, rfl⟩, _root_.map_zero]

/-- **The parity extension of a test function is its extension `ext_c`.** -/
theorem X_toL2 (c : Fin 3 → ℂ) {Φ : (Fin 3 → ℝ) → ℂ} (hΦ : Domain.IsTest (Q (Fin 3)) Φ) :
    X c (Domain.toL2 hΦ) = toL2 (Geometry.continuous_ext c hΦ) := by
  refine Lp.ext ?_
  have hsum : (X c (Domain.toL2 hΦ) : UnitAddTorus (Fin 3) → ℂ) =ᵐ[volume]
      ∑ ε : Fin 3 → Bool, ((sign c ε • reflL ε (E₀ (Domain.toL2 hΦ)) : L2T) :
        UnitAddTorus (Fin 3) → ℂ) := by
    have : X c (Domain.toL2 hΦ) = ∑ ε : Fin 3 → Bool, sign c ε • reflL ε (E₀ (Domain.toL2 hΦ)) := by
      simp [X]
    rw [this]
    exact Lp.coeFn_finsetSum _ _
  have hterm : ∀ ε : Fin 3 → Bool, ((sign c ε • reflL ε (E₀ (Domain.toL2 hΦ)) : L2T) :
      UnitAddTorus (Fin 3) → ℂ) =ᵐ[volume] fun x => sign c ε * per Φ (reflB ε x) := fun ε => by
    rw [E₀_toL2]
    filter_upwards [Lp.coeFn_smul (sign c ε) (reflL ε (toL2 (Geometry.isSmooth_per hΦ).continuous)),
      coeFn_reflL ε (toL2 (Geometry.isSmooth_per hΦ).continuous),
      (Geometry.measurePreserving_reflB ε).quasiMeasurePreserving.ae_eq_comp
        (toL2_ae_eq (Geometry.isSmooth_per hΦ).continuous)] with x h1 h2 h3
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    exact congrArg _ h3
  filter_upwards [hsum, ae_all_iff.2 hterm, toL2_ae_eq (Geometry.continuous_ext c hΦ)]
    with x h1 h2 h3
  rw [h1, h3, Finset.sum_apply, Geometry.ext]
  exact Finset.sum_congr rfl fun ε _ => h2 ε

/-- **The parity extension restricts back**: `(X_c f)|_Q = f`. -/
theorem resQ_X (c : Fin 3 → ℂ) (f : Domain.L2 ℂ (Q (Fin 3))) : resQ (X c f) = f := by
  have h : resQ.comp (X c) = ContinuousLinearMap.id ℂ _ := by
    refine ContinuousLinearMap.ext_on (s := testSub (Q (Fin 3))) ?_ ?_
    · rw [Submodule.span_eq]; exact dense_testSub Geometry.isOpen_Q
    · rintro _ ⟨Φ, hΦ, rfl⟩
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_id',
        id_eq, X_toL2]
      exact Geometry.resQ_toL2_ext c hΦ
  exact congrArg (fun T : Domain.L2 ℂ (Q (Fin 3)) →L[ℂ] Domain.L2 ℂ (Q (Fin 3)) => T f) h

variable {c : Fin 3 → ℂ}

/-- **Parity of the extension**: `X_c f ∘ R_η = sign_c(η) · X_c f`. -/
theorem X_reflB (hc : ∀ j, c j * c j = 1) (η : Fin 3 → Bool) (f : Domain.L2 ℂ (Q (Fin 3))) :
    reflL η (X c f) = sign c η • X c f := by
  have h : (reflL η).comp (X c) = sign c η • X c := by
    refine ContinuousLinearMap.ext_on (s := testSub (Q (Fin 3))) ?_ ?_
    · rw [Submodule.span_eq]; exact dense_testSub Geometry.isOpen_Q
    · rintro _ ⟨Φ, hΦ, rfl⟩
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, FunLike.coe_smul,
        Pi.smul_apply, X_toL2]
      refine Lp.ext ?_
      filter_upwards [coeFn_reflL η (toL2 (Geometry.continuous_ext c hΦ)),
        (Geometry.measurePreserving_reflB η).quasiMeasurePreserving.ae_eq_comp
          (toL2_ae_eq (Geometry.continuous_ext c hΦ)),
        Lp.coeFn_smul (sign c η) (toL2 (Geometry.continuous_ext c hΦ)),
        toL2_ae_eq (Geometry.continuous_ext c hΦ)] with x h1 h2 h3 h4
      rw [h1, h3, Pi.smul_apply, h4, smul_eq_mul]
      change (toL2 (Geometry.continuous_ext c hΦ) : UnitAddTorus (Fin 3) → ℂ) (reflB η x) = _
      rw [show (toL2 (Geometry.continuous_ext c hΦ) : UnitAddTorus (Fin 3) → ℂ) (reflB η x) =
        ext c Φ (reflB η x) from h2, Geometry.ext_reflB hc]
  exact congrArg (fun T : Domain.L2 ℂ (Q (Fin 3)) →L[ℂ] L2T => T f) h

/-- **The norm of the extension**: `‖X_c f‖² = 8 ‖f‖²`. -/
theorem norm_sq_X (hc : ∀ j, c j * c j = 1) (f : Domain.L2 ℂ (Q (Fin 3))) :
    ‖X c f‖ ^ 2 = 8 * ‖f‖ ^ 2 := by
  have h := Geometry.norm_sq_eq_two_pow (f := X c f) fun η => by
    filter_upwards [coeFn_reflL η (X c f), Lp.coeFn_smul (sign c η) (X c f)] with x h1 h2
    rw [← h1, X_reflB hc, h2, Pi.smul_apply, smul_eq_mul, norm_mul,
      Geometry.norm_sign hc, one_mul]
  rw [h, resQ_X]
  norm_num

/-- `X_c / √8` is a linear isometry. -/
def Xiso (hc : ∀ j, c j * c j = 1) : Domain.L2 ℂ (Q (Fin 3)) →ₗᵢ[ℂ] L2T where
  toLinearMap := (((Real.sqrt 8)⁻¹ : ℝ) : ℂ) • (X c : Domain.L2 ℂ (Q (Fin 3)) →ₗ[ℂ] L2T)
  norm_map' u := by
    change ‖(((Real.sqrt 8)⁻¹ : ℝ) : ℂ) • X c u‖ = ‖u‖
    have h8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 h8)]
    have : ‖X c u‖ = Real.sqrt 8 * ‖u‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (X c u)), norm_sq_X hc, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (norm_nonneg u)]
    rw [this, ← mul_assoc, inv_mul_cancel₀ h8.ne', one_mul]

/-- `⟪X_c f, X_c g⟫ = 8 ⟪f, g⟫`. -/
theorem inner_X (hc : ∀ j, c j * c j = 1) (f g : Domain.L2 ℂ (Q (Fin 3))) :
    ⟪X c f, X c g⟫_ℂ = 8 * ⟪f, g⟫_ℂ := by
  have h := (Xiso hc).inner_map_map f g
  change ⟪(((Real.sqrt 8)⁻¹ : ℝ) : ℂ) • X c f, (((Real.sqrt 8)⁻¹ : ℝ) : ℂ) • X c g⟫_ℂ = _ at h
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    ← mul_inv, Real.mul_self_sqrt (by norm_num)] at h
  rw [← h]; push_cast; field_simp

/-! #### Real extensions -/

/-- Complex conjugation of `L²` functions, as a real-linear map. -/
def cjL {α : Type*} [MeasurableSpace α] (μ : Measure α) : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  (Complex.conjCLE.toContinuousLinearMap).compLpL 2 μ

theorem coeFn_cjL {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℂ 2 μ) :
    (cjL μ f : α → ℂ) =ᵐ[μ] fun x => conj ((f : α → ℂ) x) :=
  (Complex.conjCLE.toContinuousLinearMap).coeFn_compLpL f

theorem cjL_eq_star {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℂ 2 μ) :
    cjL μ f = star f :=
  Lp.ext ((coeFn_cjL f).trans (Lp.coeFn_star f).symm)

theorem conj_sign (hc : ∀ j, conj (c j) = c j) (ε : Fin 3 → Bool) : conj (sign c ε) = sign c ε := by
  rw [sign, map_prod]
  exact Finset.prod_congr rfl fun j _ => by split_ifs <;> simp [hc j]

/-- **The extension commutes with complex conjugation** (real parity vectors). -/
theorem X_star (hc : ∀ j, conj (c j) = c j) (f : Domain.L2 ℂ (Q (Fin 3))) :
    star (X c f) = X c (star f) := by
  rw [← cjL_eq_star, ← cjL_eq_star]
  have h : (cjL (volume : Measure (UnitAddTorus (Fin 3)))).comp ((X c).restrictScalars ℝ) =
      ((X c).restrictScalars ℝ).comp (cjL (volume.restrict (Q (Fin 3)))) := by
    refine ContinuousLinearMap.ext_on (s := ((testSub (Q (Fin 3)) : Submodule ℂ _) : Set _)) ?_ ?_
    · refine (dense_testSub Geometry.isOpen_Q).mono ?_
      exact Submodule.subset_span
    · rintro _ ⟨Φ, hΦ, rfl⟩
      have hcΦ : Domain.IsTest (Q (Fin 3)) fun y => conj (Φ y) := hΦ.conjugate
      have e1 : cjL (volume.restrict (Q (Fin 3))) (Domain.toL2 hΦ) = Domain.toL2 hcΦ := by
        refine Lp.ext ?_
        filter_upwards [coeFn_cjL (Domain.toL2 hΦ), Domain.coeFn_toL2 hΦ, Domain.coeFn_toL2 hcΦ]
          with y h1 h2 h3
        rw [h1, h2, h3]
      have hext : ∀ x, conj (ext c Φ x) = ext c (fun y => conj (Φ y)) x := fun x => by
        simp only [Geometry.ext, map_sum, map_mul, conj_sign hc, per]
      change cjL volume (X c (Domain.toL2 hΦ)) = X c (cjL (volume.restrict (Q (Fin 3)))
        (Domain.toL2 hΦ))
      rw [e1, X_toL2, X_toL2]
      refine Lp.ext ?_
      filter_upwards [coeFn_cjL (toL2 (Geometry.continuous_ext c hΦ)),
        toL2_ae_eq (Geometry.continuous_ext c hΦ), toL2_ae_eq (Geometry.continuous_ext c hcΦ)]
        with x h1 h2 h3
      rw [h1, h2, h3, hext]
  exact congrArg (fun T : Domain.L2 ℂ (Q (Fin 3)) →L[ℝ] L2T => T f) h

end Scalar

/-! ### Real and complex `L²` -/

section RealComplex

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Real functions as complex ones. -/
def ofRealL (μ : Measure α) : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

/-- The real part. -/
def reL (μ : Measure α) : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ

theorem coeFn_ofRealL (f : Lp ℝ 2 μ) : (ofRealL μ f : α → ℂ) =ᵐ[μ] fun x => ((f x : ℝ) : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

theorem coeFn_reL (f : Lp ℂ 2 μ) : (reL μ f : α → ℝ) =ᵐ[μ] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f

theorem reL_ofRealL (f : Lp ℝ 2 μ) : reL μ (ofRealL μ f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reL (ofRealL μ f), coeFn_ofRealL f] with x h1 h2
  rw [h1, h2, Complex.ofReal_re]

theorem ofRealL_reL {f : Lp ℂ 2 μ} (hf : star f = f) : ofRealL μ (reL μ f) = f := by
  refine Lp.ext ?_
  have hs := Lp.coeFn_star f
  rw [hf] at hs
  filter_upwards [coeFn_ofRealL (reL μ f), coeFn_reL f, hs] with x h1 h2 h3
  rw [h1, h2]
  have : conj ((f : α → ℂ) x) = (f : α → ℂ) x := by
    rw [← Complex.star_def]; exact h3.symm
  exact Complex.conj_eq_iff_re.1 this

theorem star_ofRealL (f : Lp ℝ 2 μ) : star (ofRealL μ f) = ofRealL μ f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (ofRealL μ f), coeFn_ofRealL f] with x h1 h2
  rw [h1, Pi.star_apply, h2, Complex.star_def, Complex.conj_ofReal]

theorem inner_ofRealL (f g : Lp ℝ 2 μ) : ⟪ofRealL μ f, ofRealL μ g⟫_ℂ = (⟪f, g⟫_ℝ : ℂ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_ofRealL f, coeFn_ofRealL g] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

end RealComplex

/-! ### The parity extension of fields -/

section Fields

variable {P : Type*} [Fintype P] (pc : P → Fin 3 → ℂ)

/-- The parity extension of fields, componentwise with parity vectors `pc p`. -/
def Xf : Domain.L2F ℂ (Q (Fin 3)) P →L[ℂ] TorusWeak.Field (Fin 3) P where
  toFun f := WithLp.toLp 2 fun p => X (pc p) (f p)
  map_add' f g := by ext p; simp
  map_smul' a f := by ext p; simp
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    (X (pc p)).continuous.comp (PiLp.continuous_apply 2 _ p))

omit [Fintype P] in
@[simp] theorem Xf_apply (f : Domain.L2F ℂ (Q (Fin 3)) P) (p : P) :
    Xf pc f p = X (pc p) (f p) := rfl

/-- Real fields as complex fields. -/
def ofRealF : Domain.L2F ℝ (Q (Fin 3)) P →L[ℝ] Domain.L2F ℂ (Q (Fin 3)) P where
  toFun f := WithLp.toLp 2 fun p => ofRealL _ (f p)
  map_add' f g := by ext p; simp
  map_smul' a f := by ext p; simp
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    (ofRealL _).continuous.comp (PiLp.continuous_apply 2 _ p))

omit [Fintype P] in
@[simp] theorem ofRealF_apply (f : Domain.L2F ℝ (Q (Fin 3)) P) (p : P) :
    ofRealF f p = ofRealL _ (f p) := rfl

/-- The real part of complex fields. -/
def reF : Domain.L2F ℂ (Q (Fin 3)) P →L[ℝ] Domain.L2F ℝ (Q (Fin 3)) P where
  toFun f := WithLp.toLp 2 fun p => reL _ (f p)
  map_add' f g := by ext p; simp
  map_smul' a f := PiLp.ext fun p => (reL _).map_smul_of_tower a (f p)
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    (reL _).continuous.comp (PiLp.continuous_apply 2 _ p))

omit [Fintype P] in
@[simp] theorem reF_apply (f : Domain.L2F ℂ (Q (Fin 3)) P) (p : P) : reF f p = reL _ (f p) := rfl

/-- **The parity extension on the Fourier side**, complex fields. -/
def JC : Domain.L2F ℂ (Q (Fin 3)) P →L[ℂ]
    Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  (Fourier.Torus.fieldFourier (Fin 3) P).toContinuousLinearEquiv.toContinuousLinearMap.comp (Xf pc)

/-- **The parity extension on the Fourier side**, real fields. -/
def JR : Domain.L2F ℝ (Q (Fin 3)) P →L[ℝ]
    Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  ((JC pc).restrictScalars ℝ).comp ofRealF

/-- The restriction of Fourier-side fields to `Q`, real part. -/
def Jinv : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (Fin 3 → ℤ)) →L[ℝ]
    Domain.L2F ℝ (Q (Fin 3)) P :=
  reF.comp ((resQF.restrictScalars ℝ).comp
    ((ContinuousLinearEquiv.toContinuousLinearMap
      (Fourier.Torus.fieldFourier (Fin 3) P).symm.toContinuousLinearEquiv).restrictScalars ℝ))

theorem JR_apply (u : Domain.L2F ℝ (Q (Fin 3)) P) :
    JR pc u = Fourier.Torus.fieldFourier (Fin 3) P (Xf pc (ofRealF u)) := rfl

theorem coeff_JR (u : Domain.L2F ℝ (Q (Fin 3)) P) (n : Fin 3 → ℤ) (p : P) :
    (JR pc u : (Fin 3 → ℤ) → EuclideanSpace ℂ P) n p =
      UnitAddTorus.mFourierCoeff (X (pc p) (ofRealL _ (u p)) : UnitAddTorus (Fin 3) → ℂ) n :=
  Fourier.Torus.fieldFourier_apply _ n p

variable {pc}

/-- `Jinv` inverts `J`. -/
theorem Jinv_JR (u : Domain.L2F ℝ (Q (Fin 3)) P) : Jinv (JR pc u) = u := by
  refine PiLp.ext fun p => ?_
  change reL _ (resQ ((Fourier.Torus.fieldFourier (Fin 3) P).symm
    (Fourier.Torus.fieldFourier (Fin 3) P (Xf pc (ofRealF u))) p)) = u p
  rw [LinearIsometryEquiv.symm_apply_apply, Xf_apply, resQ_X, ofRealF_apply, reL_ofRealL]

/-- **`J` scales inner products by `8`.** -/
theorem inner_JR (hc : ∀ p j, pc p j * pc p j = 1) (u v : Domain.L2F ℝ (Q (Fin 3)) P) :
    ⟪JR pc u, JR pc v⟫_ℝ = 8 * ⟪u, v⟫_ℝ := by
  rw [MeasureTheory.L2.real_inner_eq_re_inner EuclideanSpace.real_inner_eq_re_inner, JR_apply,
    JR_apply, LinearIsometryEquiv.inner_map_map, PiLp.inner_apply, Domain.L2F.inner_def]
  simp only [Xf_apply, ofRealF_apply, inner_X (hc _), inner_ofRealL]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum]
  change Complex.re ((8 : ℂ) * ((∑ i, ⟪u i, v i⟫_ℝ : ℝ) : ℂ)) = _
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.ofReal_re]

end Fields

/-! ### Fourier-side parities -/

section FourierParity

open UnitAddTorus
open Geometry (flipB)

theorem mFourierCoeff_congr_ae {f g : UnitAddTorus (Fin 3) → ℂ} (h : f =ᵐ[volume] g)
    (n : Fin 3 → ℤ) : mFourierCoeff f n = mFourierCoeff g n :=
  integral_congr_ae (h.mono fun x hx => by simp only [hx])

theorem mFourierCoeff_smul (a : ℂ) (f : L2T) (n : Fin 3 → ℤ) :
    mFourierCoeff ((a • f : L2T) : UnitAddTorus (Fin 3) → ℂ) n =
      a * mFourierCoeff (f : UnitAddTorus (Fin 3) → ℂ) n := by
  rw [mFourierCoeff_congr_ae (Lp.coeFn_smul a f)]
  simp only [mFourierCoeff, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-- The Fourier coefficients of a reflected `L²` function. -/
theorem mFourierCoeff_reflL (ε : Fin 3 → Bool) (f : L2T) (n : Fin 3 → ℤ) :
    mFourierCoeff (reflL ε f : UnitAddTorus (Fin 3) → ℂ) n =
      mFourierCoeff (f : UnitAddTorus (Fin 3) → ℂ) (flipB ε n) := by
  rw [mFourierCoeff_congr_ae (coeFn_reflL ε f), Geometry.mFourierCoeff_comp_reflB]

variable {c : Fin 3 → ℂ}

/-- **Fourier parity of the extension**: `(X_c f)^(flip_ε n) = sign_c(ε) (X_c f)^(n)`. -/
theorem mFourierCoeff_X_flipB (hc : ∀ j, c j * c j = 1) (f : Domain.L2 ℂ (Q (Fin 3)))
    (ε : Fin 3 → Bool) (n : Fin 3 → ℤ) :
    mFourierCoeff (X c f : UnitAddTorus (Fin 3) → ℂ) (flipB ε n) =
      sign c ε * mFourierCoeff (X c f : UnitAddTorus (Fin 3) → ℂ) n := by
  rw [← mFourierCoeff_reflL, X_reflB hc, mFourierCoeff_smul]

/-- **Reality of the extension of real functions**: `(X_c u)^(-n) = conj (X_c u)^(n)`. -/
theorem mFourierCoeff_X_neg (hc : ∀ j, conj (c j) = c j)
    (u : Domain.L2 ℝ (Q (Fin 3))) (n : Fin 3 → ℤ) :
    mFourierCoeff (X c (ofRealL _ u) : UnitAddTorus (Fin 3) → ℂ) (-n) =
      conj (mFourierCoeff (X c (ofRealL _ u) : UnitAddTorus (Fin 3) → ℂ) n) :=
  (TorusWeak.star_eq_self_iff _).1 (by rw [X_star hc, star_ofRealL]) n

/-- The single reflection `R_k`. -/
def single (k : Fin 3) : Fin 3 → Bool := fun j => decide (j = k)

theorem flipB_single (k : Fin 3) (n : Fin 3 → ℤ) : flipB (single k) n = MirrorTorus.flip k n := by
  funext j; simp [flipB, single, MirrorTorus.flip]

theorem sign_single (k : Fin 3) : sign c (single k) = c k := by
  rw [sign, Finset.prod_eq_single k (fun j _ hj => by simp [single, hj]) (by simp)]
  simp [single]

theorem flipB_xor (ε η : Fin 3 → Bool) (n : Fin 3 → ℤ) :
    flipB (fun j => xor (ε j) (η j)) n = flipB ε (flipB η n) := by
  funext j; by_cases h1 : ε j <;> by_cases h2 : η j <;> simp [flipB, h1, h2]

/-- Every reflection is a product of single reflections. -/
theorem forall_of_single {P : (Fin 3 → Bool) → Prop} (h0 : P fun _ => false)
    (hstep : ∀ ε k, P ε → P fun j => xor (ε j) (single k j)) (ε : Fin 3 → Bool) : P ε := by
  have key : ∀ s : Finset (Fin 3), P fun j => decide (j ∈ s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      convert hstep _ a ih using 1
      funext j
      by_cases hj : j = a
      · subst hj; simp [single, ha]
      · simp [single, hj]
  convert key (Finset.univ.filter fun j => ε j = true) using 1
  funext j; simp

/-- **Fourier parities from single reflections**: if `x(flip_k n) = c_k x(n)` for every single
reflection, then `x(flip_ε n) = sign_c(ε) x(n)` for every reflection. -/
theorem flipB_of_single (hc : ∀ j, c j * c j = 1) {g : (Fin 3 → ℤ) → ℂ}
    (h : ∀ k n, g (MirrorTorus.flip k n) = c k * g n) (ε : Fin 3 → Bool) (n : Fin 3 → ℤ) :
    g (flipB ε n) = sign c ε * g n := by
  revert n
  refine forall_of_single (P := fun ε => ∀ n, g (flipB ε n) = sign c ε * g n) (fun n => ?_)
    (fun ε k hε n => ?_) ε
  · have : flipB (fun _ => false) n = n := by funext j; simp [flipB]
    rw [this]; simp [sign]
  · rw [flipB_xor, hε, flipB_single, h, Geometry.sign_xor hc, sign_single]; ring

/-- Restriction commutes with complex conjugation. -/
theorem resQ_star (f : L2T) : star (resQ f) = resQ (star f) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (resQ f), Geometry.coeFn_resQ f, Geometry.coeFn_resQ (star f),
    Geometry.ae_Q_of_ae_boxSet (ae_restrict_of_ae (Lp.coeFn_star f))] with y h1 h2 h3 h4
  rw [h1, Pi.star_apply, h2, h3, h4]
  rfl

/-- **Real parity fields are extensions**: a Fourier-side field `x` with real entries
(`x(-n) = conj x(n)`) and the parities `pc` (`x(flip_ε n)_p = sign_{pc p}(ε) x(n)_p`) is the
extension of its restriction to `Q`. -/
theorem JR_Jinv {P : Type*} [Fintype P] {pc : P → Fin 3 → ℂ} (hc : ∀ p j, pc p j * pc p j = 1)
    {x : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (Fin 3 → ℤ))}
    (hreal : ∀ n p, (x : (Fin 3 → ℤ) → EuclideanSpace ℂ P) (-n) p =
      conj ((x : (Fin 3 → ℤ) → EuclideanSpace ℂ P) n p))
    (hpar : ∀ ε n p, (x : (Fin 3 → ℤ) → EuclideanSpace ℂ P) (flipB ε n) p =
      sign (pc p) ε * (x : (Fin 3 → ℤ) → EuclideanSpace ℂ P) n p) :
    JR pc (Jinv x) = x := by
  set f := (Fourier.Torus.fieldFourier (Fin 3) P).symm x
  have hcoef : ∀ p n, mFourierCoeff (f p : UnitAddTorus (Fin 3) → ℂ) n =
      (x : (Fin 3 → ℤ) → EuclideanSpace ℂ P) n p := fun p n => by
    rw [← Fourier.Torus.fieldFourier_apply, LinearIsometryEquiv.apply_symm_apply]
  have hstar : ∀ p, star (f p) = f p := fun p =>
    (TorusWeak.star_eq_self_iff _).2 fun n => by rw [hcoef, hcoef, hreal]
  have hrefl : ∀ p ε, reflL ε (f p) = sign (pc p) ε • f p := fun p ε =>
    TorusWeak.eq_of_mFourierCoeff_eq fun n => by
      rw [mFourierCoeff_reflL, mFourierCoeff_smul, hcoef, hcoef, hpar]
  have hX : ∀ p, X (pc p) (resQ (f p)) = f p := fun p => by
    set h := X (pc p) (resQ (f p)) - f p
    have hh : ∀ ε, reflL ε h = sign (pc p) ε • h := fun ε => by
      rw [_root_.map_sub, X_reflB (hc p), hrefl, smul_sub]
    refine sub_eq_zero.1 (Geometry.eq_zero_of_resQ_eq_zero (fun η => ?_) ?_)
    · filter_upwards [coeFn_reflL η h, Lp.coeFn_smul (sign (pc p) η) h] with x h1 h2
      rw [← h1, hh, h2, Pi.smul_apply, smul_eq_mul, norm_mul, Geometry.norm_sign (hc p), one_mul]
    · rw [_root_.map_sub, resQ_X, sub_self]
  have hres : ∀ p, ofRealL _ (reL _ (resQ (f p))) = resQ (f p) := fun p =>
    ofRealL_reL (by rw [resQ_star, hstar])
  change Fourier.Torus.fieldFourier (Fin 3) P (Xf pc (ofRealF (Jinv x))) = x
  refine (Fourier.Torus.fieldFourier (Fin 3) P).symm.injective ?_
  rw [LinearIsometryEquiv.symm_apply_apply]
  refine PiLp.ext fun p => ?_
  change X (pc p) (ofRealL _ (reL _ (resQ (f p)))) = f p
  rw [hres, hX]

end FourierParity

/-! ### The three slots -/

section Slots

open UnitAddTorus Fourier.GradCurl
open Geometry (flipB)
open MirrorTorus (sgn)
open Models.BoundedDomain (Ix)

/-- The parities of `σ`: odd in every variable. -/
def pv : Fin 3 → Fin 3 → ℂ := fun _ _ => -1

/-- The parities of `E_{ab}`: even in `x_b`, odd in the other variables. -/
def pe : Ix → Fin 3 → ℂ := fun p j => if j = p.2 then 1 else -1

/-- The parities of `B_{ab}`: odd in `x_b`, even in the other variables. -/
def pb : Ix → Fin 3 → ℂ := fun p j => if j = p.2 then -1 else 1

theorem pv_mul_self (a j : Fin 3) : pv a j * pv a j = 1 := by simp [pv]
theorem pe_mul_self (p : Ix) (j : Fin 3) : pe p j * pe p j = 1 := by
  unfold pe; split_ifs <;> norm_num
theorem pb_mul_self (p : Ix) (j : Fin 3) : pb p j * pb p j = 1 := by
  unfold pb; split_ifs <;> norm_num
theorem conj_pv (a j : Fin 3) : conj (pv a j) = pv a j := by simp [pv]
theorem conj_pe (p : Ix) (j : Fin 3) : conj (pe p j) = pe p j := by
  unfold pe; split_ifs <;> simp
theorem conj_pb (p : Ix) (j : Fin 3) : conj (pb p j) = pb p j := by
  unfold pb; split_ifs <;> simp

theorem pe_eq (p : Ix) (k : Fin 3) : pe p k = -sgn k p.2 := by
  unfold pe sgn; by_cases h : k = p.2
  · subst h; simp
  · simp [h, Ne.symm h]

theorem pb_eq (p : Ix) (k : Fin 3) : pb p k = sgn k p.2 := by
  unfold pb sgn; by_cases h : k = p.2
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The Fourier coefficients of the first slot. -/
def cv (x : Space 0) (n : Fin 3 → ℤ) : Vec := x n

/-- The Fourier coefficients of the second slot. -/
def c1 (x : Space 1) (n : Fin 3 → ℤ) : Mat := x n

/-- The Fourier coefficients of the third slot. -/
def c2 (x : Space 2) (n : Fin 3 → ℤ) : Mat := x n

theorem ext_cv {x y : Space 0} (h : ∀ n a, cv x n a = cv y n a) : x = y :=
  Lp.ext_count fun n => (WithLp.ext_iff 2).2 (funext (h n))

theorem ext_c1 {x y : Space 1} (h : ∀ n p, c1 x n p = c1 y n p) : x = y :=
  Lp.ext_count fun n => (WithLp.ext_iff 2).2 (funext (h n))

theorem ext_c2 {x y : Space 2} (h : ∀ n p, c2 x n p = c2 y n p) : x = y :=
  Lp.ext_count fun n => (WithLp.ext_iff 2).2 (funext (h n))

theorem fixed_zero_iff {x : Space 0} : x ∈ rowAction.fixed 0 ↔
    ∀ k n a, cv x (MirrorTorus.flip k n) a = pv a k * cv x n a := by
  rw [Parity.mem_fixed_iff_coeff]
  refine forall₂_congr fun k n => ?_
  change cv x (MirrorTorus.flip k n) = -cv x n ↔ _
  constructor
  · intro h a; rw [h]; simp [pv]
  · intro h; ext a; rw [h a]; simp [pv]

theorem fixed_one_iff {x : Space 1} : x ∈ rowAction.fixed 1 ↔
    ∀ k n p, c1 x (MirrorTorus.flip k n) p = pe p k * c1 x n p := by
  rw [Parity.mem_fixed_iff_coeff]
  refine forall₂_congr fun k n => ?_
  change c1 x (MirrorTorus.flip k n) = -Parity.colR k (c1 x n) ↔ _
  constructor
  · intro h p; rw [h, PiLp.neg_apply, Parity.colR_apply, pe_eq]; ring
  · intro h; ext p; rw [h p, PiLp.neg_apply, Parity.colR_apply, pe_eq]; ring

theorem fixed_two_iff {x : Space 2} : x ∈ rowAction.fixed 2 ↔
    ∀ k n p, c2 x (MirrorTorus.flip k n) p = pb p k * c2 x n p := by
  rw [Parity.mem_fixed_iff_coeff]
  refine forall₂_congr fun k n => ?_
  change c2 x (MirrorTorus.flip k n) = Parity.colR k (c2 x n) ↔ _
  constructor
  · intro h p; rw [h, Parity.colR_apply, pb_eq]
  · intro h; ext p; rw [h p, Parity.colR_apply, pb_eq]

theorem cnj_zero_iff {x : Space 0} : Parity.cnj 0 x = x ↔
    ∀ n a, cv x (-n) a = conj (cv x n a) := by
  have hc : ∀ n, cv (Parity.cnj 0 x) n = entryConj (cv x (-n)) := fun n => Parity.coeFn_cnj 0 x n
  constructor
  · intro h n a
    have := congrArg (fun v => cv v n a) h
    simp only [hc, entryConj_apply] at this
    rw [← this, RCLike.conj_conj]
  · intro h
    refine ext_cv fun n a => ?_
    rw [hc, entryConj_apply, h, RCLike.conj_conj]

theorem cnj_one_iff {x : Space 1} : Parity.cnj 1 x = x ↔
    ∀ n p, c1 x (-n) p = conj (c1 x n p) := by
  have hc : ∀ n, c1 (Parity.cnj 1 x) n = entryConj (c1 x (-n)) := fun n => Parity.coeFn_cnj 1 x n
  constructor
  · intro h n p
    have := congrArg (fun v => c1 v n p) h
    simp only [hc, entryConj_apply] at this
    rw [← this, RCLike.conj_conj]
  · intro h
    refine ext_c1 fun n p => ?_
    rw [hc, entryConj_apply, h, RCLike.conj_conj]

theorem cnj_two_iff {x : Space 2} : Parity.cnj 2 x = x ↔
    ∀ n p, c2 x (-n) p = conj (c2 x n p) := by
  have hc : ∀ n, c2 (Parity.cnj 2 x) n = entryConj (c2 x (-n)) := fun n => Parity.coeFn_cnj 2 x n
  constructor
  · intro h n p
    have := congrArg (fun v => c2 v n p) h
    simp only [hc, entryConj_apply] at this
    rw [← this, RCLike.conj_conj]
  · intro h
    refine ext_c2 fun n p => ?_
    rw [hc, entryConj_apply, h, RCLike.conj_conj]

/-! #### The extension of each slot -/

/-- The extension of the first slot (`σ` odd in every variable). -/
def J0 : Domain.L2F ℝ (Q (Fin 3)) (Fin 3) →L[ℝ] Space 0 := JR pv

/-- The extension of the second slot (`E_{ab}` even in `x_b` only). -/
def J1 : Domain.L2F ℝ (Q (Fin 3)) Ix →L[ℝ] Space 1 := JR pe

/-- The extension of the third slot (`B_{ab}` odd in `x_b` only). -/
def J2 : Domain.L2F ℝ (Q (Fin 3)) Ix →L[ℝ] Space 2 := JR pb

theorem cv_J0 (u : Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) (n : Fin 3 → ℤ) (a : Fin 3) :
    cv (J0 u) n a = mFourierCoeff (X (pv a) (ofRealL _ (u a)) : UnitAddTorus (Fin 3) → ℂ) n :=
  coeff_JR pv u n a

theorem c1_J1 (u : Domain.L2F ℝ (Q (Fin 3)) Ix) (n : Fin 3 → ℤ) (p : Ix) :
    c1 (J1 u) n p = mFourierCoeff (X (pe p) (ofRealL _ (u p)) : UnitAddTorus (Fin 3) → ℂ) n :=
  coeff_JR pe u n p

theorem c2_J2 (u : Domain.L2F ℝ (Q (Fin 3)) Ix) (n : Fin 3 → ℤ) (p : Ix) :
    c2 (J2 u) n p = mFourierCoeff (X (pb p) (ofRealL _ (u p)) : UnitAddTorus (Fin 3) → ℂ) n :=
  coeff_JR pb u n p

theorem J0_mem (u : Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) : J0 u ∈ Parity.realAction.fixed 0 :=
  Parity.mem_realFixed_iff.2 ⟨cnj_zero_iff.2 fun n a => by
    rw [cv_J0, cv_J0, mFourierCoeff_X_neg (conj_pv a)], fixed_zero_iff.2 fun k n a => by
    rw [cv_J0, cv_J0, ← flipB_single, mFourierCoeff_X_flipB (pv_mul_self a), sign_single]⟩

theorem J1_mem (u : Domain.L2F ℝ (Q (Fin 3)) Ix) : J1 u ∈ Parity.realAction.fixed 1 :=
  Parity.mem_realFixed_iff.2 ⟨cnj_one_iff.2 fun n p => by
    rw [c1_J1, c1_J1, mFourierCoeff_X_neg (conj_pe p)], fixed_one_iff.2 fun k n p => by
    rw [c1_J1, c1_J1, ← flipB_single, mFourierCoeff_X_flipB (pe_mul_self p), sign_single]⟩

theorem J2_mem (u : Domain.L2F ℝ (Q (Fin 3)) Ix) : J2 u ∈ Parity.realAction.fixed 2 :=
  Parity.mem_realFixed_iff.2 ⟨cnj_two_iff.2 fun n p => by
    rw [c2_J2, c2_J2, mFourierCoeff_X_neg (conj_pb p)], fixed_two_iff.2 fun k n p => by
    rw [c2_J2, c2_J2, ← flipB_single, mFourierCoeff_X_flipB (pb_mul_self p), sign_single]⟩

theorem J0_Jinv {x : Space 0} (hx : x ∈ Parity.realAction.fixed 0) : J0 (Jinv x) = x := by
  obtain ⟨hcj, hfix⟩ := Parity.mem_realFixed_iff.1 hx
  have hr := cnj_zero_iff.1 hcj
  have hs := fixed_zero_iff.1 hfix
  exact JR_Jinv pv_mul_self (fun n p => hr n p)
    (fun ε n p => flipB_of_single (pv_mul_self p) (g := fun n => cv x n p)
      (fun k n => hs k n p) ε n)

theorem J1_Jinv {x : Space 1} (hx : x ∈ Parity.realAction.fixed 1) : J1 (Jinv x) = x := by
  obtain ⟨hcj, hfix⟩ := Parity.mem_realFixed_iff.1 hx
  have hr := cnj_one_iff.1 hcj
  have hs := fixed_one_iff.1 hfix
  exact JR_Jinv pe_mul_self (fun n p => hr n p)
    (fun ε n p => flipB_of_single (pe_mul_self p) (g := fun n => c1 x n p)
      (fun k n => hs k n p) ε n)

theorem J2_Jinv {x : Space 2} (hx : x ∈ Parity.realAction.fixed 2) : J2 (Jinv x) = x := by
  obtain ⟨hcj, hfix⟩ := Parity.mem_realFixed_iff.1 hx
  have hr := cnj_two_iff.1 hcj
  have hs := fixed_two_iff.1 hfix
  exact JR_Jinv pb_mul_self (fun n p => hr n p)
    (fun ε n p => flipB_of_single (pb_mul_self p) (g := fun n => c2 x n p)
      (fun k n => hs k n p) ε n)

/-- The spaces of the bounded-domain complex on `Q`. -/
abbrev WQ : Fin 3 → Type :=
  W3 (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) (Domain.L2F ℝ (Q (Fin 3)) Ix) (Domain.L2F ℝ (Q (Fin 3)) Ix)

/-- **The parity extension**, slot by slot. -/
def J : ∀ i : Fin 3, WQ i →L[ℝ] Space i
  | 0 => J0
  | 1 => J1
  | 2 => J2

/-- **The restriction to `Q`**, slot by slot. -/
def Jr : ∀ i : Fin 3, Space i →L[ℝ] WQ i
  | 0 => Jinv
  | 1 => Jinv
  | 2 => Jinv

theorem J_mem (i : Fin 3) (u : WQ i) : J i u ∈ Parity.realAction.fixed i := by
  fin_cases i
  exacts [J0_mem u, J1_mem u, J2_mem u]

theorem Jr_J (i : Fin 3) (u : WQ i) : Jr i (J i u) = u := by
  fin_cases i
  exacts [Jinv_JR u, Jinv_JR u, Jinv_JR u]

theorem J_Jr (i : Fin 3) {x : Space i} (hx : x ∈ Parity.realAction.fixed i) : J i (Jr i x) = x := by
  fin_cases i
  exacts [J0_Jinv hx, J1_Jinv hx, J2_Jinv hx]

/-- **The range of the extension is the real parity fields.** -/
theorem range_J (i : Fin 3) :
    LinearMap.range (J i : WQ i →ₗ[ℝ] Space i) = Parity.realAction.fixed i := by
  ext x
  exact ⟨fun ⟨u, hu⟩ => hu ▸ J_mem i u, fun hx => ⟨Jr i x, J_Jr i hx⟩⟩

/-- **The extension scales inner products by `8`.** -/
theorem inner_J (i : Fin 3) (u v : WQ i) : ⟪J i u, J i v⟫_ℝ = ((8 : ℝ) : ℝ) * ⟪u, v⟫_ℝ := by
  fin_cases i
  · exact inner_JR (fun p j => pv_mul_self p j) u v
  · exact inner_JR (fun p j => pe_mul_self p j) u v
  · exact inner_JR (fun p j => pb_mul_self p j) u v

end Slots

/-! ### Test fields: the extension intertwines `grad` and `curl` -/

section TestFields

open UnitAddTorus Fourier.GradCurl
open Models.BoundedDomain (Ix)

theorem ofRealL_toL2 {φ : (Fin 3 → ℝ) → ℝ} (hφ : Domain.IsTest (Q (Fin 3)) φ) :
    ofRealL _ (Domain.toL2 hφ) = Domain.toL2 (hφ.ofReal (𝕜 := ℂ)) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealL (Domain.toL2 hφ), Domain.coeFn_toL2 hφ,
    Domain.coeFn_toL2 (hφ.ofReal (𝕜 := ℂ))] with y h1 h2 h3
  rw [h1, h2, h3]
  rfl

/-- The coefficients of the extension of a real test function. -/
theorem mFourierCoeff_X_toL2 (c : Fin 3 → ℂ) {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : Domain.IsTest (Q (Fin 3)) φ) (n : Fin 3 → ℤ) :
    mFourierCoeff (X c (ofRealL _ (Domain.toL2 hφ)) : UnitAddTorus (Fin 3) → ℂ) n =
      mFourierCoeff (ext c fun y => (φ y : ℂ)) n := by
  rw [ofRealL_toL2, X_toL2, TorusWeak.mFourierCoeff_toL2]
  rfl

theorem fderiv_ofReal {φ : (Fin 3 → ℝ) → ℝ} (hφ : Differentiable ℝ φ) (y v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (φ y : ℂ)) y v = ((fderiv ℝ φ y v : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := φ y)).comp y (hφ y).hasFDerivAt
  rw [show (fun y => (φ y : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, h.fderiv]
  rfl

/-- The coefficients of a partial derivative of an extension. -/
theorem mFourierCoeff_ext_partial (c : Fin 3 → ℂ) {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : Domain.IsTest (Q (Fin 3)) φ) (b : Fin 3) (n : Fin 3 → ℤ) :
    mFourierCoeff (ext (Function.update c b (-c b))
      fun y => ((fderiv ℝ φ y (Pi.single b 1) : ℝ) : ℂ)) n =
      2 * Real.pi * Complex.I * n b * mFourierCoeff (ext c fun y => (φ y : ℂ)) n := by
  have hΦ : Domain.IsTest (Q (Fin 3)) fun y => (φ y : ℂ) := hφ.ofReal
  have e : (fun y => ((fderiv ℝ φ y (Pi.single b 1) : ℝ) : ℂ)) =
      fun y => fderiv ℝ (fun y => (φ y : ℂ)) y (Pi.single b 1) := by
    funext y; rw [fderiv_ofReal hφ.differentiable]
  rw [e, ← Geometry.partialT_ext c hΦ b,
    TorusWeak.mFourierCoeff_partialT ((Geometry.isSmooth_ext c hΦ).contDiff_one) b n]

theorem update_pv (a b : Fin 3) : Function.update (pv a) b (-pv a b) = pe (a, b) := by
  funext j; by_cases h : j = b
  · subst h; simp [pv, pe]
  · simp [pv, pe, h]

theorem update_pe_one (a b : Fin 3) :
    Function.update (pe (a, b + 2)) (b + 1) (-pe (a, b + 2) (b + 1)) = pb (a, b) := by
  funext j
  fin_cases b <;> fin_cases j <;> simp [pe, pb, Function.update]

theorem update_pe_two (a b : Fin 3) :
    Function.update (pe (a, b + 1)) (b + 2) (-pe (a, b + 1) (b + 2)) = pb (a, b) := by
  funext j
  fin_cases b <;> fin_cases j <;> simp [pe, pb, Function.update]

theorem ext_sub (c : Fin 3 → ℂ) (f g : (Fin 3 → ℝ) → ℂ) :
    ext c (f - g) = ext c f - ext c g := by
  funext x
  simp only [Geometry.ext, per, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem mFourierCoeff_sub_of_continuous {f g : UnitAddTorus (Fin 3) → ℂ} (hf : Continuous f)
    (hg : Continuous g) (n : Fin 3 → ℤ) :
    mFourierCoeff (f - g) n = mFourierCoeff f n - mFourierCoeff g n := by
  simp only [mFourierCoeff, Pi.sub_apply, smul_sub]
  exact integral_sub (TorusWeak.integrable_of_continuous ((mFourier (-n)).continuous.smul hf))
    (TorusWeak.integrable_of_continuous ((mFourier (-n)).continuous.smul hg))

/-- **The extension intertwines the gradients of test fields** (Fourier side): the coefficients of
`J (∇φ)` are `grad_ξ` of those of `J φ`. -/
theorem grad_J0_testField {φ : Fin 3 → (Fin 3 → ℝ) → ℝ} (hφ : Domain.IsTestField (Q (Fin 3)) φ)
    (n : Fin 3 → ℤ) :
    grad (Fourier.Torus.freq n) (cv (J0 (Domain.testField hφ)) n) =
      c1 (J1 (Domain.testField
        ((Domain.gradOp 3 3 : Domain.ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).isTestField_apply hφ))) n := by
  ext ⟨a, b⟩
  rw [grad_apply, cv_J0, c1_J1, Domain.testField_apply, Domain.testField_apply,
    mFourierCoeff_X_toL2, mFourierCoeff_X_toL2]
  have e : (fun y =>
      (((Domain.gradOp 3 3 : Domain.ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).apply φ (a, b) y : ℝ)
      : ℂ)) = fun y => ((fderiv ℝ (φ a) y (Pi.single b 1) : ℝ) : ℂ) := by
    funext y; rw [Domain.gradOp_apply]
  rw [e, ← update_pv, mFourierCoeff_ext_partial _ (hφ a), Fourier.Torus.freq_apply]
  push_cast; ring

/-- **The extension intertwines the curls of test fields** (Fourier side). -/
theorem curl_J1_testField {φ : Ix → (Fin 3 → ℝ) → ℝ} (hφ : Domain.IsTestField (Q (Fin 3)) φ)
    (n : Fin 3 → ℤ) :
    curl (Fourier.Torus.freq n) (c1 (J1 (Domain.testField hφ)) n) =
      c2 (J2 (Domain.testField
        ((Domain.curlOp 3 : Domain.ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).isTestField_apply hφ))) n := by
  ext ⟨a, b⟩
  rw [curl_apply, c2_J2, Domain.testField_apply, mFourierCoeff_X_toL2]
  simp only [c1_J1, Domain.testField_apply, mFourierCoeff_X_toL2]
  have e : (fun y => (((Domain.curlOp 3 : Domain.ConstCoeffOp (Fin 3 → ℝ) ℝ _ _).apply φ (a, b) y :
      ℝ) : ℂ)) = (fun y => ((fderiv ℝ (φ (a, b + 2)) y (Pi.single (b + 1) 1) : ℝ) : ℂ)) -
        fun y => ((fderiv ℝ (φ (a, b + 1)) y (Pi.single (b + 2) 1) : ℝ) : ℂ) := by
    funext y; rw [Domain.curlOp_apply]; push_cast; rfl
  have h1 := mFourierCoeff_ext_partial (pe (a, b + 2)) (hφ (a, b + 2)) (b + 1) n
  have h2 := mFourierCoeff_ext_partial (pe (a, b + 1)) (hφ (a, b + 1)) (b + 2) n
  rw [update_pe_one] at h1
  rw [update_pe_two] at h2
  have hc1 : Continuous (ext (pb (a, b))
      fun y => ((fderiv ℝ (φ (a, b + 2)) y (Pi.single (b + 1) 1) : ℝ) : ℂ)) := by
    rw [← update_pe_one]
    exact Geometry.continuous_ext _ (((hφ (a, b + 2)).fderiv_apply _).ofReal)
  have hc2 : Continuous (ext (pb (a, b))
      fun y => ((fderiv ℝ (φ (a, b + 1)) y (Pi.single (b + 2) 1) : ℝ) : ℂ)) := by
    rw [← update_pe_two]
    exact Geometry.continuous_ext _ (((hφ (a, b + 1)).fderiv_apply _).ofReal)
  rw [e, ext_sub, mFourierCoeff_sub_of_continuous hc1 hc2, h1, h2]
  simp only [Fin.sum_univ_three, leviCivita3_apply, Fourier.Torus.freq_apply]
  fin_cases b <;> simp <;> ring

end TestFields

/-! ### Cut-off functions on `Q` -/

section Cutoff

open Real
open Models.BoundedDomain (R3 Ix pd curlM gradM smoothField)

/-- A bound for the derivative of `Real.smoothTransition`. -/
theorem exists_bound_deriv_smoothTransition :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv smoothTransition x| ≤ M := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases h0 : x < 0
  · have : smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.mem_of_superset (Iio_mem_nhds h0) fun y hy =>
        smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]; simp
  by_cases h1 : 1 < x
  · have : smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
      Filter.mem_of_superset (Ioi_mem_nhds h1) fun y hy =>
        smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]; simp
  push Not at h0 h1
  exact (hC x ⟨h0, h1⟩).trans (le_max_left _ _)

/-- The scale `m = n + 2` of the `n`-th cut-off. -/
def mN (n : ℕ) : ℝ := (n : ℝ) + 2

theorem mN_pos (n : ℕ) : 0 < mN n := by unfold mN; positivity

/-- The one-dimensional cut-off `η_n(t) = s(2mt - 1) s(m - 2mt - 1)`: smooth, `1` on
`[1/m, ½ - 1/m]`, `0` outside `(1/(2m), ½ - 1/(2m))`. -/
def eta (n : ℕ) (t : ℝ) : ℝ :=
  smoothTransition (2 * mN n * t - 1) * smoothTransition (mN n - 2 * mN n * t - 1)

theorem eta_nonneg (n : ℕ) (t : ℝ) : 0 ≤ eta n t :=
  mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _)

theorem eta_le_one (n : ℕ) (t : ℝ) : eta n t ≤ 1 :=
  calc eta n t ≤ 1 * 1 := mul_le_mul (smoothTransition.le_one _) (smoothTransition.le_one _)
        (smoothTransition.nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem abs_eta_le_one (n : ℕ) (t : ℝ) : |eta n t| ≤ 1 := by
  rw [abs_of_nonneg (eta_nonneg n t)]; exact eta_le_one n t

theorem contDiff_eta (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (eta n) := by
  unfold eta
  exact (smoothTransition.contDiff.comp (by fun_prop)).mul
    (smoothTransition.contDiff.comp (by fun_prop))

theorem eta_eq_zero_of_ne {n : ℕ} {t : ℝ} (h : eta n t ≠ 0) :
    1 / (2 * mN n) < t ∧ t < 1 / 2 - 1 / (2 * mN n) := by
  have hm := mN_pos n
  unfold eta at h
  have h1 : smoothTransition (2 * mN n * t - 1) ≠ 0 := left_ne_zero_of_mul h
  have h2 : smoothTransition (mN n - 2 * mN n * t - 1) ≠ 0 := right_ne_zero_of_mul h
  rw [Ne, smoothTransition.zero_iff_nonpos, not_le] at h1 h2
  constructor
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · have : 1 / (2 * mN n) = (1 / 2) * (1 / mN n) := by field_simp
    rw [this]
    have h4 : t < 1 / 2 - 1 / 2 * (1 / mN n) := by
      have := (lt_div_iff₀ hm).2 (by linarith : t * mN n < mN n / 2 - 1 / 2)
      calc t < (mN n / 2 - 1 / 2) / mN n := this
        _ = 1 / 2 - 1 / 2 * (1 / mN n) := by field_simp
    exact h4

theorem eta_eq_one {n : ℕ} {t : ℝ} (h1 : 1 / mN n ≤ t) (h2 : t ≤ 1 / 2 - 1 / mN n) :
    eta n t = 1 := by
  have hm := mN_pos n
  unfold eta
  rw [smoothTransition.one_of_one_le, smoothTransition.one_of_one_le, one_mul]
  · have : mN n * t ≤ mN n * (1 / 2 - 1 / mN n) := mul_le_mul_of_nonneg_left h2 hm.le
    have e : mN n * (1 / 2 - 1 / mN n) = mN n / 2 - 1 := by field_simp
    linarith
  · have : mN n * (1 / mN n) ≤ mN n * t := mul_le_mul_of_nonneg_left h1 hm.le
    rw [mul_one_div_cancel hm.ne'] at this
    linarith

theorem hasDerivAt_eta (n : ℕ) (t : ℝ) :
    HasDerivAt (eta n) (deriv smoothTransition (2 * mN n * t - 1) * (2 * mN n) *
        smoothTransition (mN n - 2 * mN n * t - 1) +
      smoothTransition (2 * mN n * t - 1) *
        (deriv smoothTransition (mN n - 2 * mN n * t - 1) * (-(2 * mN n)))) t := by
  have hs : ∀ x, HasDerivAt smoothTransition (deriv smoothTransition x) x := fun x =>
    ((smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have h1 : HasDerivAt (fun t => 2 * mN n * t - 1) (2 * mN n) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * mN n)).sub_const 1
  have h2 : HasDerivAt (fun t => mN n - 2 * mN n * t - 1) (-(2 * mN n)) t := by
    simpa using (((hasDerivAt_id t).const_mul (2 * mN n)).const_sub (mN n)).sub_const 1
  exact ((hs _).comp t h1).mul ((hs _).comp t h2)

theorem abs_deriv_eta_le {M : ℝ} (hM : ∀ x, |deriv smoothTransition x| ≤ M) (n : ℕ) (t : ℝ) :
    |deriv (eta n) t| ≤ 4 * mN n * M := by
  have hm := mN_pos n
  rw [(hasDerivAt_eta n t).deriv]
  have a1 := hM (2 * mN n * t - 1)
  have a2 := hM (mN n - 2 * mN n * t - 1)
  have b1 := smoothTransition.nonneg (2 * mN n * t - 1)
  have b2 := smoothTransition.le_one (2 * mN n * t - 1)
  have b3 := smoothTransition.nonneg (mN n - 2 * mN n * t - 1)
  have b4 := smoothTransition.le_one (mN n - 2 * mN n * t - 1)
  have h2m : 0 < 2 * mN n := by positivity
  have hM0 : 0 ≤ M := (abs_nonneg _).trans a1
  have e1 : |deriv smoothTransition (2 * mN n * t - 1) * (2 * mN n) *
      smoothTransition (mN n - 2 * mN n * t - 1)| ≤ M * (2 * mN n) := by
    rw [abs_mul, abs_mul, abs_of_nonneg b3, abs_of_pos h2m]
    calc |deriv smoothTransition (2 * mN n * t - 1)| * (2 * mN n) *
          smoothTransition (mN n - 2 * mN n * t - 1) ≤ M * (2 * mN n) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right a1 h2m.le) b4 b3 (mul_nonneg hM0 h2m.le)
      _ = M * (2 * mN n) := mul_one _
  have e2 : |smoothTransition (2 * mN n * t - 1) *
      (deriv smoothTransition (mN n - 2 * mN n * t - 1) * (-(2 * mN n)))| ≤ M * (2 * mN n) := by
    rw [abs_mul, abs_mul, abs_of_nonneg b1, abs_neg, abs_of_pos h2m]
    calc smoothTransition (2 * mN n * t - 1) *
          (|deriv smoothTransition (mN n - 2 * mN n * t - 1)| * (2 * mN n)) ≤
          1 * (M * (2 * mN n)) :=
          mul_le_mul b2 (mul_le_mul_of_nonneg_right a2 h2m.le) (by positivity) zero_le_one
      _ = M * (2 * mN n) := one_mul _
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ M * (2 * mN n) + M * (2 * mN n) := add_le_add e1 e2
    _ = 4 * mN n * M := by ring

theorem deriv_eta_eq_zero {n : ℕ} {t : ℝ} (h1 : 1 / mN n < t) (h2 : t < 1 / 2 - 1 / mN n) :
    deriv (eta n) t = 0 := by
  have : eta n =ᶠ[𝓝 t] fun _ => 1 :=
    Filter.mem_of_superset (Ioo_mem_nhds h1 h2) fun s hs => eta_eq_one hs.1.le hs.2.le
  rw [this.deriv_eq, deriv_const]

/-- `|η_n'(t)| · min(t, ½ - t) ≤ 4M` on `(0, ½)`: the cut-off derivative is large only in a layer
of width `1/m`. -/
theorem abs_deriv_eta_mul_le {M : ℝ} (hM : ∀ x, |deriv smoothTransition x| ≤ M) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    |deriv (eta n) t| * min t (1 / 2 - t) ≤ 4 * M := by
  have hm := mN_pos n
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hmin0 : 0 ≤ min t (1 / 2 - t) := le_min ht.1.le (by linarith [ht.2])
  by_cases hc : 1 / mN n < t ∧ t < 1 / 2 - 1 / mN n
  · rw [deriv_eta_eq_zero hc.1 hc.2]; simp; positivity
  · have hmin : min t (1 / 2 - t) ≤ 1 / mN n := by
      rcases not_and_or.1 hc with h | h
      · exact (min_le_left _ _).trans (not_lt.1 h)
      · exact (min_le_right _ _).trans (by linarith [not_lt.1 h])
    calc |deriv (eta n) t| * min t (1 / 2 - t) ≤ (4 * mN n * M) * (1 / mN n) :=
          mul_le_mul (abs_deriv_eta_le hM n t) hmin hmin0 (by positivity)
      _ = 4 * M := by field_simp

/-- The cut-off on `Q`: `χ_n(y) = η_n(y₀) η_n(y₁) η_n(y₂)`. -/
def chi (n : ℕ) (y : R3) : ℝ := eta n (y 0) * eta n (y 1) * eta n (y 2)

theorem contDiff_chi (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (chi n) := by
  unfold chi
  have h := contDiff_eta n
  have hc : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) fun y : R3 => y i := fun i => by fun_prop
  exact ((h.comp (hc 0)).mul (h.comp (hc 1))).mul (h.comp (hc 2))

theorem abs_chi_le_one (n : ℕ) (y : R3) : |chi n y| ≤ 1 := by
  unfold chi
  rw [abs_mul, abs_mul]
  have := abs_eta_le_one n
  calc |eta n (y 0)| * |eta n (y 1)| * |eta n (y 2)| ≤ 1 * 1 * 1 := by
        gcongr <;> exact this _
    _ = 1 := by norm_num

/-- The closed box `[1/(2m), ½ - 1/(2m)]³` containing the support of `χ_n`. -/
def chiBox (n : ℕ) : Set R3 := univ.pi fun _ => Icc (1 / (2 * mN n)) (1 / 2 - 1 / (2 * mN n))

theorem support_chi_subset (n : ℕ) : Function.support (chi n) ⊆ chiBox n := by
  intro y hy i _
  have h : chi n y ≠ 0 := hy
  unfold chi at h
  have h0 : eta n (y 0) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h)
  have h1 : eta n (y 1) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have h2 : eta n (y 2) ≠ 0 := right_ne_zero_of_mul h
  fin_cases i
  · exact ⟨(eta_eq_zero_of_ne h0).1.le, (eta_eq_zero_of_ne h0).2.le⟩
  · exact ⟨(eta_eq_zero_of_ne h1).1.le, (eta_eq_zero_of_ne h1).2.le⟩
  · exact ⟨(eta_eq_zero_of_ne h2).1.le, (eta_eq_zero_of_ne h2).2.le⟩

theorem isCompact_chiBox (n : ℕ) : IsCompact (chiBox n) := isCompact_univ_pi fun _ => isCompact_Icc

theorem chiBox_subset_Q (n : ℕ) : chiBox n ⊆ Q (Fin 3) := by
  intro y hy
  refine Geometry.mem_Q.2 fun i => ?_
  have hm := mN_pos n
  have h := hy i (mem_univ i)
  have hp : 0 < 1 / (2 * mN n) := by positivity
  exact ⟨hp.trans_le h.1, h.2.trans_lt (by linarith)⟩

/-- `χ_n f` is a test function on `Q` for every smooth `f`. -/
theorem isTest_chi_mul {f : R3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    Domain.IsTest (Q (Fin 3)) (fun y => chi n y * f y) := by
  have hsub : Function.support (fun y => chi n y * f y) ⊆ chiBox n :=
    (Function.support_mul_subset_left _ _).trans (support_chi_subset n)
  refine ⟨((contDiff_chi n).mul hf).of_le (by exact_mod_cast le_top), ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_chiBox n) fun y hy =>
      Function.notMem_support.1 fun h => hy (hsub h)
  · exact (closure_minimal hsub (isCompact_chiBox n).isClosed).trans (chiBox_subset_Q n)

/-- **Near each point of `Q`, `χ_n = 1` for all large `n`.** -/
theorem eventually_chi_eq_one {y : R3} (hy : y ∈ Q (Fin 3)) :
    ∀ᶠ n in atTop, chi n =ᶠ[𝓝 y] fun _ => 1 := by
  have hy' := Geometry.mem_Q.1 hy
  have hpos : ∀ i, 0 < min (y i) (1 / 2 - y i) := fun i =>
    lt_min (hy' i).1 (by linarith [(hy' i).2])
  set δ := min (min (y 0) (1 / 2 - y 0)) (min (min (y 1) (1 / 2 - y 1)) (min (y 2) (1 / 2 - y 2)))
  have hδ : 0 < δ := lt_min (hpos 0) (lt_min (hpos 1) (hpos 2))
  have hδi : ∀ i, δ ≤ min (y i) (1 / 2 - y i) := by
    intro i; fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hm : 2 / δ < mN n := by
    unfold mN; linarith [show (N : ℝ) ≤ n from Nat.cast_le.2 hn]
  have hmδ : 1 / mN n < δ / 2 := by
    rw [div_lt_iff₀ (mN_pos n)]
    rw [div_lt_iff₀ hδ] at hm
    linarith
  filter_upwards [Metric.ball_mem_nhds y (by linarith : (0 : ℝ) < δ / 2)] with z hz
  rw [Metric.mem_ball] at hz
  have hzi : ∀ i, 1 / mN n ≤ z i ∧ z i ≤ 1 / 2 - 1 / mN n := by
    intro i
    have hd : |z i - y i| < δ / 2 := by
      have := (dist_le_pi_dist z y i).trans_lt hz
      rwa [Real.dist_eq] at this
    rw [abs_lt] at hd
    have h1 := (hδi i).trans (min_le_left _ _)
    have h2 := (hδi i).trans (min_le_right _ _)
    constructor <;> linarith
  simp only [chi]
  rw [eta_eq_one (hzi 0).1 (hzi 0).2, eta_eq_one (hzi 1).1 (hzi 1).2,
    eta_eq_one (hzi 2).1 (hzi 2).2]
  norm_num

/-- `x + t e_k = x + t • e_k`. -/
theorem single_eq_smul (k : Fin 3) (t : ℝ) : (Pi.single k t : R3) = t • Pi.single k (1 : ℝ) := by
  funext j; by_cases h : j = k
  · subst h; simp
  · simp [h]

/-- Line derivative: `d/dt f(x + t e_k) = ∂_k f (x + t e_k)`. -/
theorem hasDerivAt_line {f : R3 → ℝ} (hf : Differentiable ℝ f) (x : R3) (k : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => f (x + Pi.single k s)) (pd k f (x + Pi.single k t)) t := by
  have hl : HasDerivAt (fun s : ℝ => x + Pi.single k s) (Pi.single k 1) t := by
    have : (fun s : ℝ => x + Pi.single k s) = fun s => x + s • (Pi.single k (1 : ℝ) : R3) := by
      funext s; rw [single_eq_smul k s]
    rw [this]
    simpa using ((hasDerivAt_id t).smul_const (Pi.single k (1 : ℝ) : R3)).const_add x
  exact (hf _).hasFDerivAt.comp_hasDerivAt t hl

/-- `∂_k f = d/dt f(x + t e_k)|₀`. -/
theorem pd_eq_deriv {f : R3 → ℝ} {x : R3} (hf : DifferentiableAt ℝ f x) (k : Fin 3) :
    pd k f x = deriv (fun t => f (x + Pi.single k t)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + Pi.single k t) (Pi.single k 1) 0 := by
    have : (fun t : ℝ => x + Pi.single k t) = fun t => x + t • (Pi.single k (1 : ℝ) : R3) := by
      funext t; rw [single_eq_smul k t]
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k (1 : ℝ) : R3)).const_add x
  have h := (show HasFDerivAt f (fderiv ℝ f x) (x + Pi.single k 0) by
    simpa using hf.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hl
  exact h.deriv.symm

/-- **The derivative of the cut-off**: `|∂_c χ_n(y)| ≤ |η_n'(y_c)|`. -/
theorem abs_pd_chi_le (n : ℕ) (c : Fin 3) (y : R3) :
    |pd c (chi n) y| ≤ |deriv (eta n) (y c)| := by
  have hd : ∀ s, HasDerivAt (eta n) (deriv (eta n) s) s := fun s =>
    ((contDiff_eta n).differentiable (by simp) s).hasDerivAt
  rw [pd_eq_deriv ((contDiff_chi n).differentiable (by simp) y)]
  have hb := abs_eta_le_one n
  obtain rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
  · have h : HasDerivAt (fun t => chi n (y + Pi.single 0 t))
        (deriv (eta n) (y 0) * eta n (y 1) * eta n (y 2)) 0 := by
      have e : (fun t => chi n (y + Pi.single 0 t)) =
          fun t => eta n (y 0 + t) * eta n (y 1) * eta n (y 2) := by
        funext t; simp [chi]
      rw [e]
      have := ((hd (y 0 + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (y 0)))
      simp only [add_zero, mul_one] at this
      exact (this.mul_const _).mul_const _
    rw [h.deriv, abs_mul, abs_mul]
    calc |deriv (eta n) (y 0)| * |eta n (y 1)| * |eta n (y 2)| ≤
          |deriv (eta n) (y 0)| * 1 * 1 := by gcongr <;> exact hb _
      _ = _ := by simp
  · have h : HasDerivAt (fun t => chi n (y + Pi.single 1 t))
        (eta n (y 0) * deriv (eta n) (y 1) * eta n (y 2)) 0 := by
      have e : (fun t => chi n (y + Pi.single 1 t)) =
          fun t => eta n (y 0) * eta n (y 1 + t) * eta n (y 2) := by
        funext t; simp [chi]
      rw [e]
      have := ((hd (y 1 + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (y 1)))
      simp only [add_zero, mul_one] at this
      exact (this.const_mul _).mul_const _
    rw [h.deriv, abs_mul, abs_mul]
    calc |eta n (y 0)| * |deriv (eta n) (y 1)| * |eta n (y 2)| ≤
          1 * |deriv (eta n) (y 1)| * 1 := by gcongr <;> exact hb _
      _ = _ := by simp
  · have h : HasDerivAt (fun t => chi n (y + Pi.single 2 t))
        (eta n (y 0) * eta n (y 1) * deriv (eta n) (y 2)) 0 := by
      have e : (fun t => chi n (y + Pi.single 2 t)) =
          fun t => eta n (y 0) * eta n (y 1) * eta n (y 2 + t) := by
        funext t; simp [chi]
      rw [e]
      have := ((hd (y 2 + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (y 2)))
      simp only [add_zero, mul_one] at this
      exact this.const_mul _
    rw [h.deriv, abs_mul, abs_mul]
    calc |eta n (y 0)| * |eta n (y 1)| * |deriv (eta n) (y 2)| ≤
          1 * 1 * |deriv (eta n) (y 2)| := by gcongr <;> exact hb _
      _ = _ := by simp

/-! ### Approximation by cut-offs: smooth fields with vanishing tangential traces -/

theorem isBounded_Q : Bornology.IsBounded (Q (Fin 3)) := Geometry.isBounded_openCube _ _

/-- **Vanishing on two opposite faces with a bounded normal derivative**: if `f = 0` on
`{y_c = 0}` and `{y_c = ½}` and `|∂_c f| ≤ L`, then `|f(y)| ≤ L min(y_c, ½ - y_c)` on `Q`. -/
theorem abs_le_of_faces {f : R3 → ℝ} (hf : Differentiable ℝ f) {c : Fin 3} {L : ℝ}
    (hL : ∀ y, |pd c f y| ≤ L) (h0 : ∀ y : R3, y c = 0 → f y = 0)
    (h1 : ∀ y : R3, y c = 1 / 2 → f y = 0) {y : R3} (hy : y ∈ Q (Fin 3)) :
    |f y| ≤ L * min (y c) (1 / 2 - y c) := by
  set g : ℝ → ℝ := fun s => f (y + Pi.single c s)
  have hg : ∀ s, HasDerivAt g (pd c f (y + Pi.single c s)) s := hasDerivAt_line hf y c
  have hb : ∀ s ∈ (univ : Set ℝ), ‖deriv g s‖ ≤ L := fun s _ => by
    rw [(hg s).deriv, Real.norm_eq_abs]; exact hL _
  have hd : ∀ s ∈ (univ : Set ℝ), DifferentiableAt ℝ g s := fun s _ => (hg s).differentiableAt
  have hyc := Geometry.mem_Q.1 hy c
  have e0 : g 0 = f y := by simp [g]
  have ea : g (-y c) = 0 := h0 _ (by simp)
  have eb : g (1 / 2 - y c) = 0 := h1 _ (by simp)
  have m1 := convex_univ.norm_image_sub_le_of_norm_deriv_le hd hb (mem_univ (-y c)) (mem_univ 0)
  have m2 := convex_univ.norm_image_sub_le_of_norm_deriv_le hd hb (mem_univ 0)
    (mem_univ (1 / 2 - y c))
  rw [e0, ea, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, zero_sub, neg_neg,
    abs_of_pos hyc.1] at m1
  rw [e0, eb, zero_sub, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs, sub_zero,
    abs_of_pos (by linarith [hyc.2] : 0 < 1 / 2 - y c)] at m2
  rcases le_total (y c) (1 / 2 - y c) with h | h
  · rw [min_eq_left h]; exact m1
  · rw [min_eq_right h]; exact m2

/-- **`L²(Q)`-convergence of uniformly bounded, pointwise convergent sequences.** -/
theorem tendsto_toLp_of_bdd {g : ℕ → R3 → ℝ} {h : R3 → ℝ}
    (hg : ∀ n, MemLp (g n) 2 (volume.restrict (Q (Fin 3))))
    (hh : MemLp h 2 (volume.restrict (Q (Fin 3)))) {K : ℝ}
    (hK : ∀ n, ∀ y ∈ Q (Fin 3), |g n y| ≤ K)
    (hlim : ∀ y ∈ Q (Fin 3), Tendsto (fun n => g n y) atTop (𝓝 (h y))) :
    Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hh.toLp h)) := by
  have : IsFiniteMeasure (volume.restrict (Q (Fin 3))) :=
    isFiniteMeasure_restrict.2 isBounded_Q.measure_lt_top.ne
  rw [tendsto_iff_edist_tendsto_0]
  simp_rw [Lp.edist_toLp_toLp]
  have hui : UnifIntegrable g 2 (volume.restrict (Q (Fin 3))) := by
    refine (unifIntegrable_const (ι := ℕ) one_le_two (by norm_num)
      (memLp_const (μ := volume.restrict (Q (Fin 3))) K)).ae_mono
      (fun n => (hg n).aestronglyMeasurable) fun n => ?_
    filter_upwards [ae_restrict_mem Geometry.measurableSet_Q] with y hy
    rw [enorm_le_iff_norm_le, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hK n y hy).trans (le_abs_self K)
  exact tendsto_Lp_finite_of_tendsto_ae one_le_two (by norm_num)
    (fun n => (hg n).aestronglyMeasurable) hh hui
    (by filter_upwards [ae_restrict_mem Geometry.measurableSet_Q] with y hy; exact hlim y hy)

/-- Convergence in `L²(Q; ℝ^ι)` is componentwise. -/
theorem tendsto_L2F_of_forall {ι : Type*} {u : ℕ → Domain.L2F ℝ (Q (Fin 3)) ι}
    {v : Domain.L2F ℝ (Q (Fin 3)) ι} (h : ∀ p, Tendsto (fun n => u n p) atTop (𝓝 (v p))) :
    Tendsto u atTop (𝓝 v) := by
  have hc := (PiLp.continuous_toLp 2 (fun _ : ι => Domain.L2 ℝ (Q (Fin 3)))).tendsto
    (WithLp.ofLp v)
  exact hc.comp (tendsto_pi_nhds.2 h)

/-- **Cut-off approximation in `H(curl)`**: a smooth matrix field on `ℝ³`, bounded with bounded
first derivatives, whose tangential components vanish on the faces of `Q`
(`ψ_{ad} = 0` on `{y_c ∈ {0, ½}}` for `c ≠ d`), restricts to an element of `H̊(curl, Q)`:
`(ψ, curl ψ)` lies in the closure of the curl on `C_c^∞(Q; ℝ³ˣ³)`. The approximants are `χ_n ψ`;
the commutator `∇χ_n × ψ` stays bounded because `ψ_tan = O(dist to the face)`, and converges to
`0` pointwise in `Q`. -/
theorem mem_closure_curl_of_smooth {ψ : Ix → R3 → ℝ}
    (hψ : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (ψ p)) {M L : ℝ} (hM : ∀ p y, |ψ p y| ≤ M)
    (hMc : ∀ p y, |curlM ψ p y| ≤ M) (hL : ∀ p c y, |pd c (ψ p) y| ≤ L)
    (hV : ∀ a c d, c ≠ d → ∀ y : R3, (y c = 0 ∨ y c = 1 / 2) → ψ (a, d) y = 0) :
    (smoothField Geometry.isOpen_Q isBounded_Q ψ fun p => (hψ p).continuous,
      smoothField Geometry.isOpen_Q isBounded_Q (curlM ψ)
        fun p => Models.BoundedDomain.continuous_curlM (fun q => (hψ q).of_le (by simp)) p) ∈
      closure ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).testGraph (Q (Fin 3)) :
        Set (Domain.L2F ℝ (Q (Fin 3)) Ix × Domain.L2F ℝ (Q (Fin 3)) Ix)) := by
  obtain ⟨M₀, hM₀, hM₀b⟩ := exists_bound_deriv_smoothTransition
  set Φ : ℕ → Ix → R3 → ℝ := fun n p y => chi n y * ψ p y
  have hΦ : ∀ n, Domain.IsTestField (Q (Fin 3)) (Φ n) := fun n p => isTest_chi_mul (hψ p) n
  have hdiff : ∀ p, Differentiable ℝ (ψ p) := fun p => (hψ p).differentiable (by simp)
  have hchid : ∀ n, Differentiable ℝ (chi n) := fun n => (contDiff_chi n).differentiable (by simp)
  have hev : ∀ y ∈ Q (Fin 3), ∀ᶠ n in atTop, ∀ p, (Φ n p) =ᶠ[𝓝 y] ψ p := fun y hy => by
    filter_upwards [eventually_chi_eq_one hy] with n hn p
    filter_upwards [hn] with z hz
    simp [Φ, hz]
  have hface : ∀ a c d, c ≠ d → ∀ y ∈ Q (Fin 3), |ψ (a, d) y| ≤ L * min (y c) (1 / 2 - y c) :=
    fun a c d hcd y hy => abs_le_of_faces (hdiff _) (hL _ c)
      (fun z hz => hV a c d hcd z (Or.inl hz))
      (fun z hz => hV a c d hcd z (Or.inr hz)) hy
  have hcross : ∀ n a c d, c ≠ d → ∀ y ∈ Q (Fin 3),
      |pd c (chi n) y * ψ (a, d) y| ≤ 4 * M₀ * L := by
    intro n a c d hcd y hy
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL (a, d) c y)
    rw [abs_mul]
    calc |pd c (chi n) y| * |ψ (a, d) y| ≤
          |deriv (eta n) (y c)| * (L * min (y c) (1 / 2 - y c)) :=
          mul_le_mul (abs_pd_chi_le n c y) (hface a c d hcd y hy) (abs_nonneg _) (abs_nonneg _)
      _ = L * (|deriv (eta n) (y c)| * min (y c) (1 / 2 - y c)) := by ring
      _ ≤ L * (4 * M₀) :=
          mul_le_mul_of_nonneg_left (abs_deriv_eta_mul_le hM₀b n (Geometry.mem_Q.1 hy c)) hL0
      _ = 4 * M₀ * L := by ring
  have hcurlΦ : ∀ n a b y, curlM (Φ n) (a, b) y = chi n y * curlM ψ (a, b) y +
      (pd (b + 1) (chi n) y * ψ (a, b + 2) y - pd (b + 2) (chi n) y * ψ (a, b + 1) y) := by
    intro n a b y
    simp only [curlM, Φ, Models.BoundedDomain.pd_mul (hchid n y) (hdiff _ y)]
    ring
  have happ : ∀ n, (Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).apply (Φ n) = curlM (Φ n) :=
    fun n => (Models.BoundedDomain.curlM_eq_apply (Φ n)).symm
  refine mem_closure_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun n => (Domain.testField (hΦ n),
      Domain.testField ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply
        (hΦ n)))) ?_ (Filter.Eventually.of_forall fun n => ⟨Φ n, hΦ n, rfl⟩)
  refine Tendsto.prodMk_nhds (tendsto_L2F_of_forall fun p => ?_)
    (tendsto_L2F_of_forall fun p => ?_)
  · refine tendsto_toLp_of_bdd (fun n => (hΦ n p).memLp)
      (Domain.memLp_of_continuous Geometry.measurableSet_Q isBounded_Q (hψ p).continuous) (K := M)
      (fun n y _ => ?_) fun y hy => ?_
    · simp only [Φ, abs_mul]
      calc |chi n y| * |ψ p y| ≤ 1 * M :=
            mul_le_mul (abs_chi_le_one n y) (hM p y) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with n hn
      exact (hn p).eq_of_nhds.symm
  · obtain ⟨a, b⟩ := p
    refine tendsto_toLp_of_bdd
      (fun n => ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply
        (hΦ n) (a, b)).memLp)
      (Domain.memLp_of_continuous Geometry.measurableSet_Q isBounded_Q
        (Models.BoundedDomain.continuous_curlM (fun q => (hψ q).of_le (by simp)) (a, b)))
      (K := M + 2 * (4 * M₀ * L)) (fun n y hy => ?_) fun y hy => ?_
    · rw [happ, hcurlΦ]
      have h1 : |chi n y * curlM ψ (a, b) y| ≤ M := by
        rw [abs_mul]
        calc |chi n y| * |curlM ψ (a, b) y| ≤ 1 * M :=
              mul_le_mul (abs_chi_le_one n y) (hMc _ y) (abs_nonneg _) zero_le_one
          _ = M := one_mul M
      have h2 := hcross n a (b + 1) (b + 2) (by fin_cases b <;> decide) y hy
      have h3 := hcross n a (b + 2) (b + 1) (by fin_cases b <;> decide) y hy
      calc _ ≤ |chi n y * curlM ψ (a, b) y| +
            |pd (b + 1) (chi n) y * ψ (a, b + 2) y - pd (b + 2) (chi n) y * ψ (a, b + 1) y| :=
            abs_add_le _ _
        _ ≤ M + (4 * M₀ * L + 4 * M₀ * L) := add_le_add h1 ((abs_sub _ _).trans (add_le_add h2 h3))
        _ = M + 2 * (4 * M₀ * L) := by ring
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with n hn
      rw [happ]
      simp only [curlM, Models.BoundedDomain.pd]
      rw [(hn _).fderiv_eq, (hn _).fderiv_eq]

/-- **Cut-off approximation in `H¹`**: a smooth vector field on `ℝ³`, bounded with bounded first
derivatives, vanishing on all faces of `Q`, restricts to an element of `H̊¹(Q; ℝ³)`. -/
theorem mem_closure_grad_of_smooth {σ : Fin 3 → R3 → ℝ}
    (hσ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (σ a)) {M L : ℝ} (hM : ∀ a y, |σ a y| ≤ M)
    (hL : ∀ a c y, |pd c (σ a) y| ≤ L)
    (hV : ∀ a c, ∀ y : R3, (y c = 0 ∨ y c = 1 / 2) → σ a y = 0) :
    (smoothField Geometry.isOpen_Q isBounded_Q σ fun a => (hσ a).continuous,
      smoothField Geometry.isOpen_Q isBounded_Q (gradM σ)
        fun p => Models.BoundedDomain.continuous_pd ((hσ p.1).of_le (by simp)) p.2) ∈
      closure ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).testGraph (Q (Fin 3)) :
        Set (Domain.L2F ℝ (Q (Fin 3)) (Fin 3) × Domain.L2F ℝ (Q (Fin 3)) Ix)) := by
  obtain ⟨M₀, hM₀, hM₀b⟩ := exists_bound_deriv_smoothTransition
  set φ : ℕ → Fin 3 → R3 → ℝ := fun n a y => chi n y * σ a y
  have hφ : ∀ n, Domain.IsTestField (Q (Fin 3)) (φ n) := fun n a => isTest_chi_mul (hσ a) n
  have hdiff : ∀ a, Differentiable ℝ (σ a) := fun a => (hσ a).differentiable (by simp)
  have hchid : ∀ n, Differentiable ℝ (chi n) := fun n => (contDiff_chi n).differentiable (by simp)
  have hev : ∀ y ∈ Q (Fin 3), ∀ᶠ n in atTop, ∀ a, (φ n a) =ᶠ[𝓝 y] σ a := fun y hy => by
    filter_upwards [eventually_chi_eq_one hy] with n hn a
    filter_upwards [hn] with z hz
    simp [φ, hz]
  have hface : ∀ a c, ∀ y ∈ Q (Fin 3), |σ a y| ≤ L * min (y c) (1 / 2 - y c) :=
    fun a c y hy => abs_le_of_faces (hdiff _) (hL _ c) (fun z hz => hV a c z (Or.inl hz))
      (fun z hz => hV a c z (Or.inr hz)) hy
  have hcross : ∀ n a c, ∀ y ∈ Q (Fin 3), |pd c (chi n) y * σ a y| ≤ 4 * M₀ * L := by
    intro n a c y hy
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL a c y)
    rw [abs_mul]
    calc |pd c (chi n) y| * |σ a y| ≤
          |deriv (eta n) (y c)| * (L * min (y c) (1 / 2 - y c)) :=
          mul_le_mul (abs_pd_chi_le n c y) (hface a c y hy) (abs_nonneg _) (abs_nonneg _)
      _ = L * (|deriv (eta n) (y c)| * min (y c) (1 / 2 - y c)) := by ring
      _ ≤ L * (4 * M₀) :=
          mul_le_mul_of_nonneg_left (abs_deriv_eta_mul_le hM₀b n (Geometry.mem_Q.1 hy c)) hL0
      _ = 4 * M₀ * L := by ring
  have happ : ∀ n p y, (Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).apply (φ n) p y =
      pd p.2 (φ n p.1) y := fun n p y => Domain.gradOp_apply _ _ _
  refine mem_closure_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun n => (Domain.testField (hφ n),
      Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).isTestField_apply
        (hφ n)))) ?_ (Filter.Eventually.of_forall fun n => ⟨φ n, hφ n, rfl⟩)
  refine Tendsto.prodMk_nhds (tendsto_L2F_of_forall fun a => ?_)
    (tendsto_L2F_of_forall fun p => ?_)
  · refine tendsto_toLp_of_bdd (fun n => (hφ n a).memLp)
      (Domain.memLp_of_continuous Geometry.measurableSet_Q isBounded_Q (hσ a).continuous) (K := M)
      (fun n y _ => ?_) fun y hy => ?_
    · simp only [φ, abs_mul]
      calc |chi n y| * |σ a y| ≤ 1 * M :=
            mul_le_mul (abs_chi_le_one n y) (hM a y) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with n hn
      exact (hn a).eq_of_nhds.symm
  · obtain ⟨a, b⟩ := p
    refine tendsto_toLp_of_bdd (fun n => ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix
        ).isTestField_apply (hφ n) (a, b)).memLp)
      (Domain.memLp_of_continuous Geometry.measurableSet_Q isBounded_Q
        (Models.BoundedDomain.continuous_pd ((hσ a).of_le (by simp)) b))
      (K := 4 * M₀ * L + L) (fun n y hy => ?_) fun y hy => ?_
    · rw [happ]
      simp only [φ, Models.BoundedDomain.pd_mul (hchid n y) (hdiff _ y)]
      have h2 : |chi n y * pd b (σ a) y| ≤ L := by
        rw [abs_mul]
        calc |chi n y| * |pd b (σ a) y| ≤ 1 * L :=
              mul_le_mul (abs_chi_le_one n y) (hL a b y) (abs_nonneg _) zero_le_one
          _ = L := one_mul L
      have h3 := hcross n a b y hy
      rw [mul_comm (σ a y)]
      exact (abs_add_le _ _).trans (by linarith)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with n hn
      rw [happ]
      simp only [Models.BoundedDomain.pd]
      rw [(hn _).fderiv_eq]

end Cutoff

/-! ### The extension maps the minimal domains into the torus domains -/

section Graphs

open Fourier.GradCurl
open Models.BoundedDomain (R3 Ix)

/-- A field whose image under a torus symbol is (pointwise) an `L²` field is in the domain, with
that image. -/
theorem mem_domain_real_of_pointwise {i j : Fin 3} {x : Space i} {y : Space j}
    (h : ∀ n, gradCurl.m i j (Fourier.Torus.freq n) ((x : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n) =
      (y : (Fin 3 → ℤ) → W3 Vec Mat Mat j) n) :
    ∃ hx : x ∈ (RealTorus.gradCurl.d i j).domain, RealTorus.gradCurl.d i j ⟨x, hx⟩ = y := by
  have hm : x ∈ ((Fourier.Torus.symbolComplex gradCurl).toHilbertComplex.d i j).domain :=
    (Fourier.SymbolComplex.mem_domain_d_iff _).2
      ((Lp.memLp y).ae_eq (Filter.Eventually.of_forall fun n => (h n).symm))
  refine ⟨hm, ?_⟩
  exact (Operator.mulOp_apply_eq_iff (μ := (Measure.count : Measure (Fin 3 → ℤ)))
    (m := fun n => gradCurl.m i j (Fourier.Torus.freq n)) ⟨x, hm⟩ y).2
    (Filter.Eventually.of_forall h)

/-- The torus gradient of the extension of a test field is the extension of its gradient. -/
theorem J0_testField_mem {φ : Fin 3 → R3 → ℝ} (hφ : Domain.IsTestField (Q (Fin 3)) φ) :
    ∃ h : J0 (Domain.testField hφ) ∈ (RealTorus.gradCurl.d 0 1).domain,
      RealTorus.gradCurl.d 0 1 ⟨_, h⟩ = J1 (Domain.testField
        ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)) :=
  mem_domain_real_of_pointwise fun n => grad_J0_testField hφ n

/-- The torus curl of the extension of a test field is the extension of its curl. -/
theorem J1_testField_mem {φ : Ix → R3 → ℝ} (hφ : Domain.IsTestField (Q (Fin 3)) φ) :
    ∃ h : J1 (Domain.testField hφ) ∈ (RealTorus.gradCurl.d 1 2).domain,
      RealTorus.gradCurl.d 1 2 ⟨_, h⟩ = J2 (Domain.testField
        ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)) :=
  mem_domain_real_of_pointwise fun n => curl_J1_testField hφ n

/-- **The extension maps the closure of the gradient on test fields into the torus graph.** -/
theorem J_mem_graph_grad {p : Domain.L2F ℝ (Q (Fin 3)) (Fin 3) × Domain.L2F ℝ (Q (Fin 3)) Ix}
    (hp : p ∈ closure ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).testGraph
      (Q (Fin 3)) : Set (Domain.L2F ℝ (Q (Fin 3)) (Fin 3) × Domain.L2F ℝ (Q (Fin 3)) Ix))) :
    (J0 p.1, J1 p.2) ∈ (RealTorus.gradCurl.d 0 1).graph := by
  have hc : IsClosed ((fun q : Domain.L2F ℝ (Q (Fin 3)) (Fin 3) × Domain.L2F ℝ (Q (Fin 3)) Ix =>
      (J0 q.1, J1 q.2)) ⁻¹' ((RealTorus.gradCurl.d 0 1).graph : Set (Space 0 × Space 1))) :=
    (RealTorus.gradCurl.closed 0 1).preimage
      ((J0.continuous.comp continuous_fst).prodMk (J1.continuous.comp continuous_snd))
  refine (closure_minimal (fun q hq => ?_) hc) hp
  obtain ⟨φ, hφ, rfl⟩ := hq
  obtain ⟨h, e⟩ := J0_testField_mem hφ
  exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, h⟩, rfl, e⟩

/-- **The extension maps the closure of the curl on test fields into the torus graph.** -/
theorem J_mem_graph_curl {p : Domain.L2F ℝ (Q (Fin 3)) Ix × Domain.L2F ℝ (Q (Fin 3)) Ix}
    (hp : p ∈ closure ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).testGraph
      (Q (Fin 3)) : Set (Domain.L2F ℝ (Q (Fin 3)) Ix × Domain.L2F ℝ (Q (Fin 3)) Ix))) :
    (J1 p.1, J2 p.2) ∈ (RealTorus.gradCurl.d 1 2).graph := by
  have hc : IsClosed ((fun q : Domain.L2F ℝ (Q (Fin 3)) Ix × Domain.L2F ℝ (Q (Fin 3)) Ix =>
      (J1 q.1, J2 q.2)) ⁻¹' ((RealTorus.gradCurl.d 1 2).graph : Set (Space 1 × Space 2))) :=
    (RealTorus.gradCurl.closed 1 2).preimage
      ((J1.continuous.comp continuous_fst).prodMk (J2.continuous.comp continuous_snd))
  refine (closure_minimal (fun q hq => ?_) hc) hp
  obtain ⟨φ, hφ, rfl⟩ := hq
  obtain ⟨h, e⟩ := J1_testField_mem hφ
  exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, h⟩, rfl, e⟩

end Graphs

/-! ### Trigonometric polynomials of the parity classes -/

section Trig

open UnitAddTorus
open TorusWeak (trigPoly partialT)
open Fourier.GradCurl
open Models.BoundedDomain (R3 Ix pd curlM gradM smoothField)
open Geometry (flipB)

/-- The real part of the lift of a function on `𝕋³` to `ℝ³`. -/
def reLift (g : UnitAddTorus (Fin 3) → ℂ) (y : R3) : ℝ := (g (proj y)).re

theorem isSmooth_trigPoly (f : lp (fun _ : Fin 3 → ℤ => ℂ) 2) (S : Finset (Fin 3 → ℤ)) :
    IsSmooth (trigPoly f S) := by
  unfold IsSmooth
  have e : (trigPoly f S : UnitAddTorus (Fin 3) → ℂ) ∘ proj =
      fun y => ∑ k ∈ S, f k * mFourier k (proj y) := by
    funext y
    simp [trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, smul_eq_mul]
  rw [e]
  exact ContDiff.sum fun k _ => contDiff_const.mul (TorusWeak.isSmooth_mFourier k)

theorem contDiff_reLift {g : UnitAddTorus (Fin 3) → ℂ} (hg : IsSmooth g) :
    ContDiff ℝ (⊤ : ℕ∞) (reLift g) :=
  Complex.reCLM.contDiff.comp hg

/-- `∂_c Re(g ∘ proj) = Re((∂_c g) ∘ proj)`. -/
theorem pd_reLift {g : UnitAddTorus (Fin 3) → ℂ} (hg : IsSmooth g) (c : Fin 3) (y : R3) :
    pd c (reLift g) y = (partialT c g (proj y)).re := by
  have hd : Differentiable ℝ (g ∘ proj) := hg.contDiff_one.differentiable one_ne_zero
  rw [TorusWeak.partialT_proj hd]
  unfold pd reLift
  have : HasFDerivAt (fun y => (g (proj y)).re)
      (Complex.reCLM.comp (fderiv ℝ (g ∘ proj) y)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hd y).hasFDerivAt
  rw [this.fderiv]
  rfl

theorem abs_reLift_le (g : C(UnitAddTorus (Fin 3), ℂ)) (y : R3) : |reLift g y| ≤ ‖g‖ :=
  (Complex.abs_re_le_norm _).trans (g.norm_coe_le_norm _)

/-- A smooth function on `𝕋³` has bounded partial derivatives. -/
theorem abs_pd_reLift_le {g : UnitAddTorus (Fin 3) → ℂ} (hg : IsSmooth g) (c : Fin 3) (y : R3) :
    |pd c (reLift g) y| ≤
      ‖(⟨partialT c g, TorusWeak.continuous_partialT hg.contDiff_one c⟩ :
        C(UnitAddTorus (Fin 3), ℂ))‖ := by
  rw [pd_reLift hg]
  exact (Complex.abs_re_le_norm _).trans
    ((⟨partialT c g, TorusWeak.continuous_partialT hg.contDiff_one c⟩ :
      C(UnitAddTorus (Fin 3), ℂ)).norm_coe_le_norm _)

/-- The reflection fixes the faces: if `y_c ∈ {0, ½}` then `R_c (proj y) = proj y`. -/
theorem reflB_proj_of_face {c : Fin 3} {y : R3} (h : y c = 0 ∨ y c = 1 / 2) :
    reflB (single c) (proj y) = proj y := by
  funext j
  by_cases hj : j = c
  · subst hj
    simp only [reflB, single, decide_true, ↓reduceIte, proj]
    rcases h with h | h
    · rw [h]; simp
    · rw [h, ← AddCircle.coe_neg, show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by norm_num,
        AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
  · simp [reflB, single, hj]

/-- **Parity of a trigonometric polynomial**: if `f(flip_ε k) = s f(k)` on a reflection-invariant
support, then `P(R_ε x) = s P(x)`. -/
theorem trigPoly_reflB {ε : Fin 3 → Bool} {f : lp (fun _ : Fin 3 → ℤ => ℂ) 2}
    {S : Finset (Fin 3 → ℤ)} (hSr : ∀ k ∈ S, flipB ε k ∈ S) {s : ℂ}
    (hf : ∀ k, f (flipB ε k) = s * f k) (x : UnitAddTorus (Fin 3)) :
    trigPoly f S (reflB ε x) = s * trigPoly f S x := by
  simp only [trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Geometry.mFourier_reflB, Finset.mul_sum]
  refine Finset.sum_nbij' (flipB ε) (flipB ε) (fun k hk => hSr k hk) (fun k hk => hSr k hk)
    (fun k _ => Geometry.flipB_flipB ε k) (fun k _ => Geometry.flipB_flipB ε k) fun k _ => ?_
  have e : f k = s * f (flipB ε k) := by rw [← hf, Geometry.flipB_flipB]
  rw [e]
  ring

/-- A trigonometric polynomial odd under `R_c` vanishes on the faces `y_c ∈ {0, ½}`. -/
theorem reLift_eq_zero_of_odd {c : Fin 3} {f : lp (fun _ : Fin 3 → ℤ => ℂ) 2}
    {S : Finset (Fin 3 → ℤ)} (hSr : ∀ k ∈ S, MirrorTorus.flip c k ∈ S)
    (hf : ∀ k, f (MirrorTorus.flip c k) = -f k) {y : R3} (hy : y c = 0 ∨ y c = 1 / 2) :
    reLift (trigPoly f S) y = 0 := by
  have h := trigPoly_reflB (ε := single c) (s := -1)
    (fun k hk => by rw [flipB_single]; exact hSr k hk)
    (fun k => by rw [flipB_single, hf]; ring) (proj y)
  rw [reflB_proj_of_face hy] at h
  have h0 : trigPoly f S (proj y) = 0 := by linear_combination h / 2
  simp [reLift, h0]

theorem le_sum_norm {ι : Type*} [Fintype ι] (F : ι → C(UnitAddTorus (Fin 3), ℂ)) (j : ι) :
    ‖F j‖ ≤ ∑ i, ‖F i‖ :=
  Finset.single_le_sum (f := fun i => ‖F i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

variable {P : Type*} [Fintype P]

/-- The physical field of a Fourier-side field. -/
abbrev physF (x : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    TorusWeak.Field (Fin 3) P :=
  (Fourier.Torus.fieldFourier (Fin 3) P).symm x

theorem repr_physF (x : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (Fin 3 → ℤ))) (p : P)
    (n : Fin 3 → ℤ) :
    mFourierBasis.repr (physF x p) n = (x : (Fin 3 → ℤ) → EuclideanSpace ℂ P) n p := by
  rw [mFourierBasis_repr, ← Fourier.Torus.fieldFourier_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **The restriction of a finitely supported field is the restriction of its trigonometric
polynomials.** -/
theorem Jinv_eq_smoothField {x : Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (Fin 3 → ℤ))}
    {S : Finset (Fin 3 → ℤ)} (hS : ∀ n ∉ S, (x : (Fin 3 → ℤ) → EuclideanSpace ℂ P) n = 0) :
    Jinv x = smoothField Geometry.isOpen_Q isBounded_Q
      (fun p => reLift (trigPoly (mFourierBasis.repr (physF x p)) S))
      (fun _ => (contDiff_reLift (isSmooth_trigPoly _ S)).continuous) := by
  refine PiLp.ext fun p => Lp.ext ?_
  have hS' : ∀ n ∉ S, mFourierBasis.repr (physF x p) n = 0 := fun n hn => by
    rw [repr_physF, hS n hn]; rfl
  set T := trigPoly (mFourierBasis.repr (physF x p)) S with hT
  have he : physF x p = T.toLp 2 volume ℂ := by
    rw [hT, ← TorusWeak.ofCoeff_eq_toLp S hS', TorusWeak.ofCoeff,
      LinearIsometryEquiv.symm_apply_apply]
  change (reL _ (resQ (physF x p)) : R3 → ℝ) =ᵐ[_] _
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (μ := (volume : Measure (UnitAddTorus (Fin 3)))) T
  have h' : (physF x p : UnitAddTorus (Fin 3) → ℂ) =ᵐ[volume] T := by rw [he]; exact h
  filter_upwards [coeFn_reL (resQ (physF x p)), Geometry.coeFn_resQ (physF x p),
    Geometry.ae_Q_of_ae_boxSet (ae_restrict_of_ae h'),
    Models.BoundedDomain.coeFn_smoothField Geometry.isOpen_Q isBounded_Q _
      (fun _ => (contDiff_reLift (isSmooth_trigPoly _ S)).continuous) p] with y h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  rfl

/-- **A trigonometric polynomial in the electric parity class restricts into `H̊(curl, Q)`**: for a
real electric parity field `z` with finitely many modes, `(z|_Q, (curl z)|_Q)` is a graph-norm
limit of test fields (cut-offs of its trigonometric polynomial, whose tangential components vanish
on `∂Q`). -/
theorem trig_closure_curl {z : Space 1} (hz : z ∈ Parity.realAction.fixed 1)
    {S : Finset (Fin 3 → ℤ)} (hS : ∀ n ∉ S, c1 z n = 0)
    (hSr : ∀ k, ∀ n ∈ S, MirrorTorus.flip k n ∈ S) (hd : z ∈ (RealTorus.gradCurl.d 1 2).domain) :
    (Jinv (P := Ix) z, Jinv (P := Ix) (RealTorus.gradCurl.d 1 2 ⟨z, hd⟩)) ∈
      closure ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).testGraph (Q (Fin 3)) :
        Set (Domain.L2F ℝ (Q (Fin 3)) Ix × Domain.L2F ℝ (Q (Fin 3)) Ix)) := by
  set Pp : Ix → C(UnitAddTorus (Fin 3), ℂ) := fun p =>
    trigPoly (mFourierBasis.repr (physF (P := Ix) z p)) S
  have hPs : ∀ p, IsSmooth (Pp p) := fun p => isSmooth_trigPoly _ _
  set ψ : Ix → R3 → ℝ := fun p => reLift (Pp p)
  have hψ : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (ψ p) := fun p => contDiff_reLift (hPs p)
  set D : Ix → Fin 3 → C(UnitAddTorus (Fin 3), ℂ) := fun p c =>
    ⟨partialT c (Pp p), TorusWeak.continuous_partialT (hPs p).contDiff_one c⟩
  set L : ℝ := ∑ p, ∑ c, ‖D p c‖
  have hL : ∀ p c y, |pd c (ψ p) y| ≤ L := fun p c y => by
    refine (abs_pd_reLift_le (hPs p) c y).trans ?_
    calc ‖D p c‖ ≤ ∑ c', ‖D p c'‖ := le_sum_norm (D p) c
      _ ≤ ∑ p', ∑ c', ‖D p' c'‖ := Finset.single_le_sum (f := fun p' => ∑ c', ‖D p' c'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ p)
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set M : ℝ := ∑ p, ‖Pp p‖ + 2 * L
  have hM : ∀ p y, |ψ p y| ≤ M := fun p y =>
    (abs_reLift_le _ y).trans ((le_sum_norm Pp p).trans (le_add_of_nonneg_right (by positivity)))
  have hMc : ∀ p y, |curlM ψ p y| ≤ M := fun p y => by
    have h1 := hL (p.1, p.2 + 2) (p.2 + 1) y
    have h2 := hL (p.1, p.2 + 1) (p.2 + 2) y
    have h3 : 0 ≤ ∑ p, ‖Pp p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc |curlM ψ p y|
        ≤ |pd (p.2 + 1) (ψ (p.1, p.2 + 2)) y| + |pd (p.2 + 2) (ψ (p.1, p.2 + 1)) y| :=
          abs_sub _ _
      _ ≤ M := by linarith
  have hpar := fixed_one_iff.1 (Parity.mem_realFixed_iff.1 hz).2
  have hV : ∀ a c d, c ≠ d → ∀ y : R3, (y c = 0 ∨ y c = 1 / 2) → ψ (a, d) y = 0 := by
    intro a c d hcd y hy
    refine reLift_eq_zero_of_odd (hSr c) (fun k => ?_) hy
    have e1 : (mFourierBasis.repr (physF (P := Ix) z (a, d))) (MirrorTorus.flip c k) =
        c1 z (MirrorTorus.flip c k) (a, d) := repr_physF (P := Ix) z (a, d) _
    have e2 : (mFourierBasis.repr (physF (P := Ix) z (a, d))) k = c1 z k (a, d) :=
      repr_physF (P := Ix) z (a, d) _
    rw [e1, e2, hpar c k (a, d)]
    simp [pe, hcd]
  have hcl := mem_closure_curl_of_smooth hψ hM hMc hL hV
  have heq : Jinv (P := Ix) z =
      smoothField Geometry.isOpen_Q isBounded_Q ψ fun p => (hψ p).continuous :=
    Jinv_eq_smoothField (P := Ix) (x := z) hS
  have hgr := J_mem_graph_curl hcl
  rw [← heq, show J1 (Jinv (P := Ix) z) = z from J_Jr 1 hz] at hgr
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hgr
  have hyz : y = ⟨z, hd⟩ := Subtype.ext hy1
  subst hyz
  have hdz : Jinv (P := Ix) (RealTorus.gradCurl.d 1 2 ⟨z, hd⟩) = smoothField Geometry.isOpen_Q
      isBounded_Q (curlM ψ)
        fun p => Models.BoundedDomain.continuous_curlM (fun q => (hψ q).of_le (by simp)) p := by
    rw [hy2]; exact Jr_J 2 _
  rw [hdz, heq]
  exact hcl

/-- **A trigonometric polynomial in the Dirichlet parity class restricts into `H̊¹(Q)`.** -/
theorem trig_closure_grad {z : Space 0} (hz : z ∈ Parity.realAction.fixed 0)
    {S : Finset (Fin 3 → ℤ)} (hS : ∀ n ∉ S, cv z n = 0)
    (hSr : ∀ k, ∀ n ∈ S, MirrorTorus.flip k n ∈ S) (hd : z ∈ (RealTorus.gradCurl.d 0 1).domain) :
    (Jinv (P := Fin 3) z, Jinv (P := Ix) (RealTorus.gradCurl.d 0 1 ⟨z, hd⟩)) ∈
      closure ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).testGraph (Q (Fin 3)) :
        Set (Domain.L2F ℝ (Q (Fin 3)) (Fin 3) × Domain.L2F ℝ (Q (Fin 3)) Ix)) := by
  set Pp : Fin 3 → C(UnitAddTorus (Fin 3), ℂ) := fun a =>
    trigPoly (mFourierBasis.repr (physF (P := Fin 3) z a)) S
  have hPs : ∀ a, IsSmooth (Pp a) := fun a => isSmooth_trigPoly _ _
  set ψ : Fin 3 → R3 → ℝ := fun a => reLift (Pp a)
  have hψ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (ψ a) := fun a => contDiff_reLift (hPs a)
  set D : Fin 3 → Fin 3 → C(UnitAddTorus (Fin 3), ℂ) := fun a c =>
    ⟨partialT c (Pp a), TorusWeak.continuous_partialT (hPs a).contDiff_one c⟩
  set L : ℝ := ∑ a, ∑ c, ‖D a c‖
  have hL : ∀ a c y, |pd c (ψ a) y| ≤ L := fun a c y => by
    refine (abs_pd_reLift_le (hPs a) c y).trans ?_
    calc ‖D a c‖ ≤ ∑ c', ‖D a c'‖ := le_sum_norm (D a) c
      _ ≤ ∑ a', ∑ c', ‖D a' c'‖ := Finset.single_le_sum (f := fun a' => ∑ c', ‖D a' c'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have hM : ∀ a y, |ψ a y| ≤ ∑ a, ‖Pp a‖ := fun a y =>
    (abs_reLift_le _ y).trans (le_sum_norm Pp a)
  have hpar := fixed_zero_iff.1 (Parity.mem_realFixed_iff.1 hz).2
  have hV : ∀ a c, ∀ y : R3, (y c = 0 ∨ y c = 1 / 2) → ψ a y = 0 := by
    intro a c y hy
    refine reLift_eq_zero_of_odd (hSr c) (fun k => ?_) hy
    have e1 : (mFourierBasis.repr (physF (P := Fin 3) z a)) (MirrorTorus.flip c k) =
        cv z (MirrorTorus.flip c k) a := repr_physF (P := Fin 3) z a _
    have e2 : (mFourierBasis.repr (physF (P := Fin 3) z a)) k = cv z k a :=
      repr_physF (P := Fin 3) z a _
    rw [e1, e2, hpar c k a]
    simp [pv]
  have hcl := mem_closure_grad_of_smooth hψ hM hL hV
  have heq : Jinv (P := Fin 3) z =
      smoothField Geometry.isOpen_Q isBounded_Q ψ fun a => (hψ a).continuous :=
    Jinv_eq_smoothField (P := Fin 3) (x := z) hS
  have hgr := J_mem_graph_grad hcl
  rw [← heq, show J0 (Jinv (P := Fin 3) z) = z from J_Jr 0 hz] at hgr
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hgr
  have hyz : y = ⟨z, hd⟩ := Subtype.ext hy1
  subst hyz
  have hdz : Jinv (P := Ix) (RealTorus.gradCurl.d 0 1 ⟨z, hd⟩) = smoothField Geometry.isOpen_Q
      isBounded_Q (gradM ψ)
        fun p => Models.BoundedDomain.continuous_pd ((hψ p.1).of_le (by simp)) p.2 := by
    rw [hy2]; exact Jr_J 1 _
  rw [hdz, heq]
  exact hcl

end Trig

/-! ### Fourier truncation: the parity spaces lie in the minimal domains -/

section Trunc

open Fourier.GradCurl
open Models.BoundedDomain (R3 Ix)

/-- The torus symbol complex. -/
local notation "TS" => Fourier.Torus.symbolComplex gradCurl

instance (N : ℕ) (i : Fin 3) : ((TS).band (Fourier.Torus.bandN N) i).HasOrthogonalProjection :=
  Fourier.hasOrthogonalProjection_band (TS) (Fourier.Torus.finite_bandN N).measurableSet i

/-- The Fourier truncation to the band `|n|_∞ ≤ N`. -/
abbrev trunc (N : ℕ) (i : Fin 3) : Space i →L[ℂ] Space i :=
  ((TS).band (Fourier.Torus.bandN N) i).starProjection

open scoped Classical in
theorem coeFn_trunc (N : ℕ) (i : Fin 3) (x : Space i) (n : Fin 3 → ℤ) :
    (trunc N i x : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n =
      if n ∈ Fourier.Torus.bandN N then (x : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n else 0 := by
  have := Measure.ae_count_iff.1 (Operator.coeFn_starProjection_fibreSub
    (μ := (Measure.count : Measure (Fin 3 → ℤ)))
    (Fourier.bandFibre (𝕜 := ℂ) (E := W3 Vec Mat Mat) (Fourier.Torus.bandN N) i)
    AEStronglyMeasurable.of_discrete x) n
  rw [this]
  dsimp only
  rw [Fourier.starProjection_bandFibre]
  by_cases hn : n ∈ Fourier.Torus.bandN N
  · simp [hn, Operator.cutoff_apply_of_mem hn]
  · simp [hn, Operator.cutoff_apply_of_notMem hn]

theorem flip_mem_bandN {N : ℕ} {n : Fin 3 → ℤ} (k : Fin 3) :
    MirrorTorus.flip k n ∈ Fourier.Torus.bandN N ↔ n ∈ Fourier.Torus.bandN N := by
  have h : ∀ j, |MirrorTorus.flip k n j| = |n j| := fun j => by
    unfold MirrorTorus.flip; split_ifs <;> simp
  simp only [Fourier.Torus.bandN, mem_ofPred_eq, h]

theorem neg_mem_bandN {N : ℕ} {n : Fin 3 → ℤ} :
    -n ∈ Fourier.Torus.bandN N ↔ n ∈ Fourier.Torus.bandN N := by
  simp [Fourier.Torus.bandN]

open scoped Classical in
theorem trunc_mem_zero {N : ℕ} {x : Space 0} (hx : x ∈ Parity.realAction.fixed 0) :
    trunc N 0 x ∈ Parity.realAction.fixed 0 := by
  obtain ⟨hc, hf⟩ := Parity.mem_realFixed_iff.1 hx
  have hc' := cnj_zero_iff.1 hc
  have hf' := fixed_zero_iff.1 hf
  have e : ∀ n, cv (trunc N 0 x) n = if n ∈ Fourier.Torus.bandN N then cv x n else 0 :=
    coeFn_trunc N 0 x
  refine Parity.mem_realFixed_iff.2 ⟨cnj_zero_iff.2 fun n a => ?_, fixed_zero_iff.2 fun k n a => ?_⟩
  · rw [e, e]
    by_cases hn : n ∈ Fourier.Torus.bandN N
    · simp [hn, neg_mem_bandN.2 hn, hc']
    · simp [hn, mt neg_mem_bandN.1 hn]
  · rw [e, e]
    by_cases hn : n ∈ Fourier.Torus.bandN N
    · simp [hn, (flip_mem_bandN k).2 hn, hf']
    · simp [hn, mt (flip_mem_bandN k).1 hn]

open scoped Classical in
theorem trunc_mem_one {N : ℕ} {x : Space 1} (hx : x ∈ Parity.realAction.fixed 1) :
    trunc N 1 x ∈ Parity.realAction.fixed 1 := by
  obtain ⟨hc, hf⟩ := Parity.mem_realFixed_iff.1 hx
  have hc' := cnj_one_iff.1 hc
  have hf' := fixed_one_iff.1 hf
  have e : ∀ n, c1 (trunc N 1 x) n = if n ∈ Fourier.Torus.bandN N then c1 x n else 0 :=
    coeFn_trunc N 1 x
  refine Parity.mem_realFixed_iff.2 ⟨cnj_one_iff.2 fun n p => ?_, fixed_one_iff.2 fun k n p => ?_⟩
  · rw [e, e]
    by_cases hn : n ∈ Fourier.Torus.bandN N
    · simp [hn, neg_mem_bandN.2 hn, hc']
    · simp [hn, mt neg_mem_bandN.1 hn]
  · rw [e, e]
    by_cases hn : n ∈ Fourier.Torus.bandN N
    · simp [hn, (flip_mem_bandN k).2 hn, hf']
    · simp [hn, mt (flip_mem_bandN k).1 hn]

/-- The truncation preserves the torus domains and commutes with the differentials. -/
theorem trunc_mem_domain (N : ℕ) {i j : Fin 3} {x : Space i}
    (hx : x ∈ (RealTorus.gradCurl.d i j).domain) :
    ∃ h : trunc N i x ∈ (RealTorus.gradCurl.d i j).domain,
      RealTorus.gradCurl.d i j ⟨_, h⟩ = trunc N j (RealTorus.gradCurl.d i j ⟨x, hx⟩) := by
  have hr := (Fourier.reducingSubcomplex_band (TS)
    (Fourier.Torus.finite_bandN N).measurableSet).reduces i j
  exact ⟨hr.proj_mem ⟨x, hx⟩, hr.comm ⟨x, hx⟩⟩

theorem tendsto_trunc (i : Fin 3) (x : Space i) :
    Tendsto (fun N => trunc N i x) atTop (𝓝 x) :=
  Fourier.tendsto_starProjection_band (TS) (fun N => (Fourier.Torus.finite_bandN N).measurableSet)
    Fourier.Torus.bandN_mono Fourier.Torus.exists_mem_bandN i x

open scoped Classical in
/-- **`J⁻¹ (H(curl, 𝕋³) ∩ real parity fields) ⊆ H̊(curl, Q)`**: if the extension of `u` lies in the
torus `H(curl)`, then `u` lies in the minimal curl domain (the truncations are trigonometric
polynomials with vanishing tangential traces, `trig_closure_curl`). -/
theorem mem_minimal_curl_of_J {u : Domain.L2F ℝ (Q (Fin 3)) Ix}
    (h : J1 u ∈ (RealTorus.gradCurl.d 1 2).domain) :
    u ∈ ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).minimal (Q (Fin 3))).domain := by
  set x := J1 u
  have hx : x ∈ Parity.realAction.fixed 1 := J1_mem u
  choose hN eN using fun N => trunc_mem_domain N h
  have hmem : ∀ N, (Jinv (P := Ix) (trunc N 1 x),
      Jinv (P := Ix) (RealTorus.gradCurl.d 1 2 ⟨_, hN N⟩)) ∈
      closure ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).testGraph (Q (Fin 3)) :
        Set (Domain.L2F ℝ (Q (Fin 3)) Ix × Domain.L2F ℝ (Q (Fin 3)) Ix)) := fun N =>
    trig_closure_curl (trunc_mem_one hx) (S := (Fourier.Torus.finite_bandN N).toFinset)
      (fun n hn => by
        have : n ∉ Fourier.Torus.bandN N := fun h' => hn ((Set.Finite.mem_toFinset _).2 h')
        change (trunc N 1 x : (Fin 3 → ℤ) → W3 Vec Mat Mat 1) n = 0
        rw [coeFn_trunc]; simp [this])
      (fun k n hn => (Set.Finite.mem_toFinset _).2
        ((flip_mem_bandN k).2 ((Set.Finite.mem_toFinset _).1 hn))) (hN N)
  have hlim : Tendsto (fun N => (Jinv (P := Ix) (trunc N 1 x),
      Jinv (P := Ix) (RealTorus.gradCurl.d 1 2 ⟨_, hN N⟩))) atTop
      (𝓝 (Jinv (P := Ix) x, Jinv (P := Ix) (RealTorus.gradCurl.d 1 2 ⟨x, h⟩))) := by
    refine Tendsto.prodMk_nhds ((Jinv.continuous.tendsto _).comp (tendsto_trunc 1 x)) ?_
    simp only [eN]
    exact (Jinv.continuous.tendsto _).comp (tendsto_trunc 2 _)
  have hcl := isClosed_closure.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  rw [show Jinv (P := Ix) x = u from Jinv_JR u] at hcl
  have hg : (u, Jinv (P := Ix) (RealTorus.gradCurl.d 1 2 ⟨x, h⟩)) ∈
      ((Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).minimal (Q (Fin 3))).graph := by
    rw [Domain.ConstCoeffOp.minimal_graph _ Geometry.isOpen_Q, ← SetLike.mem_coe,
      Submodule.topologicalClosure_coe]
    exact hcl
  exact LinearPMap.mem_domain_of_mem_graph hg

open scoped Classical in
/-- **`J⁻¹ (H¹(𝕋³) ∩ real parity fields) ⊆ H̊¹(Q)`.** -/
theorem mem_minimal_grad_of_J {u : Domain.L2F ℝ (Q (Fin 3)) (Fin 3)}
    (h : J0 u ∈ (RealTorus.gradCurl.d 0 1).domain) :
    u ∈ ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal (Q (Fin 3))).domain := by
  set x := J0 u
  have hx : x ∈ Parity.realAction.fixed 0 := J0_mem u
  choose hN eN using fun N => trunc_mem_domain N h
  have hmem : ∀ N, (Jinv (P := Fin 3) (trunc N 0 x),
      Jinv (P := Ix) (RealTorus.gradCurl.d 0 1 ⟨_, hN N⟩)) ∈
      closure ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).testGraph (Q (Fin 3)) :
        Set (Domain.L2F ℝ (Q (Fin 3)) (Fin 3) × Domain.L2F ℝ (Q (Fin 3)) Ix)) := fun N =>
    trig_closure_grad (trunc_mem_zero hx) (S := (Fourier.Torus.finite_bandN N).toFinset)
      (fun n hn => by
        have : n ∉ Fourier.Torus.bandN N := fun h' => hn ((Set.Finite.mem_toFinset _).2 h')
        change (trunc N 0 x : (Fin 3 → ℤ) → W3 Vec Mat Mat 0) n = 0
        rw [coeFn_trunc]; simp [this])
      (fun k n hn => (Set.Finite.mem_toFinset _).2
        ((flip_mem_bandN k).2 ((Set.Finite.mem_toFinset _).1 hn))) (hN N)
  have hlim : Tendsto (fun N => (Jinv (P := Fin 3) (trunc N 0 x),
      Jinv (P := Ix) (RealTorus.gradCurl.d 0 1 ⟨_, hN N⟩))) atTop
      (𝓝 (Jinv (P := Fin 3) x, Jinv (P := Ix) (RealTorus.gradCurl.d 0 1 ⟨x, h⟩))) := by
    refine Tendsto.prodMk_nhds ((Jinv.continuous.tendsto _).comp (tendsto_trunc 0 x)) ?_
    simp only [eN]
    exact (Jinv.continuous.tendsto _).comp (tendsto_trunc 1 _)
  have hcl := isClosed_closure.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  rw [show Jinv (P := Fin 3) x = u from Jinv_JR u] at hcl
  have hg : (u, Jinv (P := Ix) (RealTorus.gradCurl.d 0 1 ⟨x, h⟩)) ∈
      ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).minimal (Q (Fin 3))).graph := by
    rw [Domain.ConstCoeffOp.minimal_graph _ Geometry.isOpen_Q, ← SetLike.mem_coe,
      Submodule.topologicalClosure_coe]
    exact hcl
  exact LinearPMap.mem_domain_of_mem_graph hg

end Trunc

/-! ### The scaled embedding and the compression -/

section Embedding

open Models.BoundedDomain (R3 Ix)

/-- **The thesis' complex on the cube** `H̊¹(Q; ℝ³) → H̊(curl, Q; ℝ³ˣ³) → L²(Q; ℝ³ˣ³)`, the minimal
grad–curl complex `Feec.Models.BoundedDomain.gradCurl` on `Q = (0, ½)³`, on the window `Fin 3`. -/
abbrev cubeComplex : HilbertComplex ℝ ComplexShape.fin3 WQ :=
  (Models.BoundedDomain.gradCurl ℝ Geometry.isOpen_Q).toHilbertComplex

theorem cube_d_zero {i j : Fin 3} (h : ¬ ComplexShape.fin3.Rel i j) : cubeComplex.d i j = 0 :=
  cubeComplex.shape i j h

theorem torus_d_zero {i j : Fin 3} (h : ¬ ComplexShape.fin3.Rel i j) :
    RealTorus.gradCurl.d i j = 0 :=
  RealTorus.gradCurl.shape i j h

/-- The extension maps the cube domains into the torus domains and intertwines the
differentials. -/
theorem J_mapsTo_comm (i j : Fin 3) (x : (cubeComplex.d i j).domain) :
    ∃ h : J i x ∈ (RealTorus.gradCurl.d i j).domain,
      RealTorus.gradCurl.d i j ⟨_, h⟩ = J j (cubeComplex.d i j x) := by
  by_cases hij : ComplexShape.fin3.Rel i j
  · have hc : ∀ {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [NormedAddCommGroup F] [InnerProductSpace ℝ F] {T : E →ₗ.[ℝ] F} {p : E × F}
        (_ : p ∈ T.graph), ∃ h : p.1 ∈ T.domain, T ⟨p.1, h⟩ = p.2 := fun hp => by
      obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hp
      exact ⟨hy1 ▸ y.2, by rw [← hy2]; exact congrArg _ (Subtype.ext hy1.symm)⟩
    fin_cases i <;> fin_cases j <;> simp [ComplexShape.window] at hij
    · have hp := Domain.ConstCoeffOp.mem_closure_minimal
        (Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix) Geometry.isOpen_Q x
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hp
      exact hc (J_mem_graph_grad hp)
    · have hp := Domain.ConstCoeffOp.mem_closure_minimal
        (Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix) Geometry.isOpen_Q x
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hp
      exact hc (J_mem_graph_curl hp)
  · have h0 := torus_d_zero hij
    have hm : J i x ∈ (RealTorus.gradCurl.d i j).domain := by rw [h0]; exact Submodule.mem_top
    refine ⟨hm, ?_⟩
    rw [LinearPMap.apply_eq_zero_of_eq_zero h0,
      LinearPMap.apply_eq_zero_of_eq_zero (cube_d_zero hij),
      _root_.map_zero]

/-- **The trace part**: if the extension lies in the torus domain, the field lies in the minimal
(boundary-condition) domain on the cube. -/
theorem mem_domain_of_J (i j : Fin 3) (x : WQ i) (h : J i x ∈ (RealTorus.gradCurl.d i j).domain) :
    x ∈ (cubeComplex.d i j).domain := by
  by_cases hij : ComplexShape.fin3.Rel i j
  · fin_cases i <;> fin_cases j <;> simp [ComplexShape.window] at hij
    · exact mem_minimal_grad_of_J h
    · exact mem_minimal_curl_of_J h
  · rw [cube_d_zero hij]; exact Submodule.mem_top

/-- **The parity extension is a scaled embedding** of the thesis' complex on the cube into the real
torus grad–curl complex: inner products are multiplied by `8 = 2³`, the differentials are
intertwined, and the cube domains (with their boundary conditions) are exactly the preimages of
the torus domains. -/
def scaledEmbedding : HilbertComplex.ScaledEmbedding cubeComplex RealTorus.gradCurl where
  J := J
  scale _ := 8
  scale_pos _ := by norm_num
  inner_J i x y := inner_J i x y
  dScale _ _ := 1
  dScale_ne_zero _ _ := one_ne_zero
  mapsTo i j x := (J_mapsTo_comm i j x).1
  comm i j x := by rw [one_smul]; exact (J_mapsTo_comm i j x).2
  mem_domain_of_map := mem_domain_of_J

instance (i : Fin 3) : (LinearMap.range (J i : WQ i →ₗ[ℝ] Space i)).HasOrthogonalProjection := by
  rw [range_J]; infer_instance

/-- The ranges of the extension form a reducing subcomplex of the torus complex (the real parity
fields, fixed by a finite unitary action). -/
theorem reducingSubcomplex_range :
    RealTorus.gradCurl.ReducingSubcomplex fun i => LinearMap.range (J i : WQ i →ₗ[ℝ] Space i) := by
  have h := Parity.realAction.reducingSubcomplex_fixed
  refine ⟨fun i j => ?_⟩
  convert h.reduces i j using 1 <;> exact range_J _

theorem inner_J' (i : Fin 3) (x y : WQ i) : ⟪J i x, J i y⟫_ℝ = ((8 : ℝ) : ℝ) * ⟪x, y⟫_ℝ :=
  inner_J i x y

/-- **The cube complex is the compression of the torus complex** along the parity extension. -/
theorem cubeComplex_eq_compress :
    cubeComplex = RealTorus.gradCurl.compress J (by norm_num : (0 : ℝ) < 8) inner_J'
      reducingSubcomplex_range := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  refine LinearPMap.ext (Submodule.ext fun x => ?_) fun x hx hx' => ?_
  · rw [HilbertComplex.mem_compress_domain_iff]
    exact ⟨fun h => (J_mapsTo_comm i j ⟨x, h⟩).1, mem_domain_of_J i j x⟩
  · refine scaledEmbedding.J_injective j ?_
    change J j _ = J j _
    rw [HilbertComplex.J_compress_d, ← (J_mapsTo_comm i j ⟨x, hx⟩).2]

end Embedding

/-! ### Stationary magnetic data of a short complex -/

universe u

section Stationary

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)]
  (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-- **The stationary magnetic data** of a short complex: `(0, 0, B)` is stationary under the wave
group iff `B ∈ D(d₁†)` and `d₁† B = 0`. -/
theorem inj₂_mem_stationary_iff (B : W₂) :
    inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ B ∈ S.toHilbertComplex.waveGroup.stationary ↔
      ∃ h : B ∈ (S.d₁†).domain, S.d₁† ⟨B, h⟩ = 0 := by
  have hgen := HilbertComplex.generator_waveGroup S.toHilbertComplex
  constructor
  · intro hst
    obtain ⟨hD, hL⟩ := C0Group.mem_domain_generator_of_mem_stationary hst
    have hD' : inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ B ∈ S.toHilbertComplex.wave.domain := hgen ▸ hD
    have hB : B ∈ (S.d₁†).domain := (S.mem_wave_domain.1 hD').2.2.2
    refine ⟨hB, ?_⟩
    have e := LinearPMap.apply_eq_of_eq hgen ⟨_, hD⟩
      ⟨_, inj₂_mem_wave_domain (S := S) (⟨B, hB⟩ : (S.d₁†).domain).2⟩ rfl
    have e3 := e.symm.trans hL
    rw [wave_inj₂] at e3
    have e4 := congrArg (fun z : PiLp 2 (W3 W₀ W₁ W₂) => (z 1 : W₁)) e3
    simp only [inj₁_apply_one] at e4
    exact neg_eq_zero.1 e4
  · rintro ⟨hB, h0⟩
    have hw := wave_inj₂ (S := S) ⟨B, hB⟩
    rw [h0, neg_zero, _root_.map_zero] at hw
    have hx' : inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ B ∈ S.toHilbertComplex.waveGroup.generator.domain :=
      hgen.symm ▸ inj₂_mem_wave_domain (S := S) hB
    have hgen0 : S.toHilbertComplex.waveGroup.generator ⟨_, hx'⟩ = 0 := by
      rw [LinearPMap.apply_eq_of_eq hgen ⟨_, hx'⟩ ⟨_, inj₂_mem_wave_domain (S := S) hB⟩ rfl]
      exact hw
    exact C0Group.mem_stationary.2 (C0Group.S_apply_eq_of_generator_eq_zero ⟨_, hx'⟩ hgen0)

end Stationary

/-! ### Only stationary data propagate on `Q` -/

section Invariance

open Models.BoundedDomain (Ix tsd)
open HilbertComplex (totalSub totalJ)

theorem totalJ_injective : Function.Injective (totalJ J : PiLp 2 WQ →L[ℝ] PiLp 2 Space) :=
  fun _ _ h => PiLp.ext fun i => scaledEmbedding.J_injective i (congrArg (fun z => z i) h)

/-- **The extension intertwines the wave groups**: `J e^{tL_Q} = e^{tL_𝕋} J`. -/
theorem waveGroup_J (t : ℝ) (y : PiLp 2 WQ) :
    totalJ J (cubeComplex.waveGroup.S t y) = RealTorus.gradCurl.waveGroup.S t (totalJ J y) := by
  rw [cubeComplex_eq_compress]
  exact HilbertComplex.waveGroup_compress _ _ _ t y

theorem mem_stationary_iff_J (y : PiLp 2 WQ) :
    y ∈ cubeComplex.waveGroup.stationary ↔
      totalJ J y ∈ RealTorus.gradCurl.waveGroup.stationary := by
  simp only [C0Group.mem_stationary, ← waveGroup_J]
  exact forall_congr' fun t => totalJ_injective.eq_iff.symm

/-- On `Q` the extension is the identity: `(J u)|_Q = u`. -/
theorem resM_JR (pc : Ix → Fin 3 → ℂ) (u : Domain.L2F ℝ (Q (Fin 3)) Ix) :
    Parity.resM (JR pc u) = ofRealF u := by
  refine PiLp.ext fun p => ?_
  rw [Parity.resM_apply]
  change resQ ((Fourier.Torus.fieldFourier (Fin 3) Ix).symm
    (Fourier.Torus.fieldFourier (Fin 3) Ix (Xf pc (ofRealF u))) p) = ofRealF u p
  rw [LinearIsometryEquiv.symm_apply_apply, Xf_apply, resQ_X]

theorem JR_mem_boxSym {pc : Ix → Fin 3 → ℂ} {u : Domain.L2F ℝ (Q (Fin 3)) Ix}
    (h : ∀ a b, u (a, b) = u (b, a)) : (JR pc u : Parity.MatL) ∈ Parity.boxSym :=
  Parity.mem_boxSym.2 fun a b => by rw [resM_JR, ofRealF_apply, ofRealF_apply, h]

theorem JR_mem_boxTr {pc : Ix → Fin 3 → ℂ} {u : Domain.L2F ℝ (Q (Fin 3)) Ix}
    (h : ∑ a, u (a, a) = 0) : (JR pc u : Parity.MatL) ∈ Parity.boxTr := by
  refine Parity.mem_boxTr.2 ?_
  simp only [resM_JR, ofRealF_apply]
  rw [← map_sum, h, _root_.map_zero]

theorem J_one_mem_of_tsd {u : WQ 1} (hu : u ∈ tsd (Q (Fin 3))) :
    J 1 u ∈ rowAction.fixed 1 ⊓ Parity.boxSym ⊓ Parity.boxTr :=
  ⟨⟨(Parity.mem_realFixed_iff.1 (J_mem 1 u)).2, JR_mem_boxSym hu.1⟩, JR_mem_boxTr hu.2.1⟩

theorem J_two_mem_of_tsd {u : WQ 2} (hu : u ∈ tsd (Q (Fin 3))) :
    J 2 u ∈ rowAction.fixed 2 ⊓ Parity.boxSym ⊓ Parity.boxTr :=
  ⟨⟨(Parity.mem_realFixed_iff.1 (J_mem 2 u)).2, JR_mem_boxSym hu.1⟩, JR_mem_boxTr hu.2.1⟩

/-- The torus counterpart of a constraint `S` on `Q`: the real parity fields whose restriction to
`Q` lies in the closure of `S`. -/
def torusSub (i : Fin 3) (S : Submodule ℝ (WQ i)) : Submodule ℝ (Space i) :=
  Parity.realAction.fixed i ⊓ S.topologicalClosure.comap (Jr i : Space i →ₗ[ℝ] WQ i)

theorem isClosed_torusSub (i : Fin 3) (S : Submodule ℝ (WQ i)) :
    IsClosed (torusSub i S : Set (Space i)) :=
  (Parity.realAction.isClosed_fixed i).inter
    (S.isClosed_topologicalClosure.preimage (Jr i).continuous)

instance instHasOrthogonalProjectionTorusSub (i : Fin 3) (S : Submodule ℝ (WQ i)) :
    (torusSub i S).HasOrthogonalProjection := by
  have : CompleteSpace (torusSub i S) := (isClosed_torusSub i S).completeSpace_coe
  infer_instance

theorem J_mem_torusSub {i : Fin 3} {S : Submodule ℝ (WQ i)} {u : WQ i} (hu : u ∈ S) :
    J i u ∈ torusSub i S :=
  ⟨J_mem i u, by
    change Jr i (J i u) ∈ S.topologicalClosure
    rw [Jr_J]; exact S.le_topologicalClosure hu⟩

theorem torusSub_one_le {S : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) Ix)} (h : S ≤ tsd (Q (Fin 3))) :
    torusSub 1 S ≤ rowAction.fixed 1 ⊓ Parity.boxSym ⊓ Parity.boxTr := by
  intro x hx
  rw [← J_Jr 1 hx.1]
  exact J_one_mem_of_tsd (S.topologicalClosure_minimal h Models.BoundedDomain.isClosed_tsd hx.2)

theorem torusSub_two_le {S : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) Ix)} (h : S ≤ tsd (Q (Fin 3))) :
    torusSub 2 S ≤ rowAction.fixed 2 ⊓ Parity.boxSym ⊓ Parity.boxTr := by
  intro x hx
  rw [← J_Jr 2 hx.1]
  exact J_two_mem_of_tsd (S.topologicalClosure_minimal h Models.BoundedDomain.isClosed_tsd hx.2)

/-- **On `Q` with the thesis' boundary conditions, forward invariance forces stationarity**: for
`S₁, S₂ ⊆ L²(TSD)` (closed or not), the forward orbit (`t ≥ 0`) of `y` under the wave group of
`H̊¹(Q) → H̊(curl, Q) → L²(Q)` stays in `{0} × S₁ × S₂` iff `y` lies there and is stationary.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem forward_iff {S1 S2 : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) Ix)}
    (h1 : S1 ≤ tsd (Q (Fin 3))) (h2 : S2 ≤ tsd (Q (Fin 3))) (y : PiLp 2 WQ) :
    (∀ t, 0 ≤ t → cubeComplex.waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3))) S1 S2) ∧
        y ∈ cubeComplex.waveGroup.stationary := by
  have := instHasOrthogonalProjectionTorusSub 1 S1
  have := instHasOrthogonalProjectionTorusSub 2 S2
  constructor
  · intro h
    have hy := h 0 le_rfl
    rw [C0Group.S_zero_apply] at hy
    refine ⟨hy, ?_⟩
    have hK : ∀ t, 0 ≤ t → RealTorus.gradCurl.waveGroup.S t (totalJ J y) ∈
        totalSub (Parity.constraint (torusSub 1 S1) (torusSub 2 S2)) := by
      intro t ht
      rw [← waveGroup_J]
      obtain ⟨e0, m1, m2⟩ := mem_totalSub_family3.1 (h t ht)
      refine Parity.mem_totalSub_constraint.2 ⟨?_, J_mem_torusSub m1, J_mem_torusSub m2⟩
      have e0' : ((cubeComplex.waveGroup.S t y) 0 : Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) = 0 := e0
      show J 0 ((cubeComplex.waveGroup.S t y) 0) = 0
      rw [e0', _root_.map_zero]
    have hc := RealTorus.gradCurl.isIsometric_waveGroup.mem_invariantCore_of_forward_invariant
      Parity.isPurePoint_torus HilbertComplex.isClosed_totalSub hK
    exact (mem_stationary_iff_J y).2
      ((Parity.mem_invariantCore_torus_iff (torusSub_one_le h1) (torusSub_two_le h2) _).1 hc).2
  · rintro ⟨hK, hst⟩ t _
    rw [C0Group.mem_stationary.1 hst t]; exact hK

/-- **`K*` on `Q` with the thesis' boundary conditions consists of the stationary data in `K`**,
for every `S₁, S₂ ⊆ L²(TSD)`. See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem mem_invariantCore_iff {S1 S2 : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) Ix)}
    (h1 : S1 ≤ tsd (Q (Fin 3))) (h2 : S2 ≤ tsd (Q (Fin 3))) (y : PiLp 2 WQ) :
    y ∈ cubeComplex.waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3))) S1 S2) ∧
        y ∈ cubeComplex.waveGroup.stationary := by
  refine ⟨fun hy => (forward_iff h1 h2 y).1 fun t _ => C0Group.mem_invariantCore.1 hy t,
    fun ⟨hK, hst⟩ => C0Group.mem_invariantCore.2 fun t => ?_⟩
  rw [C0Group.mem_stationary.1 hst t]; exact hK

/-- **`K*` on `Q` for the thesis' constraint, explicitly**: `y ∈ K*` iff `y = (0, 0, B₀)` with
`B₀ ∈ L²(TSD)` and `d₁† B₀ = curl B₀ = 0` (no boundary condition on `B₀`).
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem mem_invariantCore_tsd_iff (y : PiLp 2 WQ) :
    y ∈ cubeComplex.waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)))
          (tsd (Q (Fin 3))) (tsd (Q (Fin 3))))) ↔
      ∃ B ∈ tsd (Q (Fin 3)),
        ∃ h : B ∈ ((Models.BoundedDomain.gradCurl ℝ Geometry.isOpen_Q).d₁†).domain,
          (Models.BoundedDomain.gradCurl ℝ Geometry.isOpen_Q).d₁† ⟨B, h⟩ = 0 ∧
            y = inj₂ (𝕜 := ℝ) (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) (Domain.L2F ℝ (Q (Fin 3)) Ix)
              (Domain.L2F ℝ (Q (Fin 3)) Ix) B := by
  rw [mem_invariantCore_iff le_rfl le_rfl, mem_totalSub_family3]
  constructor
  · rintro ⟨⟨h0, -, h2⟩, hst⟩
    have h0' : (y 0 : WQ 0) = 0 := h0
    have hz : ((totalJ J y) 0 : Space 0) = 0 := by
      change J 0 (y 0) = 0
      rw [h0', _root_.map_zero]
    have e1 := ((Parity.mem_stationary_iff hz
      (Parity.mem_realFixed_iff.1 (J_mem 1 (y 1))).2).1 ((mem_stationary_iff_J y).1 hst)).1
    have hy1 : (y 1 : WQ 1) = 0 :=
      scaledEmbedding.J_injective 1 (e1.trans (_root_.map_zero (J 1)).symm)
    have hy : y = inj₂ (𝕜 := ℝ) (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) (Domain.L2F ℝ (Q (Fin 3)) Ix)
        (Domain.L2F ℝ (Q (Fin 3)) Ix) (y 2 : WQ 2) := PiLp.ext fun i => by
      fin_cases i
      exacts [h0', hy1, rfl]
    rw [hy] at hst
    obtain ⟨hB, hB0⟩ := (inj₂_mem_stationary_iff _ _).1 hst
    exact ⟨y 2, h2, hB, hB0, hy⟩
  · rintro ⟨B, hB, hd, hd0, rfl⟩
    exact ⟨⟨rfl, Submodule.zero_mem _, hB⟩,
      (inj₂_mem_stationary_iff _ _).2 ⟨hd, hd0⟩⟩

end Invariance

end Feec.Models.Cube.RowWise
