module

public import Feec.Models.Cube.Mirror

/-!
# Mirror boundary conditions as trace conditions

The mirror complex on `Q = (0, ½)³` (`Feec.Models.Cube.Mirror.complexQ`, Prop 4.17 with tensorial
mirror conditions) is defined by the method of images: a field lies in a domain iff its extension
by the mirror parities lies in the corresponding torus Sobolev space. This file characterizes
these domains on `Q` itself by **Green's formulas with vanishing boundary terms**, the weak form
of trace conditions (as for `H̊(curl)` in `Feec.Domain.ConstCoeffOp.mem_minimal_domain_iff`),
tested against the **trace test functions** `MirrorTrace.IsTraceTest c`: `ψ ∈ C¹(ℝ³)` with `ψ = 0`
on the closed faces `{x_j = 0}`, `{x_j = ½}` of `Q̄` for which `c_j = -1`, and no condition on the
other faces (no periodicity, no reflection symmetry). The free traces of `ψ` on the faces with
`c_j = 1` carry the boundary conditions:

| operator | parity of the test function | Green's formula | boundary condition |
|---|---|---|---|
| `d₀ = grad` | `cE (a, b)` | `∫ σ_a ∂_b ψ = -∫ G_{ab} ψ` | `σ · n = 0` |
| `d₁ = curl` | `cB (a, b)` | `∫ (E_{a,b+2} ∂_{b+1} ψ - E_{a,b+1} ∂_{b+2} ψ) = -∫ C_{ab} ψ` | `E_{nτ} = 0` |
| `d₀† = -div` | `cV a` | `Σ_c ∫ M_{ac} ∂_c ψ = ∫ D_a ψ` | `E_{τn} = 0` |
| `d₁† = curl` | `cE (a, b)` | as for `d₁` | `B_{ττ} = 0` |

(`Mirror.complexQ_d₀_iff`, `complexQ_d₁_iff`, `complexQ_adjoint_d₀_iff`,
`complexQ_adjoint_d₁_iff`). Hence `D(L)` of the mirror complex is described by these formulas
(`Mirror.mem_wave_domain_iff_trace`), and Prop 4.17 holds on `Q` with these boundary conditions,
with existence and uniqueness and TSD propagation (`Mirror.existsUnique_memQ_trace`). The same
holds on **every open cube** `∏ (bᵢ, bᵢ + s)` (`Mirror.complexCube`), with the trace test
functions of the cube (`Mirror.IsTraceTestCube`, `Mirror.mem_wave_domain_cube_iff_trace`,
`Mirror.existsUnique_memCube_trace`).

The boundary conditions in the last column are the reading of the Green's formulas (the faces on
which `ψ` is free and the boundary term `∫_{∂Q} f_p ψ n_c` that the formula forces to vanish);
pointwise traces of `L²` fields with `L²` derivatives are not formalized.

## Method

For a first-order operator `g = Σ α_{cp} ∂_c f_p` whose terms all have the same output parity,
the weak equation on `𝕋³` for the extensions (`Feec.Fourier.TorusWeak.IsWeakFO`, tested against
all smooth `φ` on `𝕋³`) is first shown equivalent to the Green's formula on `Q` against the
**smooth parity functions** (`MirrorTrace.IsParSmooth`, smooth `ℤ³`-periodic functions with the
reflection parities; `MirrorTrace.isWeakFO_extL2_iff`): a parity function `f` pairs with `φ` as
with its parity projection `P_c φ = 2⁻³ Σ_ε sign_c(ε) φ ∘ R_ε` (`MirrorTrace.integral_mul_parProj`),
the tiling of `𝕋³` by the eight reflected boxes gives `∫_{𝕋³} (ext_c g) G = 8 ∫_Q g G` for `G` of
parity `c` (`MirrorTrace.integral_extL2_mul`), and `∂_k` commutes with `P` up to the reversal of
the parity of `x_k` (`MirrorTrace.partialT_parProj`).

The smooth parity functions are trace test functions (`MirrorTrace.IsParSmooth.isTraceTest`). For
the converse (`MirrorTrace.isWeakFO_extL2_iff_trace`), the extension of a trace test function `ψ`
is weakly differentiable on `𝕋³` with derivative the extension of `∂_k ψ`
(`MirrorTrace.mFourierCoeff_extL2_fderiv`): its Fourier coefficients are pairings on `Q` with the
smooth parity functions `P_c e_{-m}`, and the divergence theorem on the box `[0, ½]³`
(`MirrorTrace.ibp_Q`) has no boundary terms because on each face either `ψ` or `P_c e_{-m}`
vanishes. Parseval then turns the Fourier form of the weak equation into the Green's formula.

## Scope

Only the first-order complex of Prop 4.17 is treated. The complex (4.16) of Prop 4.19
(`Feec.Models.Cube.MirrorSym`) has the second-order differential `grad grad`, for which the torus
weak theory (`Feec.Fourier.TorusWeak`) has no counterpart; its mirror conditions are not
characterized here.

## Main results

* `MirrorTrace.IsTraceTest`, `MirrorTrace.ibp_Q`, `MirrorTrace.mFourierCoeff_extL2_fderiv`,
  **`MirrorTrace.isWeakFO_extL2_iff_trace`**; `MirrorTrace.IsParSmooth`,
  `MirrorTrace.isWeakFO_extL2_iff`.
* **`Mirror.complexQ_d₀_iff`**, **`Mirror.complexQ_d₁_iff`**, **`Mirror.complexQ_adjoint_d₀_iff`**,
  **`Mirror.complexQ_adjoint_d₁_iff`** (and the `_isParSmooth` forms),
  **`Mirror.mem_wave_domain_iff_trace`**, **`Mirror.existsUnique_memQ_trace`**.
* `Mirror.IsTraceTestCube`, **`Mirror.mem_wave_domain_cube_iff_trace`**,
  **`Mirror.existsUnique_memCube_trace`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension by reflection)
-/

open scoped InnerProductSpace ContDiff LinearPMap ComplexConjugate
open Set MeasureTheory Filter UnitAddTorus Feec.Fourier.TorusWeak

@[expose] public noncomputable section

namespace Feec.Models.Cube.MirrorTrace

open Geometry MirrorExt

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Parity projections of smooth functions on the torus -/

/-- The **parity projection** `P_c φ = 2⁻ᵈ Σ_ε sign_c(ε) φ ∘ R_ε` of a function on `𝕋ᵈ`: the
part of `φ` with parity `c` (odd in `x_j` for `c_j = -1`, even for `c_j = 1`). -/
def parProj (c : d → ℂ) (φ : UnitAddTorus d → ℂ) (x : UnitAddTorus d) : ℂ :=
  ((2 ^ Fintype.card d : ℝ) : ℂ)⁻¹ * ∑ ε : d → Bool, sign c ε * φ (reflB ε x)

omit [DecidableEq d] in
theorem two_pow_card_ne_zero : ((2 ^ Fintype.card d : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (pow_pos two_pos _).ne'

theorem isSmooth_parProj (c : d → ℂ) {φ : UnitAddTorus d → ℂ} (hφ : IsSmooth φ) :
    IsSmooth (parProj c φ) := by
  unfold IsSmooth
  have e : parProj c φ ∘ proj = fun y => ((2 ^ Fintype.card d : ℝ) : ℂ)⁻¹ *
      ∑ ε : d → Bool, sign c ε * φ (reflB ε (proj y)) := by
    funext y; rfl
  rw [e]
  exact contDiff_const.mul (ContDiff.sum fun ε _ => contDiff_const.mul
    (isSmooth_comp_reflB hφ ε))

theorem continuous_parProj (c : d → ℂ) {φ : UnitAddTorus d → ℂ} (hφ : IsSmooth φ) :
    Continuous (parProj c φ) := (isSmooth_parProj c hφ).continuous

/-- **Parity of the projection.** -/
theorem parProj_reflB {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (φ : UnitAddTorus d → ℂ)
    (η : d → Bool) (x : UnitAddTorus d) : parProj c φ (reflB η x) = sign c η * parProj c φ x := by
  rw [parProj, parProj, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  let e : (d → Bool) ≃ (d → Bool) :=
    { toFun := fun ε j => xor (ε j) (η j)
      invFun := fun ε j => xor (ε j) (η j)
      left_inv := fun ε => funext fun j => by simp
      right_inv := fun ε => funext fun j => by simp }
  refine (Fintype.sum_equiv e _ _ fun ε => ?_)
  change ((2 ^ Fintype.card d : ℝ) : ℂ)⁻¹ * (sign c ε * φ (reflB ε (reflB η x))) =
    sign c η * (((2 ^ Fintype.card d : ℝ) : ℂ)⁻¹ *
      (sign c (fun j => xor (ε j) (η j)) * φ (reflB (fun j => xor (ε j) (η j)) x)))
  rw [reflB_comp, sign_xor hc]
  have hη : sign c η * sign c η = 1 := by
    rw [← sign_xor hc]; simp [sign]
  linear_combination (-(((2 ^ Fintype.card d : ℝ) : ℂ)⁻¹ * sign c ε *
    φ (reflB (fun j => xor (ε j) (η j)) x))) * hη

/-- A function with parity `c` is its own parity projection. -/
theorem parProj_of_parity {c : d → ℂ} (hc : ∀ j, c j * c j = 1) {φ : UnitAddTorus d → ℂ}
    (hφ : ∀ η x, φ (reflB η x) = sign c η * φ x) : parProj c φ = φ := by
  funext x
  have hs : ∀ ε : d → Bool, sign c ε * sign c ε = 1 := fun ε => by
    rw [← sign_xor hc]; simp [sign]
  simp only [parProj, hφ, ← mul_assoc, hs, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  field_simp

/-- **Derivatives of parity projections**: `∂_k (P_c φ) = P_{c'} (∂_k φ)`, with the parity of
`x_k` reversed (`c'_k = -c_k`). -/
theorem partialT_parProj (c : d → ℂ) {φ : UnitAddTorus d → ℂ} (hφ : IsSmooth φ) (k : d) :
    partialT k (parProj c φ) = parProj (Function.update c k (-c k)) (partialT k φ) := by
  funext x
  have hd : ∀ ε : d → Bool, Differentiable ℝ ((fun x => φ (reflB ε x)) ∘ proj) := fun ε =>
    (isSmooth_comp_reflB hφ ε).contDiff_one.differentiable one_ne_zero
  have hsum : HasDerivAt (fun t : ℝ => parProj c φ (x + proj (Pi.single k t)))
      (((2 ^ Fintype.card d : ℝ) : ℂ)⁻¹ * ∑ ε : d → Bool, sign c ε *
        partialT k (fun x => φ (reflB ε x)) (x + proj (Pi.single k 0))) 0 := by
    have := (HasDerivAt.sum (u := Finset.univ) fun ε _ =>
      (hasDerivAt_translate (hd ε) k x 0).const_mul (sign c ε)).const_mul
        (((2 ^ Fintype.card d : ℝ) : ℂ)⁻¹)
    convert this using 1
    funext t; simp [parProj, Finset.sum_apply]
  unfold partialT
  rw [hsum.deriv, parProj]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Pi.single_zero, proj_zero, add_zero,
    partialT_comp_reflB (hφ.contDiff_one.differentiable one_ne_zero)]
  have hs : sign (Function.update c k (-c k)) ε = (if ε k then -1 else 1) * sign c ε := by
    rw [sign, sign, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ (fun j => if ε j then c j else 1) (Finset.mem_univ k)]
    rw [show (∏ j ∈ Finset.univ.erase k,
        if ε j then Function.update c k (-c k) j else 1) =
        ∏ j ∈ Finset.univ.erase k, if ε j then c j else 1 from
      Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
    by_cases h : ε k <;> simp [h]
  rw [hs]
  unfold partialT
  ring

/-! ### Pairings of parity functions -/

/-- **Parity functions transform by their sign**: `f ∘ R_ε = sign_c(ε) f` a.e. -/
theorem comp_reflB_ae {c : d → ℂ} {f : T2 d} (hf : f ∈ paritySub c) (ε : d → Bool) :
    (fun x => (f : UnitAddTorus d → ℂ) (reflB ε x)) =ᵐ[volume]
      fun x => sign c ε * (f : UnitAddTorus d → ℂ) x := by
  set g : T2 d := Lp.compMeasurePreserving (reflB ε) (measurePreserving_reflB ε) f
  have hg : (g : UnitAddTorus d → ℂ) =ᵐ[volume] fun x => (f : UnitAddTorus d → ℂ) (reflB ε x) :=
    Lp.coeFn_compMeasurePreserving _ _
  have hsf : ((sign c ε • f : T2 d) : UnitAddTorus d → ℂ)
      =ᵐ[volume] fun x => sign c ε * (f : UnitAddTorus d → ℂ) x :=
    (Lp.coeFn_smul (sign c ε) f).mono fun x hx => by rw [hx]; rfl
  have hcoef : ∀ {u v : UnitAddTorus d → ℂ}, u =ᵐ[volume] v → ∀ n,
      mFourierCoeff u n = mFourierCoeff v n := fun h n =>
    integral_congr_ae (h.mono fun x hx => by simp [hx])
  have e : g = sign c ε • f := eq_of_mFourierCoeff_eq fun n => by
    rw [hcoef hg, mFourierCoeff_comp_reflB, mFourierCoeff_flipB hf, hcoef hsf]
    simp only [mFourierCoeff, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have e' : (g : UnitAddTorus d → ℂ) = ((sign c ε • f : T2 d) : UnitAddTorus d → ℂ) := by rw [e]
  filter_upwards [hg, hsf] with x h1 h2
  rw [← h1, congrFun e' x, h2]

/-- **Pairing against the parity projection**: `∫ f φ = ∫ f (P_c φ)` for `f` of parity `c`. -/
theorem integral_mul_parProj {c : d → ℂ} (hc : ∀ j, c j * c j = 1) {f : T2 d}
    (hf : f ∈ paritySub c) {φ : UnitAddTorus d → ℂ} (hφ : Continuous φ) :
    ∫ x, (f : UnitAddTorus d → ℂ) x * φ x =
      ∫ x, (f : UnitAddTorus d → ℂ) x * parProj c φ x := by
  have hs : ∀ ε : d → Bool, sign c ε * sign c ε = 1 := fun ε => by
    rw [← sign_xor hc]; simp [sign]
  have hint : ∀ ε : d → Bool, Integrable fun x => (f : UnitAddTorus d → ℂ) x * φ (reflB ε x) :=
    fun ε => integrable_mul_continuous f (hφ.comp (continuous_pi fun j => by
      by_cases h : ε j
      · simp only [reflB, h, ↓reduceIte]; exact (continuous_apply j).neg
      · simp only [reflB, h, Bool.false_eq_true, ↓reduceIte]; exact continuous_apply j))
  have hterm : ∀ ε : d → Bool, ∫ x, (f : UnitAddTorus d → ℂ) x * φ (reflB ε x) =
      sign c ε * ∫ x, (f : UnitAddTorus d → ℂ) x * φ x := by
    intro ε
    have h := (measurePreserving_reflB ε).integral_comp' (f := reflBE ε)
      (fun x => (f : UnitAddTorus d → ℂ) (reflB ε x) * φ x)
    simp only [reflBE, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, reflB_reflB] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [comp_reflB_ae hf ε] with x hx
    rw [hx]; ring
  have e : (fun x => (f : UnitAddTorus d → ℂ) x * parProj c φ x) = fun x =>
      ((2 ^ Fintype.card d : ℝ) : ℂ)⁻¹ * ∑ ε : d → Bool,
        sign c ε * ((f : UnitAddTorus d → ℂ) x * φ (reflB ε x)) := by
    funext x
    simp only [parProj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => by ring
  rw [e, integral_const_mul, integral_finsetSum _ fun ε _ => (hint ε).const_mul _]
  simp only [integral_const_mul, hterm]
  simp only [← mul_assoc, hs, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  field_simp

/-- **Pairing of an extension with a parity function**: `∫_{𝕋ᵈ} (ext_c g) G = 2ᵈ ∫_Q g G` for
`G` continuous with parity `c`. -/
theorem integral_extL2_mul {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (g : Domain.L2 ℂ (Q d))
    {G : UnitAddTorus d → ℂ} (hG : Continuous G) (hpar : ∀ η x, G (reflB η x) = sign c η * G x) :
    ∫ x, (extL2 hc g : UnitAddTorus d → ℂ) x * G x =
      ((2 ^ Fintype.card d : ℝ) : ℂ) * ∫ y in Q d, (g : (d → ℝ) → ℂ) y * G (proj y) := by
  have hs : ∀ ε : d → Bool, sign c ε * sign c ε = 1 := fun ε => by
    rw [← sign_xor hc]; simp [sign]
  set F := extL2 hc g
  have hint : Integrable fun x => (F : UnitAddTorus d → ℂ) x * G x :=
    integrable_mul_continuous F hG
  rw [integral_eq_sum_box hint]
  have hb : ∀ ε : d → Bool, ∫ x in boxSet d, (F : UnitAddTorus d → ℂ) (reflB ε x) * G (reflB ε x) =
      ∫ x in boxSet d, (F : UnitAddTorus d → ℂ) x * G x := fun ε => by
    refine setIntegral_congr_ae₀ measurableSet_boxSet.nullMeasurableSet ?_
    filter_upwards [comp_reflB_ae (extL2_mem hc g) ε] with x hx _
    rw [hx, hpar]
    linear_combination ((F : UnitAddTorus d → ℂ) x * G x) * hs ε
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    nsmul_eq_mul]
  rw [setIntegral_boxSet _ hint.aestronglyMeasurable.restrict]
  congr 1
  · push_cast; ring
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_resQ F] with y h
    rw [← h, resQ_extL2]

/-- **Pairing of an extension with a smooth function**: `∫_{𝕋ᵈ} (ext_c g) φ = 2ᵈ ∫_Q g (P_c φ)`. -/
theorem integral_extL2_mul_smooth {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (g : Domain.L2 ℂ (Q d))
    {φ : UnitAddTorus d → ℂ} (hφ : IsSmooth φ) :
    ∫ x, (extL2 hc g : UnitAddTorus d → ℂ) x * φ x =
      ((2 ^ Fintype.card d : ℝ) : ℂ) *
        ∫ y in Q d, (g : (d → ℝ) → ℂ) y * parProj c φ (proj y) := by
  rw [integral_mul_parProj hc (extL2_mem hc g) hφ.continuous]
  exact integral_extL2_mul hc g (continuous_parProj c hφ) (parProj_reflB hc φ)

theorem continuous_parProj' (c : d → ℂ) {φ : UnitAddTorus d → ℂ} (hφ : Continuous φ) :
    Continuous (parProj c φ) :=
  continuous_const.mul (continuous_finsetSum _ fun ε _ => continuous_const.mul
    (hφ.comp (continuous_pi fun j => by
      by_cases h : ε j
      · simp only [reflB, h, ↓reduceIte]; exact (continuous_apply j).neg
      · simp only [reflB, h, Bool.false_eq_true, ↓reduceIte]; exact continuous_apply j)))

/-- **Pairing an extension with a derivative**: if `c'` is `c` with the parity of `x_k`
reversed, `∫_{𝕋ᵈ} (ext_{c'} g) ∂_k φ = 2ᵈ ∫_Q g ∂_k (P_c φ)`. -/
theorem integral_extL2_mul_partialT {c c' : d → ℂ} (hc' : ∀ j, c' j * c' j = 1) {k : d} (hu : Function.update c' k (-c' k) = c)
    (g : Domain.L2 ℂ (Q d)) {φ : UnitAddTorus d → ℂ} (hφ : IsSmooth φ) :
    ∫ x, (extL2 hc' g : UnitAddTorus d → ℂ) x * partialT k φ x =
      ((2 ^ Fintype.card d : ℝ) : ℂ) *
        ∫ y in Q d, (g : (d → ℝ) → ℂ) y * fderiv ℝ (parProj c φ ∘ proj) y (Pi.single k 1) := by
  have hu' : Function.update c k (-c k) = c' := by
    rw [← hu]; funext j; by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hP : parProj c' (partialT k φ) = partialT k (parProj c φ) := by
    rw [partialT_parProj c hφ k, hu']
  rw [integral_mul_parProj hc' (extL2_mem hc' g) (continuous_partialT hφ.contDiff_one k), hP]
  have hPs := isSmooth_parProj c hφ
  rw [integral_extL2_mul hc' g (continuous_partialT hPs.contDiff_one k) fun η x => by
    rw [← hP]; exact parProj_reflB hc' _ η x]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [partialT_proj (hPs.contDiff_one.differentiable one_ne_zero)]

/-! ### Smooth parity functions on `ℝᵈ` -/

/-- The reflection `y ↦ (±y_j)_j` of `ℝᵈ` (`-y_j` where `ε j`). -/
def reflR (ε : d → Bool) (y : d → ℝ) : d → ℝ := fun j => if ε j then -y j else y j

/-- **A smooth parity function** for the sign vector `c` (`c_j = ±1`): `ψ ∈ C^∞(ℝᵈ)`, `ℤᵈ`-periodic,
with `ψ ∘ R_ε = (∏_{ε_j} c_j) ψ` for every reflection `R_ε y = (±y_j)_j` (odd in `y_j` for
`c_j = -1`, even for `c_j = 1`). These are the smooth functions on `[0, ½]ᵈ` whose extension by
the parity `c` is smooth: on a face `y_j ∈ {0, ½}` they vanish if `c_j = -1` and have vanishing
normal derivative if `c_j = 1`. -/
structure IsParSmooth (c : d → ℂ) (ψ : (d → ℝ) → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ ψ
  periodic : ∀ (m : d → ℤ) (y : d → ℝ), ψ (y + fun j => (m j : ℝ)) = ψ y
  parity : ∀ (ε : d → Bool) (y : d → ℝ), ψ (reflR ε y) = sign c ε * ψ y

omit [Fintype d] [DecidableEq d] in
theorem proj_intCast (m : d → ℤ) : proj (fun j => (m j : ℝ)) = 0 := by
  funext j; simp [proj]

omit [Fintype d] [DecidableEq d] in
theorem per_comp_proj {ψ : (d → ℝ) → ℂ}
    (hψ : ∀ (m : d → ℤ) (y : d → ℝ), ψ (y + fun j => (m j : ℝ)) = ψ y) :
    per ψ ∘ proj = ψ := by
  funext y
  simp only [Function.comp_apply, per_proj]
  have e : (fun i => y i - (⌊y i⌋ : ℝ)) = y + fun j => ((-⌊y j⌋ : ℤ) : ℝ) := by
    funext i; simp [sub_eq_add_neg]
  rw [e, hψ]

omit [DecidableEq d] in
/-- A smooth parity function is the lift of a smooth parity function on the torus. -/
theorem IsParSmooth.torus {c : d → ℂ} {ψ : (d → ℝ) → ℂ} (hψ : IsParSmooth c ψ) :
    IsSmooth (per ψ) ∧ (∀ η x, per ψ (reflB η x) = sign c η * per ψ x) ∧ per ψ ∘ proj = ψ := by
  have h1 := per_comp_proj hψ.periodic
  refine ⟨by unfold IsSmooth; rw [h1]; exact hψ.contDiff, fun η x => ?_, h1⟩
  obtain ⟨y, rfl⟩ := proj_surjective x
  rw [← proj_reflR, show per ψ (proj (fun j => if η j then -y j else y j)) =
    (per ψ ∘ proj) (reflR η y) from rfl, h1, show per ψ (proj y) = (per ψ ∘ proj) y from rfl, h1,
    hψ.parity]

omit [DecidableEq d] in
/-- The lift of a smooth parity function on the torus is a smooth parity function. -/
theorem isParSmooth_comp_proj {c : d → ℂ} {φ : UnitAddTorus d → ℂ} (hφ : IsSmooth φ)
    (hpar : ∀ η x, φ (reflB η x) = sign c η * φ x) : IsParSmooth c (φ ∘ proj) where
  contDiff := hφ
  periodic m y := by simp only [Function.comp_apply, proj_add, proj_intCast, add_zero]
  parity ε y := by
    simp only [Function.comp_apply]
    rw [show reflR ε y = fun j => if ε j then -y j else y j from rfl, proj_reflR, hpar]

/-! ### Weak first-order operators on extensions -/

variable {P : Type*} [Fintype P]

/-- **Weak first-order operators on mirror extensions are Green's formulas on `Q`**. Let
`g = Σ_{c,p} α_{cp} ∂_c f_p` be a first-order operator whose terms all have output parity `cout`
(the parity `cin p` of `f_p` with the parity of `x_c` reversed, whenever `α_{cp} ≠ 0`). Then the
extensions satisfy `ext g = Σ α_{cp} ∂_c (ext f_p)` weakly on `𝕋ᵈ` iff
`Σ_{c,p} α_{cp} ∫_Q f_p ∂_c ψ = -∫_Q g ψ` for every smooth parity function `ψ` with parity
`cout`. For `ψ ∈ C_c^∞(Q)` this is the weak operator on `Q`; the other `ψ` impose the boundary
conditions encoded by the parities. -/
theorem isWeakFO_extL2_iff (α : d → P → ℂ) {cin : P → d → ℂ} (hcin : ∀ p j, cin p j * cin p j = 1)
    {cout : d → ℂ} (hcout : ∀ j, cout j * cout j = 1)
    (hpar : ∀ c p, α c p ≠ 0 → Function.update (cin p) c (-cin p c) = cout)
    (f : P → Domain.L2 ℂ (Q d)) (g : Domain.L2 ℂ (Q d)) :
    IsWeakFO α (fun p => extL2 (hcin p) (f p)) (extL2 hcout g) ↔
      ∀ ψ : (d → ℝ) → ℂ, IsParSmooth cout ψ →
        ∑ c, ∑ p, α c p * ∫ y in Q d, (f p : (d → ℝ) → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
          -∫ y in Q d, (g : (d → ℝ) → ℂ) y * ψ y := by
  have h8 := two_pow_card_ne_zero (d := d)
  -- the pairing of `ext f_p` with `∂_c φ`
  have key : ∀ φ : UnitAddTorus d → ℂ, IsSmooth φ → ∀ c p, α c p *
      ∫ x, (extL2 (hcin p) (f p) : UnitAddTorus d → ℂ) x * partialT c φ x =
        ((2 ^ Fintype.card d : ℝ) : ℂ) * (α c p * ∫ y in Q d, (f p : (d → ℝ) → ℂ) y *
          fderiv ℝ (parProj cout φ ∘ proj) y (Pi.single c 1)) := by
    intro φ hφ c p
    by_cases hα : α c p = 0
    · simp [hα]
    · rw [integral_extL2_mul_partialT (hcin p) (hpar c p hα) (f p) hφ]; ring
  constructor
  · intro h ψ hψ
    obtain ⟨hs, hp, hcomp⟩ := hψ.torus
    have hpt : ∀ y, per ψ (proj y) = ψ y := congrFun hcomp
    have h1 := h (per ψ) hs
    rw [integral_sum_fo α _ hs] at h1
    simp only [key _ hs, integral_extL2_mul_smooth hcout g hs, parProj_of_parity hcout hp,
      hcomp, hpt] at h1
    simp only [← Finset.mul_sum] at h1
    have h2 : ((2 ^ Fintype.card d : ℝ) : ℂ) *
        (∑ c, ∑ p, α c p * ∫ y in Q d, (f p : (d → ℝ) → ℂ) y * fderiv ℝ ψ y (Pi.single c 1)) =
        ((2 ^ Fintype.card d : ℝ) : ℂ) * -∫ y in Q d, (g : (d → ℝ) → ℂ) y * ψ y := by
      rw [h1]; ring
    exact mul_left_cancel₀ h8 h2
  · intro h φ hφ
    have hψ := isParSmooth_comp_proj (isSmooth_parProj cout hφ) (parProj_reflB hcout φ)
    have h1 := h _ hψ
    rw [integral_sum_fo α _ hφ]
    simp only [key _ hφ, integral_extL2_mul_smooth hcout g hφ, ← Finset.mul_sum]
    rw [h1]
    simp only [Function.comp_apply]
    ring

/-! ### Test functions of `Q` are smooth parity functions -/

/-- **`C_c^∞(Q)` lies in every class of smooth parity functions**: the extension by parity
`ext_c Φ` of `Φ ∈ C_c^∞(Q)`, lifted to `ℝᵈ`, is a smooth parity function equal to `Φ` on `Q`. -/
theorem isParSmooth_ext {c : d → ℂ} (hc : ∀ j, c j * c j = 1) {Φ : (d → ℝ) → ℂ}
    (hΦ : Domain.IsTest (Q d) Φ) : IsParSmooth c (ext c Φ ∘ proj) :=
  isParSmooth_comp_proj (isSmooth_ext c hΦ) (ext_reflB hc Φ)

theorem ext_comp_proj_of_mem {c : d → ℂ} {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ)
    {y : d → ℝ} (hy : y ∈ Q d) : (ext c Φ ∘ proj) y = Φ y := by
  simp only [Function.comp_apply]
  rw [ext_of_mem_boxSet hΦ (proj_mem_boxSet (mem_Q.1 hy)), per_proj_of_mem hy]

theorem fderiv_ext_comp_proj_of_mem {c : d → ℂ} {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ)
    {y : d → ℝ} (hy : y ∈ Q d) : fderiv ℝ (ext c Φ ∘ proj) y = fderiv ℝ Φ y :=
  Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_Q.mem_nhds hy)
    fun _ hz => ext_comp_proj_of_mem hΦ hz)

/-- On `Q`, pairings with the extension of a test function are pairings with the test
function. -/
theorem setIntegral_mul_ext {c : d → ℂ} {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ)
    (f : (d → ℝ) → ℂ) :
    ∫ y in Q d, f y * (ext c Φ ∘ proj) y = ∫ y in Q d, f y * Φ y :=
  setIntegral_congr_fun measurableSet_Q fun y hy => by
    rw [ext_comp_proj_of_mem hΦ hy]

theorem setIntegral_mul_fderiv_ext {c : d → ℂ} {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ)
    (f : (d → ℝ) → ℂ) (k : d) :
    ∫ y in Q d, f y * fderiv ℝ (ext c Φ ∘ proj) y (Pi.single k 1) =
      ∫ y in Q d, f y * fderiv ℝ Φ y (Pi.single k 1) :=
  setIntegral_congr_fun measurableSet_Q fun y hy => by
    rw [fderiv_ext_comp_proj_of_mem hΦ hy]


/-! ### Trace test functions -/

/-- The closed cube `Q̄ = [0, ½]ᵈ`. -/
abbrev Qc (d : Type*) : Set (d → ℝ) := Icc 0 fun _ => 1 / 2

/-- **Trace test functions** for the sign vector `c` (`c_j = ±1`): `ψ ∈ C¹(ℝᵈ)` with `ψ = 0` on the
closed faces `{x_j = 0}`, `{x_j = ½}` of `Q̄` for which `c_j = -1`, and no condition on the other
faces. Green's formulas against this class are the weak form of the boundary conditions on the
faces with `c_j = 1` (where the trace of `ψ` is free). -/
structure IsTraceTest (c : d → ℂ) (ψ : (d → ℝ) → ℂ) : Prop where
  contDiff : ContDiff ℝ 1 ψ
  vanish : ∀ j, c j = -1 → ∀ y ∈ Qc d, (y j = 0 ∨ y j = 1 / 2) → ψ y = 0

private theorem sign_single (c : d → ℂ) (j : d) : sign c (fun i => decide (i = j)) = c j := by
  rw [sign, Finset.prod_eq_single j (fun i _ hi => by simp [hi]) (by simp)]; simp

/-- **Smooth parity functions vanish on the faces where they are odd.** -/
theorem IsParSmooth.eq_zero {c : d → ℂ} {ψ : (d → ℝ) → ℂ} (hψ : IsParSmooth c ψ) {j : d}
    (hj : c j = -1) {y : d → ℝ} (hy : y j = 0 ∨ y j = 1 / 2) : ψ y = 0 := by
  have h := hψ.parity (fun i => decide (i = j)) y
  rw [sign_single, hj] at h
  have e : ψ (reflR (fun i => decide (i = j)) y) = ψ y := by
    rcases hy with hy | hy
    · congr 1; funext i; by_cases hi : i = j
      · subst hi; simp [reflR, hy]
      · simp [reflR, hi]
    · rw [show reflR (fun i => decide (i = j)) y =
          y + fun i => ((if i = j then (-1 : ℤ) else 0 : ℤ) : ℝ) by
        funext i; by_cases hi : i = j
        · subst hi; simp [reflR, hy]; norm_num
        · simp [reflR, hi], hψ.periodic]
  rw [e] at h
  linear_combination h / 2

/-- Smooth parity functions are trace test functions. -/
theorem IsParSmooth.isTraceTest {c : d → ℂ} {ψ : (d → ℝ) → ℂ} (hψ : IsParSmooth c ψ) :
    IsTraceTest c ψ :=
  ⟨hψ.contDiff.of_le (by exact_mod_cast le_top), fun _ hj _ _ hy => hψ.eq_zero hj hy⟩

omit [DecidableEq d] in
/-- Test functions of `Q` are trace test functions for every parity. -/
theorem isTraceTest_of_isTest (c : d → ℂ) {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ) :
    IsTraceTest c Φ := by
  refine ⟨hΦ.1.of_le (by exact_mod_cast le_top), fun j _ y _ hy => ?_⟩
  by_contra h
  have := (mem_Q.1 (mem_Q_of_ne_zero hΦ h)) j
  rcases hy with hy | hy <;> rw [hy] at this <;> simp at this

omit [DecidableEq d] in
/-- Complex conjugates of trace test functions are trace test functions. -/
theorem IsTraceTest.star {c : d → ℂ} {ψ : (d → ℝ) → ℂ} (hψ : IsTraceTest c ψ) :
    IsTraceTest c fun y => conj (ψ y) :=
  ⟨Complex.conjCLE.toContinuousLinearMap.contDiff.comp hψ.contDiff,
    fun j hj y hy h => by simp [hψ.vanish j hj y hy h]⟩


/-- **Integration by parts on `Q` in the direction `e_c`** (the divergence theorem on the box
`[0, ½]ⁿ⁺¹`): `∫_Q (∂_c u) v = -∫_Q u ∂_c v` for `C¹` functions whose product vanishes on the two
faces of `Q̄` normal to `e_c`. -/
theorem ibp_Q {n : ℕ} (c : Fin (n + 1)) {u v : (Fin (n + 1) → ℝ) → ℂ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hb : ∀ y ∈ Icc (0 : Fin (n + 1) → ℝ) (fun _ => 1 / 2), (y c = 0 ∨ y c = 1 / 2) →
      u y * v y = 0) :
    ∫ y in Q (Fin (n + 1)), fderiv ℝ u y (Pi.single c 1) * v y =
      -∫ y in Q (Fin (n + 1)), u y * fderiv ℝ v y (Pi.single c 1) := by
  set a : Fin (n + 1) → ℝ := 0
  set b : Fin (n + 1) → ℝ := fun _ => 1 / 2
  have hle : a ≤ b := fun i => by simp [a, b]
  have hQ : Q (Fin (n + 1)) = univ.pi fun i => Ioo (a i) (b i) := by
    simp [Q, openCube, a, b]
  have hae : Q (Fin (n + 1)) =ᵐ[volume] Icc a b := by
    rw [hQ]; exact Measure.univ_pi_Ioo_ae_eq_Icc
  set w : (Fin (n + 1) → ℝ) → ℂ := fun y => u y * v y
  have hw : ContDiff ℝ 1 w := hu.mul hv
  have hdw : ∀ y, HasFDerivAt w (fderiv ℝ w y) y :=
    fun y => (hw.differentiable one_ne_zero y).hasFDerivAt
  have hdw' : ∀ y, fderiv ℝ w y (Pi.single c 1) =
      fderiv ℝ u y (Pi.single c 1) * v y + u y * fderiv ℝ v y (Pi.single c 1) := fun y => by
    have h := ((hu.differentiable one_ne_zero y).hasFDerivAt.mul
      (hv.differentiable one_ne_zero y).hasFDerivAt).fderiv
    change fderiv ℝ (u * v) y (Pi.single c 1) = _
    rw [h]
    simp; ring
  have hcont : Continuous fun y => fderiv ℝ w y (Pi.single c 1) :=
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsum : ∀ y, (∑ i, (if i = c then fderiv ℝ w y else 0) (Pi.single i 1)) =
      fderiv ℝ w y (Pi.single c 1) := fun y => by
    rw [Finset.sum_eq_single c (fun i _ hi => by simp [hi]) (by simp)]; simp
  have key := integral_divergence_of_hasFDerivAt_off_countable' a b hle
    (fun i => if i = c then w else fun _ => 0)
    (fun i y => if i = c then fderiv ℝ w y else 0) ∅ countable_empty
    (fun i => by split_ifs <;> [exact hw.continuous.continuousOn; exact continuousOn_const])
    (fun y _ i => by split_ifs <;> [exact hdw y; exact hasFDerivAt_const _ _])
    (by simp_rw [hsum]; exact hcont.integrableOn_Icc)
  simp_rw [hsum] at key
  have hface : ∀ i : Fin (n + 1), ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (if i = c then w else fun _ => 0) (i.insertNth (b i) x)) -
      ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (if i = c then w else fun _ => 0) (i.insertNth (a i) x)) = 0 := by
    intro i
    by_cases hi : i = c
    · subst hi
      simp only [ite_true]
      rw [setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_zero_of_forall_eq_zero, sub_zero]
      · intro x hx
        exact hb _ (Fin.insertNth_mem_Icc.2 ⟨⟨by simp [a], by simp [a, b]⟩, hx⟩) (Or.inl (by simp [a]))
      · intro x hx
        exact hb _ (Fin.insertNth_mem_Icc.2 ⟨⟨by simp [a, b], le_rfl⟩, hx⟩) (Or.inr (by simp [b]))
    · simp [hi]
  rw [Finset.sum_eq_zero fun i _ => hface i] at key
  have hi1 : IntegrableOn (fun y => fderiv ℝ u y (Pi.single c 1) * v y) (Icc a b) :=
    (((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hv.continuous).integrableOn_Icc
  have hi2 : IntegrableOn (fun y => u y * fderiv ℝ v y (Pi.single c 1)) (Icc a b) :=
    (hu.continuous.mul ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrableOn_Icc
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
  simp_rw [hdw'] at key
  rw [integral_add hi1 hi2] at key
  linear_combination key

section Trace

variable {n : ℕ}

/-- The `L²(Q)` class of a continuous function. -/
def toL2Q {ψ : (Fin (n + 1) → ℝ) → ℂ} (hψ : Continuous ψ) : Domain.L2 ℂ (Q (Fin (n + 1))) :=
  (Domain.memLp_of_continuous measurableSet_Q (isBounded_openCube _ _) hψ).toLp ψ

theorem coe_toL2Q {ψ : (Fin (n + 1) → ℝ) → ℂ} (hψ : Continuous ψ) :
    (toL2Q hψ : (Fin (n + 1) → ℝ) → ℂ) =ᵐ[volume.restrict (Q (Fin (n + 1)))] ψ :=
  MemLp.coeFn_toLp _

theorem setIntegral_toL2Q_mul {ψ : (Fin (n + 1) → ℝ) → ℂ} (hψ : Continuous ψ)
    (G : (Fin (n + 1) → ℝ) → ℂ) :
    ∫ y in Q (Fin (n + 1)), (toL2Q hψ : (Fin (n + 1) → ℝ) → ℂ) y * G y =
      ∫ y in Q (Fin (n + 1)), ψ y * G y :=
  integral_congr_ae ((coe_toL2Q hψ).mono fun y hy => by simp only []; rw [hy])

private theorem update_update_neg (c : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    Function.update (Function.update c k (-c k)) k (-(Function.update c k (-c k)) k) = c := by
  funext j; by_cases h : j = k
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sq_update {c : Fin (n + 1) → ℂ} (hc : ∀ j, c j * c j = 1) (k : Fin (n + 1)) :
    ∀ j, Function.update c k (-c k) j * Function.update c k (-c k) j = 1 := fun j => by
  by_cases h : j = k
  · subst h; simp [hc]
  · simp [Function.update_of_ne h, hc]

private theorem parProj_smul (c : Fin (n + 1) → ℂ) (a : ℂ) (φ : UnitAddTorus (Fin (n + 1)) → ℂ) :
    parProj c (fun x => a * φ x) = fun x => a * parProj c φ x := by
  funext x; simp only [parProj, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ε _ => by ring


theorem IsTraceTest.continuous_fderiv {c : Fin (n + 1) → ℂ} {ψ : (Fin (n + 1) → ℝ) → ℂ}
    (hψ : IsTraceTest c ψ) (k : Fin (n + 1)) :
    Continuous fun y => fderiv ℝ ψ y (Pi.single k 1) :=
  (hψ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem mFourierCoeff_eq_integral_mul (F : UnitAddTorus (Fin (n + 1)) → ℂ) (m : Fin (n + 1) → ℤ) :
    mFourierCoeff F m = ∫ x, F x * mFourier (-m) x := by
  simp only [mFourierCoeff, smul_eq_mul, mul_comm]

/-- **Derivatives of extensions of trace test functions**: for `ψ` a trace test function of parity
`c`, the extension of `∂_k ψ` by the parity `c` with the parity of `x_k` reversed is the weak
derivative `∂_k` of the extension of `ψ` on `𝕋ᵈ`: `(ext ∂_k ψ)^(m) = 2πi m_k (ext ψ)^(m)`. The
boundary terms of the integration by parts on `Q` vanish, since `ψ = 0` on the faces normal to
`e_k` where `c_k = -1`, and the parity function `P_{c'} e_{-m}` vanishes there where `c_k = 1`. -/
theorem mFourierCoeff_extL2_fderiv {c : Fin (n + 1) → ℂ} (hc : ∀ j, c j * c j = 1)
    {ψ : (Fin (n + 1) → ℝ) → ℂ} (hψ : IsTraceTest c ψ) (k : Fin (n + 1)) (m : Fin (n + 1) → ℤ) :
    mFourierCoeff (extL2 (sq_update hc k) (toL2Q (hψ.continuous_fderiv k)) :
        UnitAddTorus (Fin (n + 1)) → ℂ) m =
      2 * Real.pi * Complex.I * m k *
        mFourierCoeff (extL2 hc (toL2Q hψ.contDiff.continuous) : UnitAddTorus (Fin (n + 1)) → ℂ) m := by
  set c' := Function.update c k (-c k)
  have hc' := sq_update hc k
  have he := isSmooth_mFourier (d := Fin (n + 1)) (-m)
  rw [mFourierCoeff_eq_integral_mul, mFourierCoeff_eq_integral_mul,
    integral_extL2_mul_smooth hc' _ he, integral_extL2_mul_smooth hc _ he,
    setIntegral_toL2Q_mul, setIntegral_toL2Q_mul]
  have hχ : IsParSmooth c' (parProj c' (mFourier (-m)) ∘ proj) :=
    isParSmooth_comp_proj (isSmooth_parProj c' he) (parProj_reflB hc' _)
  have hb : ∀ y ∈ Icc (0 : Fin (n + 1) → ℝ) (fun _ => 1 / 2), (y k = 0 ∨ y k = 1 / 2) →
      ψ y * (parProj c' (mFourier (-m)) ∘ proj) y = 0 := by
    intro y hy hk
    rcases mul_self_eq_one_iff.1 (hc k) with h | h
    · rw [hχ.eq_zero (by simp [c', h]) hk, mul_zero]
    · rw [hψ.vanish k h y hy hk, zero_mul]
  have hibp := ibp_Q k hψ.contDiff (hχ.contDiff.of_le (by exact_mod_cast le_top)) hb
  have hd : ∀ y, fderiv ℝ (parProj c' (mFourier (-m)) ∘ proj) y (Pi.single k 1) =
      -(2 * Real.pi * Complex.I * m k) * parProj c (mFourier (-m)) (proj y) := fun y => by
    rw [← partialT_proj ((isSmooth_parProj c' he).contDiff_one.differentiable one_ne_zero),
      partialT_parProj c' he, update_update_neg]
    have : partialT k (mFourier (-m)) = fun x => -(2 * Real.pi * Complex.I * m k) * mFourier (-m) x := by
      funext x; rw [partialT_mFourier]; simp only [Pi.neg_apply, Int.cast_neg]; ring
    rw [this, parProj_smul]
  simp only [Function.comp_apply] at hibp hd
  simp_rw [hd] at hibp
  rw [hibp]
  have : ∫ y in Q (Fin (n + 1)), ψ y * (-(2 * Real.pi * Complex.I * m k) *
      parProj c (mFourier (-m)) (proj y)) = -(2 * Real.pi * Complex.I * m k) *
        ∫ y in Q (Fin (n + 1)), ψ y * parProj c (mFourier (-m)) (proj y) := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  rw [this]; ring


private theorem extL2_congr' {c c' : Fin (n + 1) → ℂ} (h : c = c') (hc : ∀ j, c j * c j = 1)
    (hc' : ∀ j, c' j * c' j = 1) (g : Domain.L2 ℂ (Q (Fin (n + 1)))) :
    extL2 hc g = extL2 hc' g := by
  subst h; rfl

private theorem inner_toL2Q_eq {A : (Fin (n + 1) → ℝ) → ℂ} (hA : Continuous A)
    (g : Domain.L2 ℂ (Q (Fin (n + 1)))) :
    ⟪toL2Q hA, g⟫_ℂ = ∫ y in Q (Fin (n + 1)), (g : (Fin (n + 1) → ℝ) → ℂ) y * conj (A y) := by
  rw [L2.inner_def]
  refine integral_congr_ae ((coe_toL2Q hA).mono fun y hy => ?_)
  simp only [RCLike.inner_apply, hy, mul_comm]

private theorem inner_L2_eq_tsum (A B : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) :
    HasSum (fun k => conj (mFourierCoeff (A : UnitAddTorus (Fin (n + 1)) → ℂ) k) *
      mFourierCoeff (B : UnitAddTorus (Fin (n + 1)) → ℂ) k) ⟪A, B⟫_ℂ := by
  have h := hasSum_prod_mFourierCoeff A B
  rwa [show ∫ t, conj ((A : UnitAddTorus (Fin (n + 1)) → ℂ) t) * B t = ⟪A, B⟫_ℂ by
    rw [L2.inner_def]; simp only [RCLike.inner_apply]; congr 1; funext t; ring] at h

variable {P : Type*} [Fintype P]

/-- **Weak first-order operators on mirror extensions are Green's formulas against trace test
functions.** In the setting of `isWeakFO_extL2_iff`, the weak equation on `𝕋ᵈ` for the extensions
is equivalent to `Σ_{c,p} α_{cp} ∫_Q f_p ∂_c ψ = -∫_Q g ψ` for every `ψ ∈ C¹(ℝᵈ)` vanishing on
the closed faces of `Q̄` normal to the `e_j` with `cout_j = -1` (`IsTraceTest cout ψ`); no
periodicity or reflection symmetry of `ψ` is required. -/
theorem isWeakFO_extL2_iff_trace (α : Fin (n + 1) → P → ℂ) {cin : P → Fin (n + 1) → ℂ}
    (hcin : ∀ p j, cin p j * cin p j = 1) {cout : Fin (n + 1) → ℂ}
    (hcout : ∀ j, cout j * cout j = 1)
    (hpar : ∀ c p, α c p ≠ 0 → Function.update (cin p) c (-cin p c) = cout)
    (f : P → Domain.L2 ℂ (Q (Fin (n + 1)))) (g : Domain.L2 ℂ (Q (Fin (n + 1)))) :
    IsWeakFO α (fun p => extL2 (hcin p) (f p)) (extL2 hcout g) ↔
      ∀ ψ : (Fin (n + 1) → ℝ) → ℂ, IsTraceTest cout ψ →
        ∑ c, ∑ p, α c p * ∫ y in Q (Fin (n + 1)),
            (f p : (Fin (n + 1) → ℝ) → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
          -∫ y in Q (Fin (n + 1)), (g : (Fin (n + 1) → ℝ) → ℂ) y * ψ y := by
  refine ⟨fun h ψ hψ => ?_, fun h =>
    (isWeakFO_extL2_iff α hcin hcout hpar f g).2 fun ψ hψ => h ψ hψ.isTraceTest⟩
  have hF := (isWeakFO_iff α _ _).1 h
  have h8 := two_pow_card_ne_zero (d := Fin (n + 1))
  set N : ℂ := ((2 ^ Fintype.card (Fin (n + 1)) : ℝ) : ℂ)
  set ζ : (Fin (n + 1) → ℝ) → ℂ := fun y => conj (ψ y)
  have hζ : IsTraceTest cout ζ := hψ.star
  have hdζ : ∀ c y, fderiv ℝ ζ y (Pi.single c 1) = conj (fderiv ℝ ψ y (Pi.single c 1)) :=
    fun c y => by
      have : ζ = Complex.conjCLE ∘ ψ := rfl
      rw [this, Complex.conjCLE.comp_fderiv]; rfl
  set Z := extL2 hcout (toL2Q hζ.contDiff.continuous)
  -- the derivative terms
  have hterm : ∀ c p, HasSum (fun k => α c p * (N⁻¹ * (-(2 * Real.pi * Complex.I * k c) *
      conj (mFourierCoeff (Z : UnitAddTorus (Fin (n + 1)) → ℂ) k) *
      mFourierCoeff (extL2 (hcin p) (f p) : UnitAddTorus (Fin (n + 1)) → ℂ) k)))
      (α c p * ∫ y in Q (Fin (n + 1)),
        (f p : (Fin (n + 1) → ℝ) → ℂ) y * fderiv ℝ ψ y (Pi.single c 1)) := by
    intro c p
    by_cases hα : α c p = 0
    · simp only [hα, zero_mul]; exact hasSum_zero
    refine HasSum.mul_left _ ?_
    have hcp : cin p = Function.update cout c (-cout c) := by
      rw [← hpar c p hα, update_update_neg]
    rw [extL2_congr' hcp (hcin p) (sq_update hcout c)]
    have hs := (inner_L2_eq_tsum (extL2 (sq_update hcout c) (toL2Q (hζ.continuous_fderiv c)))
      (extL2 (sq_update hcout c) (f p))).mul_left N⁻¹
    rw [inner_extL2, ← mul_assoc, inv_mul_cancel₀ h8, one_mul, inner_toL2Q_eq] at hs
    simp_rw [mFourierCoeff_extL2_fderiv hcout hζ c, hdζ, Complex.conj_conj] at hs
    convert hs using 2 with k
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
    ring
  have htot := hasSum_sum fun c (_ : c ∈ Finset.univ) =>
    hasSum_sum fun p (_ : p ∈ Finset.univ) => hterm c p
  -- the right-hand side
  have hg := ((inner_L2_eq_tsum Z (extL2 hcout g)).mul_left N⁻¹).neg
  rw [inner_extL2, ← mul_assoc, inv_mul_cancel₀ h8, one_mul, inner_toL2Q_eq] at hg
  simp only [ζ, Complex.conj_conj] at hg
  refine htot.unique (hg.congr_fun fun k => ?_)
  rw [hF k, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **A class of test functions for Green's formulas** on `Q`: the weak first-order equations on
`𝕋ⁿ⁺¹` for mirror extensions are equivalent to the Green's formulas on `Q` tested against the
functions `ψ` with `T cout ψ`. Both the smooth parity functions (`isGreenClass_isParSmooth`) and
the trace test functions (`isGreenClass_isTraceTest`) are such classes. -/
def IsGreenClass (T : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℝ) → ℂ) → Prop) : Prop :=
  ∀ {P : Type} [Fintype P] (α : Fin (n + 1) → P → ℂ) {cin : P → Fin (n + 1) → ℂ}
    (hcin : ∀ p j, cin p j * cin p j = 1) {cout : Fin (n + 1) → ℂ}
    (hcout : ∀ j, cout j * cout j = 1)
    (_ : ∀ c p, α c p ≠ 0 → Function.update (cin p) c (-cin p c) = cout)
    (f : P → Domain.L2 ℂ (Q (Fin (n + 1)))) (g : Domain.L2 ℂ (Q (Fin (n + 1)))),
    IsWeakFO α (fun p => extL2 (hcin p) (f p)) (extL2 hcout g) ↔
      ∀ ψ : (Fin (n + 1) → ℝ) → ℂ, T cout ψ →
        ∑ c, ∑ p, α c p * ∫ y in Q (Fin (n + 1)),
            (f p : (Fin (n + 1) → ℝ) → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
          -∫ y in Q (Fin (n + 1)), (g : (Fin (n + 1) → ℝ) → ℂ) y * ψ y

theorem isGreenClass_isParSmooth : IsGreenClass (n := n) IsParSmooth :=
  fun α _ hcin _ hcout hpar f g => isWeakFO_extL2_iff α hcin hcout hpar f g

theorem isGreenClass_isTraceTest : IsGreenClass (n := n) IsTraceTest :=
  fun α _ hcin _ hcout hpar f g => isWeakFO_extL2_iff_trace α hcin hcout hpar f g

end Trace

end Feec.Models.Cube.MirrorTrace

/-! ### The mirror complex on `Q`: boundary conditions as Green's formulas -/

namespace Feec.Models.Cube.Mirror

open Geometry MirrorExt MirrorTrace Feec.Fourier Feec.Fourier.GradCurl
open Feec.HilbertComplex (totalSub)
open Feec.Models.BoundedDomain (R3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- Graphs of the mirror complex are the graphs of the torus complex along `J`. -/
theorem complexQ_graph_iff {i j : Fin 3} (x : SpaceQ i) (y : SpaceQ j) :
    (∃ h : x ∈ (complexQ.d i j).domain, complexQ.d i j ⟨x, h⟩ = y) ↔
      ∃ h : J i x ∈ (Models.Torus.GradCurl.complex.d i j).domain,
        Models.Torus.GradCurl.complex.d i j ⟨J i x, h⟩ = J j y := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨_, (J_complexQ_d ⟨x, h⟩).symm⟩
  · rintro ⟨h, e⟩
    exact ⟨mem_complexQ_domain_iff.2 h, embeddingQ.J_injective j ((J_complexQ_d _).trans e)⟩

/-- Graphs of the adjoints of the mirror complex are those of the torus adjoints along `J`. -/
theorem complexQ_adjoint_graph_iff {i j : Fin 3} (y : SpaceQ j) (x : SpaceQ i) :
    (∃ h : y ∈ ((complexQ.d i j)†).domain, (complexQ.d i j)† ⟨y, h⟩ = x) ↔
      ∃ h : J j y ∈ ((Models.Torus.GradCurl.complex.d i j)†).domain,
        (Models.Torus.GradCurl.complex.d i j)† ⟨J j y, h⟩ = J i x := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨_, (J_complexQ_adjoint ⟨y, h⟩).symm⟩
  · rintro ⟨h, e⟩
    exact ⟨mem_complexQ_adjoint_domain_iff.2 h,
      embeddingQ.J_injective i ((J_complexQ_adjoint _).trans e)⟩

/-- **`d₀` of the mirror complex is the gradient with the mirror condition `σ · n = 0`**, as a
Green's formula: `σ ∈ D(d₀)` with `d₀ σ = G` iff for all `a, b` and every test function `ψ` of
a Green class `T` (`MirrorTrace.IsGreenClass`) with the parity `cE (a, b)` of `G_{ab}`,
`∫_Q σ_a ∂_b ψ = -∫_Q G_{ab} ψ`. For the trace test functions (`complexQ_d₀_iff`): for
`ψ ∈ C_c^∞(Q)` this says `G = ∇σ` weakly; for `b = a`, `ψ` is free on every face and the boundary
term `∫_{x_a ∈ {0, ½}} σ_a ψ` imposes `σ_a = 0` on the faces normal to `e_a`; for `b ≠ a`, `ψ`
vanishes on the faces normal to `e_b`, where the boundary term lives, and no condition is
imposed. -/
theorem complexQ_d₀_iff_of {T : (Fin 3 → ℂ) → (R3 → ℂ) → Prop}
    (hT : IsGreenClass T) (σ : VQ) (G : MQ) :
    (∃ h : σ ∈ (complexQ.d 0 1).domain, complexQ.d 0 1 ⟨σ, h⟩ = G) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, T (cE (a, b)) ψ →
        ∫ y in Q (Fin 3), (σ a : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single b 1) =
          -∫ y in Q (Fin 3), (G (a, b) : R3 → ℂ) y * ψ y := by
  refine (complexQ_graph_iff (i := 0) (j := 1) σ G).trans ?_
  refine (Models.Torus.GradCurl.mem_domain_grad_iff_weak (extPi cV_sq σ) (extPi cE_sq G)).trans ?_
  refine ⟨fun h a b ψ hψ => ?_, fun h ⟨a, b⟩ => ?_⟩
  · have e := (hT _ cV_sq (cE_sq (a, b)) (fun c p hα => by
      simp [gradCurl_m01, grad_apply, PiLp.single_apply] at hα
      obtain ⟨rfl, rfl⟩ := hα
      exact (cE_eq_update _ _).symm) (fun p => σ p) (G (a, b))).1 (h (a, b)) ψ hψ
    simp [gradCurl_m01, grad_apply, PiLp.single_apply, Fin.sum_univ_three] at e
    fin_cases b <;> simp at e ⊢ <;> linear_combination e
  · refine (hT _ cV_sq (cE_sq (a, b)) (fun c p hα => by
      simp [gradCurl_m01, grad_apply, PiLp.single_apply] at hα
      obtain ⟨rfl, rfl⟩ := hα
      exact (cE_eq_update _ _).symm) (fun p => σ p) (G (a, b))).2 fun ψ hψ => ?_
    have e := h a b ψ hψ
    simp [gradCurl_m01, grad_apply, PiLp.single_apply, Fin.sum_univ_three]
    fin_cases b <;> simp at e ⊢ <;> linear_combination e

/-! #### The symbols -/

theorem neg_I_mul_curl_single (c a b : Fin 3) (p : Fin 3 × Fin 3) :
    -Complex.I * curl (EuclideanSpace.single c 1) (EuclideanSpace.single p 1) (a, b) =
      if p.1 = a then leviCivita3 ℂ b c p.2 else 0 := by
  rw [curl_apply]
  obtain ⟨p1, p2⟩ := p
  have hI : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  simp only [PiLp.single_apply, Prod.mk.injEq]
  by_cases h : p1 = a
  · subst h
    simp only [true_and, ite_true]
    rw [← mul_assoc, hI, one_mul]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_eq_single c]
    · simp
    · intro x _ hx; simp [hx]
    · simp
  · simp [h, Ne.symm h]

theorem leviCivita3_ne_zero {b c d : Fin 3} (h : leviCivita3 ℂ b c d ≠ 0) :
    (c = b + 1 ∧ d = b + 2) ∨ (c = b + 2 ∧ d = b + 1) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [leviCivita3_apply] at h ⊢

theorem sum_curl_coeff (a b : Fin 3) (X : Fin 3 → Fin 3 × Fin 3 → ℂ) :
    ∑ c, ∑ p : Fin 3 × Fin 3, (if p.1 = a then leviCivita3 ℂ b c p.2 else 0) * X c p =
      X (b + 1) (a, b + 2) - X (b + 2) (a, b + 1) := by
  simp only [Fintype.sum_prod_type, ite_mul, zero_mul]
  fin_cases b <;> simp [Fin.sum_univ_three, leviCivita3_apply] <;> ring

theorem neg_I_mul_div_single (c a : Fin 3) (p : Fin 3 × Fin 3) :
    -Complex.I * div (EuclideanSpace.single c 1) (EuclideanSpace.single p 1) a =
      if p = (a, c) then -1 else 0 := by
  rw [div_apply]
  obtain ⟨p1, p2⟩ := p
  have hI : -Complex.I * -Complex.I = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
  rw [← mul_assoc, hI]
  simp only [PiLp.single_apply, Prod.mk.injEq]
  by_cases h : p1 = a
  · subst h
    simp only [true_and]
    rw [Finset.sum_eq_single p2]
    · by_cases h2 : p2 = c
      · subst h2; simp
      · simp [h2]
    · intro x _ hx; simp [hx]
    · simp
  · simp [h, Ne.symm h]

theorem sum_div_coeff (a : Fin 3) (X : Fin 3 → Fin 3 × Fin 3 → ℂ) :
    ∑ c, ∑ p : Fin 3 × Fin 3, (if p = (a, c) then -1 else 0) * X c p = -∑ c, X c (a, c) := by
  simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_neg_distrib]

/-- **`d₁` of the mirror complex is the row-wise curl with the mirror condition `E_{nτ} = 0`**:
`E ∈ D(d₁)` with `d₁ E = C` iff for all `a, b` and every test function `ψ` of a Green class `T` with the
parity `cB (a, b)` of `C_{ab}`,
`∫_Q (E_{a,b+2} ∂_{b+1} ψ - E_{a,b+1} ∂_{b+2} ψ) = -∫_Q C_{ab} ψ`. The free traces of `ψ` sit
on the faces `x_a ∈ {0, ½}` (for `b + 1 = a` or `b + 2 = a`), which imposes that the tangential
components `E_{ac}`, `c ≠ a`, of row `a` vanish on the faces normal to `e_a`; on the other faces
`ψ` vanishes and no condition is imposed. -/
theorem complexQ_d₁_iff_of {T : (Fin 3 → ℂ) → (R3 → ℂ) → Prop}
    (hT : IsGreenClass T) (E C : MQ) :
    (∃ h : E ∈ (complexQ.d 1 2).domain, complexQ.d 1 2 ⟨E, h⟩ = C) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, T (cB (a, b)) ψ →
        (∫ y in Q (Fin 3), (E (a, b + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 1) 1)) -
          ∫ y in Q (Fin 3), (E (a, b + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 2) 1) =
          -∫ y in Q (Fin 3), (C (a, b) : R3 → ℂ) y * ψ y := by
  refine (complexQ_graph_iff (i := 1) (j := 2) E C).trans ?_
  refine (Models.Torus.GradCurl.mem_domain_curl_iff_weak (extPi cE_sq E) (extPi cB_sq C)).trans ?_
  have hpar : ∀ a b, ∀ c (p : Fin 3 × Fin 3),
      (if p.1 = a then leviCivita3 ℂ b c p.2 else 0) ≠ 0 →
        Function.update (cE p) c (-cE p c) = cB (a, b) := by
    intro a b c p hα
    obtain ⟨p1, p2⟩ := p
    split_ifs at hα with h1
    · subst h1
      rcases leviCivita3_ne_zero hα with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (cB_eq_update₁ _ _).symm
      · exact (cB_eq_update₂ _ _).symm
    · exact absurd rfl hα
  refine ⟨fun h a b ψ hψ => ?_, fun h ⟨a, b⟩ => ?_⟩
  · have e := (hT _ cE_sq (cB_sq (a, b)) (fun c p hα => by
      simp only [gradCurl_m12, neg_I_mul_curl_single] at hα
      exact hpar a b c p hα) (fun p => E p) (C (a, b))).1 (h (a, b)) ψ hψ
    simp only [gradCurl_m12, neg_I_mul_curl_single] at e
    rw [sum_curl_coeff a b (fun c p =>
      ∫ y in Q (Fin 3), (E p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))] at e
    exact e
  · refine (hT _ cE_sq (cB_sq (a, b)) (fun c p hα => by
      simp only [gradCurl_m12, neg_I_mul_curl_single] at hα
      exact hpar a b c p hα) (fun p => E p) (C (a, b))).2 fun ψ hψ => ?_
    simp only [gradCurl_m12, neg_I_mul_curl_single]
    rw [sum_curl_coeff a b (fun c p =>
      ∫ y in Q (Fin 3), (E p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))]
    exact h a b ψ hψ

/-- **`d₀†` of the mirror complex is `-div` with the mirror condition `E_{τn} = 0`**:
`M ∈ D(d₀†)` with `d₀† M = D` iff for all `a` and every test function `ψ` of a Green class `T` with the
parity `cV a` of `D_a`, `Σ_c ∫_Q M_{ac} ∂_c ψ = ∫_Q D_a ψ`. The free traces of `ψ` sit on the
faces `x_c ∈ {0, ½}`, `c ≠ a`, which imposes `M_{ac} = 0` there (the off-diagonal normal
components vanish). -/
theorem complexQ_adjoint_d₀_iff_of {T : (Fin 3 → ℂ) → (R3 → ℂ) → Prop}
    (hT : IsGreenClass T) (M : MQ) (D : VQ) :
    (∃ h : M ∈ ((complexQ.d 0 1)†).domain, (complexQ.d 0 1)† ⟨M, h⟩ = D) ↔
      ∀ a : Fin 3, ∀ ψ : R3 → ℂ, T (cV a) ψ →
        ∑ c, ∫ y in Q (Fin 3), (M (a, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
          ∫ y in Q (Fin 3), (D a : R3 → ℂ) y * ψ y := by
  refine (complexQ_adjoint_graph_iff (i := 0) (j := 1) M D).trans ?_
  refine (Models.Torus.GradCurl.mem_domain_adjoint_grad_iff_weak (extPi cE_sq M)
    (extPi cV_sq D)).trans ?_
  have hpar : ∀ a, ∀ c (p : Fin 3 × Fin 3), (if p = (a, c) then (-1 : ℂ) else 0) ≠ 0 →
      Function.update (cE p) c (-cE p c) = cV a := by
    intro a c p hα
    split_ifs at hα with h1
    · subst h1; exact (cV_eq_update _ _).symm
    · exact absurd rfl hα
  refine ⟨fun h a ψ hψ => ?_, fun h a => ?_⟩
  · have e := (hT _ cE_sq (cV_sq a) (fun c p hα => by
      simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single] at hα
      exact hpar a c p hα) (fun p => M p) (D a)).1 (h a) ψ hψ
    simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single] at e
    rw [sum_div_coeff a (fun c p =>
      ∫ y in Q (Fin 3), (M p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))] at e
    exact neg_inj.1 e
  · refine (hT _ cE_sq (cV_sq a) (fun c p hα => by
      simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single] at hα
      exact hpar a c p hα) (fun p => M p) (D a)).2 fun ψ hψ => ?_
    simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single]
    rw [sum_div_coeff a (fun c p =>
      ∫ y in Q (Fin 3), (M p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1)), h a ψ hψ]

/-- The adjoint of the torus curl is the torus curl (`curl_ξ† = curl_ξ`). -/
theorem adjoint_torus_curl : (Models.Torus.GradCurl.complex.d 1 2)† =
    Operator.mulOp Measure.count fun n => gradCurl.m 1 2 (Fourier.Torus.freq n) := by
  rw [show (Models.Torus.GradCurl.complex.d 1 2)† = Operator.mulOp Measure.count fun n =>
      ContinuousLinearMap.adjoint (gradCurl.m 1 2 (Fourier.Torus.freq n)) from
    (Fourier.Torus.symbolComplex gradCurl).adjoint_d 1 2]
  congr 1
  funext n
  exact adjoint_curl _

/-- **`d₁†` of the mirror complex is the row-wise curl with the complementary mirror condition
`B_{ττ} = 0`**: `B ∈ D(d₁†)` with `d₁† B = C` iff for all `a, b` and every test function `ψ` of
a Green class `T` with the parity `cE (a, b)` of `C_{ab}`,
`∫_Q (B_{a,b+2} ∂_{b+1} ψ - B_{a,b+1} ∂_{b+2} ψ) = -∫_Q C_{ab} ψ`. On a face normal to `e_k`, `ψ`
has a free trace exactly when `a ≠ k`, and the boundary term then involves `B_{ad}` with
`a, d ≠ k`: every tangential–tangential component of `B` vanishes on the faces. -/
theorem complexQ_adjoint_d₁_iff_of {T : (Fin 3 → ℂ) → (R3 → ℂ) → Prop}
    (hT : IsGreenClass T) (B C : MQ) :
    (∃ h : B ∈ ((complexQ.d 1 2)†).domain, (complexQ.d 1 2)† ⟨B, h⟩ = C) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, T (cE (a, b)) ψ →
        (∫ y in Q (Fin 3), (B (a, b + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 1) 1)) -
          ∫ y in Q (Fin 3), (B (a, b + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 2) 1) =
          -∫ y in Q (Fin 3), (C (a, b) : R3 → ℂ) y * ψ y := by
  refine (complexQ_adjoint_graph_iff (i := 1) (j := 2) B C).trans ?_
  have hJ : ∀ x : MQ, J 2 x = Fourier.Torus.fieldFourier _ _ (extPi cB_sq x) := fun _ => rfl
  have hJ' : ∀ x : MQ, J 1 x = Fourier.Torus.fieldFourier _ _ (extPi cE_sq x) := fun _ => rfl
  rw [adjoint_torus_curl, hJ, hJ']
  refine (TorusWeak.mem_graph_iff_isWeak Models.Torus.GradCurl.curl_isLinear
    (extPi cB_sq B) (extPi cE_sq C)).trans ?_
  have hpar : ∀ a b, ∀ c (p : Fin 3 × Fin 3),
      (if p.1 = a then leviCivita3 ℂ b c p.2 else 0) ≠ 0 →
        Function.update (cB p) c (-cB p c) = cE (a, b) := by
    intro a b c p hα
    obtain ⟨p1, p2⟩ := p
    split_ifs at hα with h1
    · subst h1
      rcases leviCivita3_ne_zero hα with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (cE_eq_update₁ _ _).symm
      · exact (cE_eq_update₂ _ _).symm
    · exact absurd rfl hα
  refine ⟨fun h a b ψ hψ => ?_, fun h ⟨a, b⟩ => ?_⟩
  · have e := (hT _ cB_sq (cE_sq (a, b)) (fun c p hα => by
      simp only [gradCurl_m12, neg_I_mul_curl_single] at hα
      exact hpar a b c p hα) (fun p => B p) (C (a, b))).1 (h (a, b)) ψ hψ
    simp only [gradCurl_m12, neg_I_mul_curl_single] at e
    rw [sum_curl_coeff a b (fun c p =>
      ∫ y in Q (Fin 3), (B p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))] at e
    exact e
  · refine (hT _ cB_sq (cE_sq (a, b)) (fun c p hα => by
      simp only [gradCurl_m12, neg_I_mul_curl_single] at hα
      exact hpar a b c p hα) (fun p => B p) (C (a, b))).2 fun ψ hψ => ?_
    simp only [gradCurl_m12, neg_I_mul_curl_single]
    rw [sum_curl_coeff a b (fun c p =>
      ∫ y in Q (Fin 3), (B p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))]
    exact h a b ψ hψ

/-! #### The four operators against trace test functions and against smooth parity functions -/

/-- **`d₀` with `σ · n = 0` as Green's formulas against `C¹` trace test functions.** -/
theorem complexQ_d₀_iff (σ : VQ) (G : MQ) :
    (∃ h : σ ∈ (complexQ.d 0 1).domain, complexQ.d 0 1 ⟨σ, h⟩ = G) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cE (a, b)) ψ →
        ∫ y in Q (Fin 3), (σ a : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single b 1) =
          -∫ y in Q (Fin 3), (G (a, b) : R3 → ℂ) y * ψ y :=
  complexQ_d₀_iff_of isGreenClass_isTraceTest σ G

/-- **`d₁` with `E_{nτ} = 0` as Green's formulas against `C¹` trace test functions.** -/
theorem complexQ_d₁_iff (E C : MQ) :
    (∃ h : E ∈ (complexQ.d 1 2).domain, complexQ.d 1 2 ⟨E, h⟩ = C) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cB (a, b)) ψ →
        (∫ y in Q (Fin 3), (E (a, b + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 1) 1)) -
          ∫ y in Q (Fin 3), (E (a, b + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 2) 1) =
          -∫ y in Q (Fin 3), (C (a, b) : R3 → ℂ) y * ψ y :=
  complexQ_d₁_iff_of isGreenClass_isTraceTest E C

/-- **`d₀†` with `E_{τn} = 0` as Green's formulas against `C¹` trace test functions.** -/
theorem complexQ_adjoint_d₀_iff (M : MQ) (D : VQ) :
    (∃ h : M ∈ ((complexQ.d 0 1)†).domain, (complexQ.d 0 1)† ⟨M, h⟩ = D) ↔
      ∀ a : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cV a) ψ →
        ∑ c, ∫ y in Q (Fin 3), (M (a, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
          ∫ y in Q (Fin 3), (D a : R3 → ℂ) y * ψ y :=
  complexQ_adjoint_d₀_iff_of isGreenClass_isTraceTest M D

/-- **`d₁†` with `B_{ττ} = 0` as Green's formulas against `C¹` trace test functions.** -/
theorem complexQ_adjoint_d₁_iff (B C : MQ) :
    (∃ h : B ∈ ((complexQ.d 1 2)†).domain, (complexQ.d 1 2)† ⟨B, h⟩ = C) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cE (a, b)) ψ →
        (∫ y in Q (Fin 3), (B (a, b + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 1) 1)) -
          ∫ y in Q (Fin 3), (B (a, b + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 2) 1) =
          -∫ y in Q (Fin 3), (C (a, b) : R3 → ℂ) y * ψ y :=
  complexQ_adjoint_d₁_iff_of isGreenClass_isTraceTest B C

/-- `d₀` against smooth parity functions (the method-of-images form). -/
theorem complexQ_d₀_iff_isParSmooth (σ : VQ) (G : MQ) :
    (∃ h : σ ∈ (complexQ.d 0 1).domain, complexQ.d 0 1 ⟨σ, h⟩ = G) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cE (a, b)) ψ →
        ∫ y in Q (Fin 3), (σ a : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single b 1) =
          -∫ y in Q (Fin 3), (G (a, b) : R3 → ℂ) y * ψ y :=
  complexQ_d₀_iff_of isGreenClass_isParSmooth σ G

/-- `d₁` against smooth parity functions. -/
theorem complexQ_d₁_iff_isParSmooth (E C : MQ) :
    (∃ h : E ∈ (complexQ.d 1 2).domain, complexQ.d 1 2 ⟨E, h⟩ = C) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cB (a, b)) ψ →
        (∫ y in Q (Fin 3), (E (a, b + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 1) 1)) -
          ∫ y in Q (Fin 3), (E (a, b + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 2) 1) =
          -∫ y in Q (Fin 3), (C (a, b) : R3 → ℂ) y * ψ y :=
  complexQ_d₁_iff_of isGreenClass_isParSmooth E C

/-- `d₀†` against smooth parity functions. -/
theorem complexQ_adjoint_d₀_iff_isParSmooth (M : MQ) (D : VQ) :
    (∃ h : M ∈ ((complexQ.d 0 1)†).domain, (complexQ.d 0 1)† ⟨M, h⟩ = D) ↔
      ∀ a : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cV a) ψ →
        ∑ c, ∫ y in Q (Fin 3), (M (a, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
          ∫ y in Q (Fin 3), (D a : R3 → ℂ) y * ψ y :=
  complexQ_adjoint_d₀_iff_of isGreenClass_isParSmooth M D

/-- `d₁†` against smooth parity functions. -/
theorem complexQ_adjoint_d₁_iff_isParSmooth (B C : MQ) :
    (∃ h : B ∈ ((complexQ.d 1 2)†).domain, (complexQ.d 1 2)† ⟨B, h⟩ = C) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cE (a, b)) ψ →
        (∫ y in Q (Fin 3), (B (a, b + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 1) 1)) -
          ∫ y in Q (Fin 3), (B (a, b + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 2) 1) =
          -∫ y in Q (Fin 3), (C (a, b) : R3 → ℂ) y * ψ y :=
  complexQ_adjoint_d₁_iff_of isGreenClass_isParSmooth B C

/-! #### The data space of Prop 4.17 with mirror boundary conditions, by Green's formulas -/

/-- `G = ∇σ` on `Q` with `σ · n = 0`, as Green's formulas against the `C¹` trace test functions. -/
def GradTrace (σ : VQ) (G : MQ) : Prop :=
  ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cE (a, b)) ψ →
    ∫ y in Q (Fin 3), (σ a : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single b 1) =
      -∫ y in Q (Fin 3), (G (a, b) : R3 → ℂ) y * ψ y

/-- **`GradTrace` contains the weak gradient**: tested against `C_c^∞(Q)`, `GradTrace σ G` says
`G_{ab} = ∂_b σ_a` weakly in `Q`. -/
theorem GradTrace.weak {σ : VQ} {G : MQ} (h : GradTrace σ G) (a b : Fin 3) {Φ : R3 → ℂ}
    (hΦ : Domain.IsTest (Q (Fin 3)) Φ) :
    ∫ y in Q (Fin 3), (σ a : R3 → ℂ) y * fderiv ℝ Φ y (Pi.single b 1) =
      -∫ y in Q (Fin 3), (G (a, b) : R3 → ℂ) y * Φ y :=
  h a b Φ (isTraceTest_of_isTest _ hΦ)

/-- `C = curl E` (row-wise) on `Q`, with the boundary condition encoded by the parities `c` of
`C` (`cB` for `E_{nτ} = 0`, `cE` for `B_{ττ} = 0`), as Green's formulas against the `C¹` trace
test functions. -/
def CurlTrace (c : Fin 3 × Fin 3 → Fin 3 → ℂ) (E C : MQ) : Prop :=
  ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (c (a, b)) ψ →
    (∫ y in Q (Fin 3), (E (a, b + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 1) 1)) -
      ∫ y in Q (Fin 3), (E (a, b + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 2) 1) =
      -∫ y in Q (Fin 3), (C (a, b) : R3 → ℂ) y * ψ y

/-- `D = -div M` (row-wise) on `Q` with `M_{τn} = 0`, as Green's formulas against the `C¹` trace
test functions. -/
def DivTrace (M : MQ) (D : VQ) : Prop :=
  ∀ a : Fin 3, ∀ ψ : R3 → ℂ, IsTraceTest (cV a) ψ →
    ∑ c, ∫ y in Q (Fin 3), (M (a, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
      ∫ y in Q (Fin 3), (D a : R3 → ℂ) y * ψ y

/-- **The data space `D(L)` of the mirror complex by Green's formulas**: `(σ, E, B) ∈ D(L)` iff
`∇σ ∈ L²` with `σ · n = 0`, `curl E ∈ L²` with `E_{nτ} = 0`, `div E ∈ L²` with `E_{τn} = 0`, and
`curl B ∈ L²` with `B_{ττ} = 0`, each in the weak form `GradTrace`, `CurlTrace cB`, `DivTrace`,
`CurlTrace cE`. -/
theorem mem_wave_domain_iff_trace (U : PiLp 2 SpaceQ) :
    U ∈ complexQ.wave.domain ↔
      (∃ G, GradTrace (U 0) G) ∧ (∃ C, CurlTrace cB (U 1) C) ∧ (∃ D, DivTrace (U 1) D) ∧
        ∃ C, CurlTrace cE (U 2) C := by
  constructor
  · intro hU
    have h := (HilbertComplex.mem_wave_domain _).1 hU
    exact ⟨⟨_, (complexQ_d₀_iff (U 0) _).1 ⟨h.1 0 1, rfl⟩⟩,
      ⟨_, (complexQ_d₁_iff (U 1) _).1 ⟨h.1 1 2, rfl⟩⟩,
      ⟨_, (complexQ_adjoint_d₀_iff (U 1) _).1 ⟨h.2 0 1, rfl⟩⟩,
      ⟨_, (complexQ_adjoint_d₁_iff (U 2) _).1 ⟨h.2 1 2, rfl⟩⟩⟩
  · rintro ⟨⟨G, hG⟩, ⟨C, hC⟩, ⟨D, hD⟩, ⟨C', hC'⟩⟩
    exact HilbertComplex.mem_wave_domain_fin3 _ ((complexQ_d₀_iff _ _).2 hG).1
      ((complexQ_d₁_iff _ _).2 hC).1 ((complexQ_adjoint_d₀_iff _ _).2 hD).1
      ((complexQ_adjoint_d₁_iff _ _).2 hC').1

/-- **Prop 4.17 on `Q = (0, ½)³` with the mirror boundary conditions as trace conditions**: for
a datum `U₀ = (σ₀, E₀, B₀)` satisfying the Green's formulas of `mem_wave_domain_iff_trace`
(`σ₀ · n = 0`, `E₀`: `E_{nτ} = 0` and `E_{τn} = 0`, `B₀`: `B_{ττ} = 0`) and lying in the
constraint `{0} × TSD × TSD`, and admissible forcing in the constraint, the Hodge wave equation
has a classical solution, unique among strong solutions, which stays in the constraint.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem existsUnique_memQ_trace {U₀ : PiLp 2 SpaceQ}
    (hU₀ : (∃ G, GradTrace (U₀ 0) G) ∧ (∃ C, CurlTrace cB (U₀ 1) C) ∧ (∃ D, DivTrace (U₀ 1) D) ∧
      ∃ C, CurlTrace cE (U₀ 2) C)
    (hU₀S : U₀ ∈ totalSub tsdQ) {F : ℝ → PiLp 2 SpaceQ} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complexQ.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complexQ.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub tsdQ) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complexQ.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  existsUnique_memQ ((mem_wave_domain_iff_trace U₀).2 hU₀) hU₀S hF hFS


/-! ### Every open cube: the mirror conditions as trace conditions -/

section CubeTrace

variable {b : R3} {s : ℝ} (hs : 0 < s)

/-- The map `T x = (x - b)/(2s)` of the cube `∏ (bᵢ, bᵢ + s)` onto `Q`. -/
abbrev cubeMap (b : R3) (s : ℝ) : R3 → R3 := Domain.aff (2 * s)⁻¹ (-((2 * s)⁻¹ • b))

theorem cubeMap_apply (b : R3) (s : ℝ) (x : R3) (j : Fin 3) :
    cubeMap b s x j = (x j - b j) / (2 * s) := by
  simp [Domain.aff]; ring

theorem cubeMap_aff (hs : 0 < s) (b : R3) (y : R3) : cubeMap b s (Domain.aff (2 * s) b y) = y :=
  Domain.aff_inv (by positivity) b y

private theorem aff_apply' (a : ℝ) (b y : R3) (j : Fin 3) : Domain.aff a b y j = a * y j + b j := by
  simp [Domain.aff]

/-- **Trace test functions on the cube** `∏ (bᵢ, bᵢ + s)` for the parity `c`: `φ ∈ C¹(ℝ³)` with
`φ = 0` on the closed faces `{x_j = b_j}`, `{x_j = b_j + s}` of the closed cube for which
`c_j = -1`. -/
structure IsTraceTestCube (b : R3) (s : ℝ) (c : Fin 3 → ℂ) (φ : R3 → ℂ) : Prop where
  contDiff : ContDiff ℝ 1 φ
  vanish : ∀ j, c j = -1 → ∀ x ∈ Icc b (b + fun _ => s), (x j = b j ∨ x j = b j + s) → φ x = 0

include hs in
/-- Trace test functions on `Q` transplant to trace test functions on the cube. -/
theorem isTraceTestCube_comp_cubeMap {c : Fin 3 → ℂ} {ψ : R3 → ℂ} (hψ : IsTraceTest c ψ) :
    IsTraceTestCube b s c (ψ ∘ cubeMap b s) := by
  have h2s : 0 < 2 * s := by positivity
  refine ⟨hψ.contDiff.comp ((Domain.contDiff_aff _ _).of_le (by exact_mod_cast le_top)),
    fun j hj x hx hxj => hψ.vanish j hj _ ⟨fun i => ?_, fun i => ?_⟩ ?_⟩
  · have := hx.1 i
    simp only [Pi.zero_apply, cubeMap_apply]
    exact div_nonneg (by linarith) h2s.le
  · have := hx.2 i
    simp only [Pi.add_apply] at this
    rw [cubeMap_apply, div_le_iff₀ h2s]; linarith
  · rcases hxj with h | h
    · left; rw [cubeMap_apply, h, sub_self, zero_div]
    · right; rw [cubeMap_apply, h]; field_simp; ring

include hs in
/-- Trace test functions on the cube transplant to trace test functions on `Q`. -/
theorem IsTraceTestCube.comp_aff {c : Fin 3 → ℂ} {φ : R3 → ℂ} (hφ : IsTraceTestCube b s c φ) :
    IsTraceTest c (φ ∘ Domain.aff (2 * s) b) := by
  have h2s : 0 < 2 * s := by positivity
  refine ⟨hφ.contDiff.comp ((Domain.contDiff_aff _ _).of_le (by exact_mod_cast le_top)),
    fun j hj y hy hyj => hφ.vanish j hj _ ⟨fun i => ?_, fun i => ?_⟩ ?_⟩
  · have := hy.1 i
    simp only [Pi.zero_apply] at this
    rw [aff_apply']; nlinarith
  · have := hy.2 i
    simp only [Pi.add_apply]
    rw [aff_apply']; nlinarith
  · rcases hyj with h | h
    · left; rw [aff_apply', h]; ring
    · right; rw [aff_apply', h]; field_simp; ring

theorem comp_aff_cubeMap (hs : 0 < s) (φ : R3 → ℂ) :
    (φ ∘ Domain.aff (2 * s) b) ∘ cubeMap b s = φ := by
  funext x; simp only [Function.comp_apply]
  rw [Domain.aff_inv' (E := R3) (a := 2 * s) (by positivity) b x]


/-- The Jacobian factor `|2s|³` of `T⁻¹`, as the inverse Jacobian of `T`. -/
abbrev jacCube (s : ℝ) : ℂ := (((Domain.jac (E := R3) (2 * s)⁻¹)⁻¹ : ℝ) : ℂ)

theorem jacCube_ne_zero (hs : 0 < s) : jacCube s ≠ 0 :=
  RCLike.ofReal_ne_zero.2 (jac_inv_pos hs).ne'

private theorem two_s_ne_zero (hs : 0 < s) : ((2 * s : ℝ) : ℂ) ≠ 0 :=
  RCLike.ofReal_ne_zero.2 (mul_pos two_pos hs).ne'

/-- **Pairings on the cube by change of variables**: `∫_C (u ∘ T) (ψ ∘ T) = |2s|³ ∫_Q u ψ`. -/
theorem setIntegral_pullCube_mul {P : Type*} [Fintype P] (u : Domain.L2F ℂ (Q (Fin 3)) P) (p : P)
    (ψ : R3 → ℂ) :
    ∫ x in Geometry.openCube b s, (pullCube b s hs P u p : R3 → ℂ) x * (ψ ∘ cubeMap b s) x =
      jacCube s * ∫ y in Q (Fin 3), (u p : R3 → ℂ) y * ψ y :=
  Domain.setIntegral_pull_mul (inv_two_mul_ne hs) (-((2 * s)⁻¹ • b)) Geometry.measurableSet_Q
    (preimage_aff_Q hs b) (u p) ψ

theorem fderiv_comp_cubeMap {ψ : R3 → ℂ} (hψ : ContDiff ℝ 1 ψ) (x : R3) (k : Fin 3) :
    fderiv ℝ (ψ ∘ cubeMap b s) x (Pi.single k 1) =
      (((2 * s)⁻¹ : ℝ) : ℂ) * fderiv ℝ ψ (cubeMap b s x) (Pi.single k 1) := by
  rw [((hψ.differentiable one_ne_zero _).hasFDerivAt.comp x
    (Domain.hasFDerivAt_aff _ _ x)).fderiv, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul, Complex.real_smul]

/-- **Derivative pairings on the cube by change of variables**:
`∫_C (u ∘ T) ∂_k (ψ ∘ T) = (2s)⁻¹ |2s|³ ∫_Q u ∂_k ψ`. -/
theorem setIntegral_pullCube_mul_fderiv {P : Type*} [Fintype P] (u : Domain.L2F ℂ (Q (Fin 3)) P)
    (p : P) {ψ : R3 → ℂ} (hψ : ContDiff ℝ 1 ψ) (k : Fin 3) :
    ∫ x in Geometry.openCube b s, (pullCube b s hs P u p : R3 → ℂ) x *
        fderiv ℝ (ψ ∘ cubeMap b s) x (Pi.single k 1) =
      (((2 * s)⁻¹ : ℝ) : ℂ) * (jacCube s *
        ∫ y in Q (Fin 3), (u p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single k 1)) := by
  simp_rw [fderiv_comp_cubeMap hψ]
  have := setIntegral_pullCube_mul (b := b) hs u p (fun y => (((2 * s)⁻¹ : ℝ) : ℂ) *
    fderiv ℝ ψ y (Pi.single k 1))
  simp only [Function.comp_apply] at this
  rw [this]
  simp_rw [mul_left_comm _ (((2 * s)⁻¹ : ℝ) : ℂ)]
  rw [integral_const_mul]; ring

private theorem setIntegral_smul_mul {P : Type*} [Fintype P] (c : ℂ) (G : Domain.L2F ℂ (Q (Fin 3)) P)
    (p : P) (ψ : R3 → ℂ) :
    ∫ y in Q (Fin 3), ((c • G) p : R3 → ℂ) y * ψ y = c * ∫ y in Q (Fin 3), (G p : R3 → ℂ) y * ψ y := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c (G p)] with y hy
  rw [PiLp.smul_apply, hy, Pi.smul_apply, smul_eq_mul, mul_assoc]


private theorem scale_iff {c J A B : ℂ} (hc : c ≠ 0) (hJ : J ≠ 0) :
    c⁻¹ * (J * A) = J * B ↔ A = c * B := by
  constructor <;> intro h
  · have := congrArg (fun z => c * J⁻¹ * z) h
    rw [show c * J⁻¹ * (c⁻¹ * (J * A)) = A by field_simp,
      show c * J⁻¹ * (J * B) = c * B by field_simp] at this
    exact this
  · rw [h]; field_simp

/-! #### Green's formulas on the cube -/

/-- `G = ∇σ` on the cube `C = ∏ (bᵢ, bᵢ + s)` with `σ · n = 0`, as Green's formulas against the
`C¹` trace test functions of `C`. -/
def GradTraceCube (b : R3) (s : ℝ) (σ : Domain.L2F ℂ (Geometry.openCube b s) (Fin 3))
    (G : Domain.L2F ℂ (Geometry.openCube b s) (Fin 3 × Fin 3)) : Prop :=
  ∀ a b' : Fin 3, ∀ φ : R3 → ℂ, IsTraceTestCube b s (cE (a, b')) φ →
    ∫ x in Geometry.openCube b s, (σ a : R3 → ℂ) x * fderiv ℝ φ x (Pi.single b' 1) =
      -∫ x in Geometry.openCube b s, (G (a, b') : R3 → ℂ) x * φ x

/-- `C = curl E` (row-wise) on the cube, with the boundary condition encoded by the parities `c`
of `C`, as Green's formulas. -/
def CurlTraceCube (b : R3) (s : ℝ) (c : Fin 3 × Fin 3 → Fin 3 → ℂ)
    (E C : Domain.L2F ℂ (Geometry.openCube b s) (Fin 3 × Fin 3)) : Prop :=
  ∀ a b' : Fin 3, ∀ φ : R3 → ℂ, IsTraceTestCube b s (c (a, b')) φ →
    (∫ x in Geometry.openCube b s, (E (a, b' + 2) : R3 → ℂ) x *
        fderiv ℝ φ x (Pi.single (b' + 1) 1)) -
      ∫ x in Geometry.openCube b s, (E (a, b' + 1) : R3 → ℂ) x *
        fderiv ℝ φ x (Pi.single (b' + 2) 1) =
      -∫ x in Geometry.openCube b s, (C (a, b') : R3 → ℂ) x * φ x

/-- `D = -div M` (row-wise) on the cube with `M_{τn} = 0`, as Green's formulas. -/
def DivTraceCube (b : R3) (s : ℝ) (M : Domain.L2F ℂ (Geometry.openCube b s) (Fin 3 × Fin 3))
    (D : Domain.L2F ℂ (Geometry.openCube b s) (Fin 3)) : Prop :=
  ∀ a : Fin 3, ∀ φ : R3 → ℂ, IsTraceTestCube b s (cV a) φ →
    ∑ c, ∫ x in Geometry.openCube b s, (M (a, c) : R3 → ℂ) x * fderiv ℝ φ x (Pi.single c 1) =
      ∫ x in Geometry.openCube b s, (D a : R3 → ℂ) x * φ x

theorem gradTraceCube_pull_iff (u : VQ) (G : MQ) :
    GradTraceCube b s (pullCube b s hs _ u) (pullCube b s hs _ G) ↔
      GradTrace u ((((2 * s : ℝ)) : ℂ) • G) := by
  have h2 := two_s_ne_zero hs
  have hJ := jacCube_ne_zero hs
  have hinv : (((2 * s)⁻¹ : ℝ) : ℂ) = (((2 * s : ℝ)) : ℂ)⁻¹ := by push_cast; ring
  constructor
  · intro h a b' ψ hψ
    have := h a b' (ψ ∘ cubeMap b s) (isTraceTestCube_comp_cubeMap hs hψ)
    rw [setIntegral_pullCube_mul_fderiv hs u _ hψ.contDiff, setIntegral_pullCube_mul hs G, hinv,
      ← mul_neg] at this
    rw [setIntegral_smul_mul, ← mul_neg, (scale_iff h2 hJ).1 this]
  · intro h a b' φ hφ
    have hψ := hφ.comp_aff hs
    rw [← comp_aff_cubeMap (b := b) hs φ, setIntegral_pullCube_mul_fderiv hs u _ hψ.contDiff,
      setIntegral_pullCube_mul hs G, hinv, ← mul_neg]
    refine (scale_iff h2 hJ).2 ?_
    rw [h a b' _ hψ, setIntegral_smul_mul]; ring

theorem curlTraceCube_pull_iff (c : Fin 3 × Fin 3 → Fin 3 → ℂ) (E C : MQ) :
    CurlTraceCube b s c (pullCube b s hs _ E) (pullCube b s hs _ C) ↔
      CurlTrace c E ((((2 * s : ℝ)) : ℂ) • C) := by
  have h2 := two_s_ne_zero hs
  have hJ := jacCube_ne_zero hs
  have hinv : (((2 * s)⁻¹ : ℝ) : ℂ) = (((2 * s : ℝ)) : ℂ)⁻¹ := by push_cast; ring
  constructor
  · intro h a b' ψ hψ
    have := h a b' (ψ ∘ cubeMap b s) (isTraceTestCube_comp_cubeMap hs hψ)
    rw [setIntegral_pullCube_mul_fderiv hs E _ hψ.contDiff,
      setIntegral_pullCube_mul_fderiv hs E _ hψ.contDiff, setIntegral_pullCube_mul hs C, hinv,
      ← mul_sub, ← mul_sub, ← mul_neg] at this
    rw [setIntegral_smul_mul, ← mul_neg, (scale_iff h2 hJ).1 this]
  · intro h a b' φ hφ
    have hψ := hφ.comp_aff hs
    rw [← comp_aff_cubeMap (b := b) hs φ, setIntegral_pullCube_mul_fderiv hs E _ hψ.contDiff,
      setIntegral_pullCube_mul_fderiv hs E _ hψ.contDiff, setIntegral_pullCube_mul hs C, hinv,
      ← mul_sub, ← mul_sub, ← mul_neg]
    refine (scale_iff h2 hJ).2 ?_
    rw [h a b' _ hψ, setIntegral_smul_mul]; ring

theorem divTraceCube_pull_iff (M : MQ) (D : VQ) :
    DivTraceCube b s (pullCube b s hs _ M) (pullCube b s hs _ D) ↔
      DivTrace M ((((2 * s : ℝ)) : ℂ) • D) := by
  have h2 := two_s_ne_zero hs
  have hJ := jacCube_ne_zero hs
  have hinv : (((2 * s)⁻¹ : ℝ) : ℂ) = (((2 * s : ℝ)) : ℂ)⁻¹ := by push_cast; ring
  constructor
  · intro h a ψ hψ
    have := h a (ψ ∘ cubeMap b s) (isTraceTestCube_comp_cubeMap hs hψ)
    simp_rw [setIntegral_pullCube_mul_fderiv hs M _ hψ.contDiff, hinv] at this
    rw [setIntegral_pullCube_mul hs D, ← Finset.mul_sum, ← Finset.mul_sum] at this
    rw [setIntegral_smul_mul, (scale_iff h2 hJ).1 this]
  · intro h a φ hφ
    have hψ := hφ.comp_aff hs
    rw [← comp_aff_cubeMap (b := b) hs φ]
    simp_rw [setIntegral_pullCube_mul_fderiv hs M _ hψ.contDiff, hinv]
    rw [setIntegral_pullCube_mul hs D, ← Finset.mul_sum, ← Finset.mul_sum]
    refine (scale_iff h2 hJ).2 ?_
    rw [h a _ hψ, setIntegral_smul_mul]


private theorem exists_pullCube_iff {P : Type*} [Fintype P]
    {Pc : Domain.L2F ℂ (Geometry.openCube b s) P → Prop} {Pq : Domain.L2F ℂ (Q (Fin 3)) P → Prop}
    (h : ∀ G, Pc (pullCube b s hs P G) ↔ Pq ((((2 * s : ℝ)) : ℂ) • G)) :
    (∃ G, Pq G) ↔ ∃ G', Pc G' := by
  have h2 := two_s_ne_zero hs
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨_, (h ((((2 * s : ℝ)) : ℂ)⁻¹ • G)).2 (by rwa [smul_smul, mul_inv_cancel₀ h2, one_smul])⟩
  · rintro ⟨G', hG'⟩
    refine ⟨_, (h ((pullCube b s hs P).symm G')).1 ?_⟩
    rwa [ContinuousLinearEquiv.apply_symm_apply]

/-- **The data space `D(L)` of the mirror complex on every open cube by Green's formulas**: for
`C = ∏ (bᵢ, bᵢ + s)`, `(σ, E, B) ∈ D(L)` iff `∇σ ∈ L²(C)` with `σ · n = 0`, `curl E ∈ L²(C)` with
`E_{nτ} = 0`, `div E ∈ L²(C)` with `E_{τn} = 0`, and `curl B ∈ L²(C)` with `B_{ττ} = 0` on `∂C`,
each as Green's formulas against the `C¹` trace test functions of `C` (`IsTraceTestCube`). -/
theorem mem_wave_domain_cube_iff_trace (U : PiLp 2 (SpaceCube b s)) :
    U ∈ (complexCube b s hs).wave.domain ↔
      (∃ G, GradTraceCube b s (U 0) G) ∧ (∃ C, CurlTraceCube b s cB (U 1) C) ∧
        (∃ D, DivTraceCube b s (U 1) D) ∧ ∃ C, CurlTraceCube b s cE (U 2) C := by
  rw [HilbertComplex.mem_wave_domain_transport_iff (kappa_ne_zero hs) (jac_inv_pos hs)
    (inner_eCube hs), mem_wave_domain_iff_trace]
  simp only [HilbertComplex.totalMap_apply]
  have e0 : U 0 = pullCube b s hs _ ((eCube b s hs 0).symm (U 0)) :=
    ((eCube b s hs 0).apply_symm_apply (U 0)).symm
  have e1 : U 1 = pullCube b s hs _ ((eCube b s hs 1).symm (U 1)) :=
    ((eCube b s hs 1).apply_symm_apply (U 1)).symm
  have e2 : U 2 = pullCube b s hs _ ((eCube b s hs 2).symm (U 2)) :=
    ((eCube b s hs 2).apply_symm_apply (U 2)).symm
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · exact (exists_pullCube_iff hs fun G => gradTraceCube_pull_iff hs _ G).trans (by rw [← e0])
  · exact (exists_pullCube_iff hs fun G => curlTraceCube_pull_iff hs cB _ G).trans (by rw [← e1])
  · exact (exists_pullCube_iff hs fun G => divTraceCube_pull_iff hs _ G).trans (by rw [← e1])
  · exact (exists_pullCube_iff hs fun G => curlTraceCube_pull_iff hs cE _ G).trans (by rw [← e2])

/-- **Prop 4.17 on every open cube with the mirror boundary conditions as trace conditions**: on
`C = ∏ (bᵢ, bᵢ + s)`, a datum satisfying the Green's formulas of `mem_wave_domain_cube_iff_trace`
and lying in the TSD constraint, with admissible forcing in the constraint, has a classical
solution, unique among strong solutions, which stays in the constraint.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem existsUnique_memCube_trace {U₀ : PiLp 2 (SpaceCube b s)}
    (hU₀ : (∃ G, GradTraceCube b s (U₀ 0) G) ∧ (∃ C, CurlTraceCube b s cB (U₀ 1) C) ∧
      (∃ D, DivTraceCube b s (U₀ 1) D) ∧ ∃ C, CurlTraceCube b s cE (U₀ 2) C)
    (hU₀S : U₀ ∈ totalSub (tsdCube b s hs)) {F : ℝ → PiLp 2 (SpaceCube b s)} {a c : ℝ}
    (hF : Evolution.ForcingClass.admissible (complexCube b s hs).wave a c F)
    (hFS : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (complexCube b s hs).wave (Icc a c) F U ∧
      (∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F V →
        EqOn V U (Icc a c) :=
  existsUnique_memCube hs ((mem_wave_domain_cube_iff_trace hs U₀).2 hU₀) hU₀S hF hFS

end CubeTrace

end Feec.Models.Cube.Mirror
