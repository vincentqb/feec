module

public import Feec.Models.Cube.Mirror

/-!
# Mirror boundary conditions as trace conditions

The mirror complex on `Q = (0, ½)³` (`Feec.Models.Cube.Mirror.complexQ`, Prop 4.17 with tensorial
mirror conditions) is defined by the method of images: a field lies in a domain iff its extension
by the mirror parities lies in the corresponding torus Sobolev space. This file characterizes
these domains on `Q` itself, by **Green's formulas with vanishing boundary terms** (the weak form
of trace conditions, as for `H̊(curl)` in `Feec.Domain.ConstCoeffOp.mem_minimal_domain_iff`),
tested against the **smooth parity functions** (`MirrorTrace.IsParSmooth c`): `ψ ∈ C^∞(ℝ³)`,
`ℤ³`-periodic, with `ψ ∘ R_ε = (∏_{ε_j} c_j) ψ` for the reflections `R_ε`. On the faces
`x_j ∈ {0, ½}` such a `ψ` vanishes if `c_j = -1` and has a free trace if `c_j = 1`; the class
contains `C_c^∞(Q)` (`MirrorTrace.isParSmooth_ext`), so each formula contains the weak derivative
in `Q` (e.g. `Mirror.GradTrace.weak`) and, through the free traces, a boundary condition on the
faces with `c_j = 1`:

| operator | parity of the test function | Green's formula | boundary condition |
|---|---|---|---|
| `d₀ = grad` | `cE (a, b)` | `∫ σ_a ∂_b ψ = -∫ G_{ab} ψ` | `σ · n = 0` |
| `d₁ = curl` | `cB (a, b)` | `∫ (E_{a,b+2} ∂_{b+1} ψ - E_{a,b+1} ∂_{b+2} ψ) = -∫ C_{ab} ψ` | `E_{nτ} = 0` |
| `d₀† = -div` | `cV a` | `Σ_c ∫ M_{ac} ∂_c ψ = ∫ D_a ψ` | `E_{τn} = 0` |
| `d₁† = curl` | `cE (a, b)` | as for `d₁` | `B_{ττ} = 0` |

(`Mirror.complexQ_d₀_iff`, `complexQ_d₁_iff`, `complexQ_adjoint_d₀_iff`,
`complexQ_adjoint_d₁_iff`). Hence `D(L)` of the mirror complex is described by these formulas
(`Mirror.mem_wave_domain_iff_trace`), and Prop 4.17 holds on `Q` with these boundary conditions,
with existence and uniqueness and TSD propagation (`Mirror.existsUnique_memQ_trace`).

## Method

For a first-order operator `g = Σ α_{cp} ∂_c f_p` whose terms all have the same output parity,
the weak equation on `𝕋³` for the extensions (`Feec.Fourier.TorusWeak.IsWeakFO`, tested against
all smooth `φ` on `𝕋³`) is equivalent to the Green's formula on `Q` against smooth parity functions
(`MirrorTrace.isWeakFO_extL2_iff`): a parity function `f` pairs with `φ` as with its parity
projection `P_c φ = 2⁻³ Σ_ε sign_c(ε) φ ∘ R_ε` (`MirrorTrace.integral_mul_parProj`), the tiling of
`𝕋³` by the eight reflected boxes gives `∫_{𝕋³} (ext_c g) G = 8 ∫_Q g G` for `G` of parity `c`
(`MirrorTrace.integral_extL2_mul`), and `∂_k` commutes with `P` up to the reversal of the parity
of `x_k` (`MirrorTrace.partialT_parProj`).

## Scope

Only the cube `(0, ½)³` and the first-order complex of Prop 4.17 are treated. The complex (4.16)
of Prop 4.19 (`Feec.Models.Cube.MirrorSym`) has the second-order differential `grad grad`, for
which the torus weak theory (`Feec.Fourier.TorusWeak`) has no counterpart; its mirror conditions
are not characterized here. The transport to other cubes (`Mirror.complexCube`) is not carried
out for the Green's formulas.

## Main results

* `MirrorTrace.parProj`, `MirrorTrace.IsParSmooth`; **`MirrorTrace.isWeakFO_extL2_iff`**.
* **`Mirror.complexQ_d₀_iff`**, **`Mirror.complexQ_d₁_iff`**, **`Mirror.complexQ_adjoint_d₀_iff`**,
  **`Mirror.complexQ_adjoint_d₁_iff`**, **`Mirror.mem_wave_domain_iff_trace`**,
  **`Mirror.existsUnique_memQ_trace`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension by reflection)
-/

open scoped InnerProductSpace ContDiff LinearPMap
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
theorem two_pow_ne_zero : ((2 ^ Fintype.card d : ℝ) : ℂ) ≠ 0 := by
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
  have h8 := two_pow_ne_zero (d := d)
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
Green's formula: `σ ∈ D(d₀)` with `d₀ σ = G` iff for all `a, b` and every smooth parity function
`ψ` with the parity `cE (a, b)` of `G_{ab}`, `∫_Q σ_a ∂_b ψ = -∫_Q G_{ab} ψ`. For `ψ ∈ C_c^∞(Q)`
this says `G = ∇σ` weakly; for `b = a`, `ψ` is even in every variable and its trace on the faces
`x_a ∈ {0, ½}` is free, which imposes `σ_a = 0` there; for `b ≠ a`, `ψ` vanishes on the faces
`x_b ∈ {0, ½}`, and no condition is imposed. -/
theorem complexQ_d₀_iff (σ : VQ) (G : MQ) :
    (∃ h : σ ∈ (complexQ.d 0 1).domain, complexQ.d 0 1 ⟨σ, h⟩ = G) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cE (a, b)) ψ →
        ∫ y in Q (Fin 3), (σ a : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single b 1) =
          -∫ y in Q (Fin 3), (G (a, b) : R3 → ℂ) y * ψ y := by
  refine (complexQ_graph_iff (i := 0) (j := 1) σ G).trans ?_
  refine (Models.Torus.GradCurl.mem_domain_grad_iff_weak (extPi cV_sq σ) (extPi cE_sq G)).trans ?_
  refine ⟨fun h a b ψ hψ => ?_, fun h ⟨a, b⟩ => ?_⟩
  · have e := (isWeakFO_extL2_iff _ cV_sq (cE_sq (a, b)) (fun c p hα => by
      simp [gradCurl_m01, grad_apply, PiLp.single_apply] at hα
      obtain ⟨rfl, rfl⟩ := hα
      exact (cE_eq_update _ _).symm) (fun p => σ p) (G (a, b))).1 (h (a, b)) ψ hψ
    simp [gradCurl_m01, grad_apply, PiLp.single_apply, Fin.sum_univ_three] at e
    fin_cases b <;> simp at e ⊢ <;> linear_combination e
  · refine (isWeakFO_extL2_iff _ cV_sq (cE_sq (a, b)) (fun c p hα => by
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
`E ∈ D(d₁)` with `d₁ E = C` iff for all `a, b` and every smooth parity function `ψ` with the
parity `cB (a, b)` of `C_{ab}`,
`∫_Q (E_{a,b+2} ∂_{b+1} ψ - E_{a,b+1} ∂_{b+2} ψ) = -∫_Q C_{ab} ψ`. The free traces of `ψ` sit
on the faces `x_a ∈ {0, ½}` (for `b + 1 = a` or `b + 2 = a`), which imposes that the tangential
components `E_{ac}`, `c ≠ a`, of row `a` vanish on the faces normal to `e_a`; on the other faces
`ψ` vanishes and no condition is imposed. -/
theorem complexQ_d₁_iff (E C : MQ) :
    (∃ h : E ∈ (complexQ.d 1 2).domain, complexQ.d 1 2 ⟨E, h⟩ = C) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cB (a, b)) ψ →
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
  · have e := (isWeakFO_extL2_iff _ cE_sq (cB_sq (a, b)) (fun c p hα => by
      simp only [gradCurl_m12, neg_I_mul_curl_single] at hα
      exact hpar a b c p hα) (fun p => E p) (C (a, b))).1 (h (a, b)) ψ hψ
    simp only [gradCurl_m12, neg_I_mul_curl_single] at e
    rw [sum_curl_coeff a b (fun c p =>
      ∫ y in Q (Fin 3), (E p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))] at e
    exact e
  · refine (isWeakFO_extL2_iff _ cE_sq (cB_sq (a, b)) (fun c p hα => by
      simp only [gradCurl_m12, neg_I_mul_curl_single] at hα
      exact hpar a b c p hα) (fun p => E p) (C (a, b))).2 fun ψ hψ => ?_
    simp only [gradCurl_m12, neg_I_mul_curl_single]
    rw [sum_curl_coeff a b (fun c p =>
      ∫ y in Q (Fin 3), (E p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))]
    exact h a b ψ hψ

/-- **`d₀†` of the mirror complex is `-div` with the mirror condition `E_{τn} = 0`**:
`M ∈ D(d₀†)` with `d₀† M = D` iff for all `a` and every smooth parity function `ψ` with the
parity `cV a` of `D_a`, `Σ_c ∫_Q M_{ac} ∂_c ψ = ∫_Q D_a ψ`. The free traces of `ψ` sit on the
faces `x_c ∈ {0, ½}`, `c ≠ a`, which imposes `M_{ac} = 0` there (the off-diagonal normal
components vanish). -/
theorem complexQ_adjoint_d₀_iff (M : MQ) (D : VQ) :
    (∃ h : M ∈ ((complexQ.d 0 1)†).domain, (complexQ.d 0 1)† ⟨M, h⟩ = D) ↔
      ∀ a : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cV a) ψ →
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
  · have e := (isWeakFO_extL2_iff _ cE_sq (cV_sq a) (fun c p hα => by
      simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single] at hα
      exact hpar a c p hα) (fun p => M p) (D a)).1 (h a) ψ hψ
    simp only [gradCurl_m01, adjoint_grad, neg_I_mul_div_single] at e
    rw [sum_div_coeff a (fun c p =>
      ∫ y in Q (Fin 3), (M p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))] at e
    exact neg_inj.1 e
  · refine (isWeakFO_extL2_iff _ cE_sq (cV_sq a) (fun c p hα => by
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
`B_{ττ} = 0`**: `B ∈ D(d₁†)` with `d₁† B = C` iff for all `a, b` and every smooth parity function
`ψ` with the parity `cE (a, b)` of `C_{ab}`,
`∫_Q (B_{a,b+2} ∂_{b+1} ψ - B_{a,b+1} ∂_{b+2} ψ) = -∫_Q C_{ab} ψ`. On a face normal to `e_k`, `ψ`
has a free trace exactly when `a ≠ k`, and the boundary term then involves `B_{ad}` with
`a, d ≠ k`: every tangential–tangential component of `B` vanishes on the faces. -/
theorem complexQ_adjoint_d₁_iff (B C : MQ) :
    (∃ h : B ∈ ((complexQ.d 1 2)†).domain, (complexQ.d 1 2)† ⟨B, h⟩ = C) ↔
      ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cE (a, b)) ψ →
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
  · have e := (isWeakFO_extL2_iff _ cB_sq (cE_sq (a, b)) (fun c p hα => by
      simp only [gradCurl_m12, neg_I_mul_curl_single] at hα
      exact hpar a b c p hα) (fun p => B p) (C (a, b))).1 (h (a, b)) ψ hψ
    simp only [gradCurl_m12, neg_I_mul_curl_single] at e
    rw [sum_curl_coeff a b (fun c p =>
      ∫ y in Q (Fin 3), (B p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))] at e
    exact e
  · refine (isWeakFO_extL2_iff _ cB_sq (cE_sq (a, b)) (fun c p hα => by
      simp only [gradCurl_m12, neg_I_mul_curl_single] at hα
      exact hpar a b c p hα) (fun p => B p) (C (a, b))).2 fun ψ hψ => ?_
    simp only [gradCurl_m12, neg_I_mul_curl_single]
    rw [sum_curl_coeff a b (fun c p =>
      ∫ y in Q (Fin 3), (B p : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1))]
    exact h a b ψ hψ

/-! #### The data space of Prop 4.17 with mirror boundary conditions, by Green's formulas -/

/-- `G = ∇σ` on `Q` with `σ · n = 0`, as Green's formulas against smooth parity functions. -/
def GradTrace (σ : VQ) (G : MQ) : Prop :=
  ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cE (a, b)) ψ →
    ∫ y in Q (Fin 3), (σ a : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single b 1) =
      -∫ y in Q (Fin 3), (G (a, b) : R3 → ℂ) y * ψ y

/-- **`GradTrace` contains the weak gradient**: tested against `C_c^∞(Q)` (extended by parity),
`GradTrace σ G` says `G_{ab} = ∂_b σ_a` weakly in `Q`. -/
theorem GradTrace.weak {σ : VQ} {G : MQ} (h : GradTrace σ G) (a b : Fin 3) {Φ : R3 → ℂ}
    (hΦ : Domain.IsTest (Q (Fin 3)) Φ) :
    ∫ y in Q (Fin 3), (σ a : R3 → ℂ) y * fderiv ℝ Φ y (Pi.single b 1) =
      -∫ y in Q (Fin 3), (G (a, b) : R3 → ℂ) y * Φ y := by
  have e := h a b _ (isParSmooth_ext (cE_sq (a, b)) hΦ)
  rwa [setIntegral_mul_fderiv_ext hΦ, setIntegral_mul_ext hΦ] at e

/-- `C = curl E` (row-wise) on `Q`, with the boundary condition encoded by the parities `c` of
`C` (`cB` for `E_{nτ} = 0`, `cE` for `B_{ττ} = 0`), as Green's formulas. -/
def CurlTrace (c : Fin 3 × Fin 3 → Fin 3 → ℂ) (E C : MQ) : Prop :=
  ∀ a b : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (c (a, b)) ψ →
    (∫ y in Q (Fin 3), (E (a, b + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 1) 1)) -
      ∫ y in Q (Fin 3), (E (a, b + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single (b + 2) 1) =
      -∫ y in Q (Fin 3), (C (a, b) : R3 → ℂ) y * ψ y

/-- `D = -div M` (row-wise) on `Q` with `M_{τn} = 0`, as Green's formulas. -/
def DivTrace (M : MQ) (D : VQ) : Prop :=
  ∀ a : Fin 3, ∀ ψ : R3 → ℂ, IsParSmooth (cV a) ψ →
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

end Feec.Models.Cube.Mirror
