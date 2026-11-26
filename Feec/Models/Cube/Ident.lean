module

public import Feec.Models.Box.EigenDense
public import Feec.Domain.Affine

/-!
# The thesis' complex on every open cube: only stationary data propagate

For `H̊¹ → H̊(curl) → L²` on `Q = (0, ½)³` and on every open cube, forward invariance of
`{0} × S₁ × S₂`, `S₁, S₂ ⊆ L²(TSD)`, forces stationarity.

## Main results

* `RowWise.forward_iff`, `Ident.forward_iff`: on `Q` and on every open cube.
* `RowWise.mem_invariantCore_tsd_iff`, `Ident.mem_invariantCore_tsd_iff`: `K*` explicitly.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap MeasureTheory

@[expose] public noncomputable section

/-! ### Transport with a constant chain-rule factor -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)] [∀ i, CompleteSpace (W' i)]
  (H : HilbertComplex 𝕜 c W) {e : ∀ i, W i ≃L[𝕜] W' i} {s : ℝ}

theorem wave_transport_const (hs : 0 < s)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) {κ : ℝ} (hκ : κ ≠ 0) :
    Intertwines (totalMap e) ((κ : 𝕜) • H.wave)
      (H.transport e (fun _ _ => (κ : 𝕜)) fun _ _ => RCLike.ofReal_ne_zero.2 hκ).wave := by
  set H' := H.transport e (fun _ _ => (κ : 𝕜)) fun _ _ => RCLike.ofReal_ne_zero.2 hκ
  have hadj : ∀ i j, (H'.d i j)† = transportD H.dual e (fun _ _ => (κ : 𝕜)) j i := fun i j => by
    have := adjoint_transportD (H := H) (e := e) (κ := fun _ _ => (κ : 𝕜)) hs he
      (i := i) (j := j) (RCLike.ofReal_ne_zero.2 hκ)
    simp only [RCLike.conj_ofReal] at this
    exact this
  have hmem : ∀ x : ((κ : 𝕜) • H.wave).domain, totalMap e (x : PiLp 2 W) ∈ H'.wave.domain :=
    fun x => (mem_wave_domain _).2 ⟨fun i j => by
      change (e i).symm (e i ((x : PiLp 2 W) i)) ∈ (H.d i j).domain
      rw [ContinuousLinearEquiv.symm_apply_apply]; exact x.2.1 i j,
    fun i j => by
      rw [hadj]
      change (e j).symm (e j ((x : PiLp 2 W) j)) ∈ ((H.d i j)†).domain
      rw [ContinuousLinearEquiv.symm_apply_apply]; exact x.2.2 j i⟩
  refine ⟨hmem, fun x => PiLp.ext fun j => ?_⟩
  change (H'.wave ⟨_, hmem x⟩ : PiLp 2 W') j = e j ((κ : 𝕜) • (H.wave ⟨x, x.2⟩ : PiLp 2 W) j)
  rw [wave_apply, _root_.map_smul, wave_apply, _root_.map_sub, map_sum, map_sum, smul_sub,
    Finset.smul_sum, Finset.smul_sum]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun k _ => ?_)
  · change (κ : 𝕜) • e j (H.d i j ⟨(e i).symm (e i ((x : PiLp 2 W) i)), _⟩) = _
    exact congrArg (fun z => (κ : 𝕜) • e j z) (apply_congr' _ _ _ ((e i).symm_apply_apply _))
  · rw [apply_eq_of_eq (hadj j k) _ ⟨_, by
      change (e k).symm (e k ((x : PiLp 2 W) k)) ∈ ((H.d j k)†).domain
      rw [ContinuousLinearEquiv.symm_apply_apply]; exact x.2.2 k j⟩ rfl]
    change (κ : 𝕜) • e j ((H.d j k)† ⟨(e k).symm (e k ((x : PiLp 2 W) k)), _⟩) = _
    exact congrArg (fun z => (κ : 𝕜) • e j z) (apply_congr' _ _ _ ((e k).symm_apply_apply _))

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  [∀ i, NormedSpace ℝ (W' i)] [∀ i, IsScalarTower ℝ 𝕜 (W' i)]

/-- **Wave group of a transport with constant chain-rule factor `κ`**: `e^{tL'} e = e e^{κ t L}`. -/
theorem waveGroup_transport_const (hs : 0 < s)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) {κ : ℝ} (hκ : κ ≠ 0) (t : ℝ)
    (x : PiLp 2 W) :
    (H.transport e (fun _ _ => (κ : 𝕜)) fun _ _ => RCLike.ofReal_ne_zero.2 hκ).waveGroup.S t
        (totalMap e x) = totalMap e (H.waveGroup.S (κ * t) x) := by
  have h := wave_transport_const H hs he hκ
  rw [← generator_waveGroup H, ← C0Group.generator_rescale _ hκ,
    ← generator_waveGroup (H.transport e (fun _ _ => (κ : 𝕜)) _)] at h
  exact ((H.transport e _ _).isIsometric_waveGroup.intertwines_S _ h t x).symm

end Feec.HilbertComplex

/-! ### The cube `Q = (0, ½)³` -/

namespace Feec.Models.Cube.RowWise

open Models.BoundedDomain (Ix tsd)
open HilbertComplex (totalSub)
open ShortHilbertComplex (family3 inj₂)
open Geometry (Q)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-- **On `Q`, forward invariance of `{0} × S₁ × S₂`, `S₁, S₂ ⊆ L²(TSD)`, forces stationarity**
([QuennevilleBelair2015], Prop 4.17 (adapted)). -/
theorem forward_iff {S1 S2 : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) Ix)}
    (h1 : S1 ≤ tsd (Q (Fin 3))) (h2 : S2 ≤ tsd (Q (Fin 3))) (y : PiLp 2 WQ) :
    (∀ t, 0 ≤ t → cubeComplex.waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3))) S1 S2) ∧
        y ∈ cubeComplex.waveGroup.stationary :=
  Box.forward_iff (a := 0) (ℓ := fun _ => 1 / 2) (fun _ => one_half_pos) h1 h2 y

theorem mem_invariantCore_iff {S1 S2 : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) Ix)}
    (h1 : S1 ≤ tsd (Q (Fin 3))) (h2 : S2 ≤ tsd (Q (Fin 3))) (y : PiLp 2 WQ) :
    y ∈ cubeComplex.waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3))) S1 S2) ∧
        y ∈ cubeComplex.waveGroup.stationary :=
  Box.mem_invariantCore_iff (a := 0) (ℓ := fun _ => 1 / 2) (fun _ => one_half_pos) h1 h2 y

/-- **`K*` on `Q`**: `y ∈ K*` iff `y = (0, 0, B₀)` with `B₀ ∈ L²(TSD)` and `curl B₀ = 0`
([QuennevilleBelair2015], Prop 4.17 (adapted)). -/
theorem mem_invariantCore_tsd_iff (y : PiLp 2 WQ) :
    y ∈ cubeComplex.waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)))
          (tsd (Q (Fin 3))) (tsd (Q (Fin 3))))) ↔
      ∃ B ∈ tsd (Q (Fin 3)),
        ∃ h : B ∈ ((Models.BoundedDomain.gradCurl ℝ Geometry.isOpen_Q).d₁†).domain,
          (Models.BoundedDomain.gradCurl ℝ Geometry.isOpen_Q).d₁† ⟨B, h⟩ = 0 ∧
            y = inj₂ (𝕜 := ℝ) (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) (Domain.L2F ℝ (Q (Fin 3)) Ix)
              (Domain.L2F ℝ (Q (Fin 3)) Ix) B :=
  Box.mem_invariantCore_tsd_iff (a := 0) (ℓ := fun _ => 1 / 2) (fun _ => one_half_pos) y

end Feec.Models.Cube.RowWise

namespace Feec.Models.Cube.Ident

open Models.BoundedDomain (R3 Ix tsd gradCurl)
open Domain (L2F aff pullF)
open HilbertComplex (totalSub totalMap)
open ShortHilbertComplex (W3 family3 inj₂ mem_totalSub_family3)
open RowWise (WQ cubeComplex)
open Geometry (Q openCube)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

variable {b : R3} {s : ℝ}

/-! ### The complex on an open cube -/

/-- The scaling `a = 1/(2s)` of `T x = a (x - b)`, mapping `∏ (bᵢ, bᵢ + s)` onto `Q = (0, ½)³`. -/
def scale (s : ℝ) : ℝ := (2 * s)⁻¹

theorem scale_pos (hs : 0 < s) : 0 < scale s := inv_pos.2 (by linarith)

theorem scale_ne_zero (hs : 0 < s) : scale s ≠ 0 := (scale_pos hs).ne'

/-- The shift `-a b` of `T x = a x - a b`. -/
def shift (b : R3) (s : ℝ) : R3 := -(scale s • b)

theorem preimage_Q (hs : 0 < s) : aff (scale s) (shift b s) ⁻¹' Q (Fin 3) = openCube b s := by
  have h2 : 0 < 2 * s := by linarith
  ext x
  simp only [mem_preimage, Geometry.mem_Q, openCube, mem_pi, mem_univ, true_implies, mem_Ioo,
    aff, shift, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, scale]
  refine forall_congr' fun i => ?_
  have e : (2 * s)⁻¹ * x i + -((2 * s)⁻¹ * b i) = (x i - b i) / (2 * s) := by ring
  rw [e, div_pos_iff_of_pos_right h2, div_lt_iff₀ h2]
  constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith

/-- The spaces of the complex on `∏ (bᵢ, bᵢ + s)`. -/
abbrev WC (b : R3) (s : ℝ) : Fin 3 → Type :=
  W3 (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix) (L2F ℝ (openCube b s) Ix)

/-- **The complex `H̊¹ → H̊(curl) → L²` on the open cube** `∏ (bᵢ, bᵢ + s)`. -/
abbrev complexCube (b : R3) (s : ℝ) : HilbertComplex ℝ ComplexShape.fin3 (WC b s) :=
  (gradCurl ℝ (Geometry.isOpen_openCube b s)).toHilbertComplex

/-- The pull-back `u ↦ u ∘ T` of vector fields from `Q` to the cube. -/
def pullV (hs : 0 < s) : L2F ℝ (Q (Fin 3)) (Fin 3) ≃L[ℝ] L2F ℝ (openCube b s) (Fin 3) :=
  pullF (scale_ne_zero hs) (shift b s) Geometry.measurableSet_Q (preimage_Q hs) (Fin 3)

/-- The pull-back `u ↦ u ∘ T` of matrix fields from `Q` to the cube. -/
def pullM (hs : 0 < s) : L2F ℝ (Q (Fin 3)) Ix ≃L[ℝ] L2F ℝ (openCube b s) Ix :=
  pullF (scale_ne_zero hs) (shift b s) Geometry.measurableSet_Q (preimage_Q hs) Ix

/-- The pull-back, slot by slot. -/
def pullC (hs : 0 < s) : ∀ i, WQ i ≃L[ℝ] WC b s i
  | 0 => pullV hs
  | 1 => pullM hs
  | 2 => pullM hs

theorem inner_pullC (hs : 0 < s) (i : Fin 3) (x y : WQ i) :
    ⟪pullC (b := b) hs i x, pullC hs i y⟫_ℝ =
      (((Domain.jac (E := R3) (scale s))⁻¹ : ℝ) : ℝ) * ⟪x, y⟫_ℝ := by
  fin_cases i
  · exact Domain.inner_pullF _ _ _ _ x y
  · exact Domain.inner_pullF _ _ _ _ x y
  · exact Domain.inner_pullF _ _ _ _ x y

theorem isHomogeneous_gradOp :
    (Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix).IsHomogeneous 1 := by
  intro j i t ht
  simp only [Domain.gradOp] at ht
  split_ifs at ht <;> simp_all

theorem isHomogeneous_curlOp :
    (Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix).IsHomogeneous 1 := by
  intro j i t ht
  simp only [Domain.curlOp] at ht
  split_ifs at ht <;> simp_all

/-- **The cube complex is the transport of the complex on `Q`**, with chain-rule factor `1/(2s)`. -/
theorem complexCube_eq (hs : 0 < s) :
    complexCube b s = cubeComplex.transport (pullC hs) (fun _ _ => scale s)
      fun _ _ => scale_ne_zero hs := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  by_cases hij : ComplexShape.fin3.Rel i j
  · fin_cases i <;> fin_cases j <;> simp [ComplexShape.window] at hij
    · have h := Domain.ConstCoeffOp.minimal_pull isHomogeneous_gradOp (scale_ne_zero hs)
        (shift b s) Geometry.measurableSet_Q (preimage_Q hs) Geometry.isOpen_Q
      rw [pow_one] at h
      exact h
    · have h := Domain.ConstCoeffOp.minimal_pull isHomogeneous_curlOp (scale_ne_zero hs)
        (shift b s) Geometry.measurableSet_Q (preimage_Q hs) Geometry.isOpen_Q
      rw [pow_one] at h
      exact h
  · rw [(complexCube b s).shape i j hij, HilbertComplex.transport_d,
      HilbertComplex.transportD_eq_zero (cubeComplex.shape i j hij)]

/-! ### Only stationary data propagate on the cube -/

/-- **On every open cube, forward invariance of `{0} × S₁ × S₂`, `S₁, S₂ ⊆ L²(TSD)`, forces
stationarity** ([QuennevilleBelair2015], Prop 4.17 (adapted)). -/
theorem forward_iff (hs : 0 < s) {S1 S2 : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    (h1 : S1 ≤ tsd (openCube b s)) (h2 : S2 ≤ tsd (openCube b s)) (y : PiLp 2 (WC b s)) :
    (∀ t, 0 ≤ t → (complexCube b s).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2) ∧
        y ∈ (complexCube b s).waveGroup.stationary :=
  Box.forward_iff (a := b) (ℓ := fun _ => s) (fun _ => hs) h1 h2 y

theorem mem_invariantCore_iff (hs : 0 < s) {S1 S2 : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    (h1 : S1 ≤ tsd (openCube b s)) (h2 : S2 ≤ tsd (openCube b s)) (y : PiLp 2 (WC b s)) :
    y ∈ (complexCube b s).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2) ∧
        y ∈ (complexCube b s).waveGroup.stationary :=
  Box.mem_invariantCore_iff (a := b) (ℓ := fun _ => s) (fun _ => hs) h1 h2 y

/-- **`K*` on every open cube**: `y ∈ K*` iff `y = (0, 0, B₀)` with `B₀ ∈ L²(TSD)` and
`curl B₀ = 0` ([QuennevilleBelair2015], Prop 4.17 (adapted)). -/
theorem mem_invariantCore_tsd_iff (hs : 0 < s) (y : PiLp 2 (WC b s)) :
    y ∈ (complexCube b s).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3)))
          (tsd (openCube b s)) (tsd (openCube b s)))) ↔
      ∃ B ∈ tsd (openCube b s),
        ∃ h : B ∈ ((gradCurl ℝ (Geometry.isOpen_openCube b s)).d₁†).domain,
          (gradCurl ℝ (Geometry.isOpen_openCube b s)).d₁† ⟨B, h⟩ = 0 ∧
            y = inj₂ (𝕜 := ℝ) (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
              (L2F ℝ (openCube b s) Ix) B :=
  Box.mem_invariantCore_tsd_iff (a := b) (ℓ := fun _ => s) (fun _ => hs) y

/-! ### The cube `(0, π)³` -/

theorem forward_iff_pi {S1 S2 : Submodule ℝ (L2F ℝ (openCube 0 Real.pi) Ix)}
    (h1 : S1 ≤ tsd (openCube 0 Real.pi)) (h2 : S2 ≤ tsd (openCube 0 Real.pi))
    (y : PiLp 2 (WC 0 Real.pi)) :
    (∀ t, 0 ≤ t → (complexCube 0 Real.pi).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube 0 Real.pi) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube 0 Real.pi) (Fin 3))) S1 S2) ∧
        y ∈ (complexCube 0 Real.pi).waveGroup.stationary :=
  forward_iff Real.pi_pos h1 h2 y

theorem mem_invariantCore_tsd_iff_pi (y : PiLp 2 (WC 0 Real.pi)) :
    y ∈ (complexCube 0 Real.pi).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube 0 Real.pi) (Fin 3)))
          (tsd (openCube 0 Real.pi)) (tsd (openCube 0 Real.pi)))) ↔
      ∃ B ∈ tsd (openCube 0 Real.pi),
        ∃ h : B ∈ ((gradCurl ℝ (Geometry.isOpen_openCube 0 Real.pi)).d₁†).domain,
          (gradCurl ℝ (Geometry.isOpen_openCube 0 Real.pi)).d₁† ⟨B, h⟩ = 0 ∧
            y = inj₂ (𝕜 := ℝ) (L2F ℝ (openCube 0 Real.pi) (Fin 3))
              (L2F ℝ (openCube 0 Real.pi) Ix) (L2F ℝ (openCube 0 Real.pi) Ix) B :=
  mem_invariantCore_tsd_iff Real.pi_pos y

end Feec.Models.Cube.Ident
