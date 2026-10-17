module

public import Feec.Models.Cube.RowWiseIdent
public import Feec.Domain.Affine

/-!
# The thesis' complex on every open cube: only stationary data propagate

The bounded-domain complex `H̊¹ → H̊(curl) → L²` (`Feec.Models.BoundedDomain.gradCurl`, the
minimal realizations of `grad` and `curl`) on `Q = (0, ½)³` is the compression of the real torus
grad–curl complex along the parity extension (`Feec.Models.Cube.RowWise.cubeComplex_eq_compress`),
so its wave group is the restriction of the torus wave group, which has pure point spectrum. On
`Q` forward invariance of `{0} × S₁ × S₂`, `S₁, S₂ ⊆ L²(TSD)`, forces stationarity
(`Feec.Models.Cube.RowWise.forward_iff`). This file transports the results to every open cube
`∏ (bᵢ, bᵢ + s)` along the affine map `T x = (x - b) / (2s)`
(`Feec.Domain.ConstCoeffOp.minimal_pull`): the cube complex is the transport of the one on `Q`
with chain-rule factor `a = 1/(2s)` (`Ident.complexCube_eq`), so its wave group is the conjugate
of the one on `Q` with time rescaled by `a` (`Ident.waveGroup_pull`,
`Feec.HilbertComplex.waveGroup_transport_const`).

## Main results

* `HilbertComplex.wave_transport_const`, `HilbertComplex.waveGroup_transport_const`: transport
  with a constant real chain-rule factor `κ` rescales the wave operator by `κ` and time by `κ`.
* **`Ident.forward_iff`**: on every open cube, for every `S₁, S₂ ⊆ L²(TSD)` (closed or not), the
  forward orbit of `y` stays in `{0} × S₁ × S₂` iff `y` lies there and is stationary;
* **`Ident.mem_invariantCore_iff`**: the largest invariant subspace consists of the stationary
  data in `{0} × S₁ × S₂`;
* **`Ident.mem_invariantCore_tsd_iff`**: for the thesis' constraint these are the data
  `(0, 0, B₀)` with `B₀ ∈ L²(TSD)` and `d₁† B₀ = curl B₀ = 0`;
* `Ident.forward_iff_pi`, `Ident.mem_invariantCore_tsd_iff_pi`: the cube `(0, π)³`.

The comparison of the mirror complex on `Q` with the minimal and maximal realizations is in
`Feec.Models.Cube.MirrorDirichlet`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
* [Brezis2011], §9.2 (extension by reflection)
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

/-- **Transport with a constant real chain-rule factor `κ` rescales the wave operator**:
`L' (e x) = κ e (L x)`, for uniformly scaled isometries `e`. -/
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

/-- **The wave group of a transport with constant chain-rule factor `κ`** is the conjugated wave
group with time rescaled by `κ`: `e^{tL'} e = e e^{κ t L}`. -/
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

/-! ### The complex on an open cube -/

namespace Feec.Models.Cube.Ident

open Models.BoundedDomain (R3 Ix tsd gradCurl)
open Domain (L2F aff pullF)
open HilbertComplex (totalSub totalMap)
open ShortHilbertComplex (W3 family3 inj₂ mem_totalSub_family3)
open RowWise (WQ cubeComplex)
open Geometry (Q openCube)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

variable {b : R3} {s : ℝ}

theorem forall_rescale {a : ℝ} (ha : a ≠ 0) {P : ℝ → Prop} : (∀ t, P (a * t)) ↔ ∀ t, P t :=
  ⟨fun h t => by simpa [← mul_assoc, mul_inv_cancel₀ ha] using h (a⁻¹ * t), fun h _ => h _⟩

theorem forall_rescale_nonneg {a : ℝ} (ha : 0 < a) {P : ℝ → Prop} :
    (∀ t, 0 ≤ t → P (a * t)) ↔ ∀ t, 0 ≤ t → P t :=
  ⟨fun h t ht => by
    simpa [← mul_assoc, mul_inv_cancel₀ ha.ne'] using
      h (a⁻¹ * t) (mul_nonneg (inv_nonneg.2 ha.le) ht),
    fun h t ht => h _ (mul_nonneg ha.le ht)⟩

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

/-- **The thesis' complex on the open cube** `∏ (bᵢ, bᵢ + s)`: `H̊¹ → H̊(curl) → L²`, the minimal
realizations of `grad` and `curl`. -/
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

/-- **The cube complex is the transport of the complex on `Q`** along the pull-back, with
chain-rule factor `a = 1/(2s)` (`grad` and `curl` are of order one). -/
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

/-- **The wave group on the cube is the wave group on `Q` with time rescaled by `1/(2s)`**,
conjugated by the pull-back. -/
theorem waveGroup_pull (hs : 0 < s) (t : ℝ) (x : PiLp 2 WQ) :
    (complexCube b s).waveGroup.S t (totalMap (pullC hs) x) =
      totalMap (pullC hs) (cubeComplex.waveGroup.S (scale s * t) x) := by
  rw [complexCube_eq hs]
  exact HilbertComplex.waveGroup_transport_const cubeComplex
    (inv_pos.2 (Domain.jac_pos (scale_ne_zero hs))) (inner_pullC hs) (scale_ne_zero hs) t x

theorem totalMap_injective (hs : 0 < s) : Function.Injective (totalMap (pullC (b := b) hs)) :=
  fun _ _ h => PiLp.ext fun i => (pullC hs i).injective (congrArg (fun z => z i) h)

theorem totalMap_surjective (hs : 0 < s) : Function.Surjective (totalMap (pullC (b := b) hs)) :=
  fun y => ⟨WithLp.toLp 2 fun i => (pullC hs i).symm (y i),
    PiLp.ext fun i => (pullC hs i).apply_symm_apply (y i)⟩

theorem totalMap_inj₂ (hs : 0 < s) (B : L2F ℝ (Q (Fin 3)) Ix) :
    totalMap (pullC (b := b) hs) (inj₂ (𝕜 := ℝ) _ _ _ B) = inj₂ (𝕜 := ℝ) _ _ _ (pullM hs B) := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · exact _root_.map_zero (pullV (b := b) hs)
  · exact _root_.map_zero (pullM (b := b) hs)
  · rfl

/-- The pull-back of a constraint on the cube: `{u | u ∘ T⁻¹ ∈ S}` on `Q`. -/
def pullSub (hs : 0 < s) (S : Submodule ℝ (L2F ℝ (openCube b s) Ix)) :
    Submodule ℝ (L2F ℝ (Q (Fin 3)) Ix) :=
  S.comap (pullM hs).toLinearEquiv.toLinearMap

theorem mem_pullSub (hs : 0 < s) {S : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    {u : L2F ℝ (Q (Fin 3)) Ix} : u ∈ pullSub hs S ↔ pullM hs u ∈ S := Iff.rfl

theorem totalMap_mem_iff (hs : 0 < s) {S1 S2 : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    (x : PiLp 2 WQ) :
    totalMap (pullC hs) x ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2) ↔
      x ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (Q (Fin 3)) (Fin 3)))
        (pullSub hs S1) (pullSub hs S2)) := by
  rw [mem_totalSub_family3, mem_totalSub_family3]
  refine and_congr ?_ Iff.rfl
  change pullV hs (x 0 : L2F ℝ (Q (Fin 3)) (Fin 3)) = 0 ↔ (x 0 : L2F ℝ (Q (Fin 3)) (Fin 3)) = 0
  exact (pullV hs).map_eq_zero_iff

theorem mem_stationary_pull (hs : 0 < s) (x : PiLp 2 WQ) :
    totalMap (pullC hs) x ∈ (complexCube b s).waveGroup.stationary ↔
      x ∈ cubeComplex.waveGroup.stationary := by
  rw [C0Group.mem_stationary, C0Group.mem_stationary]
  simp only [waveGroup_pull hs, (totalMap_injective hs).eq_iff]
  exact forall_rescale (scale_ne_zero hs) (P := fun t => cubeComplex.waveGroup.S t x = x)

theorem mem_invariantCore_pull (hs : 0 < s) {S1 S2 : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    (x : PiLp 2 WQ) :
    totalMap (pullC hs) x ∈ (complexCube b s).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2)) ↔
      x ∈ cubeComplex.waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (Q (Fin 3)) (Fin 3)))
          (pullSub hs S1) (pullSub hs S2))) := by
  rw [C0Group.mem_invariantCore, C0Group.mem_invariantCore]
  simp only [waveGroup_pull hs, totalMap_mem_iff hs]
  exact forall_rescale (scale_ne_zero hs) (P := fun t => cubeComplex.waveGroup.S t x ∈
    totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (Q (Fin 3)) (Fin 3)))
      (pullSub hs S1) (pullSub hs S2)))

/-! ### Adjoints and `L²(TSD)` under the pull-back -/

theorem adjoint_d_eq (hs : 0 < s) (i j : Fin 3) :
    ((complexCube b s).d i j)† =
      HilbertComplex.transportD cubeComplex.dual (pullC hs) (fun _ _ => scale s) j i := by
  rw [complexCube_eq hs, HilbertComplex.transport_d,
    HilbertComplex.adjoint_transportD (inv_pos.2 (Domain.jac_pos (scale_ne_zero hs)))
      (inner_pullC hs) (scale_ne_zero hs)]
  simp only [conj_trivial]

theorem mem_adjoint_domain_iff (hs : 0 < s) {i j : Fin 3} {y : WC b s j} :
    y ∈ ((complexCube b s).d i j)†.domain ↔
      (pullC hs j).symm y ∈ (cubeComplex.d i j)†.domain := by
  rw [adjoint_d_eq hs]; exact Iff.rfl

/-- `d†` on the cube: `d†_cube (u ∘ T⁻¹) = a (d†_Q u) ∘ T⁻¹`. -/
theorem adjoint_apply_pull (hs : 0 < s) (i j : Fin 3) {u : WQ j}
    (hu : u ∈ (cubeComplex.d i j)†.domain) :
    ∃ h : pullC (b := b) hs j u ∈ ((complexCube b s).d i j)†.domain,
      ((complexCube b s).d i j)† ⟨_, h⟩ = scale s • pullC hs i ((cubeComplex.d i j)† ⟨u, hu⟩) := by
  have h : pullC (b := b) hs j u ∈ ((complexCube b s).d i j)†.domain := by
    rw [mem_adjoint_domain_iff hs, ContinuousLinearEquiv.symm_apply_apply]; exact hu
  refine ⟨h, ?_⟩
  rw [apply_eq_of_eq (adjoint_d_eq hs i j) ⟨_, h⟩ ⟨_, (mem_adjoint_domain_iff hs).1 h⟩ rfl,
    HilbertComplex.transportD_apply]
  exact congrArg (fun z => scale s • pullC hs i z)
    (apply_congr' _ _ _ ((pullC hs j).symm_apply_apply u))

theorem mem_ker_iff' {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {T : E →ₗ.[ℝ] F} {u : E} : u ∈ T.ker ↔ ∃ h : u ∈ T.domain, T ⟨u, h⟩ = 0 := by
  rw [LinearPMap.mem_ker_iff]
  exact ⟨fun ⟨y, hy, h0⟩ => ⟨hy ▸ y.2, by rw [← h0]; exact apply_congr' _ _ _ hy⟩,
    fun ⟨h, h0⟩ => ⟨⟨u, h⟩, rfl, h0⟩⟩

theorem pull_injective (hs : 0 < s) :
    Function.Injective (Domain.pull (𝕜 := ℝ) (scale_ne_zero hs) (shift b s)
      Geometry.measurableSet_Q (preimage_Q hs)) := by
  have ha := scale_ne_zero hs
  refine Function.LeftInverse.injective (g := Domain.pull (inv_ne_zero ha)
    (-((scale s)⁻¹ • shift b s)) (Domain.measurableSet_of_aff (shift b s) Geometry.measurableSet_Q
      (preimage_Q hs)) (Domain.preimage_inv_of_aff ha (shift b s) (preimage_Q hs))) fun f => ?_
  exact Domain.pull_pull ha (inv_ne_zero ha) Geometry.measurableSet_Q _ (preimage_Q hs) _
    (Domain.aff_inv' ha (shift b s)) f

/-- **`L²(TSD)` corresponds under the pull-back.** -/
theorem pullM_mem_tsd_iff (hs : 0 < s) {u : L2F ℝ (Q (Fin 3)) Ix} :
    pullM (b := b) hs u ∈ tsd (openCube b s) ↔ u ∈ tsd (Q (Fin 3)) := by
  rw [Models.BoundedDomain.mem_tsd_iff_ker (Geometry.isOpen_openCube b s),
    Models.BoundedDomain.mem_tsd_iff_ker Geometry.isOpen_Q]
  have hp : ∀ p, (pullM (b := b) hs u) p = Domain.pull (scale_ne_zero hs) (shift b s)
      Geometry.measurableSet_Q (preimage_Q hs) (u p) := fun p => rfl
  refine and_congr ?_ (and_congr ?_ ?_)
  · simp only [hp, (pull_injective hs).eq_iff]
  · rw [show ∑ i, (pullM (b := b) hs u) (i, i) = Domain.pull (scale_ne_zero hs) (shift b s)
        Geometry.measurableSet_Q (preimage_Q hs) (∑ i, u (i, i)) by simp only [hp, map_sum]]
    exact (pull_injective hs).eq_iff' (_root_.map_zero _)
  · rw [mem_ker_iff', mem_ker_iff']
    constructor
    · rintro ⟨h, h0⟩
      have hu : u ∈ (cubeComplex.d 0 1)†.domain := by
        have := (mem_adjoint_domain_iff (i := 0) (j := 1) hs).1 h
        rwa [show (pullC (b := b) hs 1).symm (pullM hs u) = u from
          (pullM hs).symm_apply_apply u] at this
      obtain ⟨h', e⟩ := adjoint_apply_pull (b := b) hs 0 1 hu
      refine ⟨hu, ?_⟩
      have e' : scale s • pullC (b := b) hs 0 ((cubeComplex.d 0 1)† ⟨u, hu⟩) = 0 := e.symm.trans h0
      rw [smul_eq_zero] at e'
      exact (pullV (b := b) hs).map_eq_zero_iff.1 (e'.resolve_left (scale_ne_zero hs))
    · rintro ⟨hu, h0⟩
      obtain ⟨h', e⟩ := adjoint_apply_pull (b := b) hs 0 1 hu
      refine ⟨h', ?_⟩
      change ((complexCube b s).d 0 1)† ⟨_, h'⟩ = 0
      rw [e]
      change scale s • pullV hs ((cubeComplex.d 0 1)† ⟨u, hu⟩) = 0
      rw [show (cubeComplex.d 0 1)† ⟨u, hu⟩ = (0 : L2F ℝ (Q (Fin 3)) (Fin 3)) from h0,
        _root_.map_zero, smul_zero]

theorem pullSub_tsd (hs : 0 < s) : pullSub (b := b) hs (tsd (openCube b s)) = tsd (Q (Fin 3)) :=
  Submodule.ext fun _ => (mem_pullSub hs).trans (pullM_mem_tsd_iff hs)

theorem pullSub_le_tsd (hs : 0 < s) {S : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    (h : S ≤ tsd (openCube b s)) : pullSub hs S ≤ tsd (Q (Fin 3)) :=
  fun _ hu => (pullM_mem_tsd_iff hs).1 (h hu)

/-! ### Only stationary data propagate on the cube -/

/-- **On every open cube with the thesis' boundary conditions, forward invariance forces
stationarity**: for `S₁, S₂ ⊆ L²(TSD)` (closed or not), the forward orbit of `y` under the wave
group stays in `{0} × S₁ × S₂` iff `y` lies there and is stationary.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem forward_iff (hs : 0 < s) {S1 S2 : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    (h1 : S1 ≤ tsd (openCube b s)) (h2 : S2 ≤ tsd (openCube b s)) (y : PiLp 2 (WC b s)) :
    (∀ t, 0 ≤ t → (complexCube b s).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2) ∧
        y ∈ (complexCube b s).waveGroup.stationary := by
  obtain ⟨x, rfl⟩ := totalMap_surjective hs y
  simp only [waveGroup_pull hs, totalMap_mem_iff hs, mem_stationary_pull hs]
  exact (forall_rescale_nonneg (scale_pos hs) (P := fun t => cubeComplex.waveGroup.S t x ∈
    totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (Q (Fin 3)) (Fin 3)))
      (pullSub hs S1) (pullSub hs S2)))).trans
    (RowWise.forward_iff (pullSub_le_tsd hs h1) (pullSub_le_tsd hs h2) x)

/-- **`K*` on every open cube with the thesis' boundary conditions consists of the stationary data
in `K`**, for every `S₁, S₂ ⊆ L²(TSD)`.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem mem_invariantCore_iff (hs : 0 < s) {S1 S2 : Submodule ℝ (L2F ℝ (openCube b s) Ix)}
    (h1 : S1 ≤ tsd (openCube b s)) (h2 : S2 ≤ tsd (openCube b s)) (y : PiLp 2 (WC b s)) :
    y ∈ (complexCube b s).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3))) S1 S2) ∧
        y ∈ (complexCube b s).waveGroup.stationary := by
  refine ⟨fun hy => (forward_iff hs h1 h2 y).1 fun t _ => C0Group.mem_invariantCore.1 hy t,
    fun ⟨hK, hst⟩ => C0Group.mem_invariantCore.2 fun t => ?_⟩
  rw [C0Group.mem_stationary.1 hst t]; exact hK

/-- **`K*` on every open cube for the thesis' constraint, explicitly**: `y ∈ K*` iff
`y = (0, 0, B₀)` with `B₀ ∈ L²(TSD)` and `d₁† B₀ = curl B₀ = 0` (no boundary condition on `B₀`).
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem mem_invariantCore_tsd_iff (hs : 0 < s) (y : PiLp 2 (WC b s)) :
    y ∈ (complexCube b s).waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube b s) (Fin 3)))
          (tsd (openCube b s)) (tsd (openCube b s)))) ↔
      ∃ B ∈ tsd (openCube b s),
        ∃ h : B ∈ ((gradCurl ℝ (Geometry.isOpen_openCube b s)).d₁†).domain,
          (gradCurl ℝ (Geometry.isOpen_openCube b s)).d₁† ⟨B, h⟩ = 0 ∧
            y = inj₂ (𝕜 := ℝ) (L2F ℝ (openCube b s) (Fin 3)) (L2F ℝ (openCube b s) Ix)
              (L2F ℝ (openCube b s) Ix) B := by
  obtain ⟨x, rfl⟩ := totalMap_surjective hs y
  rw [mem_invariantCore_pull hs, pullSub_tsd, RowWise.mem_invariantCore_tsd_iff]
  constructor
  · rintro ⟨B', hB', hd, hd0, rfl⟩
    obtain ⟨h', e⟩ := adjoint_apply_pull (b := b) hs 1 2 hd
    refine ⟨pullM hs B', (pullM_mem_tsd_iff hs).2 hB', h', ?_, totalMap_inj₂ hs B'⟩
    change ((complexCube b s).d 1 2)† ⟨_, h'⟩ = 0
    rw [e]
    change scale s • pullM hs ((cubeComplex.d 1 2)† ⟨B', hd⟩) = 0
    rw [show (cubeComplex.d 1 2)† ⟨B', hd⟩ = (0 : L2F ℝ (Q (Fin 3)) Ix) from hd0,
      _root_.map_zero, smul_zero]
  · rintro ⟨B, hB, hd, hd0, hy⟩
    obtain ⟨B', rfl⟩ := (pullM (b := b) hs).surjective B
    have hd' : B' ∈ (cubeComplex.d 1 2)†.domain := by
      have := (mem_adjoint_domain_iff (i := 1) (j := 2) hs).1 hd
      rwa [show (pullC (b := b) hs 2).symm (pullM hs B') = B' from
        (pullM hs).symm_apply_apply B'] at this
    obtain ⟨h', e⟩ := adjoint_apply_pull (b := b) hs 1 2 hd'
    have e' : scale s • pullC (b := b) hs 1 ((cubeComplex.d 1 2)† ⟨B', hd'⟩) = 0 := e.symm.trans hd0
    rw [smul_eq_zero] at e'
    refine ⟨B', (pullM_mem_tsd_iff hs).1 hB, hd',
      (pullM (b := b) hs).map_eq_zero_iff.1 (e'.resolve_left (scale_ne_zero hs)), ?_⟩
    exact totalMap_injective hs (hy.trans (totalMap_inj₂ hs B').symm)

/-! ### The cube `(0, π)³` -/

/-- **Forward invariance forces stationarity on `(0, π)³`.**
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem forward_iff_pi {S1 S2 : Submodule ℝ (L2F ℝ (openCube 0 Real.pi) Ix)}
    (h1 : S1 ≤ tsd (openCube 0 Real.pi)) (h2 : S2 ≤ tsd (openCube 0 Real.pi))
    (y : PiLp 2 (WC 0 Real.pi)) :
    (∀ t, 0 ≤ t → (complexCube 0 Real.pi).waveGroup.S t y ∈
        totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube 0 Real.pi) (Fin 3))) S1 S2)) ↔
      y ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ (openCube 0 Real.pi) (Fin 3))) S1 S2) ∧
        y ∈ (complexCube 0 Real.pi).waveGroup.stationary :=
  forward_iff Real.pi_pos h1 h2 y

/-- **`K*` on `(0, π)³` for the thesis' constraint.**
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
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
