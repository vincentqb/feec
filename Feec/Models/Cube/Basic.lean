module

public import Feec.Fourier.TorusWeak
public import Feec.Domain.L2Field
public import Feec.HilbertComplex.Equivariant
public import Feec.Semigroup.Spectral

/-!
# Shared infrastructure of the cube models

The cube `Q = (0, ½)³` is a fundamental domain of the reflection group `(ℤ/2)³` of the torus
`𝕋³ = ℝ³/ℤ³`, and the cube models (`Feec.Models.Cube.Parity`, `Feec.Models.Cube.Static` for the
thesis' row-wise boundary conditions; `Feec.Models.Cube.Mirror`, `MirrorSym`, `MirrorBGG` for the
mirror conditions) are compressions of torus complexes. This file holds what both families share
and does not depend on either.

## Main definitions and results

* `halfArc`, `boxSet`: the box `(0, ½)ᵈ` in `𝕋ᵈ` (any dimension); `ZeroOnBox f`: the function
  with Fourier coefficients `f` vanishes a.e. on the box, characterized by orthogonality to the
  functions supported off the box (`zeroOnBox_iff`), a closed subspace (`boxZero`);
  **`eq_zero_of_zeroOnBox_of_finite`**: a trigonometric polynomial vanishing a.e. on the box is
  zero (`Feec.Fourier.TorusWeak.eq_zero_of_ae_eq_zero_of_finite`).
* (namespace `Geometry`) `Q d = (0, ½)ᵈ`, `openCube b s = ∏ (bᵢ, bᵢ + s)`; **`measurePreserving_proj_Q`**: the covering
  map `proj : ℝᵈ → 𝕋ᵈ` is measure preserving from `Q` onto the box; `setIntegral_boxSet`.
* `resQ`, `resQF`: restriction of torus fields to `Q`; `per`, `isSmooth_per`, `partialT_per`,
  `integral_mul_per`: periodization of test functions supported in `Q`; **`resQ_isWeakFO`**: weak
  first-order operators on `𝕋ᵈ` restrict to weak first-order operators on `Q`.
* `reflB ε`, `piece ε`: the reflections of `𝕋ᵈ` and the `2ᵈ` reflected boxes;
  **`integral_eq_sum_box`** (the tiling, up to the null set `faceSet`);
  `mFourierCoeff_comp_reflB`: `(g ∘ R_ε)^ = ĝ ∘ flip_ε`.
* **`norm_sq_eq_two_pow`**: `‖f‖²_{L²(𝕋ᵈ)} = 2ᵈ ‖f|_Q‖²` for parity fields;
  **`eq_zero_of_resQ_eq_zero`**: parity fields are determined by their restriction to `Q`
  (`norm_comp_reflB_ae`: the Fourier-side parity criterion).
* `ext c Φ`: the parity extension of a test function for a sign vector `c`; `ext_reflB`,
  `isSmooth_ext`, **`resQ_toL2_ext`** (`(ext Φ)|_Q = Φ`), **`norm_sq_toL2_ext`**
  (`‖ext Φ‖² = 2ᵈ ‖Φ‖²`, the factor `8` for the cube), **`partialT_ext`** (`∂_k ∘ ext_c = ext_{c'} ∘ ∂_k`
  with the parity of `x_k` reversed).
* `sub3`, `reducingSubcomplex_sub3`: families of three subspaces of a short complex, and the
  reducing subcomplex `({0}, K₁, K₂)` from two reducing pairs.
* `compSub`, `mem_invariantCore_compSub_iff`, `mem_stationary_compSub_iff`,
  `forward_compSub_iff`, `mem_wave_domain_compress_iff`: invariant cores, stationary vectors and
  wave domains of a compression are those of the big complex.
* **`reducingSubcomplex_compSub_fixed`**: a reducing subcomplex invariant under a finite unitary
  action descends to the fixed (method-of-images) complex.
* `comm_of_eq_zero`, `generator_eq_zero_of_mem_stationary`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17 on the cube)
* [Brezis2011], §9.2 (extension by reflection)
-/

open scoped InnerProductSpace ENNReal Topology
open Set LinearPMap MeasureTheory Filter

@[expose] public noncomputable section

universe u

namespace Feec.Models.Cube

open Feec.ShortHilbertComplex

/- Over `ℝ`, the real structure of `W3` is the one of its inner product space; the instance
`instNormedSpaceRealW3` (meant for `𝕜 = ℂ`) would be a second, non-reducibly-equal one. -/
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-! ### The box `(0, ½)ᵈ` in the torus -/

section Box

open UnitAddTorus Feec.Fourier.TorusWeak

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : Type*} [Fintype d]

/-- The open arc `(0, ½)` of `ℝ/ℤ`. -/
def halfArc : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Ioo 0 (1 / 2)

variable (d) in
/-- The open box `(0, ½)ᵈ` in `𝕋ᵈ`. -/
def boxSet : Set (UnitAddTorus d) := univ.pi fun _ => halfArc

omit [Fintype d] in
theorem isOpen_boxSet [Finite d] : IsOpen (boxSet d) :=
  isOpen_set_pi finite_univ fun _ _ => QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

theorem measurableSet_boxSet : MeasurableSet (boxSet d) := isOpen_boxSet.measurableSet

omit [Fintype d] in
/-- Points of `(0, ½)ᵈ ⊂ ℝᵈ` project into the box. -/
theorem proj_mem_boxSet {y : d → ℝ} (hy : ∀ i, y i ∈ Ioo (0 : ℝ) (1 / 2)) : proj y ∈ boxSet d :=
  fun i _ => ⟨y i, hy i, rfl⟩

omit [Fintype d] in
theorem boxSet_nonempty : (boxSet d).Nonempty :=
  ⟨proj fun _ => 1 / 4, proj_mem_boxSet fun _ => ⟨by norm_num, by norm_num⟩⟩

/-- `ZeroOnBox f`: the `L²(𝕋ᵈ)` function with Fourier coefficients `f` vanishes almost
everywhere on the box `(0, ½)ᵈ`. -/
def ZeroOnBox (f : lp (fun _ : d → ℤ => ℂ) 2) : Prop :=
  (ofCoeff f : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)] 0

/-- Functions vanishing a.e. on `s` and functions vanishing a.e. off `s` are orthogonal. -/
theorem inner_eq_zero_of_ae {s : Set (UnitAddTorus d)}
    {g φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hg : (g : UnitAddTorus d → ℂ) =ᵐ[volume.restrict s] 0)
    (hφ : (φ : UnitAddTorus d → ℂ) =ᵐ[volume.restrict sᶜ] 0) : ⟪g, φ⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have h : (fun x => ⟪g x, φ x⟫_ℂ) =ᵐ[volume] 0 := by
    have hu : ∀ᵐ x ∂volume.restrict (s ∪ sᶜ), ⟪g x, φ x⟫_ℂ = 0 := by
      rw [ae_restrict_union_iff]
      exact ⟨hg.mono fun x hx => by simp [hx], hφ.mono fun x hx => by simp [hx]⟩
    rwa [union_compl_self, Measure.restrict_univ] at hu
  rw [integral_congr_ae h]
  simp

/-- **Characterization of `ZeroOnBox`** by orthogonality to every `L²` function supported off the
box. -/
theorem zeroOnBox_iff (f : lp (fun _ : d → ℤ => ℂ) 2) :
    ZeroOnBox f ↔ ∀ φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)),
      (φ : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)ᶜ] 0 → ⟪ofCoeff f, φ⟫_ℂ = 0 := by
  refine ⟨fun h φ hφ => inner_eq_zero_of_ae h hφ, fun h => ?_⟩
  set g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) := ofCoeff f
  have hm : MemLp ((boxSet d).indicator (g : UnitAddTorus d → ℂ)) 2 volume :=
    (Lp.memLp g).indicator measurableSet_boxSet.nullMeasurableSet
  set φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) := hm.toLp _
  have hφ : (φ : UnitAddTorus d → ℂ) =ᵐ[volume] (boxSet d).indicator g := hm.coeFn_toLp
  have hoff : (φ : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)ᶜ] 0 := by
    refine EventuallyEq.trans (ae_restrict_of_ae hφ) ?_
    filter_upwards [ae_restrict_mem measurableSet_boxSet.compl] with x hx
    simp [indicator_of_notMem hx]
  have h0 := h φ hoff
  rw [MeasureTheory.L2.inner_def] at h0
  have e : (fun x => ⟪(g : UnitAddTorus d → ℂ) x, (φ : UnitAddTorus d → ℂ) x⟫_ℂ) =ᵐ[volume]
      (boxSet d).indicator fun x => ((‖(g : UnitAddTorus d → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hφ] with x hx
    rw [hx]
    by_cases hb : x ∈ boxSet d
    · rw [indicator_of_mem hb, indicator_of_mem hb, RCLike.inner_apply, Complex.mul_conj']
      push_cast; rfl
    · rw [indicator_of_notMem hb, indicator_of_notMem hb, inner_zero_right]
  rw [integral_congr_ae e, integral_indicator measurableSet_boxSet, integral_complex_ofReal]
    at h0
  have hint : Integrable (fun x => ‖(g : UnitAddTorus d → ℂ) x‖ ^ 2) (volume.restrict (boxSet d)) :=
    ((Lp.memLp g).integrable_norm_pow two_ne_zero).restrict
  have h1 := (integral_eq_zero_iff_of_nonneg (fun _ => by positivity) hint).1
    (Complex.ofReal_eq_zero.1 h0)
  filter_upwards [h1] with x hx
  simpa using hx

/-- `ZeroOnBox` as a (complex) subspace of `ℓ²(ℤᵈ)`. -/
def boxZero : Submodule ℂ (lp (fun _ : d → ℤ => ℂ) 2) where
  carrier := {f | ZeroOnBox f}
  zero_mem' := by
    simp only [mem_ofPred_eq, zeroOnBox_iff, ofCoeff, _root_.map_zero, inner_zero_left, implies_true]
  add_mem' := by
    intro f g hf hg
    simp only [mem_ofPred_eq, zeroOnBox_iff] at hf hg ⊢
    intro φ hφ
    rw [ofCoeff, _root_.map_add, inner_add_left, ← ofCoeff, ← ofCoeff, hf φ hφ, hg φ hφ, add_zero]
  smul_mem' := by
    intro c f hf
    simp only [mem_ofPred_eq, zeroOnBox_iff] at hf ⊢
    intro φ hφ
    rw [ofCoeff, _root_.map_smul, inner_smul_left, ← ofCoeff, hf φ hφ, mul_zero]

theorem mem_boxZero {f : lp (fun _ : d → ℤ => ℂ) 2} : f ∈ boxZero ↔ ZeroOnBox f := Iff.rfl

/-- `boxZero` is closed. -/
theorem isClosed_boxZero : IsClosed (boxZero (d := d) : Set (lp (fun _ : d → ℤ => ℂ) 2)) := by
  have e : (boxZero (d := d) : Set (lp (fun _ : d → ℤ => ℂ) 2)) =
      ⋂ φ : {φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) //
        (φ : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)ᶜ] 0},
      {f | ⟪ofCoeff f, (φ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))⟫_ℂ = 0} := by
    ext f
    simp only [SetLike.mem_coe, mem_boxZero, zeroOnBox_iff, mem_iInter, mem_ofPred_eq,
      Subtype.forall]
  rw [e]
  refine isClosed_iInter fun φ => isClosed_eq ?_ continuous_const
  exact (continuous_id.inner continuous_const).comp (mFourierBasis.repr.symm.continuous)

/-- **A trigonometric polynomial vanishing a.e. on the box is zero.** -/
theorem eq_zero_of_zeroOnBox_of_finite {f : lp (fun _ : d → ℤ => ℂ) 2} (S : Finset (d → ℤ))
    (hS : ∀ k ∉ S, f k = 0) (hf : ZeroOnBox f) : f = 0 :=
  eq_zero_of_ae_eq_zero_of_finite S hS isOpen_boxSet boxSet_nonempty hf

end Box

/-! ### The cube `Q = (0, ½)ᵈ ⊂ ℝᵈ`, open cubes, and the covering map

In the namespace `Feec.Models.Cube.Geometry`, to keep these names apart from the pre-refactor
cube machinery (`Feec.Legacy.BoxIdent.openCube`, …) still opened by the cube models. -/

namespace Geometry

section Covering

open UnitAddTorus Feec.Fourier.TorusWeak

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- The open cube `∏ᵢ (bᵢ, bᵢ + s) ⊂ ℝᵈ`. -/
def openCube (b : d → ℝ) (s : ℝ) : Set (d → ℝ) := univ.pi fun i => Ioo (b i) (b i + s)

variable (d) in
/-- **The cube `Q = (0, ½)ᵈ`**, a fundamental domain of the reflection group `(ℤ/2)ᵈ` of `𝕋ᵈ`. -/
def Q : Set (d → ℝ) := openCube 0 (1 / 2)

omit [Fintype d] in
theorem mem_Q {y : d → ℝ} : y ∈ Q d ↔ ∀ i, y i ∈ Ioo (0 : ℝ) (1 / 2) := by
  simp [Q, openCube]

theorem isOpen_openCube (b : d → ℝ) (s : ℝ) : IsOpen (openCube b s) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem isOpen_Q : IsOpen (Q d) := isOpen_openCube _ _

theorem measurableSet_Q : MeasurableSet (Q d) := isOpen_Q.measurableSet

theorem isBounded_openCube (b : d → ℝ) (s : ℝ) : Bornology.IsBounded (openCube b s) :=
  (Metric.isBounded_Icc b fun i => b i + s).subset fun _ hy =>
    ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩

variable (d) in
/-- The half-open unit cube `(0, 1]ᵈ`, a fundamental domain of `ℤᵈ`. -/
def unitCube : Set (d → ℝ) := univ.pi fun _ => Ioc (0 : ℝ) 1

omit [Fintype d] in
theorem Q_subset_unitCube : Q d ⊆ unitCube d := fun y hy i hi => by
  rw [mem_Q] at hy
  exact ⟨(hy i).1, (hy i).2.le.trans (by norm_num)⟩

/-- The covering map `ℝ → ℝ/ℤ` is measure preserving from `(0, 1]` to the normalized Haar
measure. -/
theorem measurePreserving_coe_Ioc :
    MeasurePreserving ((↑) : ℝ → UnitAddCircle) (volume.restrict (Ioc (0 : ℝ) 1))
      (volume : Measure UnitAddCircle) := by
  have h := UnitAddCircle.measurePreserving_mk 0
  rw [zero_add] at h
  have e : (@volume UnitAddCircle (AddCircle.measureSpace 1)) =
      (volume : Measure UnitAddCircle) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]; rfl
  exact e ▸ h

/-- `proj : ℝᵈ → 𝕋ᵈ` is measure preserving from the unit cube `(0, 1]ᵈ`. -/
theorem measurePreserving_proj_unitCube :
    MeasurePreserving proj (volume.restrict (unitCube d)) (volume : Measure (UnitAddTorus d)) := by
  have h := measurePreserving_pi (fun _ : d => volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ : d => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) fun _ => measurePreserving_coe_Ioc
  rw [← Measure.restrict_pi_pi, ← volume_pi] at h
  exact h

/-- A point of `(0, 1]` whose class lies in the arc `(0, ½)` lies in `(0, ½)`. -/
theorem mem_Ioo_of_coe_mem_halfArc {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (h : ((t : ℝ) : UnitAddCircle) ∈ halfArc) : t ∈ Ioo (0 : ℝ) (1 / 2) := by
  obtain ⟨s, hs, e⟩ := h
  have hs' : s ∈ Ioc (0 : ℝ) (0 + 1) := ⟨hs.1, by rw [zero_add]; linarith [hs.2]⟩
  have ht' : t ∈ Ioc (0 : ℝ) (0 + 1) := by rwa [zero_add]
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hs' ht').1 e
  exact this ▸ hs

omit [Fintype d] in
/-- `proj⁻¹(box) ∩ (0, 1]ᵈ = Q`. -/
theorem preimage_boxSet_inter_unitCube : proj ⁻¹' boxSet d ∩ unitCube d = Q d := by
  ext y
  rw [mem_Q]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact mem_Ioo_of_coe_mem_halfArc (h2 i (mem_univ i)) (h1 i (mem_univ i))
  · intro hy
    exact ⟨proj_mem_boxSet hy, Q_subset_unitCube (mem_Q.2 hy)⟩

/-- **`proj` is measure preserving from `Q ⊂ ℝᵈ` onto the box of `𝕋ᵈ`.** -/
theorem measurePreserving_proj_Q :
    MeasurePreserving proj (volume.restrict (Q d)) (volume.restrict (boxSet d)) := by
  have h := (measurePreserving_proj_unitCube (d := d)).restrict_preimage measurableSet_boxSet
  rwa [Measure.restrict_restrict (measurableSet_boxSet.preimage
    measurePreserving_proj_unitCube.measurable), preimage_boxSet_inter_unitCube] at h

/-- **Change of variables between the box of `𝕋ᵈ` and `Q ⊂ ℝᵈ`.** -/
theorem setIntegral_boxSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : UnitAddTorus d → E) (hg : AEStronglyMeasurable g (volume.restrict (boxSet d))) :
    ∫ x in boxSet d, g x = ∫ y in Q d, g (proj y) := by
  rw [← measurePreserving_proj_Q.map_eq] at hg ⊢
  exact integral_map measurePreserving_proj_Q.measurable.aemeasurable hg

/-- Functions vanishing off the box integrate over `𝕋ᵈ` as over `Q`. -/
theorem integral_eq_setIntegral_Q {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : UnitAddTorus d → E} (hg : AEStronglyMeasurable g volume)
    (h0 : ∀ x, x ∉ boxSet d → g x = 0) : ∫ x, g x = ∫ y in Q d, g (proj y) := by
  rw [← setIntegral_boxSet g hg.restrict, setIntegral_eq_integral_of_forall_compl_eq_zero h0]

/-- Almost-everywhere statements on the box pull back to `Q`. -/
theorem ae_Q_of_ae_boxSet {p : UnitAddTorus d → Prop}
    (h : ∀ᵐ x ∂volume.restrict (boxSet d), p x) : ∀ᵐ y ∂volume.restrict (Q d), p (proj y) :=
  measurePreserving_proj_Q.quasiMeasurePreserving.ae h

/-! #### Restriction of torus fields to `Q` -/

/-- **Restriction to `Q`**: `f ↦ (f ∘ proj)|_Q`, a continuous linear map
`L²(𝕋ᵈ) → L²(Q)`. -/
def resQ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) →L[ℂ] Domain.L2 ℂ (Q d) :=
  ((Lp.compMeasurePreservingₗᵢ ℂ proj measurePreserving_proj_Q).toContinuousLinearMap).comp
    (LpToLpRestrictCLM (UnitAddTorus d) ℂ ℂ volume 2 (boxSet d))

theorem coeFn_resQ (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (resQ f : (d → ℝ) → ℂ) =ᵐ[volume.restrict (Q d)] fun y => (f : UnitAddTorus d → ℂ) (proj y) := by
  have h1 := LpToLpRestrictCLM_coeFn ℂ (boxSet d) f
  have h2 := Lp.coeFn_compMeasurePreserving
    (LpToLpRestrictCLM (UnitAddTorus d) ℂ ℂ volume 2 (boxSet d) f) measurePreserving_proj_Q
  filter_upwards [h2, ae_Q_of_ae_boxSet h1] with y e2 e1
  change (Lp.compMeasurePreserving proj measurePreserving_proj_Q
    (LpToLpRestrictCLM (UnitAddTorus d) ℂ ℂ volume 2 (boxSet d) f) : (d → ℝ) → ℂ) y = _
  rw [e2, Function.comp_apply, e1]

/-- Restriction of fields, componentwise. -/
def resQF {P : Type*} : Feec.Fourier.TorusWeak.Field d P →L[ℂ] Domain.L2F ℂ (Q d) P where
  toFun f := WithLp.toLp 2 fun p => resQ (f p)
  map_add' f g := by ext p; simp
  map_smul' c f := by ext p; simp
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    resQ.continuous.comp (PiLp.continuous_apply 2 _ p))

@[simp] theorem resQF_apply {P : Type*} (f : Feec.Fourier.TorusWeak.Field d P) (p : P) :
    resQF f p = resQ (f p) := rfl

/-- Functions vanishing a.e. on the box restrict to `0`. -/
theorem resQ_eq_zero_of_ae {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (h : (f : UnitAddTorus d → ℂ) =ᵐ[volume.restrict (boxSet d)] 0) : resQ f = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_resQ f, ae_Q_of_ae_boxSet h,
    Lp.coeFn_zero ℂ 2 (volume.restrict (Q d))] with y h1 h2 h3
  rw [h1, h3, h2]
  rfl

/-! #### Periodization of test functions supported in `Q` -/

/-- The representative in `[0, 1)ᵈ` of a point of `𝕋ᵈ`. -/
def rep (x : UnitAddTorus d) : d → ℝ := fun i => (AddCircle.equivIco 1 0 (x i) : ℝ)

omit [Fintype d] in
theorem rep_proj (y : d → ℝ) (i : d) : rep (proj y) i = y i - (⌊y i⌋ : ℝ) := by
  simp only [rep, proj]
  rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, Int.fract]

omit [Fintype d] in
theorem proj_rep (x : UnitAddTorus d) : proj (rep x) = x := by
  funext i
  simp [proj, rep]

/-- **Periodization** of a function supported in `Q`: `per Φ (x) = Φ(rep x)`, the
`ℤᵈ`-periodic extension of `Φ` as a function on `𝕋ᵈ`. -/
def per (Φ : (d → ℝ) → ℂ) (x : UnitAddTorus d) : ℂ := Φ (rep x)

/-- The integer vector `⌊y + ¼⌋`: near `y`, the only translate of `Q` meeting the neighbourhood
is `Q + ⌊y + ¼⌋`. -/
def nvec (y : d → ℝ) (i : d) : ℝ := (⌊y i + 1 / 4⌋ : ℤ)

section Per

variable {Φ : (d → ℝ) → ℂ}

theorem mem_Q_of_ne_zero (hΦ : Domain.IsTest (Q d) Φ) {w : d → ℝ} (h : Φ w ≠ 0) : w ∈ Q d :=
  hΦ.tsupport_subset (subset_tsupport _ h)

theorem eq_floor_self_of_ne_zero (hΦ : Domain.IsTest (Q d) Φ) {z : d → ℝ} {m : d → ℤ}
    (h : Φ (fun i => z i - (m i : ℝ)) ≠ 0) (i : d) : ⌊z i⌋ = m i := by
  have hm := mem_Q.1 (mem_Q_of_ne_zero hΦ h) i
  simp only [mem_Ioo] at hm
  rw [Int.floor_eq_iff]
  constructor <;> linarith [hm.1, hm.2]

theorem eq_floor_of_ne_zero (hΦ : Domain.IsTest (Q d) Φ) {y z : d → ℝ} (hz : dist z y < 1 / 8)
    {m : d → ℤ} (h : Φ (fun i => z i - (m i : ℝ)) ≠ 0) (i : d) : ⌊y i + 1 / 4⌋ = m i := by
  have hm := mem_Q.1 (mem_Q_of_ne_zero hΦ h) i
  have hd : |z i - y i| < 1 / 8 := by
    have := (dist_le_pi_dist z y i).trans_lt hz
    rwa [Real.dist_eq] at this
  rw [abs_lt] at hd
  simp only [mem_Ioo] at hm
  rw [Int.floor_eq_iff]
  constructor <;> linarith [hm.1, hm.2, hd.1, hd.2]

omit [Fintype d] in
theorem per_proj (y : d → ℝ) : per Φ (proj y) = Φ (fun i => y i - (⌊y i⌋ : ℝ)) := by
  simp only [per]
  congr 1
  funext i
  exact rep_proj y i

/-- **Local form of the periodization**: near `y`, `per Φ ∘ proj = Φ(· - ⌊y + ¼⌋)`. -/
theorem per_eventuallyEq (hΦ : Domain.IsTest (Q d) Φ) (y : d → ℝ) :
    (per Φ ∘ proj) =ᶠ[𝓝 y] fun z => Φ (z - nvec y) := by
  filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0 : ℝ) < 1 / 8)] with z hz
  rw [Metric.mem_ball] at hz
  simp only [Function.comp_apply, per_proj]
  set n : d → ℤ := fun i => ⌊y i + 1 / 4⌋
  have hn : (z - nvec y) = fun i => z i - (n i : ℝ) := rfl
  rw [hn]
  by_cases hdn : (fun i => ⌊z i⌋) = n
  · have : (fun i => z i - (⌊z i⌋ : ℝ)) = fun i => z i - (n i : ℝ) := by
      funext i
      rw [show ⌊z i⌋ = n i from congrFun hdn i]
    rw [this]
  · have h1 : Φ (fun i => z i - (⌊z i⌋ : ℝ)) = 0 := by
      by_contra h
      exact hdn (funext fun i => (eq_floor_of_ne_zero hΦ hz h i).symm)
    have h2 : Φ (fun i => z i - (n i : ℝ)) = 0 := by
      by_contra h
      exact hdn (funext fun i => eq_floor_self_of_ne_zero hΦ h i)
    exact h1.trans h2.symm

/-- The periodization of a test function is smooth on `𝕋ᵈ`. -/
theorem isSmooth_per (hΦ : Domain.IsTest (Q d) Φ) : IsSmooth (per Φ) := by
  unfold IsSmooth
  rw [contDiff_iff_contDiffAt]
  intro y
  have hs : ContDiff ℝ (⊤ : ℕ∞) fun z : d → ℝ => Φ (z - nvec y) :=
    (hΦ.contDiff.comp (contDiff_id.sub contDiff_const)).of_le (by exact_mod_cast le_top)
  exact hs.contDiffAt.congr_of_eventuallyEq (per_eventuallyEq hΦ y)

omit [Fintype d] in
/-- On `Q`, `per Φ ∘ proj = Φ`. -/
theorem per_proj_of_mem {y : d → ℝ} (hy : y ∈ Q d) : per Φ (proj y) = Φ y := by
  rw [per_proj]
  congr 1
  funext i
  have : ⌊y i⌋ = 0 := by
    have := mem_Q.1 hy i
    rw [Int.floor_eq_iff]
    constructor <;> norm_num <;> linarith [this.1, this.2]
  simp [this]

/-- The periodization is supported in the box. -/
theorem tsupport_per_subset (hΦ : Domain.IsTest (Q d) Φ) : tsupport (per Φ) ⊆ boxSet d := by
  have hK : IsCompact (proj '' tsupport Φ) :=
    hΦ.hasCompactSupport.isCompact.image isOpenQuotientMap_proj.continuous
  have hsub : Function.support (per Φ) ⊆ proj '' tsupport Φ := by
    intro x hx
    refine ⟨rep x, subset_tsupport _ fun h => hx ?_, proj_rep x⟩
    simp [per, h]
  refine (closure_minimal hsub hK.isClosed).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  exact proj_mem_boxSet (mem_Q.1 (hΦ.tsupport_subset hy))

theorem per_eq_zero_of_notMem (hΦ : Domain.IsTest (Q d) Φ) {x : UnitAddTorus d}
    (hx : x ∉ boxSet d) : per Φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_per_subset hΦ h)

variable [DecidableEq d]

/-- **Derivatives of the periodization**: `∂_c (per Φ) = per (∂_c Φ)`. -/
theorem partialT_per (hΦ : Domain.IsTest (Q d) Φ) (c : d) :
    partialT c (per Φ) = per fun y => fderiv ℝ Φ y (Pi.single c 1) := by
  funext x
  obtain ⟨y, rfl⟩ := proj_surjective x
  have hd : Differentiable ℝ (per Φ ∘ proj) :=
    (isSmooth_per hΦ).contDiff_one.differentiable one_ne_zero
  rw [partialT_proj hd, (per_eventuallyEq hΦ y).fderiv_eq]
  have h2 := per_eventuallyEq (hΦ.fderiv_apply (Pi.single c 1)) y
  have h2y : per (fun y => fderiv ℝ Φ y (Pi.single c 1)) (proj y) =
      fderiv ℝ Φ (y - nvec y) (Pi.single c 1) := h2.eq_of_nhds
  rw [h2y]
  have hf : HasFDerivAt (fun z : d → ℝ => Φ (z - nvec y)) (fderiv ℝ Φ (y - nvec y)) y :=
    ((hΦ.differentiable (y - nvec y)).hasFDerivAt).comp y ((hasFDerivAt_id y).sub_const (nvec y))
  rw [hf.fderiv]

omit [DecidableEq d] in
/-- **Transfer of pairings**: `∫_{𝕋ᵈ} f · per Φ = ∫_Q (f|_Q) Φ` for test functions `Φ` supported
in `Q`. -/
theorem integral_mul_per (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hΦ : Domain.IsTest (Q d) Φ) :
    ∫ x, (f : UnitAddTorus d → ℂ) x * per Φ x = ∫ y, resQ f y * Φ y ∂volume.restrict (Q d) := by
  have hc : Continuous (per Φ) := (isSmooth_per hΦ).continuous
  have hg : AEStronglyMeasurable (fun x => (f : UnitAddTorus d → ℂ) x * per Φ x) volume :=
    (Lp.aestronglyMeasurable f).mul hc.aestronglyMeasurable
  rw [integral_eq_setIntegral_Q hg fun x hx => by simp [per_eq_zero_of_notMem hΦ hx]]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_resQ f, ae_restrict_mem measurableSet_Q] with y h1 h2
  rw [per_proj_of_mem h2, h1]

/-- **Restriction of weak first-order operators**: if `g = Σ α_{cp} ∂_c f_p` weakly on `𝕋ᵈ`,
then `g|_Q = Σ α_{cp} ∂_c (f_p|_Q)` weakly on `Q` (tested against `C_c^∞(Q)`). -/
theorem resQ_isWeakFO {P : Type*} [Fintype P] {α : d → P → ℂ}
    {f : P → Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    {g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))} (h : IsWeakFO α f g)
    (hΦ : Domain.IsTest (Q d) Φ) :
    ∑ c, ∑ p, α c p *
        ∫ y, resQ (f p) y * fderiv ℝ Φ y (Pi.single c 1) ∂volume.restrict (Q d) =
      -∫ y, resQ g y * Φ y ∂volume.restrict (Q d) := by
  have h1 := h (per Φ) (isSmooth_per hΦ)
  rw [integral_sum_fo _ f (isSmooth_per hΦ)] at h1
  simp only [partialT_per hΦ] at h1
  simp only [integral_mul_per _ (hΦ.fderiv_apply _), integral_mul_per _ hΦ] at h1
  exact h1

end Per

/-! #### The reflections of `𝕋ᵈ`, the tiling by `2ᵈ` boxes, and parity fields -/

section Tiling

/-- The reflection `x_j ↦ -x_j` for every `j` with `ε j`. -/
def reflB (ε : d → Bool) (x : UnitAddTorus d) : UnitAddTorus d :=
  fun j => if ε j then -x j else x j

omit [Fintype d] in
@[simp] theorem reflB_reflB (ε : d → Bool) (x : UnitAddTorus d) : reflB ε (reflB ε x) = x := by
  funext j; by_cases h : ε j <;> simp [reflB, h]

omit [Fintype d] in
theorem reflB_comp (ε η : d → Bool) (x : UnitAddTorus d) :
    reflB ε (reflB η x) = reflB (fun j => xor (ε j) (η j)) x := by
  funext j
  by_cases h1 : ε j <;> by_cases h2 : η j <;> simp [reflB, h1, h2]

theorem measurePreserving_reflB (ε : d → Bool) :
    MeasurePreserving (reflB ε) (volume : Measure (UnitAddTorus d)) volume := by
  have h := measurePreserving_pi (fun _ : d => (volume : Measure UnitAddCircle))
    (fun _ => volume)
    (f := fun j => if ε j then (Neg.neg : UnitAddCircle → UnitAddCircle) else id) fun j => by
      split_ifs
      · exact Measure.measurePreserving_neg volume
      · exact MeasurePreserving.id volume
  convert h using 1
  funext x j
  by_cases hj : ε j <;> simp [reflB, hj]

/-- The reflection as a measurable equivalence. -/
def reflBE (ε : d → Bool) : UnitAddTorus d ≃ᵐ UnitAddTorus d where
  toFun := reflB ε
  invFun := reflB ε
  left_inv := reflB_reflB ε
  right_inv := reflB_reflB ε
  measurable_toFun := (measurePreserving_reflB ε).measurable
  measurable_invFun := (measurePreserving_reflB ε).measurable

/-- The arc `(0, ½)` and its reflection are disjoint. -/
theorem neg_notMem_halfArc {t : UnitAddCircle} (ht : t ∈ halfArc) : -t ∉ halfArc := by
  obtain ⟨s, hs, rfl⟩ := ht
  rintro ⟨u, hu, e⟩
  have e' : ((u : ℝ) : UnitAddCircle) = ((1 - s : ℝ) : UnitAddCircle) := by
    rw [e, AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  have hu' : u ∈ Ioc (0 : ℝ) (0 + 1) := ⟨hu.1, by rw [zero_add]; linarith [hu.2]⟩
  have hs' : 1 - s ∈ Ioc (0 : ℝ) (0 + 1) := ⟨by linarith [hs.2], by rw [zero_add]; linarith [hs.1]⟩
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hu' hs').1 e'
  linarith [hu.2, hs.2]

/-- The reflected box `R_ε(box)`. -/
def piece (ε : d → Bool) : Set (UnitAddTorus d) := reflB ε ⁻¹' boxSet d

theorem measurableSet_piece (ε : d → Bool) : MeasurableSet (piece ε) :=
  measurableSet_boxSet.preimage (measurePreserving_reflB ε).measurable

omit [Fintype d] in
theorem disjoint_piece {ε ε' : d → Bool} (h : ε ≠ ε') : Disjoint (piece ε) (piece ε') := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h
  rw [Set.disjoint_left]
  intro x hx hx'
  have a := hx j (mem_univ j)
  have b := hx' j (mem_univ j)
  simp only [reflB] at a b
  cases hε : ε j <;> cases hε' : ε' j <;> simp_all
  · exact neg_notMem_halfArc a b
  · exact neg_notMem_halfArc b a

/-- Points of `ℝ/ℤ` have measure zero. -/
theorem volume_singleton_circle (t : UnitAddCircle) : volume ({t} : Set UnitAddCircle) = 0 := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hsub : ((↑) : ℝ → UnitAddCircle) ⁻¹' {((r : ℝ) : UnitAddCircle)} ⊆
      Set.range fun n : ℤ => r + n := by
    intro y hy
    have e : ((y : ℝ) : UnitAddCircle) = (r : UnitAddCircle) := hy
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 e.symm)
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    simp only
    linarith
  have h0 : volume (((↑) : ℝ → UnitAddCircle) ⁻¹' {((r : ℝ) : UnitAddCircle)}) = 0 :=
    measure_mono_null hsub ((Set.countable_range _).measure_zero volume)
  rw [← measurePreserving_coe_Ioc.measure_preimage (measurableSet_singleton _).nullMeasurableSet]
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans h0.le) zero_le

variable (d) in
/-- The faces `{x_j ∈ {0, ½}}` of the reflected boxes. -/
def faceSet : Set (UnitAddTorus d) :=
  ⋃ j : d, {x | x j = 0} ∪ {x | x j = ((1 / 2 : ℝ) : UnitAddCircle)}

theorem volume_faceSet : volume (faceSet d) = 0 := by
  refine measure_iUnion_null fun j => measure_union_null ?_ ?_
  · exact Measure.pi_eval_preimage_null (μ := fun _ => (volume : Measure UnitAddCircle))
      (i := j) (s := {0}) (volume_singleton_circle 0)
  · exact Measure.pi_eval_preimage_null (μ := fun _ => (volume : Measure UnitAddCircle))
      (i := j) (s := {((1 / 2 : ℝ) : UnitAddCircle)}) (volume_singleton_circle _)

/-- Off `0` and `½`, a point of `ℝ/ℤ` or its negative lies in `(0, ½)`. -/
theorem mem_halfArc_or_neg {t : UnitAddCircle} (h0 : t ≠ 0)
    (h1 : t ≠ ((1 / 2 : ℝ) : UnitAddCircle)) : t ∈ halfArc ∨ -t ∈ halfArc := by
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ Ico (0 : ℝ) 1, (r : UnitAddCircle) = t := by
    obtain ⟨r₀, rfl⟩ := QuotientAddGroup.mk_surjective t
    refine ⟨Int.fract r₀, ⟨Int.fract_nonneg r₀, Int.fract_lt_one r₀⟩, ?_⟩
    refine QuotientAddGroup.eq.2 (AddSubgroup.mem_zmultiples_iff.2 ⟨⌊r₀⌋, ?_⟩)
    simp only [zsmul_eq_mul, mul_one, Int.fract]
    ring
  have hr0 : r ≠ 0 := fun e => h0 (by rw [e]; rfl)
  have hr1 : r ≠ 1 / 2 := fun e => h1 (by rw [e])
  rcases lt_or_gt_of_ne hr1 with h | h
  · exact Or.inl ⟨r, ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), h⟩, rfl⟩
  · refine Or.inr ⟨1 - r, ⟨by linarith [hr.2], by linarith⟩, ?_⟩
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]

omit [Fintype d] in
theorem mem_iUnion_piece {x : UnitAddTorus d} (hx : x ∉ faceSet d) : x ∈ ⋃ ε, piece ε := by
  classical
  simp only [faceSet, mem_iUnion, mem_union, mem_ofPred_eq, not_exists, not_or] at hx
  refine mem_iUnion.2 ⟨fun j => decide (x j ∉ halfArc), fun j _ => ?_⟩
  simp only [reflB]
  by_cases h : x j ∈ halfArc
  · simp [h]
  · simp only [h, not_false_eq_true, decide_true, ↓reduceIte]
    exact (mem_halfArc_or_neg (hx j).1 (hx j).2).resolve_left h

/-- **The `2ᵈ` reflected boxes tile `𝕋ᵈ`** up to the null set of their faces. -/
theorem iUnion_piece_ae_eq_univ :
    (⋃ ε, piece ε : Set (UnitAddTorus d)) =ᵐ[volume] (univ : Set (UnitAddTorus d)) := by
  refine (ae_eq_univ).2 (measure_mono_null ?_ volume_faceSet)
  intro x hx
  by_contra h
  exact hx (mem_iUnion_piece h)

/-- **Tiling formula**: `∫_{𝕋ᵈ} g = Σ_ε ∫_{box} g ∘ R_ε`. -/
theorem integral_eq_sum_box [DecidableEq d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : UnitAddTorus d → E} (hg : Integrable g) :
    ∫ x, g x = ∑ ε : d → Bool, ∫ x in boxSet d, g (reflB ε x) := by
  classical
  rw [← setIntegral_univ, ← setIntegral_congr_set iUnion_piece_ae_eq_univ,
    integral_iUnion_fintype measurableSet_piece (fun ε ε' h => disjoint_piece h)
      fun ε => hg.integrableOn]
  refine Finset.sum_congr rfl fun ε _ => ?_
  have h := (measurePreserving_reflB ε).setIntegral_preimage_emb (reflBE ε).measurableEmbedding
    (fun y => g (reflB ε y)) (boxSet d)
  simp only [reflB_reflB] at h
  exact h

/-- The reflection of the frequencies `n ↦ (±n_j)_j`. -/
def flipB (ε : d → Bool) (n : d → ℤ) : d → ℤ := fun j => if ε j then -n j else n j

omit [Fintype d] in
@[simp] theorem flipB_flipB (ε : d → Bool) (n : d → ℤ) : flipB ε (flipB ε n) = n := by
  funext j; by_cases h : ε j <;> simp [flipB, h]

omit [Fintype d] in
theorem flipB_neg (ε : d → Bool) (n : d → ℤ) : flipB ε (-n) = -flipB ε n := by
  funext j; by_cases h : ε j <;> simp [flipB, h]

theorem fourier_neg_arg (m : ℤ) (t : UnitAddCircle) : fourier m (-t) = fourier (-m) t := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_smul]

theorem mFourier_reflB (ε : d → Bool) (n : d → ℤ) (x : UnitAddTorus d) :
    mFourier n (reflB ε x) = mFourier (flipB ε n) x := by
  simp only [mFourier, ContinuousMap.coe_mk]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : ε j
  · simp only [reflB, flipB, hj, ↓reduceIte]
    exact fourier_neg_arg _ _
  · simp only [reflB, flipB, hj, ↓reduceIte, Bool.false_eq_true]

/-- **Fourier coefficients of a reflected function**: `(g ∘ R_ε)^(n) = ĝ(flip_ε n)`; the
physical reflections of `𝕋ᵈ` are the frequency reflections of the Fourier side
(`Feec.Models.Cube.MirrorTorus.flip`). -/
theorem mFourierCoeff_comp_reflB (ε : d → Bool) (g : UnitAddTorus d → ℂ) (n : d → ℤ) :
    mFourierCoeff (fun x => g (reflB ε x)) n = mFourierCoeff g (flipB ε n) := by
  simp only [mFourierCoeff]
  have e : ∀ x, mFourier (-n) x • g (reflB ε x) =
      (fun y => mFourier (-flipB ε n) y • g y) (reflB ε x) := fun x => by
    simp only
    rw [mFourier_reflB, ← flipB_neg, flipB_flipB]
  simp_rw [e]
  exact (measurePreserving_reflB ε).integral_comp' (f := reflBE ε)
    (fun y => mFourier (-flipB ε n) y • g y)

/-- The squared `L²(𝕋ᵈ)` norm is the integral of the squared modulus. -/
theorem norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖f‖ ^ 2 = ∫ x, ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2 := by
  have e : ⟪f, f⟫_ℂ = ((∫ x, ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), e]
  exact Complex.ofReal_re _

theorem norm_sq_eq_integral_Q (g : Domain.L2 ℂ (Q d)) :
    ‖g‖ ^ 2 = ∫ y, ‖(g : (d → ℝ) → ℂ) y‖ ^ 2 ∂volume.restrict (Q d) := by
  have e : ⟪g, g⟫_ℂ = ((∫ y, ‖(g : (d → ℝ) → ℂ) y‖ ^ 2 ∂volume.restrict (Q d) : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), e]
  exact Complex.ofReal_re _

/-- **The norm of a parity field**: if `|f ∘ R_ε| = |f|` a.e. for every reflection (e.g. `f`
even or odd in each variable), then `‖f‖²_{L²(𝕋ᵈ)} = 2ᵈ ‖f|_Q‖²_{L²(Q)}`. -/
theorem norm_sq_eq_two_pow [DecidableEq d] {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hf : ∀ ε, (fun x => ‖(f : UnitAddTorus d → ℂ) (reflB ε x)‖) =ᵐ[volume]
      fun x => ‖(f : UnitAddTorus d → ℂ) x‖) :
    ‖f‖ ^ 2 = 2 ^ Fintype.card d * ‖resQ f‖ ^ 2 := by
  have hint : Integrable (fun x => ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2) :=
    (Lp.memLp f).integrable_norm_pow two_ne_zero
  rw [norm_sq_eq_integral, integral_eq_sum_box hint]
  have hb : ∀ ε : d → Bool, ∫ x in boxSet d, ‖(f : UnitAddTorus d → ℂ) (reflB ε x)‖ ^ 2 =
      ∫ x in boxSet d, ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2 := fun ε =>
    setIntegral_congr_ae₀ measurableSet_boxSet.nullMeasurableSet
      ((hf ε).mono fun x hx _ => by simp only at hx ⊢; rw [hx])
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fun,
    nsmul_eq_mul]
  rw [setIntegral_boxSet _ hint.aestronglyMeasurable.restrict, norm_sq_eq_integral_Q]
  congr 1
  · push_cast; ring
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_resQ f] with y h
    rw [h]

/-- **Parity fields are determined by their restriction to `Q`.** -/
theorem eq_zero_of_resQ_eq_zero [DecidableEq d] {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hf : ∀ ε, (fun x => ‖(f : UnitAddTorus d → ℂ) (reflB ε x)‖) =ᵐ[volume]
      fun x => ‖(f : UnitAddTorus d → ℂ) x‖) (h0 : resQ f = 0) : f = 0 := by
  have := norm_sq_eq_two_pow hf
  rw [h0, norm_zero] at this
  simpa using this

/-- A parity relation on Fourier coefficients (`f̂ ∘ flip_ε = s · f̂`, `|s| = 1`) gives the
parity relation `|f ∘ R_ε| = |f|` a.e. -/
theorem norm_comp_reflB_ae {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))} {ε : d → Bool}
    {s : ℂ} (hs : ‖s‖ = 1)
    (h : ∀ n, mFourierCoeff (f : UnitAddTorus d → ℂ) (flipB ε n) =
      s * mFourierCoeff (f : UnitAddTorus d → ℂ) n) :
    (fun x => ‖(f : UnitAddTorus d → ℂ) (reflB ε x)‖) =ᵐ[volume]
      fun x => ‖(f : UnitAddTorus d → ℂ) x‖ := by
  set g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
    Lp.compMeasurePreserving (reflB ε) (measurePreserving_reflB ε) f
  have hg : (g : UnitAddTorus d → ℂ) =ᵐ[volume] fun x => (f : UnitAddTorus d → ℂ) (reflB ε x) :=
    Lp.coeFn_compMeasurePreserving _ _
  have hsf : ((s • f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : UnitAddTorus d → ℂ)
      =ᵐ[volume] fun x => s * (f : UnitAddTorus d → ℂ) x :=
    (Lp.coeFn_smul s f).mono fun x hx => by rw [hx]; rfl
  have hc : ∀ {u v : UnitAddTorus d → ℂ}, u =ᵐ[volume] v → ∀ n,
      mFourierCoeff u n = mFourierCoeff v n := fun h n =>
    integral_congr_ae (h.mono fun x hx => by simp [hx])
  have e : g = s • f := eq_of_mFourierCoeff_eq fun n => by
    rw [hc hg, mFourierCoeff_comp_reflB, h, hc hsf]
    simp only [mFourierCoeff, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have e' : (g : UnitAddTorus d → ℂ) =
      ((s • f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : UnitAddTorus d → ℂ) := by rw [e]
  filter_upwards [hg, hsf] with x h1 h2
  rw [← h1, congrFun e' x, h2, norm_mul, hs, one_mul]

end Tiling

/-! #### Extension of test functions by parity -/

section Extension

variable [DecidableEq d]

/-- The sign `∏_{j, ε j} c_j` of the reflection `R_ε` for a parity vector `c` (`c_j = ±1`). -/
def sign (c : d → ℂ) (ε : d → Bool) : ℂ := ∏ j, if ε j then c j else 1

omit [DecidableEq d] in
theorem sign_xor {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (ε η : d → Bool) :
    sign c (fun j => xor (ε j) (η j)) = sign c ε * sign c η := by
  rw [sign, sign, sign, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  cases ε j <;> cases η j <;> simp [hc j]

omit [DecidableEq d] in
theorem norm_sign {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (ε : d → Bool) : ‖sign c ε‖ = 1 := by
  rw [sign, norm_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  split_ifs
  · have h := congrArg norm (hc j)
    rw [norm_mul, norm_one, ← sq] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  · exact norm_one

/-- **Extension by parity** of a test function `Φ ∈ C_c^∞(Q)`: the function on `𝕋ᵈ` equal to `Φ`
on the box, with `ext Φ ∘ R_ε = sign_c(ε) · ext Φ` (odd in `x_j` for `c_j = -1`, even for
`c_j = 1`). -/
def ext (c : d → ℂ) (Φ : (d → ℝ) → ℂ) (x : UnitAddTorus d) : ℂ :=
  ∑ ε : d → Bool, sign c ε * per Φ (reflB ε x)

/-- **Parity of the extension.** -/
theorem ext_reflB {c : d → ℂ} (hc : ∀ j, c j * c j = 1) (Φ : (d → ℝ) → ℂ) (η : d → Bool)
    (x : UnitAddTorus d) : ext c Φ (reflB η x) = sign c η * ext c Φ x := by
  rw [ext, ext, Finset.mul_sum]
  let e : (d → Bool) ≃ (d → Bool) :=
    { toFun := fun ε j => xor (ε j) (η j)
      invFun := fun ε j => xor (ε j) (η j)
      left_inv := fun ε => funext fun j => by simp
      right_inv := fun ε => funext fun j => by simp }
  refine (Fintype.sum_equiv e _ _ fun ε => ?_)
  change sign c ε * per Φ (reflB ε (reflB η x)) =
    sign c η * (sign c (fun j => xor (ε j) (η j)) * per Φ (reflB (fun j => xor (ε j) (η j)) x))
  rw [reflB_comp, sign_xor hc]
  have hη : sign c η * sign c η = 1 := by
    rw [← sign_xor hc]; simp [sign]
  linear_combination (-(sign c ε * per Φ (reflB (fun j => xor (ε j) (η j)) x))) * hη

omit [Fintype d] [DecidableEq d] in
theorem reflB_mem_boxSet_iff {ε : d → Bool} {x : UnitAddTorus d} (hx : x ∈ boxSet d) :
    reflB ε x ∈ boxSet d ↔ ∀ j, ε j = false := by
  constructor
  · intro h j
    by_contra hj
    have hj' : ε j = true := by simpa using hj
    have := h j (mem_univ j)
    simp only [reflB, hj', ite_true] at this
    exact neg_notMem_halfArc (hx j (mem_univ j)) this
  · intro h
    have : reflB ε x = x := funext fun j => by simp [reflB, h j]
    rwa [this]

/-- **The extension equals the function on the box.** -/
theorem ext_of_mem_boxSet {c : d → ℂ} {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ)
    {x : UnitAddTorus d} (hx : x ∈ boxSet d) : ext c Φ x = per Φ x := by
  rw [ext, Finset.sum_eq_single (fun _ => false)]
  · have : reflB (fun _ => false) x = x := funext fun j => by simp [reflB]
    simp [sign, this]
  · intro ε _ hε
    have : reflB ε x ∉ boxSet d := fun h => hε (funext ((reflB_mem_boxSet_iff hx).1 h))
    rw [per_eq_zero_of_notMem hΦ this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype d] [DecidableEq d] in
/-- The reflection of `ℝᵈ` lifting `reflB ε`. -/
theorem proj_reflR (ε : d → Bool) (y : d → ℝ) :
    proj (fun j => if ε j then -y j else y j) = reflB ε (proj y) := by
  funext j; by_cases h : ε j <;> simp [proj, reflB, h]

omit [DecidableEq d] in
theorem isSmooth_comp_reflB {φ : UnitAddTorus d → ℂ} (hφ : IsSmooth φ) (ε : d → Bool) :
    IsSmooth fun x => φ (reflB ε x) := by
  unfold IsSmooth at hφ ⊢
  have e : ((fun x => φ (reflB ε x)) ∘ proj) =
      (φ ∘ proj) ∘ fun y : d → ℝ => fun j => if ε j then -y j else y j := by
    funext y; simp [proj_reflR]
  rw [e]
  refine hφ.comp (contDiff_pi.2 fun j => ?_)
  by_cases h : ε j
  · simp only [h, ↓reduceIte]; exact (contDiff_apply ℝ (fun _ : d => ℝ) j).neg
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact contDiff_apply ℝ (fun _ : d => ℝ) j

/-- The extension of a test function is smooth on `𝕋ᵈ`. -/
theorem isSmooth_ext (c : d → ℂ) {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ) :
    IsSmooth (ext c Φ) := by
  unfold IsSmooth
  have e : ext c Φ ∘ proj = fun y => ∑ ε : d → Bool, sign c ε * per Φ (reflB ε (proj y)) := by
    funext y; rfl
  rw [e]
  exact ContDiff.sum fun ε _ => contDiff_const.mul (isSmooth_comp_reflB (isSmooth_per hΦ) ε)

theorem continuous_ext (c : d → ℂ) {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ) :
    Continuous (ext c Φ) := (isSmooth_ext c hΦ).continuous

/-- **The extension restricts back to the test function**: `(ext Φ)|_Q = Φ`. -/
theorem resQ_toL2_ext (c : d → ℂ) {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ) :
    resQ (toL2 (continuous_ext c hΦ)) = Domain.toL2 hΦ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_resQ (toL2 (continuous_ext c hΦ)),
    ae_Q_of_ae_boxSet (ae_restrict_of_ae (toL2_ae_eq (continuous_ext c hΦ))),
    Domain.coeFn_toL2 hΦ, ae_restrict_mem measurableSet_Q] with y h1 h2 h3 h4
  rw [h1, h2, h3, ext_of_mem_boxSet hΦ (proj_mem_boxSet (mem_Q.1 h4)), per_proj_of_mem h4]

/-- **The norm of the extension**: `‖ext Φ‖²_{L²(𝕋ᵈ)} = 2ᵈ ‖Φ‖²_{L²(Q)}` (`8` for the cube). -/
theorem norm_sq_toL2_ext {c : d → ℂ} (hc : ∀ j, c j * c j = 1) {Φ : (d → ℝ) → ℂ}
    (hΦ : Domain.IsTest (Q d) Φ) :
    ‖toL2 (continuous_ext c hΦ)‖ ^ 2 = 2 ^ Fintype.card d * ‖Domain.toL2 hΦ‖ ^ 2 := by
  rw [← resQ_toL2_ext c hΦ]
  refine norm_sq_eq_two_pow fun η => ?_
  have h := toL2_ae_eq (continuous_ext c hΦ)
  filter_upwards [h, (measurePreserving_reflB η).quasiMeasurePreserving.ae_eq_comp h] with x h1 h2
  change ‖(toL2 (continuous_ext c hΦ) : UnitAddTorus d → ℂ) (reflB η x)‖ = _
  rw [show (toL2 (continuous_ext c hΦ) : UnitAddTorus d → ℂ) (reflB η x) = ext c Φ (reflB η x)
    from h2, h1, ext_reflB hc, norm_mul, norm_sign hc, one_mul]

/-- `∂_k (φ ∘ R_ε) = ±(∂_k φ) ∘ R_ε`. -/
theorem partialT_comp_reflB {φ : UnitAddTorus d → ℂ} (hφ : Differentiable ℝ (φ ∘ proj))
    (ε : d → Bool) (k : d) (x : UnitAddTorus d) :
    partialT k (fun x => φ (reflB ε x)) x =
      (if ε k then -1 else 1) * partialT k φ (reflB ε x) := by
  have hadd : ∀ t : ℝ, reflB ε (x + proj (Pi.single k t)) =
      reflB ε x + proj (Pi.single k (if ε k then -t else t)) := fun t => by
    funext j
    by_cases hj : j = k
    · subst hj
      by_cases h : ε j
      · simp [reflB, proj, h]; abel
      · simp [reflB, proj, h]
    · by_cases h : ε j <;> simp [reflB, proj, h, hj]
  unfold partialT
  simp_rw [hadd]
  have hd := hasDerivAt_translate hφ k (reflB ε x) 0
  rw [Pi.single_zero, proj_zero, add_zero] at hd
  by_cases h : ε k
  · simp only [h, ↓reduceIte]
    have h2 : HasDerivAt (fun t : ℝ => φ (reflB ε x + proj (Pi.single k (-t))))
        ((-1 : ℝ) • partialT k φ (reflB ε x)) 0 :=
      hd.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
    rw [h2.deriv, hd.deriv]
    simp
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [hd.deriv, one_mul]

/-- **Weak derivatives of the extension**: `∂_k (ext_c Φ) = ext_{c'} (∂_k Φ)`, with the parity of
`x_k` reversed (`c'_k = -c_k`): differentiation in `x_k` exchanges odd and even. -/
theorem partialT_ext (c : d → ℂ) {Φ : (d → ℝ) → ℂ} (hΦ : Domain.IsTest (Q d) Φ) (k : d) :
    partialT k (ext c Φ) =
      ext (Function.update c k (-c k)) fun y => fderiv ℝ Φ y (Pi.single k 1) := by
  funext x
  have hd : ∀ ε : d → Bool, Differentiable ℝ ((fun x => per Φ (reflB ε x)) ∘ proj) := fun ε =>
    (isSmooth_comp_reflB (isSmooth_per hΦ) ε).contDiff_one.differentiable one_ne_zero
  have hsum : HasDerivAt (fun t : ℝ => ext c Φ (x + proj (Pi.single k t)))
      (∑ ε : d → Bool, sign c ε *
        partialT k (fun x => per Φ (reflB ε x)) (x + proj (Pi.single k 0))) 0 := by
    have := HasDerivAt.sum (u := Finset.univ) fun ε _ =>
      (hasDerivAt_translate (hd ε) k x 0).const_mul (sign c ε)
    convert this using 1
    funext t; simp [ext, Finset.sum_apply]
  unfold partialT
  rw [hsum.deriv, ext]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Pi.single_zero, proj_zero, add_zero,
    partialT_comp_reflB ((isSmooth_per hΦ).contDiff_one.differentiable one_ne_zero),
    partialT_per hΦ]
  have hs : sign (Function.update c k (-c k)) ε = (if ε k then -1 else 1) * sign c ε := by
    rw [sign, sign, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ (fun j => if ε j then c j else 1) (Finset.mem_univ k)]
    rw [show (∏ j ∈ Finset.univ.erase k,
        if ε j then Function.update c k (-c k) j else 1) =
        ∏ j ∈ Finset.univ.erase k, if ε j then c j else 1 from
      Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
    by_cases h : ε k <;> simp [h]
  rw [hs]; ring

end Extension

end Covering

end Geometry


/-! ### Families of three subspaces -/

section Sub3

variable {𝕜 : Type*} [RCLike 𝕜] {W0 W1 W2 : Type u}
  [NormedAddCommGroup W0] [InnerProductSpace 𝕜 W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace 𝕜 W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace 𝕜 W2] [CompleteSpace W2]

/-- Three subspaces `K₀ ⊆ W0`, `K₁ ⊆ W1`, `K₂ ⊆ W2` as a family on `Fin 3`. -/
def sub3 (K₀ : Submodule 𝕜 W0) (K₁ : Submodule 𝕜 W1) (K₂ : Submodule 𝕜 W2) :
    ∀ i : Fin 3, Submodule 𝕜 (W3 W0 W1 W2 i)
  | 0 => K₀
  | 1 => K₁
  | 2 => K₂

instance instHasOrthogonalProjectionSub3 (K₀ : Submodule 𝕜 W0) (K₁ : Submodule 𝕜 W1)
    (K₂ : Submodule 𝕜 W2) [K₀.HasOrthogonalProjection] [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] : ∀ i, (sub3 K₀ K₁ K₂ i).HasOrthogonalProjection
  | 0 => inferInstanceAs K₀.HasOrthogonalProjection
  | 1 => inferInstanceAs K₁.HasOrthogonalProjection
  | 2 => inferInstanceAs K₂.HasOrthogonalProjection

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
theorem mem_totalSub_sub3 {K₀ : Submodule 𝕜 W0} {K₁ : Submodule 𝕜 W1} {K₂ : Submodule 𝕜 W2}
    {x : PiLp 2 (W3 W0 W1 W2)} :
    x ∈ HilbertComplex.totalSub (sub3 K₀ K₁ K₂) ↔
      (x 0 : W0) ∈ K₀ ∧ (x 1 : W1) ∈ K₁ ∧ (x 2 : W2) ∈ K₂ := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    exacts [h0, h1, h2]

/-- A reducing subcomplex of a short complex from the two reducing pairs. -/
theorem reducingSubcomplex_sub3 (S : ShortHilbertComplex 𝕜 W0 W1 W2) {K₀ : Submodule 𝕜 W0}
    {K₁ : Submodule 𝕜 W1} {K₂ : Submodule 𝕜 W2} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection]
    (h₀ : S.d₀.IsReducingPair K₀ K₁) (h₁ : S.d₁.IsReducingPair K₁ K₂) :
    S.toHilbertComplex.ReducingSubcomplex (sub3 K₀ K₁ K₂) := by
  refine HilbertComplex.ReducingSubcomplex.of_rel fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp at hij
  exacts [h₀, h₁]

end Sub3

/-! ### Window total spaces of short complexes -/

section Slots

variable {W0 W1 W2 : Type u}

theorem ext3 {V0 V1 V2 : Type u} {x y : PiLp 2 (W3 V0 V1 V2)}
    (h0 : (x 0 : V0) = y 0) (h1 : (x 1 : V1) = y 1) (h2 : (x 2 : V2) = y 2) : x = y := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  exacts [h0, h1, h2]

/-- The first slot of the window total space, with its own type. -/
abbrev slot0 (y : PiLp 2 (W3 W0 W1 W2)) : W0 := y 0

/-- The second slot of the window total space, with its own type. -/
abbrev slot1 (y : PiLp 2 (W3 W0 W1 W2)) : W1 := y 1

/-- The third slot of the window total space, with its own type. -/
abbrev slot2 (y : PiLp 2 (W3 W0 W1 W2)) : W2 := y 2


end Slots

/-! ### Invariant cores of compressions -/

section Compression

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex ℝ c W} {S : ∀ i, Submodule ℝ (W i)} [∀ i, (S i).HasOrthogonalProjection]
  [∀ i, CompleteSpace (S i)]

omit [∀ i, CompleteSpace (W i)] in
theorem totalIncl_injective (S : ∀ i, Submodule ℝ (W i)) :
    Function.Injective (HilbertComplex.ReducingSubcomplex.totalIncl S) :=
  (HilbertComplex.ReducingSubcomplex.totalIncl S).injective

/-- The constraint family `K` seen inside the compressed spaces `S i`. -/
def compSub (S : ∀ i, Submodule ℝ (W i)) (K : ∀ i, Submodule ℝ (W i)) :
    ∀ i, Submodule ℝ (S i) := fun i => (K i).comap (S i).subtype

omit [∀ i, CompleteSpace (W i)] [∀ i, (S i).HasOrthogonalProjection] [∀ i, CompleteSpace (S i)] in
theorem mem_totalSub_compSub {K : ∀ i, Submodule ℝ (W i)} {y : PiLp 2 fun i => S i} :
    y ∈ HilbertComplex.totalSub (compSub S K) ↔
      HilbertComplex.ReducingSubcomplex.totalIncl S y ∈ HilbertComplex.totalSub K :=
  Iff.rfl

/-- **Invariant cores of a compression are invariant cores of the big complex**: for a reducing
subcomplex `S` of `H` and any family `K`, `y` lies in the invariant core of `∏ (K i ∩ S i)` for
the compressed wave group iff its inclusion lies in the invariant core of `∏ K i` for the wave
group of `H`. -/
theorem mem_invariantCore_compSub_iff (h : H.ReducingSubcomplex S) (K : ∀ i, Submodule ℝ (W i))
    (y : PiLp 2 fun i => S i) :
    y ∈ h.toHilbertComplex.waveGroup.invariantCore (HilbertComplex.totalSub (compSub S K)) ↔
      HilbertComplex.ReducingSubcomplex.totalIncl S y ∈
        H.waveGroup.invariantCore (HilbertComplex.totalSub K) := by
  simp only [C0Group.mem_invariantCore, mem_totalSub_compSub, h.waveGroup_toHilbertComplex]

/-- Stationary vectors of a compression are the stationary vectors of the big complex. -/
theorem mem_stationary_compSub_iff (h : H.ReducingSubcomplex S) (y : PiLp 2 fun i => S i) :
    y ∈ h.toHilbertComplex.waveGroup.stationary ↔
      HilbertComplex.ReducingSubcomplex.totalIncl S y ∈ H.waveGroup.stationary := by
  simp only [C0Group.mem_stationary]
  refine forall_congr' fun t => ?_
  rw [← h.waveGroup_toHilbertComplex, (totalIncl_injective S).eq_iff]

/-- Forward orbits of a compression are the forward orbits of the big complex. -/
theorem forward_compSub_iff (h : H.ReducingSubcomplex S) (K : ∀ i, Submodule ℝ (W i))
    (y : PiLp 2 fun i => S i) :
    (∀ t, 0 ≤ t → h.toHilbertComplex.waveGroup.S t y ∈ HilbertComplex.totalSub (compSub S K)) ↔
      ∀ t, 0 ≤ t → H.waveGroup.S t (HilbertComplex.ReducingSubcomplex.totalIncl S y) ∈
        HilbertComplex.totalSub K := by
  simp only [mem_totalSub_compSub, h.waveGroup_toHilbertComplex]

/-- The domain of the wave operator of a compression. -/
theorem mem_wave_domain_compress_iff (h : H.ReducingSubcomplex S) (y : PiLp 2 fun i => S i) :
    y ∈ h.toHilbertComplex.wave.domain ↔
      HilbertComplex.ReducingSubcomplex.totalIncl S y ∈ H.wave.domain := by
  rw [HilbertComplex.mem_wave_domain, HilbertComplex.mem_wave_domain]
  refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun j => ?_)
  change y j ∈ (h.toHilbertComplex.dual.d j i).domain ↔ _
  rw [HilbertComplex.ReducingSubcomplex.dual_toHilbertComplex_d]
  exact Iff.rfl

end Compression

/-! ### Constraints invariant under a unitary action -/

section Action

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex ℝ c W} {Γ : Type*} [Group Γ] [Fintype Γ]

/-- A unitary preserving a closed subspace `K` and its inverse commutes with `P_K`. -/
theorem starProjection_comm_of_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U : E ≃ₗᵢ[ℝ] E) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hU : ∀ x ∈ K, U x ∈ K) (hU' : ∀ x ∈ K, U.symm x ∈ K) (x : E) :
    K.starProjection (U x) = U (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (u := U x)
    (hU _ (K.starProjection_apply_mem x)) fun k hk => ?_
  rw [← _root_.map_sub, show k = U (U.symm k) from (U.apply_symm_apply k).symm,
    U.inner_map_map]
  exact K.starProjection_inner_eq_zero x _ (hU' k hk)

instance instHasOrthogonalProjectionCompSub (S : ∀ i, Submodule ℝ (W i))
    [∀ i, CompleteSpace (S i)] (K : ∀ i, Submodule ℝ (W i)) [∀ i, (K i).HasOrthogonalProjection]
    (i : ι) : (compSub S K i).HasOrthogonalProjection := by
  have hc : IsClosed (compSub S K i : Set (S i)) :=
    ((K i).isClosed_of_hasOrthogonalProjection).preimage continuous_subtype_val
  have : CompleteSpace (compSub S K i) := hc.completeSpace_coe
  infer_instance

omit [Fintype ι] in
/-- **Invariant constraints descend to the fixed complex**: if `K` is a reducing subcomplex of `H`
whose spaces are preserved by a finite unitary action, then `K ∩ Fix` is a reducing subcomplex
of the fixed (method-of-images) complex. -/
theorem reducingSubcomplex_compSub_fixed (A : H.Action Γ) {K : ∀ i, Submodule ℝ (W i)}
    [∀ i, (K i).HasOrthogonalProjection] (hK : H.ReducingSubcomplex K)
    (hA : ∀ g i, ∀ x ∈ K i, A.act g i x ∈ K i) :
    A.fixedComplex.ReducingSubcomplex (compSub A.fixed K) := by
  have hS : ∀ i (x : A.fixed i), ∃ y : A.fixed i,
      A.reducingSubcomplex_fixed.toScaledEmbedding.J i y = (K i).starProjection
        (A.reducingSubcomplex_fixed.toScaledEmbedding.J i x) := by
    intro i x
    refine ⟨⟨(K i).starProjection x, fun g => ?_⟩, rfl⟩
    have hinv : ∀ y ∈ K i, (A.act g i).symm y ∈ K i := fun y hy => by
      have e : (A.act g i).symm y = A.act g⁻¹ i y := by
        apply (A.act g i).injective
        rw [LinearIsometryEquiv.apply_symm_apply, A.act_act_inv]
      rw [e]; exact hA g⁻¹ i y hy
    rw [← starProjection_comm_of_invariant (A.act g i) (K i) (hA g i) hinv, x.2 g]
  exact A.reducingSubcomplex_fixed.toScaledEmbedding.reducingSubcomplex_comap hK hS

end Action

/-! ### Zero differentials -/

/-- Two zero differentials commute with any pair of maps. -/
theorem comm_of_eq_zero {E F E' F' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F'] [Module ℝ F']
    {T : E →ₗ.[ℝ] F} {T' : E' →ₗ.[ℝ] F'} (hT : T = 0) (hT' : T' = 0) (J : E →ₗ[ℝ] E')
    (J' : F →ₗ[ℝ] F') (κ : ℝ) (x : T.domain) (h : J x ∈ T'.domain) :
    T' ⟨J x, h⟩ = κ • J' (T x) := by
  rw [LinearPMap.apply_eq_zero_of_eq_zero hT', LinearPMap.apply_eq_zero_of_eq_zero hT x,
    _root_.map_zero, smul_zero]

/-! ### Stationary vectors -/

/-- A stationary vector in the domain of the generator is killed by the generator. -/
theorem generator_eq_zero_of_mem_stationary {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (G : C0Group ℝ E) (x : G.generator.domain)
    (hx : (x : E) ∈ G.stationary) : G.generator x = 0 := by
  refine G.generator_apply_eq ?_
  have e : (fun t => G.S t x) = fun _ => (x : E) := funext (C0Group.mem_stationary.1 hx)
  rw [e]
  exact hasDerivAt_const _ _

end Feec.Models.Cube
