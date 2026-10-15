module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Pi
public import Feec.Ch4.BoxStatic
public import Feec.Ch4.BoxThesis
public import Feec.Ch4.BoundedDomainExt

/-!
# Box identification (draft)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory Set Filter Topology
open scoped LinearPMap

namespace Feec.BoxIdent

open Feec.Torus Feec.TorusWeak Feec.Box UnitAddTorus
open Feec.BoundedDomain (R3 Ix IsTest curlM)

/-- The partial derivative of `Feec.BoundedDomain` (`∂_k f = Df(x) e_k`). -/
local notation "pd" => Feec.BoundedDomain.pd

attribute [local instance] Feec.Torus.instMeasureSpaceUnitAddCircle_feec

/-- The local Haar measure on `ℝ/ℤ` is an additive Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The box in `ℝ³` and the covering map -/

/-- The open box `Q = (0, ½)³ ⊂ ℝ³`. -/
def Qr : Set R3 := univ.pi fun _ => Ioo (0 : ℝ) (1 / 2)

/-- The half-open unit cube `(0, 1]³`, a fundamental domain of `ℤ³`. -/
def cube : Set R3 := univ.pi fun _ => Ioc (0 : ℝ) 1

theorem isOpen_Qr : IsOpen Qr := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem measurableSet_Qr : MeasurableSet Qr := isOpen_Qr.measurableSet

theorem isBounded_Qr : Bornology.IsBounded Qr :=
  (Metric.isBounded_Icc (fun _ : Fin 3 => (0 : ℝ)) fun _ => 1 / 2).subset fun _ hy =>
    ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩

theorem Qr_subset_cube : Qr ⊆ cube := fun y hy i hi =>
  ⟨(hy i hi).1, (hy i hi).2.le.trans (by norm_num)⟩

/-- The covering map `ℝ → ℝ/ℤ` is measure preserving from `(0, 1]` to the local Haar
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

/-- `proj : ℝ³ → 𝕋³` is measure preserving from the cube `(0, 1]³`. -/
theorem measurePreserving_proj_cube :
    MeasurePreserving proj (volume.restrict cube) (volume : Measure T3) := by
  have h := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure UnitAddCircle))
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

/-- `proj⁻¹(box) ∩ (0, 1]³ = (0, ½)³`. -/
theorem preimage_boxSet_inter_cube : proj ⁻¹' boxSet ∩ cube = Qr := by
  ext y
  constructor
  · rintro ⟨h1, h2⟩ i _
    exact mem_Ioo_of_coe_mem_halfArc (h2 i (mem_univ i)) (h1 i (mem_univ i))
  · intro hy
    exact ⟨proj_mem_boxSet fun i => hy i (mem_univ i), Qr_subset_cube hy⟩

/-- `proj` is measure preserving from `Q ⊂ ℝ³` onto the box of `𝕋³`. -/
theorem measurePreserving_proj_box :
    MeasurePreserving proj (volume.restrict Qr) (volume.restrict boxSet) := by
  have h := measurePreserving_proj_cube.restrict_preimage measurableSet_boxSet
  rwa [Measure.restrict_restrict (measurableSet_boxSet.preimage
    measurePreserving_proj_cube.measurable), preimage_boxSet_inter_cube] at h

/-- **Change of variables between the box of `𝕋³` and `Q ⊂ ℝ³`.** -/
theorem setIntegral_boxSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : T3 → E)
    (hg : AEStronglyMeasurable g (volume.restrict boxSet)) :
    ∫ x in boxSet, g x = ∫ y in Qr, g (proj y) := by
  rw [← measurePreserving_proj_box.map_eq] at hg ⊢
  exact integral_map measurePreserving_proj_box.measurable.aemeasurable hg

/-- Functions vanishing off the box integrate over `𝕋³` as over `Q ⊂ ℝ³`. -/
theorem integral_eq_Qr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : T3 → E}
    (hg : AEStronglyMeasurable g volume) (h0 : ∀ x, x ∉ boxSet → g x = 0) :
    ∫ x, g x = ∫ y in Qr, g (proj y) := by
  rw [← setIntegral_boxSet g hg.restrict,
    setIntegral_eq_integral_of_forall_compl_eq_zero h0]

/-- Almost-everywhere statements on the box pull back to `Q`. -/
theorem ae_Qr_of_ae_boxSet {p : T3 → Prop} (h : ∀ᵐ x ∂volume.restrict boxSet, p x) :
    ∀ᵐ y ∂volume.restrict Qr, p (proj y) :=
  measurePreserving_proj_box.quasiMeasurePreserving.ae h


/-! ## Restriction of periodic fields to `Q` -/

/-- **Restriction to `Q`** (real part): `f ↦ Re (f ∘ proj)|_Q`, a contraction
`L²(𝕋³; ℂ) → L²(Q; ℝ)`. -/
def resQ : L2T →L[ℝ] BoundedDomain.L2 Qr :=
  (Complex.reCLM.compLpL 2 (volume.restrict Qr)).comp
    (((Lp.compMeasurePreservingₗᵢ ℝ proj measurePreserving_proj_box).toContinuousLinearMap).comp
      (LpToLpRestrictCLM T3 ℂ ℝ volume 2 boxSet))

/-- `resQ f = Re (f ∘ proj)` almost everywhere on `Q`. -/
theorem coeFn_resQ (f : L2T) :
    (resQ f : R3 → ℝ) =ᵐ[volume.restrict Qr] fun y => ((f : T3 → ℂ) (proj y)).re := by
  have h1 := LpToLpRestrictCLM_coeFn ℝ boxSet f
  have h2 := Lp.coeFn_compMeasurePreserving
    (LpToLpRestrictCLM T3 ℂ ℝ volume 2 boxSet f) measurePreserving_proj_box
  have h3 := Complex.reCLM.coeFn_compLp (Lp.compMeasurePreserving proj measurePreserving_proj_box
    (LpToLpRestrictCLM T3 ℂ ℝ volume 2 boxSet f))
  filter_upwards [h2, h3, ae_Qr_of_ae_boxSet h1] with y e2 e3 e1
  change (Complex.reCLM.compLp (Lp.compMeasurePreserving proj measurePreserving_proj_box
    (LpToLpRestrictCLM T3 ℂ ℝ volume 2 boxSet f)) : R3 → ℝ) y = _
  rw [e3, e2]
  simp only [Function.comp_apply, Complex.reCLM_apply]
  rw [e1]

/-- Restriction of matrix fields, entrywise. -/
def resM : MField →L[ℝ] BoundedDomain.L2M Qr where
  toFun A := WithLp.toLp 2 fun p => resQ (A p)
  map_add' A B := by ext p; simp
  map_smul' c A := by ext p; simp
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    resQ.continuous.comp (PiLp.continuous_apply 2 _ p))

@[simp] theorem resM_apply (A : MField) (p : Ix) : resM A p = resQ (A p) := rfl

/-- Restriction of vector fields, entrywise. -/
def resV : VField →L[ℝ] BoundedDomain.L2V Qr where
  toFun u := WithLp.toLp 2 fun a => resQ (u a)
  map_add' u v := by ext a; simp
  map_smul' c u := by ext a; simp
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a =>
    resQ.continuous.comp (PiLp.continuous_apply 2 _ a))

@[simp] theorem resV_apply (u : VField) (a : Fin 3) : resV u a = resQ (u a) := rfl

/-! ## Periodization of test functions supported in `Q` -/

/-- The representative in `[0, 1)³` of a point of `𝕋³`. -/
def rep (x : T3) : R3 := fun i => (AddCircle.equivIco 1 0 (x i) : ℝ)

theorem rep_proj (y : R3) (i : Fin 3) :
    rep (proj y) i = y i - (⌊y i⌋ : ℝ) := by
  simp only [rep, proj]
  rw [AddCircle.coe_equivIco_mk_apply]
  rw [div_one, mul_one, Int.fract]

theorem proj_rep (x : T3) : proj (rep x) = x := by
  funext i
  simp [proj, rep]

/-- **Periodization** of a function supported in `Q`: `per Φ (x) = Φ(rep x)`, the
`ℤ³`-periodic extension of `Φ`, as a complex-valued function on `𝕋³`. -/
def per (Φ : R3 → ℝ) (x : T3) : ℂ := (Φ (rep x) : ℂ)

/-- The integer vector `⌊y + ¼⌋`: near `y`, the only translate of `Q` that can meet the
neighbourhood is `Q + ⌊y + ¼⌋`. -/
def nvec (y : R3) (i : Fin 3) : ℝ := (⌊y i + 1 / 4⌋ : ℤ)

section Per

variable {Φ : R3 → ℝ}

theorem mem_Qr_of_ne_zero (hΦ : IsTest Qr Φ) {w : R3} (h : Φ w ≠ 0) : w ∈ Qr :=
  hΦ.tsupport_subset (subset_tsupport _ h)

/-- (C1) a nonzero translate `Φ(z - m)` forces `m = ⌊z⌋`. -/
theorem eq_floor_self_of_ne_zero (hΦ : IsTest Qr Φ) {z : R3} {m : Fin 3 → ℤ}
    (h : Φ (fun i => z i - (m i : ℝ)) ≠ 0) (i : Fin 3) : ⌊z i⌋ = m i := by
  have hm := mem_Qr_of_ne_zero hΦ h i (mem_univ i)
  simp only [mem_Ioo] at hm
  rw [Int.floor_eq_iff]
  constructor <;> linarith [hm.1, hm.2]

/-- (C2) near `y`, a nonzero translate `Φ(z - m)` forces `m = ⌊y + ¼⌋`. -/
theorem eq_floor_of_ne_zero (hΦ : IsTest Qr Φ) {y z : R3} (hz : dist z y < 1 / 8)
    {m : Fin 3 → ℤ} (h : Φ (fun i => z i - (m i : ℝ)) ≠ 0) (i : Fin 3) :
    ⌊y i + 1 / 4⌋ = m i := by
  have hm := mem_Qr_of_ne_zero hΦ h i (mem_univ i)
  have hd : |z i - y i| < 1 / 8 := by
    have := (dist_le_pi_dist z y i).trans_lt hz
    rwa [Real.dist_eq] at this
  rw [abs_lt] at hd
  simp only [mem_Ioo] at hm
  rw [Int.floor_eq_iff]
  constructor <;> linarith [hm.1, hm.2, hd.1, hd.2]

theorem per_proj (y : R3) :
    per Φ (proj y) = (Φ (fun i => y i - (⌊y i⌋ : ℝ)) : ℂ) := by
  simp only [per]
  congr 2
  funext i
  exact rep_proj y i

/-- **Local form of the periodization**: near `y`, `per Φ ∘ proj = Φ(· - ⌊y + ¼⌋)`. -/
theorem per_eventuallyEq (hΦ : IsTest Qr Φ) (y : R3) :
    (per Φ ∘ proj) =ᶠ[𝓝 y] fun z => (Φ (z - nvec y) : ℂ) := by
  filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0 : ℝ) < 1 / 8)] with z hz
  rw [Metric.mem_ball] at hz
  simp only [Function.comp_apply, per_proj]
  congr 1
  set d : Fin 3 → ℤ := fun i => ⌊z i⌋
  set n : Fin 3 → ℤ := fun i => ⌊y i + 1 / 4⌋
  have hn : (z - nvec y) = fun i => z i - (n i : ℝ) := rfl
  rw [hn]
  by_cases hdn : d = n
  · have : (fun i => z i - (⌊z i⌋ : ℝ)) = fun i => z i - (n i : ℝ) := by
      funext i
      have := congrFun hdn i
      simp only [d] at this
      rw [this]
    rw [this]
  · have h1 : Φ (fun i => z i - (d i : ℝ)) = 0 := by
      by_contra h
      exact hdn (funext fun i => (eq_floor_of_ne_zero hΦ hz h i).symm)
    have h2 : Φ (fun i => z i - (n i : ℝ)) = 0 := by
      by_contra h
      exact hdn (funext fun i => eq_floor_self_of_ne_zero hΦ h i)
    exact h1.trans h2.symm

/-- The periodization of a test function is smooth on `𝕋³`. -/
theorem isSmooth_per (hΦ : IsTest Qr Φ) : IsSmooth (per Φ) := by
  unfold IsSmooth
  rw [contDiff_iff_contDiffAt]
  intro y
  have hs : ContDiff ℝ (⊤ : ℕ∞) fun z : R3 => (Φ (z - nvec y) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hΦ.contDiff.comp (contDiff_id.sub contDiff_const))
  exact hs.contDiffAt.congr_of_eventuallyEq (per_eventuallyEq hΦ y)

/-- On `Q`, `per Φ ∘ proj = Φ`. -/
theorem per_proj_of_mem {y : R3} (hy : y ∈ Qr) : per Φ (proj y) = Φ y := by
  rw [per_proj]
  congr 2
  funext i
  have : ⌊y i⌋ = 0 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num <;> linarith [(hy i (mem_univ i)).1, (hy i (mem_univ i)).2]
  simp [this]

/-- The periodization is supported in the box. -/
theorem tsupport_per_subset (hΦ : IsTest Qr Φ) : tsupport (per Φ) ⊆ boxSet := by
  have hK : IsCompact (proj '' tsupport Φ) :=
    hΦ.hasCompactSupport.isCompact.image isOpenQuotientMap_proj.continuous
  have hsub : Function.support (per Φ) ⊆ proj '' tsupport Φ := by
    intro x hx
    refine ⟨rep x, subset_tsupport _ fun h => hx ?_, proj_rep x⟩
    simp [per, h]
  refine (closure_minimal hsub hK.isClosed).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  exact proj_mem_boxSet fun i => hΦ.tsupport_subset hy i (mem_univ i)

theorem per_eq_zero_of_notMem (hΦ : IsTest Qr Φ) {x : T3} (hx : x ∉ boxSet) : per Φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_per_subset hΦ h)

/-- **Derivatives of the periodization**: `∂_c (per Φ) = per (∂_c Φ)`. -/
theorem partialT_per (hΦ : IsTest Qr Φ) (c : Fin 3) : partialT c (per Φ) = per (pd c Φ) := by
  funext x
  obtain ⟨y, rfl⟩ := proj_surjective x
  have hd : Differentiable ℝ (per Φ ∘ proj) :=
    (isSmooth_per hΦ).contDiff_one.differentiable one_ne_zero
  rw [partialT_proj hd, (per_eventuallyEq hΦ y).fderiv_eq]
  have h2 := per_eventuallyEq (hΦ.pdiff c) y
  have h2y : per (pd c Φ) (proj y) = (pd c Φ (y - nvec y) : ℂ) := h2.eq_of_nhds
  rw [h2y]
  have hf : HasFDerivAt (fun z : R3 => (Φ (z - nvec y) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ Φ (y - nvec y))) y := by
    have h1 : HasFDerivAt (fun z : R3 => Φ (z - nvec y)) (fderiv ℝ Φ (y - nvec y)) y :=
      ((hΦ.differentiable (y - nvec y)).hasFDerivAt).comp y
        ((hasFDerivAt_id y).sub_const (nvec y))
    exact Complex.ofRealCLM.hasFDerivAt.comp y h1
  rw [hf.fderiv]
  rfl

/-- **Transfer of pairings**: `Re ∫_{𝕋³} f · per Φ = ∫_Q Re(f) Φ` for test functions `Φ`
supported in `Q`. -/
theorem re_integral_mul_per (f : L2T) (hΦ : IsTest Qr Φ) :
    (∫ x, (f : T3 → ℂ) x * per Φ x).re = ∫ y, resQ f y * Φ y ∂volume.restrict Qr := by
  have hc : Continuous (per Φ) := (isSmooth_per hΦ).continuous
  have hg : AEStronglyMeasurable (fun x => (f : T3 → ℂ) x * per Φ x) volume :=
    (Lp.aestronglyMeasurable f).mul hc.aestronglyMeasurable
  rw [integral_eq_Qr hg fun x hx => by simp [per_eq_zero_of_notMem hΦ hx]]
  have hint : Integrable (fun y => (f : T3 → ℂ) (proj y) * per Φ (proj y))
      (volume.restrict Qr) :=
    (measurePreserving_proj_box.integrable_comp hg.restrict).2
      (integrable_mul_continuous f hc).restrict
  change RCLike.re (∫ y in Qr, (f : T3 → ℂ) (proj y) * per Φ (proj y)) = _
  rw [← integral_re hint]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_resQ f, ae_restrict_mem measurableSet_Qr] with y h1 h2
  rw [per_proj_of_mem h2, h1]
  simp

/-- **Restriction of weak first-order operators with real coefficients**: if
`g = Σ α_{cp} ∂_c f_p` weakly on `𝕋³`, then `Re g|_Q = Σ α_{cp} ∂_c (Re f_p|_Q)` weakly on `Q`
(tested against `C_c^∞(Q)`). -/
theorem resQ_isWeakFO {P : Type*} [Fintype P] {α : Fin 3 → P → ℝ} {f : P → L2T} {g : L2T}
    (h : IsWeakFO (fun c p => (α c p : ℂ)) f g) (hΦ : IsTest Qr Φ) :
    ∑ c, ∑ p, α c p * ∫ y, resQ (f p) y * pd c Φ y ∂volume.restrict Qr =
      -∫ y, resQ g y * Φ y ∂volume.restrict Qr := by
  have h1 := h (per Φ) (isSmooth_per hΦ)
  rw [integral_sum_fo _ f (isSmooth_per hΦ)] at h1
  simp only [partialT_per hΦ] at h1
  have h2 := congrArg Complex.re h1
  simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.neg_re] at h2
  have hc : ∀ c p, (∫ x, (f p : T3 → ℂ) x * per (pd c Φ) x).re =
      ∫ y, resQ (f p) y * pd c Φ y ∂volume.restrict Qr := fun c p =>
    re_integral_mul_per _ (hΦ.pdiff c)
  simp only [hc, re_integral_mul_per _ hΦ] at h2
  exact h2

end Per

/-! ## Restriction of the periodic Sobolev spaces to `Q` -/

/-- Restriction of weak partial derivatives. -/
theorem resQ_hasWeakPartial {j : Fin 3} {f g : L2T} (h : HasWeakPartial j f g) {Φ : R3 → ℝ}
    (hΦ : IsTest Qr Φ) :
    ∫ y, resQ f y * pd j Φ y ∂volume.restrict Qr = -∫ y, resQ g y * Φ y ∂volume.restrict Qr := by
  rw [hasWeakPartial_iff_isWeakFO] at h
  have h' : IsWeakFO (fun c (_ : Unit) => ((if c = j then (1 : ℝ) else 0 : ℝ) : ℂ))
      (fun _ => f) g := by
    convert h using 3; split_ifs <;> simp
  have := resQ_isWeakFO h' hΦ
  simpa using this

/-- The finite-sum identity relating the two forms of the weak row-wise curl. -/
theorem curl_sum_identity (J : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    ∑ ik : Ix, (J ik.1 ik.2 (ik.2 + 1) (ik.2 + 2) - J ik.1 ik.2 (ik.2 + 2) (ik.2 + 1)) =
      -∑ ib : Ix, ∑ c, ∑ d, Feec.eps3 ib.2 c d * J ib.1 d c ib.2 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Constraints.eps3_apply]
  norm_num
  ring

/-- **Restriction of the weak curl**: if `C = curl A` weakly on `𝕋³`, then
`Re C|_Q = curl (Re A|_Q)` weakly on `Q`, in the form of the definition of `H(curl, Q)`
(`Feec.BoundedDomain.HcurlM`). -/
theorem resM_weakCurl {A C : MField} (h : IsWeakCurl A C) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    ∑ ij, ∫ x, resM A ij x * curlM Φ ij x ∂volume.restrict Qr =
      ∑ ij, ∫ x, resM C ij x * Φ ij x ∂volume.restrict Qr := by
  set J : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun a d c b =>
    ∫ y, resQ (A (a, d)) y * pd c (Φ (a, b)) y ∂volume.restrict Qr
  have hT : ∀ a b, ∑ c, ∑ d, Feec.eps3 b c d * J a d c b =
      -∫ y, resQ (C (a, b)) y * Φ (a, b) y ∂volume.restrict Qr := fun a b =>
    resQ_isWeakFO (α := fun c d => Feec.eps3 b c d) (f := fun d => A (a, d))
      (h a b) (hΦ (a, b))
  have hL : ∀ ik : Ix, ∫ x, resM A ik x * curlM Φ ik x ∂volume.restrict Qr =
      J ik.1 ik.2 (ik.2 + 1) (ik.2 + 2) - J ik.1 ik.2 (ik.2 + 2) (ik.2 + 1) := by
    rintro ⟨i, k⟩
    simp only [curlM, resM_apply, mul_sub, J]
    exact integral_sub (BoundedDomain.integrable_mul _ ((hΦ _).pdiff _).memLp)
      (BoundedDomain.integrable_mul _ ((hΦ _).pdiff _).memLp)
  rw [Finset.sum_congr rfl fun ik _ => hL ik, curl_sum_identity J]
  simp only [hT, Finset.sum_neg_distrib, neg_neg, resM_apply]

/-- **Periodic `H(curl)` restricts into `H(curl, Q)`**, with the restricted weak curl. -/
theorem resM_mem_HcurlM {A C : MField} (h : IsWeakCurl A C) : resM A ∈ BoundedDomain.HcurlM Qr :=
  ⟨resM C, fun _ hΦ => resM_weakCurl h hΦ⟩


/-- **Restriction of the weak row-wise divergence**: if `D = div A` weakly on `𝕋³`, then
`Re D|_Q = div (Re A|_Q)` weakly on `Q`, in the form of `Feec.BoundedDomain.HdivM`. -/
theorem resM_weakDiv {A : MField} {D : VField} (h : IsWeakDiv A D) {φ : Fin 3 → R3 → ℝ}
    (hφ : ∀ i, IsTest Qr (φ i)) :
    ∑ ij : Ix, ∫ x, resM A ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Qr =
      -∑ i, ∫ x, resV D i x * φ i x ∂volume.restrict Qr := by
  have row : ∀ a, ∑ b, ∫ x, resQ (A (a, b)) x * pd b (φ a) x ∂volume.restrict Qr =
      -∫ x, resQ (D a) x * φ a x ∂volume.restrict Qr := by
    intro a
    have hFO : IsWeakFO (fun c b => ((if c = b then (1 : ℝ) else 0 : ℝ) : ℂ))
        (fun b => A (a, b)) (D a) := fun ψ hψ => by
      rw [← h a ψ hψ]
      congr 1; funext x
      simp [ite_mul, apply_ite (fun r : ℝ => (r : ℂ))]
    have := resQ_isWeakFO hFO (hφ a)
    simpa [ite_mul] using this
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => row a

/-- **Periodic `H(div)` restricts into `H(div, Q)`**. -/
theorem resM_mem_HdivM {A : MField} {D : VField} (h : IsWeakDiv A D) :
    resM A ∈ BoundedDomain.HdivM Qr :=
  ⟨resV D, fun _ hφ => resM_weakDiv h hφ⟩

/-- **Restriction of the weak gradient**: if `G = ∇u` weakly on `𝕋³`, then `Re G|_Q = ∇(Re u|_Q)`
weakly on `Q`: `∫_Q Re u_a ∂_b φ = -∫_Q Re G_{ab} φ` for `φ ∈ C_c^∞(Q)`. -/
theorem resV_weakGrad {u : VField} {G : MField} (h : IsWeakGrad u G) (a b : Fin 3)
    {φ : R3 → ℝ} (hφ : IsTest Qr φ) :
    ∫ x, resV u a x * pd b φ x ∂volume.restrict Qr =
      -∫ x, resM G (a, b) x * φ x ∂volume.restrict Qr :=
  resQ_hasWeakPartial (h a b) hφ

/-- Fields vanishing a.e. on the box restrict to `0`. -/
theorem resQ_eq_zero_of_ae {f : L2T} (h : (f : T3 → ℂ) =ᵐ[volume.restrict boxSet] 0) :
    resQ f = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_resQ f, ae_Qr_of_ae_boxSet h,
    Lp.coeFn_zero ℝ 2 (volume.restrict Qr)] with y h1 h2 h3
  rw [h1, h3, h2]
  simp

/-! ## The box model (Fourier coefficients) restricted to `Q` -/

/-- Entries of the inverse Fourier transform of a matrix field. -/
theorem matrixFourier_symm_apply (A : L2M) (p : Ix) :
    matrixFourier.symm A p = ofCoeff (entry p A) := rfl

/-- Entries of the inverse Fourier transform of a vector field. -/
theorem vectorFourier_symm_apply (σ : L2V) (a : Fin 3) :
    vectorFourier.symm σ a = ofCoeff ((swapL2 (ι := Z3) (P := Fin 3)).symm σ a) := rfl

/-- Restriction to `Q` of a matrix field of the box model (given by Fourier coefficients). -/
def resB : L2M →L[ℝ] BoundedDomain.L2M Qr :=
  resM.comp ((matrixFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ)

theorem resB_apply (A : L2M) (p : Ix) : resB A p = resQ (ofCoeff (entry p A)) := rfl

/-- Restriction to `Q` of a vector field of the box model. -/
def resBV : L2V →L[ℝ] BoundedDomain.L2V Qr :=
  resV.comp ((vectorFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ)

theorem resBV_apply (σ : L2V) (a : Fin 3) : resBV σ a = resQ (vectorFourier.symm σ a) := rfl

/-- `ofCoeff` is additive. -/
theorem ofCoeff_sub (f g : L2 Z3 ℂ) : ofCoeff (f - g) = ofCoeff f - ofCoeff g := map_sub _ _ _

/-- `ofCoeff` commutes with finite sums. -/
theorem ofCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → L2 Z3 ℂ) :
    ofCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, ofCoeff (f i) := map_sum _ _ _

/-- **The box `H(curl)` restricts into `H(curl, Q)`**, and the periodic curl restricts to the
adjoint `d1*` of the thesis' complex on `Q` (the weak curl, no boundary condition). -/
theorem resB_curl {A : L2M} (hA : A ∈ Hcurl) :
    ∃ h : resB A ∈ (BoundedDomain.thesisComplex isOpen_Qr isBounded_Qr).d1†.domain,
      (BoundedDomain.thesisComplex isOpen_Qr isBounded_Qr).d1† ⟨resB A, h⟩ =
        resB (curlT ⟨A, hA⟩) := by
  have hw : IsWeakCurl (matrixFourier.symm A) (matrixFourier.symm (curlT ⟨A, hA⟩)) :=
    (isWeakCurl_iff _ _).2 fun k => by
      simp only [LinearIsometryEquiv.apply_symm_apply]
      rfl
  exact BoundedDomain.thesisComplex_adjoint_d1_apply isOpen_Qr isBounded_Qr
    fun _ hΦ => resM_weakCurl hw hΦ

theorem resB_mem_HcurlM {A : L2M} (hA : A ∈ Hcurl) : resB A ∈ BoundedDomain.HcurlM Qr :=
  (BoundedDomain.thesisComplex_adjoint_d1_iff isOpen_Qr isBounded_Qr).1 (resB_curl hA).1

/-- **The box `H(div)` restricts into `H(div, Q)`**, and `grad*` of the periodic complex
restricts to `d0* = -div` of the thesis' complex on `Q`. -/
theorem resB_div {A : L2M} (hA : A ∈ Hdiv) :
    ∃ h : resB A ∈ (BoundedDomain.thesisComplex isOpen_Qr isBounded_Qr).d0†.domain,
      (BoundedDomain.thesisComplex isOpen_Qr isBounded_Qr).d0† ⟨resB A, h⟩ =
        -resBV (TorusWeak.divT ⟨A, hA⟩) := by
  have hw : IsWeakDiv (matrixFourier.symm A) (vectorFourier.symm (TorusWeak.divT ⟨A, hA⟩)) :=
    (isWeakDiv_iff _ _).2 fun k => by
      simp only [LinearIsometryEquiv.apply_symm_apply]
      rfl
  exact BoundedDomain.thesisComplex_adjoint_d0_apply isOpen_Qr isBounded_Qr
    fun _ hφ => resM_weakDiv hw hφ

/-- **`L²(TSD)` of the box restricts into `L²(TSD)(Q)`**: symmetric, trace-free and
divergence-free on the box (in any parity class) gives the same on `Q`. -/
theorem resB_mem_TSD {τ : ℂ} {A : L2M} (hA : A ∈ boxTSD τ) : resB A ∈ BoundedDomain.TSD Qr := by
  have hsym : A ∈ boxSym := hA.1.1.2
  have htr : A ∈ boxTr := hA.1.2
  have hdiv : A ∈ boxDiv := hA.2
  rw [mem_boxSym] at hsym
  rw [mem_boxTr] at htr
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · rw [resB_apply, resB_apply, ← sub_eq_zero, ← map_sub, ← ofCoeff_sub]
    exact resQ_eq_zero_of_ae (hsym i j)
  · simp only [resB_apply, ← map_sum, ← ofCoeff_sum]
    exact resQ_eq_zero_of_ae htr
  · rw [mem_boxDiv] at hdiv
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h0 := hdiv a (per (φ a)) (isSmooth_per (hφ a)) (tsupport_per_subset (hφ a))
    simp only [partialT_per (hφ a)] at h0
    have h1 := congrArg Complex.re h0
    rw [Complex.re_sum, Complex.zero_re] at h1
    have hc : ∀ b, (∫ x, (ofCoeff (entry (a, b) A) : T3 → ℂ) x * per (pd b (φ a)) x).re =
        ∫ x, resB A (a, b) x * pd b (φ a) x ∂volume.restrict Qr := fun b =>
      re_integral_mul_per _ ((hφ a).pdiff b)
    simp only [hc] at h1
    exact h1


/-! ## Reflections of `𝕋³` and Fourier coefficients -/

/-- The reflection `x_i ↦ -x_i` of `𝕋³`. -/
def reflT (i : Fin 3) (x : T3) : T3 := fun j => if j = i then -x j else x j

@[simp] theorem reflT_reflT (i : Fin 3) (x : T3) : reflT i (reflT i x) = x := by
  funext j; by_cases h : j = i <;> simp [reflT, h]

theorem continuous_reflT (i : Fin 3) : Continuous (reflT i) := by
  show Continuous fun x : T3 => fun j => if j = i then -x j else x j
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · simp only [h, ↓reduceIte]; exact (continuous_apply i).neg
  · simp only [h, ↓reduceIte]; exact continuous_apply j

/-- The reflections preserve the Haar measure of `𝕋³`. -/
theorem measurePreserving_reflT (i : Fin 3) :
    MeasurePreserving (reflT i) (volume : Measure T3) volume := by
  have h := measurePreserving_pi (fun _ : Fin 3 => (volume : Measure UnitAddCircle))
    (fun _ => volume)
    (f := fun j => if j = i then (Neg.neg : UnitAddCircle → UnitAddCircle) else id) fun j => by
      split_ifs
      · exact Measure.measurePreserving_neg volume
      · exact MeasurePreserving.id volume
  convert h using 1
  funext x j
  by_cases hj : j = i <;> simp [reflT, hj]

/-- The reflection as a measurable equivalence. -/
def reflE (i : Fin 3) : T3 ≃ᵐ T3 where
  toFun := reflT i
  invFun := reflT i
  left_inv := reflT_reflT i
  right_inv := reflT_reflT i
  measurable_toFun := (measurePreserving_reflT i).measurable
  measurable_invFun := (measurePreserving_reflT i).measurable

theorem integral_comp_reflT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (i : Fin 3)
    (g : T3 → E) : ∫ x, g (reflT i x) = ∫ x, g x :=
  (measurePreserving_reflT i).integral_comp' (f := reflE i) g

theorem mFourier_reflT (i : Fin 3) (n : Z3) (x : T3) :
    mFourier n (reflT i x) = mFourier (Box.refl i n) x := by
  simp only [mFourier, ContinuousMap.coe_mk]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp only [reflT, Box.refl, Function.update_self]
    exact fourier_neg_arg _ _
  · simp only [reflT, hj, ↓reduceIte, Box.refl, Function.update_of_ne hj]

theorem refl_neg' (i : Fin 3) (k : Z3) : Box.refl i (-k) = -Box.refl i k := by
  ext j; by_cases h : j = i
  · subst h; simp [Box.refl]
  · simp [Box.refl, Function.update_of_ne h]

/-- **Fourier coefficients of a reflected function**: `(g ∘ R_i)^(k) = ĝ(R_i k)`. -/
theorem mFourierCoeff_comp_reflT (i : Fin 3) (g : T3 → ℂ) (k : Z3) :
    mFourierCoeff (fun x => g (reflT i x)) k = mFourierCoeff g (Box.refl i k) := by
  simp only [mFourierCoeff]
  have e : ∀ x, mFourier (-k) x • g (reflT i x) =
      (fun y => mFourier (-Box.refl i k) y • g y) (reflT i x) := fun x => by
    simp only
    rw [mFourier_reflT, ← refl_neg', refl_refl]
  simp_rw [e]
  exact integral_comp_reflT i (fun y => mFourier (-Box.refl i k) y • g y)

/-! ## Continuous matrix fields on `𝕋³` and their Fourier coefficients -/

/-- The box-model element (Fourier coefficients) of a continuous matrix field on `𝕋³`. -/
def cField (F : Ix → C(T3, ℂ)) : L2M :=
  matrixFourier (WithLp.toLp 2 fun p => (F p).toLp 2 volume ℂ)

theorem cField_apply (F : Ix → C(T3, ℂ)) (k : Z3) (p : Ix) :
    cField F k p = mFourierCoeff (F p) k := by
  obtain ⟨a, b⟩ := p
  rw [cField, matrixFourier_apply]
  exact mFourierCoeff_toLp (F (a, b)) k


theorem mFourierCoeff_real_smul (c : ℝ) (f : T3 → ℂ) (k : Z3) :
    mFourierCoeff (c • f) k = c • mFourierCoeff f k := by
  simp only [mFourierCoeff, Pi.smul_apply]
  rw [← integral_smul]
  congr 1; funext x
  rw [smul_comm]

theorem cField_add (F G : Ix → C(T3, ℂ)) : cField (F + G) = cField F + cField G := by
  simp only [cField, Pi.add_apply, map_add]
  rw [← map_add]
  rfl

theorem cField_smul (c : ℝ) (F : Ix → C(T3, ℂ)) : cField (c • F) = c • cField F := by
  refine lp.ext (funext fun k => ?_)
  ext p
  rw [cField_apply]
  change mFourierCoeff (c • ⇑(F p)) k = c • cField F k p
  rw [mFourierCoeff_real_smul, cField_apply]

theorem cField_sub (F G : Ix → C(T3, ℂ)) : cField (F - G) = cField F - cField G := by
  rw [sub_eq_add_neg, cField_add, show -G = (-1 : ℝ) • G by simp, cField_smul]
  simp [sub_eq_add_neg]

/-- The signed reflection `g ↦ c · g ∘ R_i` of a continuous function on `𝕋³`. -/
def sR (c : ℝ) (i : Fin 3) (g : C(T3, ℂ)) : C(T3, ℂ) :=
  c • g.comp ⟨reflT i, continuous_reflT i⟩

@[simp] theorem sR_apply (c : ℝ) (i : Fin 3) (g : C(T3, ℂ)) (x : T3) :
    sR c i g x = c * g (reflT i x) := by
  simp [sR, Complex.real_smul]

theorem mFourierCoeff_sR (c : ℝ) (i : Fin 3) (g : C(T3, ℂ)) (k : Z3) :
    mFourierCoeff (sR c i g) k = c * mFourierCoeff g (Box.refl i k) := by
  have : (sR c i g : T3 → ℂ) = c • fun x => g (reflT i x) := by
    funext x; simp [Complex.real_smul]
  rw [this, mFourierCoeff_real_smul, mFourierCoeff_comp_reflT, Complex.real_smul]

/-- **The row-wise reflection action on continuous fields**: `R_i` acts on the field with entries
`F_{ab}` by `F_{ab} ↦ ε colSign(i, b) · F_{ab} ∘ R_i`. -/
theorem R_cField (ε : ℝ) (hε : ε * ε = 1) (i : Fin 3) (F : Ix → C(T3, ℂ)) :
    (rowMf ε hε).lift.R i (cField F) = cField fun p => sR (ε * colSignR i p.2) i (F p) := by
  refine lp.ext (funext fun k => ?_)
  ext ⟨a, b⟩
  change rowSgn (ε : ℂ) i (cField F (Box.refl i k)) (a, b) = _
  rw [rowSgn_apply, cField_apply, cField_apply, mFourierCoeff_sR, colSign_eq]
  push_cast; ring

/-- `½ (g + c · g ∘ R_i)`. -/
def halfC (c : ℝ) (i : Fin 3) (g : C(T3, ℂ)) : C(T3, ℂ) := (1 / 2 : ℝ) • (g + sR c i g)

@[simp] theorem halfC_apply (c : ℝ) (i : Fin 3) (g : C(T3, ℂ)) (x : T3) :
    halfC c i g x = (1 / 2 : ℂ) * (g x + c * g (reflT i x)) := by
  simp [halfC, Complex.real_smul]; ring

/-- The average over the reflection group with signs `c_i`. -/
def avgC (c : Fin 3 → ℝ) (g : C(T3, ℂ)) : C(T3, ℂ) :=
  halfC (c 2) 2 (halfC (c 1) 1 (halfC (c 0) 0 g))

theorem half_cField (ε : ℝ) (hε : ε * ε = 1) (i : Fin 3) (F : Ix → C(T3, ℂ)) :
    (rowMf ε hε).lift.half i (cField F) =
      cField fun p => halfC (ε * colSignR i p.2) i (F p) := by
  rw [Refl3.half_apply, R_cField, ← cField_add, ← cField_smul]
  rfl

/-- **The averaging projection on continuous fields** (onto the parity class). -/
theorem avg_cField (ε : ℝ) (hε : ε * ε = 1) (F : Ix → C(T3, ℂ)) :
    (rowMf ε hε).lift.avg (cField F) =
      cField fun p => avgC (fun i => ε * colSignR i p.2) (F p) := by
  rw [Refl3.avg_apply, half_cField, half_cField, half_cField]
  rfl


/-! ## Values of the parity average on the box -/

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

theorem reflT_apply_self (i : Fin 3) (x : T3) : reflT i x i = -x i := by simp [reflT]

theorem reflT_apply_ne {i j : Fin 3} (h : j ≠ i) (x : T3) : reflT i x j = x j := by
  simp [reflT, h]

theorem halfC_eq_zero_of {c : ℝ} {i j : Fin 3} (hij : j ≠ i) {g : C(T3, ℂ)}
    (hg : ∀ x : T3, x j ∉ halfArc → g x = 0) :
    ∀ x : T3, x j ∉ halfArc → halfC c i g x = 0 := fun x hx => by
  rw [halfC_apply, hg x hx, hg (reflT i x) (by rwa [reflT_apply_ne hij])]
  simp

theorem halfC_eq_half {c : ℝ} {i : Fin 3} {g : C(T3, ℂ)}
    (hg : ∀ x : T3, x i ∉ halfArc → g x = 0) {x : T3} (hx : x i ∈ halfArc) :
    halfC c i g x = (1 / 2 : ℂ) * g x := by
  rw [halfC_apply, hg (reflT i x) (by rw [reflT_apply_self]; exact neg_notMem_halfArc hx)]
  simp

/-- **On the box, the parity average of a field supported in the box is `1/8` of it**: the
seven reflected copies vanish there. -/
theorem avgC_of_mem_boxSet (c : Fin 3 → ℝ) {g : C(T3, ℂ)} (hg : ∀ x, x ∉ boxSet → g x = 0)
    {x : T3} (hx : x ∈ boxSet) : avgC c g x = (1 / 8 : ℂ) * g x := by
  have hV : ∀ j, ∀ y : T3, y j ∉ halfArc → g y = 0 := fun j y hy =>
    hg y fun h => hy (h j (mem_univ j))
  have hx' : ∀ j, x j ∈ halfArc := fun j => hx j (mem_univ j)
  have h1 : ∀ j, j ≠ 0 → ∀ y : T3, y j ∉ halfArc → halfC (c 0) 0 g y = 0 := fun j hj =>
    halfC_eq_zero_of hj (hV j)
  have h2 : ∀ y : T3, y 2 ∉ halfArc → halfC (c 1) 1 (halfC (c 0) 0 g) y = 0 :=
    halfC_eq_zero_of (by decide) (h1 2 (by decide))
  rw [avgC, halfC_eq_half h2 (hx' 2), halfC_eq_half (h1 1 (by decide)) (hx' 1),
    halfC_eq_half (hV 0) (hx' 0)]
  ring

/-! ## Restriction of continuous fields -/

theorem ofCoeff_entry_cField (F : Ix → C(T3, ℂ)) (p : Ix) :
    ofCoeff (entry p (cField F)) = (F p).toLp 2 volume ℂ := by
  rw [← matrixFourier_symm_apply, cField, LinearIsometryEquiv.symm_apply_apply]

/-- The restriction of a continuous field is `Re F|_Q`. -/
theorem coeFn_resB_cField (F : Ix → C(T3, ℂ)) (p : Ix) :
    (resB (cField F) p : R3 → ℝ) =ᵐ[volume.restrict Qr] fun y => (F p (proj y)).re := by
  rw [resB_apply, ofCoeff_entry_cField]
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := (volume : Measure T3)) (F p)
  filter_upwards [coeFn_resQ ((F p).toLp 2 volume ℂ),
    ae_Qr_of_ae_boxSet (ae_restrict_of_ae h)] with y h1 h2
  rw [h1, h2]

/-! ## Parity extension of test fields -/

/-- The periodization of a test function as a continuous function on `𝕋³`. -/
def perC {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) : C(T3, ℂ) := ⟨per Φ, (isSmooth_per hΦ).continuous⟩

@[simp] theorem perC_apply {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) (x : T3) : perC hΦ x = per Φ x := rfl

/-- **Extension by parity** of a test field `Φ ∈ C_c^∞(Q; ℝ³ˣ³)`: `8 · avg (per Φ)`, the field on
`𝕋³` whose entries are the signed reflections of `Φ_{ab}` with the parities of the class
`(rowMf ε).lift.fix` (`ε = 1`: `ParRow 1`, the electric class; `ε = -1`: `ParRow (-1)`). -/
def extF (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) : L2M :=
  (8 : ℝ) • (rowMf ε hε).lift.avg (cField fun p => perC (hΦ p))

theorem extF_mem_fix (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    extF ε hε hΦ ∈ (rowMf ε hε).lift.fix :=
  Submodule.smul_mem _ _ ((rowMf ε hε).lift.avg_mem _)

/-- **The extension restricts back to the test field**: `res (ext Φ) = Φ` on `Q`. -/
theorem resB_extF (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    resB (extF ε hε hΦ) = BoundedDomain.testField hΦ := by
  ext1 p
  refine Lp.ext ?_
  rw [extF, map_smul, avg_cField]
  filter_upwards [Lp.coeFn_smul (8 : ℝ) (resB (cField fun p =>
      avgC (fun i => ε * colSignR i p.2) (perC (hΦ p))) p),
    coeFn_resB_cField (fun p => avgC (fun i => ε * colSignR i p.2) (perC (hΦ p))) p,
    BoundedDomain.coeFn_testField hΦ p, ae_restrict_mem measurableSet_Qr] with y h1 h2 h3 h4
  change ((8 : ℝ) • resB _) p y = _
  rw [PiLp.smul_apply, h1, Pi.smul_apply, h2, h3,
    avgC_of_mem_boxSet _ (fun x hx => per_eq_zero_of_notMem (hΦ p) hx)
      (proj_mem_boxSet fun i => h4 i (mem_univ i)),
    perC_apply, per_proj_of_mem h4]
  simp only [smul_eq_mul]
  rw [show ((1 / 8 : ℂ) * (Φ p y : ℂ)) = (((1 / 8 : ℝ) * Φ p y : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]
  ring


/-! ## The curl of the extension -/

/-- Fourier coefficients of a finite linear combination of continuous functions. -/
theorem mFourierCoeff_sum_sum (r : Fin 3 → Fin 3 → ℂ) {F : Fin 3 → Fin 3 → T3 → ℂ}
    (hF : ∀ c d, Continuous (F c d)) (k : Z3) :
    mFourierCoeff (fun x => ∑ c, ∑ d, r c d * F c d x) k =
      ∑ c, ∑ d, r c d * mFourierCoeff (F c d) k := by
  simp only [mFourierCoeff, smul_eq_mul, Finset.mul_sum]
  have hi : ∀ c d, Integrable fun x => mFourier (-k) x * (r c d * F c d x) := fun c d =>
    integrable_of_continuous ((mFourier (-k)).continuous.mul (continuous_const.mul (hF c d)))
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hi c d]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun d _ => hi c d]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-- The row-wise curl in Levi-Civita form. -/
theorem curlM_eq_sum (Φ : Ix → R3 → ℝ) (a b : Fin 3) (y : R3) :
    curlM Φ (a, b) y = ∑ c, ∑ d, Feec.eps3 b c d * pd c (Φ (a, d)) y := by
  simp only [curlM, Fin.sum_univ_three, Constraints.eps3_apply]
  fin_cases b <;> simp <;> ring

theorem isTest_curl {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) (ij : Ix) :
    IsTest Qr (curlM Φ ij) := BoundedDomain.isTest_curlM hΦ ij

/-- **The curl of the periodized field is the periodized curl** (on Fourier coefficients). -/
theorem curlSym_cField_per {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) (k : Z3) :
    curlSym (freq k) (cField (fun p => perC (hΦ p)) k) =
      cField (fun p => perC (isTest_curl hΦ p)) k := by
  ext ⟨a, b⟩
  rw [cField_apply, perC]
  simp only [ContinuousMap.coe_mk]
  have e : per (curlM Φ (a, b)) = fun x => ∑ c, ∑ d, ((Feec.eps3 b c d : ℝ) : ℂ) *
      partialT c (per (Φ (a, d))) x := by
    funext x
    simp only [partialT_per (hΦ _), per, curlM_eq_sum]
    push_cast; rfl
  rw [e, mFourierCoeff_sum_sum _ fun c d => continuous_partialT
    (isSmooth_per (hΦ (a, d))).contDiff_one c]
  simp only [mFourierCoeff_partialT (isSmooth_per (hΦ _)).contDiff_one]
  rw [curlSym_apply, jM_apply, curlR_apply_eps3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [cField_apply, freq_apply]
  simp only [perC, ContinuousMap.coe_mk]
  push_cast; ring

theorem cField_per_mem_Hcurl {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    cField (fun p => perC (hΦ p)) ∈ Hcurl := by
  change Memℓp (fun k => curlSym (freq k) (cField (fun p => perC (hΦ p)) k)) 2
  simp_rw [curlSym_cField_per hΦ]
  exact lp.memℓp _

theorem curlT_cField_per {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    curlT ⟨_, cField_per_mem_Hcurl hΦ⟩ = cField (fun p => perC (isTest_curl hΦ p)) :=
  lp.ext (funext fun k => curlSym_cField_per hΦ k)

/-- **The extension of a test field lies in the box `H(curl)` with the electric parities, and
`curl ∘ ext = ext ∘ curl`** (the curl lands in the magnetic parity class). -/
theorem curl_extF {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    ∃ h : extF 1 one_mul_one' hΦ ∈ Hcurl,
      curlT ⟨_, h⟩ = extF (-1) neg_one_mul_neg_one' (isTest_curl hΦ) := by
  obtain ⟨h, e⟩ := intertwines_curl_row.avg ⟨_, cField_per_mem_Hcurl hΦ⟩
  refine ⟨Submodule.smul_mem _ (8 : ℝ) h, ?_⟩
  have : (⟨extF 1 one_mul_one' hΦ, Submodule.smul_mem _ (8 : ℝ) h⟩ : curlT.domain) =
      (8 : ℝ) • ⟨_, h⟩ := rfl
  rw [this, LinearPMap.map_smul]
  change (8 : ℝ) • periodicComplex.d1 ⟨_, h⟩ = _
  rw [e]
  change (8 : ℝ) • rowB.avg (curlT ⟨_, cField_per_mem_Hcurl hΦ⟩) = _
  rw [curlT_cField_per]
  rfl


/-! ## Norm of the extension: the factor `8` -/

/-- The real inner product of the box model is the real part of the complex one. -/
theorem real_inner_L2M (u v : L2M) : ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner u v)]
  refine tsum_congr fun k => ?_
  simp only [PiLp.inner_apply, Complex.re_sum]
  rfl

/-- The real inner product of two continuous fields in the box model. -/
theorem inner_cField (F H : Ix → C(T3, ℂ)) :
    ⟪cField F, cField H⟫_ℝ = ∑ p, (∫ x, H p x * conj (F p x)).re := by
  rw [real_inner_L2M, cField, cField, LinearIsometryEquiv.inner_map_map, PiLp.inner_apply,
    Complex.re_sum]
  simp only [ContinuousMap.inner_toLp]

theorem conj_per (Φ : R3 → ℝ) (x : T3) : conj (per Φ x) = per Φ x := by
  simp [per]

/-- `∫_{𝕋³} |per Φ|² = ∫_Q Φ²`. -/
theorem re_integral_per_sq {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) :
    (∫ x, per Φ x * per Φ x).re = ∫ y, Φ y * Φ y ∂volume.restrict Qr := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := (volume : Measure T3)) (perC hΦ)
  have e : ∫ x, per Φ x * per Φ x = ∫ x, ((perC hΦ).toLp 2 volume ℂ : T3 → ℂ) x * per Φ x :=
    integral_congr_ae (h.mono fun x hx => by simp only; rw [hx]; rfl)
  rw [e, re_integral_mul_per _ hΦ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_resQ ((perC hΦ).toLp 2 volume ℂ), ae_Qr_of_ae_boxSet (ae_restrict_of_ae h),
    ae_restrict_mem measurableSet_Qr] with y h1 h2 h3
  rw [h1, h2, perC_apply, per_proj_of_mem h3, Complex.ofReal_re]

theorem norm_sq_testField {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    ‖BoundedDomain.testField hΦ‖ ^ 2 = ∑ p, ∫ y, Φ p y * Φ p y ∂volume.restrict Qr := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← real_inner_self_eq_norm_sq]
  change ⟪(hΦ p).memLp.toLp (Φ p), (hΦ p).memLp.toLp (Φ p)⟫_ℝ = _
  rw [← BoundedDomain.integral_mul_eq_inner]
  refine integral_congr_ae ?_
  filter_upwards [(hΦ p).memLp.coeFn_toLp] with y hy
  rw [hy]

/-- **The extension multiplies the `L²` norm by `√8`**: `‖ext Φ‖²_{L²(𝕋³)} = 8 ‖Φ‖²_{L²(Q)}`
(`𝕋³` has volume `1`, `Q` has volume `1/8`; the extension consists of `8` reflected copies). -/
theorem norm_sq_extF (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    ‖extF ε hε hΦ‖ ^ 2 = 8 * ‖BoundedDomain.testField hΦ‖ ^ 2 := by
  set G := (rowMf ε hε).lift
  set x := cField fun p => perC (hΦ p)
  have hsa : ⟪G.avg x, G.avg x⟫_ℝ = ⟪x, G.avg x⟫_ℝ := by
    rw [G.inner_avg, G.avg_of_mem (G.avg_mem x)]
  have h1 : ‖extF ε hε hΦ‖ ^ 2 = 8 * ⟪x, extF ε hε hΦ⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, extF, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right]
    change 8 * (8 * ⟪G.avg x, G.avg x⟫_ℝ) = 8 * (8 * ⟪x, G.avg x⟫_ℝ)
    rw [hsa]
  have h2 : extF ε hε hΦ = cField fun p => (8 : ℝ) • avgC (fun i => ε * colSignR i p.2)
      (perC (hΦ p)) := by
    rw [extF, avg_cField, ← cField_smul]
    rfl
  rw [h1, h2, inner_cField, norm_sq_testField]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : (fun x => ((8 : ℝ) • avgC (fun i => ε * colSignR i p.2) (perC (hΦ p))) x *
      conj (perC (hΦ p) x)) = fun x => per (Φ p) x * per (Φ p) x := by
    funext x
    simp only [ContinuousMap.coe_smul, Pi.smul_apply, perC_apply, conj_per, Complex.real_smul]
    by_cases hx : x ∈ boxSet
    · rw [avgC_of_mem_boxSet _ (fun y hy => per_eq_zero_of_notMem (hΦ p) hy) hx, perC_apply]
      push_cast; ring
    · rw [per_eq_zero_of_notMem (hΦ p) hx]; ring
  rw [e, re_integral_per_sq (hΦ p)]


/-! ## `H̊(curl, Q)` embeds into the box `H(curl)` -/

theorem perC_sub {Φ Ψ : R3 → ℝ} (hΦ : IsTest Qr Φ) (hΨ : IsTest Qr Ψ) :
    perC (hΦ.sub hΨ) = perC hΦ - perC hΨ := by
  ext x; simp [per]

theorem extF_sub (ε : ℝ) (hε : ε * ε = 1) {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij))
    (hΨ : ∀ ij, IsTest Qr (Ψ ij)) :
    extF ε hε (fun ij => (hΦ ij).sub (hΨ ij)) = extF ε hε hΦ - extF ε hε hΨ := by
  have e : (fun p => perC (((fun ij => (hΦ ij).sub (hΨ ij)) p))) =
      (fun p => perC (hΦ p)) - fun p => perC (hΨ p) := funext fun p => perC_sub (hΦ p) (hΨ p)
  simp only [extF]
  rw [e, cField_sub, map_sub, smul_sub]

theorem testField_sub {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij))
    (hΨ : ∀ ij, IsTest Qr (Ψ ij)) :
    BoundedDomain.testField (fun ij => (hΦ ij).sub (hΨ ij)) =
      BoundedDomain.testField hΦ - BoundedDomain.testField hΨ := by
  ext1 p
  refine Lp.ext ?_
  filter_upwards [BoundedDomain.coeFn_testField (fun ij => (hΦ ij).sub (hΨ ij)) p,
    Lp.coeFn_sub (BoundedDomain.testField hΦ p) (BoundedDomain.testField hΨ p),
    BoundedDomain.coeFn_testField hΦ p, BoundedDomain.coeFn_testField hΨ p] with y h1 h2 h3 h4
  change _ = (BoundedDomain.testField hΦ p - BoundedDomain.testField hΨ p : _) y
  rw [h1, h2, Pi.sub_apply, h3, h4]

theorem curlM_sub {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij))
    (hΨ : ∀ ij, IsTest Qr (Ψ ij)) (ij : Ix) (y : R3) :
    curlM (fun ij y => Φ ij y - Ψ ij y) ij y = curlM Φ ij y - curlM Ψ ij y := by
  simp only [curlM]
  rw [show (fun y => Φ (ij.1, ij.2 + 2) y - Ψ (ij.1, ij.2 + 2) y) =
      Φ (ij.1, ij.2 + 2) - Ψ (ij.1, ij.2 + 2) from rfl,
    show (fun y => Φ (ij.1, ij.2 + 1) y - Ψ (ij.1, ij.2 + 1) y) =
      Φ (ij.1, ij.2 + 1) - Ψ (ij.1, ij.2 + 1) from rfl,
    BoundedDomain.pd_sub (hΦ _).differentiable (hΨ _).differentiable,
    BoundedDomain.pd_sub (hΦ _).differentiable (hΨ _).differentiable]
  ring

theorem testField_curl_sub {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij))
    (hΨ : ∀ ij, IsTest Qr (Ψ ij)) :
    BoundedDomain.testField (isTest_curl fun ij => (hΦ ij).sub (hΨ ij)) =
      BoundedDomain.testField (isTest_curl hΦ) - BoundedDomain.testField (isTest_curl hΨ) := by
  have h := testField_sub (isTest_curl hΦ) (isTest_curl hΨ)
  rw [← h]
  ext1 p
  refine Lp.ext ?_
  filter_upwards [BoundedDomain.coeFn_testField (isTest_curl fun ij => (hΦ ij).sub (hΨ ij)) p,
    BoundedDomain.coeFn_testField (fun ij => (isTest_curl hΦ ij).sub (isTest_curl hΨ ij)) p]
    with y h1 h2
  rw [h1, h2, curlM_sub hΦ hΨ]

theorem dist_extF (ε : ℝ) (hε : ε * ε = 1) {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij))
    (hΨ : ∀ ij, IsTest Qr (Ψ ij)) :
    dist (extF ε hε hΦ) (extF ε hε hΨ) =
      Real.sqrt 8 * dist (BoundedDomain.testField hΦ) (BoundedDomain.testField hΨ) := by
  rw [dist_eq_norm, dist_eq_norm, ← extF_sub, ← testField_sub]
  have h := norm_sq_extF ε hε fun ij => (hΦ ij).sub (hΨ ij)
  rw [← Real.sqrt_sq (norm_nonneg (extF ε hε _)), h, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg _)]

/-- A sequence whose distances are dominated by those of a Cauchy sequence is Cauchy. -/
theorem cauchySeq_of_dist_le {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {x : ℕ → α} {y : ℕ → β} {C : ℝ} (hC : 0 ≤ C) (hx : CauchySeq x)
    (h : ∀ n m, dist (y n) (y m) ≤ C * dist (x n) (x m)) : CauchySeq y := by
  rw [Metric.cauchySeq_iff] at hx ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hx (ε / (C + 1)) (div_pos hε (by linarith))
  refine ⟨N, fun m hm n hn => (h m n).trans_lt ?_⟩
  have h1 := hN m hm n hn
  calc C * dist (x m) (x n) ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h1.le hC
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith

/-- **Extension of `H̊(curl, Q)` into the box `H(curl)`** (direction "H̊ ⊆ parity space"): every
`B ∈ H̊(curl, Q)` with `curl B = C` (a point `(B, C)` of the graph closure of the curl on
`C_c^∞(Q; ℝ³ˣ³)`) has an extension `E` in the electric parity class `ParRow 1` with
`E ∈ H(curl, 𝕋³)`, `E|_Q = B`, `(curl E)|_Q = C`, and `‖E‖² = 8 ‖B‖²`, `‖curl E‖² = 8 ‖C‖²`
(equal graph norms up to the volume factor `8`). -/
theorem exists_ext_of_mem_closure {B C : BoundedDomain.L2M Qr}
    (h : (B, C) ∈ closure (BoundedDomain.curlGraph Qr)) :
    ∃ E : L2M, ∃ hE : E ∈ Hcurl, E ∈ ParRow 1 ∧ resB E = B ∧ resB (curlT ⟨E, hE⟩) = C ∧
      ‖E‖ ^ 2 = 8 * ‖B‖ ^ 2 ∧ ‖curlT ⟨E, hE⟩‖ ^ 2 = 8 * ‖C‖ ^ 2 := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 h
  choose Φ hΦ hp using hu
  have hu1 : ∀ n, (u n).1 = BoundedDomain.testField (hΦ n) := fun n =>
    (BoundedDomain.eq_of_mem_curlGraph (hΦ n) (hp n)).1
  have hu2 : ∀ n, (u n).2 = BoundedDomain.testField (isTest_curl (hΦ n)) := fun n =>
    (BoundedDomain.eq_of_mem_curlGraph (hΦ n) (hp n)).2
  set e : ℕ → L2M := fun n => extF 1 one_mul_one' (hΦ n)
  set f : ℕ → L2M := fun n => extF (-1) neg_one_mul_neg_one' (isTest_curl (hΦ n))
  have hl1 : Tendsto (fun n => (u n).1) atTop (𝓝 B) := (continuous_fst.tendsto _).comp hlim
  have hl2 : Tendsto (fun n => (u n).2) atTop (𝓝 C) := (continuous_snd.tendsto _).comp hlim
  have he : CauchySeq e := cauchySeq_of_dist_le (Real.sqrt_nonneg 8) hl1.cauchySeq
    fun n m => by rw [dist_extF, hu1, hu1]
  have hf : CauchySeq f := cauchySeq_of_dist_le (Real.sqrt_nonneg 8) hl2.cauchySeq
    fun n m => by rw [dist_extF, hu2, hu2]
  obtain ⟨E, hE⟩ := cauchySeq_tendsto_of_complete he
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hf
  have hgraph : ∀ n, (e n, f n) ∈ curlT.graph := fun n => by
    obtain ⟨hn, en⟩ := curl_extF (hΦ n)
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hn⟩, rfl, en⟩
  have hEF : (E, F) ∈ curlT.graph :=
    (isClosed_mulOp _ : curlT.IsClosed).mem_of_tendsto (hE.prodMk_nhds hF)
      (Eventually.of_forall hgraph)
  obtain ⟨⟨E', hE'⟩, h1, h2⟩ := (LinearPMap.mem_graph_iff _).1 hEF
  simp only at h1 h2
  subst h1
  refine ⟨E', hE', ?_, ?_, ?_, ?_, ?_⟩
  · exact (isClosed_ParRow 1).mem_of_tendsto hE (Eventually.of_forall fun n =>
      mem_rowE_fix.1 (extF_mem_fix 1 one_mul_one' (hΦ n)))
  · refine tendsto_nhds_unique ((resB.continuous.tendsto _).comp hE) ?_
    refine hl1.congr fun n => ?_
    simp only [Function.comp_apply, e, resB_extF, hu1]
  · rw [h2]
    refine tendsto_nhds_unique ((resB.continuous.tendsto _).comp hF) ?_
    refine hl2.congr fun n => ?_
    simp only [Function.comp_apply, f, resB_extF, hu2]
  · refine tendsto_nhds_unique (((continuous_norm.pow 2).tendsto _).comp hE) ?_
    refine (((continuous_norm.pow 2).const_mul 8).tendsto _).comp hl1 |>.congr fun n => ?_
    change 8 * ‖(u n).1‖ ^ 2 = ‖e n‖ ^ 2
    rw [norm_sq_extF, hu1]
  · rw [h2]
    refine tendsto_nhds_unique (((continuous_norm.pow 2).tendsto _).comp hF) ?_
    refine (((continuous_norm.pow 2).const_mul 8).tendsto _).comp hl2 |>.congr fun n => ?_
    change 8 * ‖(u n).2‖ ^ 2 = ‖f n‖ ^ 2
    rw [norm_sq_extF, hu2]


/-- **`H̊(curl, Q)` embeds into the box space `D(curl) ∩ ParRow 1`** with equal graph norms up to
the volume factor `8`, compatibly with the curl. -/
theorem exists_ext_HcurlZero {B : BoundedDomain.L2M Qr} (hB : B ∈ BoundedDomain.HcurlZero Qr) :
    ∃ E : L2M, ∃ hE : E ∈ Hcurl, E ∈ ParRow 1 ∧ resB E = B ∧
      resB (curlT ⟨E, hE⟩) =
        BoundedDomain.curlClosure ⟨B, BoundedDomain.mem_domain_curlClosure.2 hB⟩ ∧
      ‖E‖ ^ 2 = 8 * ‖B‖ ^ 2 ∧
      ‖curlT ⟨E, hE⟩‖ ^ 2 =
        8 * ‖BoundedDomain.curlClosure ⟨B, BoundedDomain.mem_domain_curlClosure.2 hB⟩‖ ^ 2 :=
  exists_ext_of_mem_closure (BoundedDomain.mem_closure_curlClosure isOpen_Qr isBounded_Qr
    ⟨B, BoundedDomain.mem_domain_curlClosure.2 hB⟩)

/-! ## Vector fields: `H̊¹(Q)` embeds into the box `H¹` -/

/-- The box-model element of a continuous vector field on `𝕋³`. -/
def vField (F : Fin 3 → C(T3, ℂ)) : L2V :=
  vectorFourier (WithLp.toLp 2 fun a => (F a).toLp 2 volume ℂ)

theorem vField_apply (F : Fin 3 → C(T3, ℂ)) (k : Z3) (a : Fin 3) :
    vField F k a = mFourierCoeff (F a) k := by
  rw [vField, vectorFourier_apply']
  exact mFourierCoeff_toLp (F a) k

theorem vField_add (F G : Fin 3 → C(T3, ℂ)) : vField (F + G) = vField F + vField G := by
  simp only [vField, Pi.add_apply, map_add]
  rw [← map_add]
  rfl

theorem vField_smul (c : ℝ) (F : Fin 3 → C(T3, ℂ)) : vField (c • F) = c • vField F := by
  refine lp.ext (funext fun k => ?_)
  ext a
  rw [vField_apply]
  change mFourierCoeff (c • ⇑(F a)) k = c • vField F k a
  rw [mFourierCoeff_real_smul, vField_apply]

theorem vField_sub (F G : Fin 3 → C(T3, ℂ)) : vField (F - G) = vField F - vField G := by
  rw [sub_eq_add_neg, vField_add, show -G = (-1 : ℝ) • G by simp, vField_smul]
  simp [sub_eq_add_neg]

theorem R_vField (i : Fin 3) (F : Fin 3 → C(T3, ℂ)) :
    rowV.R i (vField F) = vField fun a => sR (-1) i (F a) := by
  refine lp.ext (funext fun k => ?_)
  ext a
  change (-ContinuousLinearMap.id ℝ Vec3) (vField F (Box.refl i k)) a = _
  rw [vField_apply, mFourierCoeff_sR]
  simp [vField_apply]

theorem half_vField (i : Fin 3) (F : Fin 3 → C(T3, ℂ)) :
    rowV.half i (vField F) = vField fun a => halfC (-1) i (F a) := by
  rw [Refl3.half_apply, R_vField, ← vField_add, ← vField_smul]
  rfl

theorem avg_vField (F : Fin 3 → C(T3, ℂ)) :
    rowV.avg (vField F) = vField fun a => avgC (fun _ => -1) (F a) := by
  rw [Refl3.avg_apply, half_vField, half_vField, half_vField]
  rfl

/-- **Extension by parity** of a test vector field (every component odd in every variable, the
Dirichlet class `ParV` of `σ ∈ H̊¹`). -/
def extV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) : L2V :=
  (8 : ℝ) • rowV.avg (vField fun a => perC (hφ a))

theorem extV_mem_ParV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) : extV hφ ∈ ParV :=
  mem_rowV_fix.1 (Submodule.smul_mem _ _ (rowV.avg_mem _))

theorem coeFn_resBV_vField (F : Fin 3 → C(T3, ℂ)) (a : Fin 3) :
    (resBV (vField F) a : R3 → ℝ) =ᵐ[volume.restrict Qr] fun y => (F a (proj y)).re := by
  rw [resBV_apply, vField, LinearIsometryEquiv.symm_apply_apply]
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := (volume : Measure T3)) (F a)
  filter_upwards [coeFn_resQ ((F a).toLp 2 volume ℂ),
    ae_Qr_of_ae_boxSet (ae_restrict_of_ae h)] with y h1 h2
  rw [h1]
  change (((F a).toLp 2 volume ℂ : T3 → ℂ) (proj y)).re = _
  rw [h2]

theorem resBV_extV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    resBV (extV hφ) = BoundedDomain.testFieldV hφ := by
  ext1 a
  refine Lp.ext ?_
  rw [extV, map_smul, avg_vField]
  filter_upwards [Lp.coeFn_smul (8 : ℝ) (resBV (vField fun a =>
      avgC (fun _ => -1) (perC (hφ a))) a),
    coeFn_resBV_vField (fun a => avgC (fun _ => -1) (perC (hφ a))) a,
    (hφ a).memLp.coeFn_toLp, ae_restrict_mem measurableSet_Qr] with y h1 h2 h3 h4
  change ((8 : ℝ) • resBV _) a y = ((hφ a).memLp.toLp (φ a) : R3 → ℝ) y
  rw [PiLp.smul_apply, h1, Pi.smul_apply, h2, h3,
    avgC_of_mem_boxSet _ (fun x hx => per_eq_zero_of_notMem (hφ a) hx)
      (proj_mem_boxSet fun i => h4 i (mem_univ i)),
    perC_apply, per_proj_of_mem h4]
  simp only [smul_eq_mul]
  rw [show ((1 / 8 : ℂ) * (φ a y : ℂ)) = (((1 / 8 : ℝ) * φ a y : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]
  ring

theorem isTest_grad {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) (ij : Ix) :
    IsTest Qr (BoundedDomain.gradM φ ij) := BoundedDomain.isTest_gradM hφ ij

theorem gradSym_vField_per {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) (k : Z3) :
    gradSym (freq k) (vField (fun a => perC (hφ a)) k) =
      cField (fun p => perC (isTest_grad hφ p)) k := by
  ext ⟨a, b⟩
  rw [cField_apply, perC]
  simp only [ContinuousMap.coe_mk, BoundedDomain.gradM]
  rw [← partialT_per (hφ a), mFourierCoeff_partialT (isSmooth_per (hφ a)).contDiff_one,
    gradSym_apply, vField_apply, freq_apply]
  simp only [perC, ContinuousMap.coe_mk]
  push_cast; ring

theorem vField_per_mem_gradT_domain {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    vField (fun a => perC (hφ a)) ∈ gradT.domain := by
  change Memℓp (fun k => gradSym (freq k) (vField (fun a => perC (hφ a)) k)) 2
  simp_rw [gradSym_vField_per hφ]
  exact lp.memℓp _

theorem gradT_vField_per {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    gradT ⟨_, vField_per_mem_gradT_domain hφ⟩ = cField (fun p => perC (isTest_grad hφ p)) :=
  lp.ext (funext fun k => gradSym_vField_per hφ k)

/-- **`grad ∘ ext = ext ∘ grad`** on test vector fields (the gradient lands in `ParRow 1`). -/
theorem grad_extV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    ∃ h : extV hφ ∈ gradT.domain,
      gradT ⟨_, h⟩ = extF 1 one_mul_one' (isTest_grad hφ) := by
  obtain ⟨h, e⟩ := intertwines_grad_row.avg ⟨_, vField_per_mem_gradT_domain hφ⟩
  refine ⟨Submodule.smul_mem _ (8 : ℝ) h, ?_⟩
  have : (⟨extV hφ, Submodule.smul_mem _ (8 : ℝ) h⟩ : gradT.domain) = (8 : ℝ) • ⟨_, h⟩ := rfl
  rw [this, LinearPMap.map_smul]
  change (8 : ℝ) • periodicComplex.d0 ⟨_, h⟩ = _
  rw [e]
  change (8 : ℝ) • rowE.avg (gradT ⟨_, vField_per_mem_gradT_domain hφ⟩) = _
  rw [gradT_vField_per]
  rfl

theorem real_inner_L2V (u v : L2V) : ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner u v)]
  refine tsum_congr fun k => ?_
  simp only [PiLp.inner_apply, Complex.re_sum]
  rfl

theorem inner_vField (F H : Fin 3 → C(T3, ℂ)) :
    ⟪vField F, vField H⟫_ℝ = ∑ a, (∫ x, H a x * conj (F a x)).re := by
  rw [real_inner_L2V, vField, vField, LinearIsometryEquiv.inner_map_map, PiLp.inner_apply,
    Complex.re_sum]
  simp only [ContinuousMap.inner_toLp]

theorem norm_sq_testFieldV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    ‖BoundedDomain.testFieldV hφ‖ ^ 2 = ∑ a, ∫ y, φ a y * φ a y ∂volume.restrict Qr := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← real_inner_self_eq_norm_sq]
  change ⟪(hφ a).memLp.toLp (φ a), (hφ a).memLp.toLp (φ a)⟫_ℝ = _
  rw [← BoundedDomain.integral_mul_eq_inner]
  refine integral_congr_ae ?_
  filter_upwards [(hφ a).memLp.coeFn_toLp] with y hy
  rw [hy]

theorem norm_sq_extV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    ‖extV hφ‖ ^ 2 = 8 * ‖BoundedDomain.testFieldV hφ‖ ^ 2 := by
  set x := vField fun a => perC (hφ a)
  have hsa : ⟪rowV.avg x, rowV.avg x⟫_ℝ = ⟪x, rowV.avg x⟫_ℝ := by
    rw [rowV.inner_avg, rowV.avg_of_mem (rowV.avg_mem x)]
  have h1 : ‖extV hφ‖ ^ 2 = 8 * ⟪x, extV hφ⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, extV, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right]
    change 8 * (8 * ⟪rowV.avg x, rowV.avg x⟫_ℝ) = 8 * (8 * ⟪x, rowV.avg x⟫_ℝ)
    rw [hsa]
  have h2 : extV hφ = vField fun a => (8 : ℝ) • avgC (fun _ => -1) (perC (hφ a)) := by
    rw [extV, avg_vField, ← vField_smul]
    rfl
  rw [h1, h2, inner_vField, norm_sq_testFieldV]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : (fun x => ((8 : ℝ) • avgC (fun _ => -1) (perC (hφ a))) x *
      conj (perC (hφ a) x)) = fun x => per (φ a) x * per (φ a) x := by
    funext x
    simp only [ContinuousMap.coe_smul, Pi.smul_apply, perC_apply, conj_per, Complex.real_smul]
    by_cases hx : x ∈ boxSet
    · rw [avgC_of_mem_boxSet _ (fun y hy => per_eq_zero_of_notMem (hφ a) hy) hx, perC_apply]
      push_cast; ring
    · rw [per_eq_zero_of_notMem (hφ a) hx]; ring
  rw [e, re_integral_per_sq (hφ a)]

theorem extV_sub {φ ψ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i))
    (hψ : ∀ i, IsTest Qr (ψ i)) :
    extV (fun i => (hφ i).sub (hψ i)) = extV hφ - extV hψ := by
  have e : (fun a => perC (((fun i => (hφ i).sub (hψ i)) a))) =
      (fun a => perC (hφ a)) - fun a => perC (hψ a) := funext fun a => perC_sub (hφ a) (hψ a)
  simp only [extV]
  rw [e, vField_sub, map_sub, smul_sub]

theorem testFieldV_sub {φ ψ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i))
    (hψ : ∀ i, IsTest Qr (ψ i)) :
    BoundedDomain.testFieldV (fun i => (hφ i).sub (hψ i)) =
      BoundedDomain.testFieldV hφ - BoundedDomain.testFieldV hψ := by
  ext1 a
  refine Lp.ext ?_
  filter_upwards [((hφ a).sub (hψ a)).memLp.coeFn_toLp,
    Lp.coeFn_sub (BoundedDomain.testFieldV hφ a) (BoundedDomain.testFieldV hψ a),
    (hφ a).memLp.coeFn_toLp, (hψ a).memLp.coeFn_toLp] with y h1 h2 h3 h4
  change ((((hφ a).sub (hψ a)).memLp.toLp _ : _) : R3 → ℝ) y =
    (BoundedDomain.testFieldV hφ a - BoundedDomain.testFieldV hψ a : _) y
  rw [h1, h2, Pi.sub_apply]
  change _ = ((hφ a).memLp.toLp (φ a) : R3 → ℝ) y - ((hψ a).memLp.toLp (ψ a) : R3 → ℝ) y
  rw [h3, h4]

theorem testField_grad_sub {φ ψ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i))
    (hψ : ∀ i, IsTest Qr (ψ i)) :
    BoundedDomain.testField (isTest_grad fun i => (hφ i).sub (hψ i)) =
      BoundedDomain.testField (isTest_grad hφ) - BoundedDomain.testField (isTest_grad hψ) := by
  rw [← testField_sub]
  ext1 p
  refine Lp.ext ?_
  filter_upwards [BoundedDomain.coeFn_testField (isTest_grad fun i => (hφ i).sub (hψ i)) p,
    BoundedDomain.coeFn_testField (fun ij => (isTest_grad hφ ij).sub (isTest_grad hψ ij)) p]
    with y h1 h2
  rw [h1, h2]
  simp only [BoundedDomain.gradM]
  rw [show (fun y => φ p.1 y - ψ p.1 y) = φ p.1 - ψ p.1 from rfl,
    BoundedDomain.pd_sub (hφ _).differentiable (hψ _).differentiable]

theorem dist_extV {φ ψ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i))
    (hψ : ∀ i, IsTest Qr (ψ i)) :
    dist (extV hφ) (extV hψ) =
      Real.sqrt 8 * dist (BoundedDomain.testFieldV hφ) (BoundedDomain.testFieldV hψ) := by
  rw [dist_eq_norm, dist_eq_norm, ← extV_sub, ← testFieldV_sub]
  have h := norm_sq_extV fun i => (hφ i).sub (hψ i)
  rw [← Real.sqrt_sq (norm_nonneg (extV _)), h, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg _)]

/-- **Extension of `H̊¹(Q; ℝ³)` into the box `H¹`**: every `u ∈ H̊¹(Q)` with `grad u = G` (a point
of the graph closure of the gradient on `C_c^∞(Q; ℝ³)`) has an extension `σ` in the Dirichlet
parity class `ParV` with `σ ∈ H¹(𝕋³)`, `σ|_Q = u`, `(grad σ)|_Q = G`, `‖σ‖² = 8 ‖u‖²`,
`‖grad σ‖² = 8 ‖G‖²`. -/
theorem exists_extV_of_mem_closure {u : BoundedDomain.L2V Qr} {G : BoundedDomain.L2M Qr}
    (h : (u, G) ∈ closure (BoundedDomain.gradGraph Qr)) :
    ∃ σ : L2V, ∃ hσ : σ ∈ gradT.domain, σ ∈ ParV ∧ resBV σ = u ∧ resB (gradT ⟨σ, hσ⟩) = G ∧
      ‖σ‖ ^ 2 = 8 * ‖u‖ ^ 2 ∧ ‖gradT ⟨σ, hσ⟩‖ ^ 2 = 8 * ‖G‖ ^ 2 := by
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.1 h
  choose φ hφ hp1 hp2 using hw
  have hu1 : ∀ n, (w n).1 = BoundedDomain.testFieldV (hφ n) := fun n =>
    (BoundedDomain.eq_of_mem_gradGraph (hφ n) (hp1 n) (hp2 n)).1
  have hu2 : ∀ n, (w n).2 = BoundedDomain.testField (isTest_grad (hφ n)) := fun n =>
    (BoundedDomain.eq_of_mem_gradGraph (hφ n) (hp1 n) (hp2 n)).2
  set e : ℕ → L2V := fun n => extV (hφ n)
  set f : ℕ → L2M := fun n => extF 1 one_mul_one' (isTest_grad (hφ n))
  have hl1 : Tendsto (fun n => (w n).1) atTop (𝓝 u) := (continuous_fst.tendsto _).comp hlim
  have hl2 : Tendsto (fun n => (w n).2) atTop (𝓝 G) := (continuous_snd.tendsto _).comp hlim
  have he : CauchySeq e := cauchySeq_of_dist_le (Real.sqrt_nonneg 8) hl1.cauchySeq
    fun n m => by rw [dist_extV, hu1, hu1]
  have hf : CauchySeq f := cauchySeq_of_dist_le (Real.sqrt_nonneg 8) hl2.cauchySeq
    fun n m => by rw [dist_extF, hu2, hu2]
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete he
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hf
  have hgraph : ∀ n, (e n, f n) ∈ gradT.graph := fun n => by
    obtain ⟨hn, en⟩ := grad_extV (hφ n)
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hn⟩, rfl, en⟩
  have hSF : (S, F) ∈ gradT.graph :=
    (isClosed_mulOp _ : gradT.IsClosed).mem_of_tendsto (hS.prodMk_nhds hF)
      (Eventually.of_forall hgraph)
  obtain ⟨⟨S', hS'⟩, h1, h2⟩ := (LinearPMap.mem_graph_iff _).1 hSF
  simp only at h1 h2
  subst h1
  refine ⟨S', hS', ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_ParV.mem_of_tendsto hS (Eventually.of_forall fun n => extV_mem_ParV (hφ n))
  · refine tendsto_nhds_unique ((resBV.continuous.tendsto _).comp hS) ?_
    refine hl1.congr fun n => ?_
    simp only [Function.comp_apply, e, resBV_extV, hu1]
  · rw [h2]
    refine tendsto_nhds_unique ((resB.continuous.tendsto _).comp hF) ?_
    refine hl2.congr fun n => ?_
    simp only [Function.comp_apply, f, resB_extF, hu2]
  · refine tendsto_nhds_unique (((continuous_norm.pow 2).tendsto _).comp hS) ?_
    refine (((continuous_norm.pow 2).const_mul 8).tendsto _).comp hl1 |>.congr fun n => ?_
    change 8 * ‖(w n).1‖ ^ 2 = ‖e n‖ ^ 2
    rw [norm_sq_extV, hu1]
  · rw [h2]
    refine tendsto_nhds_unique (((continuous_norm.pow 2).tendsto _).comp hF) ?_
    refine (((continuous_norm.pow 2).const_mul 8).tendsto _).comp hl2 |>.congr fun n => ?_
    change 8 * ‖(w n).2‖ ^ 2 = ‖f n‖ ^ 2
    rw [norm_sq_extF, hu2]

/-- **`H̊¹(Q; ℝ³)` embeds into the box space `H¹ ∩ ParV`**, compatibly with the gradient. -/
theorem exists_extV_H1Zero (u : (BoundedDomain.gradClosure (Ω := Qr)).domain) :
    ∃ σ : L2V, ∃ hσ : σ ∈ gradT.domain, σ ∈ ParV ∧ resBV σ = u ∧
      resB (gradT ⟨σ, hσ⟩) = BoundedDomain.gradClosure u ∧
      ‖σ‖ ^ 2 = 8 * ‖(u : BoundedDomain.L2V Qr)‖ ^ 2 ∧
      ‖gradT ⟨σ, hσ⟩‖ ^ 2 = 8 * ‖BoundedDomain.gradClosure u‖ ^ 2 :=
  exists_extV_of_mem_closure (BoundedDomain.mem_closure_gradClosure isOpen_Qr isBounded_Qr u)

end Feec.BoxIdent
