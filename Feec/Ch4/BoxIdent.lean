module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Feec.Ch4.BoxStatic
public import Feec.Ch4.BoxThesis
public import Feec.Ch4.BoxForward
public import Feec.Ch4.StoneApplications
public import Feec.Ch4.BoundedDomainExt

/-!
# The box parity model is the bounded-domain complex on `Q = (0, ½)³`

`Feec.Ch4.Box` models the box `Q = (0, ½)³` by parity subspaces of the Fourier model of
`𝕋³ = ℝ³/ℤ³` (`Feec.Ch4.Torus`): `ParV` (every component odd in every variable), `ParRow 1`
(`E_{ab}` even in `x_b`, odd in the other variables), `ParRow (-1)` (`B_{ab}` odd in `x_b`, even
in the others). Its docstring leaves open whether these are the bounded-domain spaces of
`Feec.Ch4.BoundedDomain` for `Ω = Q`. This file proves that they are, for every space of the
thesis' complex `H̊¹(Q; ℝ³) → H̊(curl, Q; ℝ³ˣ³) → L²(Q; ℝ³ˣ³)` ([QuennevilleBelair2015, §4.10]),
for the adjoint domains `H(curl, Q)`, `H(div, Q)` and for `L²(TSD)(Q)`, and transfers the box
theorem on `K*` (`Feec.Box.thesisBox_mem_Kmax_iff`, `Feec.Box.forward_iff_mem_Kmax`) to the
complex `Feec.BoundedDomain.thesisComplex` on `Q`. The repository's box model is `(0, ½)³` in
`ℝ³/ℤ³`; the last section carries the `K*` theorem along `x ↦ a x + b` to every open cube
`∏ᵢ (bᵢ, bᵢ + s)`, in particular to `(0, π)³`.

`Q` is `Qr ⊆ ℝ³`, with Lebesgue measure. Box-model fields are complex valued (Fourier coefficients
in `ℓ²(ℤ³)`); `resB`, `resBV`, `resQ` take the real part of the restriction to `Q`, and real
fields (`IsRealM`, `IsRealV`: `Â(-k) = conj Â(k)`) are those with zero imaginary part. `𝕋³` has
volume `1` and `Q` volume `1/8`, hence the factor `8` in all norm identities.

## Main results

Restriction (any periodic field; weak derivatives on `Q` are tested against `C_c^∞(Q)`, through
the periodization `per` of test functions):
* `resM_weakCurl`, `resM_mem_HcurlM`, `resB_curl`: the restriction of `A ∈ H(curl, 𝕋³)` lies in
  `H(curl, Q)` (`Feec.BoundedDomain.HcurlM`), its weak curl is the restriction of the periodic
  curl, and it is `d1*` of the thesis' complex on `Q`; `resM_weakDiv`, `resB_div`: the same for
  `H(div)` and `d0*`; `resV_weakGrad`: weak gradients; `resB_mem_TSD`: `boxTSD τ` restricts into
  `L²(TSD)(Q)`.

Extension (`H̊ ⊆ parity space`):
* `extF`, `extV`: the parity extension `8 · avg (per Φ)` of a test field, with `resB_extF`,
  `norm_sq_extF` (`‖ext Φ‖² = 8 ‖Φ‖²`), `curl_extF`, `grad_extV` (`curl ∘ ext = ext ∘ curl`,
  `grad ∘ ext = ext ∘ grad`).
* `exists_ext_HcurlZero`, `exists_extV_H1Zero`, `exists_extL2`, `exists_extL2V`: real extensions
  of `H̊(curl, Q)`, `H̊¹(Q)` and `L²(Q)` fields, with graph norms multiplied by `8`.

Restriction of the parity spaces (`parity space ⊆ H̊`, the trace part):
* `resB_mem_HcurlZero`, `resBV_mem_H1Zero`: `ParRow 1 ∩ H(curl, 𝕋³)` restricts into
  `H̊(curl, Q)` and `ParV ∩ H¹(𝕋³)` into `H̊¹(Q)`, intertwining the operators. Proof: the Fourier
  truncations (`trunc`) are trigonometric polynomials whose tangential components vanish on `∂Q`
  (`reLift_eq_zero_of_odd`); smooth fields with this property are graph-norm limits of `χ_n ψ` for
  explicit cut-offs `χ_n` (`mem_closure_curlGraph_of_smooth`, `mem_closure_gradGraph_of_smooth`:
  `∇χ_n × ψ` stays bounded since `ψ_tan = O(dist to the face)`, `abs_le_of_faces`, and tends to
  `0` pointwise; dominated convergence, `tendsto_toLp_of_bdd`).

Tiling and uniqueness:
* `integral_eq_sum_box`: `∫_{𝕋³} g = Σ_ε ∫_Q g ∘ R_ε` over the eight reflections.
* `norm_sq_of_mem_fix`, `norm_sq_of_mem_ParV`: `‖A‖² = 8 (‖Re A|_Q‖² + ‖Im A|_Q‖²)` on each
  parity class; `eq_of_resB_eq`, `eq_of_resBV_eq`: real parity fields are determined by their
  restriction to `Q`.

The identification (restriction is a bijection from the real fields of the parity space onto the
bounded-domain space, with norms multiplied by `8^{-1/2}` and, where defined, intertwining the
operators):
* `bijOn_resB_HcurlZero`, `resB_curl_identification`: `ParRow 1 ∩ H(curl, 𝕋³)` and `H̊(curl, Q)`;
  `bijOn_resBV_H1Zero`, `resBV_grad_identification`: `ParV ∩ H¹(𝕋³)` and `H̊¹(Q)`.
* `bijOn_resB_L2`, `bijOn_resBV_L2`: each row-wise class and `L²(Q; ℝ³ˣ³)`; `ParV` and
  `L²(Q; ℝ³)`.
* `bijOn_resB_HcurlM`: `ParRow (-1) ∩ H(curl, 𝕋³)` and `H(curl, Q) = D(d1*)`;
  `bijOn_resB_HdivM`: `ParRow 1 ∩ H(div, 𝕋³)` and `H(div, Q) = D(d0*)` (`extML_adj_curl`,
  `extML_adj_div`: by duality, using the parity projections, complex conjugation `cjM`, `cjV` and
  the identification of `H̊(curl, Q)`, `H̊¹(Q)`).
* `bijOn_resB_TSD_electric`, `bijOn_resB_TSD_magnetic`: `boxTSD (±1)` and `L²(TSD)(Q)`
  (`mem_boxTSD_of`, through the localization `isTest_loc` of box test functions).

Transfer to the thesis' complex on `Q`:
* `iota`: the extension of states `(σ, E, B) ↦ (ext σ, ext E, ext B)`; `iota_waveOp`
  (`ι L_Q = L_{𝕋³} ι`), `iota_group` (`ι e^{-tL_Q} = e^{-tL_{𝕋³}} ι` for every group),
  `iota_mem_Kc`.
* **`thesisComplexQ_forward_iff`**, **`thesisComplexQ_mem_Kmax_iff`**: on the cube with the
  thesis' boundary conditions, for every orthogonal group generated by `-L` (e.g. Stone's,
  `thesisComplexQ_mem_Kmax_iff_waveGroup`), the forward orbit of `x` stays in
  `K = {0} × L²(TSD) × L²(TSD)` iff `x ∈ K*` iff `x ∈ K` is stationary;
  `thesisComplexQ_mem_Kmax_iff'`: `K*` consists of the `(0, 0, B₀)` with `B₀ ∈ L²(TSD)(Q)` and
  weak curl `0`.

Dilations and translations (`x ↦ a x + b`, `a ≠ 0`, between any open bounded `Ω`, `Ω'`):
* `pullL`, `pullM`, `pullV`: the pull-back `f ↦ f ∘ T` on `L²`, multiplying inner products by
  `|a|⁻³` (`inner_pullM`, `map_affH_restrict`); `curlClosure_pull`, `gradClosure_pull`: it maps
  `H̊(curl, Ω')`, `H̊¹(Ω')` into `H̊(curl, Ω)`, `H̊¹(Ω)` with `curl (u ∘ T) = a (curl u) ∘ T`;
  `adj0_pull`, `adj1_pull`: the same for `D(d0*) = H(div)`, `D(d1*) = H(curl)`, by the abstract
  `adjoint_conj`; `pullM_mem_TSD`: `L²(TSD)` is preserved.
* `waveOp_conj` (abstract), `pullX_waveOp`: `L (x ∘ T) = a (L' x) ∘ T`; `rescaleGroup`: the time
  change `t ↦ c t` of a group generated by `L` is a group generated by `c L`; `pullX_group`:
  `(G'.S (a t) x) ∘ T = G.S t (x ∘ T)` for every pair of groups generated by `-L'`, `-L`.
* **`affineCube_forward_iff`**, **`affineCube_mem_Kmax_iff`**, **`affineCube_mem_Kmax_iff'`**:
  the `K*` theorem on every `Ω'` with `x ∈ Q ↔ a x + b ∈ Ω'`, `a > 0`; **`openCube_forward_iff`**,
  **`openCube_mem_Kmax_iff'`**: on every open cube `∏ᵢ (bᵢ, bᵢ + s)`; `piCube_mem_Kmax_iff`: on
  `(0, π)³` (`openCube_zero_pi`), for Stone's group.

## Not proved here

* The transfer of the mirror Props 4.17/4.19 (`Feec.Ch4.BoxMirror`): the mirror parity classes
  have no bounded-domain counterpart in the repository.
* A version of `iota` for complex-valued fields on `Q` (the box complex is the complexification
  of the complex on `Q`); only real fields on `Q` are used.
* The even (Neumann) parity classes are not identified with Sobolev spaces without boundary
  condition (`H¹(Q)`), so the box results are not transferred to the dual-boundary-condition
  complexes of `Feec.Ch4.BoundedSym`.

## References

* [QuennevilleBelair2015], §4.10 (the complex `H̊¹ → H̊(curl) → L²`, Prop 4.17)
* [Brezis2011], §9.2 (extension by reflection), §9.4 (`W₀^{1,p}`, cut-off arguments)
* [AFW2010] (Hilbert complexes)
* [Pazy1983], §1.10 (unitary groups)
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

/-- **Restriction to `Q`** (real part): `f ↦ Re (f ∘ proj)|_Q`, a continuous `ℝ`-linear map
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


/-! ## Real-valued fields -/

/-- Real-valued matrix fields of the box model: `Â(-k) = conj Â(k)`. -/
def IsRealM (A : L2M) : Prop := ∀ k p, A (-k) p = conj (A k p)

/-- Real-valued vector fields of the box model. -/
def IsRealV (σ : L2V) : Prop := ∀ k a, σ (-k) a = conj (σ k a)

theorem isClosed_isRealM : IsClosed {A : L2M | IsRealM A} := by
  have e : {A : L2M | IsRealM A} = ⋂ k, ⋂ p, {A : L2M | A (-k) p = conj (A k p)} := by
    ext A; simp [IsRealM]
  rw [e]
  exact isClosed_iInter fun k => isClosed_iInter fun p =>
    isClosed_eq (continuous_coef _ _) (Complex.continuous_conj.comp (continuous_coef _ _))

theorem isClosed_isRealV : IsClosed {σ : L2V | IsRealV σ} := by
  have e : {σ : L2V | IsRealV σ} = ⋂ k, ⋂ a, {σ : L2V | σ (-k) a = conj (σ k a)} := by
    ext σ; simp [IsRealV]
  rw [e]
  exact isClosed_iInter fun k => isClosed_iInter fun a =>
    isClosed_eq (continuous_coefV _ _) (Complex.continuous_conj.comp (continuous_coefV _ _))

theorem IsRealM.sub {A B : L2M} (hA : IsRealM A) (hB : IsRealM B) : IsRealM (A - B) :=
  fun k p => by simp [hA k p, hB k p]

theorem IsRealV.sub {σ ρ : L2V} (hσ : IsRealV σ) (hρ : IsRealV ρ) : IsRealV (σ - ρ) :=
  fun k a => by simp [hσ k a, hρ k a]

/-- Fourier coefficients of a real-valued continuous function are conjugate-symmetric. -/
theorem mFourierCoeff_neg_of_real {g : C(T3, ℂ)} (hg : ∀ x, conj (g x) = g x) (k : Z3) :
    mFourierCoeff g (-k) = conj (mFourierCoeff g k) := by
  simp only [mFourierCoeff, smul_eq_mul, neg_neg]
  rw [← integral_conj]
  congr 1; funext x
  rw [map_mul, hg, ← mFourier_neg, neg_neg]

theorem isRealM_cField {F : Ix → C(T3, ℂ)} (hF : ∀ p x, conj (F p x) = F p x) :
    IsRealM (cField F) := fun k p => by
  rw [cField_apply, cField_apply, mFourierCoeff_neg_of_real (hF p)]

theorem conj_avgC (c : Fin 3 → ℝ) {g : C(T3, ℂ)} (hg : ∀ x, conj (g x) = g x) (x : T3) :
    conj (avgC c g x) = avgC c g x := by
  have hh : ∀ (c : ℝ) (i : Fin 3) (g : C(T3, ℂ)), (∀ x, conj (g x) = g x) →
      ∀ x, conj (halfC c i g x) = halfC c i g x := fun c i g hg x => by
    rw [halfC_apply, map_mul, map_add, map_mul, hg, hg, Complex.conj_ofReal]
    congr 1; simp only [one_div, map_inv₀, map_ofNat]
  exact hh _ _ _ (hh _ _ _ (hh _ _ _ hg)) x

theorem conj_perC {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) (x : T3) : conj (perC hΦ x) = perC hΦ x :=
  conj_per Φ x

theorem isRealM_extF (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    IsRealM (extF ε hε hΦ) := by
  rw [extF, avg_cField, ← cField_smul]
  refine isRealM_cField fun p x => ?_
  change conj ((8 : ℝ) • avgC _ (perC (hΦ p)) x) = (8 : ℝ) • avgC _ (perC (hΦ p)) x
  rw [Complex.real_smul, map_mul, Complex.conj_ofReal, conj_avgC _ (conj_perC (hΦ p))]

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
    ∃ E : L2M, ∃ hE : E ∈ Hcurl, E ∈ ParRow 1 ∧ IsRealM E ∧ resB E = B ∧
      resB (curlT ⟨E, hE⟩) = C ∧ ‖E‖ ^ 2 = 8 * ‖B‖ ^ 2 ∧ ‖curlT ⟨E, hE⟩‖ ^ 2 = 8 * ‖C‖ ^ 2 := by
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
  refine ⟨E', hE', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isClosed_ParRow 1).mem_of_tendsto hE (Eventually.of_forall fun n =>
      mem_rowE_fix.1 (extF_mem_fix 1 one_mul_one' (hΦ n)))
  · exact isClosed_isRealM.mem_of_tendsto hE (Eventually.of_forall fun n =>
      isRealM_extF 1 one_mul_one' (hΦ n))
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
    ∃ E : L2M, ∃ hE : E ∈ Hcurl, E ∈ ParRow 1 ∧ IsRealM E ∧ resB E = B ∧
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

theorem isRealV_vField {F : Fin 3 → C(T3, ℂ)} (hF : ∀ a x, conj (F a x) = F a x) :
    IsRealV (vField F) := fun k a => by
  rw [vField_apply, vField_apply, mFourierCoeff_neg_of_real (hF a)]

theorem isRealV_extV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) : IsRealV (extV hφ) := by
  rw [extV, avg_vField, ← vField_smul]
  refine isRealV_vField fun a x => ?_
  change conj ((8 : ℝ) • avgC _ (perC (hφ a)) x) = (8 : ℝ) • avgC _ (perC (hφ a)) x
  rw [Complex.real_smul, map_mul, Complex.conj_ofReal, conj_avgC _ (conj_perC (hφ a))]

/-- **Extension of `H̊¹(Q; ℝ³)` into the box `H¹`**: every `u ∈ H̊¹(Q)` with `grad u = G` (a point
of the graph closure of the gradient on `C_c^∞(Q; ℝ³)`) has an extension `σ` in the Dirichlet
parity class `ParV` with `σ ∈ H¹(𝕋³)`, `σ|_Q = u`, `(grad σ)|_Q = G`, `‖σ‖² = 8 ‖u‖²`,
`‖grad σ‖² = 8 ‖G‖²`. -/
theorem exists_extV_of_mem_closure {u : BoundedDomain.L2V Qr} {G : BoundedDomain.L2M Qr}
    (h : (u, G) ∈ closure (BoundedDomain.gradGraph Qr)) :
    ∃ σ : L2V, ∃ hσ : σ ∈ gradT.domain, σ ∈ ParV ∧ IsRealV σ ∧ resBV σ = u ∧
      resB (gradT ⟨σ, hσ⟩) = G ∧ ‖σ‖ ^ 2 = 8 * ‖u‖ ^ 2 ∧ ‖gradT ⟨σ, hσ⟩‖ ^ 2 = 8 * ‖G‖ ^ 2 := by
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
  refine ⟨S', hS', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_ParV.mem_of_tendsto hS (Eventually.of_forall fun n => extV_mem_ParV (hφ n))
  · exact isClosed_isRealV.mem_of_tendsto hS (Eventually.of_forall fun n => isRealV_extV (hφ n))
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
    ∃ σ : L2V, ∃ hσ : σ ∈ gradT.domain, σ ∈ ParV ∧ IsRealV σ ∧ resBV σ = u ∧
      resB (gradT ⟨σ, hσ⟩) = BoundedDomain.gradClosure u ∧
      ‖σ‖ ^ 2 = 8 * ‖(u : BoundedDomain.L2V Qr)‖ ^ 2 ∧
      ‖gradT ⟨σ, hσ⟩‖ ^ 2 = 8 * ‖BoundedDomain.gradClosure u‖ ^ 2 :=
  exists_extV_of_mem_closure (BoundedDomain.mem_closure_gradClosure isOpen_Qr isBounded_Qr u)


/-! ## Cut-off functions on `Q` -/

section Cutoff

open Real

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

theorem two_le_mN (n : ℕ) : 2 ≤ mN n := by unfold mN; linarith [n.cast_nonneg (α := ℝ)]

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
    have h3 : t * mN n < mN n / 2 - 1 / 2 := by linarith
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

theorem chiBox_subset_Qr (n : ℕ) : chiBox n ⊆ Qr := by
  intro y hy i _
  have hm := mN_pos n
  have h := hy i (mem_univ i)
  have hp : 0 < 1 / (2 * mN n) := by positivity
  exact ⟨hp.trans_le h.1, h.2.trans_lt (by linarith)⟩

/-- `χ_n f` is a test function on `Q` for every smooth `f`. -/
theorem isTest_chi_mul {f : R3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    IsTest Qr (fun y => chi n y * f y) := by
  have hsub : Function.support (fun y => chi n y * f y) ⊆ chiBox n :=
    (Function.support_mul_subset_left _ _).trans (support_chi_subset n)
  refine ⟨(contDiff_chi n).mul hf, ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_chiBox n) fun y hy =>
      Function.notMem_support.1 fun h => hy (hsub h)
  · exact (closure_minimal hsub (isCompact_chiBox n).isClosed).trans (chiBox_subset_Qr n)

/-- **Near each point of `Q`, `χ_n = 1` for all large `n`.** -/
theorem eventually_chi_eq_one {y : R3} (hy : y ∈ Qr) :
    ∀ᶠ n in atTop, chi n =ᶠ[𝓝 y] fun _ => 1 := by
  have hpos : ∀ i, 0 < min (y i) (1 / 2 - y i) := fun i =>
    lt_min (hy i (mem_univ i)).1 (by linarith [(hy i (mem_univ i)).2])
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

/-- **The derivative of the cut-off**: `∂_c χ_n = η_n'(y_c) · (the other two factors)`, so
`|∂_c χ_n(y)| ≤ |η_n'(y_c)|`. -/
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

end Cutoff

/-! ## Approximation by cut-offs: smooth fields with vanishing tangential traces -/

section Approx

/-- Line derivative: `d/dt f(x + t e_k) = ∂_k f (x + t e_k)`. -/
theorem hasDerivAt_line {f : R3 → ℝ} (hf : Differentiable ℝ f) (x : R3) (k : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => f (x + Pi.single k s)) (pd k f (x + Pi.single k t)) t := by
  have hl : HasDerivAt (fun s : ℝ => x + Pi.single k s) (Pi.single k 1) t := by
    have : (fun s : ℝ => x + Pi.single k s) = fun s => x + s • (Pi.single k (1 : ℝ) : R3) := by
      funext s; rw [single_eq_smul k s]
    rw [this]
    simpa using ((hasDerivAt_id t).smul_const (Pi.single k (1 : ℝ) : R3)).const_add x
  exact (hf _).hasFDerivAt.comp_hasDerivAt t hl

/-- **Vanishing on two opposite faces with a bounded normal derivative**: if `f = 0` on
`{y_c = 0}` and `{y_c = ½}` and `|∂_c f| ≤ L`, then `|f(y)| ≤ L min(y_c, ½ - y_c)` on `Q`. -/
theorem abs_le_of_faces {f : R3 → ℝ} (hf : Differentiable ℝ f) {c : Fin 3} {L : ℝ}
    (hL : ∀ y, |pd c f y| ≤ L) (h0 : ∀ y : R3, y c = 0 → f y = 0)
    (h1 : ∀ y : R3, y c = 1 / 2 → f y = 0) {y : R3} (hy : y ∈ Qr) :
    |f y| ≤ L * min (y c) (1 / 2 - y c) := by
  set g : ℝ → ℝ := fun s => f (y + Pi.single c s)
  have hg : ∀ s, HasDerivAt g (pd c f (y + Pi.single c s)) s := hasDerivAt_line hf y c
  have hb : ∀ s ∈ (univ : Set ℝ), ‖deriv g s‖ ≤ L := fun s _ => by
    rw [(hg s).deriv, Real.norm_eq_abs]; exact hL _
  have hd : ∀ s ∈ (univ : Set ℝ), DifferentiableAt ℝ g s := fun s _ => (hg s).differentiableAt
  have hyc := hy c (mem_univ c)
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

/-- Product rule for `∂_k`. -/
theorem pd_mul {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (k : Fin 3)
    (x : R3) : pd k (fun y => f y * g y) x = pd k f x * g x + f x * pd k g x := by
  unfold BoundedDomain.pd
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- **`L²(Q)`-convergence of uniformly bounded, pointwise convergent sequences.** -/
theorem tendsto_toLp_of_bdd {g : ℕ → R3 → ℝ} {h : R3 → ℝ}
    (hg : ∀ n, MemLp (g n) 2 (volume.restrict Qr)) (hh : MemLp h 2 (volume.restrict Qr))
    {K : ℝ} (hK : ∀ n, ∀ y ∈ Qr, |g n y| ≤ K)
    (hlim : ∀ y ∈ Qr, Tendsto (fun n => g n y) atTop (𝓝 (h y))) :
    Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hh.toLp h)) := by
  have : IsFiniteMeasure (volume.restrict Qr) :=
    isFiniteMeasure_restrict.2 isBounded_Qr.measure_lt_top.ne
  rw [tendsto_iff_edist_tendsto_0]
  simp_rw [Lp.edist_toLp_toLp]
  have hui : UnifIntegrable g 2 (volume.restrict Qr) := by
    refine (unifIntegrable_const (ι := ℕ) one_le_two (by norm_num)
      (memLp_const (μ := volume.restrict Qr) K)).ae_mono (fun n => (hg n).aestronglyMeasurable)
      fun n => ?_
    filter_upwards [ae_restrict_mem measurableSet_Qr] with y hy
    rw [enorm_le_iff_norm_le, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hK n y hy).trans (le_abs_self K)
  exact tendsto_Lp_finite_of_tendsto_ae one_le_two (by norm_num)
    (fun n => (hg n).aestronglyMeasurable) hh hui
    (by filter_upwards [ae_restrict_mem measurableSet_Qr] with y hy; exact hlim y hy)

/-- Convergence in `L²(Q; ℝ³ˣ³)` is componentwise. -/
theorem tendsto_L2M_of_forall {u : ℕ → BoundedDomain.L2M Qr} {v : BoundedDomain.L2M Qr}
    (h : ∀ p, Tendsto (fun n => u n p) atTop (𝓝 (v p))) : Tendsto u atTop (𝓝 v) := by
  have hc := (PiLp.continuous_toLp 2 (fun _ : Ix => BoundedDomain.L2 Qr)).tendsto (WithLp.ofLp v)
  exact hc.comp (tendsto_pi_nhds.2 h)

/-- Convergence in `L²(Q; ℝ³)` is componentwise. -/
theorem tendsto_L2V_of_forall {u : ℕ → BoundedDomain.L2V Qr} {v : BoundedDomain.L2V Qr}
    (h : ∀ a, Tendsto (fun n => u n a) atTop (𝓝 (v a))) : Tendsto u atTop (𝓝 v) := by
  have hc := (PiLp.continuous_toLp 2 (fun _ : Fin 3 => BoundedDomain.L2 Qr)).tendsto
    (WithLp.ofLp v)
  exact hc.comp (tendsto_pi_nhds.2 h)

/-- **Cut-off approximation in `H(curl)`**: a smooth matrix field on `ℝ³`, bounded with bounded
first derivatives, whose tangential components vanish on the faces of `Q`
(`ψ_{ad} = 0` on `{y_c ∈ {0, ½}}` for `c ≠ d`), restricts to an element of `H̊(curl, Q)`:
`(ψ, curl ψ)` lies in the graph closure of the curl on `C_c^∞(Q; ℝ³ˣ³)`. The approximants are
`χ_n ψ`; the commutator `∇χ_n × ψ` stays bounded because `ψ_tan = O(dist to the face)`, and
converges to `0` pointwise in `Q`. -/
theorem mem_closure_curlGraph_of_smooth {ψ : Ix → R3 → ℝ}
    (hψ : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (ψ p)) {M L : ℝ} (hM : ∀ p y, |ψ p y| ≤ M)
    (hMc : ∀ p y, |curlM ψ p y| ≤ M) (hL : ∀ p c y, |pd c (ψ p) y| ≤ L)
    (hV : ∀ a c d, c ≠ d → ∀ y : R3, (y c = 0 ∨ y c = 1 / 2) → ψ (a, d) y = 0) :
    (BoundedDomain.smoothField isOpen_Qr isBounded_Qr ψ fun p => (hψ p).continuous,
      BoundedDomain.smoothField isOpen_Qr isBounded_Qr (curlM ψ)
        fun p => BoundedDomain.continuous_curlM (fun q => (hψ q).of_le (by simp)) p) ∈
      closure (BoundedDomain.curlGraph Qr) := by
  obtain ⟨M₀, hM₀, hM₀b⟩ := exists_bound_deriv_smoothTransition
  set Φ : ℕ → Ix → R3 → ℝ := fun n p y => chi n y * ψ p y
  have hΦ : ∀ n p, IsTest Qr (Φ n p) := fun n p => isTest_chi_mul (hψ p) n
  have hdiff : ∀ p, Differentiable ℝ (ψ p) := fun p => (hψ p).differentiable (by simp)
  have hchid : ∀ n, Differentiable ℝ (chi n) := fun n => (contDiff_chi n).differentiable (by simp)
  -- pointwise eventual equality on `Q`
  have hev : ∀ y ∈ Qr, ∀ᶠ n in atTop, ∀ p, (Φ n p) =ᶠ[𝓝 y] ψ p := fun y hy => by
    filter_upwards [eventually_chi_eq_one hy] with n hn p
    filter_upwards [hn] with z hz
    simp [Φ, hz]
  -- the face bound
  have hface : ∀ a c d, c ≠ d → ∀ y ∈ Qr, |ψ (a, d) y| ≤ L * min (y c) (1 / 2 - y c) :=
    fun a c d hcd y hy => abs_le_of_faces (hdiff _) (hL _ c)
      (fun z hz => hV a c d hcd z (Or.inl hz))
      (fun z hz => hV a c d hcd z (Or.inr hz)) hy
  have hcross : ∀ n a c d, c ≠ d → ∀ y ∈ Qr, |pd c (chi n) y * ψ (a, d) y| ≤ 4 * M₀ * L := by
    intro n a c d hcd y hy
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL (a, d) c y)
    rw [abs_mul]
    calc |pd c (chi n) y| * |ψ (a, d) y| ≤
          |deriv (eta n) (y c)| * (L * min (y c) (1 / 2 - y c)) :=
          mul_le_mul (abs_pd_chi_le n c y) (hface a c d hcd y hy) (abs_nonneg _) (abs_nonneg _)
      _ = L * (|deriv (eta n) (y c)| * min (y c) (1 / 2 - y c)) := by ring
      _ ≤ L * (4 * M₀) :=
          mul_le_mul_of_nonneg_left (abs_deriv_eta_mul_le hM₀b n (hy c (mem_univ c))) hL0
      _ = 4 * M₀ * L := by ring
  have hcurlΦ : ∀ n a b y, curlM (Φ n) (a, b) y = chi n y * curlM ψ (a, b) y +
      (pd (b + 1) (chi n) y * ψ (a, b + 2) y - pd (b + 2) (chi n) y * ψ (a, b + 1) y) := by
    intro n a b y
    simp only [curlM, Φ, pd_mul (hchid n) (hdiff _)]
    ring
  refine mem_closure_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun n => (BoundedDomain.testField (hΦ n),
    BoundedDomain.testField (BoundedDomain.isTest_curlM (hΦ n)))) ?_
    (Eventually.of_forall fun n => ⟨Φ n, hΦ n, fun ij =>
      ⟨BoundedDomain.coeFn_testField (hΦ n) ij,
        BoundedDomain.coeFn_testField (BoundedDomain.isTest_curlM (hΦ n)) ij⟩⟩)
  refine Tendsto.prodMk_nhds (tendsto_L2M_of_forall fun p => ?_)
    (tendsto_L2M_of_forall fun p => ?_)
  · refine tendsto_toLp_of_bdd (fun n => (hΦ n p).memLp)
      (BoundedDomain.memLp_of_continuous isOpen_Qr isBounded_Qr (hψ p).continuous) (K := M)
      (fun n y _ => ?_) fun y hy => ?_
    · simp only [Φ, abs_mul]
      calc |chi n y| * |ψ p y| ≤ 1 * M :=
            mul_le_mul (abs_chi_le_one n y) (hM p y) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with n hn
      exact (hn p).eq_of_nhds.symm
  · obtain ⟨a, b⟩ := p
    refine tendsto_toLp_of_bdd (fun n => (BoundedDomain.isTest_curlM (hΦ n) (a, b)).memLp)
      (BoundedDomain.memLp_of_continuous isOpen_Qr isBounded_Qr
        (BoundedDomain.continuous_curlM (fun q => (hψ q).of_le (by simp)) (a, b)))
      (K := M + 2 * (4 * M₀ * L)) (fun n y hy => ?_) fun y hy => ?_
    · rw [hcurlΦ]
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
      simp only [curlM, BoundedDomain.pd]
      rw [(hn _).fderiv_eq, (hn _).fderiv_eq]

/-- The `L²(Q)` class of a continuous vector field. -/
def smoothFieldV (σ : Fin 3 → R3 → ℝ) (hσ : ∀ a, Continuous (σ a)) : BoundedDomain.L2V Qr :=
  WithLp.toLp 2 fun a => (BoundedDomain.memLp_of_continuous isOpen_Qr isBounded_Qr (hσ a)).toLp _

/-- **Cut-off approximation in `H¹`**: a smooth vector field on `ℝ³`, bounded with bounded first
derivatives, vanishing on all faces of `Q`, restricts to an element of `H̊¹(Q; ℝ³)`. -/
theorem mem_closure_gradGraph_of_smooth {σ : Fin 3 → R3 → ℝ}
    (hσ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (σ a)) {M L : ℝ} (hM : ∀ a y, |σ a y| ≤ M)
    (hL : ∀ a c y, |pd c (σ a) y| ≤ L)
    (hV : ∀ a c, ∀ y : R3, (y c = 0 ∨ y c = 1 / 2) → σ a y = 0) :
    (smoothFieldV σ fun a => (hσ a).continuous,
      BoundedDomain.smoothField isOpen_Qr isBounded_Qr (BoundedDomain.gradM σ)
        fun p => BoundedDomain.continuous_pd ((hσ p.1).of_le (by simp)) p.2) ∈
      closure (BoundedDomain.gradGraph Qr) := by
  obtain ⟨M₀, hM₀, hM₀b⟩ := exists_bound_deriv_smoothTransition
  set φ : ℕ → Fin 3 → R3 → ℝ := fun n a y => chi n y * σ a y
  have hφ : ∀ n a, IsTest Qr (φ n a) := fun n a => isTest_chi_mul (hσ a) n
  have hdiff : ∀ a, Differentiable ℝ (σ a) := fun a => (hσ a).differentiable (by simp)
  have hchid : ∀ n, Differentiable ℝ (chi n) := fun n => (contDiff_chi n).differentiable (by simp)
  have hev : ∀ y ∈ Qr, ∀ᶠ n in atTop, ∀ a, (φ n a) =ᶠ[𝓝 y] σ a := fun y hy => by
    filter_upwards [eventually_chi_eq_one hy] with n hn a
    filter_upwards [hn] with z hz
    simp [φ, hz]
  have hface : ∀ a c, ∀ y ∈ Qr, |σ a y| ≤ L * min (y c) (1 / 2 - y c) :=
    fun a c y hy => abs_le_of_faces (hdiff _) (hL _ c) (fun z hz => hV a c z (Or.inl hz))
      (fun z hz => hV a c z (Or.inr hz)) hy
  have hcross : ∀ n a c, ∀ y ∈ Qr, |pd c (chi n) y * σ a y| ≤ 4 * M₀ * L := by
    intro n a c y hy
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL a c y)
    rw [abs_mul]
    calc |pd c (chi n) y| * |σ a y| ≤
          |deriv (eta n) (y c)| * (L * min (y c) (1 / 2 - y c)) :=
          mul_le_mul (abs_pd_chi_le n c y) (hface a c y hy) (abs_nonneg _) (abs_nonneg _)
      _ = L * (|deriv (eta n) (y c)| * min (y c) (1 / 2 - y c)) := by ring
      _ ≤ L * (4 * M₀) :=
          mul_le_mul_of_nonneg_left (abs_deriv_eta_mul_le hM₀b n (hy c (mem_univ c))) hL0
      _ = 4 * M₀ * L := by ring
  refine mem_closure_of_tendsto (b := (atTop : Filter ℕ)) (f := fun n =>
    (BoundedDomain.testFieldV (hφ n), BoundedDomain.testField (BoundedDomain.isTest_gradM (hφ n))))
    ?_ (Eventually.of_forall fun n => ⟨φ n, hφ n, fun i => (hφ n i).memLp.coeFn_toLp,
      fun ij => BoundedDomain.coeFn_testField (BoundedDomain.isTest_gradM (hφ n)) ij⟩)
  refine Tendsto.prodMk_nhds (tendsto_L2V_of_forall fun a => ?_)
    (tendsto_L2M_of_forall fun p => ?_)
  · refine tendsto_toLp_of_bdd (fun n => (hφ n a).memLp)
      (BoundedDomain.memLp_of_continuous isOpen_Qr isBounded_Qr (hσ a).continuous) (K := M)
      (fun n y _ => ?_) fun y hy => ?_
    · simp only [φ, abs_mul]
      calc |chi n y| * |σ a y| ≤ 1 * M :=
            mul_le_mul (abs_chi_le_one n y) (hM a y) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with n hn
      exact (hn a).eq_of_nhds.symm
  · obtain ⟨a, b⟩ := p
    refine tendsto_toLp_of_bdd (fun n => (BoundedDomain.isTest_gradM (hφ n) (a, b)).memLp)
      (BoundedDomain.memLp_of_continuous isOpen_Qr isBounded_Qr
        (BoundedDomain.continuous_pd ((hσ a).of_le (by simp)) b))
      (K := 4 * M₀ * L + L) (fun n y hy => ?_) fun y hy => ?_
    · simp only [BoundedDomain.gradM, φ, pd_mul (hchid n) (hdiff _)]
      have h2 : |chi n y * pd b (σ a) y| ≤ L := by
        rw [abs_mul]
        calc |chi n y| * |pd b (σ a) y| ≤ 1 * L :=
              mul_le_mul (abs_chi_le_one n y) (hL a b y) (abs_nonneg _) zero_le_one
          _ = L := one_mul L
      exact (abs_add_le _ _).trans (add_le_add (hcross n a b y hy) h2)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y hy] with n hn
      simp only [BoundedDomain.gradM, BoundedDomain.pd]
      rw [(hn _).fderiv_eq]

end Approx

/-! ## Trigonometric polynomials of the parity classes are smooth fields with the boundary
conditions -/

section Trig

/-- The trigonometric polynomial with coefficients `f` on `S` is smooth. -/
theorem isSmooth_trigPoly (f : L2 Z3 ℂ) (S : Finset Z3) : IsSmooth (trigPoly f S) := by
  unfold IsSmooth
  have e : (trigPoly f S : T3 → ℂ) ∘ proj = fun y => ∑ k ∈ S, f k * mFourier k (proj y) := by
    funext y
    simp [trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
      smul_eq_mul]
  rw [e]
  exact ContDiff.sum fun k _ => contDiff_const.mul (isSmooth_mFourier k)

/-- Fourier coefficients of a trigonometric polynomial. -/
theorem mFourierCoeff_trigPoly {f : L2 Z3 ℂ} {S : Finset Z3} (hS : ∀ k ∉ S, f k = 0) (k : Z3) :
    mFourierCoeff (trigPoly f S) k = f k := by
  rw [← mFourierCoeff_toLp, ← ofCoeff_eq_toLp S hS, mFourierCoeff_ofCoeff]

/-- The real part of the lift of a continuous function. -/
def reLift (g : T3 → ℂ) (y : R3) : ℝ := (g (proj y)).re

theorem contDiff_reLift {g : T3 → ℂ} (hg : IsSmooth g) : ContDiff ℝ (⊤ : ℕ∞) (reLift g) :=
  Complex.reCLM.contDiff.comp hg

/-- `∂_c Re(g ∘ proj) = Re((∂_c g) ∘ proj)`. -/
theorem pd_reLift {g : T3 → ℂ} (hg : IsSmooth g) (c : Fin 3) (y : R3) :
    pd c (reLift g) y = (partialT c g (proj y)).re := by
  have hd : Differentiable ℝ (g ∘ proj) := hg.contDiff_one.differentiable one_ne_zero
  rw [partialT_proj hd]
  unfold BoundedDomain.pd reLift
  have : HasFDerivAt (fun y => (g (proj y)).re)
      (Complex.reCLM.comp (fderiv ℝ (g ∘ proj) y)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hd y).hasFDerivAt
  rw [this.fderiv]
  rfl

theorem abs_reLift_le (g : C(T3, ℂ)) (y : R3) : |reLift g y| ≤ ‖g‖ :=
  (Complex.abs_re_le_norm _).trans (g.norm_coe_le_norm _)

/-- A smooth function on `𝕋³` has bounded partial derivatives. -/
theorem abs_pd_reLift_le {g : T3 → ℂ} (hg : IsSmooth g) (c : Fin 3) (y : R3) :
    |pd c (reLift g) y| ≤ ‖(⟨partialT c g, continuous_partialT hg.contDiff_one c⟩ : C(T3, ℂ))‖ := by
  rw [pd_reLift hg]
  exact (Complex.abs_re_le_norm _).trans
    ((⟨partialT c g, continuous_partialT hg.contDiff_one c⟩ : C(T3, ℂ)).norm_coe_le_norm _)

/-- The reflection fixes the faces: if `y_c ∈ {0, ½}` then `R_c (proj y) = proj y`. -/
theorem reflT_proj_of_face {c : Fin 3} {y : R3} (h : y c = 0 ∨ y c = 1 / 2) :
    reflT c (proj y) = proj y := by
  funext j
  by_cases hj : j = c
  · subst hj
    simp only [reflT, ↓reduceIte, proj]
    rcases h with h | h
    · rw [h]; simp
    · rw [h, ← AddCircle.coe_neg, show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by norm_num,
        AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
  · simp [reflT, hj]

/-- **Parity of a trigonometric polynomial**: if `f(R_c k) = s f(k)` on a reflection-invariant
support, then `P(R_c x) = s P(x)`. -/
theorem trigPoly_reflT {c : Fin 3} {f : L2 Z3 ℂ} {S : Finset Z3}
    (hSr : ∀ k ∈ S, Box.refl c k ∈ S) {s : ℂ} (hf : ∀ k, f (Box.refl c k) = s * f k) (x : T3) :
    trigPoly f S (reflT c x) = s * trigPoly f S x := by
  simp only [trigPoly, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mFourier_reflT, Finset.mul_sum]
  refine Finset.sum_nbij' (Box.refl c) (Box.refl c) (fun k hk => hSr k hk) (fun k hk => hSr k hk)
    (fun k _ => refl_refl c k) (fun k _ => refl_refl c k) fun k _ => ?_
  have e : f k = s * f (Box.refl c k) := by rw [← hf, refl_refl]
  rw [e]
  ring

/-- A trigonometric polynomial odd under `R_c` vanishes on the faces `y_c ∈ {0, ½}`. -/
theorem reLift_eq_zero_of_odd {c : Fin 3} {f : L2 Z3 ℂ} {S : Finset Z3}
    (hSr : ∀ k ∈ S, Box.refl c k ∈ S) (hf : ∀ k, f (Box.refl c k) = -f k) {y : R3}
    (hy : y c = 0 ∨ y c = 1 / 2) : reLift (trigPoly f S) y = 0 := by
  have h := trigPoly_reflT hSr (s := -1) (fun k => by rw [hf]; ring) (proj y)
  rw [reflT_proj_of_face hy] at h
  have h0 : trigPoly f S (proj y) = 0 := by linear_combination h / 2
  simp [reLift, h0]

theorem coeFn_resQ_toLp (g : C(T3, ℂ)) :
    (resQ (g.toLp 2 volume ℂ) : R3 → ℝ) =ᵐ[volume.restrict Qr] reLift g := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := (volume : Measure T3)) g
  filter_upwards [coeFn_resQ (g.toLp 2 volume ℂ), ae_Qr_of_ae_boxSet (ae_restrict_of_ae h)]
    with y h1 h2
  rw [h1]
  change (((g.toLp 2 volume ℂ : L2T) : T3 → ℂ) (proj y)).re = _
  rw [h2]; rfl

theorem le_sum_norm {ι : Type*} [Fintype ι] (F : ι → C(T3, ℂ)) (j : ι) :
    ‖F j‖ ≤ ∑ i, ‖F i‖ :=
  Finset.single_le_sum (f := fun i => ‖F i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- **A trigonometric polynomial in the electric parity class restricts into `H̊(curl, Q)`.** -/
theorem trig_mem_closure_curlGraph {E : L2M} (hE : E ∈ ParRow 1) {S : Finset Z3}
    (hS : ∀ k ∉ S, E k = 0) (hSr : ∀ i, ∀ k ∈ S, Box.refl i k ∈ S) (hc : E ∈ Hcurl) :
    (resB E, resB (curlT ⟨E, hc⟩)) ∈ closure (BoundedDomain.curlGraph Qr) := by
  have hent : ∀ p, ∀ k ∉ S, entry p E k = 0 := fun p k hk => by simp [hS k hk]
  set P : Ix → C(T3, ℂ) := fun p => trigPoly (entry p E) S
  have hPs : ∀ p, IsSmooth (P p) := fun p => isSmooth_trigPoly _ _
  set ψ : Ix → R3 → ℝ := fun p => reLift (P p)
  have hψ : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (ψ p) := fun p => contDiff_reLift (hPs p)
  set D : Ix → Fin 3 → C(T3, ℂ) := fun p c =>
    ⟨partialT c (P p), continuous_partialT (hPs p).contDiff_one c⟩
  set Q : Ix → C(T3, ℂ) := fun ab =>
    ⟨fun x => ∑ c, ∑ d, ((Feec.eps3 ab.2 c d : ℝ) : ℂ) * partialT c (P (ab.1, d)) x,
      continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
        continuous_const.mul (continuous_partialT (hPs _).contDiff_one c)⟩
  -- the curl in Fourier variables
  have hcurl : curlT ⟨E, hc⟩ = cField Q := by
    refine lp.ext (funext fun k => ?_)
    ext ⟨a, b⟩
    rw [cField_apply]
    simp only [Q, ContinuousMap.coe_mk]
    rw [mFourierCoeff_sum_sum _ fun c d => continuous_partialT (hPs (a, d)).contDiff_one c]
    simp only [mFourierCoeff_partialT (hPs _).contDiff_one, P,
      mFourierCoeff_trigPoly (hent _)]
    change curlSym (freq k) (E k) (a, b) = _
    rw [curlSym_apply, jM_apply, curlR_apply_eps3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [entry_apply, freq_apply]
    push_cast; ring
  have hcurlψ : ∀ ab y, curlM ψ ab y = reLift (Q ab) y := by
    rintro ⟨a, b⟩ y
    rw [curlM_eq_sum]
    simp only [ψ, pd_reLift (hPs _), reLift, Q, ContinuousMap.coe_mk, Complex.re_sum,
      Complex.re_ofReal_mul]
  have h1 : resB E = BoundedDomain.smoothField isOpen_Qr isBounded_Qr ψ
      (fun p => (hψ p).continuous) := by
    ext1 p
    refine Lp.ext ?_
    rw [resB_apply, ofCoeff_eq_toLp S (hent p)]
    filter_upwards [coeFn_resQ_toLp (P p), BoundedDomain.coeFn_smoothField isOpen_Qr isBounded_Qr
      ψ (fun p => (hψ p).continuous) p] with y h1 h2
    rw [h1, h2]
  have h2 : resB (curlT ⟨E, hc⟩) = BoundedDomain.smoothField isOpen_Qr isBounded_Qr (curlM ψ)
      (fun p => BoundedDomain.continuous_curlM (fun q => (hψ q).of_le (by simp)) p) := by
    ext1 p
    refine Lp.ext ?_
    rw [hcurl]
    filter_upwards [coeFn_resB_cField Q p, BoundedDomain.coeFn_smoothField isOpen_Qr isBounded_Qr
      (curlM ψ) (fun p => BoundedDomain.continuous_curlM (fun q => (hψ q).of_le (by simp)) p) p]
      with y h1 h2
    rw [h1, h2, hcurlψ]; rfl
  rw [h1, h2]
  refine mem_closure_curlGraph_of_smooth hψ (M := ∑ p, ‖P p‖ + ∑ p, ‖Q p‖)
    (L := ∑ p, ∑ c, ‖D p c‖) (fun p y => ?_) (fun p y => ?_) (fun p c y => ?_) ?_
  · exact (abs_reLift_le _ y).trans ((le_sum_norm P p).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
  · rw [hcurlψ]
    exact (abs_reLift_le _ y).trans ((le_sum_norm Q p).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
  · refine (abs_pd_reLift_le (hPs p) c y).trans ?_
    calc ‖D p c‖ ≤ ∑ c', ‖D p c'‖ := le_sum_norm (D p) c
      _ ≤ ∑ p', ∑ c', ‖D p' c'‖ := Finset.single_le_sum (f := fun p' => ∑ c', ‖D p' c'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ p)
  · intro a c d hcd y hy
    refine reLift_eq_zero_of_odd (hSr c) (fun k => ?_) hy
    simp only [entry_apply]
    rw [hE c k a d]
    simp [colSign, hcd]

end Trig

/-! ## Fourier truncation and the inclusion of the parity spaces into `H̊(curl, Q)`, `H̊¹(Q)` -/

section Trunc

/-- The frequency box `{k : |k_i| ≤ N}`. -/
def boxFin (N : ℕ) : Finset Z3 := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

theorem mem_boxFin {N : ℕ} {k : Z3} : k ∈ boxFin N ↔ ∀ i, |k i| ≤ N := by
  simp [boxFin, Fintype.mem_piFinset, abs_le]

theorem refl_mem_boxFin_iff {N : ℕ} (i : Fin 3) {k : Z3} :
    Box.refl i k ∈ boxFin N ↔ k ∈ boxFin N := by
  have h : ∀ j, |Box.refl i k j| = |k j| := fun j => by
    by_cases hj : j = i
    · subst hj; simp [Box.refl]
    · simp [Box.refl, Function.update_of_ne hj]
  simp only [mem_boxFin, h]

theorem monotone_boxFin : Monotone boxFin := fun N M h k hk =>
  mem_boxFin.2 fun i => (mem_boxFin.1 hk i).trans (by exact_mod_cast h)

theorem exists_mem_boxFin (k : Z3) : ∃ N, k ∈ boxFin N := by
  refine ⟨∑ i, (k i).natAbs, mem_boxFin.2 fun i => ?_⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Fourier truncation to `boxFin N`. -/
def trunc (N : ℕ) (A : L2 Z3 F) : L2 Z3 F := ∑ k ∈ boxFin N, lp.single 2 k (A k)

theorem trunc_apply (N : ℕ) (A : L2 Z3 F) (k : Z3) :
    trunc N A k = if k ∈ boxFin N then A k else 0 := by
  rw [trunc, lp_sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (fun h' => absurd h h')]
    simp
  · exact Finset.sum_eq_zero fun j hj => by
      have : k ≠ j := fun e => h (e ▸ hj)
      simp [this]

omit [NormedSpace ℝ F] in
theorem tendsto_trunc (A : L2 Z3 F) : Tendsto (fun N => trunc N A) atTop (𝓝 A) :=
  (lp.hasSum_single (p := 2) (by norm_num) A).comp
    (tendsto_atTop_finset_of_monotone monotone_boxFin exists_mem_boxFin)

theorem trunc_eq_zero {N : ℕ} {A : L2 Z3 F} {k : Z3} (hk : k ∉ boxFin N) : trunc N A k = 0 := by
  rw [trunc_apply]; exact ite_eq_right_iff.2 fun h => absurd h hk

end Trunc

theorem trunc_mem_ParRow {τ : ℂ} {A : L2M} (hA : A ∈ ParRow τ) (N : ℕ) : trunc N A ∈ ParRow τ := by
  intro i k a b
  rw [trunc_apply, trunc_apply]
  by_cases hk : k ∈ boxFin N
  · simp only [(refl_mem_boxFin_iff i).2 hk, hk, ↓reduceIte]; exact hA i k a b
  · have hk' : Box.refl i k ∉ boxFin N := fun h => hk ((refl_mem_boxFin_iff i).1 h)
    simp [hk, hk']

theorem trunc_mem_ParV {σ : L2V} (hσ : σ ∈ ParV) (N : ℕ) : trunc N σ ∈ ParV := by
  intro i k a
  rw [trunc_apply, trunc_apply]
  by_cases hk : k ∈ boxFin N
  · simp only [(refl_mem_boxFin_iff i).2 hk, hk, ↓reduceIte]; exact hσ i k a
  · have hk' : Box.refl i k ∉ boxFin N := fun h => hk ((refl_mem_boxFin_iff i).1 h)
    simp [hk, hk']

/-- Truncation commutes with the multipliers. -/
theorem trunc_mem_mulDomain {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (m : Z3 → E →L[ℝ] V) {A : L2 Z3 E}
    (hA : A ∈ mulDomain m) (N : ℕ) :
    ∃ h : trunc N A ∈ mulDomain m, mulOp m ⟨_, h⟩ = trunc N (mulOp m ⟨A, hA⟩) := by
  have e : (fun k => m k (trunc N A k)) = ⇑(trunc N (mulOp m ⟨A, hA⟩)) := by
    funext k
    rw [trunc_apply, trunc_apply]
    split_ifs
    · rfl
    · exact map_zero _
  have h : trunc N A ∈ mulDomain m := by
    change Memℓp _ 2
    rw [e]; exact lp.memℓp _
  exact ⟨h, lp.ext e⟩

/-- **The electric parity space restricts into `H̊(curl, Q)`** (direction "parity space ⊆ H̊"):
for `E ∈ ParRow 1 ∩ H(curl, 𝕋³)`, `(E|_Q, (curl E)|_Q)` is a graph-norm limit of test fields.
The Fourier truncations of `E` are trigonometric polynomials in `ParRow 1`, whose tangential
components vanish on `∂Q`; each is approximated by cut-offs (`mem_closure_curlGraph_of_smooth`). -/
theorem resB_mem_closure_curlGraph {E : L2M} (hE : E ∈ ParRow 1) (hc : E ∈ Hcurl) :
    (resB E, resB (curlT ⟨E, hc⟩)) ∈ closure (BoundedDomain.curlGraph Qr) := by
  choose hN eN using fun N => trunc_mem_mulDomain (fun k => curlSym (freq k)) hc N
  have hmem : ∀ N, (resB (trunc N E), resB (curlT ⟨_, hN N⟩)) ∈
      closure (BoundedDomain.curlGraph Qr) := fun N =>
    trig_mem_closure_curlGraph (trunc_mem_ParRow hE N) (fun k hk => trunc_eq_zero hk)
      (fun i k hk => (refl_mem_boxFin_iff i).2 hk) (hN N)
  refine isClosed_closure.mem_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun N => (resB (trunc N E), resB (curlT ⟨_, hN N⟩))) ?_ (Eventually.of_forall hmem)
  refine Tendsto.prodMk_nhds ((resB.continuous.tendsto _).comp (tendsto_trunc E)) ?_
  have : (fun N => resB (curlT ⟨_, hN N⟩)) = fun N => resB (trunc N (curlT ⟨E, hc⟩)) :=
    funext fun N => congrArg resB (eN N)
  rw [this]
  exact (resB.continuous.tendsto _).comp (tendsto_trunc _)

/-- **`ParRow 1 ∩ H(curl, 𝕋³)` restricts into `H̊(curl, Q)`**, and the restriction intertwines the
periodic curl with the curl of `H̊(curl, Q)` (`curlClosure`). -/
theorem resB_mem_HcurlZero {E : L2M} (hE : E ∈ ParRow 1) (hc : E ∈ Hcurl) :
    ∃ h : resB E ∈ BoundedDomain.HcurlZero Qr,
      BoundedDomain.curlClosure ⟨resB E, BoundedDomain.mem_domain_curlClosure.2 h⟩ =
        resB (curlT ⟨E, hc⟩) := by
  have hm := resB_mem_closure_curlGraph hE hc
  refine ⟨⟨_, hm⟩, BoundedDomain.apply_eq_of_mem_graph ?_ _⟩
  rw [BoundedDomain.curlClosure_graph isOpen_Qr isBounded_Qr, ← SetLike.mem_coe,
    BoundedDomain.coe_topologicalClosure_curlGraphSub]
  exact hm


/-- The `a`-th component of a vector field of the box model, as a scalar coefficient sequence. -/
def entV (a : Fin 3) (σ : L2V) : L2 Z3 ℂ := (swapL2 (ι := Z3) (P := Fin 3)).symm σ a

@[simp] theorem entV_apply (a : Fin 3) (σ : L2V) (k : Z3) : entV a σ k = σ k a := rfl

/-- **A trigonometric polynomial in the Dirichlet parity class restricts into `H̊¹(Q)`.** -/
theorem trig_mem_closure_gradGraph {σ : L2V} (hσ : σ ∈ ParV) {S : Finset Z3}
    (hS : ∀ k ∉ S, σ k = 0) (hSr : ∀ i, ∀ k ∈ S, Box.refl i k ∈ S) (hg : σ ∈ gradT.domain) :
    (resBV σ, resB (gradT ⟨σ, hg⟩)) ∈ closure (BoundedDomain.gradGraph Qr) := by
  have hent : ∀ a, ∀ k ∉ S, entV a σ k = 0 := fun a k hk => by simp [hS k hk]
  set P : Fin 3 → C(T3, ℂ) := fun a => trigPoly (entV a σ) S
  have hPs : ∀ a, IsSmooth (P a) := fun a => isSmooth_trigPoly _ _
  set ψ : Fin 3 → R3 → ℝ := fun a => reLift (P a)
  have hψ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (ψ a) := fun a => contDiff_reLift (hPs a)
  set D : Fin 3 → Fin 3 → C(T3, ℂ) := fun a c =>
    ⟨partialT c (P a), continuous_partialT (hPs a).contDiff_one c⟩
  set G : Ix → C(T3, ℂ) := fun ab => D ab.1 ab.2
  have hgrad : gradT ⟨σ, hg⟩ = cField G := by
    refine lp.ext (funext fun k => ?_)
    ext ⟨a, b⟩
    rw [cField_apply]
    simp only [G, D, ContinuousMap.coe_mk]
    rw [mFourierCoeff_partialT (hPs a).contDiff_one, mFourierCoeff_trigPoly (hent a)]
    change gradSym (freq k) (σ k) (a, b) = _
    rw [gradSym_apply, entV_apply, freq_apply]
    push_cast; ring
  have h1 : resBV σ = smoothFieldV ψ fun a => (hψ a).continuous := by
    ext1 a
    refine Lp.ext ?_
    rw [resBV_apply, vectorFourier_symm_apply]
    change (resQ (ofCoeff (entV a σ)) : R3 → ℝ) =ᵐ[_] _
    rw [ofCoeff_eq_toLp S (hent a)]
    filter_upwards [coeFn_resQ_toLp (P a),
      (BoundedDomain.memLp_of_continuous isOpen_Qr isBounded_Qr (hψ a).continuous).coeFn_toLp]
      with y h1 h2
    rw [h1]
    exact h2.symm
  have h2 : resB (gradT ⟨σ, hg⟩) = BoundedDomain.smoothField isOpen_Qr isBounded_Qr
      (BoundedDomain.gradM ψ)
      (fun p => BoundedDomain.continuous_pd ((hψ p.1).of_le (by simp)) p.2) := by
    ext1 p
    refine Lp.ext ?_
    rw [hgrad]
    filter_upwards [coeFn_resB_cField G p, BoundedDomain.coeFn_smoothField isOpen_Qr isBounded_Qr
      (BoundedDomain.gradM ψ)
      (fun p => BoundedDomain.continuous_pd ((hψ p.1).of_le (by simp)) p.2) p] with y h1 h2
    rw [h1, h2]
    simp only [BoundedDomain.gradM, ψ, pd_reLift (hPs _), G, D, ContinuousMap.coe_mk]
  rw [h1, h2]
  refine mem_closure_gradGraph_of_smooth hψ (M := ∑ a, ‖P a‖) (L := ∑ a, ∑ c, ‖D a c‖)
    (fun a y => (abs_reLift_le _ y).trans (le_sum_norm P a)) (fun a c y => ?_) ?_
  · refine (abs_pd_reLift_le (hPs a) c y).trans ?_
    calc ‖D a c‖ ≤ ∑ c', ‖D a c'‖ := le_sum_norm (D a) c
      _ ≤ ∑ a', ∑ c', ‖D a' c'‖ := Finset.single_le_sum (f := fun a' => ∑ c', ‖D a' c'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  · intro a c y hy
    exact reLift_eq_zero_of_odd (hSr c) (fun k => by simp only [entV_apply]; exact hσ c k a) hy

/-- **The Dirichlet parity space restricts into `H̊¹(Q; ℝ³)`**: for `σ ∈ ParV ∩ H¹(𝕋³)`,
`(σ|_Q, (grad σ)|_Q)` is a graph-norm limit of test fields. -/
theorem resBV_mem_closure_gradGraph {σ : L2V} (hσ : σ ∈ ParV) (hg : σ ∈ gradT.domain) :
    (resBV σ, resB (gradT ⟨σ, hg⟩)) ∈ closure (BoundedDomain.gradGraph Qr) := by
  choose hN eN using fun N => trunc_mem_mulDomain (fun k => gradSym (freq k)) hg N
  have hmem : ∀ N, (resBV (trunc N σ), resB (gradT ⟨_, hN N⟩)) ∈
      closure (BoundedDomain.gradGraph Qr) := fun N =>
    trig_mem_closure_gradGraph (trunc_mem_ParV hσ N) (fun k hk => trunc_eq_zero hk)
      (fun i k hk => (refl_mem_boxFin_iff i).2 hk) (hN N)
  refine isClosed_closure.mem_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun N => (resBV (trunc N σ), resB (gradT ⟨_, hN N⟩))) ?_ (Eventually.of_forall hmem)
  refine Tendsto.prodMk_nhds ((resBV.continuous.tendsto _).comp (tendsto_trunc σ)) ?_
  have : (fun N => resB (gradT ⟨_, hN N⟩)) = fun N => resB (trunc N (gradT ⟨σ, hg⟩)) :=
    funext fun N => congrArg resB (eN N)
  rw [this]
  exact (resB.continuous.tendsto _).comp (tendsto_trunc _)

/-- **`ParV ∩ H¹(𝕋³)` restricts into `H̊¹(Q; ℝ³)`**, intertwining the periodic gradient with the
gradient of `H̊¹(Q)` (`gradClosure`). -/
theorem resBV_mem_H1Zero {σ : L2V} (hσ : σ ∈ ParV) (hg : σ ∈ gradT.domain) :
    ∃ h : resBV σ ∈ (BoundedDomain.gradClosure (Ω := Qr)).domain,
      BoundedDomain.gradClosure ⟨resBV σ, h⟩ = resB (gradT ⟨σ, hg⟩) := by
  have hm := resBV_mem_closure_gradGraph hσ hg
  have hg' : (resBV σ, resB (gradT ⟨σ, hg⟩)) ∈ (BoundedDomain.gradClosure (Ω := Qr)).graph := by
    rw [BoundedDomain.gradClosure_graph isOpen_Qr isBounded_Qr]
    exact hm
  exact ⟨LinearPMap.mem_domain_of_mem_graph hg', BoundedDomain.apply_eq_of_mem_graph hg' _⟩


/-! ## The eight reflected boxes tile `𝕋³` (up to a null set) -/

section Tiling

/-- The reflection `x_j ↦ -x_j` for every `j` with `ε j`. -/
def reflB (ε : Fin 3 → Bool) (x : T3) : T3 := fun j => if ε j then -x j else x j

@[simp] theorem reflB_reflB (ε : Fin 3 → Bool) (x : T3) : reflB ε (reflB ε x) = x := by
  funext j; by_cases h : ε j <;> simp [reflB, h]

theorem measurePreserving_reflB (ε : Fin 3 → Bool) :
    MeasurePreserving (reflB ε) (volume : Measure T3) volume := by
  have h := measurePreserving_pi (fun _ : Fin 3 => (volume : Measure UnitAddCircle))
    (fun _ => volume)
    (f := fun j => if ε j then (Neg.neg : UnitAddCircle → UnitAddCircle) else id) fun j => by
      split_ifs
      · exact Measure.measurePreserving_neg volume
      · exact MeasurePreserving.id volume
  convert h using 1
  funext x j
  by_cases hj : ε j <;> simp [reflB, hj]

/-- The reflection as a measurable equivalence. -/
def reflBE (ε : Fin 3 → Bool) : T3 ≃ᵐ T3 where
  toFun := reflB ε
  invFun := reflB ε
  left_inv := reflB_reflB ε
  right_inv := reflB_reflB ε
  measurable_toFun := (measurePreserving_reflB ε).measurable
  measurable_invFun := (measurePreserving_reflB ε).measurable

/-- The reflected box `R_ε(Q)`. -/
def piece (ε : Fin 3 → Bool) : Set T3 := reflB ε ⁻¹' boxSet

theorem measurableSet_piece (ε : Fin 3 → Bool) : MeasurableSet (piece ε) :=
  measurableSet_boxSet.preimage (measurePreserving_reflB ε).measurable

theorem disjoint_piece {ε ε' : Fin 3 → Bool} (h : ε ≠ ε') : Disjoint (piece ε) (piece ε') := by
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

/-- The faces `{x_j ∈ {0, ½}}` of the reflected boxes. -/
def faceSet : Set T3 := ⋃ j : Fin 3, {x | x j = 0} ∪ {x | x j = ((1 / 2 : ℝ) : UnitAddCircle)}

theorem volume_faceSet : volume faceSet = 0 := by
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

theorem mem_iUnion_piece {x : T3} (hx : x ∉ faceSet) : x ∈ ⋃ ε, piece ε := by
  classical
  simp only [faceSet, mem_iUnion, mem_union, mem_ofPred_eq, not_exists, not_or] at hx
  refine mem_iUnion.2 ⟨fun j => decide (x j ∉ halfArc), fun j _ => ?_⟩
  simp only [reflB]
  by_cases h : x j ∈ halfArc
  · simp [h]
  · simp only [h, not_false_eq_true, decide_true, ↓reduceIte]
    exact (mem_halfArc_or_neg (hx j).1 (hx j).2).resolve_left h

theorem iUnion_piece_ae_eq_univ : (⋃ ε, piece ε : Set T3) =ᵐ[volume] (univ : Set T3) := by
  refine (ae_eq_univ).2 (measure_mono_null ?_ volume_faceSet)
  intro x hx
  by_contra h
  exact hx (mem_iUnion_piece h)

/-- **Tiling formula**: `∫_{𝕋³} g = Σ_ε ∫_Q g ∘ R_ε`. -/
theorem integral_eq_sum_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : T3 → E}
    (hg : Integrable g) : ∫ x, g x = ∑ ε : Fin 3 → Bool, ∫ x in boxSet, g (reflB ε x) := by
  rw [← setIntegral_univ, ← setIntegral_congr_set iUnion_piece_ae_eq_univ,
    integral_iUnion_fintype measurableSet_piece (fun ε ε' h => disjoint_piece h)
      fun ε => hg.integrableOn]
  refine Finset.sum_congr rfl fun ε _ => ?_
  have h := (measurePreserving_reflB ε).setIntegral_preimage_emb (reflBE ε).measurableEmbedding
    (fun y => g (reflB ε y)) boxSet
  simp only [reflB_reflB] at h
  exact h

end Tiling

/-! ## Parity fields: the `L²(𝕋³)` norm is `8` times the `L²(Q)` norm -/

section ParityNorm

theorem mFourierCoeff_congr_ae {f g : T3 → ℂ} (h : f =ᵐ[volume] g) (k : Z3) :
    mFourierCoeff f k = mFourierCoeff g k :=
  integral_congr_ae (h.mono fun x hx => by simp [hx])

/-- A parity relation on Fourier coefficients is a parity relation of the function. -/
theorem comp_reflT_ae {i : Fin 3} {f : L2T} {s : ℂ}
    (h : ∀ k, mFourierCoeff (f : T3 → ℂ) (Box.refl i k) = s * mFourierCoeff (f : T3 → ℂ) k) :
    (fun x => (f : T3 → ℂ) (reflT i x)) =ᵐ[volume] fun x => s * (f : T3 → ℂ) x := by
  set g : L2T := Lp.compMeasurePreserving (reflT i) (measurePreserving_reflT i) f
  have hg : (g : T3 → ℂ) =ᵐ[volume] fun x => (f : T3 → ℂ) (reflT i x) :=
    Lp.coeFn_compMeasurePreserving _ _
  have hsf : ((s • f : L2T) : T3 → ℂ) =ᵐ[volume] fun x => s * (f : T3 → ℂ) x :=
    (Lp.coeFn_smul s f).mono fun x hx => by rw [hx]; rfl
  have e : g = s • f := eq_of_mFourierCoeff_eq fun k => by
    rw [mFourierCoeff_congr_ae hg, mFourierCoeff_comp_reflT, h, mFourierCoeff_congr_ae hsf]
    simp only [mFourierCoeff, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have e' : (g : T3 → ℂ) = ((s • f : L2T) : T3 → ℂ) := by rw [e]
  exact hg.symm.trans (e' ▸ hsf)

theorem reflB_eq_comp (ε : Fin 3 → Bool) (x : T3) :
    reflB ε x = (if ε 2 then reflT 2 else id) ((if ε 1 then reflT 1 else id)
      ((if ε 0 then reflT 0 else id) x)) := by
  funext j
  by_cases h0 : ε 0 <;> by_cases h1 : ε 1 <;> by_cases h2 : ε 2 <;> fin_cases j <;>
    simp [reflB, reflT, h0, h1, h2]

theorem measurePreserving_ite_reflT (b : Bool) (i : Fin 3) :
    MeasurePreserving (if b then reflT i else id) (volume : Measure T3) volume := by
  cases b
  · exact MeasurePreserving.id volume
  · exact measurePreserving_reflT i

/-- **Parity functions have reflection-invariant modulus**. -/
theorem norm_comp_reflB_ae {f : L2T} {s : Fin 3 → ℂ} (hs : ∀ i, ‖s i‖ = 1)
    (h : ∀ i k, mFourierCoeff (f : T3 → ℂ) (Box.refl i k) = s i * mFourierCoeff (f : T3 → ℂ) k)
    (ε : Fin 3 → Bool) :
    (fun x => ‖(f : T3 → ℂ) (reflB ε x)‖) =ᵐ[volume] fun x => ‖(f : T3 → ℂ) x‖ := by
  have h1 : ∀ (b : Bool) (i : Fin 3), (fun x => ‖(f : T3 → ℂ) ((if b then reflT i else id) x)‖)
      =ᵐ[volume] fun x => ‖(f : T3 → ℂ) x‖ := by
    intro b i
    cases b
    · exact EventuallyEq.rfl
    · filter_upwards [comp_reflT_ae (h i)] with x hx
      change ‖(f : T3 → ℂ) (reflT i x)‖ = _
      rw [hx, norm_mul, hs, one_mul]
  have step : ∀ {T T' : T3 → T3}, MeasurePreserving T' volume volume →
      (fun x => ‖(f : T3 → ℂ) (T x)‖) =ᵐ[volume] (fun x => ‖(f : T3 → ℂ) x‖) →
      (fun x => ‖(f : T3 → ℂ) (T' x)‖) =ᵐ[volume] (fun x => ‖(f : T3 → ℂ) x‖) →
      (fun x => ‖(f : T3 → ℂ) (T (T' x))‖) =ᵐ[volume] (fun x => ‖(f : T3 → ℂ) x‖) :=
    fun hT' hT hT2 => (hT'.quasiMeasurePreserving.ae_eq_comp hT).trans hT2
  have e : (fun x => ‖(f : T3 → ℂ) (reflB ε x)‖) = fun x =>
      ‖(f : T3 → ℂ) ((if ε 2 then reflT 2 else id) ((if ε 1 then reflT 1 else id)
        ((if ε 0 then reflT 0 else id) x)))‖ := funext fun x => by rw [reflB_eq_comp]
  rw [e]
  exact step ((measurePreserving_ite_reflT _ 1).comp (measurePreserving_ite_reflT _ 0)) (h1 _ 2)
    (step (measurePreserving_ite_reflT _ 0) (h1 _ 1) (h1 _ 0))

theorem norm_sq_L2T (f : L2T) : ‖f‖ ^ 2 = ∫ x, ‖(f : T3 → ℂ) x‖ ^ 2 := by
  have e : ⟪f, f⟫_ℂ = ((∫ x, ‖(f : T3 → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), e]
  exact Complex.ofReal_re _

theorem norm_sq_L2Qr (g : BoundedDomain.L2 Qr) :
    ‖g‖ ^ 2 = ∫ y, (g : R3 → ℝ) y ^ 2 ∂volume.restrict Qr := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [sq]

/-- **The norm of a parity function**: `‖f‖²_{L²(𝕋³)} = 8 (‖Re f|_Q‖² + ‖Im f|_Q‖²)`. -/
theorem norm_sq_eq_eight {f : L2T} {s : Fin 3 → ℂ} (hs : ∀ i, ‖s i‖ = 1)
    (h : ∀ i k, mFourierCoeff (f : T3 → ℂ) (Box.refl i k) = s i * mFourierCoeff (f : T3 → ℂ) k) :
    ‖f‖ ^ 2 = 8 * (‖resQ f‖ ^ 2 + ‖resQ ((-Complex.I) • f)‖ ^ 2) := by
  have hint : Integrable (fun x => ‖(f : T3 → ℂ) x‖ ^ 2) :=
    (Lp.memLp f).integrable_norm_pow two_ne_zero
  rw [norm_sq_L2T, integral_eq_sum_box hint]
  have hb : ∀ ε : Fin 3 → Bool, ∫ x in boxSet, ‖(f : T3 → ℂ) (reflB ε x)‖ ^ 2 =
      ∫ x in boxSet, ‖(f : T3 → ℂ) x‖ ^ 2 := fun ε =>
    setIntegral_congr_ae₀ measurableSet_boxSet.nullMeasurableSet
      ((norm_comp_reflB_ae hs h ε).mono fun x hx _ => by simp only at hx ⊢; rw [hx])
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul]
  have hbox : ∫ x in boxSet, ‖(f : T3 → ℂ) x‖ ^ 2 =
      ‖resQ f‖ ^ 2 + ‖resQ ((-Complex.I) • f)‖ ^ 2 := by
    rw [setIntegral_boxSet _ hint.aestronglyMeasurable.restrict, norm_sq_L2Qr, norm_sq_L2Qr,
      ← integral_add]
    · refine integral_congr_ae ?_
      have hI0 : ∀ᵐ x ∂(volume : Measure T3), (((-Complex.I) • f : L2T) : T3 → ℂ) x =
          -Complex.I * (f : T3 → ℂ) x :=
        (Lp.coeFn_smul (-Complex.I) f).mono fun x hx => by rw [hx]; rfl
      have hI : ∀ᵐ y ∂volume.restrict Qr, (((-Complex.I) • f : L2T) : T3 → ℂ) (proj y) =
          -Complex.I * (f : T3 → ℂ) (proj y) :=
        ae_Qr_of_ae_boxSet (p := fun x => (((-Complex.I) • f : L2T) : T3 → ℂ) x =
          -Complex.I * (f : T3 → ℂ) x) (ae_restrict_of_ae hI0)
      filter_upwards [coeFn_resQ f, coeFn_resQ ((-Complex.I) • f), hI] with y h1 h2 h3
      rw [h1, h2, h3, Complex.sq_norm, Complex.normSq_apply]
      simp [sq]
    · exact (Lp.memLp (resQ f)).integrable_sq
    · exact (Lp.memLp (resQ ((-Complex.I) • f))).integrable_sq
  rw [hbox]
  norm_num

end ParityNorm

/-! ## Real parity fields are determined by their restriction to `Q` -/

section RealParity

/-- If the real part of `g` vanishes a.e. on the box, its restriction is `0`. -/
theorem resQ_eq_zero_of_re {g : L2T} (h : ∀ᵐ x ∂volume, ((g : T3 → ℂ) x).re = 0) :
    resQ g = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_resQ g, ae_Qr_of_ae_boxSet (p := fun x => ((g : T3 → ℂ) x).re = 0)
    (ae_restrict_of_ae h), Lp.coeFn_zero ℝ 2 (volume.restrict Qr)] with y h1 h2 h3
  rw [h1, h3, h2]; rfl

/-- The imaginary part of a real-valued scalar function restricts to `0`. -/
theorem resQ_I_smul_eq_zero {f : L2T}
    (hf : ∀ k, mFourierCoeff (f : T3 → ℂ) (-k) = conj (mFourierCoeff (f : T3 → ℂ) k)) :
    resQ ((-Complex.I) • f) = 0 := by
  have hs : star f = f := (star_eq_self_iff f).2 hf
  refine resQ_eq_zero_of_re ?_
  filter_upwards [Lp.coeFn_smul (-Complex.I) f, Lp.coeFn_star f] with x h1 h2
  rw [h1]
  have hx : conj ((f : T3 → ℂ) x) = (f : T3 → ℂ) x := by
    have := congrFun (congrArg (fun u : L2T => (u : T3 → ℂ)) hs) x
    rw [h2] at this
    exact this
  have him : ((f : T3 → ℂ) x).im = 0 := by
    have := congrArg Complex.im hx
    rw [Complex.conj_im] at this
    linarith
  change ((-Complex.I) * (f : T3 → ℂ) x).re = 0
  simp [him]

theorem ofCoeff_smul (c : ℂ) (f : L2 Z3 ℂ) : ofCoeff (c • f) = c • ofCoeff f :=
  (mFourierBasis (d := Fin 3)).repr.symm.map_smul c f

theorem entry_complex_smul (c : ℂ) (A : L2M) (p : Ix) : entry p (c • A) = c • entry p A := by
  ext k; simp [entry_apply]

theorem mFourierCoeff_ofCoeff_entry (A : L2M) (p : Ix) (k : Z3) :
    mFourierCoeff (ofCoeff (entry p A) : T3 → ℂ) k = A k p := by
  rw [mFourierCoeff_ofCoeff, entry_apply]

/-- **The norm of a field of a row-wise parity class**:
`‖A‖²_{L²(𝕋³)} = 8 (‖Re A|_Q‖² + ‖Im A|_Q‖²)`. -/
theorem norm_sq_of_mem_fix (ε : ℝ) (hε : ε * ε = 1) {A : L2M} (hA : A ∈ (rowMf ε hε).lift.fix) :
    ‖A‖ ^ 2 = 8 * (‖resB A‖ ^ 2 + ‖resB ((-Complex.I) • A)‖ ^ 2) := by
  have hpar : ∀ i k p, A (Box.refl i k) p = ((ε * colSignR i p.2 : ℝ) : ℂ) * A k p := by
    intro i k p
    have h1 := congrArg (fun B : L2M => B k p) (hA i)
    change rowSgn (ε : ℂ) i (A (Box.refl i k)) p = A k p at h1
    obtain ⟨a, b⟩ := p
    rw [rowSgn_apply, colSign_eq] at h1
    rw [← h1]
    have h2 := colSignR_mul_self i b
    simp only
    rw [← mul_assoc, ← mul_assoc]
    have : ((ε * colSignR i b : ℝ) : ℂ) * ε * colSignR i b =
        ((ε * ε * (colSignR i b * colSignR i b) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, hε, h2]; simp
  have hp : ∀ p, ‖ofCoeff (entry p A)‖ ^ 2 =
      8 * (‖resQ (ofCoeff (entry p A))‖ ^ 2 + ‖resQ ((-Complex.I) • ofCoeff (entry p A))‖ ^ 2) :=
    fun p => norm_sq_eq_eight (s := fun i => ((ε * colSignR i p.2 : ℝ) : ℂ))
      (fun i => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        rcases mul_self_eq_one_iff.1 hε with h | h <;> unfold colSignR <;> split_ifs <;>
          simp [h])
      fun i k => by
        rw [mFourierCoeff_ofCoeff_entry, mFourierCoeff_ofCoeff_entry, hpar]
  have hn : ‖A‖ = ‖matrixFourier.symm A‖ := (matrixFourier.symm.norm_map A).symm
  rw [hn, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [matrixFourier_symm_apply, hp p, resB_apply, resB_apply, entry_complex_smul, ofCoeff_smul]

theorem isRealM_iff (A : L2M) : IsRealM A ↔ IsReal A := by
  constructor
  · intro h k; ext ⟨a, b⟩; rw [conjM_apply]; exact h k (a, b)
  · intro h k ⟨a, b⟩; rw [h k, conjM_apply]

theorem isRealM_curlT {A : L2M} (hc : A ∈ Hcurl) (hA : IsRealM A) :
    IsRealM (curlT ⟨A, hc⟩) :=
  (isRealM_iff _).2 (isReal_curlT ⟨A, hc⟩ ((isRealM_iff A).1 hA))

theorem isRealM_gradT {σ : L2V} (hg : σ ∈ gradT.domain) (hσ : IsRealV σ) :
    IsRealM (gradT ⟨σ, hg⟩) := fun k ⟨a, b⟩ => by
  change gradSym (freq (-k)) (σ (-k)) (a, b) = conj (gradSym (freq k) (σ k) (a, b))
  rw [gradSym_apply, gradSym_apply, hσ k a, freq_neg]
  simp [map_mul, Complex.conj_I]

/-- The imaginary part of a real field restricts to `0`. -/
theorem resB_I_smul_eq_zero {A : L2M} (hA : IsRealM A) : resB ((-Complex.I) • A) = 0 := by
  ext1 p
  rw [resB_apply, entry_complex_smul, ofCoeff_smul]
  exact resQ_I_smul_eq_zero fun k => by
    rw [mFourierCoeff_ofCoeff_entry, mFourierCoeff_ofCoeff_entry, hA k p]

/-- **Real fields of a row-wise parity class**: `‖A‖² = 8 ‖A|_Q‖²`. -/
theorem norm_sq_of_mem_fix_real (ε : ℝ) (hε : ε * ε = 1) {A : L2M}
    (hA : A ∈ (rowMf ε hε).lift.fix) (hr : IsRealM A) : ‖A‖ ^ 2 = 8 * ‖resB A‖ ^ 2 := by
  rw [norm_sq_of_mem_fix ε hε hA, resB_I_smul_eq_zero hr, norm_zero]
  ring

/-- **A real field of a row-wise parity class is determined by its restriction to `Q`.** -/
theorem eq_of_resB_eq (ε : ℝ) (hε : ε * ε = 1) {A B : L2M}
    (hA : A ∈ (rowMf ε hε).lift.fix) (hB : B ∈ (rowMf ε hε).lift.fix)
    (hrA : IsRealM A) (hrB : IsRealM B) (h : resB A = resB B) : A = B := by
  have h0 := norm_sq_of_mem_fix_real ε hε (Submodule.sub_mem _ hA hB) (hrA.sub hrB)
  rw [map_sub, h, sub_self, norm_zero] at h0
  have : ‖A - B‖ = 0 := by nlinarith [norm_nonneg (A - B)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem entV_complex_smul (c : ℂ) (σ : L2V) (a : Fin 3) : entV a (c • σ) = c • entV a σ := by
  ext k; simp [entV_apply]

/-- **The norm of a field of the Dirichlet class** `ParV`. -/
theorem norm_sq_of_mem_ParV {σ : L2V} (hσ : σ ∈ ParV) :
    ‖σ‖ ^ 2 = 8 * (‖resBV σ‖ ^ 2 + ‖resBV ((-Complex.I) • σ)‖ ^ 2) := by
  have hp : ∀ a, ‖ofCoeff (entV a σ)‖ ^ 2 =
      8 * (‖resQ (ofCoeff (entV a σ))‖ ^ 2 + ‖resQ ((-Complex.I) • ofCoeff (entV a σ))‖ ^ 2) :=
    fun a => norm_sq_eq_eight (s := fun _ => -1) (fun _ => by simp) fun i k => by
      rw [mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff, entV_apply, entV_apply, hσ i k a]
      ring
  have hn : ‖σ‖ = ‖vectorFourier.symm σ‖ := (vectorFourier.symm.norm_map σ).symm
  rw [hn, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [vectorFourier_symm_apply, resBV_apply, resBV_apply, vectorFourier_symm_apply,
    vectorFourier_symm_apply]
  change ‖ofCoeff (entV a σ)‖ ^ 2 =
    8 * (‖resQ (ofCoeff (entV a σ))‖ ^ 2 + ‖resQ (ofCoeff (entV a ((-Complex.I) • σ)))‖ ^ 2)
  rw [hp a, entV_complex_smul, ofCoeff_smul]

theorem resBV_I_smul_eq_zero {σ : L2V} (hσ : IsRealV σ) : resBV ((-Complex.I) • σ) = 0 := by
  ext1 a
  rw [resBV_apply, vectorFourier_symm_apply]
  change resQ (ofCoeff (entV a ((-Complex.I) • σ))) = 0
  rw [entV_complex_smul, ofCoeff_smul]
  exact resQ_I_smul_eq_zero fun k => by
    rw [mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff, entV_apply, entV_apply, hσ k a]

theorem norm_sq_of_mem_ParV_real {σ : L2V} (hσ : σ ∈ ParV) (hr : IsRealV σ) :
    ‖σ‖ ^ 2 = 8 * ‖resBV σ‖ ^ 2 := by
  rw [norm_sq_of_mem_ParV hσ, resBV_I_smul_eq_zero hr, norm_zero]
  ring

theorem eq_of_resBV_eq {σ ρ : L2V} (hσ : σ ∈ ParV) (hρ : ρ ∈ ParV) (hrσ : IsRealV σ)
    (hrρ : IsRealV ρ) (h : resBV σ = resBV ρ) : σ = ρ := by
  have h0 := norm_sq_of_mem_ParV_real (Submodule.sub_mem _ hσ hρ) (hrσ.sub hrρ)
  rw [map_sub, h, sub_self, norm_zero] at h0
  have : ‖σ - ρ‖ = 0 := by nlinarith [norm_nonneg (σ - ρ)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end RealParity

/-! ## The identification -/

/-- **`H̊(curl, Q; ℝ³ˣ³)` is the real electric parity space**: restriction to `Q` is a bijection
from the real fields of `ParRow 1 ∩ H(curl, 𝕋³)` onto `H̊(curl, Q)`. -/
theorem bijOn_resB_HcurlZero :
    Set.BijOn resB {E : L2M | E ∈ ParRow 1 ∧ E ∈ Hcurl ∧ IsRealM E}
      (BoundedDomain.HcurlZero Qr) := by
  refine ⟨fun E hE => (resB_mem_HcurlZero hE.1 hE.2.1).1, fun E hE E' hE' h =>
    eq_of_resB_eq 1 one_mul_one' (mem_rowE_fix.2 hE.1) (mem_rowE_fix.2 hE'.1) hE.2.2 hE'.2.2 h,
    fun B hB => ?_⟩
  obtain ⟨E, hEc, hE1, hEr, hres, -⟩ := exists_ext_HcurlZero hB
  exact ⟨E, ⟨hE1, hEc, hEr⟩, hres⟩

/-- **The identification intertwines the curls and scales the graph norms by `8`**: for a real
`E ∈ ParRow 1 ∩ H(curl, 𝕋³)`, `curl (E|_Q) = (curl E)|_Q` in `H̊(curl, Q)`, `‖E‖² = 8 ‖E|_Q‖²`
and `‖curl E‖² = 8 ‖(curl E)|_Q‖²`. -/
theorem resB_curl_identification {E : L2M} (hE : E ∈ ParRow 1) (hc : E ∈ Hcurl)
    (hr : IsRealM E) :
    ∃ h : resB E ∈ BoundedDomain.HcurlZero Qr,
      BoundedDomain.curlClosure ⟨resB E, BoundedDomain.mem_domain_curlClosure.2 h⟩ =
        resB (curlT ⟨E, hc⟩) ∧
      ‖E‖ ^ 2 = 8 * ‖resB E‖ ^ 2 ∧ ‖curlT ⟨E, hc⟩‖ ^ 2 = 8 * ‖resB (curlT ⟨E, hc⟩)‖ ^ 2 := by
  obtain ⟨h, e⟩ := resB_mem_HcurlZero hE hc
  have hB : curlT ⟨E, hc⟩ ∈ (rowMf (-1) neg_one_mul_neg_one').lift.fix :=
    intertwines_curl_row.mem_fix ⟨E, hc⟩ (mem_rowE_fix.2 hE)
  exact ⟨h, e, norm_sq_of_mem_fix_real 1 one_mul_one' (mem_rowE_fix.2 hE) hr,
    norm_sq_of_mem_fix_real (-1) neg_one_mul_neg_one' hB (isRealM_curlT hc hr)⟩

/-- **`H̊¹(Q; ℝ³)` is the real Dirichlet parity space**: restriction to `Q` is a bijection from the
real fields of `ParV ∩ H¹(𝕋³)` onto `H̊¹(Q)`. -/
theorem bijOn_resBV_H1Zero :
    Set.BijOn resBV {σ : L2V | σ ∈ ParV ∧ σ ∈ gradT.domain ∧ IsRealV σ}
      ((BoundedDomain.gradClosure (Ω := Qr)).domain : Set (BoundedDomain.L2V Qr)) := by
  refine ⟨fun σ hσ => (resBV_mem_H1Zero hσ.1 hσ.2.1).1, fun σ hσ ρ hρ h =>
    eq_of_resBV_eq hσ.1 hρ.1 hσ.2.2 hρ.2.2 h, fun u hu => ?_⟩
  obtain ⟨σ, hσg, hσ1, hσr, hres, -⟩ := exists_extV_H1Zero ⟨u, hu⟩
  exact ⟨σ, ⟨hσ1, hσg, hσr⟩, hres⟩

/-- **The identification intertwines the gradients and scales the graph norms by `8`.** -/
theorem resBV_grad_identification {σ : L2V} (hσ : σ ∈ ParV) (hg : σ ∈ gradT.domain)
    (hr : IsRealV σ) :
    ∃ h : resBV σ ∈ (BoundedDomain.gradClosure (Ω := Qr)).domain,
      BoundedDomain.gradClosure ⟨resBV σ, h⟩ = resB (gradT ⟨σ, hg⟩) ∧
      ‖σ‖ ^ 2 = 8 * ‖resBV σ‖ ^ 2 ∧ ‖gradT ⟨σ, hg⟩‖ ^ 2 = 8 * ‖resB (gradT ⟨σ, hg⟩)‖ ^ 2 := by
  obtain ⟨h, e⟩ := resBV_mem_H1Zero hσ hg
  have hE : gradT ⟨σ, hg⟩ ∈ (rowMf 1 one_mul_one').lift.fix :=
    intertwines_grad_row.mem_fix ⟨σ, hg⟩ (mem_rowV_fix.2 hσ)
  exact ⟨h, e, norm_sq_of_mem_ParV_real hσ hr,
    norm_sq_of_mem_fix_real 1 one_mul_one' hE (isRealM_gradT hg hr)⟩


/-! ## The `L²` spaces -/

/-- Test fields are dense in `L²(Q; ℝ³ˣ³)`. -/
theorem mem_closure_testFields (B : BoundedDomain.L2M Qr) :
    B ∈ closure {B' | ∃ Φ : Ix → R3 → ℝ, ∃ hΦ : ∀ ij, IsTest Qr (Φ ij),
      BoundedDomain.testField hΦ = B'} := by
  set T := {B' | ∃ Φ : Ix → R3 → ℝ, ∃ hΦ : ∀ ij, IsTest Qr (Φ ij),
      BoundedDomain.testField hΦ = B'}
  have hsub : (BoundedDomain.HcurlZero Qr) ⊆ closure T := by
    rintro B' ⟨C, hC⟩
    have h1 : Prod.fst '' BoundedDomain.curlGraph Qr ⊆ T := by
      rintro _ ⟨⟨u, c⟩, ⟨Φ, hΦ, hp⟩, rfl⟩
      exact ⟨Φ, hΦ, (BoundedDomain.eq_of_mem_curlGraph hΦ hp).1.symm⟩
    exact closure_mono h1 (image_closure_subset_closure_image continuous_fst ⟨_, hC, rfl⟩)
  have hd := BoundedDomain.dense_domain_curlClosure isOpen_Qr isBounded_Qr
  have he : ((BoundedDomain.curlClosure (Ω := Qr)).domain : Set (BoundedDomain.L2M Qr)) =
      BoundedDomain.HcurlZero Qr := by
    ext u; exact BoundedDomain.mem_domain_curlClosure
  rw [he] at hd
  exact closure_minimal hsub isClosed_closure (hd B)

/-- Test fields are dense in `L²(Q; ℝ³)`. -/
theorem mem_closure_testFieldsV (u : BoundedDomain.L2V Qr) :
    u ∈ closure {u' | ∃ φ : Fin 3 → R3 → ℝ, ∃ hφ : ∀ i, IsTest Qr (φ i),
      BoundedDomain.testFieldV hφ = u'} := by
  set T := {u' | ∃ φ : Fin 3 → R3 → ℝ, ∃ hφ : ∀ i, IsTest Qr (φ i),
      BoundedDomain.testFieldV hφ = u'}
  have hsub : ((BoundedDomain.gradClosure (Ω := Qr)).domain : Set (BoundedDomain.L2V Qr)) ⊆
      closure T := by
    intro v hv
    have hC := BoundedDomain.mem_closure_gradClosure isOpen_Qr isBounded_Qr ⟨v, hv⟩
    have h1 : Prod.fst '' BoundedDomain.gradGraph Qr ⊆ T := by
      rintro _ ⟨⟨w, G⟩, ⟨φ, hφ, hp1, hp2⟩, rfl⟩
      exact ⟨φ, hφ, (BoundedDomain.eq_of_mem_gradGraph hφ hp1 hp2).1.symm⟩
    exact closure_mono h1 (image_closure_subset_closure_image continuous_fst ⟨_, hC, rfl⟩)
  exact closure_minimal hsub isClosed_closure
    (BoundedDomain.dense_domain_gradClosure isOpen_Qr isBounded_Qr u)

/-- **Every `L²(Q; ℝ³ˣ³)` field has a real extension in each row-wise parity class**, with
`‖E‖² = 8 ‖B‖²`. -/
theorem exists_extL2 (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) :
    ∃ E : L2M, E ∈ (rowMf ε hε).lift.fix ∧ IsRealM E ∧ resB E = B ∧ ‖E‖ ^ 2 = 8 * ‖B‖ ^ 2 := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (mem_closure_testFields B)
  choose Φ hΦ hu' using hu
  set e : ℕ → L2M := fun n => extF ε hε (hΦ n)
  have he : CauchySeq e := cauchySeq_of_dist_le (Real.sqrt_nonneg 8) hlim.cauchySeq
    fun n m => by rw [dist_extF, hu', hu']
  obtain ⟨E, hE⟩ := cauchySeq_tendsto_of_complete he
  refine ⟨E, (rowMf ε hε).lift.isClosed_fix.mem_of_tendsto hE
      (Eventually.of_forall fun n => extF_mem_fix ε hε (hΦ n)),
    isClosed_isRealM.mem_of_tendsto hE (Eventually.of_forall fun n => isRealM_extF ε hε (hΦ n)),
    ?_, ?_⟩
  · refine tendsto_nhds_unique ((resB.continuous.tendsto _).comp hE) (hlim.congr fun n => ?_)
    simp only [Function.comp_apply, e, resB_extF, hu']
  · refine tendsto_nhds_unique (((continuous_norm.pow 2).tendsto _).comp hE) ?_
    refine (((continuous_norm.pow 2).const_mul 8).tendsto _).comp hlim |>.congr fun n => ?_
    change 8 * ‖u n‖ ^ 2 = ‖e n‖ ^ 2
    rw [norm_sq_extF, hu']

/-- **Every `L²(Q; ℝ³)` field has a real extension in the Dirichlet class `ParV`.** -/
theorem exists_extL2V (u : BoundedDomain.L2V Qr) :
    ∃ σ : L2V, σ ∈ ParV ∧ IsRealV σ ∧ resBV σ = u ∧ ‖σ‖ ^ 2 = 8 * ‖u‖ ^ 2 := by
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.1 (mem_closure_testFieldsV u)
  choose φ hφ hw' using hw
  set e : ℕ → L2V := fun n => extV (hφ n)
  have he : CauchySeq e := cauchySeq_of_dist_le (Real.sqrt_nonneg 8) hlim.cauchySeq
    fun n m => by rw [dist_extV, hw', hw']
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete he
  refine ⟨S, isClosed_ParV.mem_of_tendsto hS (Eventually.of_forall fun n => extV_mem_ParV (hφ n)),
    isClosed_isRealV.mem_of_tendsto hS (Eventually.of_forall fun n => isRealV_extV (hφ n)),
    ?_, ?_⟩
  · refine tendsto_nhds_unique ((resBV.continuous.tendsto _).comp hS) (hlim.congr fun n => ?_)
    simp only [Function.comp_apply, e, resBV_extV, hw']
  · refine tendsto_nhds_unique (((continuous_norm.pow 2).tendsto _).comp hS) ?_
    refine (((continuous_norm.pow 2).const_mul 8).tendsto _).comp hlim |>.congr fun n => ?_
    change 8 * ‖w n‖ ^ 2 = ‖e n‖ ^ 2
    rw [norm_sq_extV, hw']

/-- **`L²(Q; ℝ³ˣ³)` is the real part of each row-wise parity class** (`ε = 1`: `ParRow 1`,
`ε = -1`: `ParRow (-1)`): restriction is a bijection, with `‖E‖² = 8 ‖E|_Q‖²`. -/
theorem bijOn_resB_L2 (ε : ℝ) (hε : ε * ε = 1) :
    Set.BijOn resB {E : L2M | E ∈ (rowMf ε hε).lift.fix ∧ IsRealM E} univ := by
  refine ⟨fun _ _ => mem_univ _, fun E hE E' hE' h =>
    eq_of_resB_eq ε hε hE.1 hE'.1 hE.2 hE'.2 h, fun B _ => ?_⟩
  obtain ⟨E, h1, h2, h3, -⟩ := exists_extL2 ε hε B
  exact ⟨E, ⟨h1, h2⟩, h3⟩

/-- **`L²(Q; ℝ³)` is the real part of the Dirichlet class `ParV`.** -/
theorem bijOn_resBV_L2 : Set.BijOn resBV {σ : L2V | σ ∈ ParV ∧ IsRealV σ} univ := by
  refine ⟨fun _ _ => mem_univ _, fun σ hσ ρ hρ h =>
    eq_of_resBV_eq hσ.1 hρ.1 hσ.2 hρ.2 h, fun u _ => ?_⟩
  obtain ⟨σ, h1, h2, h3, -⟩ := exists_extL2V u
  exact ⟨σ, ⟨h1, h2⟩, h3⟩


/-! ## The extension operators -/

section ExtOp

theorem IsRealM.add {A B : L2M} (hA : IsRealM A) (hB : IsRealM B) : IsRealM (A + B) :=
  fun k p => by simp [hA k p, hB k p]

theorem IsRealM.smul {A : L2M} (hA : IsRealM A) (c : ℝ) : IsRealM (c • A) :=
  fun k p => by simp [hA k p, Complex.real_smul]

theorem IsRealV.add {σ ρ : L2V} (hσ : IsRealV σ) (hρ : IsRealV ρ) : IsRealV (σ + ρ) :=
  fun k a => by simp [hσ k a, hρ k a]

theorem IsRealV.smul {σ : L2V} (hσ : IsRealV σ) (c : ℝ) : IsRealV (c • σ) :=
  fun k a => by simp [hσ k a, Complex.real_smul]

variable (ε : ℝ) (hε : ε * ε = 1)

/-- The real parity extension of a field of `L²(Q; ℝ³ˣ³)` in the class of `rowMf ε`. -/
def extM (B : BoundedDomain.L2M Qr) : L2M := (exists_extL2 ε hε B).choose

theorem extM_mem_fix (B : BoundedDomain.L2M Qr) : extM ε hε B ∈ (rowMf ε hε).lift.fix :=
  (exists_extL2 ε hε B).choose_spec.1

theorem isRealM_extM (B : BoundedDomain.L2M Qr) : IsRealM (extM ε hε B) :=
  (exists_extL2 ε hε B).choose_spec.2.1

theorem resB_extM (B : BoundedDomain.L2M Qr) : resB (extM ε hε B) = B :=
  (exists_extL2 ε hε B).choose_spec.2.2.1

theorem norm_sq_extM (B : BoundedDomain.L2M Qr) : ‖extM ε hε B‖ ^ 2 = 8 * ‖B‖ ^ 2 :=
  (exists_extL2 ε hε B).choose_spec.2.2.2

/-- A real parity field is the extension of its restriction. -/
theorem extM_resB {E : L2M} (hE : E ∈ (rowMf ε hε).lift.fix) (hr : IsRealM E) :
    extM ε hε (resB E) = E :=
  eq_of_resB_eq ε hε (extM_mem_fix ε hε _) hE (isRealM_extM ε hε _) hr (resB_extM ε hε _)

theorem extM_add (B B' : BoundedDomain.L2M Qr) :
    extM ε hε (B + B') = extM ε hε B + extM ε hε B' := by
  have h := extM_resB ε hε (Submodule.add_mem _ (extM_mem_fix ε hε B) (extM_mem_fix ε hε B'))
    ((isRealM_extM ε hε B).add (isRealM_extM ε hε B'))
  rw [map_add, resB_extM, resB_extM] at h
  exact h

theorem extM_smul (c : ℝ) (B : BoundedDomain.L2M Qr) : extM ε hε (c • B) = c • extM ε hε B := by
  have h := extM_resB ε hε (Submodule.smul_mem _ c (extM_mem_fix ε hε B))
    ((isRealM_extM ε hε B).smul c)
  rw [map_smul, resB_extM] at h
  exact h

/-- **The extension operator** `L²(Q; ℝ³ˣ³) → (rowMf ε).lift.fix`, `‖ext B‖ = √8 ‖B‖`. -/
def extML : BoundedDomain.L2M Qr →L[ℝ] L2M :=
  LinearMap.mkContinuous ⟨⟨extM ε hε, extM_add ε hε⟩, extM_smul ε hε⟩ (Real.sqrt 8) fun B => by
    change ‖extM ε hε B‖ ≤ _
    rw [← Real.sqrt_sq (norm_nonneg (extM ε hε B)), norm_sq_extM, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (norm_nonneg _)]

@[simp] theorem extML_apply (B : BoundedDomain.L2M Qr) : extML ε hε B = extM ε hε B := rfl

/-- The extension multiplies inner products by `8`. -/
theorem inner_extML (B B' : BoundedDomain.L2M Qr) :
    ⟪extML ε hε B, extML ε hε B'⟫_ℝ = 8 * ⟪B, B'⟫_ℝ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (B : _),
    ← map_add]
  simp only [extML_apply, ← sq, norm_sq_extM]
  ring

/-- The real Dirichlet extension of a field of `L²(Q; ℝ³)`. -/
def extVf (u : BoundedDomain.L2V Qr) : L2V := (exists_extL2V u).choose

theorem extVf_mem (u : BoundedDomain.L2V Qr) : extVf u ∈ ParV := (exists_extL2V u).choose_spec.1

theorem isRealV_extVf (u : BoundedDomain.L2V Qr) : IsRealV (extVf u) :=
  (exists_extL2V u).choose_spec.2.1

theorem resBV_extVf (u : BoundedDomain.L2V Qr) : resBV (extVf u) = u :=
  (exists_extL2V u).choose_spec.2.2.1

theorem norm_sq_extVf (u : BoundedDomain.L2V Qr) : ‖extVf u‖ ^ 2 = 8 * ‖u‖ ^ 2 :=
  (exists_extL2V u).choose_spec.2.2.2

theorem extVf_resBV {σ : L2V} (hσ : σ ∈ ParV) (hr : IsRealV σ) : extVf (resBV σ) = σ :=
  eq_of_resBV_eq (extVf_mem _) hσ (isRealV_extVf _) hr (resBV_extVf _)

theorem extVf_add (u u' : BoundedDomain.L2V Qr) : extVf (u + u') = extVf u + extVf u' := by
  have h := extVf_resBV (Submodule.add_mem _ (extVf_mem u) (extVf_mem u'))
    ((isRealV_extVf u).add (isRealV_extVf u'))
  rw [map_add, resBV_extVf, resBV_extVf] at h
  exact h

theorem extVf_smul (c : ℝ) (u : BoundedDomain.L2V Qr) : extVf (c • u) = c • extVf u := by
  have h := extVf_resBV (Submodule.smul_mem _ c (extVf_mem u)) ((isRealV_extVf u).smul c)
  rw [map_smul, resBV_extVf] at h
  exact h

/-- **The extension operator** `L²(Q; ℝ³) → ParV`. -/
def extVL : BoundedDomain.L2V Qr →L[ℝ] L2V :=
  LinearMap.mkContinuous ⟨⟨extVf, extVf_add⟩, extVf_smul⟩ (Real.sqrt 8) fun u => by
    change ‖extVf u‖ ≤ _
    rw [← Real.sqrt_sq (norm_nonneg (extVf u)), norm_sq_extVf, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (norm_nonneg _)]

@[simp] theorem extVL_apply (u : BoundedDomain.L2V Qr) : extVL u = extVf u := rfl

theorem inner_extVL (u u' : BoundedDomain.L2V Qr) :
    ⟪extVL u, extVL u'⟫_ℝ = 8 * ⟪u, u'⟫_ℝ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (u : _),
    ← map_add]
  simp only [extVL_apply, ← sq, norm_sq_extVf]
  ring

/-- **The extension intertwines the curls on `H̊(curl, Q)`**: `ext B ∈ H(curl, 𝕋³)` and
`curl (ext B) = ext (curl B)`. -/
theorem extML_curl {B : BoundedDomain.L2M Qr} (hB : B ∈ BoundedDomain.HcurlZero Qr) :
    ∃ h : extML 1 one_mul_one' B ∈ Hcurl, curlT ⟨_, h⟩ = extML (-1) neg_one_mul_neg_one'
      (BoundedDomain.curlClosure ⟨B, BoundedDomain.mem_domain_curlClosure.2 hB⟩) := by
  obtain ⟨E, hEc, hE1, hEr, hres, hcurl, -⟩ := exists_ext_HcurlZero hB
  have hE : extML 1 one_mul_one' B = E := by
    rw [extML_apply, ← hres]; exact extM_resB 1 one_mul_one' (mem_rowE_fix.2 hE1) hEr
  have hB2 : curlT ⟨E, hEc⟩ ∈ (rowMf (-1) neg_one_mul_neg_one').lift.fix :=
    intertwines_curl_row.mem_fix ⟨E, hEc⟩ (mem_rowE_fix.2 hE1)
  have key : ∀ (y : L2M) (hy : y = E) (h : y ∈ Hcurl), curlT ⟨y, h⟩ = curlT ⟨E, hEc⟩ := by
    rintro y rfl h; rfl
  refine ⟨hE ▸ hEc, ?_⟩
  rw [key _ hE, ← hcurl, extML_apply, extM_resB _ _ hB2 (isRealM_curlT hEc hEr)]

/-- **The extension intertwines the gradients on `H̊¹(Q)`.** -/
theorem extVL_grad (u : (BoundedDomain.gradClosure (Ω := Qr)).domain) :
    ∃ h : extVL u ∈ gradT.domain,
      gradT ⟨_, h⟩ = extML 1 one_mul_one' (BoundedDomain.gradClosure u) := by
  obtain ⟨σ, hσg, hσ1, hσr, hres, hgrad, -⟩ := exists_extV_H1Zero u
  have hE : extVL (u : BoundedDomain.L2V Qr) = σ := by
    rw [extVL_apply, ← hres]; exact extVf_resBV hσ1 hσr
  have hG : gradT ⟨σ, hσg⟩ ∈ (rowMf 1 one_mul_one').lift.fix :=
    intertwines_grad_row.mem_fix ⟨σ, hσg⟩ (mem_rowV_fix.2 hσ1)
  have key : ∀ (y : L2V) (hy : y = σ) (h : y ∈ gradT.domain), gradT ⟨y, h⟩ = gradT ⟨σ, hσg⟩ := by
    rintro y rfl h; rfl
  refine ⟨hE ▸ hσg, ?_⟩
  rw [key _ hE, ← hgrad, extML_apply, extM_resB _ _ hG (isRealM_gradT hσg hσr)]

end ExtOp

/-! ## Complex conjugation on the box model -/

section Conj

/-- `‖conj M‖ = ‖M‖`. -/
theorem norm_conjM (M : Mat3) : ‖conjM M‖ = ‖M‖ := by
  have h : ‖conjM M‖ ^ 2 = ‖M‖ ^ 2 := by
    rw [norm_sq_mat, norm_sq_mat]; simp [conjM_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- Entrywise conjugation of `ℂ³`. -/
def conjVec (u : Vec3) : Vec3 := WithLp.toLp 2 fun a => conj (u a)

@[simp] theorem conjVec_apply (u : Vec3) (a : Fin 3) : conjVec u a = conj (u a) := rfl

theorem norm_conjVec (u : Vec3) : ‖conjVec u‖ = ‖u‖ := by
  have h : ‖conjVec u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_vec, norm_sq_vec]; simp
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem memℓp_cjM (A : L2M) : Memℓp (fun k => conjM (A (-k))) 2 := by
  rw [memℓp_two_iff]
  simp_rw [norm_conjM]
  exact (Equiv.neg Z3).summable_iff.2 (summable_norm_sq_L2 A)

theorem memℓp_cjV (σ : L2V) : Memℓp (fun k => conjVec (σ (-k))) 2 := by
  rw [memℓp_two_iff]
  simp_rw [norm_conjVec]
  exact (Equiv.neg Z3).summable_iff.2 (summable_norm_sq_L2 σ)

/-- **Complex conjugation** of matrix fields on the Fourier side: `(C A)(k) = conj A(-k)`. -/
def cjM : L2M →L[ℝ] L2M :=
  LinearMap.mkContinuous
    { toFun := fun A => ⟨fun k => conjM (A (-k)), memℓp_cjM A⟩
      map_add' := fun A B => by ext k p; simp; rfl
      map_smul' := fun r A => by ext k p; simp [Complex.real_smul] }
    1 fun A => by
      rw [one_mul]
      refine le_of_eq ?_
      have h1 := norm_sq_L2 (⟨fun k => conjM (A (-k)), memℓp_cjM A⟩ : L2M)
      have h2 := norm_sq_L2 A
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h1, h2]
      simp_rw [norm_conjM]
      exact (Equiv.neg Z3).tsum_eq fun k => ‖A k‖ ^ 2

@[simp] theorem cjM_apply (A : L2M) (k : Z3) : cjM A k = conjM (A (-k)) := rfl

/-- **Complex conjugation** of vector fields on the Fourier side. -/
def cjV : L2V →L[ℝ] L2V :=
  LinearMap.mkContinuous
    { toFun := fun σ => ⟨fun k => conjVec (σ (-k)), memℓp_cjV σ⟩
      map_add' := fun σ ρ => by ext k a; simp; rfl
      map_smul' := fun r σ => by ext k a; simp [Complex.real_smul] }
    1 fun σ => by
      rw [one_mul]
      refine le_of_eq ?_
      have h1 := norm_sq_L2 (⟨fun k => conjVec (σ (-k)), memℓp_cjV σ⟩ : L2V)
      have h2 := norm_sq_L2 σ
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h1, h2]
      simp_rw [norm_conjVec]
      exact (Equiv.neg Z3).tsum_eq fun k => ‖σ k‖ ^ 2

@[simp] theorem cjV_apply (σ : L2V) (k : Z3) : cjV σ k = conjVec (σ (-k)) := rfl

theorem inner_cjM (A B : L2M) : ⟪cjM A, B⟫_ℝ = ⟪A, cjM B⟫_ℝ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have e : ∀ k, ⟪cjM A k, B k⟫_ℝ = ⟪A (-k), cjM B (-k)⟫_ℝ := fun k => by
    simp only [cjM_apply, neg_neg]; exact inner_conjM _ _
  simp_rw [e]
  exact (Equiv.neg Z3).tsum_eq fun k => ⟪A k, cjM B k⟫_ℝ

theorem inner_cjV (σ ρ : L2V) : ⟪cjV σ, ρ⟫_ℝ = ⟪σ, cjV ρ⟫_ℝ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have e : ∀ k, ⟪cjV σ k, ρ k⟫_ℝ = ⟪σ (-k), cjV ρ (-k)⟫_ℝ := fun k => by
    simp only [cjV_apply, neg_neg, inner_vec, conjVec_apply, Complex.conj_re, Complex.conj_im]
    congr 1; funext a; ring
  simp_rw [e]
  exact (Equiv.neg Z3).tsum_eq fun k => ⟪σ k, cjV ρ k⟫_ℝ

theorem cjM_cjM (A : L2M) : cjM (cjM A) = A := by
  ext k ⟨a, b⟩; simp [conjM_apply]

theorem cjV_cjV (σ : L2V) : cjV (cjV σ) = σ := by
  ext k a; simp

theorem isRealM_iff_cjM (A : L2M) : IsRealM A ↔ cjM A = A := by
  constructor
  · intro h; ext k p
    simp only [cjM_apply]
    obtain ⟨a, b⟩ := p
    rw [conjM_apply, h k (a, b)]; simp
  · intro h k p
    have := congrArg (fun B : L2M => B (-k) p) h
    simp only [cjM_apply, neg_neg] at this
    obtain ⟨a, b⟩ := p
    rw [conjM_apply] at this
    rw [← this]

theorem isRealV_iff_cjV (σ : L2V) : IsRealV σ ↔ cjV σ = σ := by
  constructor
  · intro h; ext k a
    simp only [cjV_apply, conjVec_apply]
    rw [h k a]; simp
  · intro h k a
    have := congrArg (fun ρ : L2V => ρ (-k) a) h
    simp only [cjV_apply, conjVec_apply, neg_neg] at this
    rw [← this]

/-- For a real `F`, `⟪F, C A⟫ = ⟪F, A⟫`. -/
theorem inner_cjM_of_real {F : L2M} (hF : IsRealM F) (A : L2M) : ⟪F, cjM A⟫_ℝ = ⟪F, A⟫_ℝ := by
  rw [← inner_cjM, (isRealM_iff_cjM F).1 hF]

theorem inner_cjV_of_real {F : L2V} (hF : IsRealV F) (σ : L2V) : ⟪F, cjV σ⟫_ℝ = ⟪F, σ⟫_ℝ := by
  rw [← inner_cjV, (isRealV_iff_cjV F).1 hF]

theorem cjM_mem_fix (ε : ℝ) (hε : ε * ε = 1) {A : L2M} (hA : A ∈ (rowMf ε hε).lift.fix) :
    cjM A ∈ (rowMf ε hε).lift.fix := fun i => by
  ext k ⟨a, b⟩
  have h := congrArg (fun B : L2M => B (-k) (a, b)) (hA i)
  change rowSgn (ε : ℂ) i (A (Box.refl i (-k))) (a, b) = A (-k) (a, b) at h
  change rowSgn (ε : ℂ) i (cjM A (Box.refl i k)) (a, b) = cjM A k (a, b)
  rw [rowSgn_apply] at h ⊢
  rw [cjM_apply, cjM_apply, conjM_apply, conjM_apply, ← refl_neg', ← h, colSign_eq]
  simp

theorem cjV_mem_ParV {σ : L2V} (hσ : σ ∈ ParV) : cjV σ ∈ ParV := fun i k a => by
  simp only [cjV_apply, conjVec_apply]
  rw [← refl_neg', hσ i (-k) a, map_neg]

theorem curlSym_conjM (k : Z3) (M : Mat3) :
    curlSym (freq (-k)) (conjM M) = conjM (curlSym (freq k) M) := by
  rw [freq_neg]
  ext ⟨a, b⟩
  fin_cases b <;> simp [curlSym_apply, jM_apply, curlR_apply, cross, conjM_apply] <;> ring

theorem gradSym_conjVec (k : Z3) (u : Vec3) :
    gradSym (freq (-k)) (conjVec u) = conjM (gradSym (freq k) u) := by
  rw [freq_neg]
  ext ⟨a, b⟩
  simp [gradSym_apply, conjM_apply]

theorem cjM_mem_Hcurl {A : L2M} (hA : A ∈ Hcurl) :
    ∃ h : cjM A ∈ Hcurl, curlT ⟨cjM A, h⟩ = cjM (curlT ⟨A, hA⟩) := by
  have e : (fun k => curlSym (freq k) (cjM A k)) = ⇑(cjM (curlT ⟨A, hA⟩)) := by
    funext k
    rw [cjM_apply, cjM_apply, show k = -(-k) from (neg_neg k).symm, curlSym_conjM, neg_neg]
    rfl
  have h : cjM A ∈ Hcurl := by
    change Memℓp _ 2
    rw [e]; exact lp.memℓp _
  exact ⟨h, lp.ext e⟩

theorem cjV_mem_gradT_domain {σ : L2V} (hσ : σ ∈ gradT.domain) :
    ∃ h : cjV σ ∈ gradT.domain, gradT ⟨cjV σ, h⟩ = cjM (gradT ⟨σ, hσ⟩) := by
  have e : (fun k => gradSym (freq k) (cjV σ k)) = ⇑(cjM (gradT ⟨σ, hσ⟩)) := by
    funext k
    rw [cjV_apply, cjM_apply, show k = -(-k) from (neg_neg k).symm, gradSym_conjVec, neg_neg]
    rfl
  have h : cjV σ ∈ gradT.domain := by
    change Memℓp _ 2
    rw [e]; exact lp.memℓp _
  exact ⟨h, lp.ext e⟩

end Conj

/-! ## The adjoints: extension of `H(curl, Q)` and `H(div, Q)` -/

section Adjoint

open scoped LinearPMap

/-- The thesis' complex on `Q`. -/
abbrev cxQ : HilbertComplex2 (BoundedDomain.L2V Qr) (BoundedDomain.L2M Qr) (BoundedDomain.L2M Qr) :=
  BoundedDomain.thesisComplex isOpen_Qr isBounded_Qr

/-- **Magnetic extension of `H(curl, Q) = D(d1*)`**: for `B ∈ D(d1*)` (a field with a weak curl,
no boundary condition), the magnetic-parity extension lies in `D(curl*) = H(curl, 𝕋³)`, with
`curl* (ext B) = ext (d1* B)`. The proof tests against `x ∈ H(curl, 𝕋³)`, reduces to the real
electric part of `x` by the parity projections and complex conjugation, and identifies that
part with an element of `H̊(curl, Q)`. -/
theorem extML_adj_curl {B : BoundedDomain.L2M Qr} (hB : B ∈ cxQ.d1†.domain) :
    ∃ h : extML (-1) neg_one_mul_neg_one' B ∈ curlT†.domain,
      curlT† ⟨_, h⟩ = extML 1 one_mul_one' (cxQ.d1† ⟨B, hB⟩) := by
  set F := extML (-1) neg_one_mul_neg_one' B
  set G := extML 1 one_mul_one' (cxQ.d1† ⟨B, hB⟩)
  have hFr : IsRealM F := isRealM_extM _ _ B
  have hGr : IsRealM G := isRealM_extM _ _ _
  have hFf : F ∈ rowB.fix := extM_mem_fix _ _ B
  have hGf : G ∈ rowE.fix := extM_mem_fix _ _ _
  have key : ∀ x : curlT.domain, ⟪G, (x : L2M)⟫_ℝ = ⟪F, curlT x⟫_ℝ := by
    intro x
    obtain ⟨hy, ey⟩ := intertwines_curl_row.avg x
    set y : L2M := rowE.avg x
    have e1 : ⟪G, (x : L2M)⟫_ℝ = ⟪G, y⟫_ℝ := by
      rw [← rowE.inner_avg, rowE.avg_of_mem hGf]
    have e2 : ⟪F, curlT x⟫_ℝ = ⟪F, curlT ⟨y, hy⟩⟫_ℝ := by
      change ⟪F, curlT x⟫_ℝ = ⟪F, periodicComplex.d1 ⟨y, hy⟩⟫_ℝ
      rw [ey, ← rowB.inner_avg, rowB.avg_of_mem hFf]
      rfl
    obtain ⟨hcy, ecy⟩ := cjM_mem_Hcurl hy
    set yr : L2M := (1 / 2 : ℝ) • (y + cjM y)
    have hyr : yr ∈ Hcurl := Submodule.smul_mem _ _ (Submodule.add_mem _ hy hcy)
    have ecyr : curlT ⟨yr, hyr⟩ = (1 / 2 : ℝ) • (curlT ⟨y, hy⟩ + cjM (curlT ⟨y, hy⟩)) := by
      rw [← ecy, ← LinearPMap.map_add, ← LinearPMap.map_smul]; rfl
    have hyfix : y ∈ rowE.fix := rowE.avg_mem x
    have hyrf : yr ∈ rowE.fix :=
      Submodule.smul_mem _ _ (Submodule.add_mem _ hyfix (cjM_mem_fix 1 one_mul_one' hyfix))
    have hyrr : IsRealM yr := by
      rw [isRealM_iff_cjM]
      simp only [yr, map_smul, map_add, cjM_cjM, add_comm]
    have e3 : ⟪G, y⟫_ℝ = ⟪G, yr⟫_ℝ := by
      simp only [yr, real_inner_smul_right, inner_add_right, inner_cjM_of_real hGr]; ring
    have e4 : ⟪F, curlT ⟨y, hy⟩⟫_ℝ = ⟪F, curlT ⟨yr, hyr⟩⟫_ℝ := by
      rw [ecyr]
      simp only [real_inner_smul_right, inner_add_right, inner_cjM_of_real hFr]; ring
    -- the real electric part is the extension of an element of `H̊(curl, Q)`
    obtain ⟨hb, eb, -, -⟩ := resB_curl_identification (mem_rowE_fix.1 hyrf) hyr hyrr
    set b := resB yr
    have hyrb : extML 1 one_mul_one' b = yr := extM_resB 1 one_mul_one' hyrf hyrr
    have hcB : curlT ⟨yr, hyr⟩ ∈ rowB.fix :=
      intertwines_curl_row.mem_fix ⟨yr, hyr⟩ hyrf
    have hcb : extML (-1) neg_one_mul_neg_one'
        (BoundedDomain.curlClosure ⟨b, BoundedDomain.mem_domain_curlClosure.2 hb⟩) =
          curlT ⟨yr, hyr⟩ := by
      rw [eb]; exact extM_resB _ _ hcB (isRealM_curlT hyr hyrr)
    have hfa := LinearPMap.adjoint_isFormalAdjoint cxQ.dense1 ⟨B, hB⟩
      ⟨b, BoundedDomain.mem_domain_curlClosure.2 hb⟩
    rw [e1, e3, e2, e4, ← hcb]
    conv_lhs => rw [← hyrb]
    rw [inner_extML, inner_extML]
    exact congrArg (8 * ·) hfa
  have hmem := LinearPMap.mem_adjoint_domain_of_exists (T := curlT) F ⟨G, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_mulDomain _) ⟨F, hmem⟩ key⟩

/-- **Electric extension of `H(div, Q) = D(d0*)`**: for `A ∈ D(d0*)`, the electric-parity
extension lies in `D(grad*)` of the periodic complex, with `grad* (ext A) = ext (d0* A)`. -/
theorem extML_adj_div {A : BoundedDomain.L2M Qr} (hA : A ∈ cxQ.d0†.domain) :
    ∃ h : extML 1 one_mul_one' A ∈ gradT†.domain,
      gradT† ⟨_, h⟩ = extVL (cxQ.d0† ⟨A, hA⟩) := by
  set F := extML 1 one_mul_one' A
  set G := extVL (cxQ.d0† ⟨A, hA⟩)
  have hFr : IsRealM F := isRealM_extM _ _ A
  have hGr : IsRealV G := isRealV_extVf _
  have hFf : F ∈ rowE.fix := extM_mem_fix _ _ A
  have hGf : G ∈ rowV.fix := mem_rowV_fix.2 (extVf_mem _)
  have key : ∀ x : gradT.domain, ⟪G, (x : L2V)⟫_ℝ = ⟪F, gradT x⟫_ℝ := by
    intro x
    obtain ⟨hy, ey⟩ := intertwines_grad_row.avg x
    set y : L2V := rowV.avg x
    have e1 : ⟪G, (x : L2V)⟫_ℝ = ⟪G, y⟫_ℝ := by
      rw [← rowV.inner_avg, rowV.avg_of_mem hGf]
    have e2 : ⟪F, gradT x⟫_ℝ = ⟪F, gradT ⟨y, hy⟩⟫_ℝ := by
      change ⟪F, gradT x⟫_ℝ = ⟪F, periodicComplex.d0 ⟨y, hy⟩⟫_ℝ
      rw [ey, ← rowE.inner_avg, rowE.avg_of_mem hFf]
      rfl
    obtain ⟨hcy, ecy⟩ := cjV_mem_gradT_domain hy
    set yr : L2V := (1 / 2 : ℝ) • (y + cjV y)
    have hyr : yr ∈ gradT.domain := Submodule.smul_mem _ _ (Submodule.add_mem _ hy hcy)
    have ecyr : gradT ⟨yr, hyr⟩ = (1 / 2 : ℝ) • (gradT ⟨y, hy⟩ + cjM (gradT ⟨y, hy⟩)) := by
      rw [← ecy, ← LinearPMap.map_add, ← LinearPMap.map_smul]; rfl
    have hyfix : y ∈ ParV := mem_rowV_fix.1 (rowV.avg_mem x)
    have hyrf : yr ∈ ParV := Submodule.smul_mem _ _ (Submodule.add_mem _ hyfix (cjV_mem_ParV hyfix))
    have hyrr : IsRealV yr := by
      rw [isRealV_iff_cjV]
      simp only [yr, map_smul, map_add, cjV_cjV, add_comm]
    have e3 : ⟪G, y⟫_ℝ = ⟪G, yr⟫_ℝ := by
      simp only [yr, real_inner_smul_right, inner_add_right, inner_cjV_of_real hGr]; ring
    have e4 : ⟪F, gradT ⟨y, hy⟩⟫_ℝ = ⟪F, gradT ⟨yr, hyr⟩⟫_ℝ := by
      rw [ecyr]
      simp only [real_inner_smul_right, inner_add_right, inner_cjM_of_real hFr]; ring
    obtain ⟨hu, eu, -, -⟩ := resBV_grad_identification hyrf hyr hyrr
    set u := resBV yr
    have hyru : extVL u = yr := extVf_resBV hyrf hyrr
    have hgE : gradT ⟨yr, hyr⟩ ∈ rowE.fix := intertwines_grad_row.mem_fix ⟨yr, hyr⟩
      (mem_rowV_fix.2 hyrf)
    have hgu : extML 1 one_mul_one' (BoundedDomain.gradClosure ⟨u, hu⟩) = gradT ⟨yr, hyr⟩ := by
      rw [eu]; exact extM_resB _ _ hgE (isRealM_gradT hyr hyrr)
    have hfa := LinearPMap.adjoint_isFormalAdjoint cxQ.dense0 ⟨A, hA⟩ ⟨u, hu⟩
    rw [e1, e3, e2, e4, ← hgu]
    conv_lhs => rw [← hyru]
    rw [inner_extML, inner_extVL]
    exact congrArg (8 * ·) hfa
  have hmem := LinearPMap.mem_adjoint_domain_of_exists (T := gradT) F ⟨G, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_mulDomain _) ⟨F, hmem⟩ key⟩

end Adjoint

/-! ## Extension of `L²(TSD)(Q)` into `boxTSD` -/

section TSDExt

/-- A real-valued `L²` function on `𝕋³` (conjugate-symmetric coefficients) is a.e. its real
part. -/
theorem ae_eq_re_of_real {f : L2T}
    (hf : ∀ k, mFourierCoeff (f : T3 → ℂ) (-k) = conj (mFourierCoeff (f : T3 → ℂ) k)) :
    (f : T3 → ℂ) =ᵐ[volume] fun x => (((f : T3 → ℂ) x).re : ℂ) := by
  have hs : star f = f := (star_eq_self_iff f).2 hf
  filter_upwards [Lp.coeFn_star f] with x h2
  have hx : conj ((f : T3 → ℂ) x) = (f : T3 → ℂ) x := by
    have := congrFun (congrArg (fun u : L2T => (u : T3 → ℂ)) hs) x
    rw [h2] at this
    exact this
  have him : ((f : T3 → ℂ) x).im = 0 := by
    have := congrArg Complex.im hx
    rw [Complex.conj_im] at this
    linarith
  exact Complex.ext (by simp) (by simp [him])

/-- On `Q`, a real-valued function is its restriction. -/
theorem ae_Qr_eq_resQ_of_real {f : L2T}
    (hf : ∀ k, mFourierCoeff (f : T3 → ℂ) (-k) = conj (mFourierCoeff (f : T3 → ℂ) k)) :
    ∀ᵐ y ∂volume.restrict Qr, (f : T3 → ℂ) (proj y) = ((resQ f y : ℝ) : ℂ) := by
  filter_upwards [coeFn_resQ f, ae_Qr_of_ae_boxSet (p := fun x => (f : T3 → ℂ) x =
    (((f : T3 → ℂ) x).re : ℂ)) (ae_restrict_of_ae (ae_eq_re_of_real hf))] with y h1 h2
  rw [h1]; exact h2

/-- The closed box `[0, ½]³`. -/
def closedBox : Set R3 := univ.pi fun _ => Icc (0 : ℝ) (1 / 2)

theorem coe_zero_notMem_halfArc : ((0 : ℝ) : UnitAddCircle) ∉ halfArc := by
  rintro ⟨s, hs, e⟩
  have hs' : s ∈ Ioc (0 : ℝ) (0 + 1) := ⟨hs.1, by rw [zero_add]; linarith [hs.2]⟩
  have h1 : (1 : ℝ) ∈ Ioc (0 : ℝ) (0 + 1) := ⟨by norm_num, by norm_num⟩
  have e' : ((s : ℝ) : UnitAddCircle) = ((1 : ℝ) : UnitAddCircle) := by
    rw [e, AddCircle.coe_period]; rfl
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hs' h1).1 e'
  linarith [hs.2]

theorem coe_half_notMem_halfArc : ((1 / 2 : ℝ) : UnitAddCircle) ∉ halfArc := by
  rintro ⟨s, hs, e⟩
  have hs' : s ∈ Ioc (0 : ℝ) (0 + 1) := ⟨hs.1, by rw [zero_add]; linarith [hs.2]⟩
  have h1 : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) (0 + 1) := ⟨by norm_num, by norm_num⟩
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hs' h1).1 e
  linarith [hs.2]

/-- Points of `[0, ½]³` projecting into the open box lie in `Q`. -/
theorem mem_Qr_of_closedBox {y : R3} (hy : y ∈ closedBox) (h : proj y ∈ boxSet) : y ∈ Qr := by
  intro i _
  have hi := hy i (mem_univ i)
  have hb := h i (mem_univ i)
  refine ⟨lt_of_le_of_ne hi.1 fun e => ?_, lt_of_le_of_ne hi.2 fun e => ?_⟩
  · exact coe_zero_notMem_halfArc (by rw [e]; exact hb)
  · exact coe_half_notMem_halfArc (by rw [← e]; exact hb)

/-- **Localization of box test functions**: for `φ` smooth on `𝕋³` with support in the box and
`ℓ : ℂ →L[ℝ] ℝ`, the function `ℓ(φ ∘ proj)` on `Q`, extended by `0`, is a test function on `Q`,
with `∂_b` equal to `ℓ(∂_b φ ∘ proj)` on `Q`. -/
theorem isTest_loc {φ : T3 → ℂ} (hφ : IsSmooth φ) (hs : tsupport φ ⊆ boxSet)
    (ℓ : ℂ →L[ℝ] ℝ) :
    IsTest Qr (Qr.indicator fun y => ℓ (φ (proj y))) ∧
      ∀ b, ∀ y ∈ Qr, pd b (Qr.indicator fun y => ℓ (φ (proj y))) y =
        ℓ (partialT b φ (proj y)) := by
  set ψ : R3 → ℝ := Qr.indicator fun y => ℓ (φ (proj y))
  set K' : Set R3 := proj ⁻¹' tsupport φ ∩ closedBox
  have hK'c : IsCompact K' :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_left
      ((isClosed_tsupport φ).preimage isOpenQuotientMap_proj.continuous)
  have hK'Q : K' ⊆ Qr := fun y hy => mem_Qr_of_closedBox hy.2 (hs hy.1)
  have hQc : Qr ⊆ closedBox := fun y hy i hi => ⟨(hy i hi).1.le, (hy i hi).2.le⟩
  have hzero : ∀ y, y ∉ K' → ψ y = 0 := by
    intro y hy
    by_cases hyQ : y ∈ Qr
    · have : proj y ∉ tsupport φ := fun h => hy ⟨h, hQc hyQ⟩
      simp only [ψ, indicator_of_mem hyQ]
      rw [image_eq_zero_of_notMem_tsupport this, map_zero]
    · simp only [ψ, indicator_of_notMem hyQ]
  have hloc : ∀ y ∈ Qr, ψ =ᶠ[𝓝 y] fun z => ℓ (φ (proj z)) := fun y hy =>
    Filter.mem_of_superset (isOpen_Qr.mem_nhds hy) fun z hz =>
      (indicator_of_mem (show z ∈ Qr from hz) _ : ψ z = _)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) fun z => ℓ (φ (proj z)) := ℓ.contDiff.comp hφ
  have hsupp : Function.support ψ ⊆ K' := fun y hy => by
    by_contra h; exact hy (hzero y h)
  refine ⟨⟨?_, HasCompactSupport.intro hK'c fun y hy => hzero y hy,
    (closure_minimal hsupp hK'c.isClosed).trans hK'Q⟩, fun b y hy => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Qr
    · exact hsm.contDiffAt.congr_of_eventuallyEq (hloc y hy)
    · have hyK : y ∉ K' := fun h => hy (hK'Q h)
      have : ψ =ᶠ[𝓝 y] fun _ => 0 :=
        Filter.mem_of_superset (hK'c.isClosed.isOpen_compl.mem_nhds hyK) fun z hz => hzero z hz
      exact contDiffAt_const.congr_of_eventuallyEq this
  · have hd : Differentiable ℝ (φ ∘ proj) := hφ.contDiff_one.differentiable one_ne_zero
    unfold BoundedDomain.pd
    rw [(hloc y hy).fderiv_eq, partialT_proj hd]
    have : HasFDerivAt (fun z => ℓ (φ (proj z))) (ℓ.comp (fderiv ℝ (φ ∘ proj) y)) y :=
      ℓ.hasFDerivAt.comp y (hd y).hasFDerivAt
    rw [this.fderiv]
    rfl

/-- The row-wise divergence condition of `L²(TSD)(Q)`, one row at a time. -/
theorem TSD_row {B : BoundedDomain.L2M Qr} (hB : B ∈ BoundedDomain.TSD Qr) (a : Fin 3)
    {ψ : R3 → ℝ} (hψ : IsTest Qr ψ) :
    ∑ b, ∫ y, B (a, b) y * pd b ψ y ∂volume.restrict Qr = 0 := by
  classical
  have h := hB.2.2 (fun i => if i = a then ψ else 0) fun i => by
    split_ifs
    · exact hψ
    · exact IsTest.zero
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a] at h
  · simpa using h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    have : pd j (0 : R3 → ℝ) = 0 := by
      funext y; simp [BoundedDomain.pd]
    simp only [hi, ↓reduceIte, this, Pi.zero_apply, mul_zero, integral_zero]
  · simp

/-- A real-valued coefficient sequence whose restriction to `Q` vanishes is zero on the box. -/
theorem zeroOnBox_of_resQ {g : L2 Z3 ℂ} (hreal : ∀ k, g (-k) = conj (g k))
    (h : resQ (ofCoeff g) = 0) : ZeroOnBox g := by
  set f : L2T := ofCoeff g
  have hfr := ae_eq_re_of_real (f := f) fun k => by
    rw [mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff, hreal]
  have h0 : (resQ f : R3 → ℝ) =ᵐ[volume.restrict Qr] 0 := by
    rw [h]; exact Lp.coeFn_zero _ _ _
  have hQ : ∀ᵐ y ∂volume.restrict Qr, ((f : T3 → ℂ) (proj y)).re = 0 := by
    filter_upwards [coeFn_resQ f, h0] with y h1 h2
    rw [← h1, h2]; rfl
  have hmeas : MeasurableSet {x : T3 | ¬ ((f : T3 → ℂ) x).re = 0} :=
    ((Complex.measurable_re.comp (Lp.stronglyMeasurable f).measurable)
      (measurableSet_singleton 0)).compl
  have hbox : ∀ᵐ x ∂volume.restrict boxSet, ((f : T3 → ℂ) x).re = 0 := by
    rw [ae_iff, ← measurePreserving_proj_box.measure_preimage hmeas.nullMeasurableSet]
    rw [ae_iff] at hQ
    exact hQ
  filter_upwards [hbox, ae_restrict_of_ae hfr] with x h1 h2
  rw [h2, h1]; simp

/-- Pairing a real function with `∂_b φ` for a box test function `φ`, in terms of `Q`. -/
theorem integral_mul_partialT_box {f : L2T}
    (hf : ∀ k, mFourierCoeff (f : T3 → ℂ) (-k) = conj (mFourierCoeff (f : T3 → ℂ) k))
    {φ : T3 → ℂ} (hφ : IsSmooth φ) (hs : tsupport φ ⊆ boxSet) (b : Fin 3) :
    ∫ x, (f : T3 → ℂ) x * partialT b φ x =
      ((∫ y, resQ f y * pd b (Qr.indicator fun y => Complex.reCLM (φ (proj y))) y
          ∂volume.restrict Qr : ℝ) : ℂ) +
        ((∫ y, resQ f y * pd b (Qr.indicator fun y => Complex.imCLM (φ (proj y))) y
          ∂volume.restrict Qr : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hre, dre⟩ := isTest_loc hφ hs Complex.reCLM
  obtain ⟨him, dim⟩ := isTest_loc hφ hs Complex.imCLM
  have hc := continuous_partialT hφ.contDiff_one b
  have hg : AEStronglyMeasurable (fun x => (f : T3 → ℂ) x * partialT b φ x) volume :=
    (Lp.aestronglyMeasurable f).mul hc.aestronglyMeasurable
  rw [integral_eq_Qr hg fun x hx => by
    rw [Box.partialT_eq_zero_of_notMem (fun h => hx (hs h)), mul_zero]]
  have i1 := BoundedDomain.integrable_mul (resQ f) (hre.pdiff b).memLp
  have i2 := BoundedDomain.integrable_mul (resQ f) (him.pdiff b).memLp
  rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_mul_const,
    ← integral_add i1.ofReal (i2.ofReal.mul_const _)]
  refine integral_congr_ae ?_
  filter_upwards [ae_Qr_eq_resQ_of_real hf, ae_restrict_mem measurableSet_Qr] with y h1 h2
  rw [h1, dre b y h2, dim b y h2]
  conv_lhs => rw [← Complex.re_add_im (partialT b φ (proj y))]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply]
  push_cast; ring

/-- **A real field of a parity class whose restriction is in `L²(TSD)(Q)` lies in `boxTSD`.** -/
theorem mem_boxTSD_of {τ : ℂ} {E : L2M} (hE : E ∈ ParRow τ) (hr : IsRealM E)
    (hT : resB E ∈ BoundedDomain.TSD Qr) : E ∈ boxTSD τ := by
  have hreal : ∀ p, ∀ k, mFourierCoeff (ofCoeff (entry p E) : T3 → ℂ) (-k) =
      conj (mFourierCoeff (ofCoeff (entry p E) : T3 → ℂ) k) := fun p k => by
    rw [mFourierCoeff_ofCoeff_entry, mFourierCoeff_ofCoeff_entry, hr k p]
  have hsym : E ∈ boxSym := by
    rw [mem_boxSym]
    intro a b
    refine zeroOnBox_of_resQ (fun k => by simp [hr k (a, b), hr k (b, a)]) ?_
    rw [ofCoeff_sub, map_sub, ← resB_apply, ← resB_apply, hT.1 a b, sub_self]
  have htr : E ∈ boxTr := by
    rw [mem_boxTr]
    refine zeroOnBox_of_resQ (fun k => by
      rw [lp_sum_apply, lp_sum_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [entry_apply, entry_apply, hr k]) ?_
    rw [ofCoeff_sum, map_sum]
    exact hT.2.1
  have hdiv : E ∈ boxDiv := by
    rw [mem_boxDiv]
    intro a φ hφ hs
    simp only [integral_mul_partialT_box (hreal _) hφ hs]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [← Complex.ofReal_sum]
    change ((∑ b, ∫ y, resB E (a, b) y * pd b _ y ∂volume.restrict Qr : ℝ) : ℂ) +
      ((∑ b, ∫ y, resB E (a, b) y * pd b _ y ∂volume.restrict Qr : ℝ) : ℂ) * Complex.I = 0
    rw [TSD_row hT a (isTest_loc hφ hs Complex.reCLM).1,
      TSD_row hT a (isTest_loc hφ hs Complex.imCLM).1]
    simp
  exact ⟨⟨⟨hE, hsym⟩, htr⟩, hdiv⟩

end TSDExt

/-! ## Transfer of the box theorems to the thesis' complex on `Q` -/

section Transfer

open Feec.Constraints Feec.HilbertComplex2

/-- The state space of the thesis' complex on `Q`. -/
abbrev XQ := Tot (BoundedDomain.L2V Qr) (BoundedDomain.L2M Qr) (BoundedDomain.L2M Qr)

/-- **Extension of states** `(σ, E, B) ↦ (ext σ, ext E, ext B)` into the periodic state space,
with the parities of the thesis' boundary conditions (`ParV`, `ParRow 1`, `ParRow (-1)`). -/
def iota : XQ →L[ℝ] Tot L2V L2M L2M :=
  (Constraints.totL (W0 := L2V) (W1 := L2M) (W2 := L2M)).symm.toContinuousLinearMap ∘L
    (extVL.prodMap ((extML 1 one_mul_one').prodMap (extML (-1) neg_one_mul_neg_one'))) ∘L
    (Constraints.totL (W0 := BoundedDomain.L2V Qr) (W1 := BoundedDomain.L2M Qr)
      (W2 := BoundedDomain.L2M Qr)).toContinuousLinearMap

theorem tot_iota (x : XQ) :
    tot L2V L2M L2M (iota x) = (extVL (tot _ _ _ x).1, extML 1 one_mul_one' (tot _ _ _ x).2.1,
      extML (-1) neg_one_mul_neg_one' (tot _ _ _ x).2.2) := by
  simp [iota]; rfl

theorem iota_injective : Function.Injective iota := by
  intro x y h
  have := congrArg (tot L2V L2M L2M) h
  rw [tot_iota, tot_iota] at this
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, h2, h3⟩ := this
  apply (tot _ _ _).injective
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have := congrArg resBV h1
    simpa only [extVL_apply, resBV_extVf] using this
  · have := congrArg resB h2
    simpa only [extML_apply, resB_extM] using this
  · have := congrArg resB h3
    simpa only [extML_apply, resB_extM] using this

theorem iota_mem_domL (x : cxQ.domL) : iota x ∈ periodicComplex.domL := by
  rw [Constraints.mem_domL, tot_iota]
  have hx := (Constraints.mem_domL (H := cxQ)).1 x.2
  obtain ⟨h0, ⟨h1, h1s⟩, h2⟩ := hx
  refine ⟨(extVL_grad ⟨_, h0⟩).1, ⟨(extML_curl (BoundedDomain.mem_domain_curlClosure.1 h1)).1,
    (extML_adj_div h1s).1⟩, (extML_adj_curl h2).1⟩

/-- **The extension intertwines the Hodge wave operators**: `ι L_Q = L_{𝕋³} ι`. -/
theorem iota_waveOp (x : cxQ.waveOp.domain) :
    iota (cxQ.waveOp x) = periodicComplex.waveOp ⟨iota x, iota_mem_domL x⟩ := by
  have hx := (Constraints.mem_domL (H := cxQ)).1 x.2
  obtain ⟨h0, ⟨h1, h1s⟩, h2⟩ := hx
  obtain ⟨g0, e0⟩ := extVL_grad ⟨_, h0⟩
  obtain ⟨g1, e1⟩ := extML_curl (BoundedDomain.mem_domain_curlClosure.1 h1)
  obtain ⟨g1s, e1s⟩ := extML_adj_div h1s
  obtain ⟨g2, e2⟩ := extML_adj_curl h2
  set y : periodicComplex.waveOp.domain := ⟨iota x, iota_mem_domL x⟩
  have q0 : periodicComplex.d0 (periodicComplex.pr0 ⟨y.1, y.2⟩) = gradT ⟨_, g0⟩ := by
    change gradT _ = gradT _; congr 1
  have q1 : periodicComplex.d1 (periodicComplex.prV1 ⟨y.1, y.2⟩) = curlT ⟨_, g1⟩ := by
    change curlT _ = curlT _; congr 1
  have q1s : periodicComplex.d0† (periodicComplex.prV1s ⟨y.1, y.2⟩) = gradT† ⟨_, g1s⟩ := by
    change gradT† _ = gradT† _; congr 1
  have q2 : periodicComplex.d1† (periodicComplex.prV2s ⟨y.1, y.2⟩) = curlT† ⟨_, g2⟩ := by
    change curlT† _ = curlT† _; congr 1
  have r0 : cxQ.d0 (cxQ.pr0 ⟨x.1, x.2⟩) = BoundedDomain.gradClosure ⟨_, h0⟩ := by
    change BoundedDomain.gradClosure _ = _; congr 1
  have r1 : cxQ.d1 (cxQ.prV1 ⟨x.1, x.2⟩) =
      BoundedDomain.curlClosure ⟨_, BoundedDomain.mem_domain_curlClosure.2
        (BoundedDomain.mem_domain_curlClosure.1 h1)⟩ := by
    change BoundedDomain.curlClosure _ = _; congr 1
  have r1s : cxQ.d0† (cxQ.prV1s ⟨x.1, x.2⟩) = cxQ.d0† ⟨_, h1s⟩ := by congr 1
  have r2 : cxQ.d1† (cxQ.prV2s ⟨x.1, x.2⟩) = cxQ.d1† ⟨_, h2⟩ := by congr 1
  apply (tot L2V L2M L2M).injective
  rw [tot_iota, Constraints.tot_waveOp, Constraints.tot_waveOp (H := periodicComplex) y]
  simp only [q0, q1, q1s, q2, r0, r1, r1s, r2, map_neg, map_add, e0, e1, e1s, e2]

theorem iota_group (G : UnitaryGroupGenerator (-cxQ.waveOp)) (t : ℝ) (x : XQ) :
    iota (G.S t x) = periodicGroup.S t (iota x) := by
  refine Box.group_intertwine G periodicGroup iota (fun y => iota_mem_domL (x := ⟨y, y.2⟩))
    (fun y => ?_) (isSkewSymm_neg (Constraints.waveOp_isSkewSymm periodicComplex))
    cxQ.neg_waveOp_isSkewAdjoint.dense_domain t x
  rw [LinearPMap.neg_apply, LinearPMap.neg_apply, _root_.map_neg]
  congr 1
  exact iota_waveOp ⟨y, y.2⟩

theorem iota_mem_Kc {x : XQ} (hx : x ∈ Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr)
    (BoundedDomain.TSD Qr)) : iota x ∈ Kc L2V (boxTSD 1) (boxTSD (-1)) := by
  rw [mem_Kc] at hx ⊢
  obtain ⟨h0, h1, h2⟩ := hx
  rw [tot_iota]
  refine ⟨?_, ?_, ?_⟩
  · dsimp only; rw [h0, map_zero]
  · dsimp only
    refine mem_boxTSD_of (mem_rowE_fix.1 (extM_mem_fix 1 one_mul_one' _)) (isRealM_extM _ _ _) ?_
    rw [extML_apply, resB_extM]; exact h1
  · dsimp only
    refine mem_boxTSD_of (mem_rowB_fix.1 (extM_mem_fix (-1) neg_one_mul_neg_one' _))
      (isRealM_extM _ _ _) ?_
    rw [extML_apply, resB_extM]; exact h2

/-- **On the cube `Q` with the thesis' boundary conditions, forward invariance of
`K = {0} × L²(TSD) × L²(TSD)` forces stationarity**, for every orthogonal group `G` generated by
`-L` of the thesis' complex `H̊¹(Q) → H̊(curl, Q) → L²(Q)` (e.g. Stone's group): the forward orbit
of `x` stays in `K` iff `x ∈ K` and `G.S t x = x` for all `t`. Transferred from the box model
(`Feec.Box.forward_iff_mem_Kmax`, `Feec.Box.mem_Kmax_iff`) through the extension `iota`, which
intertwines the groups (`iota_group`) and maps `K` into the box `K` (`iota_mem_Kc`). -/
theorem thesisComplexQ_forward_iff (G : UnitaryGroupGenerator (-cxQ.waveOp)) (x : XQ) :
    (∀ t, 0 ≤ t → G.S t x ∈ Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr)
      (BoundedDomain.TSD Qr)) ↔
      x ∈ Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr) ∧
        ∀ t, G.S t x = x := by
  constructor
  · intro hf
    have hK : x ∈ Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr) := by
      have := hf 0 le_rfl
      rwa [G.map_zero] at this
    have hfb : ∀ t, 0 ≤ t → periodicGroup.S t (iota x) ∈ Kc L2V (boxTSD 1) (boxTSD (-1)) :=
      fun t ht => by rw [← iota_group]; exact iota_mem_Kc (hf t ht)
    have hmax := (Box.forward_iff_mem_Kmax (boxTSD_le 1) (boxTSD_le (-1)) (iota x)).1 hfb
    obtain ⟨-, hs⟩ := (Box.mem_Kmax_iff (boxTSD_le 1) (boxTSD_le (-1)) _).1 hmax
    exact ⟨hK, fun t => iota_injective (by rw [iota_group, hs])⟩
  · rintro ⟨hK, hs⟩ t _
    rw [hs t]; exact hK

/-- **`K*` on the cube with the thesis' boundary conditions consists exactly of the stationary
data in `K`**, for every orthogonal group `G` generated by `-L` of the thesis' complex on `Q`. -/
theorem thesisComplexQ_mem_Kmax_iff (G : UnitaryGroupGenerator (-cxQ.waveOp)) (x : XQ) :
    x ∈ Kmax G (Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr)) ↔
      x ∈ Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr) ∧
        ∀ t, G.S t x = x :=
  ⟨fun hx => (thesisComplexQ_forward_iff G x).1 fun t _ => hx t,
    fun ⟨hK, hs⟩ t => by rw [hs t]; exact hK⟩

/-- The curl coefficients of `D(curl*)`: `(curl* y)(k) = curl_ξ y(k)`. -/
theorem adjoint_curlT_apply (y : curlT†.domain) (k : Z3) :
    curlT† y k = curlSym (freq k) ((y : L2M) k) := by
  have h := adjoint_mulOp_apply (fun k => curlSym (freq k)) y k
  rw [adjoint_curlSym] at h
  exact h

/-- **`K*` on the cube, explicitly**: `x ∈ K*` iff `x = (0, 0, B₀)` with `B₀ ∈ L²(TSD)(Q)` having
a weak curl equal to `0` (`B₀ ∈ D(d1*)`, `d1* B₀ = 0`, no boundary condition). -/
theorem thesisComplexQ_mem_Kmax_iff' (G : UnitaryGroupGenerator (-cxQ.waveOp)) (x : XQ) :
    x ∈ Kmax G (Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr)) ↔
      ∃ B ∈ BoundedDomain.TSD Qr, ∃ h : B ∈ cxQ.d1†.domain, cxQ.d1† ⟨B, h⟩ = 0 ∧
        x = ini (BoundedDomain.L2V Qr) 0 B := by
  have hG : ∀ t y, iota (G.S t y) = periodicGroup.S t (iota y) := fun t y => iota_group G t y
  constructor
  · intro hx
    obtain ⟨hK, hs⟩ := (thesisComplexQ_mem_Kmax_iff G x).1 hx
    have hmax : iota x ∈ Kmax periodicGroup (Kc L2V (boxTSD 1) (boxTSD (-1))) := fun t => by
      rw [← hG, hs]; exact iota_mem_Kc hK
    obtain ⟨B', -, hcurl, hB'⟩ := (mem_Kmax_boxTSD_iff _).1 hmax
    have ht := congrArg (tot L2V L2M L2M) hB'
    rw [tot_iota, tot_ini] at ht
    simp only [Prod.mk.injEq] at ht
    obtain ⟨e0, e1, e2⟩ := ht
    rw [mem_Kc] at hK
    obtain ⟨hk0, -, hk2⟩ := hK
    have hB'c : B' ∈ Hcurl := by
      change Memℓp _ 2
      simp_rw [hcurl]; exact zero_memℓp
    have hct : curlT ⟨B', hB'c⟩ = 0 := lp.ext (funext fun k => hcurl k)
    obtain ⟨hd, ed⟩ := resB_curl hB'c
    have hres : resB B' = (tot _ _ _ x).2.2 := by
      rw [← e2, extML_apply, resB_extM]
    have hE : (tot _ _ _ x).2.1 = 0 := by
      have := congrArg resB e1
      rwa [extML_apply, resB_extM, map_zero] at this
    refine ⟨(tot _ _ _ x).2.2, hk2, hres ▸ hd, ?_, ?_⟩
    · have key : ∀ (C : BoundedDomain.L2M Qr) (hC : C = resB B') (h : C ∈ cxQ.d1†.domain),
          cxQ.d1† ⟨C, h⟩ = cxQ.d1† ⟨resB B', hd⟩ := by rintro C rfl h; rfl
      rw [key _ hres.symm, ed, hct, map_zero]
    · apply (tot _ _ _).injective
      rw [tot_ini]
      exact Prod.ext hk0 (Prod.ext hE rfl)
  · rintro ⟨B, hBT, hB, hd, rfl⟩
    have hK : ini (BoundedDomain.L2V Qr) 0 B ∈
        Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr) := by
      rw [mem_Kc, tot_ini]; exact ⟨rfl, Submodule.zero_mem _, hBT⟩
    obtain ⟨g2, e2⟩ := extML_adj_curl hB
    have hcurl : ∀ k, curlSym (freq k) (extML (-1) neg_one_mul_neg_one' B k) = 0 := fun k => by
      have := congrArg (fun A : L2M => A k) e2
      simp only [hd, map_zero] at this
      rw [← adjoint_curlT_apply ⟨_, g2⟩ k]
      exact this
    have hi : iota (ini (BoundedDomain.L2V Qr) 0 B) =
        ini L2V 0 (extML (-1) neg_one_mul_neg_one' B) := by
      apply (tot _ _ _).injective
      rw [tot_iota, tot_ini, tot_ini, map_zero, map_zero]
    have hmax : iota (ini (BoundedDomain.L2V Qr) 0 B) ∈
        Kmax periodicGroup (Kc L2V (boxTSD 1) (boxTSD (-1))) := by
      rw [mem_Kmax_boxTSD_iff]
      refine ⟨_, ?_, hcurl, hi⟩
      have := iota_mem_Kc hK
      rw [mem_Kc, hi, tot_ini] at this
      exact this.2.2
    obtain ⟨-, hs⟩ := (Box.mem_Kmax_iff (boxTSD_le 1) (boxTSD_le (-1)) _).1 hmax
    refine (thesisComplexQ_mem_Kmax_iff G _).2 ⟨hK, fun t => iota_injective ?_⟩
    rw [hG, hs]

/-- The statements hold in particular for the Stone group of the thesis' complex on `Q`
(`Feec.HilbertComplex2.waveGroup`), so they are not vacuous. -/
theorem thesisComplexQ_mem_Kmax_iff_waveGroup (x : XQ) :
    x ∈ Kmax cxQ.waveGroup
        (Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr)) ↔
      x ∈ Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr) ∧
        ∀ t, cxQ.waveGroup.S t x = x :=
  thesisComplexQ_mem_Kmax_iff _ x

end Transfer

/-! ## The spaces without boundary condition -/

/-- **`H(curl, Q; ℝ³ˣ³)` (no boundary condition, `= D(d1*)`) is the real magnetic parity space**:
restriction is a bijection from the real fields of `ParRow (-1) ∩ H(curl, 𝕋³)` onto
`Feec.BoundedDomain.HcurlM Q`. -/
theorem bijOn_resB_HcurlM :
    Set.BijOn resB {E : L2M | E ∈ ParRow (-1) ∧ E ∈ Hcurl ∧ IsRealM E}
      (BoundedDomain.HcurlM Qr) := by
  refine ⟨fun E hE => resB_mem_HcurlM hE.2.1, fun E hE E' hE' h =>
    eq_of_resB_eq (-1) neg_one_mul_neg_one' (mem_rowB_fix.2 hE.1) (mem_rowB_fix.2 hE'.1) hE.2.2
      hE'.2.2 h, fun B hB => ?_⟩
  obtain ⟨g, -⟩ := extML_adj_curl
    ((BoundedDomain.thesisComplex_adjoint_d1_iff isOpen_Qr isBounded_Qr).2 hB)
  rw [adjoint_curlT] at g
  exact ⟨_, ⟨mem_rowB_fix.1 (extM_mem_fix _ _ B), g, isRealM_extM _ _ B⟩, resB_extM _ _ B⟩

/-- **`H(div, Q; ℝ³ˣ³)` (no boundary condition, `= D(d0*)`) is the real electric part of
`H(div, 𝕋³)`**: restriction is a bijection from the real fields of `ParRow 1 ∩ H(div, 𝕋³)` onto
`Feec.BoundedDomain.HdivM Q`. -/
theorem bijOn_resB_HdivM :
    Set.BijOn resB {E : L2M | E ∈ ParRow 1 ∧ E ∈ Hdiv ∧ IsRealM E}
      (BoundedDomain.HdivM Qr) := by
  refine ⟨fun E hE => ?_, fun E hE E' hE' h =>
    eq_of_resB_eq 1 one_mul_one' (mem_rowE_fix.2 hE.1) (mem_rowE_fix.2 hE'.1) hE.2.2
      hE'.2.2 h, fun B hB => ?_⟩
  · exact (BoundedDomain.thesisComplex_adjoint_d0_iff isOpen_Qr isBounded_Qr).1
      (resB_div hE.2.1).1
  · obtain ⟨g, -⟩ := extML_adj_div
      ((BoundedDomain.thesisComplex_adjoint_d0_iff isOpen_Qr isBounded_Qr).2 hB)
    rw [adjoint_gradT_domain] at g
    exact ⟨_, ⟨mem_rowE_fix.1 (extM_mem_fix _ _ B), g, isRealM_extM _ _ B⟩, resB_extM _ _ B⟩

/-- **`L²(TSD)(Q)` is the real part of `boxTSD`**, in either row-wise class (`ε = 1`: the
electric slot `boxTSD 1`; `ε = -1`: the magnetic slot `boxTSD (-1)`). -/
theorem bijOn_resB_TSD (ε : ℝ) (hε : ε * ε = 1) (hfix : ∀ E : L2M,
      E ∈ (rowMf ε hε).lift.fix ↔ E ∈ ParRow (ε : ℂ)) :
    Set.BijOn resB {E : L2M | E ∈ boxTSD (ε : ℂ) ∧ IsRealM E} (BoundedDomain.TSD Qr) := by
  refine ⟨fun E hE => resB_mem_TSD hE.1, fun E hE E' hE' h =>
    eq_of_resB_eq ε hε ((hfix E).2 hE.1.1.1.1) ((hfix E').2 hE'.1.1.1.1) hE.2 hE'.2 h,
    fun B hB => ⟨_, ⟨mem_boxTSD_of ((hfix _).1 (extM_mem_fix ε hε B)) (isRealM_extM _ _ B)
      (by rw [resB_extM]; exact hB), isRealM_extM _ _ B⟩, resB_extM _ _ B⟩⟩

theorem bijOn_resB_TSD_electric :
    Set.BijOn resB {E : L2M | E ∈ boxTSD 1 ∧ IsRealM E} (BoundedDomain.TSD Qr) := by
  have h := bijOn_resB_TSD 1 one_mul_one' fun E => by
    rw [Complex.ofReal_one]; exact mem_rowE_fix
  simpa using h

theorem bijOn_resB_TSD_magnetic :
    Set.BijOn resB {E : L2M | E ∈ boxTSD (-1) ∧ IsRealM E} (BoundedDomain.TSD Qr) := by
  have h := bijOn_resB_TSD (-1) neg_one_mul_neg_one' fun E => by
    rw [Complex.ofReal_neg, Complex.ofReal_one]; exact mem_rowB_fix
  simpa using h

/-! ## Dilations and translations: every open cube -/

noncomputable section Dilation

variable {a : ℝ} {b : R3}

/-- The dilation-translation `x ↦ a x + b` as a homeomorphism. -/
def affH (a : ℝ) (ha : a ≠ 0) (b : R3) : R3 ≃ₜ R3 :=
  (Homeomorph.smulOfNeZero a ha).trans (Homeomorph.addRight b)

@[simp] theorem affH_apply (ha : a ≠ 0) (x : R3) : affH a ha b x = a • x + b := rfl

theorem map_affH_volume (ha : a ≠ 0) :
    Measure.map (affH a ha b) volume = ENNReal.ofReal (|a ^ 3|⁻¹) • (volume : Measure R3) := by
  have h1 : (affH a ha b : R3 → R3) = (· + b) ∘ (a • ·) := rfl
  rw [h1, ← Measure.map_map (measurable_add_const b) (measurable_const_smul a),
    Measure.map_addHaar_smul volume ha, Module.finrank_fin_fun, Measure.map_smul,
    Measure.IsAddRightInvariant.map_add_right_eq_self, abs_inv]
  all_goals fun_prop

theorem map_affH_restrict (ha : a ≠ 0) {Ω Ω' : Set R3} (hT : ∀ x, x ∈ Ω ↔ a • x + b ∈ Ω') :
    Measure.map (affH a ha b) (volume.restrict Ω) =
      ENNReal.ofReal (|a ^ 3|⁻¹) • volume.restrict Ω' := by
  have hs : Ω = affH a ha b ⁻¹' Ω' := by ext x; exact hT x
  rw [hs, ← (affH a ha b).measurableEmbedding.restrict_map, map_affH_volume,
    Measure.restrict_smul]

variable {Ω Ω' : Set R3} (ha : a ≠ 0) (hT : ∀ x, x ∈ Ω ↔ a • x + b ∈ Ω')

include hT in
theorem qmp_affH : QuasiMeasurePreserving (affH a ha b) (volume.restrict Ω)
    (volume.restrict Ω') :=
  ⟨(affH a ha b).continuous.measurable, by
    rw [map_affH_restrict ha hT]; exact Measure.smul_absolutelyContinuous⟩

include hT in
theorem memLp_comp_affH (f : BoundedDomain.L2 Ω') :
    MemLp (fun x => f (affH a ha b x)) 2 (volume.restrict Ω) := by
  have hm : AEStronglyMeasurable f (Measure.map (affH a ha b) (volume.restrict Ω)) := by
    rw [map_affH_restrict ha hT]; exact (Lp.aestronglyMeasurable f).smul_measure _
  refine (memLp_map_measure_iff hm (qmp_affH ha hT).aemeasurable).1 ?_
  rw [map_affH_restrict ha hT]
  exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top

/-- Pull-back of `L²` functions along `x ↦ a x + b` (no normalization). -/
def pullFun (f : BoundedDomain.L2 Ω') : BoundedDomain.L2 Ω :=
  (memLp_comp_affH ha hT f).toLp _

theorem coeFn_pullFun (f : BoundedDomain.L2 Ω') :
    (pullFun ha hT f : R3 → ℝ) =ᵐ[volume.restrict Ω] fun x => f (affH a ha b x) :=
  (memLp_comp_affH ha hT f).coeFn_toLp

include hT in
theorem comp_ae_eq {f g : R3 → ℝ} (h : f =ᵐ[volume.restrict Ω'] g) :
    (fun x => f (affH a ha b x)) =ᵐ[volume.restrict Ω] fun x => g (affH a ha b x) :=
  (qmp_affH ha hT).ae_eq_comp h

theorem pullFun_add (f g : BoundedDomain.L2 Ω') :
    pullFun ha hT (f + g) = pullFun ha hT f + pullFun ha hT g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pullFun ha hT (f + g), coeFn_pullFun ha hT f, coeFn_pullFun ha hT g,
    Lp.coeFn_add (pullFun ha hT f) (pullFun ha hT g),
    comp_ae_eq ha hT (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]

theorem pullFun_smul (c : ℝ) (f : BoundedDomain.L2 Ω') :
    pullFun ha hT (c • f) = c • pullFun ha hT f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pullFun ha hT (c • f), coeFn_pullFun ha hT f,
    Lp.coeFn_smul c (pullFun ha hT f), comp_ae_eq ha hT (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply]

theorem inner_pullFun (f g : BoundedDomain.L2 Ω') :
    ⟪pullFun ha hT f, pullFun ha hT g⟫ = |a ^ 3|⁻¹ * ⟪f, g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  have e : (fun x => ⟪pullFun ha hT f x, pullFun ha hT g x⟫) =ᵐ[volume.restrict Ω]
      fun x => (fun y => ⟪f y, g y⟫) (affH a ha b x) := by
    filter_upwards [coeFn_pullFun ha hT f, coeFn_pullFun ha hT g] with x h1 h2
    rw [h1, h2]
  have hm : AEStronglyMeasurable (fun y => ⟪f y, g y⟫)
      (Measure.map (affH a ha b) (volume.restrict Ω)) := by
    rw [map_affH_restrict ha hT]
    exact ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)).smul_measure _
  have hmap := integral_map (qmp_affH ha hT).aemeasurable hm
  rw [integral_congr_ae e, ← hmap, map_affH_restrict ha hT,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- The pull-back as a linear map. -/
def pullLin : BoundedDomain.L2 Ω' →ₗ[ℝ] BoundedDomain.L2 Ω where
  toFun := pullFun ha hT
  map_add' := pullFun_add ha hT
  map_smul' := pullFun_smul ha hT

theorem norm_pullFun (f : BoundedDomain.L2 Ω') :
    ‖pullFun ha hT f‖ = Real.sqrt (|a ^ 3|⁻¹) * ‖f‖ := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_pullFun,
    real_inner_self_eq_norm_sq, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The pull-back `f ↦ f ∘ T` along `T x = a x + b`, `L²(Ω') → L²(Ω)`. -/
def pullL : BoundedDomain.L2 Ω' →L[ℝ] BoundedDomain.L2 Ω :=
  (pullLin ha hT).mkContinuous (Real.sqrt (|a ^ 3|⁻¹)) fun f => (norm_pullFun ha hT f).le

theorem pullL_apply (f : BoundedDomain.L2 Ω') : pullL ha hT f = pullFun ha hT f := rfl

/-- Componentwise pull-back of matrix fields. -/
def pullM : BoundedDomain.L2M Ω' →L[ℝ] BoundedDomain.L2M Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Ix => BoundedDomain.L2 Ω)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun ij => pullL ha hT ∘L ContinuousLinearMap.proj ij) ∘L
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Ix => BoundedDomain.L2 Ω')).toContinuousLinearMap

/-- Componentwise pull-back of vector fields. -/
def pullV : BoundedDomain.L2V Ω' →L[ℝ] BoundedDomain.L2V Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => BoundedDomain.L2 Ω)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun i => pullL ha hT ∘L ContinuousLinearMap.proj i) ∘L
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => BoundedDomain.L2 Ω')).toContinuousLinearMap

@[simp] theorem pullM_apply (A : BoundedDomain.L2M Ω') (ij : Ix) :
    pullM ha hT A ij = pullFun ha hT (A ij) := rfl

@[simp] theorem pullV_apply (u : BoundedDomain.L2V Ω') (i : Fin 3) :
    pullV ha hT u i = pullFun ha hT (u i) := rfl

theorem inner_pullM (A B : BoundedDomain.L2M Ω') :
    ⟪pullM ha hT A, pullM ha hT B⟫ = |a ^ 3|⁻¹ * ⟪A, B⟫ := by
  simp only [PiLp.inner_apply, pullM_apply, inner_pullFun, Finset.mul_sum]

theorem inner_pullV (u v : BoundedDomain.L2V Ω') :
    ⟪pullV ha hT u, pullV ha hT v⟫ = |a ^ 3|⁻¹ * ⟪u, v⟫ := by
  simp only [PiLp.inner_apply, pullV_apply, inner_pullFun, Finset.mul_sum]

include hT in
theorem isTest_comp {f : R3 → ℝ} (hf : IsTest Ω' f) :
    IsTest Ω (fun x => f (affH a ha b x)) where
  contDiff := hf.contDiff.comp (show ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : R3 => a • x + b) by fun_prop)
  hasCompactSupport := hf.hasCompactSupport.comp_homeomorph (affH a ha b)
  tsupport_subset := by
    intro x hx
    rw [show (fun x => f (affH a ha b x)) = f ∘ affH a ha b from rfl,
      tsupport_comp_eq_preimage] at hx
    exact (hT x).2 (hf.tsupport_subset hx)

theorem hasFDerivAt_affH (x : R3) :
    HasFDerivAt (affH a ha b) (a • ContinuousLinearMap.id ℝ R3) x :=
  ((hasFDerivAt_id x).const_smul a).add_const b

theorem pd_comp {f : R3 → ℝ} (hf : Differentiable ℝ f) (k : Fin 3) (x : R3) :
    BoundedDomain.pd k (fun y => f (affH a ha b y)) x = a * BoundedDomain.pd k f (affH a ha b x) := by
  have h := ((hf (affH a ha b x)).hasFDerivAt.comp x (hasFDerivAt_affH ha x)).fderiv
  simp only [BoundedDomain.pd]
  rw [show (fun y => f (affH a ha b y)) = f ∘ affH a ha b from rfl, h]
  simp

include hT in
theorem curlGraph_pull {p : BoundedDomain.L2M Ω' × BoundedDomain.L2M Ω'}
    (hp : p ∈ BoundedDomain.curlGraph Ω') :
    (pullM ha hT p.1, a • pullM ha hT p.2) ∈ BoundedDomain.curlGraph Ω := by
  obtain ⟨Φ, hΦ, hae⟩ := hp
  refine ⟨fun ij x => Φ ij (affH a ha b x), fun ij => isTest_comp ha hT (hΦ ij), fun ij => ⟨?_, ?_⟩⟩
  · filter_upwards [coeFn_pullFun ha hT (p.1 ij), comp_ae_eq ha hT (hae ij).1] with x h1 h2
    simp only [pullM_apply]; rw [h1, h2]
  · filter_upwards [Lp.coeFn_smul a (pullM ha hT p.2 ij), coeFn_pullFun ha hT (p.2 ij),
      comp_ae_eq ha hT (hae ij).2] with x h0 h1 h2
    simp only [PiLp.smul_apply, pullM_apply] at h0 ⊢
    rw [h0, Pi.smul_apply, h1, smul_eq_mul, h2]
    simp only [curlM]
    rw [pd_comp ha (hΦ _).differentiable, pd_comp ha (hΦ _).differentiable]
    ring

include hT in
theorem gradGraph_pull {p : BoundedDomain.L2V Ω' × BoundedDomain.L2M Ω'}
    (hp : p ∈ BoundedDomain.gradGraph Ω') :
    (pullV ha hT p.1, a • pullM ha hT p.2) ∈ BoundedDomain.gradGraph Ω := by
  obtain ⟨φ, hφ, hae1, hae2⟩ := hp
  refine ⟨fun i x => φ i (affH a ha b x), fun i => isTest_comp ha hT (hφ i), fun i => ?_,
    fun ij => ?_⟩
  · filter_upwards [coeFn_pullFun ha hT (p.1 i), comp_ae_eq ha hT (hae1 i)] with x h1 h2
    simp only [pullV_apply]; rw [h1, h2]
  · filter_upwards [Lp.coeFn_smul a (pullM ha hT p.2 ij), coeFn_pullFun ha hT (p.2 ij),
      comp_ae_eq ha hT (hae2 ij)] with x h0 h1 h2
    simp only [PiLp.smul_apply, pullM_apply] at h0 ⊢
    rw [h0, Pi.smul_apply, h1, smul_eq_mul, h2]
    simp only [BoundedDomain.gradM]
    rw [pd_comp ha (hφ _).differentiable]

variable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hΩ' : IsOpen Ω')
  (hb' : Bornology.IsBounded Ω')

include hΩ hb hΩ' hb' in
theorem curlClosure_pull (u : (BoundedDomain.curlClosure (Ω := Ω')).domain) :
    ∃ h : pullM ha hT u ∈ (BoundedDomain.curlClosure (Ω := Ω)).domain,
      BoundedDomain.curlClosure ⟨_, h⟩ = a • pullM ha hT (BoundedDomain.curlClosure u) := by
  have hc : Continuous fun p : BoundedDomain.L2M Ω' × BoundedDomain.L2M Ω' =>
      (pullM ha hT p.1, a • pullM ha hT p.2) := by fun_prop
  have hmem := map_mem_closure hc (BoundedDomain.mem_closure_curlClosure hΩ' hb' u)
    (fun p hp => curlGraph_pull ha hT hp)
  rw [← BoundedDomain.coe_topologicalClosure_curlGraphSub, ← BoundedDomain.curlClosure_graph hΩ hb]
    at hmem
  exact ⟨LinearPMap.mem_domain_of_mem_graph hmem, BoundedDomain.apply_eq_of_mem_graph hmem _⟩

include hΩ hb hΩ' hb' in
theorem gradClosure_pull (u : (BoundedDomain.gradClosure (Ω := Ω')).domain) :
    ∃ h : pullV ha hT u ∈ (BoundedDomain.gradClosure (Ω := Ω)).domain,
      BoundedDomain.gradClosure ⟨_, h⟩ = a • pullM ha hT (BoundedDomain.gradClosure u) := by
  have hc : Continuous fun p : BoundedDomain.L2V Ω' × BoundedDomain.L2M Ω' =>
      (pullV ha hT p.1, a • pullM ha hT p.2) := by fun_prop
  have hmem := map_mem_closure hc (BoundedDomain.mem_closure_gradClosure hΩ' hb' u)
    (fun p hp => gradGraph_pull ha hT hp)
  replace hmem : (pullV ha hT u, a • pullM ha hT (BoundedDomain.gradClosure u)) ∈
      (BoundedDomain.gradClosure (Ω := Ω)).graph := by
    rw [BoundedDomain.gradClosure_graph hΩ hb]; exact hmem
  exact ⟨LinearPMap.mem_domain_of_mem_graph hmem, BoundedDomain.apply_eq_of_mem_graph hmem _⟩

omit hΩ hb hΩ' hb' in
theorem pullFun_pullFun {a' : ℝ} {b' : R3} (ha' : a' ≠ 0)
    (hT' : ∀ y, y ∈ Ω' ↔ a' • y + b' ∈ Ω) (hinv : ∀ x, a' • (a • x + b) + b' = x)
    (g : BoundedDomain.L2 Ω) : pullFun ha hT (pullFun ha' hT' g) = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pullFun ha hT (pullFun ha' hT' g),
    comp_ae_eq ha hT (coeFn_pullFun ha' hT' g)] with x h1 h2
  rw [h1, h2]
  simp only [affH_apply, hinv]

end Dilation

/-! ## Conjugating a Hilbert complex by scaled unitaries -/

section Conj

variable {X Y X' Y' : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X'] [InnerProductSpace ℝ X'] [CompleteSpace X']
  [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [CompleteSpace Y']

omit [CompleteSpace Y] [CompleteSpace Y'] in
/-- Adjoints under scaled unitary conjugation: if `U V = id`, `U' V' = id`, `U`, `U'` multiply
inner products by `λ`, and `V' (d x) = a d' (V x)` on `D(d)`, then `U'` maps `D(d'*)` into `D(d*)`
with `d* (U' y) = a U (d'* y)`. -/
theorem adjoint_conj {d : X →ₗ.[ℝ] Y} {d' : X' →ₗ.[ℝ] Y'} (hd : Dense (d.domain : Set X))
    (hd' : Dense (d'.domain : Set X'))
    {U : X' →L[ℝ] X} {U' : Y' →L[ℝ] Y} {V : X →L[ℝ] X'} {V' : Y →L[ℝ] Y'} {lam a : ℝ}
    (hUV : ∀ x, U (V x) = x) (hUV' : ∀ y, U' (V' y) = y)
    (hU : ∀ p q, ⟪U p, U q⟫ = lam * ⟪p, q⟫) (hU' : ∀ p q, ⟪U' p, U' q⟫ = lam * ⟪p, q⟫)
    (hVdom : ∀ x : d.domain, V x ∈ d'.domain)
    (hV : ∀ x : d.domain, V' (d x) = a • d' ⟨V x, hVdom x⟩) (y : d'†.domain) :
    ∃ h : U' y ∈ d†.domain, d† ⟨U' y, h⟩ = a • U (d'† y) := by
  have key : ∀ x : d.domain, ⟪a • U (d'† y), (x : X)⟫ = ⟪U' y, d x⟫ := by
    intro x
    have e1 := LinearPMap.adjoint_isFormalAdjoint hd' y ⟨V x, hVdom x⟩
    calc ⟪a • U (d'† y), (x : X)⟫ = a * ⟪U (d'† y), U (V x)⟫ := by
            rw [real_inner_smul_left, hUV]
        _ = a * (lam * ⟪(d'† y : X'), V x⟫) := by rw [hU]
        _ = lam * ⟪(y : Y'), a • d' ⟨V x, hVdom x⟩⟫ := by
            rw [real_inner_smul_right]; simp only at e1; rw [e1]; ring
        _ = ⟪U' y, d x⟫ := by
            rw [← hV, ← hU', hUV']
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq hd ⟨_, hmem⟩ key⟩

theorem lpmap_congr {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ₗ.[ℝ] F) {x y : E} (hx : x ∈ f.domain) (hy : y ∈ f.domain) (h : x = y) :
    f ⟨x, hx⟩ = f ⟨y, hy⟩ := by subst h; rfl

end Conj

section ConjComplex

open Feec.Constraints Feec.HilbertComplex2

variable {W0 W1 W2 W0' W1' W2' : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  [NormedAddCommGroup W0'] [InnerProductSpace ℝ W0'] [CompleteSpace W0']
  [NormedAddCommGroup W1'] [InnerProductSpace ℝ W1'] [CompleteSpace W1']
  [NormedAddCommGroup W2'] [InnerProductSpace ℝ W2'] [CompleteSpace W2']

/-- A triple of maps acting on states. -/
def totMap (U0 : W0' →L[ℝ] W0) (U1 : W1' →L[ℝ] W1) (U2 : W2' →L[ℝ] W2) :
    Tot W0' W1' W2' →L[ℝ] Tot W0 W1 W2 :=
  (Constraints.totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.toContinuousLinearMap ∘L
    (U0.prodMap (U1.prodMap U2)) ∘L
    (Constraints.totL (W0 := W0') (W1 := W1') (W2 := W2')).toContinuousLinearMap

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] [CompleteSpace W0']
  [CompleteSpace W1'] [CompleteSpace W2'] in
theorem tot_totMap (U0 : W0' →L[ℝ] W0) (U1 : W1' →L[ℝ] W1) (U2 : W2' →L[ℝ] W2)
    (x : Tot W0' W1' W2') :
    tot W0 W1 W2 (totMap U0 U1 U2 x) =
      (U0 (tot _ _ _ x).1, U1 (tot _ _ _ x).2.1, U2 (tot _ _ _ x).2.2) := by
  simp [totMap]; rfl

variable (H : HilbertComplex2 W0 W1 W2) (H' : HilbertComplex2 W0' W1' W2')
  {U0 : W0' →L[ℝ] W0} {U1 : W1' →L[ℝ] W1} {U2 : W2' →L[ℝ] W2}
  {V0 : W0 →L[ℝ] W0'} {V1 : W1 →L[ℝ] W1'} {V2 : W2 →L[ℝ] W2'} {lam a : ℝ}

/-- **Conjugation of the Hodge wave operator.** If `U_k` (with right inverses `V_k`) multiply
inner products by `λ` and intertwine the differentials up to the factor `a`
(`d (U x) = a U (d' x)`, `V (d x) = a d' (V x)`), then `U = (U0, U1, U2)` maps `D(L')` into
`D(L)` and `L (U x) = a U (L' x)`. -/
theorem waveOp_conj
    (hUV0 : ∀ x, U0 (V0 x) = x) (hUV1 : ∀ x, U1 (V1 x) = x) (hUV2 : ∀ x, U2 (V2 x) = x)
    (hU0 : ∀ p q, ⟪U0 p, U0 q⟫ = lam * ⟪p, q⟫) (hU1 : ∀ p q, ⟪U1 p, U1 q⟫ = lam * ⟪p, q⟫)
    (hU2 : ∀ p q, ⟪U2 p, U2 q⟫ = lam * ⟪p, q⟫)
    (hd0 : ∀ x : H'.d0.domain, ∃ h : U0 x ∈ H.d0.domain, H.d0 ⟨_, h⟩ = a • U1 (H'.d0 x))
    (hd1 : ∀ x : H'.d1.domain, ∃ h : U1 x ∈ H.d1.domain, H.d1 ⟨_, h⟩ = a • U2 (H'.d1 x))
    (he0 : ∀ x : H.d0.domain, ∃ h : V0 x ∈ H'.d0.domain, V1 (H.d0 x) = a • H'.d0 ⟨_, h⟩)
    (he1 : ∀ x : H.d1.domain, ∃ h : V1 x ∈ H'.d1.domain, V2 (H.d1 x) = a • H'.d1 ⟨_, h⟩)
    (x : H'.waveOp.domain) :
    ∃ h : totMap U0 U1 U2 x ∈ H.waveOp.domain,
      H.waveOp ⟨_, h⟩ = a • totMap U0 U1 U2 (H'.waveOp x) := by
  have hx := (Constraints.mem_domL (H := H')).1 x.2
  obtain ⟨h0, ⟨h1, h1s⟩, h2⟩ := hx
  obtain ⟨g0, e0⟩ := hd0 ⟨_, h0⟩
  obtain ⟨g1, e1⟩ := hd1 ⟨_, h1⟩
  obtain ⟨g1s, e1s⟩ := adjoint_conj H.dense0 H'.dense0 hUV0 hUV1 hU0 hU1
    (fun x => (he0 x).1) (fun x => (he0 x).2) ⟨_, h1s⟩
  obtain ⟨g2, e2⟩ := adjoint_conj H.dense1 H'.dense1 hUV1 hUV2 hU1 hU2
    (fun x => (he1 x).1) (fun x => (he1 x).2) ⟨_, h2⟩
  have hmem : totMap U0 U1 U2 x ∈ H.waveOp.domain := by
    change _ ∈ H.domL
    rw [Constraints.mem_domL, tot_totMap]
    exact ⟨g0, ⟨g1, g1s⟩, g2⟩
  refine ⟨hmem, ?_⟩
  apply (tot W0 W1 W2).injective
  rw [Constraints.tot_waveOp (H := H) ⟨_, hmem⟩, map_smul, tot_totMap, Constraints.tot_waveOp]
  have q0 : H.d0 (H.pr0 ⟨_, hmem⟩) = H.d0 ⟨_, g0⟩ := lpmap_congr _ _ _ (by simp [tot_totMap])
  have q1 : H.d1 (H.prV1 ⟨_, hmem⟩) = H.d1 ⟨_, g1⟩ := lpmap_congr _ _ _ (by simp [tot_totMap])
  have q1s : H.d0† (H.prV1s ⟨_, hmem⟩) = H.d0† ⟨_, g1s⟩ :=
    lpmap_congr _ _ _ (by simp [tot_totMap])
  have q2 : H.d1† (H.prV2s ⟨_, hmem⟩) = H.d1† ⟨_, g2⟩ := lpmap_congr _ _ _ (by simp [tot_totMap])
  have r0 : H'.d0 (H'.pr0 ⟨x.1, x.2⟩) = H'.d0 ⟨_, h0⟩ := rfl
  have r1 : H'.d1 (H'.prV1 ⟨x.1, x.2⟩) = H'.d1 ⟨_, h1⟩ := rfl
  have r1s : H'.d0† (H'.prV1s ⟨x.1, x.2⟩) = H'.d0† ⟨_, h1s⟩ := rfl
  have r2 : H'.d1† (H'.prV2s ⟨x.1, x.2⟩) = H'.d1† ⟨_, h2⟩ := rfl
  simp only [q0, q1, q1s, q2, r0, r1, r1s, r2, e0, e1, e1s, e2, map_neg, map_add, smul_neg,
    smul_add, Prod.smul_mk]

end ConjComplex
section Rescale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {L : E →ₗ.[ℝ] E}

/-- **Time rescaling of a group**: `t ↦ e^{(ct) L}` is the orthogonal group generated by `c L`. -/
def rescaleGroup (G : UnitaryGroupGenerator L) (c : ℝ) (hc : c ≠ 0) :
    UnitaryGroupGenerator (c • L) where
  S t := G.S (c * t)
  map_zero := by simp [G.map_zero]
  map_add s t := by rw [mul_add, G.map_add]
  norm_map t x := G.norm_map _ x
  continuous_apply x := (G.continuous_apply x).comp (continuous_const.mul continuous_id)
  mem_domain_iff x := by
    rw [LinearPMap.smul_domain, G.mem_domain_iff]
    constructor
    · intro h
      have h' : DifferentiableAt ℝ (fun t : ℝ => c * t) 0 := by fun_prop
      rw [show (0 : ℝ) = c * 0 by simp] at h
      exact h.comp (0 : ℝ) h'
    · intro h
      have h' : DifferentiableAt ℝ (fun t : ℝ => c⁻¹ * t) 0 := by fun_prop
      rw [show (0 : ℝ) = c⁻¹ * 0 by simp] at h
      have := h.comp (0 : ℝ) h'
      simp only [Function.comp_def, ← mul_assoc, mul_inv_cancel₀ hc, one_mul] at this
      exact this
  hasDerivAt_zero x := by
    have hx : (x : E) ∈ L.domain := x.2
    have h1 := G.hasDerivAt_zero ⟨x, hx⟩
    have h2 : HasDerivAt (fun t : ℝ => c * t) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
    rw [show (0 : ℝ) = c * 0 by simp] at h1
    have := h1.scomp (0 : ℝ) h2
    rw [LinearPMap.smul_apply]
    exact this

theorem rescaleGroup_S (G : UnitaryGroupGenerator L) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    (rescaleGroup G c hc).S t = G.S (c * t) := rfl

end Rescale

/-! ## The thesis' complex under `x ↦ a x + b` -/

noncomputable section PullComplex

open Feec.Constraints Feec.HilbertComplex2

variable {a : ℝ} {b : R3} {Ω Ω' : Set R3} (ha : a ≠ 0) (hT : ∀ x, x ∈ Ω ↔ a • x + b ∈ Ω')
  (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hΩ' : IsOpen Ω')
  (hb' : Bornology.IsBounded Ω')

include ha

theorem affine_inv_left (x : R3) : a⁻¹ • (a • x + b) + -(a⁻¹ • b) = x := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul]; abel

theorem affine_inv_right (y : R3) : a • (a⁻¹ • y + -(a⁻¹ • b)) + b = y := by
  rw [smul_add, smul_smul, mul_inv_cancel₀ ha, one_smul, smul_neg, smul_smul,
    mul_inv_cancel₀ ha, one_smul]; abel

include hT in
/-- The inverse map `y ↦ a⁻¹ y - a⁻¹ b` carries `Ω'` onto `Ω`. -/
theorem hT_inv : ∀ y, y ∈ Ω' ↔ a⁻¹ • y + -(a⁻¹ • b) ∈ Ω := by
  intro y
  rw [hT, affine_inv_right ha]

theorem pull_inv (g : BoundedDomain.L2 Ω) :
    pullFun ha hT (pullFun (inv_ne_zero ha) (hT_inv ha hT) g) = g :=
  pullFun_pullFun ha hT (inv_ne_zero ha) (hT_inv ha hT) (affine_inv_left ha) g

theorem inv_pull (g : BoundedDomain.L2 Ω') :
    pullFun (inv_ne_zero ha) (hT_inv ha hT) (pullFun ha hT g) = g := by
  refine pullFun_pullFun (inv_ne_zero ha) (hT_inv ha hT) ha hT ?_ g
  intro y; simpa using affine_inv_right ha y

theorem pullM_inv (A : BoundedDomain.L2M Ω) :
    pullM ha hT (pullM (inv_ne_zero ha) (hT_inv ha hT) A) = A :=
  (WithLp.ext_iff 2).2 (funext fun ij => pull_inv ha hT (A ij))

theorem pullV_inv (u : BoundedDomain.L2V Ω) :
    pullV ha hT (pullV (inv_ne_zero ha) (hT_inv ha hT) u) = u :=
  (WithLp.ext_iff 2).2 (funext fun i => pull_inv ha hT (u i))

theorem inv_pullM (A : BoundedDomain.L2M Ω') :
    pullM (inv_ne_zero ha) (hT_inv ha hT) (pullM ha hT A) = A :=
  (WithLp.ext_iff 2).2 (funext fun ij => inv_pull ha hT (A ij))

include hΩ hb hΩ' hb' in
/-- `D(d0*) = H(div)` is carried along: `d0* (B ∘ T) = a (d0'* B) ∘ T`. -/
theorem adj0_pull (B : (BoundedDomain.gradClosure (Ω := Ω'))†.domain) :
    ∃ h : pullM ha hT B ∈ (BoundedDomain.gradClosure (Ω := Ω))†.domain,
      (BoundedDomain.gradClosure (Ω := Ω))† ⟨_, h⟩ = a • pullV ha hT
        ((BoundedDomain.gradClosure (Ω := Ω'))† B) := by
  refine adjoint_conj (BoundedDomain.dense_domain_gradClosure hΩ hb)
    (BoundedDomain.dense_domain_gradClosure hΩ' hb') (pullV_inv ha hT) (pullM_inv ha hT)
    (inner_pullV ha hT) (inner_pullM ha hT)
    (fun x => (gradClosure_pull (inv_ne_zero ha) (hT_inv ha hT) hΩ' hb' hΩ hb x).1) (fun x => ?_) B
  obtain ⟨h, e⟩ := gradClosure_pull (inv_ne_zero ha) (hT_inv ha hT) hΩ' hb' hΩ hb x
  rw [e, smul_smul, mul_inv_cancel₀ ha, one_smul]

include hΩ hb hΩ' hb' in
/-- `D(d1*) = H(curl)` is carried along: `d1* (B ∘ T) = a (d1'* B) ∘ T`. -/
theorem adj1_pull (B : (BoundedDomain.curlClosure (Ω := Ω'))†.domain) :
    ∃ h : pullM ha hT B ∈ (BoundedDomain.curlClosure (Ω := Ω))†.domain,
      (BoundedDomain.curlClosure (Ω := Ω))† ⟨_, h⟩ = a • pullM ha hT
        ((BoundedDomain.curlClosure (Ω := Ω'))† B) := by
  refine adjoint_conj (BoundedDomain.dense_domain_curlClosure hΩ hb)
    (BoundedDomain.dense_domain_curlClosure hΩ' hb') (pullM_inv ha hT) (pullM_inv ha hT)
    (inner_pullM ha hT) (inner_pullM ha hT)
    (fun x => (curlClosure_pull (inv_ne_zero ha) (hT_inv ha hT) hΩ' hb' hΩ hb x).1) (fun x => ?_) B
  obtain ⟨h, e⟩ := curlClosure_pull (inv_ne_zero ha) (hT_inv ha hT) hΩ' hb' hΩ hb x
  rw [e, smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- Pull-back of states `(σ, E, B) ↦ (σ ∘ T, E ∘ T, B ∘ T)`. -/
def pullX : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω') →L[ℝ]
    Tot (BoundedDomain.L2V Ω) (BoundedDomain.L2M Ω) (BoundedDomain.L2M Ω) :=
  totMap (pullV ha hT) (pullM ha hT) (pullM ha hT)

include hΩ hb hΩ' hb' in
/-- **The Hodge wave operators are conjugate**: `L (x ∘ T) = a (L' x) ∘ T`. -/
theorem pullX_waveOp (x : (BoundedDomain.thesisComplex hΩ' hb').waveOp.domain) :
    ∃ h : pullX ha hT x ∈ (BoundedDomain.thesisComplex hΩ hb).waveOp.domain,
      (BoundedDomain.thesisComplex hΩ hb).waveOp ⟨_, h⟩ =
        a • pullX ha hT ((BoundedDomain.thesisComplex hΩ' hb').waveOp x) := by
  refine waveOp_conj (BoundedDomain.thesisComplex hΩ hb) (BoundedDomain.thesisComplex hΩ' hb')
    (pullV_inv ha hT) (pullM_inv ha hT) (pullM_inv ha hT)
    (inner_pullV ha hT) (inner_pullM ha hT) (inner_pullM ha hT)
    (gradClosure_pull ha hT hΩ hb hΩ' hb') (curlClosure_pull ha hT hΩ hb hΩ' hb')
    (fun x => ?_) (fun x => ?_) x
  · obtain ⟨h, e⟩ := gradClosure_pull (inv_ne_zero ha) (hT_inv ha hT) hΩ' hb' hΩ hb x
    refine ⟨h, ?_⟩
    change _ = a • BoundedDomain.gradClosure ⟨_, h⟩
    rw [e, smul_smul, mul_inv_cancel₀ ha, one_smul]; rfl
  · obtain ⟨h, e⟩ := curlClosure_pull (inv_ne_zero ha) (hT_inv ha hT) hΩ' hb' hΩ hb x
    refine ⟨h, ?_⟩
    change _ = a • BoundedDomain.curlClosure ⟨_, h⟩
    rw [e, smul_smul, mul_inv_cancel₀ ha, one_smul]; rfl

include hΩ hb hΩ' hb' in
/-- `L²(TSD)` is carried along. -/
theorem pullM_mem_TSD {B : BoundedDomain.L2M Ω'} (hB : B ∈ BoundedDomain.TSD Ω') :
    pullM ha hT B ∈ BoundedDomain.TSD Ω := by
  obtain ⟨h1, h2, h3⟩ := hB
  refine ⟨fun i j => by simp only [pullM_apply, h1 i j], ?_, ?_⟩
  · simp only [pullM_apply]
    have := map_sum (pullL ha hT) (fun i => B (i, i)) Finset.univ
    simp only [pullL_apply] at this
    rw [← this, h2]; exact map_zero (pullL ha hT)
  · have hk := (BoundedDomain.mem_ker_adjoint_gradClosure_iff hΩ' hb').2 h3
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hk
    obtain ⟨h, e⟩ := adj0_pull ha hT hΩ hb hΩ' hb' y
    refine (BoundedDomain.mem_ker_adjoint_gradClosure_iff hΩ hb).1
      (LinearPMap.mem_ker_iff.2 ⟨⟨_, h⟩, by simp only [hy], ?_⟩)
    rw [e, hy0, map_zero, smul_zero]

theorem tot_pullX (x : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω')) :
    tot _ _ _ (pullX ha hT x) = (pullV ha hT (tot _ _ _ x).1, pullM ha hT (tot _ _ _ x).2.1,
      pullM ha hT (tot _ _ _ x).2.2) := tot_totMap _ _ _ x

include hΩ hb hΩ' hb' in
theorem pullX_mem_Kc {x : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω')}
    (hx : x ∈ Kc (BoundedDomain.L2V Ω') (BoundedDomain.TSD Ω') (BoundedDomain.TSD Ω')) :
    pullX ha hT x ∈ Kc (BoundedDomain.L2V Ω) (BoundedDomain.TSD Ω) (BoundedDomain.TSD Ω) := by
  rw [mem_Kc] at hx ⊢
  obtain ⟨h0, h1, h2⟩ := hx
  rw [tot_pullX]
  exact ⟨by dsimp only; rw [h0, map_zero], pullM_mem_TSD ha hT hΩ hb hΩ' hb' h1,
    pullM_mem_TSD ha hT hΩ hb hΩ' hb' h2⟩

theorem pullX_pullX_inv (x : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω')) :
    pullX (inv_ne_zero ha) (hT_inv ha hT) (pullX ha hT x) = x := by
  apply (tot _ _ _).injective
  rw [tot_pullX, tot_pullX]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact (WithLp.ext_iff 2).2 (funext fun i => inv_pull ha hT _)
  · exact inv_pullM ha hT _
  · exact inv_pullM ha hT _

theorem pullX_injective : Function.Injective (pullX ha hT) := fun x y h => by
  rw [← pullX_pullX_inv ha hT x, h, pullX_pullX_inv]

theorem pullX_ini (E₀ B₀ : BoundedDomain.L2M Ω') :
    pullX ha hT (ini (BoundedDomain.L2V Ω') E₀ B₀) =
      ini (BoundedDomain.L2V Ω) (pullM ha hT E₀) (pullM ha hT B₀) := by
  apply (tot _ _ _).injective
  rw [tot_pullX, tot_ini, tot_ini, map_zero]

include hΩ hb hΩ' hb' in
/-- **The groups are conjugate**: for every orthogonal group `G'` generated by `-L'` on `Ω'` and
`G` generated by `-L` on `Ω`, `(G'.S (a t) x) ∘ T = G.S t (x ∘ T)`. -/
theorem pullX_group (G' : UnitaryGroupGenerator (-(BoundedDomain.thesisComplex hΩ' hb').waveOp))
    (G : UnitaryGroupGenerator (-(BoundedDomain.thesisComplex hΩ hb).waveOp)) (t : ℝ)
    (x : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω')) :
    pullX ha hT (G'.S (a * t) x) = G.S t (pullX ha hT x) := by
  have hdom : ∀ y : (a • -(BoundedDomain.thesisComplex hΩ' hb').waveOp).domain,
      pullX ha hT y ∈ (-(BoundedDomain.thesisComplex hΩ hb).waveOp).domain := fun y =>
    (pullX_waveOp ha hT hΩ hb hΩ' hb' ⟨y, y.2⟩).1
  refine Box.group_intertwine (rescaleGroup G' a ha) G (pullX ha hT) hdom (fun y => ?_)
    (isSkewSymm_neg (Constraints.waveOp_isSkewSymm _))
    (BoundedDomain.thesisComplex hΩ' hb').neg_waveOp_isSkewAdjoint.dense_domain t x
  obtain ⟨h, e⟩ := pullX_waveOp ha hT hΩ hb hΩ' hb' ⟨y, y.2⟩
  rw [LinearPMap.smul_apply, LinearPMap.neg_apply, LinearPMap.neg_apply, map_smul, map_neg,
    smul_neg]
  congr 1
  exact e.symm

end PullComplex

/-! ## Transfer to every cube -/

section Cube

open Feec.Constraints Feec.HilbertComplex2

variable {a : ℝ} {b : R3} {Ω' : Set R3} (ha : 0 < a) (hT : ∀ x, x ∈ Qr ↔ a • x + b ∈ Ω')
  (hΩ' : IsOpen Ω') (hb' : Bornology.IsBounded Ω')

include ha hT in
theorem pullX_group_Q (G' : UnitaryGroupGenerator (-(BoundedDomain.thesisComplex hΩ' hb').waveOp))
    (t : ℝ) (x : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω')) :
    pullX ha.ne' hT (G'.S t x) = cxQ.waveGroup.S (t / a) (pullX ha.ne' hT x) := by
  rw [← pullX_group ha.ne' hT isOpen_Qr isBounded_Qr hΩ' hb' G' cxQ.waveGroup, mul_div_cancel₀ _ ha.ne']

include ha hT in
/-- **On every image `Ω' = aQ + b` of the cube (`a > 0`), with the thesis' boundary conditions,
forward invariance of `K = {0} × L²(TSD) × L²(TSD)` forces stationarity**, for every orthogonal
group generated by `-L` of `Feec.BoundedDomain.thesisComplex` on `Ω'`. Transferred from
`thesisComplexQ_forward_iff` by the pull-back along `x ↦ a x + b`, which conjugates `L'` to
`a⁻¹ L` (`pullX_waveOp`) and hence the groups up to the time change `t ↦ t / a`
(`pullX_group`). -/
theorem affineCube_forward_iff
    (G' : UnitaryGroupGenerator (-(BoundedDomain.thesisComplex hΩ' hb').waveOp))
    (x : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω')) :
    (∀ t, 0 ≤ t → G'.S t x ∈ Kc (BoundedDomain.L2V Ω') (BoundedDomain.TSD Ω')
      (BoundedDomain.TSD Ω')) ↔
      x ∈ Kc (BoundedDomain.L2V Ω') (BoundedDomain.TSD Ω') (BoundedDomain.TSD Ω') ∧
        ∀ t, G'.S t x = x := by
  constructor
  · intro hf
    have hK := hf 0 le_rfl
    rw [G'.map_zero] at hK
    have hfb : ∀ t, 0 ≤ t → cxQ.waveGroup.S t (pullX ha.ne' hT x) ∈
        Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr) := by
      intro t ht
      rw [← pullX_group ha.ne' hT isOpen_Qr isBounded_Qr hΩ' hb' G' cxQ.waveGroup]
      exact pullX_mem_Kc ha.ne' hT isOpen_Qr isBounded_Qr hΩ' hb' (hf _ (mul_nonneg ha.le ht))
    obtain ⟨-, hs⟩ := (thesisComplexQ_forward_iff cxQ.waveGroup _).1 hfb
    exact ⟨hK, fun t => pullX_injective ha.ne' hT (by rw [pullX_group_Q ha hT, hs])⟩
  · rintro ⟨hK, hs⟩ t _
    rw [hs t]; exact hK

include ha hT in
/-- `K*` on `Ω' = aQ + b` consists exactly of the stationary data in `K`, for every group. -/
theorem affineCube_mem_Kmax_iff
    (G' : UnitaryGroupGenerator (-(BoundedDomain.thesisComplex hΩ' hb').waveOp))
    (x : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω')) :
    x ∈ Kmax G' (Kc (BoundedDomain.L2V Ω') (BoundedDomain.TSD Ω') (BoundedDomain.TSD Ω')) ↔
      x ∈ Kc (BoundedDomain.L2V Ω') (BoundedDomain.TSD Ω') (BoundedDomain.TSD Ω') ∧
        ∀ t, G'.S t x = x :=
  ⟨fun hx => (affineCube_forward_iff ha hT hΩ' hb' G' x).1 fun t _ => hx t,
    fun ⟨hK, hs⟩ t => by rw [hs t]; exact hK⟩

include ha hT in
/-- **`K*` on `Ω' = aQ + b`, explicitly**: `x ∈ K*` iff `x = (0, 0, B₀)` with `B₀ ∈ L²(TSD)(Ω')`,
`B₀ ∈ D(d1*)` and `d1* B₀ = 0` (weak curl `0`, no boundary condition). -/
theorem affineCube_mem_Kmax_iff'
    (G' : UnitaryGroupGenerator (-(BoundedDomain.thesisComplex hΩ' hb').waveOp))
    (x : Tot (BoundedDomain.L2V Ω') (BoundedDomain.L2M Ω') (BoundedDomain.L2M Ω')) :
    x ∈ Kmax G' (Kc (BoundedDomain.L2V Ω') (BoundedDomain.TSD Ω') (BoundedDomain.TSD Ω')) ↔
      ∃ B ∈ BoundedDomain.TSD Ω', ∃ h : B ∈ (BoundedDomain.thesisComplex hΩ' hb').d1†.domain,
        (BoundedDomain.thesisComplex hΩ' hb').d1† ⟨B, h⟩ = 0 ∧
          x = ini (BoundedDomain.L2V Ω') 0 B := by
  have ha0 := ha.ne'
  constructor
  · intro hx
    obtain ⟨hK, hs⟩ := (affineCube_mem_Kmax_iff ha hT hΩ' hb' G' x).1 hx
    have hmax : pullX ha0 hT x ∈ Kmax cxQ.waveGroup
        (Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr)) := fun t => by
      rw [← pullX_group ha0 hT isOpen_Qr isBounded_Qr hΩ' hb' G' cxQ.waveGroup, hs]
      exact pullX_mem_Kc ha0 hT isOpen_Qr isBounded_Qr hΩ' hb' hK
    obtain ⟨B₀, hB₀, hd, hd0, he⟩ := (thesisComplexQ_mem_Kmax_iff' cxQ.waveGroup _).1 hmax
    have hx' : x = ini (BoundedDomain.L2V Ω') 0
        (pullM (inv_ne_zero ha0) (hT_inv ha0 hT) B₀) := by
      rw [← pullX_pullX_inv ha0 hT x, he, pullX_ini, map_zero]
    obtain ⟨h, e⟩ := adj1_pull (inv_ne_zero ha0) (hT_inv ha0 hT) hΩ' hb' isOpen_Qr isBounded_Qr
      ⟨B₀, hd⟩
    refine ⟨_, pullM_mem_TSD (inv_ne_zero ha0) (hT_inv ha0 hT) hΩ' hb' isOpen_Qr isBounded_Qr hB₀,
      h, ?_, hx'⟩
    refine e.trans ?_
    have hd0' : (BoundedDomain.curlClosure (Ω := Qr))† ⟨B₀, hd⟩ = 0 := hd0
    rw [hd0', map_zero, smul_zero]
  · rintro ⟨B, hBT, hB, hd, rfl⟩
    have hK : ini (BoundedDomain.L2V Ω') 0 B ∈
        Kc (BoundedDomain.L2V Ω') (BoundedDomain.TSD Ω') (BoundedDomain.TSD Ω') := by
      rw [mem_Kc, tot_ini]; exact ⟨rfl, Submodule.zero_mem _, hBT⟩
    obtain ⟨h, e⟩ := adj1_pull ha0 hT isOpen_Qr isBounded_Qr hΩ' hb' ⟨B, hB⟩
    have hmax : pullX ha0 hT (ini (BoundedDomain.L2V Ω') 0 B) ∈ Kmax cxQ.waveGroup
        (Kc (BoundedDomain.L2V Qr) (BoundedDomain.TSD Qr) (BoundedDomain.TSD Qr)) := by
      rw [thesisComplexQ_mem_Kmax_iff', pullX_ini, map_zero]
      refine ⟨_, pullM_mem_TSD ha0 hT isOpen_Qr isBounded_Qr hΩ' hb' hBT, h, ?_, rfl⟩
      refine e.trans ?_
      have hd' : (BoundedDomain.curlClosure (Ω := Ω'))† ⟨B, hB⟩ = 0 := hd
      rw [hd', map_zero, smul_zero]
    obtain ⟨-, hs⟩ := (thesisComplexQ_mem_Kmax_iff cxQ.waveGroup _).1 hmax
    refine (affineCube_mem_Kmax_iff ha hT hΩ' hb' G' _).2 ⟨hK, fun t => pullX_injective ha0 hT ?_⟩
    rw [pullX_group_Q ha hT, hs]

end Cube

/-! ## Arbitrary open cubes, and `(0, π)³` -/

noncomputable section OpenCube

open Feec.Constraints Feec.HilbertComplex2

/-- The open cube `∏ᵢ (bᵢ, bᵢ + s)` with corner `b` and side `s`. -/
def openCube (b : R3) (s : ℝ) : Set R3 := univ.pi fun i => Ioo (b i) (b i + s)

theorem isOpen_openCube (b : R3) (s : ℝ) : IsOpen (openCube b s) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem isBounded_openCube (b : R3) (s : ℝ) : Bornology.IsBounded (openCube b s) :=
  (Metric.isBounded_Icc b fun i => b i + s).subset fun _ hy =>
    ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩

/-- `x ↦ 2s x + b` maps `Q = (0, ½)³` onto `openCube b s`. -/
theorem mem_Qr_iff_openCube {s : ℝ} (hs : 0 < s) (b : R3) (x : R3) :
    x ∈ Qr ↔ (2 * s) • x + b ∈ openCube b s := by
  simp only [Qr, openCube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

variable {b : R3} {s : ℝ} (hs : 0 < s)

/-- The thesis' complex `H̊¹ → H̊(curl) → L²` on the open cube `∏ᵢ (bᵢ, bᵢ + s)`. -/
abbrev cxCube (b : R3) (s : ℝ) := BoundedDomain.thesisComplex (isOpen_openCube b s)
  (isBounded_openCube b s)

include hs in
/-- **On every open cube with the thesis' boundary conditions, forward invariance of
`K = {0} × L²(TSD) × L²(TSD)` forces stationarity**, for every orthogonal group generated by
`-L` of `Feec.BoundedDomain.thesisComplex` (e.g. Stone's group). -/
theorem openCube_forward_iff (G : UnitaryGroupGenerator (-(cxCube b s).waveOp))
    (x : Tot (BoundedDomain.L2V (openCube b s)) (BoundedDomain.L2M (openCube b s))
      (BoundedDomain.L2M (openCube b s))) :
    (∀ t, 0 ≤ t → G.S t x ∈ Kc (BoundedDomain.L2V (openCube b s))
      (BoundedDomain.TSD (openCube b s)) (BoundedDomain.TSD (openCube b s))) ↔
      x ∈ Kc (BoundedDomain.L2V (openCube b s)) (BoundedDomain.TSD (openCube b s))
        (BoundedDomain.TSD (openCube b s)) ∧ ∀ t, G.S t x = x :=
  affineCube_forward_iff (by positivity) (mem_Qr_iff_openCube hs b) _ _ G x

include hs in
/-- **`K*` on every open cube with the thesis' boundary conditions**: `x ∈ K*` iff
`x = (0, 0, B₀)` with `B₀ ∈ L²(TSD)` having weak curl `0`, for every group generated by `-L`. -/
theorem openCube_mem_Kmax_iff' (G : UnitaryGroupGenerator (-(cxCube b s).waveOp))
    (x : Tot (BoundedDomain.L2V (openCube b s)) (BoundedDomain.L2M (openCube b s))
      (BoundedDomain.L2M (openCube b s))) :
    x ∈ Kmax G (Kc (BoundedDomain.L2V (openCube b s)) (BoundedDomain.TSD (openCube b s))
      (BoundedDomain.TSD (openCube b s))) ↔
      ∃ B ∈ BoundedDomain.TSD (openCube b s), ∃ h : B ∈ (cxCube b s).d1†.domain,
        (cxCube b s).d1† ⟨B, h⟩ = 0 ∧ x = ini (BoundedDomain.L2V (openCube b s)) 0 B :=
  affineCube_mem_Kmax_iff' (by positivity) (mem_Qr_iff_openCube hs b) _ _ G x

/-- The cube `(0, π)³` of the task statement is `openCube 0 π`. -/
theorem openCube_zero_pi : openCube 0 Real.pi = univ.pi fun _ => Ioo (0 : ℝ) Real.pi := by
  simp [openCube]

/-- **The cube `(0, π)³`**: for Stone's group of the thesis' complex on `(0, π)³`, `K*` is
`{(0, 0, B₀) : B₀ ∈ L²(TSD), weak curl B₀ = 0}`, and these are exactly the stationary data
in `K`. -/
theorem piCube_mem_Kmax_iff
    (x : Tot (BoundedDomain.L2V (openCube 0 Real.pi)) (BoundedDomain.L2M (openCube 0 Real.pi))
      (BoundedDomain.L2M (openCube 0 Real.pi))) :
    (x ∈ Kmax (cxCube 0 Real.pi).waveGroup (Kc (BoundedDomain.L2V (openCube 0 Real.pi))
      (BoundedDomain.TSD (openCube 0 Real.pi)) (BoundedDomain.TSD (openCube 0 Real.pi))) ↔
      ∃ B ∈ BoundedDomain.TSD (openCube 0 Real.pi), ∃ h : B ∈ (cxCube 0 Real.pi).d1†.domain,
        (cxCube 0 Real.pi).d1† ⟨B, h⟩ = 0 ∧
          x = ini (BoundedDomain.L2V (openCube 0 Real.pi)) 0 B) ∧
    (x ∈ Kmax (cxCube 0 Real.pi).waveGroup (Kc (BoundedDomain.L2V (openCube 0 Real.pi))
      (BoundedDomain.TSD (openCube 0 Real.pi)) (BoundedDomain.TSD (openCube 0 Real.pi))) ↔
      x ∈ Kc (BoundedDomain.L2V (openCube 0 Real.pi)) (BoundedDomain.TSD (openCube 0 Real.pi))
        (BoundedDomain.TSD (openCube 0 Real.pi)) ∧
          ∀ t, (cxCube 0 Real.pi).waveGroup.S t x = x) :=
  ⟨openCube_mem_Kmax_iff' Real.pi_pos _ x,
    affineCube_mem_Kmax_iff (by positivity) (mem_Qr_iff_openCube Real.pi_pos 0) _ _ _ x⟩

end OpenCube

end Feec.BoxIdent
