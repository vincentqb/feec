module

public import Feec.Models.Cube.Basic
public import Feec.Models.Cube.ShellExtension

/-!
# The Helmholtz decomposition of test fields on the torus, with `H¹` bounds

Let `uₐ` (`a = 0, 1, 2`) be test functions on `Q = (0, ½)³`, periodized to `𝕋³ = ℝ³/ℤ³` (`U`),
with Fourier coefficients `û(k)` (`uh`). For a finite set of frequencies `F` the truncated
potential `p_F = Σ_{k ∈ F} p̂(k) e_k`, `p̂(k) = -i k · û(k) / (2π |k|²)` (`Pc`), and the remainder
`w = u - ∇p_F - û(0)` (`Wc`) satisfy, by Parseval on `𝕋³`:

* `‖p_F‖ ≤ ‖u‖` (`integral_Pc_le`), `Σₐ ‖wₐ‖² ≤ ‖u‖²` (`sum_integral_Wc_le`), `|û(0)| ≤ ‖u‖`;
* **Gaffney's identity on the torus**: for `k ∈ F`, `ŵ(k)` is the projection of `û(k)` onto
  `k⊥` (`proj_sq`), and `|k|² |ŵ(k)|² = |k × û(k)|²` (Lagrange's identity `lagrange`), so
  `‖∇w‖² ≤ ‖curl u‖² + Σ_{k ∉ F} |2πk|² |û(k)|²` (`sum_integral_partialT_Wc_le`); the tail is
  `≤ ‖u‖²` for a suitable `F` (`exists_tail_le`).

Back on `ℝ³` (`pR`, `wR`, `cR`, real parts of the lifts), on the unit cell `(-¼, ¾]³ ⊇ Q̄`
(`cell`, where the periodization of `u` is `u`) this is the decomposition
`u = ∇p + c + w` with `‖p‖, |cₐ|, ‖wₐ‖ ≤ ‖u‖` and `‖∂ⱼ wₐ‖² ≤ ‖curl u‖² + ‖u‖²`
(**`exists_helmholtz`**). The truncation keeps every function a trigonometric polynomial plus the
periodized `u`, so all of them are smooth; this is the first step of the regular decomposition
of `Feec.Models.Cube.RegularDecomposition`.

## Main results

* `measurePreserving_proj_cell`, `hasSum_sq_mFourierCoeff_of_continuous`, `mFourierCoeff_mFourier`,
  `mFourierCoeff_tpoly`, `partialT_tpoly`, `integral_norm_sq_tpoly`, `eLpNorm_re_comp_proj_le`.
* `lagrange`, `proj_sq`; `sum_norm_sq_coeff_Wc_le`, `nk_mul_sum_coeff_Wc_le`, `norm_sq_pco_le`.
* `integral_Pc_le`, `sum_integral_Wc_le`, **`sum_integral_partialT_Wc_le`**, `exists_tail_le`.
* `per_proj_of_mem_cell`, `wR_eq`, `Nu_eq`, `Ncurl_eq`, **`exists_helmholtz`**.

## References

* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], §2
  (Helmholtz and regular decompositions of `H(curl)`)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §5.4 (Hilbert bases, Parseval)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter Complex UnitAddTorus
open scoped ENNReal NNReal Topology

namespace Feec.Models.Cube.TorusHelmholtz

open Feec.Fourier.TorusWeak Feec.Models.Cube.Geometry

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The torus `𝕋³`. -/
abbrev T3 := UnitAddTorus (Fin 3)

/-! ### Generic facts on `𝕋³` -/

/-- The unit cell `(-¼, ¾]³`. -/
def cell : Set (Fin 3 → ℝ) := univ.pi fun _ => Ioc (-1 / 4 : ℝ) (3 / 4)

theorem measurableSet_cell : MeasurableSet cell :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- `proj : ℝ³ → 𝕋³` is measure preserving from the cell `(-¼, ¾]³`. -/
theorem measurePreserving_proj_cell :
    MeasurePreserving proj (volume.restrict cell) (volume : Measure T3) := by
  have h1 : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Ioc (-1 / 4 : ℝ) (3 / 4))) (volume : Measure UnitAddCircle) := by
    have h := UnitAddCircle.measurePreserving_mk (-1 / 4)
    rw [show (-1 / 4 : ℝ) + 1 = 3 / 4 by norm_num] at h
    have e : (@volume UnitAddCircle (AddCircle.measureSpace 1)) =
        (volume : Measure UnitAddCircle) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]; rfl
    exact e ▸ h
  have h := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ioc (-1 / 4 : ℝ) (3 / 4)))
    (fun _ : Fin 3 => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) fun _ => h1
  rw [← Measure.restrict_pi_pi, ← volume_pi] at h
  exact h

/-- **Parseval** for continuous functions on `𝕋³`. -/
theorem hasSum_sq_mFourierCoeff_of_continuous {f : T3 → ℂ} (hf : Continuous f) :
    HasSum (fun k => ‖mFourierCoeff f k‖ ^ 2) (∫ x, ‖f x‖ ^ 2) := by
  let g : C(T3, ℂ) := ⟨f, hf⟩
  have h := hasSum_sq_mFourierCoeff (g.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp] at h
  have e : ∫ x, ‖(g.toLp 2 volume ℂ : T3 → ℂ) x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := volume) g] with x hx
    rw [hx]; rfl
  rw [e] at h
  exact h

theorem mFourierCoeff_mFourier (m k : Fin 3 → ℤ) :
    mFourierCoeff (mFourier m : T3 → ℂ) k = if k = m then 1 else 0 := by
  rw [← mFourierCoeff_toLp, ← mFourierBasis_repr]
  have : (mFourier m).toLp 2 volume ℂ = mFourierBasis (d := Fin 3) m := by
    rw [coe_mFourierBasis]
  rw [this, HilbertBasis.repr_self, lp.single_apply, Pi.single_apply]

theorem integrable_smul_mFourier {f : T3 → ℂ} (hf : Continuous f) (k : Fin 3 → ℤ) :
    Integrable fun t => mFourier (-k) t • f t :=
  integrable_of_continuous ((mFourier (-k)).continuous.smul hf)

theorem mFourierCoeff_add' {f g : T3 → ℂ} (hf : Continuous f) (hg : Continuous g)
    (k : Fin 3 → ℤ) :
    mFourierCoeff (fun x => f x + g x) k = mFourierCoeff f k + mFourierCoeff g k := by
  simp only [mFourierCoeff, smul_add]
  exact integral_add (integrable_smul_mFourier hf k) (integrable_smul_mFourier hg k)

theorem mFourierCoeff_sub' {f g : T3 → ℂ} (hf : Continuous f) (hg : Continuous g)
    (k : Fin 3 → ℤ) :
    mFourierCoeff (fun x => f x - g x) k = mFourierCoeff f k - mFourierCoeff g k := by
  simp only [mFourierCoeff, smul_sub]
  exact integral_sub (integrable_smul_mFourier hf k) (integrable_smul_mFourier hg k)

theorem mFourierCoeff_const_mul (c : ℂ) (f : T3 → ℂ) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun x => c * f x) k = c * mFourierCoeff f k := by
  simp only [mFourierCoeff, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext t; ring

theorem mFourierCoeff_sum {ι : Type*} (s : Finset ι) {f : ι → T3 → ℂ}
    (hf : ∀ i, Continuous (f i)) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun x => ∑ i ∈ s, f i x) k = ∑ i ∈ s, mFourierCoeff (f i) k := by
  simp only [mFourierCoeff, Finset.smul_sum]
  exact integral_finsetSum s fun i _ => integrable_smul_mFourier (hf i) k

theorem mFourierCoeff_const (c : ℂ) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun _ : T3 => c) k = if k = 0 then c else 0 := by
  have : (fun _ : T3 => c) = fun x => c * mFourier 0 x := by
    funext x; simp [mFourier_zero]
  rw [this, mFourierCoeff_const_mul, mFourierCoeff_mFourier]
  split_ifs <;> simp

/-! ### Trigonometric polynomials -/

/-- The trigonometric polynomial `Σ_{k ∈ F} a_k e_k`. -/
def tpoly (a : (Fin 3 → ℤ) → ℂ) (F : Finset (Fin 3 → ℤ)) (x : T3) : ℂ :=
  ∑ k ∈ F, a k * mFourier k x

theorem isSmooth_tpoly (a : (Fin 3 → ℤ) → ℂ) (F : Finset (Fin 3 → ℤ)) :
    IsSmooth (tpoly a F) := by
  unfold IsSmooth
  have : tpoly a F ∘ proj = fun y => ∑ k ∈ F, a k * (mFourier k ∘ proj) y := rfl
  rw [this]
  exact ContDiff.sum fun k _ => contDiff_const.mul (isSmooth_mFourier k)

theorem continuous_tpoly (a : (Fin 3 → ℤ) → ℂ) (F : Finset (Fin 3 → ℤ)) :
    Continuous (tpoly a F) :=
  continuous_finsetSum _ fun k _ => continuous_const.mul (mFourier k).continuous

theorem mFourierCoeff_tpoly (a : (Fin 3 → ℤ) → ℂ) (F : Finset (Fin 3 → ℤ)) (k : Fin 3 → ℤ) :
    mFourierCoeff (tpoly a F) k = if k ∈ F then a k else 0 := by
  unfold tpoly
  rw [mFourierCoeff_sum F (f := fun m x => a m * mFourier m x)
    fun m => continuous_const.mul (mFourier m).continuous]
  simp only [mFourierCoeff_const_mul, mFourierCoeff_mFourier, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

theorem partialT_tpoly (a : (Fin 3 → ℤ) → ℂ) (F : Finset (Fin 3 → ℤ)) (j : Fin 3) :
    partialT j (tpoly a F) = tpoly (fun k => 2 * Real.pi * I * k j * a k) F := by
  funext x
  have hd : ∀ k : Fin 3 → ℤ, Differentiable ℝ (mFourier k ∘ proj) := fun k =>
    (isSmooth_mFourier k).contDiff_one.differentiable one_ne_zero
  have h : HasDerivAt (fun t : ℝ => tpoly a F (x + proj (Pi.single j t)))
      (∑ k ∈ F, a k * partialT j (mFourier k) (x + proj (Pi.single j 0))) 0 := by
    unfold tpoly
    exact HasDerivAt.fun_sum (u := F) fun k _ => (hasDerivAt_translate (hd k) j x 0).const_mul (a k)
  unfold partialT
  rw [h.deriv]
  simp only [Pi.single_zero, proj_zero, add_zero, partialT_mFourier, tpoly]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem integral_norm_sq_tpoly (a : (Fin 3 → ℤ) → ℂ) (F : Finset (Fin 3 → ℤ)) :
    ∫ x, ‖tpoly a F x‖ ^ 2 = ∑ k ∈ F, ‖a k‖ ^ 2 := by
  have h := hasSum_sq_mFourierCoeff_of_continuous (continuous_tpoly a F)
  simp only [mFourierCoeff_tpoly] at h
  have h2 : HasSum (fun k => ‖if k ∈ F then a k else 0‖ ^ 2) (∑ k ∈ F, ‖a k‖ ^ 2) := by
    have : HasSum (fun k => ‖if k ∈ F then a k else 0‖ ^ 2)
        (∑ k ∈ F, ‖if k ∈ F then a k else 0‖ ^ 2) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by simp [hk]
    convert this using 1
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  exact h.unique h2

/-! ### Squared norms through the cell -/

/-- `‖Re (G ∘ proj)‖_{L²(cell)} ≤ ‖G‖_{L²(𝕋³)}`. -/
theorem eLpNorm_re_comp_proj_le {G : T3 → ℂ} (hG : Continuous G) :
    eLpNorm (fun y => (G (proj y)).re) 2 (volume.restrict cell) ≤
      ENNReal.ofReal (Real.sqrt (∫ x, ‖G x‖ ^ 2)) := by
  have h1 : eLpNorm (fun y => (G (proj y)).re) 2 (volume.restrict cell) ≤
      eLpNorm (G ∘ proj) 2 (volume.restrict cell) := by
    refine eLpNorm_mono (Complex.continuous_re.comp (hG.comp
      isOpenQuotientMap_proj.continuous)).aestronglyMeasurable fun y => ?_
    rw [Real.norm_eq_abs, Function.comp_apply]
    exact Complex.abs_re_le_norm _
  rw [eLpNorm_comp_measurePreserving hG.aestronglyMeasurable measurePreserving_proj_cell] at h1
  refine h1.trans (le_of_eq ?_)
  have hm : MemLp G 2 (volume : Measure T3) :=
    MemLp.of_bound hG.aestronglyMeasurable ‖(⟨G, hG⟩ : C(T3, ℂ))‖
      (Eventually.of_forall fun x => (⟨G, hG⟩ : C(T3, ℂ)).norm_coe_le_norm x)
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), Real.sqrt_eq_rpow]
  norm_num

/-! ### Two vector identities in `ℂ³` -/

/-- `|κ × v|²` for `κ ∈ ℝ³`, `v ∈ ℂ³`, through the pairs `(0, 1)`, `(0, 2)`, `(1, 2)`. -/
def curl3 (κ : Fin 3 → ℝ) (v : Fin 3 → ℂ) : ℝ :=
  ‖(κ 0 : ℂ) * v 1 - κ 1 * v 0‖ ^ 2 + ‖(κ 0 : ℂ) * v 2 - κ 2 * v 0‖ ^ 2 +
    ‖(κ 1 : ℂ) * v 2 - κ 2 * v 1‖ ^ 2

theorem curl3_nonneg (κ : Fin 3 → ℝ) (v : Fin 3 → ℂ) : 0 ≤ curl3 κ v := by
  unfold curl3; positivity

/-- **Lagrange's identity** `|κ|² |v|² = |κ · v|² + |κ × v|²`. -/
theorem lagrange (κ : Fin 3 → ℝ) (v : Fin 3 → ℂ) :
    (∑ a, κ a ^ 2) * ∑ a, ‖v a‖ ^ 2 = ‖∑ a, (κ a : ℂ) * v a‖ ^ 2 + curl3 κ v := by
  simp only [curl3, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- **The projection onto `κ⊥`**: `|v - κ (κ · v)/|κ|²|² = |v|² - |κ · v|²/|κ|²`. -/
theorem proj_sq (κ : Fin 3 → ℝ) (v : Fin 3 → ℂ) (hn : (∑ a, κ a ^ 2) ≠ 0) :
    ∑ a, ‖v a - (κ a : ℂ) * ((∑ b, (κ b : ℂ) * v b) / ((∑ b, κ b ^ 2 : ℝ) : ℂ))‖ ^ 2 =
      ∑ a, ‖v a‖ ^ 2 - ‖∑ a, (κ a : ℂ) * v a‖ ^ 2 / ∑ a, κ a ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.re_sum, Complex.im_sum]
  rw [Fin.sum_univ_three] at hn
  simp only [Fin.sum_univ_three]
  field_simp
  ring

/-! ### The Fourier side of the decomposition -/

section Decomp

variable (u : Fin 3 → (Fin 3 → ℝ) → ℝ)

/-- The periodization of the component `u_a` (a test function on `Q`). -/
def U (a : Fin 3) : T3 → ℂ := per fun y => ((u a y : ℝ) : ℂ)

/-- The Fourier coefficients `û_a(k)`. -/
def uh (a : Fin 3) (k : Fin 3 → ℤ) : ℂ := mFourierCoeff (U u a) k

/-- The frequency as a real vector. -/
def kv (k : Fin 3 → ℤ) : Fin 3 → ℝ := fun a => (k a : ℝ)

/-- `|k|²`. -/
def nk (k : Fin 3 → ℤ) : ℝ := ∑ a, kv k a ^ 2

/-- `k · û(k)`. -/
def zk (k : Fin 3 → ℤ) : ℂ := ∑ a, (kv k a : ℂ) * uh u a k

/-- The coefficients of `∂_a p`: `k_a (k · û)/|k|²`. -/
def gco (a : Fin 3) (k : Fin 3 → ℤ) : ℂ := (kv k a : ℂ) * (zk u k / (nk k : ℂ))

/-- The coefficients of the potential `p`: `-i (k · û)/(2π |k|²)`. -/
def pco (k : Fin 3 → ℤ) : ℂ := -I * (zk u k / (nk k : ℂ)) / (2 * Real.pi)

/-- The truncated potential `p_F = Σ_{k ∈ F} p̂(k) e_k`. -/
def Pc (F : Finset (Fin 3 → ℤ)) : T3 → ℂ := tpoly (pco u) F

/-- `∂_a p_F`. -/
def Gc (F : Finset (Fin 3 → ℤ)) (a : Fin 3) : T3 → ℂ := tpoly (gco u a) F

/-- The remainder `w = u - ∇p_F - û(0)`. -/
def Wc (F : Finset (Fin 3 → ℤ)) (a : Fin 3) : T3 → ℂ := fun x => U u a x - Gc u F a x - uh u a 0

theorem partialT_Pc (F : Finset (Fin 3 → ℤ)) (a : Fin 3) : partialT a (Pc u F) = Gc u F a := by
  rw [Pc, partialT_tpoly, Gc]
  congr 1
  funext k
  simp only [pco, gco, kv]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem kv_zero : kv 0 = 0 := by funext a; simp [kv]

theorem nk_zero : nk 0 = 0 := by simp [nk, kv]

theorem zk_zero : zk u 0 = 0 := by simp [zk, kv]

theorem gco_zero (a : Fin 3) : gco u a 0 = 0 := by simp [gco, kv]

theorem one_le_nk {k : Fin 3 → ℤ} (hk : k ≠ 0) : 1 ≤ nk k := by
  obtain ⟨a, ha⟩ : ∃ a, k a ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1 : ℝ) ≤ kv k a ^ 2 := by
    have : (1 : ℤ) ≤ k a ^ 2 := by
      have := Int.one_le_abs ha
      nlinarith [sq_abs (k a)]
    simp only [kv]; exact_mod_cast this
  calc (1 : ℝ) ≤ kv k a ^ 2 := h1
    _ ≤ nk k := Finset.single_le_sum (f := fun b => kv k b ^ 2) (fun b _ => sq_nonneg _)
        (Finset.mem_univ a)

variable {u}

theorem isSmooth_U (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (a : Fin 3) : IsSmooth (U u a) :=
  isSmooth_per (hu a).ofReal

theorem isSmooth_Wc (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (F : Finset (Fin 3 → ℤ))
    (a : Fin 3) : IsSmooth (Wc u F a) := by
  unfold IsSmooth
  have : Wc u F a ∘ proj = fun y => (U u a ∘ proj) y - (Gc u F a ∘ proj) y - uh u a 0 := rfl
  rw [this]
  exact ((isSmooth_U hu a).sub (isSmooth_tpoly _ F)).sub contDiff_const

theorem coeff_Wc (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (F : Finset (Fin 3 → ℤ)) (a : Fin 3)
    (k : Fin 3 → ℤ) : mFourierCoeff (Wc u F a) k =
      uh u a k - (if k ∈ F then gco u a k else 0) - (if k = 0 then uh u a 0 else 0) := by
  have hU := (isSmooth_U hu a).continuous
  have hG := continuous_tpoly (gco u a) F
  unfold Wc
  rw [mFourierCoeff_sub' (f := fun x => U u a x - Gc u F a x) (g := fun _ => uh u a 0)
    (hU.sub hG) continuous_const, mFourierCoeff_sub' (f := U u a) (g := Gc u F a) hU hG,
    mFourierCoeff_const, Gc, mFourierCoeff_tpoly]
  rfl

/-- The coefficients of the remainder as a vector: `0` at `k = 0`, the projection of `û(k)` onto
`k⊥` for `k ∈ F`, `û(k)` otherwise. -/
theorem coeff_Wc_eq (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (F : Finset (Fin 3 → ℤ))
    (k : Fin 3 → ℤ) (a : Fin 3) : mFourierCoeff (Wc u F a) k =
      if k = 0 then 0 else if k ∈ F then uh u a k - (kv k a : ℂ) * (zk u k / (nk k : ℂ))
        else uh u a k := by
  rw [coeff_Wc hu]
  by_cases h0 : k = 0
  · subst h0; simp [gco_zero]
  · simp only [h0, ite_false, sub_zero]
    split_ifs <;> simp [gco]

/-- `Σₐ |ŵₐ(k)|² ≤ Σₐ |ûₐ(k)|²`. -/
theorem sum_norm_sq_coeff_Wc_le (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a))
    (F : Finset (Fin 3 → ℤ)) (k : Fin 3 → ℤ) :
    ∑ a, ‖mFourierCoeff (Wc u F a) k‖ ^ 2 ≤ ∑ a, ‖uh u a k‖ ^ 2 := by
  simp only [coeff_Wc_eq hu]
  by_cases h0 : k = 0
  · simp only [h0, ite_true, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · simp only [h0, ite_false]
    by_cases hF : k ∈ F
    · simp only [hF, ite_true]
      have hn := one_le_nk h0
      have := proj_sq (kv k) (fun a => uh u a k) (by unfold nk at hn; linarith)
      simp only [zk, nk] at this ⊢
      rw [this]
      have : 0 ≤ ‖∑ a, (kv k a : ℂ) * uh u a k‖ ^ 2 / ∑ a, kv k a ^ 2 := by positivity
      linarith
    · simp [hF]

/-- `|k|² Σₐ |ŵₐ(k)|² ≤ |k × û(k)|² + [k ∉ F] |k|² |û(k)|²`. -/
theorem nk_mul_sum_coeff_Wc_le (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a))
    (F : Finset (Fin 3 → ℤ)) (k : Fin 3 → ℤ) :
    nk k * ∑ a, ‖mFourierCoeff (Wc u F a) k‖ ^ 2 ≤
      curl3 (kv k) (fun a => uh u a k) + if k ∈ F then 0 else nk k * ∑ a, ‖uh u a k‖ ^ 2 := by
  have hc := curl3_nonneg (kv k) (fun a => uh u a k)
  simp only [coeff_Wc_eq hu]
  by_cases h0 : k = 0
  · subst h0
    simp only [ite_true, norm_zero, nk_zero, zero_mul]
    split_ifs <;> linarith
  · simp only [h0, ite_false]
    by_cases hF : k ∈ F
    · simp only [hF, ite_true, add_zero]
      have hn := one_le_nk h0
      have e := proj_sq (kv k) (fun a => uh u a k) (by unfold nk at hn; linarith)
      have l := lagrange (kv k) (fun a => uh u a k)
      simp only [zk, nk] at e l hn ⊢
      rw [e, mul_sub, mul_div_cancel₀ _ (by linarith)]
      linarith
    · simp only [hF, ite_false]
      linarith

/-- `|p̂(k)|² ≤ Σₐ |ûₐ(k)|²`. -/
theorem norm_sq_pco_le (k : Fin 3 → ℤ) : ‖pco u k‖ ^ 2 ≤ ∑ a, ‖uh u a k‖ ^ 2 := by
  by_cases h0 : k = 0
  · subst h0; simp only [pco, zk_zero, zero_div, mul_zero, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  have hn := one_le_nk h0
  have l := lagrange (kv k) (fun a => uh u a k)
  have hc := curl3_nonneg (kv k) (fun a => uh u a k)
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  simp only [pco, zk, nk] at l hn ⊢
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith), Complex.norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  set z := ‖∑ a, (kv k a : ℂ) * uh u a k‖
  set n := ∑ a, kv k a ^ 2
  set V := ∑ a, ‖uh u a k‖ ^ 2
  have hV : 0 ≤ V := by positivity
  have hz : z ^ 2 ≤ n * V := by linarith
  rw [div_pow, div_pow]
  rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  have h2 : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith
  calc z ^ 2 ≤ n * V := hz
    _ ≤ V * n ^ 2 * (2 * Real.pi) ^ 2 := by
        have : n ≤ n ^ 2 := by nlinarith
        calc n * V ≤ n ^ 2 * V := by nlinarith
          _ = V * n ^ 2 * 1 := by ring
          _ ≤ V * n ^ 2 * (2 * Real.pi) ^ 2 := by gcongr
    _ = _ := by ring

end Decomp

/-! ### Parseval sums -/

section Sums

variable (u : Fin 3 → (Fin 3 → ℝ) → ℝ)

/-- `Σₐ ‖uₐ‖²_{L²(𝕋³)}`. -/
def Nu : ℝ := ∑ a, ∫ x, ‖U u a x‖ ^ 2

/-- The component `(j, l)` of `curl u` on the torus. -/
def curlU (j l : Fin 3) (x : T3) : ℂ := partialT j (U u l) x - partialT l (U u j) x

/-- `‖curl u‖²_{L²(𝕋³)}`. -/
def Ncurl : ℝ :=
  (∫ x, ‖curlU u 0 1 x‖ ^ 2) + (∫ x, ‖curlU u 0 2 x‖ ^ 2) + ∫ x, ‖curlU u 1 2 x‖ ^ 2

/-- `‖∇u‖²_{L²(𝕋³)}`. -/
def NT : ℝ := ∑ j, ∑ a, ∫ x, ‖partialT j (U u a) x‖ ^ 2

/-- The frequency density of `‖∇u‖²`. -/
def T4 (k : Fin 3 → ℤ) : ℝ := ∑ j, ∑ a, ‖mFourierCoeff (partialT j (U u a)) k‖ ^ 2

variable {u}

theorem norm_sq_freq_mul (j : Fin 3) (k : Fin 3 → ℤ) (c : ℂ) :
    ‖2 * Real.pi * I * (k j : ℂ) * c‖ ^ 2 = 4 * Real.pi ^ 2 * (kv k j ^ 2 * ‖c‖ ^ 2) := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast]
  simp only [kv]
  rw [show (2 * Real.pi * 1 * |((k j : ℤ) : ℝ)| * ‖c‖) ^ 2 =
    4 * Real.pi ^ 2 * (|((k j : ℤ) : ℝ)| ^ 2 * ‖c‖ ^ 2) by ring, sq_abs]

theorem sum_freq_mul (k : Fin 3 → ℤ) (c : Fin 3 → ℂ) :
    ∑ j, ∑ a, ‖2 * Real.pi * I * (k j : ℂ) * c a‖ ^ 2 =
      4 * Real.pi ^ 2 * (nk k * ∑ a, ‖c a‖ ^ 2) := by
  simp only [norm_sq_freq_mul, ← Finset.mul_sum, ← Finset.sum_mul, nk]

theorem T4_eq (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (k : Fin 3 → ℤ) :
    T4 u k = 4 * Real.pi ^ 2 * (nk k * ∑ a, ‖uh u a k‖ ^ 2) := by
  simp only [T4, mFourierCoeff_partialT (isSmooth_U hu _).contDiff_one]
  exact sum_freq_mul k _

theorem hasSum_Nu (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) :
    HasSum (fun k => ∑ a, ‖uh u a k‖ ^ 2) (Nu u) :=
  hasSum_sum fun a _ => hasSum_sq_mFourierCoeff_of_continuous (isSmooth_U hu a).continuous

theorem hasSum_T4 (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) : HasSum (T4 u) (NT u) :=
  hasSum_sum fun j _ => hasSum_sum fun a _ => hasSum_sq_mFourierCoeff_of_continuous
    (continuous_partialT (isSmooth_U hu a).contDiff_one j)

theorem coeff_curlU (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (j l : Fin 3) (k : Fin 3 → ℤ) :
    mFourierCoeff (curlU u j l) k =
      2 * Real.pi * I * ((kv k j : ℂ) * uh u l k - (kv k l : ℂ) * uh u j k) := by
  unfold curlU
  rw [mFourierCoeff_sub' (continuous_partialT (isSmooth_U hu l).contDiff_one j)
    (continuous_partialT (isSmooth_U hu j).contDiff_one l),
    mFourierCoeff_partialT (isSmooth_U hu l).contDiff_one,
    mFourierCoeff_partialT (isSmooth_U hu j).contDiff_one]
  simp only [kv, uh]; push_cast; ring

theorem hasSum_Ncurl (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) :
    HasSum (fun k => 4 * Real.pi ^ 2 * curl3 (kv k) (fun a => uh u a k)) (Ncurl u) := by
  have h : ∀ j l,
      HasSum (fun k => ‖mFourierCoeff (curlU u j l) k‖ ^ 2) (∫ x, ‖curlU u j l x‖ ^ 2) :=
    fun j l => hasSum_sq_mFourierCoeff_of_continuous
      ((continuous_partialT (isSmooth_U hu l).contDiff_one j).sub
        (continuous_partialT (isSmooth_U hu j).contDiff_one l))
  have := ((h 0 1).add (h 0 2)).add (h 1 2)
  unfold Ncurl
  convert this using 1
  funext k
  simp only [coeff_curlU hu, curl3, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_pow]
  ring

/-- **The `L²` bound of the potential**: `‖p_F‖² ≤ Σₐ ‖uₐ‖²`. -/
theorem integral_Pc_le (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (F : Finset (Fin 3 → ℤ)) :
    ∫ x, ‖Pc u F x‖ ^ 2 ≤ Nu u := by
  rw [Pc, integral_norm_sq_tpoly]
  calc ∑ k ∈ F, ‖pco u k‖ ^ 2 ≤ ∑ k ∈ F, ∑ a, ‖uh u a k‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => norm_sq_pco_le k
    _ ≤ Nu u := sum_le_hasSum F (fun k _ => by positivity) (hasSum_Nu hu)

/-- **The `L²` bound of the remainder**: `Σₐ ‖wₐ‖² ≤ Σₐ ‖uₐ‖²`. -/
theorem sum_integral_Wc_le (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (F : Finset (Fin 3 → ℤ)) :
    ∑ a, ∫ x, ‖Wc u F a x‖ ^ 2 ≤ Nu u := by
  have h : HasSum (fun k => ∑ a, ‖mFourierCoeff (Wc u F a) k‖ ^ 2) (∑ a, ∫ x, ‖Wc u F a x‖ ^ 2) :=
    hasSum_sum fun a _ => hasSum_sq_mFourierCoeff_of_continuous (isSmooth_Wc hu F a).continuous
  exact hasSum_le (fun k => sum_norm_sq_coeff_Wc_le hu F k) h (hasSum_Nu hu)

/-- **The `H¹` bound of the remainder** (Gaffney on `𝕋³`):
`‖∇w‖² ≤ ‖curl u‖² + Σ_{k ∉ F} |2πk|² |û(k)|²`. -/
theorem sum_integral_partialT_Wc_le (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a))
    (F : Finset (Fin 3 → ℤ)) :
    ∑ j, ∑ a, ∫ x, ‖partialT j (Wc u F a) x‖ ^ 2 ≤ Ncurl u + (NT u - ∑ k ∈ F, T4 u k) := by
  have h : HasSum (fun k => ∑ j, ∑ a, ‖mFourierCoeff (partialT j (Wc u F a)) k‖ ^ 2)
      (∑ j, ∑ a, ∫ x, ‖partialT j (Wc u F a) x‖ ^ 2) :=
    hasSum_sum fun j _ => hasSum_sum fun a _ => hasSum_sq_mFourierCoeff_of_continuous
      (continuous_partialT (isSmooth_Wc hu F a).contDiff_one j)
  have hF : HasSum (fun k => if k ∈ F then T4 u k else 0) (∑ k ∈ F, T4 u k) := by
    have : HasSum (fun k => if k ∈ F then T4 u k else 0)
        (∑ k ∈ F, if k ∈ F then T4 u k else 0) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by simp [hk]
    convert this using 1
    exact (Finset.sum_congr rfl fun k hk => by simp [hk]).symm
  have hrhs := (hasSum_Ncurl hu).add ((hasSum_T4 hu).sub hF)
  refine hasSum_le (fun k => ?_) h hrhs
  simp only [mFourierCoeff_partialT (isSmooth_Wc hu F _).contDiff_one]
  rw [sum_freq_mul, T4_eq hu]
  have := nk_mul_sum_coeff_Wc_le hu F k
  have hπ : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  split_ifs at this ⊢ with hk
  · nlinarith
  · nlinarith

/-- **Choice of the truncation**: the tail `Σ_{k ∉ F} |2πk|² |û(k)|²` is at most `Σₐ ‖uₐ‖²`
for some finite `F`. -/
theorem exists_tail_le (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) :
    ∃ F : Finset (Fin 3 → ℤ), NT u - ∑ k ∈ F, T4 u k ≤ Nu u := by
  have hN : 0 ≤ Nu u := (hasSum_Nu hu).nonneg fun k => by positivity
  rcases hN.lt_or_eq with hpos | hzero
  · have ht := (hasSum_T4 hu)
    have hev := (Metric.tendsto_nhds.1 ht) (Nu u) hpos
    obtain ⟨F, hF⟩ := hev.exists
    refine ⟨F, ?_⟩
    rw [Real.dist_eq] at hF
    have := neg_abs_le (∑ k ∈ F, T4 u k - NT u)
    linarith [le_abs_self (∑ k ∈ F, T4 u k - NT u)]
  · refine ⟨∅, ?_⟩
    have h0 : ∀ k, ∑ a, ‖uh u a k‖ ^ 2 = 0 := by
      have := (hasSum_zero_iff_of_nonneg (f := fun k => ∑ a, ‖uh u a k‖ ^ 2)
        (fun k => by positivity)).1 (hzero ▸ hasSum_Nu hu)
      exact fun k => congrFun this k
    have hT : ∀ k, T4 u k = 0 := fun k => by rw [T4_eq hu, h0 k]; ring
    have hz : HasSum (T4 u) 0 := by
      have : T4 u = fun _ => 0 := funext hT
      rw [this]; exact hasSum_zero
    have : NT u = 0 := (hasSum_T4 hu).unique hz
    simp [this, ← hzero]

/-- `|û_a(0)|² ≤ Σₐ ‖uₐ‖²`. -/
theorem norm_sq_uh_zero_le (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (a : Fin 3) :
    ‖uh u a 0‖ ^ 2 ≤ Nu u := by
  calc ‖uh u a 0‖ ^ 2 ≤ ∑ b, ‖uh u b 0‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖uh u b 0‖ ^ 2) (fun b _ => by positivity)
          (Finset.mem_univ a)
    _ ≤ Nu u := by
        have := sum_le_hasSum {0} (fun k _ => by positivity) (hasSum_Nu hu)
        simpa using this

end Sums

/-! ### Back to `ℝ³` -/

section Lift

open Feec.Models.Cube.ShellExtension (pd)

/-- On the cell `(-¼, ¾]³` the periodization of a function supported in `Q` is the function. -/
theorem per_proj_of_mem_cell {Φ : (Fin 3 → ℝ) → ℂ} (hΦ : Domain.IsTest (Q (Fin 3)) Φ)
    {y : Fin 3 → ℝ} (hy : y ∈ cell) : per Φ (proj y) = Φ y := by
  by_cases hQ : y ∈ Q (Fin 3)
  · exact per_proj_of_mem hQ
  rw [per_proj, hΦ.eq_zero_of_notMem hQ]
  by_contra h
  have hm := mem_Q.1 (mem_Q_of_ne_zero hΦ h)
  refine hQ (mem_Q.2 fun i => ?_)
  have hi := hm i
  have hyi := hy i (mem_univ i)
  simp only [mem_Ioo, mem_Ioc] at hi hyi
  have hf : ⌊y i⌋ = 0 := by
    rw [Int.floor_eq_iff]
    constructor
    · by_contra hlt
      push Not at hlt
      have h1 : ⌊y i⌋ ≤ -1 := by
        have : (⌊y i⌋ : ℝ) < 0 := lt_of_le_of_lt (Int.floor_le _) (by push_cast at hlt; linarith)
        exact_mod_cast (show (⌊y i⌋ : ℝ) ≤ -1 by
          have := Int.cast_lt.1 (show (⌊y i⌋ : ℝ) < ((0 : ℤ) : ℝ) by simpa using this)
          exact_mod_cast Int.le_sub_one_of_lt this)
      have h2 : (⌊y i⌋ : ℝ) ≤ -1 := by exact_mod_cast h1
      linarith
    · push_cast; linarith
  rw [hf] at hi
  simpa using hi

theorem isTest_ofReal {f : (Fin 3 → ℝ) → ℝ} (hf : Domain.IsTest (Q (Fin 3)) f) :
    Domain.IsTest (Q (Fin 3)) fun y => ((f y : ℝ) : ℂ) := hf.ofReal

theorem contDiff_re_comp {G : T3 → ℂ} (hG : IsSmooth G) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => (G (proj y)).re :=
  Complex.reCLM.contDiff.comp hG

theorem pd_re_comp {G : T3 → ℂ} (hG : IsSmooth G) (j : Fin 3) (y : Fin 3 → ℝ) :
    pd j (fun y => (G (proj y)).re) y = (partialT j G (proj y)).re := by
  have hd : Differentiable ℝ (G ∘ proj) := hG.contDiff_one.differentiable one_ne_zero
  have h := (Complex.reCLM.hasFDerivAt (x := (G ∘ proj) y)).comp y (hd y).hasFDerivAt
  rw [pd, show (fun y => (G (proj y)).re) = Complex.reCLM ∘ (G ∘ proj) from rfl, h.fderiv,
    partialT_proj hd]
  rfl

variable {u : Fin 3 → (Fin 3 → ℝ) → ℝ}

/-- The truncated potential `p_F` on `ℝ³`. -/
def pR (u : Fin 3 → (Fin 3 → ℝ) → ℝ) (F : Finset (Fin 3 → ℤ)) (y : Fin 3 → ℝ) : ℝ :=
  (Pc u F (proj y)).re

/-- The remainder `w = u - ∇p_F - c` on `ℝ³` (periodic). -/
def wR (u : Fin 3 → (Fin 3 → ℝ) → ℝ) (F : Finset (Fin 3 → ℤ)) (a : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  (Wc u F a (proj y)).re

/-- The mean `c_a = ∫ uₐ`. -/
def cR (u : Fin 3 → (Fin 3 → ℝ) → ℝ) (a : Fin 3) : ℝ := (uh u a 0).re

theorem contDiff_pR (F : Finset (Fin 3 → ℤ)) : ContDiff ℝ (⊤ : ℕ∞) (pR u F) :=
  contDiff_re_comp (isSmooth_tpoly _ F)

theorem contDiff_wR (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (F : Finset (Fin 3 → ℤ))
    (a : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (wR u F a) :=
  contDiff_re_comp (isSmooth_Wc hu F a)

theorem pd_pR (F : Finset (Fin 3 → ℤ)) (a : Fin 3) (y : Fin 3 → ℝ) :
    pd a (pR u F) y = (Gc u F a (proj y)).re := by
  unfold pR
  rw [pd_re_comp (G := Pc u F) (isSmooth_tpoly _ F), partialT_Pc]

/-- **On the cell**, `w = u - ∇p - c`. -/
theorem wR_eq (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (F : Finset (Fin 3 → ℤ)) (a : Fin 3)
    {y : Fin 3 → ℝ} (hy : y ∈ cell) : wR u F a y = u a y - pd a (pR u F) y - cR u a := by
  rw [wR, pd_pR, cR, Wc, U, per_proj_of_mem_cell (isTest_ofReal (hu a)) hy]
  simp

/-- The `L²(Q)` norm of `u`. -/
def NuQ (u : Fin 3 → (Fin 3 → ℝ) → ℝ) : ℝ := ∑ a, ∫ y in Q (Fin 3), u a y ^ 2

/-- The component `(j, l)` of `curl u` on `ℝ³`. -/
def curlR (u : Fin 3 → (Fin 3 → ℝ) → ℝ) (j l : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  pd j (u l) y - pd l (u j) y

/-- The `L²(Q)` norm of `curl u`. -/
def NcurlQ (u : Fin 3 → (Fin 3 → ℝ) → ℝ) : ℝ :=
  (∫ y in Q (Fin 3), curlR u 0 1 y ^ 2) + (∫ y in Q (Fin 3), curlR u 0 2 y ^ 2) +
    ∫ y in Q (Fin 3), curlR u 1 2 y ^ 2

theorem integral_norm_sq_per {f : (Fin 3 → ℝ) → ℝ} (hf : Domain.IsTest (Q (Fin 3)) f) :
    ∫ x, ‖per (fun y => ((f y : ℝ) : ℂ)) x‖ ^ 2 = ∫ y in Q (Fin 3), f y ^ 2 := by
  have hc := (isSmooth_per (isTest_ofReal hf)).continuous
  rw [integral_eq_setIntegral_Q (g := fun x => ‖per (fun y => ((f y : ℝ) : ℂ)) x‖ ^ 2)
    (hc.norm.pow 2).aestronglyMeasurable
    fun x hx => by simp [per_eq_zero_of_notMem (isTest_ofReal hf) hx]]
  refine setIntegral_congr_fun measurableSet_Q fun y hy => ?_
  rw [per_proj_of_mem hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem Nu_eq (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) : Nu u = NuQ u := by
  simp only [Nu, NuQ, U, integral_norm_sq_per (hu _)]

theorem partialT_U (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (j l : Fin 3) :
    partialT j (U u l) = per fun y => ((pd j (u l) y : ℝ) : ℂ) := by
  rw [U, partialT_per (isTest_ofReal (hu l))]
  congr 1; funext y
  have h := (Complex.ofRealCLM.hasFDerivAt (x := u l y)).comp y
    ((hu l).differentiable y).hasFDerivAt
  rw [show (fun y => ((u l y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ u l from rfl, h.fderiv]
  rfl

theorem curlU_eq (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (j l : Fin 3) :
    curlU u j l = per fun y => ((curlR u j l y : ℝ) : ℂ) := by
  funext x
  simp only [curlU, partialT_U hu, per, curlR]
  push_cast; ring

theorem isTest_curlR (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) (j l : Fin 3) :
    Domain.IsTest (Q (Fin 3)) (curlR u j l) :=
  ((hu l).fderiv_apply _).sub ((hu j).fderiv_apply _)

theorem Ncurl_eq (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) : Ncurl u = NcurlQ u := by
  simp only [Ncurl, NcurlQ, curlU_eq hu, integral_norm_sq_per (isTest_curlR hu _ _)]

theorem eLpNorm_le_sqrt_of {G : T3 → ℂ} (hG : Continuous G) {X : ℝ} (h : ∫ x, ‖G x‖ ^ 2 ≤ X) :
    eLpNorm (fun y => (G (proj y)).re) 2 (volume.restrict cell) ≤ ENNReal.ofReal (Real.sqrt X) :=
  (eLpNorm_re_comp_proj_le hG).trans (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt h))

/-- **The Helmholtz decomposition of a test field on the torus, with `H¹` bounds**: for test
functions `uₐ` on `Q`, there are a smooth potential `p`, a constant vector `c` and smooth `wₐ`
with `w = u - ∇p - c` on the cell `(-¼, ¾]³ ⊇ Q̄`,
`‖p‖, |cₐ|, ‖wₐ‖ ≤ ‖u‖` and `‖∂ⱼ wₐ‖² ≤ ‖curl u‖² + ‖u‖²` in `L²` of the cell. -/
theorem exists_helmholtz (hu : ∀ a, Domain.IsTest (Q (Fin 3)) (u a)) :
    ∃ (p : (Fin 3 → ℝ) → ℝ) (c : Fin 3 → ℝ) (w : Fin 3 → (Fin 3 → ℝ) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ a, ContDiff ℝ (⊤ : ℕ∞) (w a)) ∧
      (∀ a, ∀ y ∈ cell, w a y = u a y - pd a p y - c a) ∧
      eLpNorm p 2 (volume.restrict cell) ≤ ENNReal.ofReal (Real.sqrt (NuQ u)) ∧
      (∀ a, |c a| ≤ Real.sqrt (NuQ u)) ∧
      (∀ a, eLpNorm (w a) 2 (volume.restrict cell) ≤ ENNReal.ofReal (Real.sqrt (NuQ u))) ∧
      (∀ j a, eLpNorm (pd j (w a)) 2 (volume.restrict cell) ≤
        ENNReal.ofReal (Real.sqrt (NcurlQ u + NuQ u))) := by
  obtain ⟨F, hF⟩ := exists_tail_le hu
  refine ⟨pR u F, cR u, wR u F, contDiff_pR F, contDiff_wR hu F, fun a y hy => wR_eq hu F a hy,
    ?_, fun a => ?_, fun a => ?_, fun j a => ?_⟩
  · rw [← Nu_eq hu]
    exact eLpNorm_le_sqrt_of (continuous_tpoly _ F) (integral_Pc_le hu F)
  · rw [← Nu_eq hu, cR]
    refine Real.le_sqrt_of_sq_le ?_
    calc |(uh u a 0).re| ^ 2 ≤ ‖uh u a 0‖ ^ 2 := by
          gcongr; exact Complex.abs_re_le_norm _
      _ ≤ Nu u := norm_sq_uh_zero_le hu a
  · rw [← Nu_eq hu]
    refine eLpNorm_le_sqrt_of (isSmooth_Wc hu F a).continuous ?_
    calc ∫ x, ‖Wc u F a x‖ ^ 2 ≤ ∑ b, ∫ x, ‖Wc u F b x‖ ^ 2 :=
          Finset.single_le_sum (f := fun b => ∫ x, ‖Wc u F b x‖ ^ 2)
            (fun b _ => integral_nonneg fun x => by positivity) (Finset.mem_univ a)
      _ ≤ Nu u := sum_integral_Wc_le hu F
  · rw [← Nu_eq hu, ← Ncurl_eq hu]
    have hpd : pd j (wR u F a) = fun y => (partialT j (Wc u F a) (proj y)).re :=
      funext fun y => pd_re_comp (isSmooth_Wc hu F a) j y
    rw [hpd]
    refine eLpNorm_le_sqrt_of (continuous_partialT (isSmooth_Wc hu F a).contDiff_one j) ?_
    have hnn : ∀ j b, 0 ≤ ∫ x, ‖partialT j (Wc u F b) x‖ ^ 2 := fun j b =>
      integral_nonneg fun x => by positivity
    calc ∫ x, ‖partialT j (Wc u F a) x‖ ^ 2 ≤ ∑ b, ∫ x, ‖partialT j (Wc u F b) x‖ ^ 2 :=
          Finset.single_le_sum (f := fun b => ∫ x, ‖partialT j (Wc u F b) x‖ ^ 2)
            (fun b _ => hnn j b) (Finset.mem_univ a)
      _ ≤ ∑ j, ∑ b, ∫ x, ‖partialT j (Wc u F b) x‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ∑ b, ∫ x, ‖partialT j (Wc u F b) x‖ ^ 2)
            (fun j _ => Finset.sum_nonneg fun b _ => hnn j b) (Finset.mem_univ j)
      _ ≤ Ncurl u + (NT u - ∑ k ∈ F, T4 u k) := sum_integral_partialT_Wc_le hu F
      _ ≤ Ncurl u + Nu u := by linarith

end Lift

end Feec.Models.Cube.TorusHelmholtz
