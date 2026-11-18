module

public import Feec.Models.Cube.SobolevRateHigh

/-!
# Restrictions of `Hᵐ(ℝⁿ)` to the cube lie in `Hᵐ(Q)`

`Feec.Models.Cube.SobolevRateHigh` proves the finite element rates for the spaces `Hˢ(Q)` of
restrictions to `Q = (0, ½)ⁿ` of forms of `Hˢ(𝕋ⁿ)` on the period-`1` torus
(`Feec.Models.Cube.Sobolev.sobolevQ`). **`exists_qNorm_le`**: the restriction to `Q` of every
form whose coefficients lie in `Hᵐ(ℝⁿ)` (`IsWeakDeriv`: weak derivatives in `L²(ℝⁿ)` along all
words of length `≤ m`) lies in `Hᵐ(Q)`, with `‖u‖_{Hᵐ(Q)} ≤ C ‖U‖_{Hᵐ(ℝⁿ)}`. The proof
multiplies by a cutoff `χ = 1` near `cl Q` supported in the cell `(-¼, ¾]ⁿ` (Leibniz's rule for
weak derivatives along words, `leibniz`), periodizes (`perCell`), tests the weak derivatives
against the smooth functions of the torus (`hasWeakDerivT_perCell`), and bounds the Fourier norm
by the pure derivatives (`Feec.Models.Cube.Sobolev.sobSum_le`). This is the backward direction
for `Hᵐ(Q)` given an extension to `ℝⁿ` (the extension operator itself is not formalized).

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2 (weak derivatives)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped ContDiff
open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace Feec.Models.Cube.SobolevRestriction

open Feec.Models.Cube.Sobolev

variable {n : ℕ}

/-! ### Weak derivatives on `ℝⁿ` -/

/-- `v` is the **weak derivative** `∂^l f` on `ℝⁿ`: `∫ f ∂^l φ = (-1)^{|l|} ∫ v φ` for every test
function `φ`. -/
def IsWeakDeriv (l : List (Fin n)) (f v : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ φ : (Fin n → ℝ) → ℝ, Feec.Domain.IsTest (univ : Set (Fin n → ℝ)) φ →
    ∫ y, f y * iterPartial l φ y = (-1) ^ l.length * ∫ y, v y * φ y

/-- `φ` is a test function on `ℝⁿ`. -/
abbrev IsT (φ : (Fin n → ℝ) → ℝ) : Prop := Feec.Domain.IsTest (univ : Set (Fin n → ℝ)) φ

theorem isT_memLp {φ : (Fin n → ℝ) → ℝ} (hφ : IsT φ) (p : ENNReal) : MemLp φ p volume :=
  hφ.continuous.memLp_of_hasCompactSupport hφ.hasCompactSupport

theorem integrable_mul_test {f φ : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) (hφ : IsT φ) :
    Integrable (fun y => f y * φ y) volume :=
  hf.integrable_mul (isT_memLp hφ 2)

theorem isT_mul {χ φ : (Fin n → ℝ) → ℝ} (hχ : IsT χ) (hφ : IsT φ) : IsT fun y => χ y * φ y :=
  ⟨hχ.contDiff.mul hφ.contDiff, hφ.hasCompactSupport.mul_left, subset_univ _⟩

theorem isT_partialDeriv {χ : (Fin n → ℝ) → ℝ} (hχ : IsT χ) (j : Fin n) :
    IsT (_root_.partialDeriv j χ) :=
  hχ.fderiv_apply (Pi.single j 1)

theorem isT_bound {χ : (Fin n → ℝ) → ℝ} (hχ : IsT χ) : ∃ C, 0 ≤ C ∧ ∀ y, |χ y| ≤ C := by
  obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχ.hasCompactSupport
  exact ⟨max C 0, le_max_right _ _, fun y => (hC y).trans (le_max_left _ _)⟩

theorem IsWeakDeriv.cons {j : Fin n} {l : List (Fin n)} {f g v : (Fin n → ℝ) → ℝ}
    (h1 : IsWeakDeriv [j] f g) (h2 : IsWeakDeriv l g v) : IsWeakDeriv (j :: l) f v := by
  intro φ hφ
  have e1 := h1 (iterPartial l φ) (isTest_iterPartial hφ l)
  have e2 := h2 φ hφ
  simp only [iterPartial_cons, iterPartial_nil, List.length_cons, List.length_nil] at e1 ⊢
  rw [e1, e2]
  ring

theorem IsWeakDeriv.tail {j : Fin n} {l : List (Fin n)} {f g v : (Fin n → ℝ) → ℝ}
    (h1 : IsWeakDeriv [j] f g) (h2 : IsWeakDeriv (j :: l) f v) : IsWeakDeriv l g v := by
  intro φ hφ
  have e1 := h1 (iterPartial l φ) (isTest_iterPartial hφ l)
  have e2 := h2 φ hφ
  simp only [iterPartial_cons, iterPartial_nil, List.length_cons, List.length_nil] at e1 e2
  have := e1.symm.trans e2
  linear_combination (-1 : ℝ) * this

theorem IsWeakDeriv.add {l : List (Fin n)} {f₁ f₂ v₁ v₂ : (Fin n → ℝ) → ℝ} (hf₁ : MemLp f₁ 2 volume)
    (hf₂ : MemLp f₂ 2 volume) (hv₁ : MemLp v₁ 2 volume) (hv₂ : MemLp v₂ 2 volume)
    (h₁ : IsWeakDeriv l f₁ v₁) (h₂ : IsWeakDeriv l f₂ v₂) :
    IsWeakDeriv l (fun y => f₁ y + f₂ y) (fun y => v₁ y + v₂ y) := by
  intro φ hφ
  simp only [add_mul]
  rw [integral_add (integrable_mul_test hf₁ (isTest_iterPartial hφ l))
      (integrable_mul_test hf₂ (isTest_iterPartial hφ l)),
    integral_add (integrable_mul_test hv₁ hφ) (integrable_mul_test hv₂ hφ), h₁ φ hφ, h₂ φ hφ]
  ring

theorem memLp_mul_test {χ f : (Fin n → ℝ) → ℝ} (hχ : IsT χ) (hf : MemLp f 2 volume) :
    MemLp (fun y => χ y * f y) 2 volume := by
  obtain ⟨C, -, hC⟩ := isT_bound hχ
  refine hf.of_le_mul (c := C) (hχ.continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC y) (abs_nonneg _)

theorem integral_sq_mul_le {χ f : (Fin n → ℝ) → ℝ} (hχ : IsT χ) (hf : MemLp f 2 volume) {C : ℝ}
    (hC : ∀ y, |χ y| ≤ C) : ∫ y, (χ y * f y) ^ 2 ≤ C ^ 2 * ∫ y, f y ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono (memLp_mul_test hχ hf).integrable_sq (hf.integrable_sq.const_mul _)
    fun y => ?_
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by
    rw [← sq_abs (χ y)]; exact pow_le_pow_left₀ (abs_nonneg _) (hC y) 2) (sq_nonneg _)

theorem integral_add_sq_le {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    ∫ y, (f y + g y) ^ 2 ≤ 2 * (∫ y, f y ^ 2) + 2 * ∫ y, g y ^ 2 := by
  calc ∫ y, (f y + g y) ^ 2 ≤ ∫ y, (2 * f y ^ 2 + 2 * g y ^ 2) :=
        integral_mono (hf.add hg).integrable_sq
          ((hf.integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2))
          fun y => by nlinarith [sq_nonneg (f y - g y)]
    _ = _ := by
        rw [integral_add (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2),
          integral_const_mul, integral_const_mul]

/-- **Leibniz's rule, first order**: `∂_j (χ f) = ∂_j χ f + χ ∂_j f` weakly. -/
theorem isWeakDeriv_mul_single {χ f g : (Fin n → ℝ) → ℝ} (hχ : IsT χ) (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) {j : Fin n} (h : IsWeakDeriv [j] f g) :
    IsWeakDeriv [j] (fun y => χ y * f y)
      (fun y => _root_.partialDeriv j χ y * f y + χ y * g y) := by
  intro φ hφ
  have e := h _ (isT_mul hχ hφ)
  simp only [iterPartial_cons, iterPartial_nil, List.length_cons, List.length_nil, zero_add,
    pow_one] at e ⊢
  have hd : ∀ y, _root_.partialDeriv j (fun y => χ y * φ y) y =
      _root_.partialDeriv j χ y * φ y + χ y * _root_.partialDeriv j φ y := fun y =>
    partialDeriv_mul (hχ.differentiable y) (hφ.differentiable y) j
  have i1 : Integrable (fun y => f y * (_root_.partialDeriv j χ y * φ y)) volume :=
    integrable_mul_test hf (isT_mul (isT_partialDeriv hχ j) hφ)
  have i2 : Integrable (fun y => f y * (χ y * _root_.partialDeriv j φ y)) volume :=
    integrable_mul_test hf (isT_mul hχ (isT_partialDeriv hφ j))
  have i3 : Integrable (fun y => g y * (χ y * φ y)) volume :=
    integrable_mul_test hg (isT_mul hχ hφ)
  have e1 : ∫ y, f y * _root_.partialDeriv j (fun y => χ y * φ y) y =
      (∫ y, f y * (_root_.partialDeriv j χ y * φ y)) +
        ∫ y, f y * (χ y * _root_.partialDeriv j φ y) := by
    refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans (integral_add i1 i2)
    simp only [hd]; ring
  have e2 : ∫ y, χ y * f y * _root_.partialDeriv j φ y =
      ∫ y, f y * (χ y * _root_.partialDeriv j φ y) :=
    integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
  have e3 : ∫ y, (_root_.partialDeriv j χ y * f y + χ y * g y) * φ y =
      (∫ y, f y * (_root_.partialDeriv j χ y * φ y)) + ∫ y, g y * (χ y * φ y) := by
    refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans (integral_add i1 i3)
    ring
  rw [e2, e3]
  rw [e1] at e
  linarith

/-- **Leibniz's rule for weak derivatives along words**: for a test function `χ` and `U = D []`
with weak derivatives `D l'` in `L²(ℝⁿ)` along the words `|l'| ≤ |l|`, of squared norms `≤ L²`,
the product `χ U` has a weak derivative `E` along `l`, measurable, vanishing off `tsupport χ`,
with `∫ E² ≤ K L²`, `K` depending only on `χ` and `l`. -/
theorem leibniz (l : List (Fin n)) : ∀ χ : (Fin n → ℝ) → ℝ, IsT χ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : List (Fin n) → (Fin n → ℝ) → ℝ) (L : ℝ),
      (∀ l' : List (Fin n), l'.length ≤ l.length → StronglyMeasurable (D l') ∧
        MemLp (D l') 2 volume ∧ IsWeakDeriv l' (D []) (D l') ∧ ∫ y, D l' y ^ 2 ≤ L ^ 2) →
      ∃ E : (Fin n → ℝ) → ℝ, StronglyMeasurable E ∧ MemLp E 2 volume ∧
        IsWeakDeriv l (fun y => χ y * D [] y) E ∧ (∀ y ∉ tsupport χ, E y = 0) ∧
        ∫ y, E y ^ 2 ≤ K * L ^ 2 := by
  induction l with
  | nil =>
    intro χ hχ
    obtain ⟨C, hC0, hC⟩ := isT_bound hχ
    refine ⟨C ^ 2, sq_nonneg _, fun D L hD => ?_⟩
    obtain ⟨hm, hD0, -, hDL⟩ := hD [] le_rfl
    refine ⟨fun y => χ y * D [] y, hχ.continuous.stronglyMeasurable.mul hm,
      memLp_mul_test hχ hD0, fun φ _ => by simp, fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy], ?_⟩
    exact (integral_sq_mul_le hχ hD0 hC).trans (mul_le_mul_of_nonneg_left hDL (sq_nonneg _))
  | cons j l ih =>
    intro χ hχ
    obtain ⟨K₁, hK₁, h₁⟩ := ih _ (isT_partialDeriv hχ j)
    obtain ⟨K₂, hK₂, h₂⟩ := ih χ hχ
    refine ⟨2 * K₁ + 2 * K₂, by positivity, fun D L hD => ?_⟩
    have hDl : ∀ l' : List (Fin n), l'.length ≤ l.length → StronglyMeasurable (D l') ∧
        MemLp (D l') 2 volume ∧ IsWeakDeriv l' (D []) (D l') ∧ ∫ y, D l' y ^ 2 ≤ L ^ 2 :=
      fun l' hl' => hD l' (hl'.trans (by simp))
    have hj := hD [j] (by simp)
    have hD' : ∀ l' : List (Fin n), l'.length ≤ l.length → StronglyMeasurable (D (j :: l')) ∧
        MemLp (D (j :: l')) 2 volume ∧ IsWeakDeriv l' (D [j]) (D (j :: l')) ∧
          ∫ y, D (j :: l') y ^ 2 ≤ L ^ 2 := fun l' hl' => by
      obtain ⟨a, b, c, d⟩ := hD (j :: l') (by simpa using hl')
      exact ⟨a, b, hj.2.2.1.tail c, d⟩
    obtain ⟨E₁, hE₁m, hE₁, hE₁w, hE₁0, hE₁L⟩ := h₁ D L hDl
    obtain ⟨E₂, hE₂m, hE₂, hE₂w, hE₂0, hE₂L⟩ := h₂ (fun l' => D (j :: l')) L hD'
    have h0 := (hD [] (Nat.zero_le _)).2.1
    refine ⟨fun y => E₁ y + E₂ y, hE₁m.add hE₂m, hE₁.add hE₂, ?_, fun y hy => ?_, ?_⟩
    · exact (isWeakDeriv_mul_single hχ h0 hj.2.1 hj.2.2.1).cons
        (IsWeakDeriv.add (memLp_mul_test (isT_partialDeriv hχ j) h0) (memLp_mul_test hχ hj.2.1)
          hE₁ hE₂ hE₁w hE₂w)
    · show E₁ y + E₂ y = 0
      rw [hE₁0 y fun h => hy (tsupport_partialDeriv_subset χ j h), hE₂0 y hy, add_zero]
    · refine (integral_add_sq_le hE₁ hE₂).trans ?_
      nlinarith

/-- **Weak derivatives against complex test functions** (real and imaginary parts). -/
theorem IsWeakDeriv.complex {l : List (Fin n)} {f v : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume)
    (hv : MemLp v 2 volume) (h : IsWeakDeriv l f v) {Ψ : (Fin n → ℝ) → ℂ}
    (hΨ : Feec.Domain.IsTest (univ : Set (Fin n → ℝ)) Ψ) :
    ∫ y, (f y : ℂ) * iterPartial l Ψ y = (-1) ^ l.length * ∫ y, (v y : ℂ) * Ψ y := by
  have e1 := h _ (hΨ.comp_clm Complex.reCLM)
  have e2 := h _ (hΨ.comp_clm Complex.imCLM)
  rw [iterPartial_clm _ hΨ.contDiff] at e1 e2
  have hΨl := isTest_iterPartial hΨ l
  have hI1 : Integrable (fun y => (f y : ℂ) * iterPartial l Ψ y) volume :=
    hf.ofReal.integrable_mul
      (hΨl.continuous.memLp_of_hasCompactSupport (p := 2) hΨl.hasCompactSupport)
  have hI2 : Integrable (fun y => (v y : ℂ) * Ψ y) volume :=
    hv.ofReal.integrable_mul
      (hΨ.continuous.memLp_of_hasCompactSupport (p := 2) hΨ.hasCompactSupport)
  have hc : ((-1 : ℂ) ^ l.length) = (((-1 : ℝ) ^ l.length : ℝ) : ℂ) := by push_cast; rfl
  rw [hc]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at e1 e2
  have r1 := Complex.reCLM.integral_comp_comm hI1
  have r2 := Complex.reCLM.integral_comp_comm hI2
  have i1 := Complex.imCLM.integral_comp_comm hI1
  have i2 := Complex.imCLM.integral_comp_comm hI2
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul] at r1 r2 i1 i2
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, ← r1, ← r2]; exact e1
  · rw [Complex.im_ofReal_mul, ← i1, ← i2]; exact e2

/-! ### Periodization -/

section Torus

open UnitAddTorus Feec.Fourier.TorusWeak Feec.Models.Cube.Sobolev

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The period cell `(-¼, ¾]ⁿ`. -/
def cell : Set (Fin n → ℝ) := univ.pi fun _ => Ioc (-(1 / 4) : ℝ) (3 / 4)

theorem measurableSet_cell : MeasurableSet (cell (n := n)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem measurePreserving_coe_cell :
    MeasurePreserving ((↑) : ℝ → UnitAddCircle) (volume.restrict (Ioc (-(1 / 4) : ℝ) (3 / 4)))
      (volume : Measure UnitAddCircle) := by
  have h := UnitAddCircle.measurePreserving_mk (-(1 / 4))
  rw [show -(1 / 4 : ℝ) + 1 = 3 / 4 by norm_num] at h
  have e : (@volume UnitAddCircle (AddCircle.measureSpace 1)) =
      (volume : Measure UnitAddCircle) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]; rfl
  exact e ▸ h

/-- `proj : ℝⁿ → 𝕋ⁿ` is measure preserving from the cell. -/
theorem measurePreserving_proj_cell :
    MeasurePreserving (proj (d := Fin n)) (volume.restrict cell) volume := by
  have h := measurePreserving_pi (fun _ : Fin n => volume.restrict (Ioc (-(1 / 4) : ℝ) (3 / 4)))
    (fun _ : Fin n => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) fun _ => measurePreserving_coe_cell
  rw [← Measure.restrict_pi_pi, ← volume_pi] at h
  exact h

theorem integral_torus_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : UnitAddTorus (Fin n) → E} (hg : AEStronglyMeasurable g volume) :
    ∫ x, g x = ∫ y in cell, g (proj y) := by
  rw [← (measurePreserving_proj_cell (n := n)).map_eq] at hg ⊢
  exact integral_map measurePreserving_proj_cell.measurable.aemeasurable hg

/-- The representative in the cell of a point of `𝕋ⁿ`. -/
def repCell (p : UnitAddTorus (Fin n)) : Fin n → ℝ :=
  fun i => (AddCircle.measurableEquivIoc 1 (-(1 / 4)) (p i) : ℝ)

theorem measurable_repCell : Measurable (repCell (n := n)) :=
  measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc 1 _).measurable.comp (measurable_pi_apply i))

theorem repCell_proj {y : Fin n → ℝ} (hy : y ∈ cell) : repCell (proj y) = y := by
  funext i
  have hi : y i ∈ Ioc (-(1 / 4) : ℝ) (-(1 / 4) + 1) := by
    have := hy i (mem_univ i); rw [show -(1 / 4 : ℝ) + 1 = 3 / 4 by norm_num]; exact this
  change ((AddCircle.equivIoc 1 (-(1 / 4)) ((y i : ℝ) : UnitAddCircle)) : ℝ) = y i
  rw [AddCircle.equivIoc_coe_eq hi]

/-- The periodization `W ∘ repCell` of a function on `ℝⁿ`. -/
def perCell (W : (Fin n → ℝ) → ℝ) (p : UnitAddTorus (Fin n)) : ℂ := (W (repCell p) : ℂ)

theorem perCell_proj (W : (Fin n → ℝ) → ℝ) {y : Fin n → ℝ} (hy : y ∈ cell) :
    perCell W (proj y) = W y := by
  rw [perCell, repCell_proj hy]

theorem measurable_perCell {W : (Fin n → ℝ) → ℝ} (hW : StronglyMeasurable W) :
    Measurable (perCell W) :=
  Complex.measurable_ofReal.comp (hW.measurable.comp measurable_repCell)

/-- The centre `(¼, …, ¼)`. -/
def cellCenter : Fin n → ℝ := fun _ => 1 / 4

/-- The support `B̄(c, 7/16) = [-3/16, 11/16]ⁿ` of the cutoff, inside the cell. -/
abbrev cutoffSupport : Set (Fin n → ℝ) := Metric.closedBall cellCenter (7 / 16)

theorem cutoffSupport_subset_cell : cutoffSupport (n := n) ⊆ cell := fun y hy i _ => by
  have := (dist_le_pi_dist y cellCenter i).trans (Metric.mem_closedBall.1 hy)
  rw [Real.dist_eq, abs_le] at this
  simp only [cellCenter] at this
  constructor <;> linarith [this.1, this.2]

theorem memLp_perCell {W : (Fin n → ℝ) → ℝ} (hWm : StronglyMeasurable W) (hW : MemLp W 2 volume) :
    MemLp (perCell W) 2 volume := by
  have hg : AEStronglyMeasurable (perCell W) volume := (measurable_perCell hWm).aestronglyMeasurable
  rw [← (measurePreserving_proj_cell (n := n)).map_eq] at hg ⊢
  rw [memLp_map_measure_iff hg measurePreserving_proj_cell.measurable.aemeasurable]
  refine (hW.restrict cell).ofReal.ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_cell] with y hy
  exact (perCell_proj W hy).symm

theorem integral_perCell_mul {W : (Fin n → ℝ) → ℝ} (hWm : StronglyMeasurable W)
    (hW0 : ∀ y ∉ cutoffSupport, W y = 0) {ψ : UnitAddTorus (Fin n) → ℂ} (hψ : Continuous ψ) :
    ∫ x, perCell W x * ψ x = ∫ y, (W y : ℂ) * ψ (proj y) := by
  rw [integral_torus_eq (g := fun x => perCell W x * ψ x)
      ((measurable_perCell hWm).aestronglyMeasurable.mul hψ.aestronglyMeasurable),
    setIntegral_congr_fun measurableSet_cell fun y hy => by rw [perCell_proj W hy]]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  rw [hW0 y fun h => hy (cutoffSupport_subset_cell h), Complex.ofReal_zero, zero_mul]

theorem norm_toLp_perCell_sq {W : (Fin n → ℝ) → ℝ} (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 volume) (hW0 : ∀ y ∉ cutoffSupport, W y = 0) :
    ‖(memLp_perCell hWm hW).toLp (perCell W)‖ ^ 2 = ∫ y, W y ^ 2 := by
  rw [Feec.Models.Cube.Geometry.norm_sq_eq_integral,
    integral_congr_ae ((memLp_perCell hWm hW).coeFn_toLp.mono fun x hx => by rw [hx])]
  rw [integral_torus_eq (g := fun x => ‖perCell W x‖ ^ 2)
      ((measurable_perCell hWm).norm.pow_const 2).aestronglyMeasurable,
    setIntegral_congr_fun measurableSet_cell fun y hy => by
      rw [perCell_proj W hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  rw [hW0 y fun h => hy (cutoffSupport_subset_cell h)]; simp

/-- `(∂^l φ) ∘ proj = ∂^l (φ ∘ proj)` for smooth `φ` on `𝕋ⁿ`. -/
theorem iterPartialT_proj {φ : UnitAddTorus (Fin n) → ℂ} (hφ : IsSmooth φ) (l : List (Fin n)) :
    iterPartialT l φ ∘ proj = iterPartial l (φ ∘ proj) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    funext y
    change partialT j (iterPartialT l φ) (proj y) =
      _root_.partialDeriv j (iterPartial l (φ ∘ proj)) y
    rw [partialT_proj ((isSmooth_iterPartialT hφ l).contDiff_one.differentiable one_ne_zero), ih]
    rfl

/-- The outer cutoff `ψ = 1` on `B̄(c, 15/32) ⊇ cutoffSupport`. -/
def ψc : ContDiffBump (cellCenter (n := n)) := ⟨15 / 32, 1 / 2, by norm_num, by norm_num⟩

/-- **Weak derivatives of a periodized function**: if `W`, supported in `cutoffSupport`, has the
weak derivative `E` (supported in `cutoffSupport`) along `l` on `ℝⁿ`, then its periodization has
the weak derivative `perCell E` along `l` on `𝕋ⁿ`. -/
theorem hasWeakDerivT_perCell {l : List (Fin n)} {W E : (Fin n → ℝ) → ℝ}
    (hWm : StronglyMeasurable W) (hEm : StronglyMeasurable E) (hW : MemLp W 2 volume)
    (hE : MemLp E 2 volume) (hW0 : ∀ y ∉ cutoffSupport, W y = 0)
    (hE0 : ∀ y ∉ cutoffSupport, E y = 0) (h : IsWeakDeriv l W E) :
    HasWeakDerivT l ((memLp_perCell hWm hW).toLp (perCell W))
      ((memLp_perCell hEm hE).toLp (perCell E)) := by
  intro φ hφ
  have hφc : ContDiff ℝ ∞ (φ ∘ proj) := hφ
  have hc : Continuous φ := continuous_of_comp_proj hφc.continuous
  have hlc : Continuous (iterPartialT l φ) := (isSmooth_iterPartialT hφ l).continuous
  -- the test function `ψ Φ` on `ℝⁿ`
  set Φ : (Fin n → ℝ) → ℂ := φ ∘ proj
  set Ψ : (Fin n → ℝ) → ℂ := fun y => ((ψc (n := n) y : ℝ) : ℂ) * Φ y
  have hΨ : Feec.Domain.IsTest (univ : Set (Fin n → ℝ)) Ψ :=
    ⟨(Complex.ofRealCLM.contDiff.comp (ψc (n := n)).contDiff).mul hφc,
      (ψc (n := n)).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
        |>.mul_right, subset_univ _⟩
  have hO : EqOn Ψ Φ (Metric.ball cellCenter (15 / 32)) := fun y hy => by
    simp only [Ψ]
    rw [(ψc (n := n)).one_of_mem_closedBall (Metric.ball_subset_closedBall hy),
      Complex.ofReal_one, one_mul]
  have hKO : cutoffSupport (n := n) ⊆ Metric.ball cellCenter (15 / 32) :=
    Metric.closedBall_subset_ball (by norm_num)
  have hPl := iterPartial_eqOn Metric.isOpen_ball hO l
  calc ∫ x, ((memLp_perCell hWm hW).toLp (perCell W) : UnitAddTorus (Fin n) → ℂ) x *
        iterPartialT l φ x
      = ∫ x, perCell W x * iterPartialT l φ x :=
        integral_congr_ae ((memLp_perCell hWm hW).coeFn_toLp.mono fun x hx => by simp only [hx])
    _ = ∫ y, (W y : ℂ) * iterPartial l Ψ y := by
        rw [integral_perCell_mul hWm hW0 hlc]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        by_cases hy : y ∈ cutoffSupport
        · rw [show iterPartialT l φ (proj y) = (iterPartialT l φ ∘ proj) y from rfl,
            iterPartialT_proj hφ l, hPl (hKO hy)]
        · rw [hW0 y hy, Complex.ofReal_zero, zero_mul, zero_mul]
    _ = (-1) ^ l.length * ∫ y, (E y : ℂ) * Ψ y := IsWeakDeriv.complex hW hE h hΨ
    _ = (-1) ^ l.length * ∫ y, (E y : ℂ) * φ (proj y) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        by_cases hy : y ∈ cutoffSupport
        · rw [hO (hKO hy)]; rfl
        · rw [hE0 y hy, Complex.ofReal_zero, zero_mul, zero_mul]
    _ = (-1) ^ l.length *
          ∫ x, ((memLp_perCell hEm hE).toLp (perCell E) : UnitAddTorus (Fin n) → ℂ) x * φ x := by
        rw [← integral_perCell_mul hEm hE0 hc]
        congr 1
        exact integral_congr_ae ((memLp_perCell hEm hE).coeFn_toLp.mono fun x hx => by
          simp only [hx])

/-- The inner cutoff `χ = 1` on `B̄(c, 3/8) ⊇ cl Q`, `tsupport χ = cutoffSupport`. -/
def χc : ContDiffBump (cellCenter (n := n)) := ⟨3 / 8, 7 / 16, by norm_num, by norm_num⟩

theorem isT_χc : IsT (χc (n := n)) :=
  ⟨(χc (n := n)).contDiff, (χc (n := n)).hasCompactSupport, subset_univ _⟩

theorem tsupport_χc : tsupport (χc (n := n)) = cutoffSupport := (χc (n := n)).tsupport_eq

theorem Q_subset_closedBall {y : Fin n → ℝ} (hy : y ∈ Feec.Models.Cube.Geometry.Q (Fin n)) :
    y ∈ Metric.closedBall (cellCenter (n := n)) (3 / 8) := by
  rw [Feec.Models.Cube.Geometry.mem_Q] at hy
  refine Metric.mem_closedBall.2 ((dist_pi_le_iff (by norm_num)).2 fun i => ?_)
  rw [Real.dist_eq, abs_le]
  simp only [cellCenter]
  constructor <;> linarith [(hy i).1, (hy i).2]

theorem Q_subset_cell : Feec.Models.Cube.Geometry.Q (Fin n) ⊆ cell := fun y hy =>
  cutoffSupport_subset_cell
    (Metric.closedBall_subset_closedBall (by norm_num) (Q_subset_closedBall hy))

open Feec.Models.Cube.DeRhamIdent Feec.Models.Cube.Geometry in
/-- **Restrictions of `H^{m+1}(ℝⁿ)` forms lie in `H^{m+1}(Q)`**: if the coefficients of
`u ∈ L²(Q; Λᵏ)` are the restrictions of `D t []` whose weak derivatives `D t l`, `|l| ≤ m + 1`, lie
in `L²(ℝⁿ)` with `∫ (D t l)² ≤ L²`, then `u ∈ H^{m+1}(Q)` and `‖u‖_{H^{m+1}(Q)} ≤ C L`, `C`
depending only on `n`, `k`, `m`. -/
theorem exists_qNorm_le (k m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (u : Feec.Domain.L2F ℝ (Feec.Models.Cube.Geometry.Q (Fin n)) (Feec.Domain.formIdx n (k : ℤ)))
      (D : Feec.Domain.formIdx n (k : ℤ) → List (Fin n) → (Fin n → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
      (∀ t l, l.length ≤ m + 1 → MemLp (D t l) 2 volume ∧ IsWeakDeriv l (D t []) (D t l) ∧
        ∫ y, D t l y ^ 2 ≤ L ^ 2) →
      (∀ t, ((u t : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ)
        =ᵐ[volume.restrict (Feec.Models.Cube.Geometry.Q (Fin n))] D t []) →
      u ∈ sobolevQ n k ((m + 1 : ℕ) : ℝ) ∧ qNorm k ((m + 1 : ℕ) : ℝ) u ≤ C * L := by
  have hχ := isT_χc (n := n)
  obtain ⟨C₀, -, hC₀⟩ := isT_bound hχ
  choose Kf hKf0 hKf using fun l : List (Fin n) => leibniz l _ hχ
  set A : ℝ := (n + 1 : ℝ) ^ m * (Fintype.card (Feec.Domain.formIdx n (k : ℤ)) : ℝ) *
    (C₀ ^ 2 + ∑ j : Fin n, Kf (List.replicate (m + 1) j))
  have hA : 0 ≤ A := by
    have : 0 ≤ ∑ j : Fin n, Kf (List.replicate (m + 1) j) := Finset.sum_nonneg fun j _ => hKf0 _
    positivity
  refine ⟨√A, Real.sqrt_nonneg _, fun u D L hL hD hu => ?_⟩
  -- measurable representatives
  set D' : Feec.Domain.formIdx n (k : ℤ) → List (Fin n) → (Fin n → ℝ) → ℝ := fun t l =>
    if h : l.length ≤ m + 1 then (hD t l h).1.aestronglyMeasurable.mk (D t l) else 0
  have hDD : ∀ t l (h : l.length ≤ m + 1), D' t l =ᵐ[volume] D t l := fun t l h => by
    simp only [D', h, dite_true]
    exact (hD t l h).1.aestronglyMeasurable.ae_eq_mk.symm
  have hD' : ∀ t l, l.length ≤ m + 1 → StronglyMeasurable (D' t l) ∧ MemLp (D' t l) 2 volume ∧
      IsWeakDeriv l (D' t []) (D' t l) ∧ ∫ y, D' t l y ^ 2 ≤ L ^ 2 := fun t l h => by
    obtain ⟨h1, h2, h3⟩ := hD t l h
    have h0 := hDD t [] (Nat.zero_le _)
    refine ⟨by
        simp only [D', h, dite_true]; exact (hD t l h).1.aestronglyMeasurable.stronglyMeasurable_mk,
      h1.ae_eq (hDD t l h).symm, fun φ hφ => ?_, ?_⟩
    · have ea : ∫ y, D' t [] y * iterPartial l φ y = ∫ y, D t [] y * iterPartial l φ y :=
        integral_congr_ae (h0.mono fun y hy => by simp only [hy])
      have eb : ∫ y, D' t l y * φ y = ∫ y, D t l y * φ y :=
        integral_congr_ae ((hDD t l h).mono fun y hy => by simp only [hy])
      rw [ea, eb]
      exact h2 φ hφ
    · have ec : ∫ y, D' t l y ^ 2 = ∫ y, D t l y ^ 2 :=
        integral_congr_ae ((hDD t l h).mono fun y hy => by simp only [hy])
      rw [ec]
      exact h3
  -- the cut-off forms and their weak derivatives
  set W : Feec.Domain.formIdx n (k : ℤ) → (Fin n → ℝ) → ℝ := fun t y => χc (n := n) y * D' t [] y
  have hE : ∀ t (l : List (Fin n)), l.length ≤ m + 1 → ∃ E : (Fin n → ℝ) → ℝ,
      StronglyMeasurable E ∧ MemLp E 2 volume ∧ IsWeakDeriv l (W t) E ∧
        (∀ y ∉ tsupport (χc (n := n)), E y = 0) ∧ ∫ y, E y ^ 2 ≤ Kf l * L ^ 2 :=
    fun t l hl => hKf l (D' t) L fun l' hl' => hD' t l' (hl'.trans hl)
  choose E hEm hE2 hEw hE0 hEL using hE
  have hW0 : ∀ t, StronglyMeasurable (W t) := fun t =>
    hχ.continuous.stronglyMeasurable.mul (hD' t [] (Nat.zero_le _)).1
  have hW2 : ∀ t, MemLp (W t) 2 volume := fun t => memLp_mul_test hχ (hD' t [] (Nat.zero_le _)).2.1
  have hWK : ∀ t, ∀ y ∉ cutoffSupport, W t y = 0 := fun t y hy => by
    have h0 : (χc (n := n) : (Fin n → ℝ) → ℝ) y = 0 :=
      image_eq_zero_of_notMem_tsupport (by rwa [tsupport_χc])
    simp only [W]; rw [h0, zero_mul]
  have hEK : ∀ t l (hl : l.length ≤ m + 1), ∀ y ∉ cutoffSupport, E t l hl y = 0 :=
    fun t l hl y hy => hE0 t l hl y (by rwa [tsupport_χc])
  -- the torus field and its coefficient sequence
  set G : Feec.Fourier.TorusWeak.Field (Fin n) (Feec.Domain.formIdx n (k : ℤ)) :=
    WithLp.toLp 2 fun t => (memLp_perCell (hW0 t) (hW2 t)).toLp (perCell (W t))
  set x : Seq n k := Feec.Fourier.Torus.fieldFourier (Fin n) _ G
  have hphys : physF k x = G := by simp [x, physF]
  have hder : ∀ t l (hl : l.length ≤ m + 1), HasWeakDerivT l (physF k x t)
      ((memLp_perCell (hEm t l hl) (hE2 t l hl)).toLp (perCell (E t l hl))) := fun t l hl => by
    rw [hphys]
    exact hasWeakDerivT_perCell (hW0 t) (hEm t l hl) (hW2 t) (hE2 t l hl) (hWK t) (hEK t l hl)
      (hEw t l hl)
  have hmem : MemSob ((m + 1 : ℕ) : ℝ) x :=
    (memSob_nat_iff x (m + 1)).2 fun t l hl => ⟨_, hder t l hl⟩
  have hJ : Jinvf k x = u := by
    have e1 : Jinvf k x = reF (Q (Fin n)) _ (resQF G) := by
      change Jinv (Fin n) _ x = _
      rw [Jinv_apply]; simp [x]
    rw [e1]
    ext1 t
    refine Lp.ext ?_
    rw [reF_apply, resQF_apply]
    have h1 := Feec.Models.Cube.RowWise.coeFn_reL (resQ (G t))
    have h2 := coeFn_resQ (G t)
    have h3 : ∀ᵐ y ∂volume.restrict (Q (Fin n)),
        ((G t : Lp ℂ 2 _) : UnitAddTorus (Fin n) → ℂ) (Feec.Fourier.TorusWeak.proj y) =
          perCell (W t) (Feec.Fourier.TorusWeak.proj y) :=
      ae_Q_of_ae_boxSet (ae_restrict_of_ae (memLp_perCell (hW0 t) (hW2 t)).coeFn_toLp)
    have h4 := ae_restrict_of_ae (μ := volume) (s := Q (Fin n)) (hDD t [] (Nat.zero_le _))
    filter_upwards [h1, h2, h3, h4, hu t, ae_restrict_mem measurableSet_Q] with y e1 e2 e3 e4 e5 hy
    rw [e1, e2, e3, perCell_proj _ (Q_subset_cell hy), Complex.ofReal_re, e5]
    simp only [W]
    rw [(χc (n := n)).one_of_mem_closedBall (Q_subset_closedBall hy), one_mul, e4]
  refine ⟨⟨x, hmem, hJ⟩, (qNorm_le hmem hJ).trans ?_⟩
  -- the norm bound
  set v : Fin n → Feec.Domain.formIdx n (k : ℤ) →
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))) :=
    fun j t => (memLp_perCell (hEm t _ (by simp)) (hE2 t _ (by simp))).toLp
      (perCell (E t (List.replicate (m + 1) j) (by simp)))
  have hS := sobSum_le x v fun j t => hder t _ (by simp)
  have hx2 : ‖x‖ ^ 2 ≤ (Fintype.card (Feec.Domain.formIdx n (k : ℤ)) : ℝ) * (C₀ ^ 2 * L ^ 2) := by
    rw [show ‖x‖ = ‖G‖ by simp [x], PiLp.norm_sq_eq_of_L2]
    refine (Finset.sum_le_sum (g := fun _ => C₀ ^ 2 * L ^ 2) fun t _ => ?_).trans_eq (by simp)
    change ‖(memLp_perCell (hW0 t) (hW2 t)).toLp (perCell (W t))‖ ^ 2 ≤ _
    rw [norm_toLp_perCell_sq (hW0 t) (hW2 t) (hWK t)]
    exact (integral_sq_mul_le hχ (hD' t [] (Nat.zero_le _)).2.1 hC₀).trans
      (mul_le_mul_of_nonneg_left (hD' t [] (Nat.zero_le _)).2.2.2 (sq_nonneg _))
  have hv2 : ∑ j, ∑ t, ‖v j t‖ ^ 2 ≤ (Fintype.card (Feec.Domain.formIdx n (k : ℤ)) : ℝ) *
      ((∑ j : Fin n, Kf (List.replicate (m + 1) j)) * L ^ 2) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ =>
      (Finset.sum_le_sum (g := fun _ => Kf (List.replicate (m + 1) j) * L ^ 2)
        fun t _ => ?_).trans_eq (by simp)
    simp only [v]
    rw [norm_toLp_perCell_sq (hEm t _ (by simp)) (hE2 t _ (by simp)) (hEK t _ (by simp))]
    exact hEL t _ _
  have hfin : sobSum ((m + 1 : ℕ) : ℝ) x ≤ A * L ^ 2 := by
    refine hS.trans ?_
    have h1 : 0 ≤ (n + 1 : ℝ) ^ m := by positivity
    calc (n + 1 : ℝ) ^ m * (‖x‖ ^ 2 + ∑ j, ∑ t, ‖v j t‖ ^ 2)
        ≤ (n + 1 : ℝ) ^ m * ((Fintype.card (Feec.Domain.formIdx n (k : ℤ)) : ℝ) * (C₀ ^ 2 * L ^ 2)
          + (Fintype.card (Feec.Domain.formIdx n (k : ℤ)) : ℝ) *
            ((∑ j : Fin n, Kf (List.replicate (m + 1) j)) * L ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hx2 hv2) h1
      _ = A * L ^ 2 := by simp only [A]; ring
  calc √(sobSum ((m + 1 : ℕ) : ℝ) x) ≤ √(A * L ^ 2) := Real.sqrt_le_sqrt hfin
    _ = √A * L := by rw [Real.sqrt_mul hA, Real.sqrt_sq hL]

end Torus

end Feec.Models.Cube.SobolevRestriction
