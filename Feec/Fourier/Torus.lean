module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Feec.Fourier.ClosedRange
public import Feec.Fourier.FibreReducing

/-!
# Symbol complexes on the torus `𝕋ᵈ = ℝᵈ/ℤᵈ`

A constant-coefficient complex on `𝕋ᵈ` is, after Fourier series, a symbol complex over the
lattice `ℤᵈ` with counting measure, at the frequencies `ξ_k = 2πk`. This file sets up that
model for any finite index type `d` (dimension `#d`), any coefficient field `𝕜 = ℝ, ℂ` and any
complex shape, and proves the features that distinguish the torus from `ℝᵈ`:

* every symbol is measurable and every fibre projection is measurable (counting measure), so
  fibre reducing subspaces need no measurability proof (`fibreReducing`);
* the nonzero frequencies are bounded away from `0`, `2π ≤ |2πk|` (`two_pi_le_norm_freq`), so a
  fibre gap on `|ξ| ≥ 2π` gives **closed range** (`closedRangeAt_of_gap`).

The coefficient isometry `fieldFourier : L²(𝕋ᵈ; ℂᴾ) ≃ₗᵢ L²(ℤᵈ, count; ℂᴾ)` (Parseval, from
Mathlib's `UnitAddTorus.mFourierBasis`) identifies the model with fields on the torus.

## Main definitions and results

* `Torus.freq k = 2πk ∈ ℝᵈ`; `Torus.symbolComplex S`, `Torus.complex S` for a continuous family
  of fibre complexes `S`.
* `Torus.fibreReducing`: fibre reducing subspaces of `S` give a reducing subcomplex of the torus
  model (hence constraint propagation, `Feec.Fourier.FibreReducing.propagates`).
* `Torus.closedRangeAt_of_gap`, `Torus.dual_closedRangeAt_of_gap`.
* `Torus.fieldFourier`, `Torus.fieldFourier_apply` (the entries are the Fourier coefficients
  `mFourierCoeff`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10–4.11 (the periodic analogue of the complexes (4.2), (4.16))
* Mathlib, `Mathlib.Analysis.Fourier.AddCircleMulti`
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal
open MeasureTheory LinearPMap Set

namespace Feec.Fourier.Torus

variable {d : Type*}

/-! ### Frequencies -/

/-- The frequency `ξ_k = 2πk` of the Fourier mode `e^{2πi k·x}` on `𝕋ᵈ = ℝᵈ/ℤᵈ`. -/
def freq (k : d → ℤ) : EuclideanSpace ℝ d := WithLp.toLp 2 fun j => 2 * Real.pi * k j

@[simp] theorem freq_apply (k : d → ℤ) (j : d) : freq k j = 2 * Real.pi * k j := rfl

@[simp] theorem freq_zero : freq (0 : d → ℤ) = 0 := by
  ext j; simp

@[simp] theorem freq_neg (k : d → ℤ) : freq (-k) = -freq k := by
  ext j; simp

variable [Fintype d]

theorem norm_freq_sq (k : d → ℤ) : ‖freq k‖ ^ 2 = (2 * Real.pi) ^ 2 * ∑ j, ((k j : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [freq_apply, Real.norm_eq_abs, sq_abs]; ring

/-- **The torus frequencies are bounded away from `0`**: `2π ≤ |2πk|` for `k ≠ 0`. -/
theorem two_pi_le_norm_freq {k : d → ℤ} (hk : k ≠ 0) : 2 * Real.pi ≤ ‖freq k‖ := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1 : ℝ) ≤ ((k j : ℝ)) ^ 2 := by
    have : (1 : ℤ) ≤ k j ^ 2 := by
      have := sq_pos_of_ne_zero hj; omega
    exact_mod_cast this
  have h2 : ((k j : ℝ)) ^ 2 ≤ ∑ j, ((k j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h3 : (2 * Real.pi) ^ 2 ≤ ‖freq k‖ ^ 2 := by
    rw [norm_freq_sq]
    nlinarith [Real.pi_pos, sq_nonneg (2 * Real.pi)]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  nlinarith [norm_nonneg (freq k), sq_nonneg (‖freq k‖ - 2 * Real.pi),
    sq_nonneg (‖freq k‖ + 2 * Real.pi)]

theorem freq_eq_zero_iff {k : d → ℤ} : freq k = 0 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have := two_pi_le_norm_freq hk
    rw [h, norm_zero] at this
    linarith [Real.pi_pos]
  · rintro rfl; exact freq_zero

/-! ### The torus model of a fibre complex -/

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  [∀ i, FiniteDimensional 𝕜 (E i)]

/-- The torus symbol complex of a continuous family of fibre complexes: symbols `S.m i j (2πk)`
on `ℓ²(ℤᵈ) = L²(ℤᵈ, count)`. -/
def symbolComplex (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E) :
    SymbolComplex 𝕜 (Measure.count : Measure (d → ℤ)) c E :=
  S.toSymbolComplex _ freq (Measurable.of_discrete).aemeasurable

@[simp] theorem symbolComplex_m (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E) (i j : ι)
    (k : d → ℤ) : (symbolComplex S).m i j k = S.m i j (freq k) := rfl

variable [∀ i, CompleteSpace (E i)]

/-- **The Hilbert complex of a constant-coefficient complex on `𝕋ᵈ`** (Fourier side). -/
def complex (S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E) :
    HilbertComplex 𝕜 c fun i => Lp (E i) 2 (Measure.count : Measure (d → ℤ)) :=
  (symbolComplex S).toHilbertComplex

/-- On the torus, fibre reducing subspaces always give a fibre reducing family (all fibre
projections are measurable for the counting measure). -/
theorem fibreReducing {S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E}
    {K : ∀ i, EuclideanSpace ℝ d → Submodule 𝕜 (E i)} [∀ i ξ, (K i ξ).HasOrthogonalProjection]
    (h : S.IsFibreReducing K) : FibreReducing (symbolComplex S) fun i k => K i (freq k) :=
  h.toFibreReducing _ freq _ fun _ => AEStronglyMeasurable.of_discrete

/-- **Closed range on the torus**: a fibre gap at the frequencies `|ξ| ≥ 2π`, with a vanishing
symbol at `ξ = 0`, gives closed range of the torus complex. -/
theorem closedRangeAt_of_gap {S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E} {i : ι} {C : ℝ}
    (h0 : S.m (c.prev i) i 0 = 0)
    (hgap : ∀ ξ : EuclideanSpace ℝ d, 2 * Real.pi ≤ ‖ξ‖ →
      ∀ v ∈ (LinearMap.ker (S.m (c.prev i) i ξ : E (c.prev i) →ₗ[𝕜] E i))ᗮ,
        ‖v‖ ≤ C * ‖S.m (c.prev i) i ξ v‖) :
    (complex S).ClosedRangeAt i := by
  refine (symbolComplex S).closedRangeAt_of_gap (C := C) (Filter.Eventually.of_forall fun k => ?_)
  by_cases hk : k = 0
  · subst hk
    intro v hv
    simp only [symbolComplex_m, freq_zero, h0] at hv ⊢
    have : LinearMap.ker ((0 : E (c.prev i) →L[𝕜] E i) : E (c.prev i) →ₗ[𝕜] E i) = ⊤ := by
      ext; simp
    rw [this, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hv
    simp [hv]
  · exact hgap _ (two_pi_le_norm_freq hk)

/-- Closed range of the dual torus complex from a fibre gap of the outgoing symbol. -/
theorem dual_closedRangeAt_of_gap {S : FibreComplex 𝕜 (EuclideanSpace ℝ d) c E} {i j : ι}
    (hij : c.Rel i j) {C : ℝ} (h0 : S.m i j 0 = 0)
    (hgap : ∀ ξ : EuclideanSpace ℝ d, 2 * Real.pi ≤ ‖ξ‖ →
      ∀ v ∈ (LinearMap.ker (S.m i j ξ : E i →ₗ[𝕜] E j))ᗮ, ‖v‖ ≤ C * ‖S.m i j ξ v‖) :
    (complex S).dual.ClosedRangeAt i := by
  have hj : (complex S).ClosedRangeAt j := by
    have hprev := (c.prev_eq' hij)
    subst hprev
    exact closedRangeAt_of_gap h0 hgap
  exact ((complex S).dual_closedRangeAt_iff hij).2 hj

/-! ### Fourier coefficients of fields on `𝕋ᵈ` -/

section Coefficients

variable {P : Type*} [Fintype P]

omit [Fintype d] in
/-- The swapped sequence of components is square-summable. -/
theorem swap_memℓp (f : PiLp 2 fun _ : P => lp (fun _ : d → ℤ => ℂ) 2) :
    Memℓp (fun k => (WithLp.toLp 2 fun p => (f p : (d → ℤ) → ℂ) k : EuclideanSpace ℂ P)) 2 := by
  refine memℓp_gen ?_
  have : ∀ k, ‖(WithLp.toLp 2 fun p => (f p : (d → ℤ) → ℂ) k : EuclideanSpace ℂ P)‖ ^
      (2 : ℝ≥0∞).toReal = ∑ p, ‖(f p : (d → ℤ) → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal := by
    intro k
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, EuclideanSpace.norm_sq_eq]
  simp_rw [this]
  exact summable_sum fun p _ => (lp.memℓp (f p)).summable (by norm_num)

omit [Fintype d] in
theorem swap_inv_memℓp (g : lp (fun _ : d → ℤ => EuclideanSpace ℂ P) 2) (p : P) :
    Memℓp (fun k => (g k : EuclideanSpace ℂ P) p) 2 :=
  (lp.memℓp g).mono' fun k => PiLp.norm_apply_le (g k) p

/-- Exchanging the finite `ℓ²` sum over components with the sum over frequencies. -/
def swapL2 : PiLp 2 (fun _ : P => lp (fun _ : d → ℤ => ℂ) 2) ≃ₗᵢ[ℂ]
    lp (fun _ : d → ℤ => EuclideanSpace ℂ P) 2 where
  toFun f := ⟨fun k => WithLp.toLp 2 fun p => (f p : (d → ℤ) → ℂ) k, swap_memℓp f⟩
  map_add' f g := by ext k p; simp; rfl
  map_smul' c f := by ext k p; simp
  invFun g := WithLp.toLp 2 fun p => ⟨fun k => (g k : EuclideanSpace ℂ P) p, swap_inv_memℓp g p⟩
  left_inv f := by ext p k; rfl
  right_inv g := by ext k p; rfl
  norm_map' f := by
    have h1 := lp.hasSum_norm (p := 2) (by norm_num)
      (⟨fun k => WithLp.toLp 2 fun p => (f p : (d → ℤ) → ℂ) k, swap_memℓp f⟩ :
        lp (fun _ : d → ℤ => EuclideanSpace ℂ P) 2)
    have h2 : HasSum (fun k => ∑ p, ‖(f p : (d → ℤ) → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal)
        (∑ p, ‖f p‖ ^ (2 : ℝ≥0∞).toReal) :=
      hasSum_sum fun p _ => lp.hasSum_norm (by norm_num) (f p)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2
    have h3 := h1.unique (by
      convert h2 using 2 with k
      rw [EuclideanSpace.norm_sq_eq])
    rw [← PiLp.norm_sq_eq_of_L2] at h3
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

omit [Fintype d] in
@[simp] theorem swapL2_apply (f : PiLp 2 fun _ : P => lp (fun _ : d → ℤ => ℂ) 2) (k : d → ℤ)
    (p : P) : swapL2 f k p = (f p : (d → ℤ) → ℂ) k := rfl

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Mathlib.Analysis.Fourier.AddCircleMulti`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- **Fourier coefficients of `L²` fields on `𝕋ᵈ`** (Parseval): componentwise
`UnitAddTorus.mFourierBasis.repr`, then `swapL2` and `lp.equivLpCount`; a linear isometric
equivalence `L²(𝕋ᵈ; ℂᴾ) ≃ₗᵢ L²(ℤᵈ, count; ℂᴾ)`. -/
def fieldFourier (d P : Type*) [Fintype d] [Fintype P] :
    PiLp 2 (fun _ : P => Lp ℂ 2 (volume : Measure (UnitAddTorus d))) ≃ₗᵢ[ℂ]
      Lp (EuclideanSpace ℂ P) 2 (Measure.count : Measure (d → ℤ)) :=
  ((LinearIsometryEquiv.piLpCongrRight 2 fun _ => UnitAddTorus.mFourierBasis.repr).trans
    swapL2).trans (lp.equivLpCount ℂ (d → ℤ) (EuclideanSpace ℂ P) 2)

/-- The entries of `fieldFourier d P f` are the Fourier coefficients of the components of `f`. -/
theorem fieldFourier_apply (f : PiLp 2 fun _ : P => Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (k : d → ℤ) (p : P) :
    (fieldFourier d P f : (d → ℤ) → EuclideanSpace ℂ P) k p =
      UnitAddTorus.mFourierCoeff (f p) k := by
  simp [fieldFourier, LinearIsometryEquiv.piLpCongrRight_apply, UnitAddTorus.mFourierBasis_repr]

end Coefficients

end Feec.Fourier.Torus
