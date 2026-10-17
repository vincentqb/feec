module

public import Feec.Fourier.Torus
public import Feec.Fourier.ExteriorSymbol

/-!
# The `L²` de Rham complex of the torus `𝕋ᵈ`, in every dimension and degree

The de Rham complex `L²Λ⁰(𝕋ᵈ) → L²Λ¹(𝕋ᵈ) → ⋯ → L²Λᵈ(𝕋ᵈ)` with its maximal (weak) domains, on the
Fourier side: `k`-forms are `ℓ²(ℤᵈ; Λᵏ)` and the exterior derivative is the multiplier
`d_ξ = i ξ ∧ ·` at `ξ = 2πk` (`Feec.Fourier.Exterior.deRham`). This is the torus model of the
abstract theory: every result of `Feec.HilbertComplex` (Hodge decomposition, Hodge wave equation,
constraint propagation) applies to it.

## Main results

* `DeRham.complex d`: the Hilbert complex, on `ComplexShape.up ℕ` (degrees `k > #d` are zero).
* **`closedRangeAt`**, `dual_closedRangeAt`: closed range in every degree, with the sharp
  **Poincaré inequality** `‖u‖ ≤ (2π)⁻¹ ‖d u‖` on `D(d) ∩ N(d)ᗮ` (`norm_le_of_mem_orthogonal`),
  from the fibre identity `‖d_ξ v‖ = |ξ| ‖v‖` on `N(d_ξ)ᗮ` and `|2πk| ≥ 2π`.
* **`mem_harmonic_iff`**: the harmonic `k`-forms are the constant forms (only the zero mode);
  `harmonicEquiv : ℌᵏ ≃ₗ Λᵏ`, and **`cohomologyEquiv : Hᵏ(𝕋ᵈ) ≃ₗ Λᵏ`** with
  `finrank_cohomology : dim Hᵏ(𝕋ᵈ) = (d choose k)` (the Betti numbers of the torus).

## References

* [AFW2010], [Arnold2018] (the de Rham complex as a Hilbert complex)
* [QuennevilleBelair2015], §4.2
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.Exterior

namespace Feec.Models.Torus.DeRham

variable (d : Type*) [Fintype d] [LinearOrder d]

/-- `L²` `k`-forms on `𝕋ᵈ`, by their Fourier coefficients `ℓ²(ℤᵈ; Λᵏ)`. -/
abbrev L2Form (k : ℕ) : Type _ := Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))

/-- **The `L²` de Rham complex of `𝕋ᵈ`** (Fourier coefficients). -/
abbrev complex : HilbertComplex ℂ (ComplexShape.up ℕ)
    fun k => Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ)) :=
  Fourier.Torus.complex (deRham d)

variable {d}

/-- The fibre gap of every arrow at the torus frequencies `|ξ| ≥ 2π`. -/
theorem gap (i j : ℕ) {ξ : EuclideanSpace ℝ d} (hξ : 2 * Real.pi ≤ ‖ξ‖) :
    ∀ v ∈ (LinearMap.ker ((deRham d).m i j ξ : Form ℂ d i →ₗ[ℂ] Form ℂ d j))ᗮ,
      ‖v‖ ≤ (2 * Real.pi)⁻¹ * ‖(deRham d).m i j ξ v‖ := by
  intro v hv
  by_cases h : i + 1 = j
  · subst h
    rw [norm_deRham_of_mem_orthogonal hv, ← mul_assoc]
    have h2pi : 0 < 2 * Real.pi := by positivity
    have : 1 ≤ (2 * Real.pi)⁻¹ * ‖ξ‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ h2pi, one_mul]; exact hξ
    nlinarith [norm_nonneg v]
  · have h0 : (deRham d).m i j ξ = 0 := by rw [(deRham d).shape i j h]; rfl
    rw [h0] at hv ⊢
    have : LinearMap.ker ((0 : Form ℂ d i →L[ℂ] Form ℂ d j) : Form ℂ d i →ₗ[ℂ] Form ℂ d j) = ⊤ := by
      ext; simp
    rw [this, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hv
    simp [hv]

/-- **The de Rham complex of `𝕋ᵈ` has closed range in every degree.** -/
theorem closedRangeAt (k : ℕ) : (complex d).ClosedRangeAt k :=
  Fourier.Torus.closedRangeAt_of_gap (deRham_m_zero _ _) fun _ hξ => gap _ _ hξ

/-- Closed range of the adjoint complex in every degree. -/
theorem dual_closedRangeAt (k : ℕ) : (complex d).dual.ClosedRangeAt k :=
  Fourier.Torus.dual_closedRangeAt_of_gap (j := k + 1) rfl (deRham_m_zero _ _)
    fun _ hξ => gap _ _ hξ

/-- **Poincaré inequality on `𝕋ᵈ` with the sharp constant `(2π)⁻¹`**:
`‖u‖ ≤ (2π)⁻¹ ‖d u‖` for `u ∈ D(d) ∩ N(d)ᗮ`. -/
theorem norm_le_of_mem_orthogonal {k : ℕ} (u : ((complex d).d k (k + 1)).domain)
    (hu : (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) ∈
      ((complex d).d k (k + 1)).kerᗮ) :
    ‖(u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ)))‖ ≤
      (2 * Real.pi)⁻¹ * ‖(complex d).d k (k + 1) u‖ := by
  refine (Fourier.Torus.symbolComplex (deRham d)).norm_le_of_gap
    (Filter.Eventually.of_forall fun q => ?_) u hu
  by_cases hq : q = 0
  · subst hq
    intro v hv
    simp only [Fourier.Torus.symbolComplex_m, Fourier.Torus.freq_zero, deRham_m_zero] at hv ⊢
    have : LinearMap.ker ((0 : Form ℂ d k →L[ℂ] Form ℂ d (k + 1)) :
        Form ℂ d k →ₗ[ℂ] Form ℂ d (k + 1)) = ⊤ := by ext; simp
    rw [this, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hv
    simp [hv]
  · exact gap _ _ (Fourier.Torus.two_pi_le_norm_freq hq)

/-! ### Harmonic forms and cohomology -/

/-- **Harmonic forms on `𝕋ᵈ` are the constant forms**: `u ∈ ℌᵏ` iff all its nonzero Fourier
modes vanish. -/
theorem mem_harmonic_iff {k : ℕ} {u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))} :
    u ∈ (complex d).harmonic k ↔ ∀ q, q ≠ 0 → u q = 0 := by
  change u ∈ (Fourier.Torus.symbolComplex (deRham d)).toHilbertComplex.harmonic k ↔ _
  rw [SymbolComplex.harmonic_toHilbertComplex, Operator.mem_fibreSub, Measure.ae_count_iff]
  refine forall_congr' fun q => ?_
  by_cases hq : q = 0
  · subst hq
    simp only [Fourier.Torus.symbolComplex_m, Fourier.Torus.freq_zero, deRham_m_zero, _root_.map_zero]
    simp
  · have hξ : Fourier.Torus.freq q ≠ 0 := fun h => hq (Fourier.Torus.freq_eq_zero_iff.1 h)
    simp only [Fourier.Torus.symbolComplex_m, deRham_harmonic_fibre hξ k, Submodule.mem_bot]
    exact ⟨fun h _ => h, fun h => h hq⟩

/-- The constant `k`-form `v` (supported on the zero mode). -/
def const (k : ℕ) (v : Form ℂ d k) : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ)) :=
  lp.equivLpCount ℂ (d → ℤ) (Form ℂ d k) 2 (lp.single 2 0 v)

omit [LinearOrder d] in
theorem const_apply (k : ℕ) (v : Form ℂ d k) (q : d → ℤ) :
    (const k v : (d → ℤ) → Form ℂ d k) q = if q = 0 then v else 0 := by
  rw [const, lp.coeFn_equivLpCount, lp.single_apply]
  split_ifs with h
  · subst h; simp
  · simp [Pi.single, Function.update, h]

theorem const_mem_harmonic (k : ℕ) (v : Form ℂ d k) : const k v ∈ (complex d).harmonic k :=
  mem_harmonic_iff.2 fun q hq => by simp [const_apply, hq]

/-- **`ℌᵏ(𝕋ᵈ) ≅ Λᵏ`**: a harmonic form is its constant coefficient. -/
def harmonicEquiv (k : ℕ) : (complex d).harmonic k ≃ₗ[ℂ] Form ℂ d k where
  toFun u := (u : Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))) 0
  map_add' u v := by
    simp only [Submodule.coe_add]
    exact Measure.ae_count_iff.1 (Lp.coeFn_add (u : L2Form d k) (v : L2Form d k)) 0
  map_smul' a u := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact Measure.ae_count_iff.1 (Lp.coeFn_smul a (u : L2Form d k)) 0
  invFun v := ⟨const k v, const_mem_harmonic k v⟩
  left_inv u := by
    refine Subtype.ext (Lp.ext_count fun q => ?_)
    change (const k _ : (d → ℤ) → Form ℂ d k) q = _
    rw [const_apply]
    split_ifs with h
    · subst h; rfl
    · exact (mem_harmonic_iff.1 u.2 q h).symm
  right_inv v := by
    change (const k v : (d → ℤ) → Form ℂ d k) 0 = v
    simp [const_apply]

/-- **The cohomology of the torus**: `Hᵏ(𝕋ᵈ) ≅ Λᵏ`. -/
def cohomologyEquiv (k : ℕ) : (complex d).cohomology k ≃ₗ[ℂ] Form ℂ d k :=
  ((complex d).cohomologyEquivHarmonic (closedRangeAt k)).trans (harmonicEquiv k)

/-- **The Betti numbers of the torus**: `dim Hᵏ(𝕋ᵈ) = (#d choose k)`. -/
theorem finrank_cohomology (k : ℕ) :
    Module.finrank ℂ ((complex d).cohomology k) = (Fintype.card d).choose k := by
  rw [(cohomologyEquiv k).finrank_eq, finrank_euclideanSpace, Fintype.card_finset_len]

end Feec.Models.Torus.DeRham
