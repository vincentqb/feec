module

public import Feec.Fourier.Torus
public import Feec.Fourier.ExteriorSymbol
public import Feec.Fourier.SpectralGalerkin
public import Feec.Fourier.TorusWeak

/-!
# The `L²` de Rham complex of the torus `𝕋ᵈ`, in every dimension and degree

The de Rham complex `L²Λ⁰(𝕋ᵈ) → L²Λ¹(𝕋ᵈ) → ⋯ → L²Λᵈ(𝕋ᵈ)` with its maximal (weak) domains, on the
Fourier side: `k`-forms are `ℓ²(ℤᵈ; Λᵏ)` and the exterior derivative is the multiplier
`d_ξ = i ξ ∧ ·` at `ξ = 2πk` (`Feec.Fourier.Exterior.deRham`). This is the torus model of the
abstract theory: every result of `Feec.HilbertComplex` (Hodge decomposition, Hodge wave equation,
constraint propagation) applies to it.

## Main results

* `DeRham.complex d`: the Hilbert complex, on `ComplexShape.up ℤ` (the spaces of the degrees
  `k < 0` and `k > #d` are zero).
* **`closedRangeAt`**, `dual_closedRangeAt`: closed range in every degree, with the sharp
  **Poincaré inequality** `‖u‖ ≤ (2π)⁻¹ ‖d u‖` on `D(d) ∩ N(d)ᗮ` (`norm_le_of_mem_orthogonal`),
  from the fibre identity `‖d_ξ v‖ = |ξ| ‖v‖` on `N(d_ξ)ᗮ` and `|2πk| ≥ 2π`.
* **`mem_harmonic_iff`**: the harmonic `k`-forms are the constant forms (only the zero mode);
  `harmonicEquiv : ℌᵏ ≃ₗ Λᵏ`, so `ℌᵏ` is finite-dimensional with `finrank_harmonic :
  dim ℌᵏ = (#d choose k)`, and **`cohomologyEquiv : Hᵏ(𝕋ᵈ) ≃ₗ Λᵏ`** with
  `finrank_cohomology : dim Hᵏ(𝕋ᵈ) = (#d choose k)` (the Betti numbers of the torus).
* `window d`: the full complex `Λ⁰ → ⋯ → Λᵈ` on `Fin (d + 1)`; **`window_hasCompactProperty`**
  (Rellich on `𝕋ᵈ`, from the fibre Cartan identity `window_cartan`) and **`window_eigenDense`**:
  the Hodge wave group of the torus de Rham complex has a dense set of eigenvectors (discrete
  spectrum).
* `windowReal`: the real structure of the window (real forms have `ω̂(-k) = conj ω̂(k)`).
* **`mem_graph_iff_isWeak`**: the multiplier `d` is the weak exterior derivative of `L²` forms on
  `𝕋ᵈ`, through their Fourier coefficients (`Fourier.Torus.fieldFourier`), tested against all
  smooth functions (`Feec.Fourier.TorusWeak`); coefficientwise (`isWeak_deRham_iff`), `w = d u`
  weakly iff `∫ w_s φ = -Σ_{j ∈ s} ε(j, s) ∫ u_{s ∖ j} ∂_j φ` for every `(k + 1)`-subset `s` and
  every smooth `φ`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
  (the de Rham complex as a Hilbert complex)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018] (the de Rham complex as a Hilbert
  complex)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.Exterior

namespace Feec.Models.Torus.DeRham

variable (d : Type*) [Fintype d] [LinearOrder d]

/-- `L²` `k`-forms on `𝕋ᵈ`, by their Fourier coefficients `ℓ²(ℤᵈ; Λᵏ)`. -/
abbrev L2Form (k : ℤ) : Type _ := Lp (Form ℂ d k) 2 (Measure.count : Measure (d → ℤ))

/-- **The `L²` de Rham complex of `𝕋ᵈ`** (Fourier coefficients). -/
abbrev complex : HilbertComplex ℂ (ComplexShape.up ℤ) (L2Form d) :=
  Fourier.Torus.complex (deRham d)

variable {d}

/-- The fibre gap of every arrow at the torus frequencies `|ξ| ≥ 2π`. -/
theorem gap (i j : ℤ) {ξ : EuclideanSpace ℝ d} (hξ : 2 * Real.pi ≤ ‖ξ‖) :
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
    simp [eq_zero_of_mem_orthogonal_ker_zero hv]

/-- **The de Rham complex of `𝕋ᵈ` has closed range in every degree.** -/
theorem closedRangeAt (k : ℤ) : (complex d).ClosedRangeAt k :=
  Fourier.Torus.closedRangeAt_of_gap (deRham_m_zero _ _) fun _ hξ => gap _ _ hξ

/-- Closed range of the adjoint complex in every degree. -/
theorem dual_closedRangeAt (k : ℤ) : (complex d).dual.ClosedRangeAt k :=
  Fourier.Torus.dual_closedRangeAt_of_gap (j := k + 1) rfl (deRham_m_zero _ _)
    fun _ hξ => gap _ _ hξ

/-- **Poincaré inequality on `𝕋ᵈ` with the sharp constant `(2π)⁻¹`**:
`‖u‖ ≤ (2π)⁻¹ ‖d u‖` for `u ∈ D(d) ∩ N(d)ᗮ`. -/
theorem norm_le_of_mem_orthogonal {k : ℤ} (u : ((complex d).d k (k + 1)).domain)
    (hu : (u : L2Form d k) ∈ ((complex d).d k (k + 1)).kerᗮ) :
    ‖(u : L2Form d k)‖ ≤ (2 * Real.pi)⁻¹ * ‖(complex d).d k (k + 1) u‖ := by
  refine (Fourier.Torus.symbolComplex (deRham d)).norm_le_of_gap
    (Filter.Eventually.of_forall fun q => ?_) u hu
  by_cases hq : q = 0
  · subst hq
    intro v hv
    simp only [Fourier.Torus.symbolComplex_m, Fourier.Torus.freq_zero, deRham_m_zero] at hv ⊢
    simp [eq_zero_of_mem_orthogonal_ker_zero hv]
  · exact gap _ _ (Fourier.Torus.two_pi_le_norm_freq hq)

/-! ### Harmonic forms and cohomology -/

/-- **Harmonic forms on `𝕋ᵈ` are the constant forms**: `u ∈ ℌᵏ` iff all its nonzero Fourier
modes vanish. -/
theorem mem_harmonic_iff {k : ℤ} {u : L2Form d k} :
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

/-- The constant `k`-form `v`: the zero mode `δ₀ v` (`Fourier.Torus.mode`). -/
def const (k : ℤ) (v : Form ℂ d k) : L2Form d k := Fourier.Torus.mode 0 v

omit [LinearOrder d] in
theorem const_apply (k : ℤ) (v : Form ℂ d k) (q : d → ℤ) :
    (const k v : (d → ℤ) → Form ℂ d k) q = if q = 0 then v else 0 := by
  rw [const, Fourier.Torus.coeFn_mode, Pi.single_apply]

theorem const_mem_harmonic (k : ℤ) (v : Form ℂ d k) : const k v ∈ (complex d).harmonic k :=
  mem_harmonic_iff.2 fun q hq => by simp [const_apply, hq]

/-- **`ℌᵏ(𝕋ᵈ) ≅ Λᵏ`**: a harmonic form is its constant coefficient. -/
def harmonicEquiv (k : ℤ) : (complex d).harmonic k ≃ₗ[ℂ] Form ℂ d k where
  toFun u := (u : L2Form d k) 0
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

/-- **The harmonic forms of the torus are finite-dimensional.** -/
instance (k : ℤ) : FiniteDimensional ℂ ((complex d).harmonic k) :=
  (harmonicEquiv k).symm.finiteDimensional

/-- **`dim ℌᵏ(𝕋ᵈ) = (#d choose k)`.** -/
theorem finrank_harmonic (k : ℕ) :
    Module.finrank ℂ ((complex d).harmonic k) = (Fintype.card d).choose k := by
  rw [(harmonicEquiv _).finrank_eq, finrank_form]

/-- **The cohomology of the torus**: `Hᵏ(𝕋ᵈ) ≅ Λᵏ`. -/
def cohomologyEquiv (k : ℤ) : (complex d).cohomology k ≃ₗ[ℂ] Form ℂ d k :=
  ((complex d).cohomologyEquivHarmonic (closedRangeAt k)).trans (harmonicEquiv k)

/-- **The Betti numbers of the torus**: `dim Hᵏ(𝕋ᵈ) = (#d choose k)`. -/
theorem finrank_cohomology (k : ℕ) :
    Module.finrank ℂ ((complex d).cohomology k) = (Fintype.card d).choose k := by
  rw [(cohomologyEquiv _).finrank_eq, finrank_form]

/-! ### The full de Rham window: compactness and eigenbasis -/

variable (d) in
/-- The full window `Λ⁰ → Λ¹ → ⋯ → Λᵈ` of the torus de Rham symbol complex. -/
def windowSymbol : SymbolComplex ℂ (Measure.count : Measure (d → ℤ))
    (ComplexShape.window (Fintype.card d + 1)) fun i : Fin (Fintype.card d + 1) => Form ℂ d i :=
  (Fourier.Torus.symbolComplex (deRham d)).restrict
    (fun i : Fin (Fintype.card d + 1) => ((i : ℕ) : ℤ)) fun _ _ h => by
      change ((_ : ℕ) : ℤ) + 1 = (_ : ℕ) at h
      change (_ : ℕ) + 1 = _
      omega

variable (d) in
/-- **The full `L²` de Rham complex of `𝕋ᵈ`** on the window `Fin (d + 1)`, whose total space
carries the Dirac and Hodge wave operators. -/
abbrev window : HilbertComplex ℂ (ComplexShape.window (Fintype.card d + 1))
    fun i : Fin (Fintype.card d + 1) => L2Form d i :=
  (windowSymbol d).toHilbertComplex

omit [LinearOrder d] in
theorem eq_zero_of_card_lt {k : ℤ} (hk : Fintype.card d < k) (v : Form ℂ d k) : v = 0 := by
  ext ⟨s, hs⟩
  have := Finset.card_le_univ s
  omega

/-- The fibre Cartan identity on the window: `‖d_ξ v‖² + ‖d_ξ* v‖² = |ξ|² ‖v‖²`. -/
theorem window_cartan (i : Fin (Fintype.card d + 1)) (ξ : EuclideanSpace ℝ d) (v : Form ℂ d i) :
    ‖(deRham d).m i ((ComplexShape.window (Fintype.card d + 1)).next i) ξ v‖ ^ 2 +
      ‖ContinuousLinearMap.adjoint
        ((deRham d).m ((ComplexShape.window (Fintype.card d + 1)).prev i) i ξ) v‖ ^ 2 =
      ‖ξ‖ ^ 2 * ‖v‖ ^ 2 := by
  have hcartan : ‖koszul ξ (Exterior.ext (i : ℤ) v)‖ ^ 2 + ‖contr ξ (Exterior.ext (i : ℤ) v)‖ ^ 2 =
      ‖ξ‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_koszul_sq_add_norm_contr_sq, sum_sq_eq_norm_sq, (Exterior.ext _).norm_map]
  -- the outgoing arrow
  have hnext : ‖(deRham d).m i ((ComplexShape.window (Fintype.card d + 1)).next i) ξ v‖ =
      ‖koszul ξ (Exterior.ext (i : ℤ) v)‖ := by
    by_cases h : (i : ℕ) + 1 < Fintype.card d + 1
    · have hn : (ComplexShape.window (Fintype.card d + 1)).next i = ⟨i + 1, h⟩ :=
        ComplexShape.next_eq' _ rfl
      have hij : ((i : ℕ) : ℤ) + 1 = ((ComplexShape.window (Fintype.card d + 1)).next i : ℕ) := by
        rw [hn]; push_cast; rfl
      rw [← (Exterior.ext (𝕜 := ℂ) (d := d) _).norm_map, ext_deRham hij, norm_smul, Complex.norm_I,
        one_mul]
    · have hn : (ComplexShape.window (Fintype.card d + 1)).next i = i :=
        ComplexShape.next_eq_self' _ _ fun k hk => by
          have := k.isLt; simp only [ComplexShape.window_rel] at hk; omega
      have h0 : koszul ξ (Exterior.ext (i : ℤ) v) = 0 := by
        ext s
        exact koszul_ext_eq_zero ξ _ v (by have := Finset.card_le_univ s; omega)
      rw [hn, (deRham d).shape _ _ fun h' => by change ((i : ℕ) : ℤ) + 1 = (i : ℕ) at h'; omega,
        h0]
      simp
  -- the incoming arrow
  have hprev : ‖ContinuousLinearMap.adjoint
      ((deRham d).m ((ComplexShape.window (Fintype.card d + 1)).prev i) i ξ) v‖ =
      ‖contr ξ (Exterior.ext (i : ℤ) v)‖ := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · have hp : (ComplexShape.window (Fintype.card d + 1)).prev i = i :=
        ComplexShape.prev_eq_self' _ _ fun k hk => by
          simp only [ComplexShape.window_rel] at hk; omega
      have hc : contr ξ (Exterior.ext (i : ℤ) v) = 0 := by
        ext s
        exact contr_ext_eq_zero ξ _ v (by omega)
      rw [hp, (deRham d).shape _ _ fun h' => by change ((i : ℕ) : ℤ) + 1 = (i : ℕ) at h'; omega,
        hc]
      simp
    · have hp : (ComplexShape.window (Fintype.card d + 1)).prev i = ⟨i - 1, by omega⟩ :=
        ComplexShape.prev_eq' _ (by simp only [ComplexShape.window_rel]; omega)
      have hij : (((ComplexShape.window (Fintype.card d + 1)).prev i : ℕ) : ℤ) + 1 = (i : ℕ) := by
        rw [hp]; push_cast [Nat.cast_sub hpos]; ring
      rw [← (Exterior.ext (𝕜 := ℂ) (d := d) _).norm_map, ext_adjoint_deRham hij, norm_smul,
        norm_neg, Complex.norm_I, one_mul]
  rw [hnext, hprev, hcartan]

omit [LinearOrder d] in
/-- The frequencies with `|2πk|² ≤ R` are finitely many. -/
theorem finite_norm_freq_sq_le (R : ℝ) :
    {k : d → ℤ | ‖Fourier.Torus.freq k‖ ^ 2 ≤ R}.Finite := by
  refine (Fourier.Torus.finite_bandN (d := d) ⌈R⌉₊).subset fun k hk j => ?_
  have hk' : ‖Fourier.Torus.freq k‖ ^ 2 ≤ R := hk
  have h1 : ((k j : ℝ)) ^ 2 ≤ ‖Fourier.Torus.freq k‖ ^ 2 := by
    rw [Fourier.Torus.norm_freq_sq]
    have hs : ((k j : ℝ)) ^ 2 ≤ ∑ l, ((k l : ℝ)) ^ 2 :=
      Finset.single_le_sum (f := fun l => ((k l : ℝ)) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2pi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
    nlinarith [sq_nonneg ((k j : ℝ))]
  have h2 : (|k j| : ℝ) ≤ ((k j : ℝ)) ^ 2 := by
    have : (|k j| : ℤ) ≤ k j ^ 2 := by
      rcases eq_or_ne (k j) 0 with h | h
      · simp [h]
      · have : 1 ≤ |k j| := Int.one_le_abs h
        nlinarith [abs_mul_abs_self (k j), sq_abs (k j)]
    exact_mod_cast this
  have h3 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  have : (|k j| : ℝ) ≤ (⌈R⌉₊ : ℝ) := by linarith
  exact_mod_cast this

/-- **The compactness property of the de Rham complex of `𝕋ᵈ`** at every degree (Rellich on the
torus): `‖d_ξ v‖² + ‖d_ξ* v‖² = |ξ|² ‖v‖²` with `|2πk| → ∞`. -/
theorem window_coercive (i : Fin (Fintype.card d + 1)) (k : d → ℤ) (v : Form ℂ d i) :
    ‖Fourier.Torus.freq k‖ ^ 2 * ‖v‖ ^ 2 ≤
      ‖(windowSymbol d).m i ((ComplexShape.window (Fintype.card d + 1)).next i) k v‖ ^ 2 +
        ‖ContinuousLinearMap.adjoint
          ((windowSymbol d).m ((ComplexShape.window (Fintype.card d + 1)).prev i) i k) v‖ ^ 2 :=
  (window_cartan i (Fourier.Torus.freq k) v).ge

theorem window_hasCompactProperty : (window d).HasCompactProperty := fun i =>
  hasCompactPropertyAt_of_coercive (windowSymbol d) i (fun k => ‖Fourier.Torus.freq k‖ ^ 2)
    (window_coercive i) finite_norm_freq_sq_le

/-- The real structure of the total space of the window (a shortcut instance). -/
instance instNormedSpaceRealTotal :
    NormedSpace ℝ (PiLp 2 fun i : Fin (Fintype.card d + 1) => L2Form d i) := inferInstance

instance instIsScalarTowerRealTotal :
    IsScalarTower ℝ ℂ (PiLp 2 fun i : Fin (Fintype.card d + 1) => L2Form d i) := inferInstance

/-- **The Hodge wave group of the de Rham complex of `𝕋ᵈ` has a dense set of eigenvectors**
(discrete spectrum, from the compact resolvent of the wave operator). -/
theorem window_eigenDense : (window d).isSkewAdjoint_wave.group.EigenDense :=
  window_hasCompactProperty.eigenDense_wave

/-! ### Real forms -/

/-- **The real structure** of the torus de Rham window: real forms have
`ω̂(-k) = conj ω̂(k)`. -/
def windowReal : (windowSymbol d).RealStructure Reflection.count_neg where
  cj _ := entryConj
  antilinear _ a v := entryConj_smul a v
  invol _ v := entryConj_entryConj v
  inner_cj _ v w := inner_entryConj v w
  symm i j k v := by
    change (deRham d).m i j (Fourier.Torus.freq (-k)) (entryConj v) = _
    rw [Fourier.Torus.freq_neg]
    exact deRham_neg_entryConj _ _ _ v

/-! ### The weak exterior derivative -/

section Weak

open scoped Finset

/-- The normalised Haar measure on `ℝ/ℤ`, as in `Feec.Fourier.TorusWeak`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

open TorusWeak Finset in
/-- **The weak exterior derivative on `𝕋ᵈ`, coefficientwise**: `w = d u` weakly (the operator
`-i Σ_c d_{e_c} ∂_c = Σ_c dx_c ∧ ∂_c`) iff for every `(k + 1)`-subset `s` and every smooth `φ`,
`∫ w_s φ = -Σ_{j ∈ s} ε(j, s) ∫ u_{s ∖ j} ∂_j φ`: the coefficients of
`d u = Σ_s Σ_{j ∈ s} ε(j, s) ∂_j u_{s ∖ j} dx_s` in the sense of distributions. -/
theorem isWeak_deRham_iff {k : ℤ} (u : Field d {s : Finset d // (#s : ℤ) = k})
    (w : Field d {s : Finset d // (#s : ℤ) = k + 1}) :
    IsWeak ((deRham d).m k (k + 1)) u w ↔
      ∀ (s : {s : Finset d // (#s : ℤ) = k + 1}) (φ : UnitAddTorus d → ℂ), IsSmooth φ →
        ∫ x, w s x * φ x = -∑ j ∈ s.1, ExteriorFibre.sgn j s.1 *
          if h : (#(s.1.erase j) : ℤ) = k then ∫ x, u ⟨s.1.erase j, h⟩ x * partialT j φ x
          else 0 := by
  -- the coefficients `-i (d_{e_c})_{s, p} = ε(c, s) [c ∈ s] [p = s ∖ c]` of the operator
  have key : ∀ (s : {s : Finset d // (#s : ℤ) = k + 1})
      (X : d → {s : Finset d // (#s : ℤ) = k} → ℂ),
      ∑ c, ∑ p, -Complex.I * (deRham d).m k (k + 1) (EuclideanSpace.single c 1)
          (EuclideanSpace.single p 1) s * X c p =
        ∑ j ∈ s.1, ExteriorFibre.sgn j s.1 *
          if h : (#(s.1.erase j) : ℤ) = k then X j ⟨s.1.erase j, h⟩ else 0 := fun s X => by
    have h1 : ∀ c, ∑ p, -Complex.I * (deRham d).m k (k + 1) (EuclideanSpace.single c 1)
        (EuclideanSpace.single p 1) s * X c p =
          -Complex.I * (deRham d).m k (k + 1) (EuclideanSpace.single c 1) (WithLp.toLp 2 (X c)) s :=
      fun c => by
        rw [apply_eq_sum _ (WithLp.toLp 2 (X c)) s, Finset.mul_sum]
        exact sum_congr rfl fun p _ => by ring
    have hI : ∀ z : ℂ, -Complex.I * (Complex.I * z) = z := fun z => by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    simp_rw [h1, deRham_m_succ_apply, hI]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_eq_single j (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
    simp only [PiLp.single_apply, ite_true, Complex.ofReal_one, mul_one]
    split_ifs with h
    · rw [ext_apply _ _ h]
    · rw [ext_apply_of_ne _ _ h]
  refine forall_congr' fun s => forall_congr' fun φ => forall_congr' fun hφ => ?_
  rw [integral_sum_fo _ _ hφ, key s fun c p => ∫ x, u p x * partialT c φ x]
  exact eq_comm.trans neg_eq_iff_eq_neg

/-- **The differential of the `L²` de Rham complex of `𝕋ᵈ` is the weak exterior derivative**:
through the Fourier coefficients of `L²` forms (Parseval, `Fourier.Torus.fieldFourier`), the graph
of `d` is the weak graph of the exterior derivative, tested against all smooth functions on `𝕋ᵈ`
(`isWeak_deRham_iff`). -/
theorem mem_graph_iff_isWeak {k : ℤ} (u : TorusWeak.Field d {s : Finset d // (#s : ℤ) = k})
    (w : TorusWeak.Field d {s : Finset d // (#s : ℤ) = k + 1}) :
    (Fourier.Torus.fieldFourier d _ u, Fourier.Torus.fieldFourier d _ w) ∈
        ((complex d).d k (k + 1)).graph ↔
      TorusWeak.IsWeak ((deRham d).m k (k + 1)) u w := by
  rw [← TorusWeak.mem_graph_iff_isWeak (deRham_m_succ_eq_sum k)]
  exact ⟨fun h => ⟨mem_domain_of_mem_graph h, ((image_iff (mem_domain_of_mem_graph h)).2 h).symm⟩,
    fun ⟨h, e⟩ => e ▸ ((complex d).d k (k + 1)).mem_graph ⟨_, h⟩⟩

end Weak

end Feec.Models.Torus.DeRham
