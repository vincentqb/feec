module

public import Feec.Fourier.Torus
public import Feec.Fourier.ExteriorSymbol
public import Feec.Fourier.SpectralGalerkin

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
* `window d`: the full complex `Λ⁰ → ⋯ → Λᵈ` on `Fin (d + 1)`; **`window_hasCompactProperty`**
  (Rellich on `𝕋ᵈ`, from the fibre Cartan identity `window_cartan`) and **`window_eigenDense`**:
  the Hodge wave group of the torus de Rham complex has a dense set of eigenvectors (discrete
  spectrum).
* `windowReal`: the real structure of the window (real forms have `ω̂(-k) = conj ω̂(k)`).

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
    simp [eq_zero_of_mem_orthogonal_ker_zero hv]

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
    simp [eq_zero_of_mem_orthogonal_ker_zero hv]
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

/-! ### The full de Rham window: compactness and eigenbasis -/

variable (d) in
/-- The full window `Λ⁰ → Λ¹ → ⋯ → Λᵈ` of the torus de Rham symbol complex. -/
def windowSymbol : SymbolComplex ℂ (Measure.count : Measure (d → ℤ))
    (ComplexShape.window (Fintype.card d + 1)) fun i : Fin (Fintype.card d + 1) => Form ℂ d i :=
  (Fourier.Torus.symbolComplex (deRham d)).restrict (fun i : Fin (Fintype.card d + 1) => (i : ℕ))
    fun _ _ h => h

variable (d) in
/-- **The full `L²` de Rham complex of `𝕋ᵈ`** on the window `Fin (d + 1)`, whose total space
carries the Dirac and Hodge wave operators. -/
abbrev window : HilbertComplex ℂ (ComplexShape.window (Fintype.card d + 1))
    fun i : Fin (Fintype.card d + 1) => Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ)) :=
  (windowSymbol d).toHilbertComplex

omit [LinearOrder d] in
theorem eq_zero_of_card_lt {k : ℕ} (hk : Fintype.card d < k) (v : Form ℂ d k) : v = 0 := by
  ext ⟨s, hs⟩
  have := Finset.card_le_univ s
  omega

/-- The fibre Cartan identity on the window: `‖d_ξ v‖² + ‖d_ξ* v‖² = |ξ|² ‖v‖²`. -/
theorem window_cartan (i : Fin (Fintype.card d + 1)) (ξ : EuclideanSpace ℝ d) (v : Form ℂ d i) :
    ‖(deRham d).m i ((ComplexShape.window (Fintype.card d + 1)).next i) ξ v‖ ^ 2 +
      ‖ContinuousLinearMap.adjoint
        ((deRham d).m ((ComplexShape.window (Fintype.card d + 1)).prev i) i ξ) v‖ ^ 2 =
      ‖ξ‖ ^ 2 * ‖v‖ ^ 2 := by
  have hcartan := norm_koszulDeg_sq_add (𝕜 := ℂ) (i : ℕ) ξ v
  -- the outgoing arrow
  have hnext : ‖(deRham d).m i ((ComplexShape.window (Fintype.card d + 1)).next i) ξ v‖ =
      ‖koszulDeg (𝕜 := ℂ) (i : ℕ) ξ v‖ := by
    by_cases h : (i : ℕ) + 1 < Fintype.card d + 1
    · have hn : (ComplexShape.window (Fintype.card d + 1)).next i = ⟨i + 1, h⟩ :=
        ComplexShape.next_eq' _ rfl
      rw [hn]
      exact norm_deRham_apply (i : ℕ) ξ v
    · have hn : (ComplexShape.window (Fintype.card d + 1)).next i = i :=
        ComplexShape.next_eq_self' _ _ fun k hk => by
          have := k.isLt; simp only [ComplexShape.window_rel] at hk; omega
      rw [hn, (deRham d).shape (i : ℕ) (i : ℕ) fun h' => by
        change (i : ℕ) + 1 = i at h'; omega]
      rw [eq_zero_of_card_lt (by omega) (koszulDeg (i : ℕ) ξ v)]
      simp
  -- the incoming arrow
  have hprev : ‖ContinuousLinearMap.adjoint
      ((deRham d).m ((ComplexShape.window (Fintype.card d + 1)).prev i) i ξ) v‖ =
      ‖contr ξ (ext (i : ℕ) v)‖ := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · have hp : (ComplexShape.window (Fintype.card d + 1)).prev i = i :=
        ComplexShape.prev_eq_self' _ _ fun k hk => by
          simp only [ComplexShape.window_rel] at hk; omega
      rw [hp, (deRham d).shape (i : ℕ) (i : ℕ) fun h' => by
        change (i : ℕ) + 1 = i at h'; omega]
      have : contr ξ (ext (i : ℕ) v) = 0 := by
        ext s; exact contr_ext_eq_zero ξ _ v (by omega)
      rw [this]; simp
    · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      have hp : (ComplexShape.window (Fintype.card d + 1)).prev i = ⟨k, by omega⟩ :=
        ComplexShape.prev_eq' _ (by simp only [ComplexShape.window_rel]; omega)
      rw [hp]
      have key : ∀ (j : ℕ) (hj : j = k + 1) (w : Form ℂ d j),
          ‖ContinuousLinearMap.adjoint ((deRham d).m k j ξ) w‖ = ‖contr ξ (ext j w)‖ := by
        intro j hj w
        subst hj
        rw [adjoint_deRham, _root_.smul_apply, norm_smul, norm_neg, Complex.norm_I, one_mul,
          ← ext_contrDeg, LinearIsometry.norm_map]
      exact key _ hk v
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
instance instNormedSpaceRealTotal : NormedSpace ℝ (PiLp 2 fun i : Fin (Fintype.card d + 1) =>
    Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))) := inferInstance

instance instIsScalarTowerRealTotal : IsScalarTower ℝ ℂ (PiLp 2 fun i : Fin (Fintype.card d + 1) =>
    Lp (Form ℂ d i) 2 (Measure.count : Measure (d → ℤ))) := inferInstance

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

end Feec.Models.Torus.DeRham
