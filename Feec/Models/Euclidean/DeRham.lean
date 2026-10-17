module

public import Feec.Fourier.Euclidean
public import Feec.Fourier.ExteriorSymbol
public import Feec.Fourier.Weak

/-!
# The `L²` de Rham complex of `ℝᵈ`, in every dimension and degree

The de Rham complex `L²Λ⁰(ℝᵈ) → ⋯ → L²Λᵈ(ℝᵈ)` with its maximal domains, on the Fourier side
(Plancherel, `Feec.Fourier.Euclidean.fourier`): `k`-forms are `L²(ℝᵈ; Λᵏ)` and the exterior
derivative is the multiplier `d_ξ = i ξ ∧ ·` at `ξ = 2πx` (`Feec.Fourier.Exterior.deRham`).

In contrast with the torus (`Feec.Models.Torus.DeRham`):

* **no closed range** in degrees `1 ≤ k ≤ d` (`not_closedRangeAt`): the symbol degenerates at low
  frequencies, so there is no Poincaré inequality;
* **no `L²` harmonic forms** in any degree, for `d ≥ 1` (`harmonic_eq_bot`): the fibre harmonic
  spaces vanish off `ξ = 0`, a null set;
* hence the complex is not exact although `ℌᵏ = 0` (`boundaries_ne_cycles`): the cycles are the
  closure of the boundaries;
* **the Fourier domain of `d` is the weak domain** (`mem_domain_d_iff_weak`): `d (𝓕 f) = 𝓕 g` iff
  `⟪f, δ φ⟫ = ⟪g, φ⟫` for every Schwartz `(k+1)`-form `φ`, with the codifferential
  `δ = codiff k` (the formal adjoint of `d`); on Schwartz forms `d` is the classical exterior
  derivative `extDeriv k` (`mulOp_fourier_extDeriv`);
* `window d`, `windowReal`, `window_conj_eq`: the full window `Λ⁰ → ⋯ → Λᵈ`; real forms give
  real solutions of the Hodge wave equation.

## References

* [AFW2010], [Arnold2018] (Hilbert complexes; closed range and Poincaré inequalities)
* [QuennevilleBelair2015], §4.2
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open scoped FourierTransform SchwartzMap
open MeasureTheory LinearPMap Set Feec.Fourier Feec.Fourier.Exterior

namespace Feec.Models.Euclidean.DeRham

variable (d : Type*) [Fintype d] [LinearOrder d]

/-- `L²` `k`-forms on `ℝᵈ`, by their Fourier transforms. -/
abbrev L2Form (k : ℕ) : Type _ := Lp (Form ℂ d k) 2 (volume : Measure (EuclideanSpace ℝ d))

/-- **The `L²` de Rham complex of `ℝᵈ`** (Fourier side). -/
abbrev complex : HilbertComplex ℂ (ComplexShape.up ℕ) (L2Form d) :=
  Fourier.Euclidean.complex (deRham d)

variable {d}

/-- The de Rham symbol `Λᵏ → Λᵏ⁺¹` is not identically zero for `k < #d`. -/
theorem deRham_m_ne_zero {k : ℕ} (hk : k < Fintype.card d) : (deRham d).m k (k + 1) ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset d, s.card = k + 1 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset d)) (n := k + 1)
      (by rw [Finset.card_univ]; omega)
    exact ⟨s, hs⟩
  obtain ⟨j, hj⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  have hsj : (s.erase j).card = k := by rw [Finset.card_erase_of_mem hj, hs]; rfl
  intro h0
  set ω : Form ℂ d k := EuclideanSpace.single ⟨s.erase j, hsj⟩ 1
  set ξ : EuclideanSpace ℝ d := EuclideanSpace.single j 1
  have hval := congrArg (fun T : EuclideanSpace ℝ d → Form ℂ d k →L[ℂ] Form ℂ d (k + 1) =>
    T ξ ω ⟨s, hs⟩) h0
  simp only [Pi.zero_apply, _root_.zero_apply, PiLp.zero_apply] at hval
  rw [deRham_m_succ, _root_.smul_apply, PiLp.smul_apply, koszulDeg_apply, res_apply,
    koszul_apply, Finset.sum_eq_single j] at hval
  · rw [ext_apply k ω hsj] at hval
    simp [ω, ξ, Exterior.sgn] at hval
  · intro l hl hlj
    rw [show (ξ l : ℝ) = 0 by simp [ξ, hlj]]
    simp
  · intro h; exact absurd hj h

/-- **No closed range on `ℝᵈ`** in the degrees `1 ≤ k ≤ #d`. -/
theorem not_closedRangeAt {k : ℕ} (hk : k < Fintype.card d) :
    ¬ (complex d).ClosedRangeAt (k + 1) := by
  have hp : (ComplexShape.up ℕ).prev (k + 1) = k := (ComplexShape.up ℕ).prev_eq' rfl
  have h1 : (deRham d).IsHomogeneous ((ComplexShape.up ℕ).prev (k + 1)) (k + 1) 1 := by
    rw [hp]; exact deRham_isHomogeneous k
  have h2 : (deRham d).m ((ComplexShape.up ℕ).prev (k + 1)) (k + 1) ≠ 0 := by
    rw [hp]; exact deRham_m_ne_zero hk
  exact Fourier.Euclidean.not_closedRangeAt one_pos h1 h2

/-- **There are no `L²` harmonic forms on `ℝᵈ`**, in any degree. -/
theorem harmonic_eq_bot [Nonempty d] (k : ℕ) : (complex d).harmonic k = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  change u ∈ (Fourier.Euclidean.symbolComplex (deRham d)).toHilbertComplex.harmonic k at hu
  rw [SymbolComplex.harmonic_toHilbertComplex, Operator.mem_fibreSub] at hu
  rw [Submodule.mem_bot]
  have : Nontrivial (EuclideanSpace ℝ d) := inferInstance
  have hnull : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ d)), x ≠ 0 :=
    Measure.ae_ne volume 0
  refine Lp.ext ?_
  filter_upwards [hu, hnull, Lp.coeFn_zero (Form ℂ d k) 2 volume] with x h1 h2 h3
  rw [h3]
  have hξ : Fourier.Euclidean.scale x ≠ 0 := by
    simp only [Fourier.Euclidean.scale, ne_eq, smul_eq_zero, not_or]
    exact ⟨by positivity, h2⟩
  simp only [Fourier.Euclidean.symbolComplex_m, deRham_harmonic_fibre hξ k] at h1
  exact h1

/-- On `ℝᵈ` the de Rham complex is not exact in degrees `1 ≤ k ≤ #d`, although it has no
harmonic forms: the boundaries are dense in, but not equal to, the cycles. -/
theorem boundaries_ne_cycles {k : ℕ} (hk : k < Fintype.card d) :
    (complex d).boundaries (k + 1) ≠ (complex d).cycles (k + 1) :=
  (complex d).boundaries_ne_cycles_of_not_closedRangeAt (not_closedRangeAt hk)

/-! ### Weak exterior derivatives -/

/-- The exterior derivative of Schwartz `k`-forms, `d ψ = Σ_j dx_j ∧ ∂_j ψ`. -/
def extDeriv (k : ℕ) :
    𝓢(EuclideanSpace ℝ d, Form ℂ d k) → 𝓢(EuclideanSpace ℝ d, Form ℂ d (k + 1)) :=
  Weak.symbolOp ((deRham d).m k (k + 1))

/-- The codifferential of Schwartz `(k+1)`-forms, the formal adjoint of `d`. -/
def codiff (k : ℕ) :
    𝓢(EuclideanSpace ℝ d, Form ℂ d (k + 1)) → 𝓢(EuclideanSpace ℝ d, Form ℂ d k) :=
  Weak.formalAdjointOp ((deRham d).m k (k + 1))

theorem deRham_isLinear (k : ℕ) : Weak.IsLinear ((deRham d).m k (k + 1)) :=
  deRham_eq_sum k

/-- **The `L²` de Rham complex of `ℝᵈ` is the weak de Rham complex.** For `L²` forms `f, g`
(physical side), `𝓕 f ∈ D(d)` with `d 𝓕 f = 𝓕 g` iff `⟪f, δ φ⟫ = ⟪g, φ⟫` for every Schwartz
`(k+1)`-form `φ`. -/
theorem mem_domain_d_iff_weak (k : ℕ) (f : L2Form d k) (g : L2Form d (k + 1)) :
    (∃ h : 𝓕 f ∈ ((complex d).d k (k + 1)).domain, (complex d).d k (k + 1) ⟨𝓕 f, h⟩ = 𝓕 g) ↔
      ∀ φ : 𝓢(EuclideanSpace ℝ d, Form ℂ d (k + 1)),
        ⟪f, (codiff k φ).toLp 2⟫_ℂ = ⟪g, φ.toLp 2⟫_ℂ :=
  Weak.mem_graph_iff_weak_of_isLinear (deRham_isLinear k) ((deRham d).cont k (k + 1)) f g

/-- On Schwartz forms, the Fourier-model `d` is the classical exterior derivative. -/
theorem mulOp_fourier_extDeriv (k : ℕ) (ψ : 𝓢(EuclideanSpace ℝ d, Form ℂ d k)) :
    ∃ h : 𝓕 (ψ.toLp 2 : L2Form d k) ∈ ((complex d).d k (k + 1)).domain,
      (complex d).d k (k + 1) ⟨_, h⟩ = 𝓕 ((extDeriv k ψ).toLp 2 : L2Form d (k + 1)) :=
  Weak.mulOp_fourier_toLp (deRham_isLinear k) ψ

/-! ### The full window and real forms -/

variable (d) in
/-- The full window `Λ⁰ → ⋯ → Λᵈ` of the whole-space de Rham symbol complex. -/
def windowSymbol : SymbolComplex ℂ (volume : Measure (EuclideanSpace ℝ d))
    (ComplexShape.window (Fintype.card d + 1)) fun i : Fin (Fintype.card d + 1) => Form ℂ d i :=
  (Fourier.Euclidean.symbolComplex (deRham d)).restrict
    (fun i : Fin (Fintype.card d + 1) => (i : ℕ)) fun _ _ h => h

variable (d) in
/-- **The full `L²` de Rham complex of `ℝᵈ`** on the window `Fin (d + 1)`. -/
abbrev window : HilbertComplex ℂ (ComplexShape.window (Fintype.card d + 1))
    fun i : Fin (Fintype.card d + 1) => L2Form d i :=
  (windowSymbol d).toHilbertComplex

/-- **The real structure** of the whole-space de Rham window: real forms have
`𝓕ω(-ξ) = conj 𝓕ω(ξ)` (`Feec.Fourier.Weak.fourier_fixed_iff`). -/
def windowReal : (windowSymbol d).RealStructure (Reflection.neg volume) where
  cj _ := entryConj
  antilinear _ a v := entryConj_smul a v
  invol _ v := entryConj_entryConj v
  inner_cj _ v w := inner_entryConj v w
  symm i j x v := by
    change (deRham d).m i j (Fourier.Euclidean.scale (-x)) (entryConj v) = _
    rw [Fourier.Euclidean.scale_neg]
    exact deRham_neg_entryConj _ _ _ v

/-- **Real data give real solutions** of the Hodge wave equation of the de Rham complex of `ℝᵈ`. -/
theorem window_conj_eq {a b : ℝ} {F U : ℝ → PiLp 2 fun i : Fin (Fintype.card d + 1) =>
      L2Form d i}
    (hU : Evolution.IsStrongSolution (window d).wave (Icc a b) F U)
    (h0 : windowReal.toConj.totalConj (U a) = U a)
    (hF : ∀ t ∈ Icc a b, windowReal.toConj.totalConj (F t) = F t) :
    ∀ t ∈ Icc a b, windowReal.toConj.totalConj (U t) = U t :=
  windowReal.conj_eq hU h0 hF

end Feec.Models.Euclidean.DeRham
