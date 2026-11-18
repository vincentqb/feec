module

public import Solution.OfFeec
public import Solution.Bridge
public import Feec.Fourier.SpectralGalerkin
public import Feec.Fourier.ExteriorSymbol
public import Feec.Fourier.Torus
public import Feec.ForMathlib.Lp.CountEquiv

/-!
# The spectral Galerkin family of the torus

The de Rham complex of the torus `𝕋ⁿ` in Fourier coefficients, graded by `ℤ` as the challenge's
`FEEC.TorusForm`: the fibres `Λᵏ = ℂ^{k-subsets of Fin n}` (`Torus.Fib`), the symbol
`d_ξ = i κ_ξ` (`Torus.δ`, the Koszul differential `Feec.Fourier.Exterior.koszul` of the full
exterior algebra restricted to degree `k` through `Torus.extZ` and `Torus.resZ`), the family of
fibre complexes `Torus.fibre` on `ComplexShape.up ℤ` and its Hilbert complex `Torus.complex`
(`Feec.Fourier.Torus.complex`). The fibre gap `‖d_ξ v‖ = |ξ| ‖v‖` on `N(d_ξ)ᗮ`
(`Torus.norm_δ_of_mem_orthogonal`) gives closed ranges and the Poincaré inequality with constant
`(2π)⁻¹`. The band-limited forms are a reducing subcomplex with the Fourier truncation as cochain
projection (`Torus.bandSubcomplex`, `Torus.bandProj`), as in `Feec.Models.Torus.DeRhamGalerkin`
for the complex graded by `ℕ`; the challenge's family is `Torus.family`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006], §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap MeasureTheory Finset

@[expose] public noncomputable section

namespace FEEC.Torus

variable {n : ℕ}

/-! ### The graded fibres -/

variable (n) in
/-- The fibre `Λᵏ = ℂ^{k-subsets of Fin n}` of the `k`-forms at one frequency, graded by `ℤ`. -/
abbrev Fib (k : ℤ) : Type := EuclideanSpace ℂ {s : Finset (Fin n) // (s.card : ℤ) = k}

theorem sum_dite_card {M : Type*} [AddCommMonoid M] (k : ℤ)
    (g : {s : Finset (Fin n) // (s.card : ℤ) = k} → M) :
    ∑ s : Finset (Fin n), (if h : (s.card : ℤ) = k then g ⟨s, h⟩ else 0) = ∑ t, g t := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun s : Finset (Fin n) => (s.card : ℤ) = k)]
  have h1 : ∀ t : {s : Finset (Fin n) // (s.card : ℤ) = k},
      (if h : ((t : Finset (Fin n)).card : ℤ) = k then g ⟨t, h⟩ else 0) = g t := fun t => by
    simp [t.2]
  have h2 : ∀ t : {s : Finset (Fin n) // ¬ (s.card : ℤ) = k},
      (if h : ((t : Finset (Fin n)).card : ℤ) = k then g ⟨t, h⟩ else 0) = 0 := fun t => by
    simp [t.2]
  simp only [h1, h2, sum_const_zero, add_zero]

/-- Extension by zero `Λᵏ → Λ` into the full exterior algebra. -/
def extZ (k : ℤ) : Fib n k →ₗᵢ[ℂ] Feec.Fourier.Exterior.Lam ℂ (Fin n) where
  toFun ω := WithLp.toLp 2 fun s => if h : (s.card : ℤ) = k then ω ⟨s, h⟩ else 0
  map_add' ω η := by
    ext s; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' a ω := by
    ext s; simp only [PiLp.smul_apply, RingHom.id_apply]; split_ifs <;> simp
  norm_map' ω := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← sum_dite_card k fun t => ‖ω t‖ ^ 2]
    refine sum_congr rfl fun s _ => ?_
    split_ifs <;> simp

/-- Restriction `Λ → Λᵏ` to the coefficients of degree `k`. -/
def resZ (k : ℤ) : Feec.Fourier.Exterior.Lam ℂ (Fin n) →L[ℂ] Fib n k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => WithLp.toLp 2 fun t => ω t.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem extZ_apply (k : ℤ) (ω : Fib n k) {s : Finset (Fin n)} (h : (s.card : ℤ) = k) :
    extZ k ω s = ω ⟨s, h⟩ := by
  simp [extZ, h]

theorem extZ_apply_of_ne (k : ℤ) (ω : Fib n k) {s : Finset (Fin n)} (h : (s.card : ℤ) ≠ k) :
    extZ k ω s = 0 := by
  simp [extZ, h]

@[simp] theorem resZ_apply (k : ℤ) (ω : Feec.Fourier.Exterior.Lam ℂ (Fin n))
    (t : {s : Finset (Fin n) // (s.card : ℤ) = k}) : resZ k ω t = ω t.1 := rfl

theorem extZ_resZ {k : ℤ} {ω : Feec.Fourier.Exterior.Lam ℂ (Fin n)}
    (h : ∀ s : Finset (Fin n), (s.card : ℤ) ≠ k → ω s = 0) : extZ k (resZ k ω) = ω := by
  ext s
  by_cases hs : (s.card : ℤ) = k
  · rw [extZ_apply k _ hs, resZ_apply]
  · rw [extZ_apply_of_ne k _ hs, h s hs]

theorem koszul_extZ_eq_zero (ξ : EuclideanSpace ℝ (Fin n)) (k : ℤ) (ω : Fib n k)
    {s : Finset (Fin n)} (hs : (s.card : ℤ) ≠ k + 1) :
    Feec.Fourier.Exterior.koszul ξ (extZ k ω) s = 0 := by
  rw [Feec.Fourier.Exterior.koszul_apply]
  refine sum_eq_zero fun j hj => ?_
  rw [extZ_apply_of_ne k ω, mul_zero]
  rw [card_erase_of_mem hj]
  have : 1 ≤ s.card := card_pos.2 ⟨j, hj⟩
  omega

theorem contr_extZ_eq_zero (ξ : EuclideanSpace ℝ (Fin n)) (k : ℤ) (ω : Fib n k)
    {s : Finset (Fin n)} (hs : (s.card : ℤ) + 1 ≠ k) :
    Feec.Fourier.Exterior.contr ξ (extZ k ω) s = 0 := by
  rw [Feec.Fourier.Exterior.contr_apply]
  refine sum_eq_zero fun j hj => ?_
  rw [extZ_apply_of_ne k ω, mul_zero]
  rw [card_insert_of_notMem (mem_compl.1 hj)]
  push_cast
  exact hs

/-- The Koszul differential of a `(k - 1)`-form is a `k`-form. -/
theorem koszul_contr_extZ_eq_zero (ξ : EuclideanSpace ℝ (Fin n)) (k : ℤ) (ω : Fib n k)
    {s : Finset (Fin n)} (hs : (s.card : ℤ) ≠ k) :
    Feec.Fourier.Exterior.koszul ξ (Feec.Fourier.Exterior.contr ξ (extZ k ω)) s = 0 := by
  rw [Feec.Fourier.Exterior.koszul_apply]
  refine sum_eq_zero fun j hj => ?_
  rw [contr_extZ_eq_zero ξ k ω, mul_zero]
  rw [card_erase_of_mem hj]
  have : 1 ≤ s.card := card_pos.2 ⟨j, hj⟩
  omega

/-! ### The de Rham symbol -/

/-- The symbol `d_ξ = i κ_ξ : Λᵏ → Λᵏ⁺¹` of the exterior derivative at the frequency `ξ`. -/
def δ (k : ℤ) (ξ : EuclideanSpace ℝ (Fin n)) : Fib n k →L[ℂ] Fib n (k + 1) :=
  Complex.I • (resZ (k + 1) ∘L Feec.Fourier.Exterior.koszul ξ ∘L (extZ k).toContinuousLinearMap)

theorem δ_apply (k : ℤ) (ξ : EuclideanSpace ℝ (Fin n)) (ω : Fib n k) :
    δ k ξ ω = Complex.I • resZ (k + 1) (Feec.Fourier.Exterior.koszul ξ (extZ k ω)) := rfl

theorem extZ_resZ_koszul (k : ℤ) (ξ : EuclideanSpace ℝ (Fin n)) (ω : Fib n k) :
    extZ (k + 1) (resZ (k + 1) (Feec.Fourier.Exterior.koszul ξ (extZ k ω))) =
      Feec.Fourier.Exterior.koszul ξ (extZ k ω) :=
  extZ_resZ fun _ hs => koszul_extZ_eq_zero ξ k ω hs

theorem extZ_δ (k : ℤ) (ξ : EuclideanSpace ℝ (Fin n)) (ω : Fib n k) :
    extZ (k + 1) (δ k ξ ω) = Complex.I • Feec.Fourier.Exterior.koszul ξ (extZ k ω) := by
  rw [δ_apply, LinearIsometry.map_smul, extZ_resZ_koszul]

/-- **`d_ξ d_ξ = 0`.** -/
theorem δ_comp (k : ℤ) (ξ : EuclideanSpace ℝ (Fin n)) :
    (δ (k + 1) ξ).comp (δ k ξ) = 0 := by
  refine ContinuousLinearMap.ext fun ω => ?_
  rw [ContinuousLinearMap.comp_apply, δ_apply (k + 1), extZ_δ, _root_.map_smul,
    Feec.Fourier.Exterior.koszul_koszul, smul_zero, _root_.map_zero, smul_zero]
  rfl

/-- The symbol depends continuously on the frequency. -/
theorem continuous_δ (k : ℤ) : Continuous (δ (n := n) k) := by
  have h : Continuous fun ξ : EuclideanSpace ℝ (Fin n) =>
      resZ (k + 1) ∘L Feec.Fourier.Exterior.koszul ξ ∘L (extZ k).toContinuousLinearMap := by
    refine continuous_clm_apply.2 fun ω => ?_
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun t => ?_)
    change Continuous fun ξ : EuclideanSpace ℝ (Fin n) =>
      ∑ j ∈ t.1, Feec.ExteriorFibre.sgn j t.1 * ((ξ j : ℝ) : ℂ) * extZ k ω (t.1.erase j)
    refine continuous_finsetSum _ fun j _ => ?_
    refine (continuous_const.mul ?_).mul continuous_const
    exact RCLike.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)
  exact h.const_smul Complex.I

/-- The symbol at the frequency `2π ξ` of `ξ ∈ ℤⁿ`, coefficientwise: the challenge's `torusD`. -/
theorem δ_freq_apply (k : ℤ) (ξ : Fin n → ℤ) (v : Fib n k)
    (s : {s : Finset (Fin n) // (s.card : ℤ) = k + 1}) :
    δ k (Feec.Fourier.Torus.freq ξ) v s =
      2 * Real.pi * Complex.I * ∑ j ∈ s.1, (-1) ^ (s.1.filter fun l => l < j).card * (ξ j : ℂ) *
        if h : ((s.1.erase j).card : ℤ) = k then v ⟨s.1.erase j, h⟩ else 0 := by
  rw [δ_apply, PiLp.smul_apply, resZ_apply, Feec.Fourier.Exterior.koszul_apply, smul_eq_mul,
    mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  change Complex.I * ((-1) ^ (s.1.filter fun l => l < j).card *
      ((2 * Real.pi * (ξ j : ℝ) : ℝ) : ℂ) * (if h : ((s.1.erase j).card : ℤ) = k then
        v ⟨s.1.erase j, h⟩ else 0)) = _
  push_cast
  ring

variable (n) in
/-- The family of fibre complexes `⋯ → Λᵏ → Λᵏ⁺¹ → ⋯` of the de Rham symbol on
`ComplexShape.up ℤ`. -/
def fibre : Feec.Fourier.FibreComplex ℂ (EuclideanSpace ℝ (Fin n)) (ComplexShape.up ℤ) (Fib n) :=
  Feec.Fourier.FibreComplex.ofSucc δ δ_comp continuous_δ

theorem fibre_m_succ (k : ℤ) : (fibre n).m k (k + 1) = δ k :=
  Feec.Fourier.FibreComplex.ofSucc_m_succ _ _ _ k

theorem δ_zero (k : ℤ) : δ (n := n) k 0 = 0 := by
  refine ContinuousLinearMap.ext fun ω => ?_
  ext t
  simp [δ_apply, Feec.Fourier.Exterior.koszul_apply]

theorem fibre_m_zero (i j : ℤ) : (fibre n).m i j 0 = 0 := by
  by_cases h : i + 1 = j
  · subst h; rw [fibre_m_succ, δ_zero]
  · rw [(fibre n).shape i j h]; rfl

/-- **The fibre gap**: `‖d_ξ v‖ = |ξ| ‖v‖` for `v ⊥ N(d_ξ)`. -/
theorem norm_δ_of_mem_orthogonal {k : ℤ} {ξ : EuclideanSpace ℝ (Fin n)} {v : Fib n k}
    (hv : v ∈ (LinearMap.ker (δ k ξ : Fib n k →ₗ[ℂ] Fib n (k + 1)))ᗮ) :
    ‖δ k ξ v‖ = ‖ξ‖ * ‖v‖ := by
  set w := Feec.Fourier.Exterior.contr ξ (extZ k v)
  set r := resZ k (Feec.Fourier.Exterior.koszul ξ w)
  have hr : extZ k r = Feec.Fourier.Exterior.koszul ξ w :=
    extZ_resZ fun _ hs => koszul_contr_extZ_eq_zero ξ k v hs
  have hrk : r ∈ LinearMap.ker (δ k ξ : Fib n k →ₗ[ℂ] Fib n (k + 1)) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, δ_apply, hr,
      Feec.Fourier.Exterior.koszul_koszul, _root_.map_zero, smul_zero]
  have hw : w = 0 := by
    refine (inner_self_eq_zero (𝕜 := ℂ)).1 ?_
    calc ⟪w, w⟫_ℂ = ⟪Feec.Fourier.Exterior.koszul ξ w, extZ k v⟫_ℂ :=
          (Feec.Fourier.Exterior.inner_koszul (𝕜 := ℂ) ξ w (extZ k v)).symm
      _ = ⟪r, v⟫_ℂ := by rw [← hr, LinearIsometry.inner_map_map]
      _ = 0 := Submodule.inner_right_of_mem_orthogonal hrk hv
  have h := Feec.Fourier.Exterior.norm_koszul_sq_add_norm_contr_sq (𝕜 := ℂ) ξ (extZ k v)
  rw [show Feec.Fourier.Exterior.contr ξ (extZ k v) = 0 from hw, norm_zero,
    zero_pow two_ne_zero, add_zero, Feec.Fourier.Exterior.sum_sq_eq_norm_sq,
    LinearIsometry.norm_map, ← mul_pow] at h
  have e : ‖δ k ξ v‖ = ‖Feec.Fourier.Exterior.koszul ξ (extZ k v)‖ := by
    rw [← LinearIsometry.norm_map (extZ (k + 1)), extZ_δ, norm_smul, Complex.norm_I, one_mul]
  rw [e]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- **The uniform fibre gap of the torus**: `‖v‖ ≤ (2π)⁻¹ ‖m v‖` on `N(m)ᗮ` for `|ξ| ≥ 2π`. -/
theorem gap (i j : ℤ) {ξ : EuclideanSpace ℝ (Fin n)} (hξ : 2 * Real.pi ≤ ‖ξ‖) :
    ∀ v ∈ (LinearMap.ker ((fibre n).m i j ξ : Fib n i →ₗ[ℂ] Fib n j))ᗮ,
      ‖v‖ ≤ (2 * Real.pi)⁻¹ * ‖(fibre n).m i j ξ v‖ := by
  intro v hv
  by_cases h : i + 1 = j
  · subst h
    rw [fibre_m_succ] at hv ⊢
    rw [norm_δ_of_mem_orthogonal hv, ← mul_assoc]
    have h2pi : 0 < 2 * Real.pi := by positivity
    have : 1 ≤ (2 * Real.pi)⁻¹ * ‖ξ‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ h2pi, one_mul]; exact hξ
    nlinarith [norm_nonneg v]
  · have h0 : (fibre n).m i j ξ = 0 := by rw [(fibre n).shape i j h]; rfl
    rw [h0] at hv ⊢
    simp [Feec.Fourier.eq_zero_of_mem_orthogonal_ker_zero hv]

/-! ### The complex and its band subcomplexes -/

variable (n) in
/-- **The `L²` de Rham complex of `𝕋ⁿ`** in Fourier coefficients, graded by `ℤ`. -/
abbrev complex : Feec.HilbertComplex ℂ (ComplexShape.up ℤ) (TorusForm n) :=
  Feec.Fourier.Torus.complex (fibre n)

theorem complex_d (i j : ℤ) : (complex n).d i j =
    Feec.Operator.mulOp (Measure.count : Measure (Fin n → ℤ))
      fun ξ => (fibre n).m i j (Feec.Fourier.Torus.freq ξ) := rfl

/-- The band-limited `k`-forms `|ξ|_∞ ≤ N`. -/
abbrev band (N : ℕ) (k : ℤ) : Submodule ℂ (TorusForm n k) :=
  (Feec.Fourier.Torus.symbolComplex (fibre n)).band (Feec.Fourier.Torus.bandN N) k

instance (N : ℕ) (k : ℤ) : (band (n := n) N k).HasOrthogonalProjection :=
  Feec.Fourier.hasOrthogonalProjection_band (Feec.Fourier.Torus.symbolComplex (fibre n))
    (Feec.Fourier.Torus.finite_bandN N).measurableSet k

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℂ (band (n := n) N k) :=
  Feec.Fourier.finiteDimensional_band (Feec.Fourier.Torus.symbolComplex (fibre n))
    (Feec.Fourier.Torus.finite_bandN N) k

theorem reducingSubcomplex_band (N : ℕ) : (complex n).ReducingSubcomplex (band (n := n) N) :=
  Feec.Fourier.reducingSubcomplex_band (Feec.Fourier.Torus.symbolComplex (fibre n))
    (Feec.Fourier.Torus.finite_bandN N).measurableSet

/-- **The band subcomplex** `{u | u ξ = 0 for |ξ|_∞ > N}`. -/
def bandSubcomplex (N : ℕ) : (complex n).Subcomplex where
  V := band N
  le_domain k j :=
    ((reducingSubcomplex_band (n := n) N).reduces k j).le_domain ((complex n).dense k j)
  mapsTo _ _ x hx := (reducingSubcomplex_band (n := n) N).mapsTo ⟨x, _⟩ hx

/-- The truncation commutes with `d`. -/
theorem band_comm (N : ℕ) (k j : ℤ) (x : ((complex n).d k j).domain) :
    (complex n).d k j ⟨(band N k).starProjection (x : TorusForm n k),
        ((reducingSubcomplex_band (n := n) N).reduces k j).proj_mem x⟩ =
      (band N j).starProjection ((complex n).d k j x) :=
  ((reducingSubcomplex_band (n := n) N).reduces k j).comm x

/-- **The Fourier truncation** as a cochain projection onto the band subcomplex. -/
def bandProj (N : ℕ) : (bandSubcomplex (n := n) N).CochainProjection where
  π k := (band N k).starProjection.toLinearMap
  mem k x := Submodule.starProjection_apply_mem (band N k) x
  proj k _ hx := (Submodule.starProjection_eq_self_iff (K := band N k)).2 hx
  comm k j x := band_comm N k j x

theorem mem_band_iff {N : ℕ} {k : ℤ} {u : TorusForm n k} :
    u ∈ band N k ↔ ∀ ξ, (∃ j, (N : ℤ) < |ξ j|) → u ξ = 0 := by
  rw [Feec.Fourier.mem_band_iff, Measure.ae_count_iff]
  refine forall_congr' fun ξ => ?_
  simp only [Feec.Fourier.Torus.mem_bandN, not_forall, not_le]

/-- The Fourier truncation is the restriction of the coefficients to `|ξ|_∞ ≤ N`. -/
theorem starProjection_band_apply (N : ℕ) (k : ℤ) (x : TorusForm n k) (ξ : Fin n → ℤ) :
    ((band N k).starProjection x : TorusForm n k) ξ =
      if ∀ j, |ξ j| ≤ N then x ξ else 0 := by
  have hP := Feec.Operator.coeFn_starProjection_fibreSub
    (μ := (Measure.count : Measure (Fin n → ℤ)))
    (Feec.Fourier.bandFibre (𝕜 := ℂ) (E := Fib n) (Feec.Fourier.Torus.bandN N) k)
    (Feec.Fourier.aestronglyMeasurable_starProjection_bandFibre
      (Feec.Fourier.Torus.finite_bandN N).measurableSet k) x
  have h1 : ((band N k).starProjection x : TorusForm n k) ξ =
      (Feec.Fourier.bandFibre (𝕜 := ℂ) (E := Fib n) (Feec.Fourier.Torus.bandN N) k ξ).starProjection
        (x ξ) := Measure.ae_count_iff.1 hP ξ
  rw [h1, Feec.Fourier.starProjection_bandFibre]
  by_cases h : ∀ j, |ξ j| ≤ (N : ℤ)
  · rw [Feec.Operator.cutoff_apply_of_mem (show ξ ∈ Feec.Fourier.Torus.bandN N from h),
      ite_eq_left h]
  · rw [Feec.Operator.cutoff_apply_of_notMem (show ξ ∉ Feec.Fourier.Torus.bandN N from h),
      ite_eq_right h]

/-! ### The challenge's complex and family -/

variable (n) in
/-- The complex as a Hilbert complex of the challenge. -/
abbrev complexC : HilbertComplex ℂ (TorusForm n) := HilbertComplex.ofFeec (complex n)

variable (n) in
/-- **The spectral Galerkin family**: the band subcomplexes with the Fourier truncations. -/
def family : (complexC n).SubcomplexFamily ℕ where
  l := atTop
  V N := HilbertComplex.Subcomplex.ofFeec (bandSubcomplex N)
  finiteDimensional N k := inferInstanceAs (FiniteDimensional ℂ (band (n := n) N k))
  π N := HilbertComplex.CochainProjection.ofFeec (bandProj N)

theorem family_π_apply (N : ℕ) (k : ℤ) (x : ((complexC n).d k (k + 1)).domain) :
    (((family n).π N).π k x : TorusForm n k) = (band N k).starProjection (x : TorusForm n k) :=
  rfl

/-- **The graph of `d` is that of the multiplier `torusD`.** -/
theorem mem_graph_iff (k : ℤ) (u : TorusForm n k) (w : TorusForm n (k + 1)) :
    (u, w) ∈ ((complexC n).d k (k + 1)).graph ↔
      ∀ ξ (s : {s : Finset (Fin n) // (s.card : ℤ) = k + 1}), w ξ s = torusD u ξ s.1 := by
  have key : ∀ ξ (s : {s : Finset (Fin n) // (s.card : ℤ) = k + 1}),
      (fibre n).m k (k + 1) (Feec.Fourier.Torus.freq ξ) (u ξ) s = torusD u ξ s.1 := fun ξ s => by
    rw [fibre_m_succ, δ_freq_apply]; rfl
  constructor
  · rintro hg ξ s
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hg
    have h : (fibre n).m k (k + 1) (Feec.Fourier.Torus.freq ξ) ((y : TorusForm n k) ξ) = w ξ :=
      Measure.ae_count_iff.1 ((Feec.Operator.mulOp_apply_eq_iff
        (μ := (Measure.count : Measure (Fin n → ℤ)))
        (m := fun ξ => (fibre n).m k (k + 1) (Feec.Fourier.Torus.freq ξ)) y w).1 hy2) ξ
    dsimp only at hy1
    subst hy1
    rw [← h, key]
  · intro h
    have hw : ∀ ξ, w ξ = (fibre n).m k (k + 1) (Feec.Fourier.Torus.freq ξ) (u ξ) := fun ξ =>
      PiLp.ext fun s => (h ξ s).trans (key ξ s).symm
    have hu : u ∈ ((complexC n).d k (k + 1)).domain := by
      change MemLp _ 2 _
      exact (Lp.memLp w).ae_eq (ae_of_all _ hw)
    refine (LinearPMap.mem_graph_iff _).2 ⟨⟨u, hu⟩, rfl, ?_⟩
    exact (Feec.Operator.mulOp_apply_eq_iff (μ := (Measure.count : Measure (Fin n → ℤ)))
      (m := fun ξ => (fibre n).m k (k + 1) (Feec.Fourier.Torus.freq ξ)) ⟨u, hu⟩ w).2
      (ae_of_all _ fun ξ => (hw ξ).symm)

theorem mem_V_iff (N : ℕ) (k : ℤ) (u : TorusForm n k) :
    u ∈ ((family n).V N).V k ↔ ∀ ξ, (∃ j, (N : ℤ) < |ξ j|) → u ξ = 0 :=
  mem_band_iff

theorem π_apply (N : ℕ) (k : ℤ) (x : ((complexC n).d k (k + 1)).domain) (ξ : Fin n → ℤ) :
    (((family n).π N).π k x : TorusForm n k) ξ =
      if ∀ j, |ξ j| ≤ N then (x : TorusForm n k) ξ else 0 :=
  starProjection_band_apply N k _ ξ

/-- The constant `k`-form `v` (supported on the zero mode), and more generally the mode `ξ₀`. -/
def single (k : ℤ) (ξ₀ : Fin n → ℤ) (v : Fib n k) : TorusForm n k :=
  lp.equivLpCount ℂ (Fin n → ℤ) (Fib n k) 2 (lp.single 2 ξ₀ v)

theorem single_apply (k : ℤ) (ξ₀ : Fin n → ℤ) (v : Fib n k) (ξ : Fin n → ℤ) :
    (single k ξ₀ v : (Fin n → ℤ) → Fib n k) ξ = if ξ = ξ₀ then v else 0 := by
  rw [single, lp.coeFn_equivLpCount, lp.single_apply]
  split_ifs with h
  · subst h; simp
  · simp [Pi.single, Function.update, h]

/-- In degrees `0 ≤ k ≤ n` the fibre has a nonzero vector. -/
theorem exists_ne_zero {k : ℤ} (hk0 : 0 ≤ k) (hkn : k ≤ n) : ∃ v : Fib n k, v ≠ 0 := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (show k.toNat ≤ (Finset.univ : Finset (Fin n)).card by
      rw [Finset.card_univ, Fintype.card_fin]; omega)
  have htk : (t.card : ℤ) = k := by rw [ht]; exact Int.toNat_of_nonneg hk0
  refine ⟨EuclideanSpace.single ⟨t, htk⟩ 1, fun h0 => ?_⟩
  have := congrArg (fun v : Fib n k => v ⟨t, htk⟩) h0
  simp at this

/-- **Nonzero harmonic forms**: the constant forms. -/
theorem exists_harmonic_ne_zero {k : ℤ} (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    ∃ q ∈ (complexC n).harmonic k, q ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne_zero (n := n) hk0 hkn
  refine ⟨single k 0 v, ?_, fun h0 => hv ?_⟩
  · rw [← (complexC n).harmonic_eq k]
    change single k 0 v ∈ (Feec.Fourier.Torus.symbolComplex (fibre n)).toHilbertComplex.harmonic k
    rw [Feec.Fourier.SymbolComplex.harmonic_toHilbertComplex, Feec.Operator.mem_fibreSub,
      Measure.ae_count_iff]
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp only [Feec.Fourier.Torus.symbolComplex_m, Feec.Fourier.Torus.freq_zero, fibre_m_zero,
        _root_.map_zero]
      simp
    · rw [single_apply, ite_eq_right hξ]
      exact Submodule.zero_mem _
  · have := congrArg (fun q : TorusForm n k => (q : (Fin n → ℤ) → Fib n k) 0) h0
    rw [single_apply, ite_eq_left rfl,
      Measure.ae_count_iff.1 (Lp.coeFn_zero (Fib n k) 2 _) 0] at this
    exact this

/-- **No band subcomplex is the whole space** in degrees `0 ≤ k ≤ n` (`n ≥ 1`). -/
theorem V_ne_top [NeZero n] {k : ℤ} (hk0 : 0 ≤ k) (hkn : k ≤ n) (N : ℕ) :
    ((family n).V N).V k ≠ ⊤ := by
  obtain ⟨v, hv⟩ := exists_ne_zero (n := n) hk0 hkn
  intro htop
  have hmem : single k (fun _ => (N : ℤ) + 1) v ∈ ((family n).V N).V k := by
    rw [htop]; exact Submodule.mem_top
  have h := (mem_V_iff N k _).1 hmem (fun _ => (N : ℤ) + 1)
    ⟨0, show (N : ℤ) < |(N : ℤ) + 1| by rw [abs_of_nonneg (by positivity)]; omega⟩
  rw [single_apply, ite_eq_left rfl] at h
  exact hv h

/-! ### The hypotheses of the three theorems -/

/-- **Closed ranges**, from the fibre gap. -/
theorem isClosed_boundaries (k : ℤ) :
    IsClosed ((complexC n).boundaries k : Set (TorusForm n k)) :=
  ((complexC n).closedRangeAt_iff k).1
    (Feec.Fourier.Torus.closedRangeAt_of_gap (fibre_m_zero _ _) fun _ hξ => gap _ _ hξ)

/-- **The Poincaré inequality** `‖v‖ ≤ (2π)⁻¹ ‖d v‖` on `D(d) ∩ N(d)ᗮ`. -/
theorem norm_le_of_mem_orthogonal {k : ℤ} (u : ((complexC n).d k (k + 1)).domain)
    (hu : (u : TorusForm n k) ∈ ((complexC n).cycles k)ᗮ) :
    ‖(u : TorusForm n k)‖ ≤ (2 * Real.pi)⁻¹ * ‖(complexC n).d k (k + 1) u‖ := by
  refine (Feec.Fourier.Torus.symbolComplex (fibre n)).norm_le_of_gap
    (Filter.Eventually.of_forall fun q => ?_) u hu
  by_cases hq : q = 0
  · subst hq
    intro v hv
    simp only [Feec.Fourier.Torus.symbolComplex_m, Feec.Fourier.Torus.freq_zero,
      fibre_m_zero] at hv ⊢
    simp [Feec.Fourier.eq_zero_of_mem_orthogonal_ker_zero hv]
  · exact gap _ _ (Feec.Fourier.Torus.two_pi_le_norm_freq hq)

/-- **The Poincaré inequality in the graph norm**, constant `√(1 + (2π)⁻²)`. -/
theorem poincareBy (k : ℤ) : (complexC n).PoincareBy k (√(1 + (2 * Real.pi)⁻¹ ^ 2)) := by
  intro u hu
  have h := norm_le_of_mem_orthogonal u hu
  set a := ‖(u : TorusForm n k)‖
  set b := ‖(complexC n).d k (k + 1) u‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  change √(a ^ 2 + b ^ 2) ≤ √(1 + (2 * Real.pi)⁻¹ ^ 2) * b
  have e : √(1 + (2 * Real.pi)⁻¹ ^ 2) * b = √((1 + (2 * Real.pi)⁻¹ ^ 2) * b ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb]
  rw [e]
  refine Real.sqrt_le_sqrt ?_
  have : a ^ 2 ≤ ((2 * Real.pi)⁻¹ * b) ^ 2 := pow_le_pow_left₀ ha h 2
  nlinarith

/-- **The truncations are bounded by `1` in the graph norm.** -/
theorem isGraphBoundedBy (k : ℤ) : (family n).IsGraphBoundedBy k 1 := by
  intro N x
  refine (complexC n).graphNorm_le_of_sq zero_le_one ?_
  have hc : (complexC n).d k (k + 1) ⟨((family n).π N).π k x,
      ((family n).V N).le_domain k (k + 1) (((family n).π N).π k x).2⟩ =
      (band N (k + 1)).starProjection ((complexC n).d k (k + 1) x) :=
    band_comm N k (k + 1) x
  rw [hc, one_pow, one_mul]
  have h1 := Submodule.norm_starProjection_apply_le (band (n := n) N k) (x : TorusForm n k)
  have h2 := Submodule.norm_starProjection_apply_le (band (n := n) N (k + 1))
    ((complexC n).d k (k + 1) x)
  change ‖(band N k).starProjection (x : TorusForm n k)‖ ^ 2 + _ ≤ _
  gcongr

/-- **The truncations are bounded by `1` in `L²`.** -/
theorem norm_π_le (N : ℕ) (k : ℤ) (x : ((complexC n).d k (k + 1)).domain) :
    ‖(((family n).π N).π k x : TorusForm n k)‖ ≤ ‖(x : TorusForm n k)‖ :=
  Submodule.norm_starProjection_apply_le _ _

theorem tendsto_starProjection_band (k : ℤ) (u : TorusForm n k) :
    Tendsto (fun N => (band (n := n) N k).starProjection u) atTop (𝓝 u) :=
  Feec.Fourier.tendsto_starProjection_band (Feec.Fourier.Torus.symbolComplex (fibre n))
    (fun N => (Feec.Fourier.Torus.finite_bandN N).measurableSet) Feec.Fourier.Torus.bandN_mono
    Feec.Fourier.Torus.exists_mem_bandN k u

/-- **The family approximates in the graph norm.** -/
theorem approximates (k : ℤ) : (family n).Approximates k := by
  refine (complexC n).approximates_of_eventually (family n) k fun x ε hε => ?_
  have h1 := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1
    (tendsto_starProjection_band k (x : TorusForm n k)))).2 ε hε
  have h2 := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1
    (tendsto_starProjection_band (k + 1) ((complexC n).d k (k + 1) x)))).2 ε hε
  filter_upwards [h1, h2] with N hN1 hN2
  refine ⟨(band N k).starProjection (x : TorusForm n k),
    Submodule.starProjection_apply_mem (band N k) _, ?_, ?_⟩
  · rwa [norm_sub_rev]
  · have hv : (band N k).starProjection (x : TorusForm n k) ∈
        ((complexC n).d k (k + 1)).domain :=
      (bandSubcomplex N).le_domain k (k + 1) (Submodule.starProjection_apply_mem (band N k) _)
    have e : ((complexC n).d k (k + 1))
        ⟨(x : TorusForm n k) - (band N k).starProjection (x : TorusForm n k),
          Submodule.sub_mem _ x.2 hv⟩ =
        (complexC n).d k (k + 1) x -
          (band N (k + 1)).starProjection ((complexC n).d k (k + 1) x) := by
      have hc : (complexC n).d k (k + 1) ⟨(band N k).starProjection (x : TorusForm n k), hv⟩ =
          (band N (k + 1)).starProjection ((complexC n).d k (k + 1) x) :=
        band_comm N k (k + 1) x
      rw [← hc, ← LinearPMap.map_sub]
      rfl
    rw [e, norm_sub_rev]
    exact hN2

/-- **The family approximates on every window**: in the graph norm in every degree, and in `L²`
in the last one. -/
theorem approximatesOn (a : ℤ) (m : ℕ) : (family n).ApproximatesOn a m :=
  ⟨fun _ _ => approximates _, fun i _ x =>
    (complexC n).tendsto_infDist (family n) (approximates (a + (i : ℕ))) x⟩

end FEEC.Torus
