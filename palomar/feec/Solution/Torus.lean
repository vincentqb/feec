module

public import Solution.OfFeec
public import Solution.Bridge
public import Feec.Models.Torus.DeRhamGalerkin

/-!
# The spectral Galerkin family of the torus

The challenge's de Rham complex of the torus `𝕋ⁿ` in Fourier coefficients is `Feec`'s
`Feec.Models.Torus.DeRham.complex (Fin n)`, graded by `ℤ` (`FEEC.TorusForm n` is
`Feec.Models.Torus.DeRham.L2Form (Fin n)`), and the challenge's family `Torus.family` is that of
the band subcomplexes with the Fourier truncations (`Feec.Models.Torus.DeRham.bandSubcomplex`,
`Feec.Models.Torus.DeRham.bandProj`). This file reads the clauses of the witness off `Feec`: the
multiplier `torusD` (`Feec.Fourier.Exterior.deRham_m_succ_apply`), closed ranges and the
Poincaré inequality (`Feec.Models.Torus.DeRham.closedRangeAt`,
`Feec.Models.Torus.DeRham.norm_le_of_mem_orthogonal`), the harmonic forms
(`Feec.Models.Torus.DeRham.finrank_harmonic`), the band-limited forms and the truncations
(`Feec.Models.Torus.DeRham.mem_band_iff`, `Feec.Models.Torus.DeRham.coeFn_starProjection_band`,
`Feec.Models.Torus.DeRham.isGraphBounded_bandProj`) and approximation
(`Feec.Models.Torus.DeRham.tendsto_starProjection_band`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006], §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap MeasureTheory Finset

@[expose] public noncomputable section

namespace FEEC.Torus

open Feec.Models.Torus.DeRham (complex band bandSubcomplex bandProj)

variable {n : ℕ}

variable (n) in
/-- **The `L²` de Rham complex of `𝕋ⁿ`**, as a Hilbert complex of the challenge. -/
abbrev complexC : HilbertComplex ℂ (TorusForm n) := HilbertComplex.ofFeec (complex (Fin n))

variable (n) in
/-- **The spectral Galerkin family**: the band subcomplexes with the Fourier truncations. -/
def family : (complexC n).SubcomplexFamily ℕ where
  l := atTop
  V N := HilbertComplex.Subcomplex.ofFeec (bandSubcomplex (Fin n) N)
  finiteDimensional N k := inferInstanceAs (FiniteDimensional ℂ (band (d := Fin n) N k))
  π N := HilbertComplex.CochainProjection.ofFeec (bandProj (Fin n) N)

/-- The de Rham symbol at the frequency `2π ξ` of `ξ ∈ ℤⁿ`, coefficientwise: the challenge's
`torusD`. -/
theorem deRham_freq_apply (k : ℤ) (ξ : Fin n → ℤ) (v : Feec.Fourier.Exterior.Form ℂ (Fin n) k)
    (s : {s : Finset (Fin n) // (s.card : ℤ) = k + 1}) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq ξ) v s =
      2 * Real.pi * Complex.I * ∑ j ∈ s.1, (-1) ^ (s.1.filter fun l => l < j).card *
        (ξ j : ℂ) * if h : ((s.1.erase j).card : ℤ) = k then v ⟨s.1.erase j, h⟩ else 0 := by
  rw [Feec.Fourier.Exterior.deRham_m_succ_apply, mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  change Complex.I * ((-1) ^ (s.1.filter fun l => l < j).card *
      ((2 * Real.pi * (ξ j : ℝ) : ℝ) : ℂ) * (if h : ((s.1.erase j).card : ℤ) = k then
        v ⟨s.1.erase j, h⟩ else 0)) = _
  push_cast
  ring

/-- **The graph of `d` is that of the multiplier `torusD`.** -/
theorem mem_graph_iff (k : ℤ) (u : TorusForm n k) (w : TorusForm n (k + 1)) :
    (u, w) ∈ ((complexC n).d k (k + 1)).graph ↔
      ∀ ξ (s : {s : Finset (Fin n) // (s.card : ℤ) = k + 1}), w ξ s = torusD u ξ s.1 := by
  have hd : ∀ (y : ((complexC n).d k (k + 1)).domain),
      ((complexC n).d k (k + 1) y : TorusForm n (k + 1)) = w ↔ ∀ ξ,
        (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (Feec.Fourier.Torus.freq ξ)
          ((y : TorusForm n k) ξ) = w ξ := fun y =>
    (Feec.Operator.mulOp_apply_eq_iff (μ := (Measure.count : Measure (Fin n → ℤ)))
      (m := fun ξ => (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1)
        (Feec.Fourier.Torus.freq ξ)) y w).trans Measure.ae_count_iff
  constructor
  · rintro hg ξ s
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hg
    dsimp only at hy1
    subst hy1
    rw [← (hd y).1 hy2 ξ, deRham_freq_apply]
    rfl
  · intro h
    have hw : ∀ ξ, w ξ = (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1)
        (Feec.Fourier.Torus.freq ξ) (u ξ) := fun ξ =>
      PiLp.ext fun s => (h ξ s).trans (deRham_freq_apply k ξ (u ξ) s).symm
    have hu : u ∈ ((complexC n).d k (k + 1)).domain := by
      change MemLp _ 2 _
      exact (Lp.memLp w).ae_eq (ae_of_all _ hw)
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨u, hu⟩, rfl, (hd ⟨u, hu⟩).2 fun ξ => (hw ξ).symm⟩

theorem mem_V_iff (N : ℕ) (k : ℤ) (u : TorusForm n k) :
    u ∈ ((family n).V N).V k ↔ ∀ ξ, (∃ j, (N : ℤ) < |ξ j|) → u ξ = 0 := by
  change u ∈ band N k ↔ _
  rw [Feec.Models.Torus.DeRham.mem_band_iff]
  simp only [Feec.Fourier.Torus.mem_bandN, not_forall, not_le]

theorem π_apply (N : ℕ) (k : ℤ) (x : ((complexC n).d k (k + 1)).domain) (ξ : Fin n → ℤ) :
    (((family n).π N).π k x : TorusForm n k) ξ =
      if ∀ j, |ξ j| ≤ N then (x : TorusForm n k) ξ else 0 := by
  change ((band N k).starProjection (x : TorusForm n k) : TorusForm n k) ξ = _
  rw [Feec.Models.Torus.DeRham.coeFn_starProjection_band]
  by_cases h : ∀ j, |ξ j| ≤ (N : ℤ)
  · rw [if_pos (Feec.Fourier.Torus.mem_bandN.2 h), if_pos h]
  · rw [if_neg (mt Feec.Fourier.Torus.mem_bandN.1 h), if_neg h]

/-! ### Harmonic forms and the band subcomplexes -/

/-- **The harmonic forms are finite-dimensional** (the constant forms). -/
instance (k : ℤ) : FiniteDimensional ℂ ((complexC n).harmonic k) := by
  rw [← (complexC n).harmonic_eq k]
  exact inferInstanceAs (FiniteDimensional ℂ ((complex (Fin n)).harmonic k))

/-- **`dim ℌᵏ = (n choose k)`** (the constant forms). -/
theorem finrank_harmonic (k : ℕ) : Module.finrank ℂ ((complexC n).harmonic k) = n.choose k := by
  rw [← (complexC n).harmonic_eq k]
  exact (Feec.Models.Torus.DeRham.finrank_harmonic (d := Fin n) k).trans (by rw [Fintype.card_fin])

/-- **No band subcomplex is the whole space** in degrees `0 ≤ k ≤ n` (`n ≥ 1`): the mode
`e^{2πi (N + 1)·x} dx_t`, `#t = k`, lies outside. -/
theorem V_ne_top [NeZero n] {k : ℤ} (hk0 : 0 ≤ k) (hkn : k ≤ n) (N : ℕ) :
    ((family n).V N).V k ≠ ⊤ := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (show k.toNat ≤ (Finset.univ : Finset (Fin n)).card by
      rw [Finset.card_univ, Fintype.card_fin]; omega)
  have htk : (t.card : ℤ) = k := by rw [ht]; exact Int.toNat_of_nonneg hk0
  set v : Feec.Fourier.Exterior.Form ℂ (Fin n) k := EuclideanSpace.single ⟨t, htk⟩ 1
  set q : Fin n → ℤ := fun _ => (N : ℤ) + 1
  intro htop
  have hmem : Feec.Models.Torus.DeRham.mode k q v ∈ ((family n).V N).V k := by
    rw [htop]; exact Submodule.mem_top
  have h := (mem_V_iff N k _).1 hmem q
    ⟨0, show (N : ℤ) < |(N : ℤ) + 1| by rw [abs_of_nonneg (by positivity)]; omega⟩
  rw [Feec.Models.Torus.DeRham.mode_apply, if_pos rfl] at h
  have := congrArg (fun w : Feec.Fourier.Exterior.Form ℂ (Fin n) k => w ⟨t, htk⟩) h
  simp [v] at this

/-! ### The hypotheses of the three theorems -/

/-- **Closed ranges**, from the fibre gap. -/
theorem isClosed_boundaries (k : ℤ) :
    IsClosed ((complexC n).boundaries k : Set (TorusForm n k)) :=
  ((complexC n).closedRangeAt_iff k).1 (Feec.Models.Torus.DeRham.closedRangeAt k)

/-- **The Poincaré inequality in the graph norm**, constant `√(1 + (2π)⁻²)`, from
`‖v‖ ≤ (2π)⁻¹ ‖d v‖` on `D(d) ∩ N(d)ᗮ`. -/
theorem poincareBy (k : ℤ) : (complexC n).PoincareBy k (√(1 + (2 * Real.pi)⁻¹ ^ 2)) := by
  intro u hu
  have h := Feec.Models.Torus.DeRham.norm_le_of_mem_orthogonal u hu
  set a := ‖(u : TorusForm n k)‖
  set b := ‖(complexC n).d k (k + 1) u‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  change √(a ^ 2 + b ^ 2) ≤ √(1 + (2 * Real.pi)⁻¹ ^ 2) * b
  rw [show √(1 + (2 * Real.pi)⁻¹ ^ 2) * b = √((1 + (2 * Real.pi)⁻¹ ^ 2) * b ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb]]
  refine Real.sqrt_le_sqrt ?_
  have : a ^ 2 ≤ ((2 * Real.pi)⁻¹ * b) ^ 2 := pow_le_pow_left₀ ha h 2
  nlinarith

/-- **The truncations are bounded by `1` in the graph norm.** -/
theorem isGraphBoundedBy (k : ℤ) : (family n).IsGraphBoundedBy k 1 := fun N x =>
  (complexC n).graphNorm_le_of_sq zero_le_one
    (Feec.Models.Torus.DeRham.isGraphBounded_bandProj N k (k + 1) x)

/-- **The truncations are bounded by `1` in `L²`.** -/
theorem norm_π_le (N : ℕ) (k : ℤ) (x : ((complexC n).d k (k + 1)).domain) :
    ‖(((family n).π N).π k x : TorusForm n k)‖ ≤ ‖(x : TorusForm n k)‖ :=
  Submodule.norm_starProjection_apply_le _ _

/-- **The family approximates in the graph norm**: `π_N x → x` and `d π_N x = π_N d x → d x`. -/
theorem approximates (k : ℤ) : (family n).Approximates k := by
  refine (complexC n).approximates_of_eventually (family n) k fun x ε hε => ?_
  have h1 := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1
    (Feec.Models.Torus.DeRham.tendsto_starProjection_band k (x : TorusForm n k)))).2 ε hε
  have h2 := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1
    (Feec.Models.Torus.DeRham.tendsto_starProjection_band (k + 1)
      ((complexC n).d k (k + 1) x)))).2 ε hε
  filter_upwards [h1, h2] with N hN1 hN2
  refine ⟨(band N k).starProjection (x : TorusForm n k),
    Submodule.starProjection_apply_mem (band N k) _, by rwa [norm_sub_rev], ?_⟩
  have hv : (band N k).starProjection (x : TorusForm n k) ∈ ((complexC n).d k (k + 1)).domain :=
    (bandSubcomplex (Fin n) N).le_domain k (k + 1) (Submodule.starProjection_apply_mem _ _)
  have hc : (complexC n).d k (k + 1) ⟨(band N k).starProjection (x : TorusForm n k), hv⟩ =
      (band N (k + 1)).starProjection ((complexC n).d k (k + 1) x) :=
    ((Feec.Models.Torus.DeRham.reducingSubcomplex_band (d := Fin n) N).reduces k (k + 1)).comm x
  have e : (complexC n).d k (k + 1) ⟨(x : TorusForm n k) -
      (band N k).starProjection (x : TorusForm n k), Submodule.sub_mem _ x.2 hv⟩ =
      (complexC n).d k (k + 1) x - (band N (k + 1)).starProjection ((complexC n).d k (k + 1) x) := by
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
