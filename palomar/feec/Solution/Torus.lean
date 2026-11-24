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
multiplier `torusD` (`Feec.Fourier.Exterior.deRham_m_succ_apply`), the weak exterior derivative
through the inverse Fourier transform `torusInv` (`Feec.Models.Torus.DeRham.mem_graph_iff_isWeak`,
`Feec.Models.Torus.DeRham.isWeak_deRham_iff`), closed ranges and the
Poincaré inequality (`Feec.Models.Torus.DeRham.closedRangeAt`,
`Feec.Models.Torus.DeRham.norm_le_of_mem_orthogonal`), the harmonic forms
(`Feec.Models.Torus.DeRham.finrank_harmonic`), the band-limited forms and the truncations
(`Feec.Models.Torus.DeRham.mem_band_iff`, `Feec.Models.Torus.DeRham.coeFn_starProjection_band`,
`Feec.Models.Torus.DeRham.isGraphBounded_bandProj`), approximation
(`Feec.Models.Torus.DeRham.tendsto_starProjection_band`), the truncations fixing the harmonic
forms (`Feec.Models.Torus.DeRham.bandProj_harmonic`) and the Jackson estimate on the `Hˢ` classes
(`jackson`, from the spectral approximation estimate
`Feec.Fourier.Torus.norm_sub_starProjection_band_le`).

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
open Feec.Fourier.Torus (symbolComplex)
open Feec.Fourier.Exterior (deRham)

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

/-! ### The weak exterior derivative -/

/-- **The challenge's inverse Fourier transform is the inverse of `Feec`'s coefficient isometry**
`Feec.Fourier.Torus.fieldFourier`: the Fourier series of an `L²` function sums to it in `L²`
(`UnitAddTorus.hasSum_mFourier_series_L2`). -/
theorem torusInv_eq {k : ℤ} (u : TorusForm n k) (s : {s : Finset (Fin n) // (s.card : ℤ) = k}) :
    torusInv u s = (Feec.Fourier.Torus.fieldFourier (Fin n) _).symm u s := by
  have hc : ∀ ξ, UnitAddTorus.mFourierCoeff
      ((Feec.Fourier.Torus.fieldFourier (Fin n) _).symm u s) ξ = u ξ s := fun ξ => by
    rw [← Feec.Fourier.Torus.fieldFourier_apply, LinearIsometryEquiv.apply_symm_apply]
  have h := UnitAddTorus.hasSum_mFourier_series_L2
    ((Feec.Fourier.Torus.fieldFourier (Fin n) _).symm u s)
  simp_rw [hc] at h
  exact h.tsum_eq

/-- **The Fourier coefficients of `torusInv u` are `u`.** -/
theorem mFourierCoeff_torusInv (k : ℤ) (u : TorusForm n k)
    (s : {s : Finset (Fin n) // (s.card : ℤ) = k}) (ξ : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (torusInv u s) ξ = u ξ s := by
  rw [torusInv_eq]
  exact (Feec.Fourier.Torus.fieldFourier_apply _ ξ s).symm.trans
    (by rw [LinearIsometryEquiv.apply_symm_apply])

/-- **Every `L²` form is `torusInv` of its Fourier coefficients** (`torusInv_eq`: `torusInv` is
the inverse of the isometry `Feec.Fourier.Torus.fieldFourier`). -/
theorem torusInv_surjective (k : ℤ) : Function.Surjective fun u : TorusForm n k => torusInv u :=
  fun f => ⟨Feec.Fourier.Torus.fieldFourier (Fin n) _ (WithLp.toLp 2 f), funext fun s => by
    dsimp only; rw [torusInv_eq, LinearIsometryEquiv.symm_apply_apply]⟩

/-- **The graph of `d` is the weak exterior derivative of `L²(𝕋ⁿ; Λᵏ)`**, through `torusInv`:
`Feec.Models.Torus.DeRham.mem_graph_iff_isWeak` at the forms with coefficients `u`, `w`, read
coefficientwise by `Feec.Models.Torus.DeRham.isWeak_deRham_iff`. -/
theorem mem_graph_iff_isWeakTorusD (k : ℤ) (u : TorusForm n k) (w : TorusForm n (k + 1)) :
    (u, w) ∈ ((complexC n).d k (k + 1)).graph ↔ IsWeakTorusD (torusInv u) (torusInv w) := by
  have h := Feec.Models.Torus.DeRham.mem_graph_iff_isWeak
    ((Feec.Fourier.Torus.fieldFourier (Fin n) _).symm u)
    ((Feec.Fourier.Torus.fieldFourier (Fin n) _).symm w)
  simp only [LinearIsometryEquiv.apply_symm_apply] at h
  refine h.trans ((Feec.Models.Torus.DeRham.isWeak_deRham_iff _ _).trans ?_)
  unfold IsWeakTorusD
  simp only [torusInv_eq, Feec.Fourier.TorusWeak.partialT_eq_deriv]
  exact Iff.rfl

theorem mem_V_iff (N : ℕ) (k : ℤ) (u : TorusForm n k) :
    u ∈ ((family n).V N).V k ↔ ∀ ξ, (∃ j, (N : ℤ) < |ξ j|) → u ξ = 0 := by
  change u ∈ band (d := Fin n) N k ↔ _
  rw [Feec.Models.Torus.DeRham.mem_band_iff]
  simp only [Feec.Fourier.Torus.mem_bandN, not_forall, not_le]

theorem π_apply (N : ℕ) (k : ℤ) (x : ((complexC n).d k (k + 1)).domain) (ξ : Fin n → ℤ) :
    (((family n).π N).π k x : TorusForm n k) ξ =
      if ∀ j, |ξ j| ≤ N then (x : TorusForm n k) ξ else 0 := by
  change ((band (d := Fin n) N k).starProjection (x : TorusForm n k) : TorusForm n k) ξ = _
  rw [Feec.Models.Torus.DeRham.coeFn_starProjection_band]
  by_cases h : ∀ j, |ξ j| ≤ (N : ℤ)
  · rw [ite_eq_left (Feec.Fourier.Torus.mem_bandN.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt Feec.Fourier.Torus.mem_bandN.1 h), ite_eq_right h]

/-! ### Harmonic forms and the band subcomplexes -/

/-- **The harmonic forms are finite-dimensional** (the constant forms). -/
instance (k : ℤ) : FiniteDimensional ℂ ((complexC n).harmonic k) := by
  rw [← (complexC n).harmonic_eq k]
  exact inferInstanceAs (FiniteDimensional ℂ ((complex (Fin n)).harmonic k))

/-- **`dim ℌᵏ = (n choose k)`** (the constant forms). -/
theorem finrank_harmonic (k : ℕ) : Module.finrank ℂ ((complexC n).harmonic k) = n.choose k := by
  rw [← (complexC n).harmonic_eq k]
  have h := Feec.Models.Torus.DeRham.finrank_harmonic (d := Fin n) k
  rwa [Fintype.card_fin] at h

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
  have hmem : (Feec.Fourier.Torus.mode q v : TorusForm n k) ∈ ((family n).V N).V k := by
    rw [htop]; exact Submodule.mem_top
  have h := (mem_V_iff N k _).1 hmem q
    ⟨0, show (N : ℤ) < |(N : ℤ) + 1| by rw [abs_of_nonneg (by positivity)]; omega⟩
  rw [Feec.Fourier.Torus.coeFn_mode, Pi.single_eq_same] at h
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

/-- **The truncation commutes with `d`**: `d (x - π_N x) = d x - π_N (d x)`. -/
theorem d_sub_starProjection_band (N : ℕ) {k : ℤ} (x : ((complexC n).d k (k + 1)).domain)
    (hv : (x : TorusForm n k) - (band (d := Fin n) N k).starProjection x ∈
      ((complexC n).d k (k + 1)).domain) :
    (complexC n).d k (k + 1) ⟨_, hv⟩ = (complexC n).d k (k + 1) x -
      (band (d := Fin n) N (k + 1)).starProjection ((complexC n).d k (k + 1) x) := by
  have hP : (band (d := Fin n) N k).starProjection (x : TorusForm n k) ∈
      ((complexC n).d k (k + 1)).domain :=
    (bandSubcomplex (Fin n) N).le_domain k (k + 1) (Submodule.starProjection_apply_mem _ _)
  have hc : (complexC n).d k (k + 1) ⟨_, hP⟩ =
      (band (d := Fin n) N (k + 1)).starProjection ((complexC n).d k (k + 1) x) :=
    ((Feec.Models.Torus.DeRham.reducingSubcomplex_band (d := Fin n) N).reduces k (k + 1)).comm x
  rw [← hc, ← LinearPMap.map_sub]
  rfl

/-- **The family approximates in the graph norm**: `π_N x → x` and `d π_N x = π_N d x → d x`. -/
theorem approximates (k : ℤ) : (family n).Approximates k := by
  refine (complexC n).approximates_of_eventually (family n) k fun x ε hε => ?_
  have h1 := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1
    (Feec.Models.Torus.DeRham.tendsto_starProjection_band k (x : TorusForm n k)))).2 ε hε
  have h2 := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1
    (Feec.Models.Torus.DeRham.tendsto_starProjection_band (k + 1)
      ((complexC n).d k (k + 1) x)))).2 ε hε
  filter_upwards [h1, h2] with N hN1 hN2
  refine ⟨_, Submodule.starProjection_apply_mem (band (d := Fin n) N k) (x : TorusForm n k),
    by rwa [norm_sub_rev], ?_⟩
  rw [d_sub_starProjection_band, norm_sub_rev]
  exact hN2

/-- **The family approximates on every window**: in the graph norm in every degree, and in `L²`
in the last one. -/
theorem approximatesOn (a : ℤ) (m : ℕ) : (family n).ApproximatesOn a m :=
  ⟨fun _ _ => approximates _, fun i _ x =>
    (complexC n).tendsto_infDist (family n) (approximates (a + (i : ℕ))) x⟩

/-- **The truncations fix the harmonic forms** (the constant forms,
`Feec.Models.Torus.DeRham.bandProj_harmonic`): `‖q - π_N q‖ = 0`. -/
theorem harmonicError_eq_zero (N : ℕ) {k : ℤ} (q : (complexC n).harmonic k) :
    ((family n).π N).harmonicError q = 0 := by
  have hq : (q : TorusForm n k) ∈ (complex (Fin n)).harmonic k :=
    (SetLike.ext_iff.1 ((complexC n).harmonic_eq k) _).2 q.2
  change ‖(q : TorusForm n k) - (bandProj (Fin n) N).π k q‖ = 0
  rw [Feec.Models.Torus.DeRham.bandProj_harmonic N hq, sub_self, norm_zero]

/-! ### The Jackson estimate -/

/-- **`IsTorusSobolev` in the terms of `Feec`**: the weights are `(1 + |2πξ|²)^s` with
`Feec.Fourier.Torus.freq ξ = 2πξ`, and for `L ≥ 0` the bound is `‖u‖_{Hˢ} ≤ L`. -/
theorem isTorusSobolev_iff {s L : ℝ} (hL : 0 ≤ L) {k : ℤ} {u : TorusForm n k} :
    IsTorusSobolev s L u ↔
      Summable (fun ξ => (1 + ‖Feec.Fourier.Torus.freq ξ‖ ^ 2) ^ s * ‖u ξ‖ ^ 2) ∧
        √(∑' ξ, (1 + ‖Feec.Fourier.Torus.freq ξ‖ ^ 2) ^ s * ‖u ξ‖ ^ 2) ≤ L := by
  simp_rw [Feec.Fourier.Torus.norm_freq_sq]
  rw [IsTorusSobolev, Real.sqrt_le_left hL]

variable (n) in
/-- **The `Hˢ` Jackson estimate of the spectral family**: mesh size `(2π (N + 1))⁻¹`, order `s`,
constant `1`, the class of the `k`-forms `x` with `‖x‖_{Hˢ} ≤ L` and, if `x ∈ D(d)`,
`‖d x‖_{Hˢ} ≤ L`, approximated by their truncations
(`Feec.Fourier.Torus.norm_sub_starProjection_band_le`, for `d` with
`d_sub_starProjection_band`). -/
def jackson : (family n).Jackson NNReal where
  meshSize N := (2 * Real.pi * (N + 1))⁻¹
  meshSize_nonneg N := inv_nonneg.2 (by positivity)
  tendsto_meshSize := tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop Real.two_pi_pos
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
  Reg s k L x := IsTorusSobolev s L x ∧ ∀ hx : x ∈ ((complexC n).d k (k + 1)).domain,
    IsTorusSobolev s L ((complexC n).d k (k + 1) ⟨x, hx⟩)
  ord s := s
  B _ _ := 1
  jackson := fun s N k {L} x hL hx => by
    have hh : 0 ≤ (2 * Real.pi * (N + 1))⁻¹ ^ (s : ℝ) := by positivity
    have hfin : ∀ {T : ℝ}, √T ≤ L → (2 * Real.pi * (N + 1))⁻¹ ^ (s : ℝ) * √T ≤
        1 * (L * (2 * Real.pi * (N + 1))⁻¹ ^ (s : ℝ)) := fun hT => by
      rw [one_mul, mul_comm L]
      exact mul_le_mul_of_nonneg_left hT hh
    refine ⟨(band (d := Fin n) N k).starProjection x,
      Submodule.starProjection_apply_mem (band (d := Fin n) N k) x, ?_, fun j hxj => ?_⟩
    · obtain ⟨h1, h2⟩ := (isTorusSobolev_iff hL).1 hx.1
      exact (Feec.Fourier.Torus.norm_sub_starProjection_band_le (symbolComplex (deRham (Fin n)))
        s.coe_nonneg N h1).trans (hfin h2)
    · by_cases hkj : k + 1 = j
      · subst hkj
        obtain ⟨h1, h2⟩ := (isTorusSobolev_iff hL).1 (hx.2 hxj)
        rw [d_sub_starProjection_band N ⟨x, hxj⟩]
        exact (Feec.Fourier.Torus.norm_sub_starProjection_band_le
          (symbolComplex (deRham (Fin n))) s.coe_nonneg N h1).trans (hfin h2)
      · rw [LinearPMap.apply_eq_zero_of_eq_zero ((complexC n).shape k j hkj), norm_zero]
        exact mul_nonneg zero_le_one (mul_nonneg hL hh)

end FEEC.Torus
