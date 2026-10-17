module

public import Feec.Fourier.SymbolComplex

/-!
# Closed range of symbol complexes

A multiplication operator `mulOp μ m` has closed range as soon as its fibres have a *uniform
spectral gap*: `‖v‖ ≤ C ‖m a v‖` on `N(m a)ᗮ` for a.e. `a` (`isClosed_range_mulOp_of_gap`). On
the torus the gap comes from `|2πk| ≥ 2π` for `k ≠ 0`; it fails on `ℝⁿ`, where the symbols
degenerate at low frequency, and then the range is not closed (`not_isClosed_range_mulOp`).

## Main results

* `Operator.isClosed_range_mulOp_of_gap`: a uniform fibre gap gives closed range (the fibrewise
  Poincaré inequality, assembled through the measurable kernel projections
  `Feec.Fourier.aestronglyMeasurable_starProjection_ker`).
* `Operator.not_isClosed_range_mulOp`: if for every `ε > 0` the symbol has norm `≤ ε` on a set
  of positive finite measure where it does not vanish on a fixed vector, the range is not
  closed.
* `gap_of_homotopy`: a fibre homotopy `m₀ h₁ + h₂ m₁ = 1` with `‖h₂‖ ≤ C` gives the gap of `m₁`
  with constant `C` (an algebraic Poincaré inequality).
* `SymbolComplex.closedRangeAt_of_gap`, `SymbolComplex.not_closedRangeAt`: the same statements
  for the boundaries of a symbol complex; `SymbolComplex.dual_closedRangeAt_of_gap` for the dual.

## References

* [QuennevilleBelair2015], §4.2 (closed range and the Poincaré inequality, Thm 4.2)
* [AFW2010], §3.1; [BruningLesch1992]
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal
open MeasureTheory LinearPMap Set Filter

namespace Feec

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### A bounded-preimage criterion -/

namespace Operator

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {m : α → E →L[𝕜] F}

/-- The fibrewise component orthogonal to the kernel, `u ↦ (a ↦ u a - P_{N(m a)} (u a))`. -/
def kerOrthProj (hm : AEStronglyMeasurable m μ) : Lp E 2 μ →L[𝕜] Lp E 2 μ :=
  ContinuousLinearMap.id 𝕜 _ - fibreProj (fun a => LinearMap.ker (m a : E →ₗ[𝕜] F))
    (Fourier.aestronglyMeasurable_starProjection_ker hm)

theorem coeFn_kerOrthProj (hm : AEStronglyMeasurable m μ) (u : Lp E 2 μ) :
    kerOrthProj hm u =ᵐ[μ] fun a =>
      u a - (LinearMap.ker (m a : E →ₗ[𝕜] F)).starProjection (u a) := by
  have e : kerOrthProj hm u = u - fibreProj (fun a => LinearMap.ker (m a : E →ₗ[𝕜] F))
      (Fourier.aestronglyMeasurable_starProjection_ker hm) u := rfl
  rw [e]
  filter_upwards [Lp.coeFn_sub u (fibreProj _ (Fourier.aestronglyMeasurable_starProjection_ker hm)
    u), coeFn_fibreProj _ (Fourier.aestronglyMeasurable_starProjection_ker hm) u] with a h1 h2
  rw [h1, Pi.sub_apply, h2]

omit [FiniteDimensional 𝕜 E] [CompleteSpace F] in
theorem apply_sub_starProjection_ker (T : E →L[𝕜] F) (v : E) :
    T (v - (LinearMap.ker (T : E →ₗ[𝕜] F)).starProjection v) = T v := by
  have h := LinearMap.mem_ker.1 ((LinearMap.ker (T : E →ₗ[𝕜] F)).starProjection_apply_mem v)
  rw [ContinuousLinearMap.coe_coe] at h
  rw [_root_.map_sub, h, sub_zero]

/-- **A uniform fibre gap gives closed range.** If `‖v‖ ≤ C ‖m a v‖` for `v ⊥ N(m a)`, for a.e.
`a`, then `R(mulOp μ m)` is closed, with Poincaré constant `C`. -/
theorem norm_le_of_gap (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hgap : ∀ᵐ a ∂μ, ∀ v ∈ (LinearMap.ker (m a : E →ₗ[𝕜] F))ᗮ, ‖v‖ ≤ C * ‖m a v‖)
    (x : (mulOp μ m).domain) (hx : (x : Lp E 2 μ) ∈ (mulOp μ m).kerᗮ) :
    ‖(x : Lp E 2 μ)‖ ≤ C * ‖mulOp μ m x‖ := by
  set u : Lp E 2 μ := (x : Lp E 2 μ) with hu_def
  set v := kerOrthProj hm u
  have hk : u - v ∈ (mulOp μ m).ker := by
    rw [mem_ker_mulOp]
    filter_upwards [Lp.coeFn_sub u v, coeFn_kerOrthProj hm u] with a h1 h2
    rw [h1, Pi.sub_apply, h2, sub_sub_cancel]
    exact LinearMap.mem_ker.1 ((LinearMap.ker (m a : E →ₗ[𝕜] F)).starProjection_apply_mem _)
  have hinner : ⟪u, u - v⟫_𝕜 = 0 := (Submodule.mem_orthogonal' _ _).1 hx _ hk
  have hv : ‖v‖ ≤ C * ‖mulOp μ m x‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_kerOrthProj hm u, coeFn_mulOp μ m x, hgap] with a h1 h2 h3
    rw [h1, h2]
    have := h3 _ ((LinearMap.ker (m a : E →ₗ[𝕜] F)).sub_starProjection_mem_orthogonal (u a))
    rwa [apply_sub_starProjection_ker] at this
  have huv : ‖u‖ ^ 2 ≤ ‖u‖ * ‖v‖ := by
    have h1 : ⟪u, u⟫_𝕜 = ⟪u, v⟫_𝕜 := by
      rw [inner_sub_right, sub_eq_zero] at hinner; exact hinner
    have h2 : ‖u‖ ^ 2 = RCLike.re ⟪u, v⟫_𝕜 := by
      rw [← h1, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    rw [h2]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg u).eq_or_lt with h0 | h0
  · rw [← h0]; exact (norm_nonneg v).trans hv
  · have : ‖u‖ ≤ ‖v‖ := by nlinarith
    exact this.trans hv

/-- **Closed range from a uniform fibre gap.** -/
theorem isClosed_range_mulOp_of_gap (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hgap : ∀ᵐ a ∂μ, ∀ v ∈ (LinearMap.ker (m a : E →ₗ[𝕜] F))ᗮ, ‖v‖ ≤ C * ‖m a v‖) :
    _root_.IsClosed (LinearMap.range (mulOp μ m).toFun : Set (Lp F 2 μ)) :=
  isClosed_range_of_norm_le (isClosed_mulOp hm) (norm_le_of_gap hm hgap)

/-- **Non-closed range from degeneration of the symbol.** If for every `ε > 0` there are a
measurable set `s` of positive finite measure and a vector `v` with `m a v ≠ 0` and `‖m a‖ ≤ ε`
on `s`, then the range of `mulOp μ m` is not closed (no Poincaré inequality). -/
theorem not_isClosed_range_mulOp (hm : AEStronglyMeasurable m μ)
    (h : ∀ ε > 0, ∃ s, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ ∧
      ∃ v : E, ∀ a ∈ s, m a v ≠ 0 ∧ ‖m a‖ ≤ ε) :
    ¬ _root_.IsClosed (LinearMap.range (mulOp μ m).toFun : Set (Lp F 2 μ)) := by
  intro hR
  obtain ⟨c, hc⟩ := exists_norm_le_of_isClosed_range (T := mulOp μ m) (isClosed_mulOp hm) hR
  set ε : ℝ := 1 / (2 * (|c| + 1)) with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨s, hs, hs0, hsT, v, hv⟩ := h ε hε
  set w : Lp E 2 μ := indicatorConstLp 2 hs hsT v
  have hw := indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hsT) (c := v)
  set u := kerOrthProj hm w
  have hu_ae : ∀ᵐ a ∂μ, u a = s.indicator (fun a =>
      v - (LinearMap.ker (m a : E →ₗ[𝕜] F)).starProjection v) a := by
    filter_upwards [coeFn_kerOrthProj hm w, hw] with a h1 h2
    rw [h1, h2]
    by_cases ha : a ∈ s
    · simp [Set.indicator_of_mem ha]
    · simp [Set.indicator_of_notMem ha]
  have hmu : ∀ᵐ a ∂μ, m a (u a) = s.indicator (fun a => m a v) a := by
    filter_upwards [hu_ae] with a h1
    rw [h1]
    by_cases ha : a ∈ s
    · simp [Set.indicator_of_mem ha, apply_sub_starProjection_ker]
    · simp [Set.indicator_of_notMem ha]
  have hbound : ∀ᵐ a ∂μ, ‖m a (u a)‖ ≤ ε * ‖u a‖ := by
    filter_upwards [hu_ae] with a h1
    rw [h1]
    by_cases ha : a ∈ s
    · simp only [Set.indicator_of_mem ha]
      exact (m a).le_of_opNorm_le (hv a ha).2 _
    · simp [Set.indicator_of_notMem ha]
  have hud : u ∈ mulDomain μ m :=
    MemLp.of_le_mul (Lp.memLp u)
      (aestronglyMeasurable_clm_apply hm (Lp.aestronglyMeasurable u)) hbound
  have horth : u ∈ (mulOp μ m).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    rw [mem_ker_mulOp] at hk
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans (integral_zero α 𝕜)
    filter_upwards [hk, coeFn_kerOrthProj hm w] with a h1 h2
    rw [h2]
    have h := (LinearMap.ker (m a : E →ₗ[𝕜] F)).inner_left_of_mem_orthogonal h1
      ((LinearMap.ker (m a : E →ₗ[𝕜] F)).sub_starProjection_mem_orthogonal (w a))
    rw [← inner_conj_symm, h, _root_.map_zero]
  have h1 := hc ⟨u, hud⟩ horth
  have h2 : ‖mulOp μ m ⟨u, hud⟩‖ ≤ ε * ‖u‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_mulOp μ m ⟨u, hud⟩, hbound] with a h3 h4
    rw [h3]; exact h4
  have hkey : |c| * ε ≤ 1 / 2 := by
    rw [hε_def, show |c| * (1 / (2 * (|c| + 1))) = |c| / (2 * (|c| + 1)) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg c]
  have hle : ‖u‖ ≤ ‖u‖ / 2 := by
    calc ‖u‖ ≤ c * ‖mulOp μ m ⟨u, hud⟩‖ := h1
      _ ≤ |c| * ‖mulOp μ m ⟨u, hud⟩‖ := mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)
      _ ≤ |c| * (ε * ‖u‖) := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
      _ = (|c| * ε) * ‖u‖ := by ring
      _ ≤ (1 / 2) * ‖u‖ := mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
      _ = ‖u‖ / 2 := by ring
  have hu0 : u = 0 := norm_eq_zero.1 (le_antisymm (by linarith [norm_nonneg u]) (norm_nonneg u))
  have hnull : ∀ᵐ a ∂μ, a ∉ s := by
    filter_upwards [hmu, Lp.coeFn_zero E 2 μ] with a h3 h4 ha
    rw [hu0, h4, Pi.zero_apply, _root_.map_zero, Set.indicator_of_mem ha] at h3
    exact (hv a ha).1 h3.symm
  exact hs0 (measure_eq_zero_iff_ae_notMem.2 hnull)

end Operator

namespace Fourier

/-! ### Fibre gaps from homotopies -/

section Homotopy

variable {E₀ E₁ E₂ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace 𝕜 E₂]

/-- **Algebraic Poincaré inequality from a homotopy.** If `m₁ m₀ = 0` and
`m₀ h₁ + h₂ m₁ = 1` on `E₁` with `‖h₂‖ ≤ C`, then `‖v‖ ≤ C ‖m₁ v‖` for `v ⊥ N(m₁)`. -/
theorem gap_of_homotopy (m₀ : E₀ →L[𝕜] E₁) (m₁ : E₁ →L[𝕜] E₂) (h₁ : E₁ →L[𝕜] E₀)
    (h₂ : E₂ →L[𝕜] E₁) (hcomp : ∀ x, m₁ (m₀ x) = 0) (hhom : ∀ v, m₀ (h₁ v) + h₂ (m₁ v) = v)
    {C : ℝ} (hC : ‖h₂‖ ≤ C) :
    ∀ v ∈ (LinearMap.ker (m₁ : E₁ →ₗ[𝕜] E₂))ᗮ, ‖v‖ ≤ C * ‖m₁ v‖ := by
  intro v hv
  have h0 : ⟪v, m₀ (h₁ v)⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal' _ _).1 hv _ (LinearMap.mem_ker.2 (hcomp _))
  have hsq : ‖v‖ ^ 2 ≤ ‖v‖ * (C * ‖m₁ v‖) := by
    have e : ‖v‖ ^ 2 = RCLike.re ⟪v, h₂ (m₁ v)⟫_𝕜 := by
      conv_lhs => rw [← hhom v]
      rw [show ‖m₀ (h₁ v) + h₂ (m₁ v)‖ = ‖v‖ by rw [hhom v]]
      conv_rhs => rw [← sub_eq_of_eq_add' (hhom v).symm]
      rw [inner_sub_right, h0, sub_zero, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
        RCLike.ofReal_re]
    rw [e]
    refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (h₂.le_opNorm _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  rcases (norm_nonneg v).eq_or_lt with h | h
  · rw [← h]
    have : (0 : ℝ) ≤ C := (norm_nonneg _).trans hC
    positivity
  · nlinarith

end Homotopy

/-! ### Symbol complexes -/

namespace SymbolComplex

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*} {c : ComplexShape ι}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  [∀ i, CompleteSpace (E i)] (S : SymbolComplex 𝕜 μ c E)

/-- **Closed range of a symbol complex from a uniform fibre gap** of the incoming symbol. -/
theorem closedRangeAt_of_gap {i : ι} [FiniteDimensional 𝕜 (E (c.prev i))] {C : ℝ}
    (hgap : ∀ᵐ a ∂μ, ∀ v ∈ (LinearMap.ker (S.m (c.prev i) i a : E (c.prev i) →ₗ[𝕜] E i))ᗮ,
      ‖v‖ ≤ C * ‖S.m (c.prev i) i a v‖) :
    S.toHilbertComplex.ClosedRangeAt i :=
  Operator.isClosed_range_mulOp_of_gap (S.meas _ _) hgap

/-- The Poincaré inequality of a symbol complex, with the fibre constant. -/
theorem norm_le_of_gap {i j : ι} [FiniteDimensional 𝕜 (E i)] {C : ℝ}
    (hgap : ∀ᵐ a ∂μ, ∀ v ∈ (LinearMap.ker (S.m i j a : E i →ₗ[𝕜] E j))ᗮ,
      ‖v‖ ≤ C * ‖S.m i j a v‖)
    (x : (S.toHilbertComplex.d i j).domain)
    (hx : (x : Lp (E i) 2 μ) ∈ (S.toHilbertComplex.d i j).kerᗮ) :
    ‖(x : Lp (E i) 2 μ)‖ ≤ C * ‖S.toHilbertComplex.d i j x‖ :=
  Operator.norm_le_of_gap (S.meas i j) hgap x hx

/-- Closed range of the dual complex from a fibre gap of the outgoing symbol. -/
theorem dual_closedRangeAt_of_gap {i j : ι} (hij : c.Rel i j) [FiniteDimensional 𝕜 (E i)]
    {C : ℝ} (hgap : ∀ᵐ a ∂μ, ∀ v ∈ (LinearMap.ker (S.m i j a : E i →ₗ[𝕜] E j))ᗮ,
      ‖v‖ ≤ C * ‖S.m i j a v‖) :
    S.toHilbertComplex.dual.ClosedRangeAt i := by
  have hj : S.toHilbertComplex.ClosedRangeAt j := by
    have := Operator.isClosed_range_mulOp_of_gap (S.meas i j) hgap
    rwa [HilbertComplex.ClosedRangeAt, S.toHilbertComplex.boundaries_eq hij]
  exact (S.toHilbertComplex.dual_closedRangeAt_iff hij).2 hj

/-- **Non-closed range of a symbol complex** when the incoming symbol degenerates. -/
theorem not_closedRangeAt {i : ι} [FiniteDimensional 𝕜 (E (c.prev i))]
    (h : ∀ ε > 0, ∃ s, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ ∧
      ∃ v : E (c.prev i), ∀ a ∈ s, S.m (c.prev i) i a v ≠ 0 ∧ ‖S.m (c.prev i) i a‖ ≤ ε) :
    ¬ S.toHilbertComplex.ClosedRangeAt i :=
  Operator.not_isClosed_range_mulOp (S.meas _ _) h

end SymbolComplex


/-! ### Homogeneous families of fibre complexes -/

namespace FibreComplex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type*} {c : ComplexShape ι}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]

/-- The arrow `i → j` of a family of fibre complexes is **homogeneous of degree `r`**:
`m (t ξ) = tʳ m ξ` for `t > 0` (an order-`r` constant-coefficient operator). -/
def IsHomogeneous (S : FibreComplex 𝕜 V c E) (i j : ι) (r : ℕ) : Prop :=
  ∀ (t : ℝ) (ξ : V), 0 < t → S.m i j (t • ξ) = ((t ^ r : ℝ) : 𝕜) • S.m i j ξ

variable {S : FibreComplex 𝕜 V c E} {i j : ι} {r : ℕ}

theorem IsHomogeneous.ker_eq (h : S.IsHomogeneous i j r) {t : ℝ} (ht : 0 < t) (ξ : V) :
    LinearMap.ker (S.m i j (t • ξ) : E i →ₗ[𝕜] E j) = LinearMap.ker (S.m i j ξ : E i →ₗ[𝕜] E j) := by
  ext v
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, h t ξ ht,
    _root_.smul_apply, smul_eq_zero, RCLike.ofReal_eq_zero,
    pow_eq_zero_iff', ht.ne', false_and, false_or]

/-- **Scaling of a fibre gap**: a gap `‖v‖ ≤ C ‖m ω v‖` on the unit sphere gives
`|ξ|ʳ ‖v‖ ≤ C ‖m ξ v‖` at every `ξ ≠ 0`. -/
theorem IsHomogeneous.gap (h : S.IsHomogeneous i j r) {C : ℝ}
    (hgap : ∀ ω : V, ‖ω‖ = 1 → ∀ v ∈ (LinearMap.ker (S.m i j ω : E i →ₗ[𝕜] E j))ᗮ,
      ‖v‖ ≤ C * ‖S.m i j ω v‖) {ξ : V} (hξ : ξ ≠ 0) :
    ∀ v ∈ (LinearMap.ker (S.m i j ξ : E i →ₗ[𝕜] E j))ᗮ, ‖ξ‖ ^ r * ‖v‖ ≤ C * ‖S.m i j ξ v‖ := by
  intro v hv
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set ω : V := ‖ξ‖⁻¹ • ξ
  have hω : ‖ω‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hξω : ξ = ‖ξ‖ • ω := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hm : S.m i j ξ = ((‖ξ‖ ^ r : ℝ) : 𝕜) • S.m i j ω := by
    conv_lhs => rw [hξω]
    exact h _ _ hn
  have hv' : v ∈ (LinearMap.ker (S.m i j ω : E i →ₗ[𝕜] E j))ᗮ := by
    rwa [hξω, h.ker_eq hn] at hv
  have key := hgap ω hω v hv'
  rw [hm, _root_.smul_apply, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity)]
  calc ‖ξ‖ ^ r * ‖v‖ ≤ ‖ξ‖ ^ r * (C * ‖S.m i j ω v‖) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = C * (‖ξ‖ ^ r * ‖S.m i j ω v‖) := by ring

/-- A fibre gap on the unit sphere gives a uniform gap `C / Rʳ` on `|ξ| ≥ R > 0`. -/
theorem IsHomogeneous.gap_of_le (h : S.IsHomogeneous i j r) {C : ℝ}
    (hgap : ∀ ω : V, ‖ω‖ = 1 → ∀ v ∈ (LinearMap.ker (S.m i j ω : E i →ₗ[𝕜] E j))ᗮ,
      ‖v‖ ≤ C * ‖S.m i j ω v‖) {R : ℝ} (hR : 0 < R) {ξ : V} (hξ : R ≤ ‖ξ‖) :
    ∀ v ∈ (LinearMap.ker (S.m i j ξ : E i →ₗ[𝕜] E j))ᗮ, ‖v‖ ≤ C / R ^ r * ‖S.m i j ξ v‖ := by
  intro v hv
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (hR.trans_le hξ)
  have key := h.gap hgap hξ0 v hv
  have hRr : 0 < R ^ r := pow_pos hR r
  rw [div_mul_eq_mul_div, le_div_iff₀ hRr]
  calc ‖v‖ * R ^ r ≤ ‖v‖ * ‖ξ‖ ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hξ r) (norm_nonneg _)
    _ = ‖ξ‖ ^ r * ‖v‖ := mul_comm _ _
    _ ≤ C * ‖S.m i j ξ v‖ := key

end FibreComplex

end Fourier

end Feec
