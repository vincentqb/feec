module

public import Feec.HilbertComplex.Hodge
public import Feec.HilbertComplex.Window
public import Feec.Operator.Multiplication
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Symbol complexes: Hilbert complexes of multiplication operators on `L²(μ)`

A constant-coefficient differential complex becomes, after a Fourier transform (Fourier series on
the torus `𝕋ⁿ`, Plancherel on `ℝⁿ`), a complex of multiplication operators: at every frequency `a`
a finite-dimensional complex of matrices `m i j a : E i →L[𝕜] E j` with `m j k a ∘ m i j a = 0`.
This file is the one theory behind all such models, for any measure space `(α, μ)` (counting
measure on `ℤⁿ` for `𝕋ⁿ`, Lebesgue measure on `ℝⁿ`), any index shape, and `𝕜 = ℝ` or `ℂ`.

## Main definitions

* `Fourier.SymbolComplex 𝕜 μ c E`: measurable families of operators `m i j`, zero off the
  relation of `c`, with fibrewise `m j k a ∘ m i j a = 0`.
* `SymbolComplex.toHilbertComplex`: the Hilbert complex `L²(μ; E i)` with `d i j = mulOp μ (m i j)`.
  No measurability beyond a.e. strong measurability, no σ-finiteness, no finite dimension
  (complete fibres suffice).
* `SymbolComplex.adjoint`: the fibrewise adjoint symbols, a symbol complex on `c.symm`.
* `Fourier.FibreComplex 𝕜 β c E`: a continuous family of fibre complexes parametrised by a
  frequency `ξ ∈ β`, and `FibreComplex.toSymbolComplex`, its pull-back along a measurable
  frequency map `α → β` (e.g. `k ↦ 2πk` on `ℤⁿ`, `x ↦ 2πx` on `ℝⁿ`).

## Main results

* `toHilbertComplex_dual`: **the dual complex is the complex of adjoint symbols**,
  `(toHilbertComplex S).dual = toHilbertComplex S.adjoint`.
* `ker_mulOp`, `cycles_toHilbertComplex`, `harmonic_toHilbertComplex`: kernels, cycles and
  harmonic forms are the fibrewise subspaces of the fibre kernels, cycles and harmonic forms.
* `aestronglyMeasurable_starProjection_ker`: the fibre kernel projections of a measurable family
  on a finite-dimensional space are measurable (through `P_{ker b} = P_{ker b† b}` and
  `Feec.Operator.stronglyMeasurable_starProjection_ker`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10–4.11 (the Fourier models of the periodic and whole-space complexes)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
  (Hilbert complexes)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018] (Hilbert complexes)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set

namespace Feec

namespace Operator

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (μ) in
/-- The multiplier by the zero symbol is the zero operator (domain `⊤`). -/
theorem mulOp_zero : mulOp μ (0 : α → E →L[𝕜] F) = 0 := by
  have hdom : mulDomain μ (0 : α → E →L[𝕜] F) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    change MemLp _ 2 μ
    simp
  refine LinearPMap.ext (hdom.trans rfl) fun x hx _ => ?_
  rw [mulOp_apply_eq_iff ⟨x, hx⟩, LinearPMap.zero_apply]
  filter_upwards [Lp.coeFn_zero F 2 μ] with a h
  rw [h]; rfl

/-- `u` is in the kernel of `mulOp μ m` iff `m a (u a) = 0` for a.e. `a`. -/
theorem mem_ker_mulOp {m : α → E →L[𝕜] F} {u : Lp E 2 μ} :
    u ∈ (mulOp μ m).ker ↔ ∀ᵐ a ∂μ, m a (u a) = 0 := by
  constructor
  · intro hu
    obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hu
    have := (mulOp_apply_eq_iff y 0).1 hy
    filter_upwards [this, Lp.coeFn_zero F 2 μ] with a h1 h2
    rw [h1, h2]; rfl
  · intro h
    have hu : u ∈ mulDomain μ m := by
      change MemLp _ 2 μ
      exact (MemLp.zero : MemLp (0 : α → F) 2 μ).ae_eq (h.mono fun a ha => ha.symm)
    refine LinearPMap.mem_ker_iff.2 ⟨⟨u, hu⟩, rfl, (mulOp_apply_eq_iff _ 0).2 ?_⟩
    filter_upwards [h, Lp.coeFn_zero F 2 μ] with a h1 h2
    rw [h1, h2]; rfl

/-- **The kernel of a multiplication operator is the fibrewise kernel.** -/
theorem ker_mulOp (m : α → E →L[𝕜] F) :
    (mulOp μ m).ker = Operator.fibreSub μ fun a => LinearMap.ker (m a : E →ₗ[𝕜] F) := by
  ext u; exact mem_ker_mulOp

/-- `u ∈ L²` is in the range of `mulOp μ m` iff it is `m v` for some `v ∈ L²` with `m v ∈ L²`. -/
theorem mem_range_mulOp {m : α → E →L[𝕜] F} {y : Lp F 2 μ} :
    y ∈ LinearMap.range (mulOp μ m).toFun ↔
      ∃ v : Lp E 2 μ, ∀ᵐ a ∂μ, m a (v a) = y a := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, (coeFn_mulOp μ m v).mono fun a h => h.symm⟩
  · rintro ⟨v, hv⟩
    have hvd : v ∈ mulDomain μ m := by
      change MemLp _ 2 μ
      exact (Lp.memLp y).ae_eq (hv.mono fun a h => h.symm)
    exact ⟨⟨v, hvd⟩, (mulOp_apply_eq_iff ⟨v, hvd⟩ y).2 hv⟩

end Operator

namespace Fourier

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Measurable kernel projections -/

section KerProj

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- `b ↦ P_{ker b}` is strongly measurable on `E →L[𝕜] F` (finite dimensions). -/
theorem stronglyMeasurable_starProjection_ker_clm :
    StronglyMeasurable fun b : E →L[𝕜] F => (LinearMap.ker (b : E →ₗ[𝕜] F)).starProjection := by
  have hker : ∀ b : E →L[𝕜] F, LinearMap.ker (b : E →ₗ[𝕜] F) =
      LinearMap.ker ((ContinuousLinearMap.adjoint b ∘L b : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    intro b
    ext x
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h
      have : ⟪b x, b x⟫_𝕜 = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_right, h, inner_zero_right]
      exact inner_self_eq_zero.1 this
  have hfun : (fun b : E →L[𝕜] F => (LinearMap.ker (b : E →ₗ[𝕜] F)).starProjection) =
      fun b => (LinearMap.ker ((ContinuousLinearMap.adjoint b ∘L b : E →L[𝕜] E) :
        E →ₗ[𝕜] E)).starProjection := by
    funext b; simp_rw [hker b]
  rw [hfun]
  refine Operator.stronglyMeasurable_starProjection_ker (H := fun b : E →L[𝕜] F =>
    ContinuousLinearMap.adjoint b ∘L b) ?_ ?_ ?_
  · exact (ContinuousLinearMap.compL 𝕜 E F E).continuous₂.comp₂
      (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := E) (F := F)).continuous continuous_id
  · intro b x y
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  · intro b x
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    positivity

/-- **Fibre kernel projections of a measurable family are measurable.** -/
theorem aestronglyMeasurable_starProjection_ker {m : α → E →L[𝕜] F}
    (hm : AEStronglyMeasurable m μ) :
    AEStronglyMeasurable (fun a => (LinearMap.ker (m a : E →ₗ[𝕜] F)).starProjection) μ :=
  (stronglyMeasurable_starProjection_ker_clm (𝕜 := 𝕜) (E := E) (F := F)).aestronglyMeasurable.comp_aemeasurable
    hm.aemeasurable

end KerProj

/-! ### Symbol complexes -/

/-- A **symbol complex** over `(α, μ)` with index shape `c`: a.e. strongly measurable families
`m i j : α → E i →L[𝕜] E j`, zero off the relation of `c`, with `m j k a ∘ m i j a = 0` at every
frequency `a`. Its Hilbert complex (`toHilbertComplex`) is the complex of multiplication
operators on `L²(μ; E i)`. -/
structure SymbolComplex (𝕜 : Type*) [RCLike 𝕜] {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ι : Type*} (c : ComplexShape ι) (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] where
  /-- the symbols -/
  m : ∀ i j, α → E i →L[𝕜] E j
  shape : ∀ i j, ¬ c.Rel i j → m i j = 0
  comp : ∀ i j k a, (m j k a).comp (m i j a) = 0
  meas : ∀ i j, AEStronglyMeasurable (m i j) μ

namespace SymbolComplex

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*} {c : ComplexShape ι}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  (S : SymbolComplex 𝕜 μ c E)

theorem comp_apply (i j k : ι) (a : α) (v : E i) : S.m j k a (S.m i j a v) = 0 := by
  have := congrArg (fun T : E i →L[𝕜] E k => T v) (S.comp i j k a)
  simpa using this

/-- The fibre complex at a frequency `a` satisfies `R(m i j a) ⊆ N(m j k a)`. -/
theorem range_le_ker (i j k : ι) (a : α) :
    LinearMap.range (S.m i j a : E i →ₗ[𝕜] E j) ≤ LinearMap.ker (S.m j k a : E j →ₗ[𝕜] E k) := by
  rintro _ ⟨v, rfl⟩
  exact S.comp_apply i j k a v

variable [∀ i, CompleteSpace (E i)]

/-- **The Hilbert complex of a symbol complex**: `L²(μ; E i)` with the multiplication operators
`d i j = mulOp μ (m i j)` (closed, densely defined, `d d = 0`). -/
def toHilbertComplex : HilbertComplex 𝕜 c fun i => Lp (E i) 2 μ where
  d i j := Operator.mulOp μ (S.m i j)
  shape i j h := by rw [S.shape i j h]; exact Operator.mulOp_zero μ
  dense i j := Operator.dense_mulDomain (S.meas i j)
  closed i j := Operator.isClosed_mulOp (S.meas i j)
  mapsTo i j k x := by
    change MemLp _ 2 μ
    refine (MemLp.zero : MemLp (0 : α → E k) 2 μ).ae_eq ?_
    filter_upwards [Operator.coeFn_mulOp μ (S.m i j) x] with a h
    rw [h]; exact (S.comp_apply i j k a _).symm
  d_comp_d i j k x := by
    refine (Operator.mulOp_apply_eq_iff _ 0).2 ?_
    filter_upwards [Operator.coeFn_mulOp μ (S.m i j) x, Lp.coeFn_zero (E k) 2 μ] with a h1 h2
    change S.m j k a ((Operator.mulOp μ (S.m i j) x : Lp (E j) 2 μ) a) = _
    rw [h1, h2]; exact S.comp_apply i j k a _

@[simp] theorem toHilbertComplex_d (i j : ι) :
    S.toHilbertComplex.d i j = Operator.mulOp μ (S.m i j) := rfl

/-- The differentials act fibrewise. -/
theorem coeFn_d {i j : ι} (u : (S.toHilbertComplex.d i j).domain) :
    S.toHilbertComplex.d i j u =ᵐ[μ] fun a => S.m i j a ((u : Lp (E i) 2 μ) a) :=
  Operator.coeFn_mulOp μ (S.m i j) u

theorem mem_domain_d_iff {i j : ι} {u : Lp (E i) 2 μ} :
    u ∈ (S.toHilbertComplex.d i j).domain ↔ MemLp (fun a => S.m i j a (u a)) 2 μ := Iff.rfl

/-- **The adjoint differentials are the multipliers by the adjoint symbols**, domain included. -/
theorem adjoint_d (i j : ι) :
    (S.toHilbertComplex.d i j)† = Operator.mulOp μ fun a => ContinuousLinearMap.adjoint (S.m i j a) :=
  Operator.adjoint_mulOp (S.meas i j)

/-- The adjoint symbol complex on `c.symm`: `m' i j a = (m j i a)†`. -/
def adjoint : SymbolComplex 𝕜 μ c.symm E where
  m i j a := ContinuousLinearMap.adjoint (S.m j i a)
  shape i j h := by
    funext a
    change ¬ c.Rel j i at h
    rw [S.shape j i h]
    exact _root_.map_zero _
  comp i j k a := by
    rw [← ContinuousLinearMap.adjoint_comp, S.comp k j i a, _root_.map_zero]
  meas i j := Operator.aestronglyMeasurable_adjoint (S.meas j i)

@[simp] theorem adjoint_m (i j : ι) (a : α) :
    S.adjoint.m i j a = ContinuousLinearMap.adjoint (S.m j i a) := rfl

/-- Two Hilbert complexes with the same differentials are equal. -/
theorem _root_.Feec.HilbertComplex.ext' {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] {H H' : HilbertComplex 𝕜 c W}
    (h : H.d = H'.d) : H = H' := by
  cases H; cases H'; subst h; rfl

/-- **The dual of a symbol complex is the complex of the adjoint symbols.** -/
theorem toHilbertComplex_dual : S.toHilbertComplex.dual = S.adjoint.toHilbertComplex := by
  refine HilbertComplex.ext' ?_
  funext i j
  exact S.adjoint_d j i

/-- Cycles are the fibrewise cycles. -/
theorem cycles_toHilbertComplex (i : ι) :
    S.toHilbertComplex.cycles i = Operator.fibreSub μ fun a => LinearMap.ker (S.m i (c.next i) a : E i →ₗ[𝕜] E (c.next i)) :=
  Operator.ker_mulOp _

/-- Cycles of the dual complex (kernels of the adjoints) are fibrewise. -/
theorem ker_adjoint_d (i j : ι) : ((S.toHilbertComplex.d i j)†).ker =
    Operator.fibreSub μ fun a => LinearMap.ker (ContinuousLinearMap.adjoint (S.m i j a) : E j →ₗ[𝕜] E i) := by
  rw [adjoint_d]; exact Operator.ker_mulOp _

/-- **Harmonic forms are the fibrewise harmonic forms**: `ℌⁱ = {u | u a ∈ N(m_a) ∩ N(m'_a†)}`. -/
theorem harmonic_toHilbertComplex (i : ι) :
    S.toHilbertComplex.harmonic i = Operator.fibreSub μ fun a =>
      LinearMap.ker (S.m i (c.next i) a : E i →ₗ[𝕜] E (c.next i)) ⊓
        LinearMap.ker (ContinuousLinearMap.adjoint (S.m (c.prev i) i a) : E i →ₗ[𝕜] E (c.prev i)) := by
  ext u
  change u ∈ S.toHilbertComplex.cycles i ⊓ _ ↔ _
  rw [Submodule.mem_inf, cycles_toHilbertComplex, ker_adjoint_d]
  simp only [Operator.mem_fibreSub, Submodule.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩; filter_upwards [h1, h2] with a h1 h2 using ⟨h1, h2⟩
  · intro h; exact ⟨h.mono fun a h => h.1, h.mono fun a h => h.2⟩

/-- Boundaries: `y` is a boundary iff it is fibrewise `m v` for an `L²` field `v`. -/
theorem mem_boundaries_iff {i : ι} {y : Lp (E i) 2 μ} :
    y ∈ S.toHilbertComplex.boundaries i ↔
      ∃ v : Lp (E (c.prev i)) 2 μ, ∀ᵐ a ∂μ, S.m (c.prev i) i a (v a) = y a :=
  Operator.mem_range_mulOp

/-- Pull a symbol complex back along an index map reflecting the relation (e.g. a window). -/
def restrict {ι' : Type*} {c' : ComplexShape ι'} (f : ι' → ι)
    (hf : ∀ i j, c.Rel (f i) (f j) → c'.Rel i j) : SymbolComplex 𝕜 μ c' fun i => E (f i) where
  m i j := S.m (f i) (f j)
  shape i j h := S.shape _ _ fun h' => h (hf i j h')
  comp _ _ _ a := S.comp _ _ _ a
  meas _ _ := S.meas _ _

/-- The Hilbert complex of a restricted symbol complex is the restricted Hilbert complex. -/
theorem toHilbertComplex_restrict {ι' : Type*} {c' : ComplexShape ι'} (f : ι' → ι)
    (hf : ∀ i j, c.Rel (f i) (f j) → c'.Rel i j) :
    (S.restrict f hf).toHilbertComplex = S.toHilbertComplex.restrict f hf :=
  HilbertComplex.ext' rfl

end SymbolComplex

/-! ### Continuous families of fibre complexes -/

/-- A **continuous family of fibre complexes** parametrised by a frequency `ξ ∈ β`: continuous
`m i j : β → E i →L[𝕜] E j`, zero off the relation of `c`, with `m j k ξ ∘ m i j ξ = 0`. The
symbols of a constant-coefficient differential complex (`β = ℝⁿ`). -/
structure FibreComplex (𝕜 : Type*) [RCLike 𝕜] (β : Type*) [TopologicalSpace β] {ι : Type*}
    (c : ComplexShape ι) (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] where
  /-- the symbols -/
  m : ∀ i j, β → E i →L[𝕜] E j
  shape : ∀ i j, ¬ c.Rel i j → m i j = 0
  comp : ∀ i j k ξ, (m j k ξ).comp (m i j ξ) = 0
  cont : ∀ i j, Continuous (m i j)

namespace FibreComplex

variable {β : Type*} [TopologicalSpace β] {ι : Type*} {c : ComplexShape ι}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  (S : FibreComplex 𝕜 β c E)

theorem comp_apply (i j k : ι) (ξ : β) (v : E i) : S.m j k ξ (S.m i j ξ v) = 0 := by
  have := congrArg (fun T : E i →L[𝕜] E k => T v) (S.comp i j k ξ)
  simpa using this


/-! ### Families on `ComplexShape.up α` from successive symbols -/

section OfSucc

variable {α : Type*} [Add α] [One α] {V : α → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)]

open Classical in
/-- The symbols of `ofSucc`: `δ i` transported along `i + 1 = j`, else `0`. -/
def ofSuccM (δ : ∀ i, β → V i →L[𝕜] V (i + 1)) (i j : α) : β → V i →L[𝕜] V j :=
  if h : i + 1 = j then h ▸ δ i else 0

omit [TopologicalSpace β] in
theorem ofSuccM_succ (δ : ∀ i, β → V i →L[𝕜] V (i + 1)) (i : α) : ofSuccM δ i (i + 1) = δ i := by
  simp [ofSuccM]

omit [TopologicalSpace β] in
theorem ofSuccM_of_ne (δ : ∀ i, β → V i →L[𝕜] V (i + 1)) {i j : α} (h : i + 1 ≠ j) :
    ofSuccM δ i j = 0 := by
  simp [ofSuccM, h]

/-- The family of fibre complexes `⋯ → V i → V (i + 1) → ⋯` on `ComplexShape.up α` built from
continuous `δ i : β → V i →L[𝕜] V (i + 1)` with `δ (i + 1) ξ ∘ δ i ξ = 0`. -/
def ofSucc [IsRightCancelAdd α] (δ : ∀ i, β → V i →L[𝕜] V (i + 1))
    (comp : ∀ i ξ, (δ (i + 1) ξ).comp (δ i ξ) = 0) (cont : ∀ i, Continuous (δ i)) :
    FibreComplex 𝕜 β (ComplexShape.up α) V where
  m := ofSuccM δ
  shape i j h := ofSuccM_of_ne δ h
  comp i j k ξ := by
    by_cases h : i + 1 = j
    · subst h
      by_cases h' : i + 1 + 1 = k
      · subst h'; rw [ofSuccM_succ, ofSuccM_succ]; exact comp i ξ
      · rw [ofSuccM_of_ne δ h']; exact ContinuousLinearMap.zero_comp _
    · rw [ofSuccM_of_ne δ h]; exact ContinuousLinearMap.comp_zero _
  cont i j := by
    by_cases h : i + 1 = j
    · subst h; rw [ofSuccM_succ]; exact cont i
    · rw [ofSuccM_of_ne δ h]; exact continuous_const

@[simp] theorem ofSucc_m_succ [IsRightCancelAdd α] (δ : ∀ i, β → V i →L[𝕜] V (i + 1))
    (comp : ∀ i ξ, (δ (i + 1) ξ).comp (δ i ξ) = 0) (cont : ∀ i, Continuous (δ i)) (i : α) :
    (ofSucc δ comp cont).m i (i + 1) = δ i := ofSuccM_succ δ i

end OfSucc

section Adjoint

variable [∀ i, CompleteSpace (E i)]

/-- The adjoint fibre complex on `c.symm`. -/
def adjoint : FibreComplex 𝕜 β c.symm E where
  m i j ξ := ContinuousLinearMap.adjoint (S.m j i ξ)
  shape i j h := by
    funext ξ
    change ¬ c.Rel j i at h
    rw [S.shape j i h]
    exact _root_.map_zero _
  comp i j k ξ := by
    rw [← ContinuousLinearMap.adjoint_comp, S.comp k j i ξ, _root_.map_zero]
  cont i j := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := E j) (F := E i)).continuous.comp
    (S.cont j i)

end Adjoint

variable [MeasurableSpace β] [OpensMeasurableSpace β] [∀ i, FiniteDimensional 𝕜 (E i)]
  {α : Type*} [MeasurableSpace α]

/-- The symbol complex `a ↦ S.m i j (f a)` over `(α, μ)`, for an a.e. measurable frequency map
`f : α → β`. -/
def toSymbolComplex (μ : Measure α) (f : α → β) (hf : AEMeasurable f μ) :
    SymbolComplex 𝕜 μ c E where
  m i j a := S.m i j (f a)
  shape i j h := by rw [S.shape i j h]; rfl
  comp i j k a := S.comp i j k (f a)
  meas i j := by
    have : ProperSpace (E i →L[𝕜] E j) := FiniteDimensional.proper_rclike 𝕜 _
    have : SecondCountableTopology (E i →L[𝕜] E j) := secondCountable_of_proper
    exact (S.cont i j).aestronglyMeasurable.comp_aemeasurable hf

@[simp] theorem toSymbolComplex_m (μ : Measure α) (f : α → β) (hf : AEMeasurable f μ)
    (i j : ι) (a : α) : (S.toSymbolComplex μ f hf).m i j a = S.m i j (f a) := rfl

end FibreComplex

end Fourier

end Feec
