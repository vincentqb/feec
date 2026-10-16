module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Ring.Units
public import Feec.ForMathlib.Lp.CountEquiv

/-!
# Multiplication operators on `L²(μ; E)`

For a measure space `(α, μ)`, Hilbert spaces `E, F` over `𝕜 = ℝ` or `ℂ`, and a measurable
family of operators `m : α → E →L[𝕜] F` (a *fibre-matrix symbol*), the multiplication operator
`u ↦ (a ↦ m a (u a))` on `L²(μ; E)`. This one theory covers

* Fourier multipliers on `L²(ℝⁿ)` (`α = ℝⁿ` frequency space, `μ = volume`), and
* Fourier multipliers on the torus, `ℓ²(ℤⁿ)` (`α = ℤⁿ`, `μ = count`), through the isometry
  `lp.equivLpCount : ℓ²(α; E) ≃ₗᵢ L²(α, count; E)`; for the counting measure no measurability
  hypothesis is needed (`isClosed_mulOp_count`, `dense_mulDomain_count`, `adjoint_mulOp_count`)
  and the domain is the weighted-`ℓ²` condition (`equivLpCount_mem_mulDomain_iff`).

## Main results

* `mulCLM μ B hB C hC`: the bounded multiplier by an a.e. strongly measurable, a.e. bounded
  family `B`, with `coeFn_mulCLM`, `norm_mulCLM_le` and `inner_mulCLM`
  (`⟪B u, v⟫ = ⟪u, B* v⟫`).
* `mulOp μ m` with domain `mulDomain μ m = {u | m u ∈ L²}`: closed (`isClosed_mulOp`),
  densely defined (`dense_mulDomain`), with adjoint the multiplier by the fibrewise adjoints,
  *domain included* (`adjoint_mulOp`). Only a.e. strong measurability of `m` is assumed, and
  `mulOp` depends on `m` only up to a.e. equality (`mulOp_congr_ae`). No σ-finiteness: the
  proofs use the truncations `𝟙_{‖m‖ ≤ n} m` and the exhaustion `⋃ₙ {‖m‖ ≤ n} = α`.
* `fibreSub μ K`: the fibrewise subspace `{u | u a ∈ K a a.e.}` for a family of subspaces with
  measurable orthogonal projections; it is closed (`isClosed_fibreSub`) and its orthogonal
  projection is the fibrewise projection (`starProjection_fibreSub`).
* Measurable dependence of kernel projections: for a continuous family `H b` of positive
  symmetric operators on a finite-dimensional space, `b ↦ P_{ker H b}` is strongly measurable
  (`stronglyMeasurable_starProjection_ker`), as the limit of the continuous resolvents
  `ε (ε + H b)⁻¹` (`tendsto_smul_inverse_smul_one_add`). This makes projections like the
  transverse-traceless projection `P_ξ`, discontinuous at `ξ = 0`, bounded multipliers.

## References

* [Kato1995] (closed operators and their adjoints; multiplication operators are the standard
  example)
-/

@[expose] public noncomputable section

open scoped ENNReal Topology
open MeasureTheory LinearPMap Set Filter

namespace Feec.Operator

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section Bounded

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `a ↦ B a (u a)` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_clm_apply {B : α → E →L[𝕜] F} (hB : AEStronglyMeasurable B μ)
    {u : α → E} (hu : AEStronglyMeasurable u μ) : AEStronglyMeasurable (fun a => B a (u a)) μ :=
  isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hB hu

/-- An a.e. uniformly bounded measurable family maps `L²` into `L²`. -/
theorem memLp_clm_apply {B : α → E →L[𝕜] F} (hB : AEStronglyMeasurable B μ) {C : ℝ}
    (hC : ∀ᵐ a ∂μ, ‖B a‖ ≤ C) (u : Lp E 2 μ) : MemLp (fun a => B a (u a)) 2 μ :=
  MemLp.of_le_mul (Lp.memLp u) (aestronglyMeasurable_clm_apply hB (Lp.aestronglyMeasurable u))
    (hC.mono fun a h => (B a).le_of_opNorm_le h _)

variable (μ) in
/-- The bounded multiplier `u ↦ (a ↦ B a (u a))` on `L²`, for an a.e. bounded family. -/
def mulCLM (B : α → E →L[𝕜] F) (hB : AEStronglyMeasurable B μ) (C : ℝ)
    (hC : ∀ᵐ a ∂μ, ‖B a‖ ≤ C) : Lp E 2 μ →L[𝕜] Lp F 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_clm_apply hB hC u).toLp _
      map_add' := fun u v => by
        refine Lp.ext ?_
        filter_upwards [(memLp_clm_apply hB hC (u + v)).coeFn_toLp,
          (memLp_clm_apply hB hC u).coeFn_toLp, (memLp_clm_apply hB hC v).coeFn_toLp,
          Lp.coeFn_add u v,
          Lp.coeFn_add ((memLp_clm_apply hB hC u).toLp _) ((memLp_clm_apply hB hC v).toLp _)]
          with a h1 h2 h3 h4 h5
        rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply, _root_.map_add]
      map_smul' := fun r u => by
        refine Lp.ext ?_
        filter_upwards [(memLp_clm_apply hB hC (r • u)).coeFn_toLp,
          (memLp_clm_apply hB hC u).coeFn_toLp, Lp.coeFn_smul r u,
          Lp.coeFn_smul r ((memLp_clm_apply hB hC u).toLp _)] with a h1 h2 h3 h4
        rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply, _root_.map_smul] }
    C fun u => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_clm_apply hB hC u).coeFn_toLp, hC] with a h hCa
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h]
      exact (B a).le_of_opNorm_le hCa _

theorem coeFn_mulCLM (B : α → E →L[𝕜] F) (hB : AEStronglyMeasurable B μ) (C : ℝ)
    (hC : ∀ᵐ a ∂μ, ‖B a‖ ≤ C) (u : Lp E 2 μ) :
    mulCLM μ B hB C hC u =ᵐ[μ] fun a => B a (u a) :=
  (memLp_clm_apply hB hC u).coeFn_toLp

/-- `‖B u‖ ≤ C ‖u‖`. -/
theorem norm_mulCLM_apply_le (B : α → E →L[𝕜] F) (hB : AEStronglyMeasurable B μ) (C : ℝ)
    (hC : ∀ᵐ a ∂μ, ‖B a‖ ≤ C) (u : Lp E 2 μ) : ‖mulCLM μ B hB C hC u‖ ≤ C * ‖u‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coeFn_mulCLM B hB C hC u, hC] with a h hCa
  rw [h]
  exact (B a).le_of_opNorm_le hCa _

/-- The multiplier only depends on the family up to a.e. equality. -/
theorem mulCLM_congr_ae {B B' : α → E →L[𝕜] F} {hB : AEStronglyMeasurable B μ}
    {hB' : AEStronglyMeasurable B' μ} {C C' : ℝ} {hC : ∀ᵐ a ∂μ, ‖B a‖ ≤ C}
    {hC' : ∀ᵐ a ∂μ, ‖B' a‖ ≤ C'} (h : B =ᵐ[μ] B') (u : Lp E 2 μ) :
    mulCLM μ B hB C hC u = mulCLM μ B' hB' C' hC' u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulCLM B hB C hC u, coeFn_mulCLM B' hB' C' hC' u, h] with a h1 h2 h3
  rw [h1, h2, h3]

variable [CompleteSpace E] [CompleteSpace F]

/-- The fibrewise adjoint family of a measurable family is measurable. -/
theorem aestronglyMeasurable_adjoint {B : α → E →L[𝕜] F} (hB : AEStronglyMeasurable B μ) :
    AEStronglyMeasurable (fun a => ContinuousLinearMap.adjoint (B a)) μ :=
  (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := E) (F := F)).continuous.comp_aestronglyMeasurable hB

/-- **Bounded multipliers**: `⟪B u, v⟫ = ⟪u, B* v⟫` with `B*` the fibrewise adjoint. -/
theorem inner_mulCLM {B : α → E →L[𝕜] F} {B' : α → F →L[𝕜] E} {hB : AEStronglyMeasurable B μ}
    {hB' : AEStronglyMeasurable B' μ} {C C' : ℝ} {hC : ∀ᵐ a ∂μ, ‖B a‖ ≤ C}
    {hC' : ∀ᵐ a ∂μ, ‖B' a‖ ≤ C'} (h : ∀ᵐ a ∂μ, B' a = ContinuousLinearMap.adjoint (B a))
    (u : Lp E 2 μ) (v : Lp F 2 μ) :
    ⟪mulCLM μ B hB C hC u, v⟫ = ⟪u, mulCLM μ B' hB' C' hC' v⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulCLM B hB C hC u, coeFn_mulCLM B' hB' C' hC' v, h] with a h1 h2 h3
  rw [h1, h2, h3, ContinuousLinearMap.adjoint_inner_right]

end Bounded

section Cutoff

variable {α : Type*}
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (𝕜 E) in
/-- The cut-off `𝟙_S id` (multiplication by an indicator). -/
def cutoff (S : Set α) : α → E →L[𝕜] E := S.indicator fun _ => ContinuousLinearMap.id 𝕜 E

theorem cutoff_apply_of_mem {S : Set α} {a : α} (h : a ∈ S) (x : E) : cutoff 𝕜 E S a x = x := by
  simp [cutoff, h]

theorem cutoff_apply_of_notMem {S : Set α} {a : α} (h : a ∉ S) (x : E) :
    cutoff 𝕜 E S a x = 0 := by
  simp [cutoff, h]

theorem norm_cutoff_le (S : Set α) (a : α) : ‖cutoff 𝕜 E S a‖ ≤ 1 := by
  by_cases h : a ∈ S
  · simp only [cutoff, Set.indicator_of_mem h]; exact ContinuousLinearMap.norm_id_le
  · simp [cutoff, h]

variable [MeasurableSpace α] {μ : Measure α}

theorem aestronglyMeasurable_cutoff {S : Set α} (hS : MeasurableSet S) :
    AEStronglyMeasurable (cutoff 𝕜 E S) μ :=
  (stronglyMeasurable_const.indicator hS).aestronglyMeasurable

omit [MeasurableSpace α] in
theorem norm_indicator_le {m : α → E →L[𝕜] F} {S : Set α} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a ∈ S, ‖m a‖ ≤ C) (a : α) : ‖S.indicator m a‖ ≤ C := by
  by_cases h : a ∈ S
  · rw [Set.indicator_of_mem h]; exact hb a h
  · rw [Set.indicator_of_notMem h, norm_zero]; exact hC

omit [MeasurableSpace α] in
/-- An a.e. property holding on each set of an exhausting sequence holds a.e. -/
theorem ae_of_forall_mem_cover {m0 : MeasurableSpace α} {μ : Measure α} {S : ℕ → Set α}
    (hcov : ∀ a, ∃ n, a ∈ S n) {P : α → Prop} (h : ∀ᵐ a ∂μ, ∀ n, a ∈ S n → P a) :
    ∀ᵐ a ∂μ, P a := by
  filter_upwards [h] with a ha
  obtain ⟨n, hn⟩ := hcov a
  exact ha n hn

variable (𝕜 E) in
/-- The cut-off multiplier `𝟙_S`. -/
abbrev cutoffCLM (μ : Measure α) {S : Set α} (hS : MeasurableSet S) : Lp E 2 μ →L[𝕜] Lp E 2 μ :=
  mulCLM μ (cutoff 𝕜 E S) (aestronglyMeasurable_cutoff hS) 1 (ae_of_all _ (norm_cutoff_le S))

/-- `𝟙_S` is a symmetric idempotent multiplier: `⟪𝟙_S w, w⟫ = ⟪𝟙_S w, 𝟙_S w⟫`. -/
theorem inner_cutoffCLM_self {S : Set α} (hS : MeasurableSet S) (w : Lp E 2 μ) :
    ⟪cutoffCLM 𝕜 E μ hS w, w⟫ = ⟪cutoffCLM 𝕜 E μ hS w, cutoffCLM 𝕜 E μ hS w⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulCLM (cutoff 𝕜 E S) (aestronglyMeasurable_cutoff hS) 1
    (ae_of_all _ (norm_cutoff_le S)) w] with a h
  rw [h]
  by_cases ha : a ∈ S
  · rw [cutoff_apply_of_mem ha]
  · rw [cutoff_apply_of_notMem ha, inner_zero_left, inner_zero_left]

end Cutoff

section MulOp

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable (m : α → E →L[𝕜] F)

/-- The domain `{u ∈ L² | m u ∈ L²}` of a multiplication operator. -/
def mulDomain : Submodule 𝕜 (Lp E 2 μ) where
  carrier := {u | MemLp (fun a => m a (u a)) 2 μ}
  zero_mem' := by
    change MemLp _ 2 μ
    refine (MemLp.zero (ε := F)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero E 2 μ] with a h
    rw [h]; simp
  add_mem' := by
    intro u v hu hv
    change MemLp _ 2 μ
    refine (MemLp.add hu hv).ae_eq ?_
    filter_upwards [Lp.coeFn_add u v] with a h
    rw [Pi.add_apply, ← _root_.map_add]
    exact congrArg (m a) h.symm
  smul_mem' := by
    intro r u hu
    change MemLp _ 2 μ
    refine (hu.const_smul r).ae_eq ?_
    filter_upwards [Lp.coeFn_smul r u] with a h
    rw [Pi.smul_apply, ← _root_.map_smul]
    exact congrArg (m a) h.symm

variable {μ m} in
/-- Membership in `mulDomain μ m`, by definition. -/
theorem mem_mulDomain {u : Lp E 2 μ} : u ∈ mulDomain μ m ↔ MemLp (fun a => m a (u a)) 2 μ :=
  Iff.rfl

/-- The (unbounded) multiplication operator `u ↦ (a ↦ m a (u a))` on `L²`. -/
def mulOp : Lp E 2 μ →ₗ.[𝕜] Lp F 2 μ where
  domain := mulDomain μ m
  toFun :=
    { toFun := fun u => (u.2 : MemLp (fun a => m a ((u : Lp E 2 μ) a)) 2 μ).toLp _
      map_add' := fun u v => by
        refine Lp.ext ?_
        filter_upwards [(u + v).2.coeFn_toLp, u.2.coeFn_toLp, v.2.coeFn_toLp,
          Lp.coeFn_add (u : Lp E 2 μ) v, Lp.coeFn_add (u.2.toLp _) (v.2.toLp _)]
          with a h1 h2 h3 h4 h5
        rw [h5, Pi.add_apply, h2, h3, h1, Submodule.coe_add, h4, Pi.add_apply, _root_.map_add]
      map_smul' := fun r u => by
        refine Lp.ext ?_
        filter_upwards [(r • u).2.coeFn_toLp, u.2.coeFn_toLp, Lp.coeFn_smul r (u : Lp E 2 μ),
          Lp.coeFn_smul r (u.2.toLp _)] with a h1 h2 h3 h4
        rw [RingHom.id_apply, h4, Pi.smul_apply, h2, h1, Submodule.coe_smul, h3, Pi.smul_apply,
          _root_.map_smul] }

theorem mulOp_domain : (mulOp μ m).domain = mulDomain μ m := rfl

/-- `mulOp μ m` acts fibrewise by `m a`. -/
theorem coeFn_mulOp (u : (mulOp μ m).domain) :
    mulOp μ m u =ᵐ[μ] fun a => m a ((u : Lp E 2 μ) a) :=
  (u.2 : MemLp (fun a => m a ((u : Lp E 2 μ) a)) 2 μ).coeFn_toLp

variable {μ m}

/-- `mulOp μ m u = v` iff `m u = v` a.e. -/
theorem mulOp_apply_eq_iff (u : (mulOp μ m).domain) (v : Lp F 2 μ) :
    mulOp μ m u = v ↔ ∀ᵐ a ∂μ, m a ((u : Lp E 2 μ) a) = v a := by
  constructor
  · rintro rfl
    filter_upwards [coeFn_mulOp μ m u] with a h
    exact h.symm
  · intro h
    refine Lp.ext ?_
    filter_upwards [coeFn_mulOp μ m u, h] with a h1 h2
    rw [h1, h2]

/-- **`mulOp` only depends on the symbol up to a.e. equality.** -/
theorem mulOp_congr_ae {m' : α → E →L[𝕜] F} (h : m =ᵐ[μ] m') : mulOp μ m = mulOp μ m' := by
  have hdom : mulDomain μ m = mulDomain μ m' := by
    ext u
    refine ⟨fun hu => hu.ae_eq ?_, fun hu => hu.ae_eq ?_⟩ <;>
      filter_upwards [h] with a ha <;> simp [ha]
  refine LinearPMap.ext hdom fun x hx hy => Lp.ext ?_
  filter_upwards [coeFn_mulOp μ m ⟨x, hx⟩, coeFn_mulOp μ m' ⟨x, hy⟩, h] with a h1 h2 h3
  rw [h1, h2, h3]

/-- Characterization of the graph through the truncations `𝟙_{S n} m` along an exhausting
sequence of measurable sets on which `m` is bounded. -/
theorem exists_mulOp_eq_iff {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n))
    (hcov : ∀ a, ∃ n, a ∈ S n) (hb : ∀ n, ∀ a ∈ S n, ‖m a‖ ≤ n)
    (hm : StronglyMeasurable m) (u : Lp E 2 μ) (v : Lp F 2 μ) :
    (∃ hu : u ∈ mulDomain μ m, mulOp μ m ⟨u, hu⟩ = v) ↔
      ∀ n : ℕ, mulCLM μ ((S n).indicator m) ((hm.indicator (hS n)).aestronglyMeasurable) n
          (ae_of_all _ (norm_indicator_le (Nat.cast_nonneg n) (hb n))) u =
        cutoffCLM 𝕜 F μ (hS n) v := by
  constructor
  · rintro ⟨hu, rfl⟩ n
    refine Lp.ext ?_
    filter_upwards [coeFn_mulCLM ((S n).indicator m) ((hm.indicator (hS n)).aestronglyMeasurable)
        n (ae_of_all _ (norm_indicator_le (Nat.cast_nonneg n) (hb n))) u,
      coeFn_mulCLM (cutoff 𝕜 F (S n)) (aestronglyMeasurable_cutoff (hS n)) 1
        (ae_of_all _ (norm_cutoff_le _)) (mulOp μ m ⟨u, hu⟩), coeFn_mulOp μ m ⟨u, hu⟩]
      with a h1 h2 h3
    rw [h1, h2, h3]
    by_cases ha : a ∈ S n
    · rw [Set.indicator_of_mem ha, cutoff_apply_of_mem ha]
    · rw [Set.indicator_of_notMem ha, cutoff_apply_of_notMem ha, _root_.zero_apply]
  · intro h
    have hn : ∀ n, ∀ᵐ a ∂μ, (S n).indicator m a (u a) = cutoff 𝕜 F (S n) a (v a) := fun n => by
      filter_upwards [coeFn_mulCLM ((S n).indicator m)
          ((hm.indicator (hS n)).aestronglyMeasurable) n
          (ae_of_all _ (norm_indicator_le (Nat.cast_nonneg n) (hb n))) u,
        coeFn_mulCLM (cutoff 𝕜 F (S n)) (aestronglyMeasurable_cutoff (hS n)) 1
          (ae_of_all _ (norm_cutoff_le _)) v,
        Lp.ext_iff.1 (h n)] with a h1 h2 h3
      rw [← h1, ← h2, h3]
    have hae : ∀ᵐ a ∂μ, m a (u a) = v a := by
      refine ae_of_forall_mem_cover hcov ?_
      filter_upwards [ae_all_iff.2 hn] with a ha n hmem
      have := ha n
      rwa [Set.indicator_of_mem hmem, cutoff_apply_of_mem hmem] at this
    have hu : u ∈ mulDomain μ m := (Lp.memLp v).ae_eq (hae.mono fun a h => h.symm)
    exact ⟨hu, (mulOp_apply_eq_iff ⟨u, hu⟩ v).2 hae⟩

/-- The truncation sets `{‖m‖ ≤ n}`. -/
def truncSet (m : α → E →L[𝕜] F) (n : ℕ) : Set α := {a | ‖m a‖ ≤ n}

theorem measurableSet_truncSet (hm : StronglyMeasurable m) (n : ℕ) :
    MeasurableSet (truncSet m n) :=
  hm.norm.measurable measurableSet_Iic

omit [MeasurableSpace α] in
theorem exists_mem_truncSet (a : α) : ∃ n, a ∈ truncSet m n := by
  obtain ⟨n, hn⟩ := exists_nat_ge ‖m a‖
  exact ⟨n, hn⟩

omit [MeasurableSpace α] in
theorem norm_le_of_mem_truncSet (n : ℕ) : ∀ a ∈ truncSet m n, ‖m a‖ ≤ n := fun _ h => h

/-- The bounded truncation `𝟙_{‖m‖ ≤ n} m` as a multiplier. -/
abbrev truncCLM (hm : StronglyMeasurable m) (n : ℕ) : Lp E 2 μ →L[𝕜] Lp F 2 μ :=
  mulCLM μ ((truncSet m n).indicator m)
    ((hm.indicator (measurableSet_truncSet hm n)).aestronglyMeasurable) n
    (ae_of_all _ (norm_indicator_le (Nat.cast_nonneg n) (norm_le_of_mem_truncSet n)))

/-- Multiplication operators by strongly measurable symbols are closed. -/
theorem isClosed_mulOp_of_stronglyMeasurable (hm : StronglyMeasurable m) :
    (mulOp μ m).IsClosed := by
  have hS := measurableSet_truncSet hm
  have : ((mulOp μ m).graph : Set (Lp E 2 μ × Lp F 2 μ)) =
      ⋂ n : ℕ, {p | truncCLM (μ := μ) hm n p.1 = cutoffCLM 𝕜 F μ (hS n) p.2} := by
    ext ⟨u, v⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, LinearPMap.mem_graph_iff]
    rw [← exists_mulOp_eq_iff hS exists_mem_truncSet norm_le_of_mem_truncSet hm u v]
    constructor
    · rintro ⟨y, rfl, hy⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hu, hy⟩; exact ⟨⟨u, hu⟩, rfl, hy⟩
  change IsClosed ((mulOp μ m).graph : Set (Lp E 2 μ × Lp F 2 μ))
  rw [this]
  exact isClosed_iInter fun n => isClosed_eq
    ((ContinuousLinearMap.continuous _).comp continuous_fst)
    ((ContinuousLinearMap.continuous _).comp continuous_snd)

/-- Cut-offs `𝟙_{‖m‖ ≤ n} z` lie in the domain. -/
theorem cutoffCLM_mem_mulDomain (hm : StronglyMeasurable m) (n : ℕ) (z : Lp E 2 μ) :
    cutoffCLM 𝕜 E μ (measurableSet_truncSet hm n) z ∈ mulDomain μ m := by
  refine (memLp_clm_apply ((hm.indicator (measurableSet_truncSet hm n)).aestronglyMeasurable)
    (ae_of_all _ (norm_indicator_le (Nat.cast_nonneg n) (norm_le_of_mem_truncSet n))) z).ae_eq ?_
  filter_upwards [coeFn_mulCLM (cutoff 𝕜 E (truncSet m n))
    (aestronglyMeasurable_cutoff (measurableSet_truncSet hm n)) 1
    (ae_of_all _ (norm_cutoff_le _)) z] with a h
  rw [h]
  by_cases ha : a ∈ truncSet m n
  · rw [Set.indicator_of_mem ha, cutoff_apply_of_mem ha]
  · rw [Set.indicator_of_notMem ha, cutoff_apply_of_notMem ha, _root_.zero_apply,
      _root_.map_zero]

/-- On cut-offs, `m` acts as the bounded truncation `𝟙_{‖m‖ ≤ n} m`. -/
theorem mulOp_cutoffCLM (hm : StronglyMeasurable m) (n : ℕ) (z : Lp E 2 μ) :
    mulOp μ m ⟨_, cutoffCLM_mem_mulDomain hm n z⟩ = truncCLM hm n z := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulOp μ m ⟨_, cutoffCLM_mem_mulDomain hm n z⟩,
    coeFn_mulCLM (cutoff 𝕜 E (truncSet m n))
      (aestronglyMeasurable_cutoff (measurableSet_truncSet hm n)) 1
      (ae_of_all _ (norm_cutoff_le _)) z,
    coeFn_mulCLM ((truncSet m n).indicator m)
      ((hm.indicator (measurableSet_truncSet hm n)).aestronglyMeasurable) n
      (ae_of_all _ (norm_indicator_le (Nat.cast_nonneg n) (norm_le_of_mem_truncSet n))) z]
    with a h1 h2 h3
  rw [h1, h3, h2]
  by_cases ha : a ∈ truncSet m n
  · rw [Set.indicator_of_mem ha, cutoff_apply_of_mem ha]
  · rw [Set.indicator_of_notMem ha, cutoff_apply_of_notMem ha, _root_.zero_apply,
      _root_.map_zero]

/-- Multiplication operators by strongly measurable symbols are densely defined: the
orthogonal complement of the domain is orthogonal to every cut-off. -/
theorem dense_mulDomain_of_stronglyMeasurable [CompleteSpace E] (hm : StronglyMeasurable m) :
    Dense (mulDomain μ m : Set (Lp E 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro w hw
  have hS := measurableSet_truncSet hm
  have h0 : ∀ n, cutoffCLM 𝕜 E μ (hS n) w = 0 := fun n => by
    have h := Submodule.inner_right_of_mem_orthogonal (cutoffCLM_mem_mulDomain hm n w) hw
    rw [inner_cutoffCLM_self (hS n)] at h
    exact inner_self_eq_zero.1 h
  have hn : ∀ n, ∀ᵐ a ∂μ, cutoff 𝕜 E (truncSet m n) a (w a) = 0 := fun n => by
    filter_upwards [coeFn_mulCLM (cutoff 𝕜 E (truncSet m n)) (aestronglyMeasurable_cutoff (hS n))
      1 (ae_of_all _ (norm_cutoff_le _)) w, Lp.ext_iff.1 (h0 n), Lp.coeFn_zero E 2 μ]
      with a h1 h2 h3
    rw [← h1, h2, h3]; rfl
  have hw : (w : α → E) =ᵐ[μ] 0 := by
    refine ae_of_forall_mem_cover (S := truncSet m) exists_mem_truncSet ?_
    filter_upwards [ae_all_iff.2 hn] with a ha n hmem
    have := ha n
    rwa [cutoff_apply_of_mem hmem] at this
  exact Lp.ext (hw.trans (Lp.coeFn_zero E 2 μ).symm)

variable [CompleteSpace E] [CompleteSpace F]

/-- The fibrewise-adjoint multiplier is a formal adjoint. -/
theorem mulOp_isFormalAdjoint :
    (mulOp μ m).IsFormalAdjoint (mulOp μ fun a => ContinuousLinearMap.adjoint (m a)) := by
  intro x y
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulOp μ m x, coeFn_mulOp μ (fun a => ContinuousLinearMap.adjoint (m a)) y]
    with a h1 h2
  rw [h1, h2, ContinuousLinearMap.adjoint_inner_right]

/-- The adjoint of a multiplication operator by a strongly measurable symbol. -/
theorem adjoint_mulOp_of_stronglyMeasurable (hm : StronglyMeasurable m) :
    (mulOp μ m)† = mulOp μ fun a => ContinuousLinearMap.adjoint (m a) := by
  have hd : Dense ((mulOp μ m).domain : Set (Lp E 2 μ)) := dense_mulDomain_of_stronglyMeasurable hm
  have hle := (mulOp_isFormalAdjoint (μ := μ) (m := m)).le_adjoint hd
  have hm' : StronglyMeasurable fun a => ContinuousLinearMap.adjoint (m a) :=
    (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := E) (F := F)).continuous.comp_stronglyMeasurable hm
  have hS := measurableSet_truncSet hm
  have hb' : ∀ n, ∀ a ∈ truncSet m n, ‖ContinuousLinearMap.adjoint (m a)‖ ≤ n := fun n a ha => by
    rw [LinearIsometryEquiv.norm_map]; exact ha
  have hdom :
      (mulOp μ m)†.domain ≤ (mulOp μ fun a => ContinuousLinearMap.adjoint (m a)).domain := by
    intro y hy
    have hcutadj : ∀ n, ∀ᵐ a ∂μ, cutoff 𝕜 E (truncSet m n) a =
        ContinuousLinearMap.adjoint (cutoff 𝕜 E (truncSet m n) a) := fun n =>
        ae_of_all _ fun a => by
      by_cases ha : a ∈ truncSet m n
      · simp only [cutoff, Set.indicator_of_mem ha]; exact ContinuousLinearMap.adjoint_id.symm
      · simp [cutoff, ha]
    have hindadj : ∀ n, ∀ᵐ a ∂μ, (truncSet m n).indicator
        (fun a => ContinuousLinearMap.adjoint (m a)) a =
        ContinuousLinearMap.adjoint ((truncSet m n).indicator m a) := fun n =>
      ae_of_all _ fun a => by
        by_cases ha : a ∈ truncSet m n
        · simp [ha]
        · simp [ha]
    obtain ⟨hy', -⟩ := (exists_mulOp_eq_iff hS exists_mem_truncSet hb' hm' y
      ((mulOp μ m)† ⟨y, hy⟩)).2 fun n => by
      refine ext_inner_left 𝕜 fun z => ?_
      have h1 := (LinearPMap.adjoint_isFormalAdjoint hd).symm
        ⟨_, cutoffCLM_mem_mulDomain hm n z⟩ ⟨y, hy⟩
      rw [mulOp_cutoffCLM hm n z] at h1
      calc _ = ⟪truncCLM (μ := μ) hm n z, y⟫ := (inner_mulCLM (hindadj n) z y).symm
        _ = ⟪cutoffCLM 𝕜 E μ (hS n) z, (mulOp μ m)† ⟨y, hy⟩⟫ := h1
        _ = _ := inner_mulCLM (hcutadj n) z _
    exact hy'
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

end MulOp

section AEMeasurable

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {m : α → E →L[𝕜] F}

/-- **Multiplication operators are closed.** -/
theorem isClosed_mulOp (hm : AEStronglyMeasurable m μ) : (mulOp μ m).IsClosed := by
  rw [mulOp_congr_ae hm.ae_eq_mk]
  exact isClosed_mulOp_of_stronglyMeasurable hm.stronglyMeasurable_mk

/-- **Multiplication operators are densely defined.** -/
theorem dense_mulDomain [CompleteSpace E] (hm : AEStronglyMeasurable m μ) :
    Dense (mulDomain μ m : Set (Lp E 2 μ)) := by
  rw [← mulOp_domain, mulOp_congr_ae hm.ae_eq_mk]
  exact dense_mulDomain_of_stronglyMeasurable hm.stronglyMeasurable_mk

variable [CompleteSpace E] [CompleteSpace F]

/-- **The adjoint of a multiplication operator is the multiplier by the fibrewise adjoints**,
domain included. -/
theorem adjoint_mulOp (hm : AEStronglyMeasurable m μ) :
    (mulOp μ m)† = mulOp μ fun a => ContinuousLinearMap.adjoint (m a) := by
  rw [mulOp_congr_ae hm.ae_eq_mk, adjoint_mulOp_of_stronglyMeasurable hm.stronglyMeasurable_mk]
  refine mulOp_congr_ae ?_
  filter_upwards [hm.ae_eq_mk] with a ha
  rw [ha]

/-- Membership in the adjoint domain: `y ∈ D(T*)` iff `m* y ∈ L²`. -/
theorem mem_adjoint_mulOp_domain (hm : AEStronglyMeasurable m μ) {y : Lp F 2 μ} :
    y ∈ (mulOp μ m)†.domain ↔
      MemLp (fun a => ContinuousLinearMap.adjoint (m a) (y a)) 2 μ := by
  rw [adjoint_mulOp hm]; rfl

/-- The adjoint acts fibrewise by the fibre adjoints. -/
theorem coeFn_adjoint_mulOp (hm : AEStronglyMeasurable m μ) (y : (mulOp μ m)†.domain) :
    (mulOp μ m)† y =ᵐ[μ] fun a => ContinuousLinearMap.adjoint (m a) ((y : Lp F 2 μ) a) := by
  obtain ⟨hd, hv⟩ := LinearPMap.ext_iff.1 (adjoint_mulOp hm)
  have : (mulOp μ m)† y = (mulOp μ fun a => ContinuousLinearMap.adjoint (m a)) ⟨y, hd ▸ y.2⟩ :=
    hv (x := y) (hf := y.2) (hg := hd ▸ y.2)
  rw [this]
  exact coeFn_mulOp μ _ _

/-- A multiplier by fibrewise self-adjoint operators is self-adjoint. -/
theorem adjoint_mulOp_eq_self {m : α → E →L[𝕜] E} (hm : AEStronglyMeasurable m μ)
    (hsa : ∀ᵐ a ∂μ, ContinuousLinearMap.adjoint (m a) = m a) : (mulOp μ m)† = mulOp μ m := by
  rw [adjoint_mulOp hm]; exact mulOp_congr_ae hsa

/-- A multiplier by fibrewise skew-adjoint operators is skew-adjoint. -/
theorem adjoint_mulOp_eq_neg {m : α → E →L[𝕜] E} (hm : AEStronglyMeasurable m μ)
    (hsk : ∀ᵐ a ∂μ, ContinuousLinearMap.adjoint (m a) = -m a) : (mulOp μ m)† = -mulOp μ m := by
  rw [adjoint_mulOp hm, mulOp_congr_ae hsk]
  refine LinearPMap.ext ?_ fun x hx hy => ?_
  · ext u
    change MemLp _ 2 μ ↔ MemLp _ 2 μ
    simp only [_root_.neg_apply]
    exact memLp_neg_iff
  · refine Lp.ext ?_
    have hy' : x ∈ mulDomain μ m := hy
    filter_upwards [coeFn_mulOp μ (fun a => -m a) ⟨x, hx⟩, Lp.coeFn_neg (mulOp μ m ⟨x, hy'⟩),
      coeFn_mulOp μ m ⟨x, hy'⟩] with a h1 h2 h3
    rw [h1, LinearPMap.neg_apply]
    change _ = (-(mulOp μ m ⟨x, hy'⟩) : Lp E 2 μ) a
    rw [h2, Pi.neg_apply, h3]
    rfl

end AEMeasurable

section Fibre

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (μ) in
/-- The fibrewise subspace `{u ∈ L² | u a ∈ K a for a.e. a}`. -/
def fibreSub (K : α → Submodule 𝕜 E) : Submodule 𝕜 (Lp E 2 μ) where
  carrier := {u | ∀ᵐ a ∂μ, u a ∈ K a}
  zero_mem' := by
    change ∀ᵐ a ∂μ, _
    filter_upwards [Lp.coeFn_zero E 2 μ] with a h
    rw [h]; exact (K a).zero_mem
  add_mem' := by
    intro u v hu hv
    change ∀ᵐ a ∂μ, _
    filter_upwards [hu, hv, Lp.coeFn_add u v] with a h1 h2 h3
    rw [h3]; exact (K a).add_mem h1 h2
  smul_mem' := by
    intro r u hu
    change ∀ᵐ a ∂μ, _
    filter_upwards [hu, Lp.coeFn_smul r u] with a h1 h2
    rw [h2]; exact (K a).smul_mem r h1

/-- Membership in `fibreSub μ K`, by definition. -/
theorem mem_fibreSub {K : α → Submodule 𝕜 E} {u : Lp E 2 μ} :
    u ∈ fibreSub μ K ↔ ∀ᵐ a ∂μ, u a ∈ K a := Iff.rfl

variable (K : α → Submodule 𝕜 E) [∀ a, (K a).HasOrthogonalProjection]
  (hP : AEStronglyMeasurable (fun a => (K a).starProjection) μ)

/-- The fibrewise projection `u ↦ (a ↦ P_{K a} (u a))`, a bounded multiplier. -/
def fibreProj : Lp E 2 μ →L[𝕜] Lp E 2 μ :=
  mulCLM μ (fun a => (K a).starProjection) hP 1 (ae_of_all _ fun a => (K a).starProjection_norm_le)

theorem coeFn_fibreProj (u : Lp E 2 μ) :
    fibreProj K hP u =ᵐ[μ] fun a => (K a).starProjection (u a) :=
  coeFn_mulCLM _ hP 1 _ u

theorem fibreProj_mem (u : Lp E 2 μ) : fibreProj K hP u ∈ fibreSub μ K := by
  filter_upwards [coeFn_fibreProj K hP u] with a h
  rw [h]; exact (K a).starProjection_apply_mem _

theorem mem_fibreSub_iff_fibreProj {u : Lp E 2 μ} :
    u ∈ fibreSub μ K ↔ fibreProj K hP u = u := by
  constructor
  · intro hu
    refine Lp.ext ?_
    filter_upwards [coeFn_fibreProj K hP u, hu] with a h1 h2
    rw [h1, (K a).starProjection_eq_self_iff.2 h2]
  · intro hu
    have := Lp.ext_iff.1 hu
    filter_upwards [coeFn_fibreProj K hP u, this] with a h1 h2
    rw [← (K a).starProjection_eq_self_iff, ← h1, h2]

include hP in
/-- Fibrewise subspaces with measurable fibre projections are closed. -/
theorem isClosed_fibreSub : IsClosed (fibreSub μ K : Set (Lp E 2 μ)) := by
  have : (fibreSub μ K : Set (Lp E 2 μ)) = {u | fibreProj K hP u = u} := by
    ext u; exact mem_fibreSub_iff_fibreProj K hP
  rw [this]
  exact isClosed_eq (ContinuousLinearMap.continuous _) continuous_id

variable [CompleteSpace E]

include hP in
/-- Fibrewise subspaces admit orthogonal projections. -/
theorem hasOrthogonalProjection_fibreSub : (fibreSub μ K).HasOrthogonalProjection := by
  have : CompleteSpace (fibreSub μ K) := (isClosed_fibreSub K hP).completeSpace_coe
  infer_instance

omit [CompleteSpace E] in
/-- **The orthogonal projection onto a fibrewise subspace acts fibrewise.** -/
theorem starProjection_fibreSub [(fibreSub μ K).HasOrthogonalProjection] (u : Lp E 2 μ) :
    (fibreSub μ K).starProjection u = fibreProj K hP u := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (fibreProj_mem K hP u)
    fun w hw => ?_
  rw [L2.inner_def]
  refine (integral_congr_ae ?_).trans (integral_zero α 𝕜)
  filter_upwards [Lp.coeFn_sub u (fibreProj K hP u), coeFn_fibreProj K hP u, hw] with a h1 h2 h3
  rw [h1, Pi.sub_apply, h2]
  exact (K a).starProjection_inner_eq_zero _ _ h3

omit [CompleteSpace E] in
include hP in
/-- Pointwise form of `starProjection_fibreSub`. -/
theorem coeFn_starProjection_fibreSub [(fibreSub μ K).HasOrthogonalProjection]
    (u : Lp E 2 μ) :
    (fibreSub μ K).starProjection u =ᵐ[μ] fun a => (K a).starProjection (u a) := by
  rw [starProjection_fibreSub K hP]; exact coeFn_fibreProj K hP u

end Fibre

/-! ### The counting measure: `ℓ²` multipliers -/

section Count

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable (m : α → E →L[𝕜] F)

/-- For the counting measure, the domain is the weighted-`ℓ²` condition. -/
theorem mem_mulDomain_count_iff {u : Lp E 2 (Measure.count : Measure α)} :
    u ∈ mulDomain Measure.count m ↔ Memℓp (fun a => m a (u a)) 2 :=
  memLp_count_iff two_ne_zero

omit [MeasurableSingletonClass α] [Countable α] in
/-- For the counting measure, `mulOp` acts pointwise, everywhere. -/
theorem coeFn_mulOp_count (u : (mulOp Measure.count m).domain) (a : α) :
    (mulOp (Measure.count : Measure α) m u : α → F) a = m a ((u : Lp E 2 Measure.count) a) :=
  Measure.ae_count_iff.1 (coeFn_mulOp Measure.count m u) a

/-- `ℓ²` form of the domain: `u ∈ ℓ²` is in the domain iff `(m a (u a))ₐ ∈ ℓ²`. -/
theorem equivLpCount_mem_mulDomain_iff (u : lp (fun _ : α => E) 2) :
    lp.equivLpCount 𝕜 α E 2 u ∈ mulDomain Measure.count m ↔ Memℓp (fun a => m a (u a)) 2 := by
  rw [mem_mulDomain_count_iff, lp.coeFn_equivLpCount]

/-- `ℓ²` form of the action: `mulOp` transported to `ℓ²` is `u ↦ (m a (u a))ₐ`. -/
theorem mulOp_equivLpCount (u : lp (fun _ : α => E) 2)
    (hu : lp.equivLpCount 𝕜 α E 2 u ∈ mulDomain Measure.count m) :
    (lp.equivLpCount 𝕜 α F 2).symm (mulOp Measure.count m ⟨_, hu⟩) =
      ⟨fun a => m a (u a), (equivLpCount_mem_mulDomain_iff m u).1 hu⟩ := by
  ext a
  rw [lp.equivLpCount_symm_apply, coeFn_mulOp_count]
  change m a ((lp.equivLpCount 𝕜 α E 2 u : α → E) a) = m a (u a)
  rw [lp.coeFn_equivLpCount]

/-- **`ℓ²` multipliers are closed** (no measurability hypothesis). -/
theorem isClosed_mulOp_count : (mulOp (Measure.count : Measure α) m).IsClosed :=
  isClosed_mulOp AEStronglyMeasurable.of_discrete

/-- **`ℓ²` multipliers are densely defined.** -/
theorem dense_mulDomain_count [CompleteSpace E] :
    Dense ((mulDomain (Measure.count : Measure α) m : Submodule 𝕜 (Lp E 2 Measure.count)) :
      Set (Lp E 2 (Measure.count : Measure α))) :=
  dense_mulDomain AEStronglyMeasurable.of_discrete

/-- **The adjoint of an `ℓ²` multiplier** is the multiplier by the fibre adjoints. -/
theorem adjoint_mulOp_count [CompleteSpace E] [CompleteSpace F] :
    (mulOp (Measure.count : Measure α) m)† =
      mulOp Measure.count fun a => ContinuousLinearMap.adjoint (m a) :=
  adjoint_mulOp AEStronglyMeasurable.of_discrete

end Count

/-! ### Measurable dependence of kernel projections -/

section MeasurableProj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- On a finite-dimensional source, a family of operators is strongly measurable as soon as all
its applications are. -/
theorem stronglyMeasurable_clm_of_apply {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] {β : Type*} [MeasurableSpace β] {f : β → E →L[𝕜] F}
    (h : ∀ x, StronglyMeasurable fun b => f b x) : StronglyMeasurable f := by
  let b := Module.finBasis 𝕜 E
  have hf : f = fun c => ∑ i, ContinuousLinearMap.smulRight
      (LinearMap.toContinuousLinearMap (b.coord i)) (f c (b i)) := by
    funext c
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr x]
    rw [_root_.map_sum]
    simp [_root_.map_smul]
  rw [hf]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL 𝕜 E F
    (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_stronglyMeasurable (h (b i))

section Resolvent

variable (H : E →L[𝕜] E) (hsym : ∀ x y, inner 𝕜 (H x) y = inner 𝕜 x (H y))
  (hpos : ∀ x, 0 ≤ RCLike.re (inner 𝕜 (H x) x))
include hpos

omit [FiniteDimensional 𝕜 E] in
/-- `ε ‖v‖ ≤ ‖(ε + H) v‖` for a positive operator `H` and `ε ≥ 0`. -/
theorem mul_norm_le_norm_smul_one_add_apply (ε : ℝ) (v : E) :
    ε * ‖v‖ ≤ ‖((ε : 𝕜) • (1 : E →L[𝕜] E) + H) v‖ := by
  have h1 : ε * ‖v‖ ^ 2 ≤ RCLike.re ⟪((ε : 𝕜) • (1 : E →L[𝕜] E) + H) v, v⟫ := by
    rw [_root_.add_apply, inner_add_left, _root_.smul_apply, one_apply_eq_self, inner_smul_left,
      RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K, _root_.map_add, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul, RCLike.ofReal_re]
    linarith [hpos v]
  have h2 : RCLike.re ⟪((ε : 𝕜) • (1 : E →L[𝕜] E) + H) v, v⟫ ≤
      ‖((ε : 𝕜) • (1 : E →L[𝕜] E) + H) v‖ * ‖v‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg v).eq_or_lt with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right (by nlinarith) h

/-- `ε + H` is invertible for a positive operator `H` and `ε > 0`. -/
theorem isUnit_smul_one_add {ε : ℝ} (hε : 0 < ε) : IsUnit ((ε : 𝕜) • (1 : E →L[𝕜] E) + H) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hinj : Function.Injective ((ε : 𝕜) • (1 : E →L[𝕜] E) + H) := by
    rw [← ((ε : 𝕜) • (1 : E →L[𝕜] E) + H).coe_coe, ← LinearMap.ker_eq_bot,
      LinearMap.ker_eq_bot']
    intro v hv
    have := mul_norm_le_norm_smul_one_add_apply H hpos ε v
    rw [ContinuousLinearMap.coe_coe] at hv
    rw [hv, norm_zero] at this
    exact norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg v]) (norm_nonneg v))
  refine ContinuousLinearMap.isUnit_iff_bijective.2 ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective
    (f := (((ε : 𝕜) • (1 : E →L[𝕜] E) + H : E →L[𝕜] E) : E →ₗ[𝕜] E))).1 hinj

omit hpos in
include hsym in
/-- For a symmetric operator, `(ker H)ᗮ ⊆ range H`. -/
theorem orthogonal_ker_le_range_of_symm :
    (LinearMap.ker (H : E →ₗ[𝕜] E))ᗮ ≤ LinearMap.range (H : E →ₗ[𝕜] E) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hadj : ContinuousLinearMap.adjoint H = H :=
    ((ContinuousLinearMap.eq_adjoint_iff H H).2 hsym).symm
  have h := ContinuousLinearMap.orthogonal_range H
  rw [hadj] at h
  rw [← h, Submodule.orthogonal_orthogonal]

include hsym in
/-- **Resolvent limit**: `ε (ε + H)⁻¹ x → P_{ker H} x` as `ε = 1/(n+1) → 0`, for a positive
symmetric operator `H` on a finite-dimensional space. -/
theorem tendsto_smul_inverse_smul_one_add (x : E) :
    Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : 𝕜) •
        Ring.inverse (((1 / ((n : ℝ) + 1) : ℝ) : 𝕜) • (1 : E →L[𝕜] E) + H) x) atTop
      (𝓝 ((LinearMap.ker (H : E →ₗ[𝕜] E)).starProjection x)) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set K := LinearMap.ker (H : E →ₗ[𝕜] E)
  set k := K.starProjection x
  obtain ⟨z, hz⟩ := orthogonal_ker_le_range_of_symm H hsym (K.sub_starProjection_mem_orthogonal x)
  have hk : H k = 0 := LinearMap.mem_ker.1 (K.starProjection_apply_mem x)
  have hz' : H z = x - k := hz
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(ε : 𝕜) • Ring.inverse ((ε : 𝕜) • (1 : E →L[𝕜] E) + H) x - k‖ ≤ 2 * ε * ‖z‖ := by
    intro ε hε
    set A := (ε : 𝕜) • (1 : E →L[𝕜] E) + H
    have hA := isUnit_smul_one_add H hpos hε
    have hAR : ∀ w, A (Ring.inverse A w) = w := fun w => by
      rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel A hA, one_apply_eq_self]
    set y := (ε : 𝕜) • Ring.inverse A x
    have hy : A y = (ε : 𝕜) • x := by rw [_root_.map_smul, hAR]
    have hAk : A (k + (ε : 𝕜) • z) = (ε : 𝕜) • x + ((ε : 𝕜) * ε) • z := by
      simp only [A, _root_.add_apply, _root_.smul_apply, one_apply_eq_self, _root_.map_add,
        _root_.map_smul, hk, hz']
      simp only [smul_add, smul_sub, mul_smul]; abel
    have hdiff : A (y - (k + (ε : 𝕜) • z)) = -(((ε : 𝕜) * ε) • z) := by
      rw [_root_.map_sub, hy, hAk]; abel
    have h1 := mul_norm_le_norm_smul_one_add_apply H hpos ε (y - (k + (ε : 𝕜) • z))
    rw [hdiff, norm_neg, norm_smul, ← RCLike.ofReal_mul, RCLike.norm_ofReal,
      abs_of_nonneg (by positivity)] at h1
    have h2 : ‖y - (k + (ε : 𝕜) • z)‖ ≤ ε * ‖z‖ := by
      have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hε.le)
      rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul, ← mul_assoc, ← mul_assoc,
        inv_mul_cancel₀ hε.ne', one_mul] at this
      exact this
    calc ‖y - k‖ = ‖(y - (k + (ε : 𝕜) • z)) + (ε : 𝕜) • z‖ := by congr 1; abel
      _ ≤ ‖y - (k + (ε : 𝕜) • z)‖ + ‖(ε : 𝕜) • z‖ := norm_add_le _ _
      _ ≤ ε * ‖z‖ + ε * ‖z‖ := by
          rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hε.le]; linarith
      _ = 2 * ε * ‖z‖ := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) * ‖z‖) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
    simpa using this.mul_const ‖z‖
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => key _ (by positivity)) hlim

end Resolvent

/-- **Measurable dependence of kernel projections.** For a continuous family `H b` of positive
symmetric operators on a finite-dimensional space, `b ↦ P_{ker H b}` is strongly measurable
(though in general discontinuous): it is the pointwise limit of the continuous resolvents
`ε (ε + H b)⁻¹` (`tendsto_smul_inverse_smul_one_add`). -/
theorem stronglyMeasurable_starProjection_ker {β : Type*} [TopologicalSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {H : β → E →L[𝕜] E} (hH : Continuous H)
    (hsym : ∀ b x y, ⟪H b x, y⟫ = ⟪x, H b y⟫) (hpos : ∀ b x, 0 ≤ RCLike.re ⟪H b x, x⟫) :
    StronglyMeasurable fun b => (LinearMap.ker (H b : E →ₗ[𝕜] E)).starProjection := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  refine stronglyMeasurable_clm_of_apply fun x => ?_
  have hcont : ∀ n : ℕ, Continuous fun b => ((1 / ((n : ℝ) + 1) : ℝ) : 𝕜) •
      Ring.inverse (((1 / ((n : ℝ) + 1) : ℝ) : 𝕜) • (1 : E →L[𝕜] E) + H b) x := fun n => by
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine continuous_const.smul ?_
    refine Continuous.clm_apply ?_ continuous_const
    refine continuous_iff_continuousAt.2 fun b => ?_
    have hu := isUnit_smul_one_add (H b) (hpos b) hε
    have := NormedRing.inverse_continuousAt hu.unit
    rw [IsUnit.unit_spec] at this
    exact this.comp (f := fun b => ((1 / ((n : ℝ) + 1) : ℝ) : 𝕜) • (1 : E →L[𝕜] E) + H b)
      (continuous_const.add hH).continuousAt
  exact stronglyMeasurable_of_tendsto atTop (fun n => (hcont n).stronglyMeasurable)
    (tendsto_pi_nhds.2 fun b => tendsto_smul_inverse_smul_one_add (H b) (hsym b) (hpos b) x)

end MeasurableProj

end Feec.Operator
