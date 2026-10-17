module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# Multiplication operators on `L²(μ; E)`

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

The `L²` counterpart of the `ℓ²` multiplier machinery of `Feec.Legacy.Torus.Basic` (`Feec.Legacy.Torus.mulOp`,
`Feec.Legacy.Torus.fibreSub`), for an arbitrary measure space `(α, μ)` and real inner product fibres.
It is the operator theory behind the whole-space model `Feec.Legacy.Whole.Basic`, where `α = ℝ³` is the
frequency space and the operators are Fourier multipliers.

## Main results

* `bmul`: the bounded multiplier `u ↦ (a ↦ B a (u a))` by a strongly measurable, uniformly
  bounded family `B : α → E →L[ℝ] F`, with `coeFn_bmul`, `norm_bmul_le`, `inner_bmul`
  (`⟪B u, v⟫ = ⟪u, B* v⟫`).
* `mulOp m`: the (unbounded) multiplier by a strongly measurable family
  `m : α → E →L[ℝ] F`, with domain `mulDomain m = {u | m u ∈ L²}`. It is closed
  (`isClosed_mulOp`), densely defined (`dense_mulDomain`), and its adjoint is the multiplier by
  the fibrewise adjoints, *domain included* (`adjoint_mulOp`). The proofs use the truncations
  `𝟙_{‖m‖ ≤ n} m` (bounded multipliers) and the exhaustion `⋃ₙ {‖m‖ ≤ n} = α`.
* `fibreSub K`: the fibrewise subspace `{u | u a ∈ K a a.e.}` for a family of subspaces whose
  orthogonal projections depend measurably on `a`; it is closed (`isClosed_fibreSub`) and its
  orthogonal projection is the fibrewise projection (`starProjection_fibreSub`).
* Measurable dependence of kernel projections: for a continuous family `H a` of positive
  symmetric operators on a finite-dimensional space, `a ↦ P_{ker H a}` is strongly measurable
  (`stronglyMeasurable_starProjection_ker`). The proof is the resolvent limit
  `ε (ε + H)⁻¹ x → P_{ker H} x` as `ε → 0⁺` (`tendsto_resolvent`), each resolvent being
  continuous in `a`. This is what makes the TSD projection `P_ξ` (which is discontinuous at
  `ξ = 0`) act as a bounded multiplier on `L²(ℝ³)`.

## References

* [Kato1995] (closed operators and their adjoints; multiplication operators are the standard
  example)
* [QuennevilleBelair2015], §4.10 (the TSD projection `P_{L²(TSD)}` whose fibrewise action is
  formalized here)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology
open MeasureTheory LinearPMap Set Filter

namespace Feec.Legacy.Whole

section Bounded

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `a ↦ B a (u a)` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_apply {B : α → E →L[ℝ] F} (hB : AEStronglyMeasurable B μ)
    {u : α → E} (hu : AEStronglyMeasurable u μ) : AEStronglyMeasurable (fun a => B a (u a)) μ :=
  isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hB hu

/-- A uniformly bounded measurable family maps `L²` into `L²`. -/
theorem memLp_apply {B : α → E →L[ℝ] F} (hB : AEStronglyMeasurable B μ) {C : ℝ}
    (hC : ∀ a, ‖B a‖ ≤ C) (u : Lp E 2 μ) : MemLp (fun a => B a (u a)) 2 μ :=
  MemLp.of_le_mul (Lp.memLp u) (aestronglyMeasurable_apply hB (Lp.aestronglyMeasurable u))
    (Eventually.of_forall fun a => (B a).le_of_opNorm_le (hC a) _)

variable (μ) in
/-- The bounded multiplier `u ↦ (a ↦ B a (u a))` on `L²`. -/
def bmul (B : α → E →L[ℝ] F) (hB : AEStronglyMeasurable B μ) (C : ℝ) (hC : ∀ a, ‖B a‖ ≤ C) :
    Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_apply hB hC u).toLp _
      map_add' := fun u v => by
        refine Lp.ext ?_
        filter_upwards [(memLp_apply hB hC (u + v)).coeFn_toLp, (memLp_apply hB hC u).coeFn_toLp,
          (memLp_apply hB hC v).coeFn_toLp, Lp.coeFn_add u v,
          Lp.coeFn_add ((memLp_apply hB hC u).toLp _) ((memLp_apply hB hC v).toLp _)]
          with a h1 h2 h3 h4 h5
        rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply, _root_.map_add]
      map_smul' := fun r u => by
        refine Lp.ext ?_
        filter_upwards [(memLp_apply hB hC (r • u)).coeFn_toLp, (memLp_apply hB hC u).coeFn_toLp,
          Lp.coeFn_smul r u, Lp.coeFn_smul r ((memLp_apply hB hC u).toLp _)]
          with a h1 h2 h3 h4
        rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply, _root_.map_smul] }
    C fun u => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_apply hB hC u).coeFn_toLp] with a h
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h]
      exact (B a).le_of_opNorm_le (hC a) _

theorem coeFn_bmul (B : α → E →L[ℝ] F) (hB : AEStronglyMeasurable B μ) (C : ℝ)
    (hC : ∀ a, ‖B a‖ ≤ C) (u : Lp E 2 μ) :
    bmul μ B hB C hC u =ᵐ[μ] fun a => B a (u a) :=
  (memLp_apply hB hC u).coeFn_toLp

variable [CompleteSpace E] [CompleteSpace F]

/-- The fibrewise adjoint family of a measurable family is measurable. -/
theorem aestronglyMeasurable_adjoint {B : α → E →L[ℝ] F} (hB : AEStronglyMeasurable B μ) :
    AEStronglyMeasurable (fun a => ContinuousLinearMap.adjoint (B a)) μ :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous.comp_aestronglyMeasurable hB

/-- **Bounded multipliers**: `⟪B u, v⟫ = ⟪u, B* v⟫` with `B*` the fibrewise adjoint. -/
theorem inner_bmul {B : α → E →L[ℝ] F} {B' : α → F →L[ℝ] E} {hB : AEStronglyMeasurable B μ}
    {hB' : AEStronglyMeasurable B' μ} {C C' : ℝ} {hC : ∀ a, ‖B a‖ ≤ C} {hC' : ∀ a, ‖B' a‖ ≤ C'}
    (h : ∀ a, B' a = ContinuousLinearMap.adjoint (B a)) (u : Lp E 2 μ) (v : Lp F 2 μ) :
    ⟪bmul μ B hB C hC u, v⟫ = ⟪u, bmul μ B' hB' C' hC' v⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bmul B hB C hC u, coeFn_bmul B' hB' C' hC' v] with a h1 h2
  rw [h1, h2, h a, ContinuousLinearMap.adjoint_inner_right]

end Bounded

section Cut

variable {α : Type*}
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable (E) in
/-- The cut-off `𝟙_S id` (multiplication by an indicator). -/
def cut (S : Set α) : α → E →L[ℝ] E := S.indicator fun _ => ContinuousLinearMap.id ℝ E

theorem cut_apply_of_mem {S : Set α} {a : α} (h : a ∈ S) (x : E) : cut E S a x = x := by
  simp [cut, h]

theorem cut_apply_of_not_mem {S : Set α} {a : α} (h : a ∉ S) (x : E) : cut E S a x = 0 := by
  simp [cut, h]

theorem norm_cut_le (S : Set α) (a : α) : ‖cut E S a‖ ≤ 1 := by
  by_cases h : a ∈ S
  · simp only [cut, Set.indicator_of_mem h]; exact ContinuousLinearMap.norm_id_le
  · simp [cut, h]

variable [MeasurableSpace α] {μ : Measure α}

theorem aestronglyMeasurable_cut {S : Set α} (hS : MeasurableSet S) :
    AEStronglyMeasurable (cut E S) μ :=
  (stronglyMeasurable_const.indicator hS).aestronglyMeasurable

omit [MeasurableSpace α] in
theorem norm_indicator_le {m : α → E →L[ℝ] F} {S : Set α} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a ∈ S, ‖m a‖ ≤ C) (a : α) : ‖S.indicator m a‖ ≤ C := by
  by_cases h : a ∈ S
  · rw [Set.indicator_of_mem h]; exact hb a h
  · rw [Set.indicator_of_notMem h, norm_zero]; exact hC

/-- An a.e. property holding on each set of an exhausting sequence holds a.e. -/
theorem ae_of_cover {S : ℕ → Set α} (hcov : ∀ a, ∃ n, a ∈ S n) {P : α → Prop}
    (h : ∀ᵐ a ∂μ, ∀ n, a ∈ S n → P a) : ∀ᵐ a ∂μ, P a := by
  filter_upwards [h] with a ha
  obtain ⟨n, hn⟩ := hcov a
  exact ha n hn

/-- `𝟙_S` is a symmetric bounded multiplier. -/
theorem inner_bmul_cut_self {S : Set α} (hS : MeasurableSet S) (w : Lp E 2 μ) :
    ⟪bmul μ (cut E S) (aestronglyMeasurable_cut hS) 1 (norm_cut_le S) w, w⟫ =
      ⟪bmul μ (cut E S) (aestronglyMeasurable_cut hS) 1 (norm_cut_le S) w,
        bmul μ (cut E S) (aestronglyMeasurable_cut hS) 1 (norm_cut_le S) w⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bmul (cut E S) (aestronglyMeasurable_cut hS) 1 (norm_cut_le S) w]
    with a h
  rw [h]
  by_cases ha : a ∈ S
  · rw [cut_apply_of_mem ha]
  · rw [cut_apply_of_not_mem ha, inner_zero_left, inner_zero_left]

end Cut

section MulOp

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (m : α → E →L[ℝ] F)

/-- The domain `{u ∈ L² | m u ∈ L²}` of a multiplication operator. -/
def mulDomain : Submodule ℝ (Lp E 2 μ) where
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

/-- The (unbounded) multiplication operator `u ↦ (a ↦ m a (u a))` on `L²`. -/
def mulOp : Lp E 2 μ →ₗ.[ℝ] Lp F 2 μ where
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

/-- `mulOp μ m` acts fibrewise by `m a`. -/
theorem coeFn_mulOp (u : (mulOp μ m).domain) :
    mulOp μ m u =ᵐ[μ] fun a => m a ((u : Lp E 2 μ) a) :=
  (u.2 : MemLp (fun a => m a ((u : Lp E 2 μ) a)) 2 μ).coeFn_toLp

variable {μ m}

/-- Characterization of the graph through the truncations `𝟙_{S n} m` along an exhausting
sequence of measurable sets on which `m` is bounded. -/
theorem graph_iff_trunc {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n))
    (hcov : ∀ a, ∃ n, a ∈ S n) (hb : ∀ n, ∀ a ∈ S n, ‖m a‖ ≤ n)
    (hm : StronglyMeasurable m) (u : Lp E 2 μ) (v : Lp F 2 μ) :
    (∃ hu : u ∈ mulDomain μ m, mulOp μ m ⟨u, hu⟩ = v) ↔
      ∀ n : ℕ, bmul μ ((S n).indicator m) ((hm.indicator (hS n)).aestronglyMeasurable) n
          (norm_indicator_le (Nat.cast_nonneg n) (hb n)) u =
        bmul μ (cut F (S n)) (aestronglyMeasurable_cut (hS n)) 1 (norm_cut_le _) v := by
  constructor
  · rintro ⟨hu, rfl⟩ n
    refine Lp.ext ?_
    filter_upwards [coeFn_bmul ((S n).indicator m) ((hm.indicator (hS n)).aestronglyMeasurable)
        n (norm_indicator_le (Nat.cast_nonneg n) (hb n)) u,
      coeFn_bmul (cut F (S n)) (aestronglyMeasurable_cut (hS n)) 1 (norm_cut_le _)
        (mulOp μ m ⟨u, hu⟩), coeFn_mulOp μ m ⟨u, hu⟩] with a h1 h2 h3
    rw [h1, h2, h3]
    by_cases ha : a ∈ S n
    · rw [Set.indicator_of_mem ha, cut_apply_of_mem ha]
    · rw [Set.indicator_of_notMem ha, cut_apply_of_not_mem ha, _root_.zero_apply]
  · intro h
    have hn : ∀ n, ∀ᵐ a ∂μ, (S n).indicator m a (u a) = cut F (S n) a (v a) := fun n => by
      filter_upwards [coeFn_bmul ((S n).indicator m) ((hm.indicator (hS n)).aestronglyMeasurable)
          n (norm_indicator_le (Nat.cast_nonneg n) (hb n)) u,
        coeFn_bmul (cut F (S n)) (aestronglyMeasurable_cut (hS n)) 1 (norm_cut_le _) v,
        Lp.ext_iff.1 (h n)] with a h1 h2 h3
      rw [← h1, ← h2, h3]
    have hae : ∀ᵐ a ∂μ, m a (u a) = v a := by
      refine ae_of_cover hcov ?_
      filter_upwards [ae_all_iff.2 hn] with a ha n hmem
      have := ha n
      rwa [Set.indicator_of_mem hmem, cut_apply_of_mem hmem] at this
    have hu : u ∈ mulDomain μ m := (Lp.memLp v).ae_eq (hae.mono fun a h => h.symm)
    refine ⟨hu, Lp.ext ?_⟩
    filter_upwards [coeFn_mulOp μ m ⟨u, hu⟩, hae] with a h1 h2
    rw [h1, ← h2]

/-- The truncation sets `{‖m‖ ≤ n}`. -/
def truncSet (m : α → E →L[ℝ] F) (n : ℕ) : Set α := {a | ‖m a‖ ≤ n}

theorem measurableSet_truncSet (hm : StronglyMeasurable m) (n : ℕ) :
    MeasurableSet (truncSet m n) :=
  hm.norm.measurable measurableSet_Iic

omit [MeasurableSpace α] in
theorem exists_mem_truncSet (a : α) : ∃ n, a ∈ truncSet m n := by
  obtain ⟨n, hn⟩ := exists_nat_ge ‖m a‖
  exact ⟨n, hn⟩

omit [MeasurableSpace α] in
theorem norm_le_of_mem_truncSet (n : ℕ) : ∀ a ∈ truncSet m n, ‖m a‖ ≤ n := fun _ h => h

/-- **Multiplication operators are closed.** -/
theorem isClosed_mulOp (hm : StronglyMeasurable m) : (mulOp μ m).IsClosed := by
  have hS := measurableSet_truncSet hm
  have : ((mulOp μ m).graph : Set (Lp E 2 μ × Lp F 2 μ)) =
      ⋂ n : ℕ, {p | bmul μ ((truncSet m n).indicator m) ((hm.indicator (hS n)).aestronglyMeasurable)
          n (norm_indicator_le (Nat.cast_nonneg n) (norm_le_of_mem_truncSet n)) p.1 =
        bmul μ (cut F (truncSet m n)) (aestronglyMeasurable_cut (hS n)) 1 (norm_cut_le _) p.2} := by
    ext ⟨u, v⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, LinearPMap.mem_graph_iff]
    rw [← graph_iff_trunc hS exists_mem_truncSet norm_le_of_mem_truncSet hm u v]
    constructor
    · rintro ⟨y, rfl, hy⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hu, hy⟩; exact ⟨⟨u, hu⟩, rfl, hy⟩
  change IsClosed ((mulOp μ m).graph : Set (Lp E 2 μ × Lp F 2 μ))
  rw [this]
  exact isClosed_iInter fun n => isClosed_eq
    ((ContinuousLinearMap.continuous _).comp continuous_fst)
    ((ContinuousLinearMap.continuous _).comp continuous_snd)

/-- Cut-offs `𝟙_{‖m‖ ≤ n} z` lie in the domain. -/
theorem bmul_cut_mem_mulDomain (hm : StronglyMeasurable m) (n : ℕ) (z : Lp E 2 μ) :
    bmul μ (cut E (truncSet m n)) (aestronglyMeasurable_cut (measurableSet_truncSet hm n)) 1
      (norm_cut_le _) z ∈ mulDomain μ m := by
  refine (memLp_apply ((hm.indicator (measurableSet_truncSet hm n)).aestronglyMeasurable)
    (norm_indicator_le (Nat.cast_nonneg n) (norm_le_of_mem_truncSet n)) z).ae_eq ?_
  filter_upwards [coeFn_bmul (cut E (truncSet m n))
    (aestronglyMeasurable_cut (measurableSet_truncSet hm n)) 1 (norm_cut_le _) z] with a h
  rw [h]
  by_cases ha : a ∈ truncSet m n
  · rw [Set.indicator_of_mem ha, cut_apply_of_mem ha]
  · rw [Set.indicator_of_notMem ha, cut_apply_of_not_mem ha, _root_.zero_apply,
      _root_.map_zero]

/-- On cut-offs, `m` acts as the bounded truncation `𝟙_{‖m‖ ≤ n} m`. -/
theorem mulOp_bmul_cut (hm : StronglyMeasurable m) (n : ℕ) (z : Lp E 2 μ) :
    mulOp μ m ⟨_, bmul_cut_mem_mulDomain hm n z⟩ =
      bmul μ ((truncSet m n).indicator m)
        ((hm.indicator (measurableSet_truncSet hm n)).aestronglyMeasurable) n
        (norm_indicator_le (Nat.cast_nonneg n) (norm_le_of_mem_truncSet n)) z := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulOp μ m ⟨_, bmul_cut_mem_mulDomain hm n z⟩,
    coeFn_bmul (cut E (truncSet m n)) (aestronglyMeasurable_cut (measurableSet_truncSet hm n)) 1
      (norm_cut_le _) z,
    coeFn_bmul ((truncSet m n).indicator m)
      ((hm.indicator (measurableSet_truncSet hm n)).aestronglyMeasurable) n
      (norm_indicator_le (Nat.cast_nonneg n) (norm_le_of_mem_truncSet n)) z] with a h1 h2 h3
  rw [h1, h3, h2]
  by_cases ha : a ∈ truncSet m n
  · rw [Set.indicator_of_mem ha, cut_apply_of_mem ha]
  · rw [Set.indicator_of_notMem ha, cut_apply_of_not_mem ha, _root_.zero_apply,
      _root_.map_zero]

variable [CompleteSpace E]

/-- **Multiplication operators are densely defined**: the orthogonal complement of the domain
is trivial, since it is orthogonal to every cut-off. -/
theorem dense_mulDomain (hm : StronglyMeasurable m) : Dense (mulDomain μ m : Set (Lp E 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro w hw
  have hS := measurableSet_truncSet hm
  have h0 : ∀ n, bmul μ (cut E (truncSet m n)) (aestronglyMeasurable_cut (hS n)) 1
      (norm_cut_le _) w = 0 := fun n => by
    have h := Submodule.inner_right_of_mem_orthogonal (bmul_cut_mem_mulDomain hm n w) hw
    rw [inner_bmul_cut_self (hS n)] at h
    exact inner_self_eq_zero.1 h
  have hn : ∀ n, ∀ᵐ a ∂μ, cut E (truncSet m n) a (w a) = 0 := fun n => by
    filter_upwards [coeFn_bmul (cut E (truncSet m n)) (aestronglyMeasurable_cut (hS n)) 1
      (norm_cut_le _) w, Lp.ext_iff.1 (h0 n), Lp.coeFn_zero E 2 μ] with a h1 h2 h3
    rw [← h1, h2, h3]; rfl
  have hw : (w : α → E) =ᵐ[μ] 0 := by
    refine ae_of_cover (S := truncSet m) exists_mem_truncSet ?_
    filter_upwards [ae_all_iff.2 hn] with a ha n hmem
    have := ha n
    rwa [cut_apply_of_mem hmem] at this
  exact Lp.ext (hw.trans (Lp.coeFn_zero E 2 μ).symm)

variable [CompleteSpace F]

/-- The fibrewise-adjoint multiplier is a formal adjoint. -/
theorem mulOp_isFormalAdjoint :
    (mulOp μ m).IsFormalAdjoint (mulOp μ fun a => ContinuousLinearMap.adjoint (m a)) := by
  intro x y
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulOp μ m x, coeFn_mulOp μ (fun a => ContinuousLinearMap.adjoint (m a)) y]
    with a h1 h2
  rw [h1, h2, ContinuousLinearMap.adjoint_inner_right]

/-- **The adjoint of a multiplication operator is the multiplier by the fibrewise adjoints**,
domain included. -/
theorem adjoint_mulOp (hm : StronglyMeasurable m) :
    (mulOp μ m)† = mulOp μ fun a => ContinuousLinearMap.adjoint (m a) := by
  have hd : Dense ((mulOp μ m).domain : Set (Lp E 2 μ)) := dense_mulDomain hm
  have hle := (mulOp_isFormalAdjoint (μ := μ) (m := m)).le_adjoint hd
  have hm' : StronglyMeasurable fun a => ContinuousLinearMap.adjoint (m a) := by
    have hc : Continuous fun A : E →L[ℝ] F => ContinuousLinearMap.adjoint A :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous
    exact hc.comp_stronglyMeasurable hm
  have hS := measurableSet_truncSet hm
  have hb' : ∀ n, ∀ a ∈ truncSet m n, ‖ContinuousLinearMap.adjoint (m a)‖ ≤ n := fun n a ha => by
    rw [LinearIsometryEquiv.norm_map]; exact ha
  have hdom :
      (mulOp μ m)†.domain ≤ (mulOp μ fun a => ContinuousLinearMap.adjoint (m a)).domain := by
    intro y hy
    have hcutadj : ∀ n a, cut E (truncSet m n) a =
        ContinuousLinearMap.adjoint (cut E (truncSet m n) a) := fun n a => by
      by_cases ha : a ∈ truncSet m n
      · simp only [cut, Set.indicator_of_mem ha]; exact ContinuousLinearMap.adjoint_id.symm
      · simp [cut, ha]
    have hindadj : ∀ n a, (truncSet m n).indicator (fun a => ContinuousLinearMap.adjoint (m a)) a =
        ContinuousLinearMap.adjoint ((truncSet m n).indicator m a) := fun n a => by
      by_cases ha : a ∈ truncSet m n
      · simp [ha]
      · simp [ha]
    obtain ⟨hy', -⟩ := (graph_iff_trunc hS exists_mem_truncSet hb' hm' y
      ((mulOp μ m)† ⟨y, hy⟩)).2 fun n => by
      refine ext_inner_right ℝ fun z => ?_
      have h1 := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩
        ⟨_, bmul_cut_mem_mulDomain hm n z⟩
      rw [mulOp_bmul_cut hm n z] at h1
      calc _ = ⟪z, bmul μ ((truncSet m n).indicator fun a => ContinuousLinearMap.adjoint (m a))
              ((hm'.indicator (hS n)).aestronglyMeasurable) n
              (norm_indicator_le (Nat.cast_nonneg n) (hb' n)) y⟫ := real_inner_comm _ _
        _ = ⟪bmul μ ((truncSet m n).indicator m) ((hm.indicator (hS n)).aestronglyMeasurable) n
              (norm_indicator_le (Nat.cast_nonneg n) (norm_le_of_mem_truncSet n)) z, y⟫ :=
            (inner_bmul (hindadj n) z y).symm
        _ = ⟪(mulOp μ m)† ⟨y, hy⟩, bmul μ (cut E (truncSet m n)) (aestronglyMeasurable_cut (hS n))
              1 (norm_cut_le _) z⟫ := by rw [real_inner_comm]; exact h1.symm
        _ = _ := by
          rw [inner_bmul (hB' := aestronglyMeasurable_cut (hS n)) (C' := 1)
            (hC' := norm_cut_le _) (hcutadj n)]
    exact hy'
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

/-- Membership in the adjoint domain: `y ∈ D(T*)` iff `m* y ∈ L²`. -/
theorem mem_adjoint_mulOp_domain (hm : StronglyMeasurable m) {y : Lp F 2 μ} :
    y ∈ (mulOp μ m)†.domain ↔
      MemLp (fun a => ContinuousLinearMap.adjoint (m a) (y a)) 2 μ := by
  rw [adjoint_mulOp hm]; rfl

/-- The adjoint acts fibrewise by the fibre adjoints. -/
theorem coeFn_adjoint_mulOp (hm : StronglyMeasurable m) (y : (mulOp μ m)†.domain) :
    (mulOp μ m)† y =ᵐ[μ] fun a => ContinuousLinearMap.adjoint (m a) ((y : Lp F 2 μ) a) := by
  obtain ⟨hd, hv⟩ := LinearPMap.ext_iff.1 (adjoint_mulOp hm)
  have : (mulOp μ m)† y = (mulOp μ fun a => ContinuousLinearMap.adjoint (m a)) ⟨y, hd ▸ y.2⟩ :=
    hv (x := y) (hf := y.2) (hg := hd ▸ y.2)
  rw [this]
  exact coeFn_mulOp μ _ _

end MulOp

section Fibre

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (μ) in
/-- The fibrewise subspace `{u ∈ L² | u a ∈ K a for a.e. a}`. -/
def fibreSub (K : α → Submodule ℝ E) : Submodule ℝ (Lp E 2 μ) where
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
theorem mem_fibreSub {K : α → Submodule ℝ E} {u : Lp E 2 μ} :
    u ∈ fibreSub μ K ↔ ∀ᵐ a ∂μ, u a ∈ K a := Iff.rfl

variable (K : α → Submodule ℝ E) [∀ a, (K a).HasOrthogonalProjection]
  (hP : AEStronglyMeasurable (fun a => (K a).starProjection) μ)

/-- The fibrewise projection `u ↦ (a ↦ P_{K a} (u a))`, a bounded multiplier. -/
def projMul : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  bmul μ (fun a => (K a).starProjection) hP 1 fun a => (K a).starProjection_norm_le

theorem coeFn_projMul (u : Lp E 2 μ) :
    projMul K hP u =ᵐ[μ] fun a => (K a).starProjection (u a) :=
  coeFn_bmul _ hP 1 _ u

theorem projMul_mem (u : Lp E 2 μ) : projMul K hP u ∈ fibreSub μ K := by
  filter_upwards [coeFn_projMul K hP u] with a h
  rw [h]; exact (K a).starProjection_apply_mem _

theorem mem_fibreSub_iff_projMul {u : Lp E 2 μ} : u ∈ fibreSub μ K ↔ projMul K hP u = u := by
  constructor
  · intro hu
    refine Lp.ext ?_
    filter_upwards [coeFn_projMul K hP u, hu] with a h1 h2
    rw [h1, (K a).starProjection_eq_self_iff.2 h2]
  · intro hu
    have := Lp.ext_iff.1 hu
    filter_upwards [coeFn_projMul K hP u, this] with a h1 h2
    rw [← (K a).starProjection_eq_self_iff, ← h1, h2]

include hP in
/-- Fibrewise subspaces with measurable fibre projections are closed. -/
theorem isClosed_fibreSub : IsClosed (fibreSub μ K : Set (Lp E 2 μ)) := by
  have : (fibreSub μ K : Set (Lp E 2 μ)) = {u | projMul K hP u = u} := by
    ext u; exact mem_fibreSub_iff_projMul K hP
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
    (fibreSub μ K).starProjection u = projMul K hP u := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (projMul_mem K hP u) fun w hw => ?_
  rw [L2.inner_def]
  refine (integral_congr_ae ?_).trans (integral_zero α ℝ)
  filter_upwards [Lp.coeFn_sub u (projMul K hP u), coeFn_projMul K hP u, hw] with a h1 h2 h3
  rw [h1, Pi.sub_apply, h2]
  exact (K a).starProjection_inner_eq_zero _ _ h3

omit [CompleteSpace E] in
include hP in
/-- Pointwise form of `starProjection_fibreSub`. -/
theorem coeFn_starProjection_fibreSub [(fibreSub μ K).HasOrthogonalProjection] (u : Lp E 2 μ) :
    (fibreSub μ K).starProjection u =ᵐ[μ] fun a => (K a).starProjection (u a) := by
  rw [starProjection_fibreSub K hP]; exact coeFn_projMul K hP u

end Fibre

section MeasurableProj

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- On a finite-dimensional source, a family of operators is strongly measurable as soon as all
its applications are. -/
theorem stronglyMeasurable_clm_of_apply {β : Type*} [MeasurableSpace β] {f : β → E →L[ℝ] F}
    (h : ∀ x, StronglyMeasurable fun b => f b x) : StronglyMeasurable f := by
  let b := Module.finBasis ℝ E
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
  exact (ContinuousLinearMap.smulRightL ℝ E F
    (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_stronglyMeasurable (h (b i))

section Resolvent

variable (H : E →L[ℝ] E) (hsym : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫) (hpos : ∀ x, 0 ≤ ⟪H x, x⟫)
include hpos

omit [FiniteDimensional ℝ E] in
/-- `ε ‖v‖ ≤ ‖(ε + H) v‖` for a positive operator `H` and `ε > 0`. -/
theorem norm_le_resolvent (ε : ℝ) (v : E) :
    ε * ‖v‖ ≤ ‖(ε • (1 : E →L[ℝ] E) + H) v‖ := by
  have h1 : ε * ‖v‖ ^ 2 ≤ ⟪(ε • (1 : E →L[ℝ] E) + H) v, v⟫ := by
    rw [_root_.add_apply, inner_add_left, _root_.smul_apply,
      one_apply_eq_self, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hpos v]
  have h2 := real_inner_le_norm ((ε • (1 : E →L[ℝ] E) + H) v) v
  rcases (norm_nonneg v).eq_or_lt with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right (by nlinarith) h

/-- `ε + H` is invertible for a positive operator `H` and `ε > 0`. -/
theorem isUnit_resolvent {ε : ℝ} (hε : 0 < ε) : IsUnit (ε • (1 : E →L[ℝ] E) + H) := by
  have hinj : Function.Injective (ε • (1 : E →L[ℝ] E) + H) := by
    rw [← (ε • (1 : E →L[ℝ] E) + H).coe_coe, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have := norm_le_resolvent H hpos ε v
    rw [ContinuousLinearMap.coe_coe] at hv
    rw [hv, norm_zero] at this
    exact norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg v]) (norm_nonneg v))
  refine ContinuousLinearMap.isUnit_iff_bijective.2 ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective
    (f := ((ε • (1 : E →L[ℝ] E) + H : E →L[ℝ] E) : E →ₗ[ℝ] E))).1 hinj

omit hpos in
include hsym in
/-- For a symmetric operator, `(ker H)ᗮ ⊆ range H`. -/
theorem orthogonal_ker_le_range :
    (LinearMap.ker (H : E →ₗ[ℝ] E))ᗮ ≤ LinearMap.range (H : E →ₗ[ℝ] E) := by
  have hadj : ContinuousLinearMap.adjoint H = H :=
    ((ContinuousLinearMap.eq_adjoint_iff H H).2 hsym).symm
  have h := ContinuousLinearMap.orthogonal_range H
  rw [hadj] at h
  rw [← h, Submodule.orthogonal_orthogonal]

include hsym in
/-- **Resolvent limit**: `ε (ε + H)⁻¹ x → P_{ker H} x` as `ε = 1/(n+1) → 0`, for a positive
symmetric operator `H` on a finite-dimensional space. -/
theorem tendsto_resolvent (x : E) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) •
        Ring.inverse ((1 / ((n : ℝ) + 1)) • (1 : E →L[ℝ] E) + H) x) atTop
      (𝓝 ((LinearMap.ker (H : E →ₗ[ℝ] E)).starProjection x)) := by
  set K := LinearMap.ker (H : E →ₗ[ℝ] E)
  set k := K.starProjection x
  obtain ⟨z, hz⟩ := orthogonal_ker_le_range H hsym (K.sub_starProjection_mem_orthogonal x)
  have hk : H k = 0 := LinearMap.mem_ker.1 (K.starProjection_apply_mem x)
  have hz' : H z = x - k := hz
  have key : ∀ ε : ℝ, 0 < ε → ‖ε • Ring.inverse (ε • (1 : E →L[ℝ] E) + H) x - k‖ ≤ 2 * ε * ‖z‖ := by
    intro ε hε
    set A := ε • (1 : E →L[ℝ] E) + H
    have hA := isUnit_resolvent H hpos hε
    have hAR : ∀ w, A (Ring.inverse A w) = w := fun w => by
      rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel A hA,
        one_apply_eq_self]
    set y := ε • Ring.inverse A x
    have hy : A y = ε • x := by rw [_root_.map_smul, hAR]
    have hAk : A (k + ε • z) = ε • x + (ε * ε) • z := by
      simp only [A, _root_.add_apply, _root_.smul_apply,
        one_apply_eq_self, _root_.map_add, _root_.map_smul, hk, hz']
      simp only [smul_add, smul_sub, mul_smul]; abel
    have hdiff : A (y - (k + ε • z)) = -((ε * ε) • z) := by
      rw [_root_.map_sub, hy, hAk]; abel
    have h1 := norm_le_resolvent H hpos ε (y - (k + ε • z))
    rw [hdiff, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)] at h1
    have h2 : ‖y - (k + ε • z)‖ ≤ ε * ‖z‖ := by
      have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hε.le)
      rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul, ← mul_assoc, ← mul_assoc,
        inv_mul_cancel₀ hε.ne', one_mul] at this
      exact this
    calc ‖y - k‖ = ‖(y - (k + ε • z)) + ε • z‖ := by congr 1; abel
      _ ≤ ‖y - (k + ε • z)‖ + ‖ε • z‖ := norm_add_le _ _
      _ ≤ ε * ‖z‖ + ε * ‖z‖ := by
          rw [norm_smul, Real.norm_of_nonneg hε.le]; linarith
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
`ε (ε + H b)⁻¹` (`tendsto_resolvent`). -/
theorem stronglyMeasurable_starProjection_ker {β : Type*} [TopologicalSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {H : β → E →L[ℝ] E} (hH : Continuous H)
    (hsym : ∀ b x y, ⟪H b x, y⟫ = ⟪x, H b y⟫) (hpos : ∀ b x, 0 ≤ ⟪H b x, x⟫) :
    StronglyMeasurable fun b => (LinearMap.ker (H b : E →ₗ[ℝ] E)).starProjection := by
  refine stronglyMeasurable_clm_of_apply fun x => ?_
  have hcont : ∀ n : ℕ, Continuous fun b => (1 / ((n : ℝ) + 1)) •
      Ring.inverse ((1 / ((n : ℝ) + 1)) • (1 : E →L[ℝ] E) + H b) x := fun n => by
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine continuous_const.smul ?_
    refine Continuous.clm_apply ?_ continuous_const
    refine continuous_iff_continuousAt.2 fun b => ?_
    have hu := isUnit_resolvent (H b) (hpos b) hε
    have := NormedRing.inverse_continuousAt hu.unit
    rw [IsUnit.unit_spec] at this
    exact this.comp (f := fun b => (1 / ((n : ℝ) + 1)) • (1 : E →L[ℝ] E) + H b)
      (continuous_const.add hH).continuousAt
  exact stronglyMeasurable_of_tendsto atTop (fun n => (hcont n).stronglyMeasurable)
    (tendsto_pi_nhds.2 fun b => tendsto_resolvent (H b) (hsym b) (hpos b) x)

end MeasurableProj

end Feec.Legacy.Whole
