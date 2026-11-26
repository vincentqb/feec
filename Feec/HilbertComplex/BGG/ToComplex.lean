module

public import Feec.HilbertComplex.BGG.Basic
public import Feec.HilbertComplex.Hodge
public import Feec.HilbertComplex.Short
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The complex with weak symmetries (5.1) as a closed Hilbert complex

Two closed Hilbert complexes linked by `S₀`, `S₁` with `d¹S₀ = -S₁d̃⁰` give the complex with weak
symmetries (5.1) of [QuennevilleBelair2015], §5.1,
`Γ̄ ⊃ Γ --(0 d̃)--> W̃¹ ⊃ Ṽ¹ --(S₁, d̃)--> W² × W̃²`; under exactness, closed ranges and
`d¹V¹ ⊆ d¹S₀Ṽ⁰`, with `S₀` injective, it is a closed Hilbert complex, exact at `Γ̄` and `W̃¹`.

## Main results

* `Hilb.isClosed_closedRange_exact`: (5.1) is a closed Hilbert complex, exact at `Γ̄` and `W̃¹`.
* `Hilb.toHilbertComplex`: (5.1) as a Hilbert complex on `ComplexShape.fin3`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.BGG

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem norm_sq_of_inner_eq {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] {x : E} {a : F} {b : G}
    (h : ⟪x, x⟫ = ⟪a, a⟫ + ⟪b, b⟫) : ‖x‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- If the bottom complex is exact at `Ṽ¹`, `d¹`, `d̃¹` have closed ranges and `d¹V¹ ⊆ d¹S₀Ṽ⁰`,
then `u ↦ (S₁u, d̃¹u)` has closed range. [QuennevilleBelair2015], Prop 5.1 (adapted) -/
theorem isClosed_range_prod {V1 W2 Vt0 Vt1 Wt2 : Type*}
    [NormedAddCommGroup V1] [NormedSpace 𝕜 V1]
    [NormedAddCommGroup W2] [NormedSpace 𝕜 W2]
    [NormedAddCommGroup Vt0] [NormedSpace 𝕜 Vt0]
    [NormedAddCommGroup Vt1] [NormedSpace 𝕜 Vt1] [CompleteSpace Vt1]
    [NormedAddCommGroup Wt2] [NormedSpace 𝕜 Wt2] [CompleteSpace Wt2]
    (d1 : V1 →L[𝕜] W2) (dt0 : Vt0 →L[𝕜] Vt1) (dt1 : Vt1 →L[𝕜] Wt2)
    (S0 : Vt0 →L[𝕜] V1) (S1 : Vt1 →L[𝕜] W2)
    (anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)) (hdd : ∀ φ, dt1 (dt0 φ) = 0)
    (exact_bot : ∀ z, dt1 z = 0 → ∃ φ, dt0 φ = z)
    (hd1 : IsClosed (Set.range d1)) (hdt1 : IsClosed (Set.range dt1))
    (hreg : Set.range d1 ⊆ Set.range (d1 ∘ S0)) :
    IsClosed (Set.range (S1.prod dt1)) := by
  let R : Submodule 𝕜 Wt2 := LinearMap.range (dt1 : Vt1 →ₗ[𝕜] Wt2)
  have : CompleteSpace R := by
    have : IsClosed (R : Set Wt2) := hdt1
    exact this.completeSpace_coe
  let g : Vt1 →L[𝕜] R := (dt1 : Vt1 →L[𝕜] Wt2).codRestrict R (fun x => ⟨x, rfl⟩)
  have gsurj : Function.Surjective g := by
    rintro ⟨_, ⟨x, rfl⟩⟩; exact ⟨x, rfl⟩
  obtain ⟨C, -, hC⟩ := g.exists_preimage_norm_le gsurj
  have hker : ∀ z, dt1 z = 0 → S1 z ∈ Set.range d1 := by
    intro z hz
    obtain ⟨φ, rfl⟩ := exact_bot z hz
    exact ⟨-(S0 φ), by simp [anticomm]⟩
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨q, hq, hqp⟩ := mem_closure_iff_seq_limit.1 hp
  choose u hu using hq
  have hμ : Tendsto (fun n => (q n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto _).comp hqp
  have hρ : Tendsto (fun n => (q n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto _).comp hqp
  obtain ⟨w, hw⟩ : p.2 ∈ Set.range dt1 :=
    hdt1.mem_of_tendsto hμ (Eventually.of_forall fun n => ⟨u n, by simp [← hu n]⟩)
  have hmem : ∀ n, (q n).2 - p.2 ∈ R := fun n => ⟨u n - w, by simp [← hu n, hw]⟩
  choose w' hw' hw'n using fun n => hC ⟨(q n).2 - p.2, hmem n⟩
  have hw'0 : Tendsto w' atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => hw'n n) ?_
    have : Tendsto (fun n => ‖(q n).2 - p.2‖) atTop (𝓝 0) := by
      simpa using (hμ.sub_const p.2).norm
    simpa using this.const_mul C
  have hin : ∀ n, (q n).1 - S1 w - S1 (w' n) ∈ Set.range d1 := by
    intro n
    have h1 : dt1 (u n - w - w' n) = 0 := by
      have : dt1 (w' n) = (q n).2 - p.2 := congrArg Subtype.val (hw' n)
      rw [map_sub, map_sub, this, hw, ← hu n]; simp
    obtain ⟨y, hy⟩ := hker _ h1
    refine ⟨y, ?_⟩
    rw [hy, map_sub, map_sub, ← hu n]; simp
  have hlim : Tendsto (fun n => (q n).1 - S1 w - S1 (w' n)) atTop (𝓝 (p.1 - S1 w)) := by
    have := (hρ.sub_const (S1 w)).sub ((S1.continuous.tendsto 0).comp hw'0)
    simpa using this
  obtain ⟨lam, hlam⟩ := hreg (hd1.mem_of_tendsto hlim (Eventually.of_forall hin))
  refine ⟨w - dt0 lam, ?_⟩
  simp only [Function.comp_apply, anticomm] at hlam
  ext
  · show S1 (w - dt0 lam) = p.1
    rw [map_sub, sub_eq_add_neg, hlam]; abel
  · simp [hdd, hw]

/-! ## Analytic BGG data on one segment -/

/-- Analytic BGG data on one segment, each domain a Hilbert space with its graph inner product. -/
structure Hilb (𝕜 : Type*) [RCLike 𝕜] (W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1 : Type*)
    [NormedAddCommGroup W0] [InnerProductSpace 𝕜 W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace 𝕜 W1] [CompleteSpace W1]
    [NormedAddCommGroup Wt0] [InnerProductSpace 𝕜 Wt0] [CompleteSpace Wt0]
    [NormedAddCommGroup Wt1] [InnerProductSpace 𝕜 Wt1] [CompleteSpace Wt1]
    [NormedAddCommGroup W2] [InnerProductSpace 𝕜 W2] [CompleteSpace W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace 𝕜 Wt2] [CompleteSpace Wt2]
    [NormedAddCommGroup V0] [InnerProductSpace 𝕜 V0] [CompleteSpace V0]
    [NormedAddCommGroup V1] [InnerProductSpace 𝕜 V1] [CompleteSpace V1]
    [NormedAddCommGroup Vt0] [InnerProductSpace 𝕜 Vt0] [CompleteSpace Vt0]
    [NormedAddCommGroup Vt1] [InnerProductSpace 𝕜 Vt1] [CompleteSpace Vt1] where
  ι0 : V0 →L[𝕜] W0
  ι1 : V1 →L[𝕜] W1
  ιt0 : Vt0 →L[𝕜] Wt0
  ιt1 : Vt1 →L[𝕜] Wt1
  ι0_injective : Function.Injective ι0
  ι1_injective : Function.Injective ι1
  ιt0_injective : Function.Injective ιt0
  ιt1_injective : Function.Injective ιt1
  /-- densely defined operators -/
  dense0 : DenseRange ι0
  dense1 : DenseRange ι1
  denset0 : DenseRange ιt0
  denset1 : DenseRange ιt1
  d0 : V0 →L[𝕜] V1
  d1 : V1 →L[𝕜] W2
  dt0 : Vt0 →L[𝕜] Vt1
  dt1 : Vt1 →L[𝕜] Wt2
  S0 : Vt0 →L[𝕜] V1
  S1 : Vt1 →L[𝕜] W2
  /-- graph inner products -/
  graph0 : ∀ u v : V0, inner 𝕜 u v = inner 𝕜 (ι0 u) (ι0 v) + inner 𝕜 (ι1 (d0 u)) (ι1 (d0 v))
  graph1 : ∀ u v : V1, inner 𝕜 u v = inner 𝕜 (ι1 u) (ι1 v) + inner 𝕜 (d1 u) (d1 v)
  grapht0 : ∀ u v : Vt0,
    inner 𝕜 u v = inner 𝕜 (ιt0 u) (ιt0 v) + inner 𝕜 (ιt1 (dt0 u)) (ιt1 (dt0 v))
  grapht1 : ∀ u v : Vt1, inner 𝕜 u v = inner 𝕜 (ιt1 u) (ιt1 v) + inner 𝕜 (dt1 u) (dt1 v)
  d1_d0 : ∀ σ, d1 (d0 σ) = 0
  dt1_dt0 : ∀ φ, dt1 (dt0 φ) = 0
  anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)

namespace Hilb

variable {W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace 𝕜 W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace 𝕜 W1] [CompleteSpace W1]
    [NormedAddCommGroup Wt0] [InnerProductSpace 𝕜 Wt0] [CompleteSpace Wt0]
    [NormedAddCommGroup Wt1] [InnerProductSpace 𝕜 Wt1] [CompleteSpace Wt1]
    [NormedAddCommGroup W2] [InnerProductSpace 𝕜 W2] [CompleteSpace W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace 𝕜 Wt2] [CompleteSpace Wt2]
    [NormedAddCommGroup V0] [InnerProductSpace 𝕜 V0] [CompleteSpace V0]
    [NormedAddCommGroup V1] [InnerProductSpace 𝕜 V1] [CompleteSpace V1]
    [NormedAddCommGroup Vt0] [InnerProductSpace 𝕜 Vt0] [CompleteSpace Vt0]
    [NormedAddCommGroup Vt1] [InnerProductSpace 𝕜 Vt1] [CompleteSpace Vt1]
    (D : Hilb 𝕜 W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1)

/-- The algebraic BGG data underlying `D`. -/
def toSegment : Segment 𝕜 V0 V1 W2 Vt0 Vt1 Wt2 where
  d0 := D.d0
  d1 := D.d1
  dt0 := D.dt0
  dt1 := D.dt1
  S0 := D.S0
  S1 := D.S1
  d1_d0 := D.d1_d0
  dt1_dt0 := D.dt1_dt0
  anticomm := D.anticomm

/-- `Γ = {(σ, φ) ∈ V⁰ × Ṽ⁰ | d σ = S φ}` -/
abbrev Γ : Submodule 𝕜 (V0 × Vt0) := D.toSegment.Γ

lemma mem_Γ {x : V0 × Vt0} : x ∈ D.Γ ↔ D.d0 x.1 = D.S0 x.2 := D.toSegment.mem_Γ

/-- `(S₁, d̃¹) : Ṽ¹ → W² × W̃²` as a bounded operator. -/
def T : Vt1 →L[𝕜] W2 × Wt2 := D.S1.prod D.dt1

@[simp] lemma T_apply (u : Vt1) : D.T u = (D.S1 u, D.dt1 u) := rfl

/-- `N(S₁) ∩ N(d̃¹)` -/
abbrev Z1 : Submodule 𝕜 Vt1 := D.T.ker

lemma mem_Z1 {u : Vt1} : u ∈ D.Z1 ↔ D.S1 u = 0 ∧ D.dt1 u = 0 := by
  simp [Z1, LinearMap.mem_ker, Prod.ext_iff]

/-- Injectivity and closed range of `d⁰`, `d̃⁰`, exactness, closed ranges, `d¹V¹ ⊆ d¹S₀Ṽ⁰`. -/
structure Hyps : Prop where
  d0_injective : Function.Injective D.d0
  dt0_injective : Function.Injective D.dt0
  d0_closed : IsClosed (Set.range (D.ι1 ∘L D.d0))
  dt0_closed : IsClosed (Set.range (D.ιt1 ∘L D.dt0))
  exact1 : D.toSegment.ExactTop
  exactt1 : D.toSegment.ExactBot
  d1_closed : IsClosed (Set.range D.d1)
  dt1_closed : IsClosed (Set.range D.dt1)
  reg : Set.range D.d1 ⊆ Set.range (D.d1 ∘ D.S0)

lemma norm_sq_V0 (σ : V0) : ‖σ‖ ^ 2 = ‖D.ι0 σ‖ ^ 2 + ‖D.ι1 (D.d0 σ)‖ ^ 2 :=
  norm_sq_of_inner_eq (D.graph0 σ σ)

lemma norm_sq_Vt1 (u : Vt1) : ‖u‖ ^ 2 = ‖D.ιt1 u‖ ^ 2 + ‖D.dt1 u‖ ^ 2 :=
  norm_sq_of_inner_eq (D.grapht1 u u)

lemma norm_ι0_le (σ : V0) : ‖D.ι0 σ‖ ≤ ‖σ‖ := by
  have h := D.norm_sq_V0 σ
  nlinarith [norm_nonneg (D.ι0 σ), norm_nonneg σ, sq_nonneg ‖D.ι1 (D.d0 σ)‖]

lemma exists_poincare {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (f : E →L[𝕜] F)
    (hf : Function.Injective f) (hr : IsClosed (Set.range f)) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ C * ‖f x‖ := by
  obtain ⟨K, hK⟩ := f.antilipschitz_of_injective_of_isClosed_range hf hr
  exact ⟨K, K.2, fun x => hK.le_mul_norm (map_zero f) x⟩

theorem isClosed_Γ : IsClosed (D.Γ : Set (V0 × Vt0)) := by
  have : (D.Γ : Set (V0 × Vt0)) = {x | D.d0 x.1 = D.S0 x.2} := by
    ext x; exact D.mem_Γ
  rw [this]
  exact isClosed_eq (D.d0.continuous.comp continuous_fst) (D.S0.continuous.comp continuous_snd)

instance : CompleteSpace D.Γ := D.isClosed_Γ.completeSpace_coe

/-- For `(σ, φ) ∈ Γ`, `‖σ‖_{V⁰} ≤ C ‖d̃φ‖` and `‖φ‖_{Ṽ⁰} ≤ C ‖d̃φ‖`. -/
theorem poincare_Γ (h : D.Hyps) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ D.Γ, ‖x.1‖ ≤ C * ‖D.ιt1 (D.dt0 x.2)‖ ∧
      ‖x.2‖ ≤ C * ‖D.ιt1 (D.dt0 x.2)‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_poincare (D.ι1 ∘L D.d0)
    (D.ι1_injective.comp h.d0_injective) h.d0_closed
  obtain ⟨Kt, hKt0, hKt⟩ := exists_poincare (D.ιt1 ∘L D.dt0)
    (D.ιt1_injective.comp h.dt0_injective) h.dt0_closed
  refine ⟨max Kt (K * ‖D.ι1 ∘L D.S0‖ * Kt), le_max_of_le_left hKt0, fun x hx => ?_⟩
  have hφ := hKt x.2
  simp only [ContinuousLinearMap.comp_apply] at hφ
  have hσ := hK x.1
  simp only [ContinuousLinearMap.comp_apply, D.mem_Γ.1 hx] at hσ
  have hS : ‖D.ι1 (D.S0 x.2)‖ ≤ ‖D.ι1 ∘L D.S0‖ * ‖x.2‖ := (D.ι1 ∘L D.S0).le_opNorm x.2
  have hn := norm_nonneg (D.ιt1 (D.dt0 x.2))
  constructor
  · calc ‖x.1‖ ≤ K * ‖D.ι1 (D.S0 x.2)‖ := hσ
      _ ≤ K * (‖D.ι1 ∘L D.S0‖ * ‖x.2‖) := by gcongr
      _ ≤ K * (‖D.ι1 ∘L D.S0‖ * (Kt * ‖D.ιt1 (D.dt0 x.2)‖)) := by gcongr
      _ = K * ‖D.ι1 ∘L D.S0‖ * Kt * ‖D.ιt1 (D.dt0 x.2)‖ := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · exact hφ.trans (by gcongr; exact le_max_left _ _)

lemma exactt1' (h : D.Hyps) (z : Vt1) (hz : D.dt1 z = 0) : ∃ φ, D.dt0 φ = z := by
  have : z ∈ LinearMap.ker D.toSegment.dt1 := hz
  rw [h.exactt1] at this
  exact this

theorem isClosed_range_T (h : D.Hyps) : IsClosed (Set.range D.T) :=
  isClosed_range_prod D.d1 D.dt0 D.dt1 D.S0 D.S1 D.anticomm D.dt1_dt0 (D.exactt1' h)
    h.d1_closed h.dt1_closed h.reg

lemma isClosed_Z1 : IsClosed (D.Z1 : Set Vt1) := D.T.isClosed_ker

instance : CompleteSpace D.Z1 := D.isClosed_Z1.completeSpace_coe

theorem mem_Z1_iff (h : D.Hyps) {u : Vt1} : u ∈ D.Z1 ↔ ∃ x ∈ D.Γ, D.dt0 x.2 = u := by
  have e := D.toSegment.ker_D1_eq_range_D0 h.exact1 h.exactt1
  have h1 : u ∈ D.Z1 ↔ u ∈ LinearMap.ker D.toSegment.D1 := by
    rw [mem_Z1, LinearMap.mem_ker, Segment.D1_apply, Prod.mk_eq_zero]; rfl
  rw [h1, e]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩

lemma dt0_mem_Z1 {x : V0 × Vt0} (hx : x ∈ D.Γ) : D.dt0 x.2 ∈ D.Z1 :=
  D.mem_Z1.2 ⟨D.toSegment.S1_dt0_of_mem hx, D.dt1_dt0 _⟩

/-- `‖u‖_{Ṽ¹} ≤ C ‖(S₁u, d̃¹u)‖` for `u ⊥ N(S₁) ∩ N(d̃¹)`. -/
theorem poincare_T (h : D.Hyps) : ∃ C, 0 ≤ C ∧ ∀ w ∈ D.Z1ᗮ, ‖w‖ ≤ C * ‖D.T w‖ := by
  let f : D.Z1ᗮ →L[𝕜] W2 × Wt2 := D.T ∘L D.Z1ᗮ.subtypeL
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun w hw => ?_
    have h1 : (w : Vt1) ∈ D.Z1 := hw
    have : (w : Vt1) ∈ D.Z1 ⊓ D.Z1ᗮ := ⟨h1, w.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hr : Set.range f = Set.range D.T := by
    ext p
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨⟨u - D.Z1.starProjection u, D.Z1.sub_starProjection_mem_orthogonal u⟩, ?_⟩
      have := D.mem_Z1.1 (D.Z1.starProjection_apply_mem u)
      simp [f, this.1, this.2]
  obtain ⟨C, hC0, hC⟩ := exists_poincare f hf (hr ▸ D.isClosed_range_T h)
  exact ⟨C, hC0, fun w hw => hC ⟨w, hw⟩⟩

/-- `u = d̃χ + w` with `(ρ, χ) ∈ Γ` and `w ⊥ N(S₁) ∩ N(d̃¹)`.
Cf. [QuennevilleBelair2015], Prop 5.2 -/
theorem hodge_Vt1 (h : D.Hyps) (u : Vt1) : ∃ x ∈ D.Γ, ∃ w ∈ D.Z1ᗮ, u = D.dt0 x.2 + w := by
  obtain ⟨x, hx, hxu⟩ := (D.mem_Z1_iff h).1 (D.Z1.starProjection_apply_mem u)
  exact ⟨x, hx, _, D.Z1.sub_starProjection_mem_orthogonal u, by rw [hxu]; abel⟩

/-! ### The complex (5.1) as unbounded operators -/

/-- `(σ, φ) ↦ (σ, d̃φ)` (in `W⁰ × W̃¹`), whose image of `Γ` is the graph of `(0 d)`. -/
def LΓ : V0 × Vt0 →L[𝕜] W0 × Wt1 :=
  (D.ι0 ∘L ContinuousLinearMap.fst 𝕜 V0 Vt0).prod
    ((D.ιt1 ∘L D.dt0) ∘L ContinuousLinearMap.snd 𝕜 V0 Vt0)

/-- `Γ̄`: the closure of `π₁Γ` in `W⁰`. -/
def Γbar : Submodule 𝕜 W0 :=
  (D.Γ.map ((D.ι0 : V0 →ₗ[𝕜] W0) ∘ₗ LinearMap.fst 𝕜 V0 Vt0)).topologicalClosure

/-- The first operator `(0 d) : Γ̄ ⊃ Γ → W̃¹` of (5.1), as an unbounded operator `W⁰ → W̃¹`. -/
def D0op : W0 →ₗ.[𝕜] Wt1 := (D.Γ.map (D.LΓ : V0 × Vt0 →ₗ[𝕜] W0 × Wt1)).toLinearPMap

/-- The second operator `(S, d) : W̃¹ ⊃ Ṽ¹ → W² × W̃²` of (5.1). -/
def D1op : Wt1 →ₗ.[𝕜] W2 × Wt2 :=
  (LinearMap.range ((D.ιt1.prod D.T : Vt1 →L[𝕜] Wt1 × (W2 × Wt2)) :
    Vt1 →ₗ[𝕜] Wt1 × (W2 × Wt2))).toLinearPMap

lemma graph0_hg (hS0 : Function.Injective D.S0) :
    ∀ (x : W0 × Wt1) (_ : x ∈ D.Γ.map (D.LΓ : V0 × Vt0 →ₗ[𝕜] W0 × Wt1)), x.1 = 0 → x.2 = 0 := by
  rintro _ ⟨y, hy, rfl⟩ h0
  have h1 : y.1 = 0 := D.ι0_injective (by simpa [LΓ] using h0)
  have h2 : y.2 = 0 := hS0 (by rw [← D.mem_Γ.1 hy, h1, map_zero, map_zero])
  simp [LΓ, h2]

lemma graph1_hg : ∀ (x : Wt1 × (W2 × Wt2))
    (_ : x ∈ LinearMap.range ((D.ιt1.prod D.T : Vt1 →L[𝕜] Wt1 × (W2 × Wt2)) :
      Vt1 →ₗ[𝕜] Wt1 × (W2 × Wt2))), x.1 = 0 → x.2 = 0 := by
  rintro _ ⟨v, rfl⟩ h0
  have : v = 0 := D.ιt1_injective (by simpa using h0)
  simp [this]

theorem D0op_graph (hS0 : Function.Injective D.S0) :
    D.D0op.graph = D.Γ.map (D.LΓ : V0 × Vt0 →ₗ[𝕜] W0 × Wt1) :=
  Submodule.toLinearPMap_graph_eq _ (D.graph0_hg hS0)

theorem D1op_graph : D.D1op.graph = LinearMap.range ((D.ιt1.prod D.T : Vt1 →L[𝕜]
    Wt1 × (W2 × Wt2)) : Vt1 →ₗ[𝕜] Wt1 × (W2 × Wt2)) :=
  Submodule.toLinearPMap_graph_eq _ D.graph1_hg

theorem D0op_domain : D.D0op.domain.topologicalClosure = D.Γbar := by
  simp only [D0op, Submodule.toLinearPMap_domain, Γbar, ← Submodule.map_comp]
  rfl

theorem D1op_domain : D.D1op.domain = LinearMap.range (D.ιt1 : Vt1 →ₗ[𝕜] Wt1) := by
  simp only [D1op, Submodule.toLinearPMap_domain, ← LinearMap.range_comp]
  rfl

lemma exists_bound_Γ (h : D.Hyps) : ∃ C : NNReal, ∀ x : D.Γ,
    ‖x‖ ≤ C * ‖D.ιt1 (D.dt0 (x : V0 × Vt0).2)‖ := by
  obtain ⟨C, hC0, hC⟩ := D.poincare_Γ h
  refine ⟨⟨C, hC0⟩, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hC x x.2
  show ‖(x : V0 × Vt0)‖ ≤ _
  rw [Prod.norm_def]
  exact max_le h1 h2

theorem D0op_isClosed (h : D.Hyps) (hS0 : Function.Injective D.S0) : D.D0op.IsClosed := by
  obtain ⟨C, hC⟩ := D.exists_bound_Γ h
  let g : D.Γ →L[𝕜] W0 × Wt1 := D.LΓ ∘L D.Γ.subtypeL
  have hg : AntilipschitzWith C g := g.antilipschitz_of_bound fun x =>
    (hC x).trans (by gcongr; exact norm_snd_le (g x))
  have hset : (D.D0op.graph : Set (W0 × Wt1)) = Set.range g := by
    rw [D.D0op_graph hS0]
    ext p
    simp only [SetLike.mem_coe, Submodule.mem_map, Set.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, y.2, rfl⟩
  show IsClosed (D.D0op.graph : Set (W0 × Wt1))
  rw [hset]
  exact hg.isClosed_range g.uniformContinuous

theorem D0op_isClosed_range (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    IsClosed (LinearMap.range D.D0op.toFun : Set Wt1) := by
  obtain ⟨C, hC⟩ := D.exists_bound_Γ h
  let g : D.Γ →L[𝕜] Wt1 := (D.ιt1 ∘L D.dt0) ∘L ContinuousLinearMap.snd 𝕜 V0 Vt0 ∘L D.Γ.subtypeL
  have hg : AntilipschitzWith C g := g.antilipschitz_of_bound hC
  have hset : (LinearMap.range D.D0op.toFun : Set Wt1) = Set.range g := by
    rw [D0op, Submodule.toLinearPMap_range _ (D.graph0_hg hS0)]
    ext p
    simp only [SetLike.mem_coe, Submodule.mem_map, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, y.2, rfl⟩, rfl⟩
  rw [hset]
  exact hg.isClosed_range g.uniformContinuous

theorem D1op_isClosed : D.D1op.IsClosed := by
  let g : Vt1 →L[𝕜] Wt1 × (W2 × Wt2) := D.ιt1.prod D.T
  have hb : ∀ v, ‖v‖ ≤ (2 : NNReal) * ‖g v‖ := by
    intro v
    have h1 : ‖D.ιt1 v‖ ≤ ‖g v‖ := norm_fst_le (g v)
    have h2 : ‖D.dt1 v‖ ≤ ‖g v‖ :=
      (norm_snd_le (D.T v)).trans (norm_snd_le (g v))
    have := D.norm_sq_Vt1 v
    push_cast
    nlinarith [norm_nonneg v, norm_nonneg (g v), norm_nonneg (D.ιt1 v), norm_nonneg (D.dt1 v)]
  have hg : AntilipschitzWith 2 g := g.antilipschitz_of_bound hb
  show IsClosed (D.D1op.graph : Set (Wt1 × (W2 × Wt2)))
  rw [D.D1op_graph]
  exact hg.isClosed_range g.uniformContinuous

theorem D1op_isClosed_range (h : D.Hyps) :
    IsClosed (LinearMap.range D.D1op.toFun : Set (W2 × Wt2)) := by
  have hset : (LinearMap.range D.D1op.toFun : Set (W2 × Wt2)) = Set.range D.T := by
    rw [D1op, Submodule.toLinearPMap_range _ D.graph1_hg]
    ext p
    simp only [SetLike.mem_coe, Submodule.mem_map, Set.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩; exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩; exact ⟨_, ⟨v, rfl⟩, rfl⟩
  rw [hset]
  exact D.isClosed_range_T h

lemma mem_ker_D1op {y : Wt1} : y ∈ D.D1op.ker ↔ ∃ v ∈ D.Z1, D.ιt1 v = y := by
  rw [LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨x, rfl, hx⟩
    have hm : ((x : Wt1), D.D1op x) ∈ D.D1op.graph := LinearPMap.mem_graph D.D1op x
    rw [D.D1op_graph, hx] at hm
    obtain ⟨v, hv⟩ := hm
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
      Prod.mk.injEq] at hv
    exact ⟨v, hv.2, hv.1⟩
  · rintro ⟨v, hv, rfl⟩
    have hm : (D.ιt1 v, (0 : W2 × Wt2)) ∈ D.D1op.graph := by
      rw [D.D1op_graph]
      exact ⟨v, by simp [show D.T v = 0 from hv]⟩
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff D.D1op).1 hm
    exact ⟨x, hx1.symm, hx2⟩

lemma mem_range_D0op (hS0 : Function.Injective D.S0) {y : Wt1} :
    y ∈ LinearMap.range D.D0op.toFun ↔ ∃ x ∈ D.Γ, D.ιt1 (D.dt0 x.2) = y := by
  rw [D0op, Submodule.toLinearPMap_range _ (D.graph0_hg hS0)]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem range_D0op_le_ker_D1op (hS0 : Function.Injective D.S0) :
    LinearMap.range D.D0op.toFun ≤ D.D1op.ker := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (D.mem_range_D0op hS0).1 hy
  exact D.mem_ker_D1op.2 ⟨_, D.dt0_mem_Z1 hx, rfl⟩

theorem exact_D0op_D1op (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    D.D1op.ker = LinearMap.range D.D0op.toFun ∧ D.D0op.ker = ⊥ := by
  constructor
  · ext y
    rw [D.mem_ker_D1op, D.mem_range_D0op hS0]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (D.mem_Z1_iff h).1 hv
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, D.dt0_mem_Z1 hx, rfl⟩
  · rw [Submodule.eq_bot_iff]
    intro y hy
    rw [LinearPMap.mem_ker_iff] at hy
    obtain ⟨z, rfl, hz⟩ := hy
    have hm : ((z : W0), D.D0op z) ∈ D.D0op.graph := LinearPMap.mem_graph D.D0op z
    rw [D.D0op_graph hS0, hz] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    simp only [LΓ, ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.mk.injEq] at hxe
    have h2 : x.2 = 0 := h.dt0_injective (D.ιt1_injective (by rw [hxe.2, map_zero, map_zero]))
    have h1 : x.1 = 0 := h.d0_injective (by rw [D.mem_Γ.1 hx, h2, map_zero, map_zero])
    rw [← hxe.1, h1, map_zero]

/-- `Γ̄ ⊃ Γ --(0 d)--> W̃¹ ⊃ Ṽ¹ --(S, d)--> W² × W̃²` is a closed Hilbert complex with closed
ranges, exact at `Γ̄` and at `W̃¹`. [QuennevilleBelair2015], Prop 5.1 (adapted) -/
theorem isClosed_closedRange_exact (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    D.D0op.IsClosed ∧ D.D0op.domain.topologicalClosure = D.Γbar ∧
    IsClosed (LinearMap.range D.D0op.toFun : Set Wt1) ∧
    D.D1op.IsClosed ∧ Dense (D.D1op.domain : Set Wt1) ∧
    IsClosed (LinearMap.range D.D1op.toFun : Set (W2 × Wt2)) ∧
    LinearMap.range D.D0op.toFun ≤ D.D1op.ker ∧
    D.D1op.ker = LinearMap.range D.D0op.toFun ∧ D.D0op.ker = ⊥ := by
  refine ⟨D.D0op_isClosed h hS0, D.D0op_domain, D.D0op_isClosed_range h hS0, D.D1op_isClosed,
    ?_, D.D1op_isClosed_range h, D.range_D0op_le_ker_D1op hS0, D.exact_D0op_D1op h hS0⟩
  rw [D.D1op_domain]
  exact D.denset1

/-! ### (5.1) as a short Hilbert complex on `Γ̄` -/

instance : CompleteSpace D.Γbar := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

lemma ι0_mem_Γbar (x : D.Γ) : D.ι0 (x : V0 × Vt0).1 ∈ D.Γbar :=
  Submodule.le_topologicalClosure _ ⟨x, x.2, rfl⟩

/-- `(σ, φ) ↦ (ι⁰σ, ι̃¹d̃φ) ∈ Γ̄ × W̃¹` on `Γ`: its range is the graph of `(0 d̃)` on `Γ̄`. -/
def jΓ : D.Γ →L[𝕜] D.Γbar × Wt1 :=
  ((D.ι0 ∘L ContinuousLinearMap.fst 𝕜 V0 Vt0 ∘L D.Γ.subtypeL).codRestrict D.Γbar
    D.ι0_mem_Γbar).prod (D.ιt1 ∘L D.dt0 ∘L ContinuousLinearMap.snd 𝕜 V0 Vt0 ∘L D.Γ.subtypeL)

@[simp] lemma jΓ_apply (x : D.Γ) : D.jΓ x =
    (⟨D.ι0 (x : V0 × Vt0).1, D.ι0_mem_Γbar x⟩, D.ιt1 (D.dt0 (x : V0 × Vt0).2)) := rfl

/-- The first operator `(0 d̃) : Γ̄ ⊃ π₁Γ → W̃¹` of (5.1), on the Hilbert space `Γ̄`. -/
def D0Γ : D.Γbar →ₗ.[𝕜] Wt1 := (LinearMap.range (D.jΓ : D.Γ →ₗ[𝕜] D.Γbar × Wt1)).toLinearPMap

lemma graphΓ_hg (hS0 : Function.Injective D.S0) : ∀ (x : D.Γbar × Wt1)
    (_ : x ∈ LinearMap.range (D.jΓ : D.Γ →ₗ[𝕜] D.Γbar × Wt1)), x.1 = 0 → x.2 = 0 := by
  rintro _ ⟨y, rfl⟩ h0
  have h1 : (y : V0 × Vt0).1 = 0 :=
    D.ι0_injective (by simpa using congrArg Subtype.val h0)
  have h2 : (y : V0 × Vt0).2 = 0 := hS0 (by rw [← D.mem_Γ.1 y.2, h1, map_zero, map_zero])
  simp [h2]

theorem D0Γ_graph (hS0 : Function.Injective D.S0) :
    D.D0Γ.graph = LinearMap.range (D.jΓ : D.Γ →ₗ[𝕜] D.Γbar × Wt1) :=
  Submodule.toLinearPMap_graph_eq _ (D.graphΓ_hg hS0)

theorem D0Γ_isClosed (h : D.Hyps) (hS0 : Function.Injective D.S0) : D.D0Γ.IsClosed := by
  obtain ⟨C, hC⟩ := D.exists_bound_Γ h
  have hg : AntilipschitzWith C D.jΓ := D.jΓ.antilipschitz_of_bound fun x =>
    (hC x).trans (by gcongr; exact norm_snd_le (D.jΓ x))
  show IsClosed (D.D0Γ.graph : Set (D.Γbar × Wt1))
  rw [D.D0Γ_graph hS0, LinearMap.coe_range]
  exact hg.isClosed_range D.jΓ.uniformContinuous

theorem D0Γ_dense : Dense (D.D0Γ.domain : Set D.Γbar) := by
  rw [dense_iff_closure_eq, Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have himg : Subtype.val '' (D.D0Γ.domain : Set D.Γbar) =
      (D.Γ.map ((D.ι0 : V0 →ₗ[𝕜] W0) ∘ₗ LinearMap.fst 𝕜 V0 Vt0) : Set W0) := by
    ext w
    simp only [D0Γ, Submodule.toLinearPMap_domain, Set.mem_image, SetLike.mem_coe,
      Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨_, ⟨y, rfl⟩, rfl⟩, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩, rfl⟩
  erw [himg, ← Submodule.topologicalClosure_coe]
  exact Set.eq_univ_of_forall fun x => x.2

lemma mem_D0Γ_graph (hS0 : Function.Injective D.S0) (x : D.D0Γ.domain) :
    ∃ y : D.Γ, D.jΓ y = ((x : D.Γbar), D.D0Γ x) := by
  have hm : ((x : D.Γbar), D.D0Γ x) ∈ D.D0Γ.graph := LinearPMap.mem_graph D.D0Γ x
  rw [D.D0Γ_graph hS0] at hm
  exact hm

/-- `(S₁, d̃¹) : Ṽ¹ → W² × W̃²` with the `ℓ²` product norm on the target. -/
def TL : Vt1 →L[𝕜] WithLp 2 (W2 × Wt2) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 W2 Wt2).symm.toContinuousLinearMap ∘L D.T

lemma TL_eq_zero_iff (u : Vt1) : D.TL u = 0 ↔ u ∈ D.Z1 := by
  rw [mem_Z1, TL, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.map_eq_zero_iff, T_apply, Prod.mk_eq_zero]

/-- The second operator `(S₁, d̃¹) : W̃¹ ⊃ Ṽ¹ → W² × W̃²` of (5.1), into `WithLp 2 (W² × W̃²)`. -/
def D1L : Wt1 →ₗ.[𝕜] WithLp 2 (W2 × Wt2) :=
  (LinearMap.range ((D.ιt1.prod D.TL : Vt1 →L[𝕜] Wt1 × WithLp 2 (W2 × Wt2)) :
    Vt1 →ₗ[𝕜] Wt1 × WithLp 2 (W2 × Wt2))).toLinearPMap

lemma graph1L_hg : ∀ (x : Wt1 × WithLp 2 (W2 × Wt2))
    (_ : x ∈ LinearMap.range ((D.ιt1.prod D.TL : Vt1 →L[𝕜] Wt1 × WithLp 2 (W2 × Wt2)) :
      Vt1 →ₗ[𝕜] Wt1 × WithLp 2 (W2 × Wt2))), x.1 = 0 → x.2 = 0 := by
  rintro _ ⟨v, rfl⟩ h0
  have : v = 0 := D.ιt1_injective (by simpa using h0)
  simp [this]

theorem D1L_graph : D.D1L.graph = LinearMap.range ((D.ιt1.prod D.TL : Vt1 →L[𝕜]
    Wt1 × WithLp 2 (W2 × Wt2)) : Vt1 →ₗ[𝕜] Wt1 × WithLp 2 (W2 × Wt2)) :=
  Submodule.toLinearPMap_graph_eq _ D.graph1L_hg

theorem D1L_domain : D.D1L.domain = LinearMap.range (D.ιt1 : Vt1 →ₗ[𝕜] Wt1) := by
  simp only [D1L, Submodule.toLinearPMap_domain, ← LinearMap.range_comp]
  rfl

theorem D1L_isClosed : D.D1L.IsClosed := by
  let g : Vt1 →L[𝕜] Wt1 × WithLp 2 (W2 × Wt2) := D.ιt1.prod D.TL
  have hb : ∀ v, ‖v‖ ≤ (2 : NNReal) * ‖g v‖ := by
    intro v
    have h1 : ‖D.ιt1 v‖ ≤ ‖g v‖ := norm_fst_le (g v)
    have h2 : ‖D.dt1 v‖ ≤ ‖g v‖ := (WithLp.norm_snd_le (x := D.TL v)).trans (norm_snd_le (g v))
    have := D.norm_sq_Vt1 v
    push_cast
    nlinarith [norm_nonneg v, norm_nonneg (g v), norm_nonneg (D.ιt1 v), norm_nonneg (D.dt1 v)]
  have hg : AntilipschitzWith 2 g := g.antilipschitz_of_bound hb
  show IsClosed (D.D1L.graph : Set (Wt1 × WithLp 2 (W2 × Wt2)))
  rw [D.D1L_graph, LinearMap.coe_range]
  exact hg.isClosed_range g.uniformContinuous

lemma mem_D1L_graph (v : Vt1) : ∃ y : D.D1L.domain, (y : Wt1) = D.ιt1 v ∧ D.D1L y = D.TL v :=
  (LinearPMap.mem_graph_iff D.D1L).1 (by rw [D.D1L_graph]; exact ⟨v, rfl⟩)

theorem D0Γ_mapsTo (hS0 : Function.Injective D.S0) (x : D.D0Γ.domain) :
    (D.D0Γ x : Wt1) ∈ D.D1L.domain := by
  obtain ⟨y, hy⟩ := D.mem_D0Γ_graph hS0 x
  rw [D.D1L_domain]
  exact ⟨D.dt0 (y : V0 × Vt0).2, (congrArg Prod.snd hy : _)⟩

theorem D1L_D0Γ (hS0 : Function.Injective D.S0) (x : D.D0Γ.domain) :
    D.D1L ⟨D.D0Γ x, D.D0Γ_mapsTo hS0 x⟩ = 0 := by
  obtain ⟨y, hy⟩ := D.mem_D0Γ_graph hS0 x
  obtain ⟨z, hz, hTz⟩ := D.mem_D1L_graph (D.dt0 (y : V0 × Vt0).2)
  have hzx : z = ⟨D.D0Γ x, D.D0Γ_mapsTo hS0 x⟩ := Subtype.ext (hz.trans (congrArg Prod.snd hy))
  rw [← hzx, hTz, D.TL_eq_zero_iff]
  exact D.dt0_mem_Z1 y.2

lemma range_D0Γ (hS0 : Function.Injective D.S0) :
    LinearMap.range D.D0Γ.toFun = LinearMap.range D.D0op.toFun := by
  rw [D0Γ, Submodule.toLinearPMap_range _ (D.graphΓ_hg hS0), D0op,
    Submodule.toLinearPMap_range _ (D.graph0_hg hS0)]
  ext p
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, y.2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩

lemma mem_ker_D1L {y : Wt1} : y ∈ D.D1L.ker ↔ ∃ v ∈ D.Z1, D.ιt1 v = y := by
  rw [LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨x, rfl, hx⟩
    have hm : ((x : Wt1), D.D1L x) ∈ D.D1L.graph := LinearPMap.mem_graph D.D1L x
    rw [D.D1L_graph, hx] at hm
    obtain ⟨v, hv⟩ := hm
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
      Prod.mk.injEq] at hv
    exact ⟨v, (D.TL_eq_zero_iff v).1 hv.2, hv.1⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨z, hz, hTz⟩ := D.mem_D1L_graph v
    exact ⟨z, hz.symm, by rw [hTz, D.TL_eq_zero_iff]; exact hv⟩

lemma ker_D1L : D.D1L.ker = D.D1op.ker := by
  ext y; rw [D.mem_ker_D1L, D.mem_ker_D1op]

lemma range_D1L : (LinearMap.range D.D1L.toFun : Set (WithLp 2 (W2 × Wt2))) =
    (WithLp.prodContinuousLinearEquiv 2 𝕜 W2 Wt2).symm '' Set.range D.T := by
  rw [D1L, Submodule.toLinearPMap_range _ D.graph1L_hg]
  ext p
  simp only [SetLike.mem_coe, Submodule.mem_map, Set.mem_image, Set.mem_range,
    LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩; exact ⟨_, ⟨v, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩; exact ⟨_, ⟨v, rfl⟩, rfl⟩

/-- (5.1) on `Γ̄` as a short Hilbert complex `Γ̄ --(0 d̃)--> W̃¹ --(S₁, d̃¹)--> W² × W̃²`. -/
def toShort (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    ShortHilbertComplex 𝕜 D.Γbar Wt1 (WithLp 2 (W2 × Wt2)) where
  d₀ := D.D0Γ
  d₁ := D.D1L
  dense₀ := D.D0Γ_dense
  dense₁ := by rw [D.D1L_domain]; exact D.denset1
  closed₀ := D.D0Γ_isClosed h hS0
  closed₁ := D.D1L_isClosed
  mapsTo := D.D0Γ_mapsTo hS0
  comp := D.D1L_D0Γ hS0

theorem toShort_closedRange_exact (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    IsClosed (LinearMap.range (D.toShort h hS0).d₀.toFun : Set Wt1) ∧
    IsClosed (LinearMap.range (D.toShort h hS0).d₁.toFun : Set (WithLp 2 (W2 × Wt2))) ∧
    (D.toShort h hS0).d₁.ker = LinearMap.range (D.toShort h hS0).d₀.toFun ∧
    (D.toShort h hS0).d₀.ker = ⊥ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show IsClosed (LinearMap.range D.D0Γ.toFun : Set Wt1)
    rw [D.range_D0Γ hS0]; exact D.D0op_isClosed_range h hS0
  · show IsClosed (LinearMap.range D.D1L.toFun : Set (WithLp 2 (W2 × Wt2)))
    rw [D.range_D1L]
    exact (WithLp.prodContinuousLinearEquiv 2 𝕜 W2 Wt2).symm.toHomeomorph.isClosedMap _
      (D.isClosed_range_T h)
  · show D.D1L.ker = LinearMap.range D.D0Γ.toFun
    rw [D.ker_D1L, D.range_D0Γ hS0]; exact (D.exact_D0op_D1op h hS0).1
  · show D.D0Γ.ker = ⊥
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [LinearPMap.mem_ker_iff] at hy
    obtain ⟨z, rfl, hz⟩ := hy
    obtain ⟨x, hx⟩ := D.mem_D0Γ_graph hS0 z
    rw [hz, jΓ_apply, Prod.mk.injEq] at hx
    have h2 : (x : V0 × Vt0).2 = 0 :=
      h.dt0_injective (D.ιt1_injective (by rw [hx.2, map_zero, map_zero]))
    have h1 : (x : V0 × Vt0).1 = 0 :=
      h.d0_injective (by rw [D.mem_Γ.1 x.2, h2, map_zero, map_zero])
    rw [← hx.1]
    ext
    simp [h1]

section Example

/-- `c • id` on `ℝ` -/
def sc (c : ℝ) : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ

end Example

end Hilb

section HilbertComplex

universe u

variable {W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1 : Type u}
    [NormedAddCommGroup W0] [InnerProductSpace 𝕜 W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace 𝕜 W1] [CompleteSpace W1]
    [NormedAddCommGroup Wt0] [InnerProductSpace 𝕜 Wt0] [CompleteSpace Wt0]
    [NormedAddCommGroup Wt1] [InnerProductSpace 𝕜 Wt1] [CompleteSpace Wt1]
    [NormedAddCommGroup W2] [InnerProductSpace 𝕜 W2] [CompleteSpace W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace 𝕜 Wt2] [CompleteSpace Wt2]
    [NormedAddCommGroup V0] [InnerProductSpace 𝕜 V0] [CompleteSpace V0]
    [NormedAddCommGroup V1] [InnerProductSpace 𝕜 V1] [CompleteSpace V1]
    [NormedAddCommGroup Vt0] [InnerProductSpace 𝕜 Vt0] [CompleteSpace Vt0]
    [NormedAddCommGroup Vt1] [InnerProductSpace 𝕜 Vt1] [CompleteSpace Vt1]
    (D : Hilb 𝕜 W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1) (h : D.Hyps) (hS0 : Function.Injective D.S0)

namespace Hilb

/-- The BGG complex (5.1) as a Hilbert complex on `ComplexShape.fin3`. -/
def toHilbertComplex : HilbertComplex 𝕜 ComplexShape.fin3
    (ShortHilbertComplex.W3 D.Γbar Wt1 (WithLp 2 (W2 × Wt2))) :=
  (D.toShort h hS0).toHilbertComplex

theorem toHilbertComplex_closedRangeAt_one : (D.toHilbertComplex h hS0).ClosedRangeAt 1 := by
  rw [HilbertComplex.ClosedRangeAt,
    HilbertComplex.boundaries_eq _ (show ComplexShape.fin3.Rel 0 1 from rfl)]
  exact (D.toShort_closedRange_exact h hS0).1

theorem toHilbertComplex_closedRangeAt_two : (D.toHilbertComplex h hS0).ClosedRangeAt 2 := by
  rw [HilbertComplex.ClosedRangeAt,
    HilbertComplex.boundaries_eq _ (show ComplexShape.fin3.Rel 1 2 from rfl)]
  exact (D.toShort_closedRange_exact h hS0).2.1

theorem toHilbertComplex_cycles_one :
    (D.toHilbertComplex h hS0).cycles 1 = (D.toHilbertComplex h hS0).boundaries 1 := by
  rw [HilbertComplex.cycles_eq _ (show ComplexShape.fin3.Rel 1 2 from rfl),
    HilbertComplex.boundaries_eq _ (show ComplexShape.fin3.Rel 0 1 from rfl)]
  exact (D.toShort_closedRange_exact h hS0).2.2.1

theorem toHilbertComplex_cycles_zero : (D.toHilbertComplex h hS0).cycles 0 = ⊥ := by
  rw [HilbertComplex.cycles_eq _ (show ComplexShape.fin3.Rel 0 1 from rfl)]
  exact (D.toShort_closedRange_exact h hS0).2.2.2

end Hilb

end HilbertComplex

end Feec.BGG
