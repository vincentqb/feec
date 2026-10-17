module

public import Feec.Fourier.SymbolComplex
public import Feec.HilbertComplex.Reducing

/-!
# Fibrewise reducing subspaces of a symbol complex

A family of fibre subspaces `K i a ⊆ E i` that every symbol `m i j a` maps into `K j a`, and every
adjoint symbol maps back into `K i a`, defines the fibrewise subspaces
`L²(K i) = {u | u a ∈ K i a a.e.}` of `L²(μ; E i)`. This file proves that they form a reducing
subcomplex of the symbol complex (`FibreReducing.toReducingSubcomplex`), so every propagation and
existence theorem of `Feec.HilbertComplex.Reducing` applies, with no projection or density
hypothesis left to check: the projection hypothesis `P_K D(d) ⊆ D(d)` and the commutation
`d P_K = P_K d` are fibrewise matrix identities.

## Main definitions and results

* `Fourier.FibreReducing S K`: the fibre conditions `m i j a (K i a) ⊆ K j a`,
  `(m i j a)† (K j a) ⊆ K i a`, and measurability of `a ↦ P_{K i a}`.
* `FibreReducing.of_orthogonal`: the adjoint condition follows from `m (K i a)ᗮ ⊆ (K j a)ᗮ`.
* `starProjection_comm_of_map`: at one fibre, `P_L T = T P_K` (the fibrewise commutation).
* **`FibreReducing.toReducingSubcomplex`**: `L²(K)` is a reducing subcomplex.
* `FibreReducing.propagates`, `FibreReducing.existsUnique_mem`: constraint propagation for the
  Hodge wave equation of any finite symbol complex, with existence and uniqueness.
* `FibreComplex.IsFibreReducing` and `IsFibreReducing.toFibreReducing`: the same conditions for a
  frequency-dependent family, pulled back along a frequency map.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10–4.11 (Props 4.17, 4.19: the fibrewise commutation of `P_TSD` with the curl symbol)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap Set

namespace Feec.Fourier

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### One fibre -/

section Fibre

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Fibrewise commutation**: if `T K ⊆ L` and `T† L ⊆ K` then `P_L T = T P_K`. -/
theorem starProjection_comm_of_map (T : E →L[𝕜] F) (K : Submodule 𝕜 E) (L : Submodule 𝕜 F)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hT : K.map (T : E →ₗ[𝕜] F) ≤ L)
    (hT' : L.map (ContinuousLinearMap.adjoint T : F →ₗ[𝕜] E) ≤ K) (x : E) :
    L.starProjection (T x) = T (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hT ⟨_, K.starProjection_apply_mem x, rfl⟩) fun w hw => ?_
  rw [← _root_.map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact K.inner_left_of_mem_orthogonal (hT' ⟨w, hw, rfl⟩) (K.sub_starProjection_mem_orthogonal x)

/-- The adjoint condition from the orthogonal condition: `T Kᗮ ⊆ Lᗮ ⇒ T† L ⊆ K`. -/
theorem map_adjoint_le_of_map_orthogonal (T : E →L[𝕜] F) (K : Submodule 𝕜 E) (L : Submodule 𝕜 F)
    [K.HasOrthogonalProjection] (hT : Kᗮ.map (T : E →ₗ[𝕜] F) ≤ Lᗮ) :
    L.map (ContinuousLinearMap.adjoint T : F →ₗ[𝕜] E) ≤ K := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← K.orthogonal_orthogonal]
  intro w hw
  change ⟪w, ContinuousLinearMap.adjoint T v⟫_𝕜 = 0
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h : ⟪v, T w⟫_𝕜 = 0 := (L.mem_orthogonal _).1 (hT ⟨w, hw, rfl⟩) v hv
  rw [← inner_conj_symm, h, _root_.map_zero]

end Fibre

/-! ### Fibrewise reducing subspaces -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*} {c : ComplexShape ι}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  [∀ i, CompleteSpace (E i)]

/-- **Fibrewise reducing subspaces** of a symbol complex: `m i j a (K i a) ⊆ K j a`,
`(m i j a)† (K j a) ⊆ K i a`, and `a ↦ P_{K i a}` is a.e. strongly measurable. -/
structure FibreReducing (S : SymbolComplex 𝕜 μ c E) (K : ∀ i, α → Submodule 𝕜 (E i))
    [∀ i a, (K i a).HasOrthogonalProjection] : Prop where
  map : ∀ i j a, (K i a).map (S.m i j a : E i →ₗ[𝕜] E j) ≤ K j a
  map_adj : ∀ i j a, (K j a).map (ContinuousLinearMap.adjoint (S.m i j a) : E j →ₗ[𝕜] E i) ≤ K i a
  meas : ∀ i, AEStronglyMeasurable (fun a => (K i a).starProjection) μ

namespace FibreReducing

variable {S : SymbolComplex 𝕜 μ c E} {K : ∀ i, α → Submodule 𝕜 (E i)}
  [∀ i a, (K i a).HasOrthogonalProjection]

/-- Only the arrows of the shape need checking. -/
theorem of_rel (map : ∀ i j, c.Rel i j → ∀ a, (K i a).map (S.m i j a : E i →ₗ[𝕜] E j) ≤ K j a)
    (map_adj : ∀ i j, c.Rel i j → ∀ a,
      (K j a).map (ContinuousLinearMap.adjoint (S.m i j a) : E j →ₗ[𝕜] E i) ≤ K i a)
    (meas : ∀ i, AEStronglyMeasurable (fun a => (K i a).starProjection) μ) :
    FibreReducing S K where
  map i j a := by
    by_cases h : c.Rel i j
    · exact map i j h a
    · rw [S.shape i j h]; rintro _ ⟨v, -, rfl⟩; exact (K j a).zero_mem
  map_adj i j a := by
    by_cases h : c.Rel i j
    · exact map_adj i j h a
    · rw [S.shape i j h]; rintro _ ⟨v, -, rfl⟩
      change ContinuousLinearMap.adjoint (0 : E i →L[𝕜] E j) v ∈ K i a
      rw [_root_.map_zero]; exact (K i a).zero_mem
  meas := meas

/-- The adjoint condition from `m (K i a)ᗮ ⊆ (K j a)ᗮ`. -/
theorem of_orthogonal (map : ∀ i j a, (K i a).map (S.m i j a : E i →ₗ[𝕜] E j) ≤ K j a)
    (map_orth : ∀ i j a, (K i a)ᗮ.map (S.m i j a : E i →ₗ[𝕜] E j) ≤ (K j a)ᗮ)
    (meas : ∀ i, AEStronglyMeasurable (fun a => (K i a).starProjection) μ) :
    FibreReducing S K :=
  ⟨map, fun i j a => map_adjoint_le_of_map_orthogonal _ _ _ (map_orth i j a), meas⟩

variable (h : FibreReducing S K)
include h

theorem comm (i j : ι) (a : α) (x : E i) :
    (K j a).starProjection (S.m i j a x) = S.m i j a ((K i a).starProjection x) :=
  starProjection_comm_of_map _ _ _ (h.map i j a) (h.map_adj i j a) x

/-- The fibrewise subspaces are closed and admit orthogonal projections. -/
theorem hasOrthogonalProjection (i : ι) : (Operator.fibreSub μ (K i)).HasOrthogonalProjection :=
  Operator.hasOrthogonalProjection_fibreSub (K i) (h.meas i)

/-- **Fibrewise reducing subspaces form a reducing subcomplex** of the symbol complex. -/
theorem toReducingSubcomplex [∀ i, (Operator.fibreSub μ (K i)).HasOrthogonalProjection] :
    S.toHilbertComplex.ReducingSubcomplex fun i => Operator.fibreSub μ (K i) := by
  refine ⟨fun i j => ?_⟩
  have hP : ∀ k (u : Lp (E k) 2 μ), (Operator.fibreSub μ (K k)).starProjection u =ᵐ[μ]
      fun a => (K k a).starProjection (u a) := fun k u =>
    Operator.coeFn_starProjection_fibreSub (K k) (h.meas k) u
  have key : ∀ x : (S.toHilbertComplex.d i j).domain, (fun a =>
      S.m i j a (((Operator.fibreSub μ (K i)).starProjection (x : Lp (E i) 2 μ)) a)) =ᵐ[μ]
      (Operator.fibreSub μ (K j)).starProjection (S.toHilbertComplex.d i j x) := by
    intro x
    filter_upwards [hP i x, hP j (S.toHilbertComplex.d i j x), S.coeFn_d x] with a h1 h2 h3
    rw [h1, h2, h3, h.comm]
  have hmem : ∀ x : (S.toHilbertComplex.d i j).domain,
      (Operator.fibreSub μ (K i)).starProjection (x : Lp (E i) 2 μ) ∈
        (S.toHilbertComplex.d i j).domain := fun x =>
    (Lp.memLp _).ae_eq (key x).symm
  refine ⟨hmem, fun x => ?_⟩
  exact (Operator.mulOp_apply_eq_iff _ _).2 (key x)

variable [Fintype ι] [∀ i, (Operator.fibreSub μ (K i)).HasOrthogonalProjection]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]

/-- **Constraint propagation for a symbol complex**: every strong solution of the Hodge wave
equation `U' = L U + F` with data and forcing in the fibrewise constraint `∏ L²(K i)` stays in it.
[QuennevilleBelair2015], Prop 4.17, Prop 4.19 -/
theorem propagates {a b : ℝ} {F U : ℝ → PiLp 2 fun i => Lp (E i) 2 μ}
    (hU : Evolution.IsStrongSolution S.toHilbertComplex.wave (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i))
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i)) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i) :=
  h.toReducingSubcomplex.propagates hU h0 hF

/-- Constraint propagation for `U' = -L U + F`. -/
theorem propagates_neg {a b : ℝ} {F U : ℝ → PiLp 2 fun i => Lp (E i) 2 μ}
    (hU : Evolution.IsStrongSolution (-S.toHilbertComplex.wave) (Icc a b) F U)
    (h0 : U a ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i))
    (hF : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i)) :
    ∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i) :=
  h.toReducingSubcomplex.propagates_neg hU h0 hF

/-- **Existence, uniqueness and constraint propagation** for a symbol complex: for
`U₀ ∈ D(L) ∩ ∏ L²(K i)` and admissible forcing valued in `∏ L²(K i)`, the Hodge wave equation has
a classical solution, unique among strong solutions, and it stays in `∏ L²(K i)`.
[QuennevilleBelair2015], Prop 4.17, Prop 4.19 -/
theorem existsUnique_mem {U₀ : PiLp 2 fun i => Lp (E i) 2 μ}
    (hU₀ : U₀ ∈ S.toHilbertComplex.wave.domain)
    (hU₀S : U₀ ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i))
    {F : ℝ → PiLp 2 fun i => Lp (E i) 2 μ} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible S.toHilbertComplex.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution S.toHilbertComplex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution S.toHilbertComplex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  h.toReducingSubcomplex.existsUnique_mem hU₀ hU₀S hF hFS

/-- The wave group preserves the fibrewise constraint, for all times. -/
theorem waveGroup_mem (t : ℝ) {x : PiLp 2 fun i => Lp (E i) 2 μ}
    (hx : x ∈ HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i)) :
    S.toHilbertComplex.waveGroup.S t x ∈
      HilbertComplex.totalSub fun i => Operator.fibreSub μ (K i) :=
  h.toReducingSubcomplex.waveGroup_mem t hx

end FibreReducing

/-! ### Frequency-dependent families -/

namespace FibreComplex

variable {β : Type*} [TopologicalSpace β] (S : FibreComplex 𝕜 β c E)

/-- Fibre subspaces `K i ξ` reducing a frequency-dependent family of fibre complexes. -/
structure IsFibreReducing (K : ∀ i, β → Submodule 𝕜 (E i)) : Prop where
  map : ∀ i j ξ, (K i ξ).map (S.m i j ξ : E i →ₗ[𝕜] E j) ≤ K j ξ
  map_adj : ∀ i j ξ, (K j ξ).map (ContinuousLinearMap.adjoint (S.m i j ξ) : E j →ₗ[𝕜] E i) ≤ K i ξ

variable {S} in
/-- The adjoint condition from `m (K i ξ)ᗮ ⊆ (K j ξ)ᗮ`. -/
theorem IsFibreReducing.of_orthogonal {K : ∀ i, β → Submodule 𝕜 (E i)}
    [∀ i ξ, (K i ξ).HasOrthogonalProjection]
    (map : ∀ i j ξ, (K i ξ).map (S.m i j ξ : E i →ₗ[𝕜] E j) ≤ K j ξ)
    (map_orth : ∀ i j ξ, (K i ξ)ᗮ.map (S.m i j ξ : E i →ₗ[𝕜] E j) ≤ (K j ξ)ᗮ) :
    S.IsFibreReducing K :=
  ⟨map, fun i j ξ => map_adjoint_le_of_map_orthogonal _ _ _ (map_orth i j ξ)⟩

variable [MeasurableSpace β] [OpensMeasurableSpace β] [∀ i, FiniteDimensional 𝕜 (E i)]

variable {S} in
/-- Pull-back of fibre reducing subspaces along a frequency map. -/
theorem IsFibreReducing.toFibreReducing {K : ∀ i, β → Submodule 𝕜 (E i)}
    [∀ i ξ, (K i ξ).HasOrthogonalProjection] (h : S.IsFibreReducing K)
    (μ : Measure α) (f : α → β) (hf : AEMeasurable f μ)
    (meas : ∀ i, AEStronglyMeasurable (fun a => (K i (f a)).starProjection) μ) :
    FibreReducing (S.toSymbolComplex μ f hf) fun i a => K i (f a) :=
  ⟨fun i j a => h.map i j (f a), fun i j a => h.map_adj i j (f a), meas⟩

end FibreComplex

end Feec.Fourier
