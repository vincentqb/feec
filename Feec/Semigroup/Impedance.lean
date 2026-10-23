module

public import Feec.Semigroup.DissipativeInvariance

/-!
# Boundary-dissipative realizations: impedance triples

First-order systems `E' = -c* P + (boundary)`, `P' = c E` with an absorbing (impedance) boundary
condition — Maxwell's equations with the Silver–Müller condition `n × E + B_τ = 0`, the row-wise
Einstein–Bianchi system, acoustics with a radiation condition — have generators that are
m-dissipative but not skew-adjoint. Their m-dissipativity follows from one abstract structure,
which avoids any trace theory beyond what defines the energy space.

An **impedance triple** (`Feec.ImpedanceTriple`) consists of Hilbert spaces `V`, `H₁`, `H₂`, `Y`
and bounded maps `ι : V → H₁` (the field), `c : V → H₂` (its differential, e.g. the curl) and
`γ : V → Y` (its boundary trace), such that
`⟪v, w⟫_V = ⟪ι v, ι w⟫ + ⟪c v, c w⟫ + ⟪γ v, γ w⟫`, `ι` is injective and `ι V` is dense. On
`X = H₁ ⊕₂ H₂` the operator `A = ImpedanceTriple.op` has domain the pairs `(E, P)` with
`E = ι v` for some `v ∈ V` such that `v' ↦ -⟪P, c v'⟫ - ⟪γ v, γ v'⟫` is represented by some
`w ∈ H₁` on `ι V`, and `A (E, P) = (w, c v)`. For a smooth `P` the identity
`⟪w, ι v'⟫ = -⟪P, c v'⟫ - ⟪γ v, γ v'⟫` says `w = -c* P` in the interior together with the
**natural boundary condition** coupling the boundary values of `P` with `γ v`; in the Maxwell case
it is `n × B = E_τ`, i.e. the absorbing condition `n × E + B_τ = 0`.

## Main results

* `ImpedanceTriple.op` and `mem_graph_op_iff`: the operator and its graph.
* **`ImpedanceTriple.re_inner_op`**: the energy flux `re ⟪A u, u⟫ = -‖γ v‖²` (the boundary
  dissipation).
* **`ImpedanceTriple.isMDissipative_op`**: `A` is m-dissipative. Surjectivity of `1 - A` is the
  Riesz representation of `v' ↦ ⟪f, ι v'⟫ - ⟪g, c v'⟫` on `V` (the energy space carries the
  boundary term in its inner product; this is the Lax–Milgram step of the impedance problem).
* **`ImpedanceTriple.norm_sq_semigroup`**: the semigroup radiates: for `u₀ ∈ D(A)`,
  `‖S(t) u₀‖² = ‖u₀‖² - 2 ∫₀ᵗ ‖γ v(s)‖² ds`, the energy lost being the outgoing flux.

## References

* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §4.6 (the impedance
  problem), §1.4 (the Silver–Müller condition)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4 (Lumer–Phillips)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

namespace Feec

variable (𝕜 : Type*) [RCLike 𝕜] (V H₁ H₂ Y : Type*)
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

/-- An **impedance triple**: an energy space `V` with a field map `ι : V → H₁`, a differential
`c : V → H₂` and a boundary trace `γ : V → Y`, whose inner product is the sum of the three, with
`ι` injective and of dense range. [Monk2003], §4.6 -/
structure ImpedanceTriple where
  /-- the field -/
  ι : V →L[𝕜] H₁
  /-- its differential -/
  c : V →L[𝕜] H₂
  /-- its boundary trace -/
  γ : V →L[𝕜] Y
  inner_eq : ∀ v w, ⟪v, w⟫_𝕜 = ⟪ι v, ι w⟫_𝕜 + ⟪c v, c w⟫_𝕜 + ⟪γ v, γ w⟫_𝕜
  injective : Function.Injective ι
  denseRange : DenseRange ι

variable {𝕜 V H₁ H₂ Y}

namespace ImpedanceTriple

theorem _root_.Feec.withLp_prod_ext {A B : Type*} {x y : WithLp 2 (A × B)} (h1 : x.fst = y.fst)
    (h2 : x.snd = y.snd) : x = y :=
  (WithLp.ext_iff _).2 (Prod.ext h1 h2)

variable (T : ImpedanceTriple 𝕜 V H₁ H₂ Y)

/-- The weak equation `⟪w, ι v'⟫ = -⟪P, c v'⟫ - ⟪γ v, γ v'⟫` for all `v' ∈ V`. -/
def IsWeak (v : V) (P : H₂) (w : H₁) : Prop :=
  ∀ v' : V, ⟪w, T.ι v'⟫_𝕜 = -⟪P, T.c v'⟫_𝕜 - ⟪T.γ v, T.γ v'⟫_𝕜

/-- The graph of the impedance operator. -/
def graph : Submodule 𝕜 (WithLp 2 (H₁ × H₂) × WithLp 2 (H₁ × H₂)) where
  carrier := {p | ∃ v : V, T.ι v = p.1.fst ∧ T.c v = p.2.snd ∧ T.IsWeak v p.1.snd p.2.fst}
  add_mem' := by
    rintro ⟨a, a'⟩ ⟨b, b'⟩ ⟨v, hv1, hv2, hv3⟩ ⟨w, hw1, hw2, hw3⟩
    refine ⟨v + w, ?_, ?_, fun v' => ?_⟩
    · simp only [_root_.map_add, hv1, hw1, Prod.fst_add, WithLp.add_fst]
    · simp only [_root_.map_add, hv2, hw2, Prod.snd_add, WithLp.add_snd]
    · simp only [Prod.fst_add, Prod.snd_add, WithLp.add_fst, WithLp.add_snd, inner_add_left,
        _root_.map_add, hv3 v', hw3 v']
      ring
  zero_mem' := ⟨0, by simp, by simp, fun v' => by simp⟩
  smul_mem' := by
    rintro r ⟨a, a'⟩ ⟨v, hv1, hv2, hv3⟩
    refine ⟨r • v, ?_, ?_, fun v' => ?_⟩
    · simp only [_root_.map_smul, hv1, Prod.smul_fst, WithLp.smul_fst]
    · simp only [_root_.map_smul, hv2, Prod.smul_snd, WithLp.smul_snd]
    · simp only [Prod.smul_fst, Prod.smul_snd, WithLp.smul_fst, WithLp.smul_snd,
        inner_smul_left, _root_.map_smul, hv3 v']
      ring

/-- The witness of a graph point is unique, and a graph point with zero first component is zero:
`ι` is injective and `ι V` is dense. -/
theorem graph_snd_eq_zero (p : WithLp 2 (H₁ × H₂) × WithLp 2 (H₁ × H₂)) (hp : p ∈ T.graph)
    (h0 : p.1 = 0) : p.2 = 0 := by
  obtain ⟨v, hv1, hv2, hv3⟩ := hp
  rw [h0] at hv1 hv3
  have hv : v = 0 := T.injective (by rw [hv1, _root_.map_zero]; rfl)
  subst hv
  have hw : p.2.fst = 0 := by
    have hort : ∀ y ∈ Set.range T.ι, ⟪p.2.fst, y⟫_𝕜 = 0 := by
      rintro _ ⟨v', rfl⟩
      rw [hv3 v']
      simp
    have hcl : ∀ y ∈ closure (Set.range T.ι), ⟪p.2.fst, y⟫_𝕜 = 0 := fun y hy =>
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const).closure_subset_iff.2
        hort hy
    exact inner_self_eq_zero.1 (hcl _ (T.denseRange.closure_eq ▸ mem_univ _))
  have hc : p.2.snd = 0 := by rw [← hv2, _root_.map_zero]
  exact withLp_prod_ext (by rw [hw]; rfl) (by rw [hc]; rfl)

/-- **The impedance operator** `A (ι v, P) = (w, c v)`, `⟪w, ι v'⟫ = -⟪P, c v'⟫ - ⟪γ v, γ v'⟫`. -/
def op : WithLp 2 (H₁ × H₂) →ₗ.[𝕜] WithLp 2 (H₁ × H₂) := T.graph.toLinearPMap

theorem graph_op : T.op.graph = T.graph :=
  Submodule.toLinearPMap_graph_eq _ fun p hp h0 => T.graph_snd_eq_zero p hp h0

theorem mem_graph_op_iff {u y : WithLp 2 (H₁ × H₂)} :
    (u, y) ∈ T.op.graph ↔ ∃ v : V, T.ι v = u.fst ∧ T.c v = y.snd ∧ T.IsWeak v u.snd y.fst := by
  rw [graph_op]; rfl

theorem mem_graph_op (u : T.op.domain) : ((u : WithLp 2 (H₁ × H₂)), T.op u) ∈ T.op.graph :=
  T.op.mem_graph u

/-- The energy-space element of a state in the domain. -/
def witness (u : T.op.domain) : V := ((T.mem_graph_op_iff).1 (T.mem_graph_op u)).choose

theorem ι_witness (u : T.op.domain) : T.ι (T.witness u) = (u : WithLp 2 (H₁ × H₂)).fst :=
  ((T.mem_graph_op_iff).1 (T.mem_graph_op u)).choose_spec.1

theorem c_witness (u : T.op.domain) : T.c (T.witness u) = (T.op u).snd :=
  ((T.mem_graph_op_iff).1 (T.mem_graph_op u)).choose_spec.2.1

theorem isWeak_witness (u : T.op.domain) :
    T.IsWeak (T.witness u) (u : WithLp 2 (H₁ × H₂)).snd (T.op u).fst :=
  ((T.mem_graph_op_iff).1 (T.mem_graph_op u)).choose_spec.2.2

/-- **The boundary trace of a state** of the domain: `γ v` for its energy-space element. -/
def trace (u : T.op.domain) : Y := T.γ (T.witness u)

/-- **The energy flux**: `re ⟪A u, u⟫ = -‖γ v‖²`, the boundary dissipation. -/
theorem re_inner_op (u : T.op.domain) :
    RCLike.re ⟪T.op u, (u : WithLp 2 (H₁ × H₂))⟫_𝕜 = -‖T.trace u‖ ^ 2 := by
  set v := T.witness u
  have h1 := T.isWeak_witness u v
  rw [T.ι_witness u] at h1
  have e : ⟪T.op u, (u : WithLp 2 (H₁ × H₂))⟫_𝕜 =
      ⟪(T.op u).fst, (u : WithLp 2 (H₁ × H₂)).fst⟫_𝕜 +
        ⟪(T.op u).snd, (u : WithLp 2 (H₁ × H₂)).snd⟫_𝕜 := WithLp.prod_inner_apply _ _
  rw [e, h1, ← T.c_witness u]
  have h2 : RCLike.re (-⟪(u : WithLp 2 (H₁ × H₂)).snd, T.c v⟫_𝕜 +
      ⟪T.c v, (u : WithLp 2 (H₁ × H₂)).snd⟫_𝕜) = 0 := by
    rw [_root_.map_add, _root_.map_neg, inner_re_symm (𝕜 := 𝕜)]; ring
  have h3 : RCLike.re ⟪T.γ v, T.γ v⟫_𝕜 = ‖T.γ v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := 𝕜) _
  simp only [trace]
  rw [show -⟪(u : WithLp 2 (H₁ × H₂)).snd, T.c v⟫_𝕜 - ⟪T.γ v, T.γ v⟫_𝕜 +
      ⟪T.c v, (u : WithLp 2 (H₁ × H₂)).snd⟫_𝕜 =
      (-⟪(u : WithLp 2 (H₁ × H₂)).snd, T.c v⟫_𝕜 + ⟪T.c v, (u : WithLp 2 (H₁ × H₂)).snd⟫_𝕜) -
        ⟪T.γ v, T.γ v⟫_𝕜 by ring, _root_.map_sub, h2, h3]
  ring

theorem isDissipative_op : T.op.IsDissipative := fun u => by
  rw [T.re_inner_op u]; exact neg_nonpos.2 (sq_nonneg _)

/-- **`1 - A` is onto**: for `(f, g)`, the Riesz representative `v` of `v' ↦ ⟪f, ι v'⟫ - ⟪g, c v'⟫`
in `V` gives the solution `(ι v, g + c v)`. -/
theorem surjective_one_sub [CompleteSpace V] (y : WithLp 2 (H₁ × H₂)) :
    ∃ u : T.op.domain, ((1 : ℝ) : 𝕜) • (u : WithLp 2 (H₁ × H₂)) - T.op u = y := by
  set f := y.fst
  set g := y.snd
  set ℓ : V →L[𝕜] 𝕜 := (innerSL 𝕜 f).comp T.ι - (innerSL 𝕜 g).comp T.c
  set v := (InnerProductSpace.toDual 𝕜 V).symm ℓ
  have hv : ∀ v', ⟪v, v'⟫_𝕜 = ⟪f, T.ι v'⟫_𝕜 - ⟪g, T.c v'⟫_𝕜 := fun v' => by
    rw [InnerProductSpace.toDual_symm_apply]; simp [ℓ]
  set u : WithLp 2 (H₁ × H₂) := WithLp.toLp 2 (T.ι v, g + T.c v)
  set w : WithLp 2 (H₁ × H₂) := WithLp.toLp 2 (T.ι v - f, T.c v)
  have hmem : (u, w) ∈ T.op.graph := by
    rw [mem_graph_op_iff]
    refine ⟨v, rfl, rfl, fun v' => ?_⟩
    have := hv v'
    rw [T.inner_eq] at this
    change ⟪T.ι v - f, T.ι v'⟫_𝕜 = -⟪g + T.c v, T.c v'⟫_𝕜 - ⟪T.γ v, T.γ v'⟫_𝕜
    rw [inner_sub_left, inner_add_left]
    linear_combination this
  obtain ⟨hu, hw⟩ := LinearPMap.mem_graph_iff_exists.1 hmem
  refine ⟨⟨u, hu⟩, ?_⟩
  rw [hw]
  refine withLp_prod_ext ?_ ?_
  · change ((1 : ℝ) : 𝕜) • T.ι v - (T.ι v - f) = f
    simp
  · change ((1 : ℝ) : 𝕜) • (g + T.c v) - T.c v = g
    simp

/-- **The impedance operator is m-dissipative**, hence (Lumer–Phillips) generates a contraction
semigroup. -/
theorem isMDissipative_op [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] :
    T.op.IsMDissipative :=
  ⟨T.isDissipative_op, 1, one_pos, T.surjective_one_sub⟩

variable [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [NormedSpace ℝ H₁]
  [IsScalarTower ℝ 𝕜 H₁] [NormedSpace ℝ H₂] [IsScalarTower ℝ 𝕜 H₂]

open scoped Classical in
/-- The boundary trace on `D(A)`, extended by `0`. -/
def traceExt (u : WithLp 2 (H₁ × H₂)) : Y := if h : u ∈ T.op.domain then T.trace ⟨u, h⟩ else 0

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [NormedSpace ℝ H₁]
  [IsScalarTower ℝ 𝕜 H₁] [NormedSpace ℝ H₂] [IsScalarTower ℝ 𝕜 H₂] in
theorem traceExt_of_mem {u : WithLp 2 (H₁ × H₂)} (h : u ∈ T.op.domain) :
    T.traceExt u = T.trace ⟨u, h⟩ := by
  unfold traceExt; simp [h]

/-- **The semigroup radiates**: for `u₀ ∈ D(A)` and `t ≥ 0`,
`‖S(t) u₀‖² = ‖u₀‖² - 2 ∫₀ᵗ ‖γ v(s)‖² ds`, where `γ v(s)` is the boundary trace of `S(s) u₀`:
the energy lost is the outgoing boundary flux. -/
theorem norm_sq_semigroup (u₀ : T.op.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖T.isMDissipative_op.semigroup.S t u₀‖ ^ 2 = ‖(u₀ : WithLp 2 (H₁ × H₂))‖ ^ 2 -
      2 * ∫ s in (0 : ℝ)..t, ‖T.traceExt (T.isMDissipative_op.semigroup.S s u₀)‖ ^ 2 := by
  set hA := T.isMDissipative_op
  rw [hA.norm_sq_semigroup_apply u₀ ht, ← intervalIntegral.integral_const_mul, sub_eq_add_neg,
    ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  have hmem := hA.semigroup_mem_domain u₀ hs.1
  have e1 := hA.apply_semigroup u₀ hs.1
  rw [← e1, T.traceExt_of_mem hmem]
  have := T.re_inner_op ⟨_, hmem⟩
  linarith

end ImpedanceTriple

end Feec
