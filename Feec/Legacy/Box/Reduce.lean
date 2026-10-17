module

public import Feec.Legacy.WaveGroup

/-!
# Hilbert complexes on reflection-invariant subspaces

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

The method of images models a box `Q` by the subspace of a periodic model fixed by a group of
reflections. This file does the functional analysis once, for an abstract Hilbert complex: given
three commuting isometric involutions `R_0, R_1, R_2` on each space (`Refl3`) that commute with
the differentials (`Intertwines`), the fixed subspaces form a Hilbert complex (`resComplex`)
whose differentials are the restrictions (`res`), whose adjoints are the restrictions of the
adjoints (`mem_adjoint_res_domain`, `coe_adjoint_res_apply`), and to which the hypotheses of
thesis Props 4.17/4.19 transfer (`Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`, with existence `Feec.HilbertComplex.ReducingSubcomplex.existsUnique_mem`).

## Main results

* `Refl3.fix`, the fixed subspace, and `Refl3.avg = Π_i (1 + R_i)/2`, a self-adjoint idempotent
  onto it (`avg_mem`, `avg_of_mem`, `inner_avg`).
* `Intertwines.adjoint`: the adjoint of an intertwining densely defined operator intertwines.
* `res`, `isClosed_res`, `dense_res`; `resComplex`.
* **`Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`**: if the hypotheses of `Feec.Legacy.Constraints.Kc_propagates` hold for `H` and
  `(S1, S2)`, and `S1`, `S2` are invariant under the reflections, then the conclusion of
  Prop 4.17 holds for `resComplex` and `(S1 ∩ fix, S2 ∩ fix)`.

## References

* [QuennevilleBelair2015], §4.2 (Hilbert complexes), §4.10–4.11 (Props 4.17, 4.19)
* [AFW2010], [BruningLesch1992] (Hilbert complexes)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open LinearPMap Set Filter Topology

namespace Feec.Legacy.Box

/-- Three commuting isometric involutions (the reflections `x_i ↦ -x_i`, `i = 0, 1, 2`, acting
on a space of fields). -/
structure Refl3 (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  /-- the reflections -/
  R : Fin 3 → W →L[ℝ] W
  invol : ∀ i x, R i (R i x) = x
  inner_map : ∀ i x y, ⟪R i x, R i y⟫ = ⟪x, y⟫
  comm : ∀ i j x, R i (R j x) = R j (R i x)

namespace Refl3

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (G : Refl3 W)

/-- The reflections are self-adjoint. -/
theorem inner_R_left (i : Fin 3) (x y : W) : ⟪G.R i x, y⟫ = ⟪x, G.R i y⟫ := by
  conv_lhs => rw [← G.invol i y]
  exact G.inner_map i x (G.R i y)

/-- The fixed subspace (fields with the prescribed parities). -/
def fix : Submodule ℝ W where
  carrier := {x | ∀ i, G.R i x = x}
  zero_mem' := fun i => by simp
  add_mem' := fun hx hy i => by simp [hx i, hy i]
  smul_mem' := fun c x hx i => by simp [hx i]

theorem mem_fix {x : W} : x ∈ G.fix ↔ ∀ i, G.R i x = x := Iff.rfl

theorem isClosed_fix : IsClosed (G.fix : Set W) := by
  have e : (G.fix : Set W) = ⋂ i, {x | G.R i x = x} := by ext; simp [mem_fix]
  rw [e]
  exact isClosed_iInter fun i => isClosed_eq (G.R i).continuous continuous_id

instance [CompleteSpace W] : CompleteSpace G.fix := G.isClosed_fix.completeSpace_coe

/-- `(1 + R_i)/2`. -/
def half (i : Fin 3) : W →L[ℝ] W := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ W + G.R i)

theorem half_apply (i : Fin 3) (x : W) : G.half i x = (1 / 2 : ℝ) • (x + G.R i x) := rfl

theorem R_half (i : Fin 3) (x : W) : G.R i (G.half i x) = G.half i x := by
  rw [half_apply, _root_.map_smul, _root_.map_add, G.invol, add_comm]

theorem R_half_comm (i j : Fin 3) (x : W) : G.R i (G.half j x) = G.half j (G.R i x) := by
  rw [half_apply, half_apply, _root_.map_smul, _root_.map_add, G.comm]

theorem half_of_eq {i : Fin 3} {x : W} (h : G.R i x = x) : G.half i x = x := by
  rw [half_apply, h, ← two_smul ℝ x, smul_smul]; norm_num

theorem inner_half (i : Fin 3) (x y : W) : ⟪G.half i x, y⟫ = ⟪x, G.half i y⟫ := by
  rw [half_apply, half_apply, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    G.inner_R_left]
  simp

/-- The averaging operator `Π_i (1 + R_i)/2`. -/
def avg : W →L[ℝ] W := G.half 2 ∘L G.half 1 ∘L G.half 0

theorem avg_apply (x : W) : G.avg x = G.half 2 (G.half 1 (G.half 0 x)) := rfl

theorem avg_mem (x : W) : G.avg x ∈ G.fix := by
  intro i
  rw [avg_apply]
  fin_cases i
  · change G.R 0 _ = _
    rw [G.R_half_comm, G.R_half_comm, G.R_half]
  · change G.R 1 _ = _
    rw [G.R_half_comm, G.R_half, ]
  · change G.R 2 _ = _
    rw [G.R_half]

theorem avg_of_mem {x : W} (hx : x ∈ G.fix) : G.avg x = x := by
  rw [avg_apply, G.half_of_eq (hx 0), G.half_of_eq (hx 1), G.half_of_eq (hx 2)]

theorem half_comm (i j : Fin 3) (x : W) : G.half i (G.half j x) = G.half j (G.half i x) := by
  rw [half_apply, half_apply, half_apply, half_apply]
  simp only [_root_.map_smul, _root_.map_add, G.comm i j]
  module

theorem inner_avg (x y : W) : ⟪G.avg x, y⟫ = ⟪x, G.avg y⟫ := by
  rw [avg_apply, avg_apply, G.inner_half, G.inner_half, G.inner_half, G.half_comm 0 1,
    G.half_comm 0 2, G.half_comm 1 2]

/-- `avg` as a map onto the fixed subspace. -/
def avgFix : W →L[ℝ] G.fix := G.avg.codRestrict G.fix G.avg_mem

@[simp] theorem coe_avgFix (x : W) : (G.avgFix x : W) = G.avg x := rfl

/-- A closed subspace invariant under the reflections: its projection commutes with them. -/
theorem R_starProjection {S : Submodule ℝ W} [S.HasOrthogonalProjection]
    (hS : ∀ i, ∀ x ∈ S, G.R i x ∈ S) (i : Fin 3) (x : W) :
    G.R i (S.starProjection x) = S.starProjection (G.R i x) := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS i _ (S.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← _root_.map_sub, G.inner_R_left]
  exact S.starProjection_inner_eq_zero x _ (hS i w hw)

end Refl3

/-! ## Intertwining operators and their restrictions -/

section Res

variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `T` commutes with the reflections: `T R_i = R'_i T` on `D(T)` (and `R_i D(T) ⊆ D(T)`). -/
def Intertwines (G : Refl3 W) (G' : Refl3 V) (T : W →ₗ.[ℝ] V) : Prop :=
  ∀ i (x : T.domain), ∃ h : G.R i x ∈ T.domain, T ⟨_, h⟩ = G'.R i (T x)

variable {G : Refl3 W} {G' : Refl3 V} {T : W →ₗ.[ℝ] V}

theorem Intertwines.half (hT : Intertwines G G' T) (i : Fin 3) (x : T.domain) :
    ∃ h : G.half i x ∈ T.domain, T ⟨_, h⟩ = G'.half i (T x) := by
  obtain ⟨h, e⟩ := hT i x
  have hm : G.half i x ∈ T.domain := T.domain.smul_mem _ (T.domain.add_mem x.2 h)
  refine ⟨hm, ?_⟩
  have : (⟨_, hm⟩ : T.domain) = (1 / 2 : ℝ) • (x + ⟨_, h⟩) := Subtype.ext rfl
  rw [this, T.map_smul, T.map_add, e]
  rfl

theorem Intertwines.avg (hT : Intertwines G G' T) (x : T.domain) :
    ∃ h : G.avg x ∈ T.domain, T ⟨_, h⟩ = G'.avg (T x) := by
  obtain ⟨h0, e0⟩ := hT.half 0 x
  obtain ⟨h1, e1⟩ := hT.half 1 ⟨_, h0⟩
  obtain ⟨h2, e2⟩ := hT.half 2 ⟨_, h1⟩
  refine ⟨h2, e2.trans ?_⟩
  rw [e1, e0]; rfl

theorem Intertwines.mem_fix (hT : Intertwines G G' T) (x : T.domain) (hx : (x : W) ∈ G.fix) :
    T x ∈ G'.fix := fun i => by
  obtain ⟨h, e⟩ := hT i x
  rw [← e]
  congr 1
  exact Subtype.ext (hx i)

variable [CompleteSpace W] [CompleteSpace V]

omit [CompleteSpace V] in
/-- **Adjoints of intertwining operators intertwine.** -/
theorem Intertwines.adjoint (hT : Intertwines G G' T) (hd : Dense (T.domain : Set W)) :
    Intertwines G' G T† := by
  intro i y
  have hfa := adjoint_isFormalAdjoint hd
  have key : ∀ x : T.domain, ⟪G.R i (T† y), x⟫ = ⟪G'.R i y, T x⟫ := by
    intro x
    obtain ⟨h, e⟩ := hT i x
    rw [G.inner_R_left, hfa y ⟨_, h⟩, e, ← G'.inner_R_left]
  have hm : G'.R i y ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hm, adjoint_apply_eq hd ⟨_, hm⟩ key⟩

omit [CompleteSpace W] [CompleteSpace V] in
/-- The restriction of an intertwining operator to the fixed subspaces. -/
def res (T : W →ₗ.[ℝ] V) (G : Refl3 W) (G' : Refl3 V) (hT : Intertwines G G' T) :
    G.fix →ₗ.[ℝ] G'.fix where
  domain := T.domain.comap G.fix.subtype
  toFun :=
    { toFun := fun x => ⟨T ⟨((x : G.fix) : W), x.2⟩, hT.mem_fix ⟨_, x.2⟩ (x : G.fix).2⟩
      map_add' := fun x y => Subtype.ext (by
        change T ⟨_, _⟩ = T ⟨_, _⟩ + T ⟨_, _⟩
        rw [← T.map_add]; rfl)
      map_smul' := fun c x => Subtype.ext (by
        change T ⟨_, _⟩ = c • T ⟨_, _⟩
        rw [← T.map_smul]; rfl) }

omit [CompleteSpace W] [CompleteSpace V] in
theorem mem_res_domain (hT : Intertwines G G' T) {x : G.fix} :
    x ∈ (res T G G' hT).domain ↔ (x : W) ∈ T.domain := Iff.rfl

omit [CompleteSpace W] [CompleteSpace V] in
@[simp] theorem coe_res_apply (hT : Intertwines G G' T) (x : (res T G G' hT).domain) :
    ((res T G G' hT x : G'.fix) : V) = T ⟨((x : G.fix) : W), x.2⟩ := rfl

omit [CompleteSpace W] [CompleteSpace V] in
/-- Restrictions of closed operators are closed. -/
theorem isClosed_res (hT : Intertwines G G' T) (hc : T.IsClosed) : (res T G G' hT).IsClosed := by
  have e : ((res T G G' hT).graph : Set (G.fix × G'.fix)) =
      (Prod.map (Subtype.val : G.fix → W) (Subtype.val : G'.fix → V)) ⁻¹'
        (T.graph : Set (W × V)) := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, mem_preimage, Prod.map_apply]
    constructor
    · rintro ⟨x', rfl, rfl⟩
      exact ⟨⟨_, x'.2⟩, rfl, rfl⟩
    · rintro ⟨x', hx, hy⟩
      refine ⟨⟨x, by rw [mem_res_domain, ← hx]; exact x'.2⟩, rfl, Subtype.ext ?_⟩
      rw [coe_res_apply, ← hy]
      congr 1
      exact Subtype.ext hx.symm
  change IsClosed ((res T G G' hT).graph : Set (G.fix × G'.fix))
  rw [e]
  exact hc.preimage (continuous_subtype_val.prodMap continuous_subtype_val)

omit [CompleteSpace W] [CompleteSpace V] in
/-- Restrictions of densely defined operators are densely defined. -/
theorem dense_res (hT : Intertwines G G' T) (hd : Dense (T.domain : Set W)) :
    Dense ((res T G G' hT).domain : Set G.fix) := by
  intro p
  have h := map_mem_closure G.avgFix.continuous (hd (p : W))
    (t := ((res T G G' hT).domain : Set G.fix)) fun x hx => by
      obtain ⟨h, -⟩ := hT.avg ⟨x, hx⟩
      exact h
  have hp : G.avgFix (p : W) = p := Subtype.ext (G.avg_of_mem p.2)
  rwa [hp] at h

omit [CompleteSpace V] in
/-- **The adjoint of the restriction is the restriction of the adjoint** (domains). -/
theorem mem_adjoint_res_domain (hT : Intertwines G G' T) (hd : Dense (T.domain : Set W))
    {y : G'.fix} : y ∈ (res T G G' hT)†.domain ↔ (y : V) ∈ T†.domain := by
  constructor
  · intro hy
    set z := (res T G G' hT)† ⟨y, hy⟩
    have hfa := adjoint_isFormalAdjoint (dense_res hT hd)
    refine mem_adjoint_domain_of_exists _ ⟨(z : W), fun x => ?_⟩
    obtain ⟨h, e⟩ := hT.avg x
    have h1 : ⟪(y : V), T x⟫ = ⟪(y : V), T ⟨_, h⟩⟫ := by
      rw [e, ← G'.inner_avg, G'.avg_of_mem y.2]
    have h2 := hfa ⟨y, hy⟩ ⟨G.avgFix x, h⟩
    rw [Submodule.coe_inner, Submodule.coe_inner] at h2
    rw [h1]
    change ⟪(z : W), (x : W)⟫ = ⟪(y : V), T ⟨_, h⟩⟫
    rw [← G.avg_of_mem z.2, G.inner_avg]
    exact h2
  · intro hy
    refine mem_adjoint_domain_of_exists _ ⟨⟨T† ⟨_, hy⟩,
      (hT.adjoint hd).mem_fix ⟨_, hy⟩ y.2⟩, fun x => ?_⟩
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact adjoint_isFormalAdjoint hd ⟨_, hy⟩ ⟨_, x.2⟩

omit [CompleteSpace V] in
/-- **The adjoint of the restriction is the restriction of the adjoint** (values). -/
theorem coe_adjoint_res_apply (hT : Intertwines G G' T) (hd : Dense (T.domain : Set W))
    (y : (res T G G' hT)†.domain) :
    (((res T G G' hT)† y : G.fix) : W) =
      T† ⟨((y : G'.fix) : V), (mem_adjoint_res_domain hT hd).1 y.2⟩ := by
  have hfa := adjoint_isFormalAdjoint (dense_res hT hd)
  symm
  refine adjoint_apply_eq hd _ fun x => ?_
  obtain ⟨h, e⟩ := hT.avg x
  have h1 : ⟪((y : G'.fix) : V), T x⟫ = ⟪((y : G'.fix) : V), T ⟨_, h⟩⟫ := by
    rw [e, ← G'.inner_avg, G'.avg_of_mem (y : G'.fix).2]
  have h2 := hfa y ⟨G.avgFix x, h⟩
  rw [Submodule.coe_inner, Submodule.coe_inner] at h2
  rw [h1, ← G.avg_of_mem ((res T G G' hT)† y).2, G.inner_avg]
  exact h2

end Res

/-! ## The restricted Hilbert complex -/

section Complex

open HilbertComplex2 Constraints

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- **The Hilbert complex on the fixed subspaces** of three reflection groups commuting with the
differentials. -/
def resComplex (H : HilbertComplex2 W0 W1 W2) (G0 : Refl3 W0) (G1 : Refl3 W1) (G2 : Refl3 W2)
    (h0 : Intertwines G0 G1 H.d0) (h1 : Intertwines G1 G2 H.d1) :
    HilbertComplex2 G0.fix G1.fix G2.fix where
  d0 := res H.d0 G0 G1 h0
  d1 := res H.d1 G1 G2 h1
  dense0 := dense_res h0 H.dense0
  dense1 := dense_res h1 H.dense1
  closed0 := isClosed_res h0 H.closed0
  closed1 := isClosed_res h1 H.closed1
  map_mem x := H.map_mem ⟨_, x.2⟩
  comp_zero x := Subtype.ext (H.comp_zero ⟨_, x.2⟩)

variable {H : HilbertComplex2 W0 W1 W2} {G0 : Refl3 W0} {G1 : Refl3 W1} {G2 : Refl3 W2}
  {h0 : Intertwines G0 G1 H.d0} {h1 : Intertwines G1 G2 H.d1}

/-- The middle domain of the restricted complex. -/
theorem mem_midDomain_res {u : G1.fix} :
    u ∈ (resComplex H G0 G1 G2 h0 h1).midDomain ↔ (u : W1) ∈ H.midDomain := by
  change u ∈ (res H.d1 G1 G2 h1).domain ⊓ (res H.d0 G0 G1 h0)†.domain ↔ _
  rw [Submodule.mem_inf, mem_res_domain, mem_adjoint_res_domain h0 H.dense0]
  rfl

/-- The domain of `d1*` of the restricted complex. -/
theorem mem_adj1_domain_res {ρ : G2.fix} :
    ρ ∈ (resComplex H G0 G1 G2 h0 h1).d1†.domain ↔ (ρ : W2) ∈ H.d1†.domain :=
  mem_adjoint_res_domain h1 H.dense1

variable (S1 : Submodule ℝ W1) (S2 : Submodule ℝ W2)
  [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]
  [(S1.comap G1.fix.subtype).HasOrthogonalProjection]
  [(S2.comap G2.fix.subtype).HasOrthogonalProjection]

end Complex

/-! ## Groups and the inclusion of the fixed subspaces -/

section Groups

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Groups are determined by their generators, through an intertwiner**: if `ι` maps `D(A)` into
`D(B)` with `ι A = B ι`, `B` is skew-symmetric and `D(A)` is dense, then `ι e^{tA} = e^{tB} ι` for
every orthogonal group `e^{tA}` generated by `A` and `e^{tB}` generated by `B`. (Uniqueness of
strong solutions for `B`, forward in time; the group law backward; density.) -/
theorem group_intertwine {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F} (Ga : UnitaryGroupGenerator A)
    (Gb : UnitaryGroupGenerator B) (ι : E →L[ℝ] F) (hdom : ∀ x : A.domain, ι x ∈ B.domain)
    (hcomm : ∀ x : A.domain, ι (A x) = B ⟨ι x, hdom x⟩) (hB : IsSkewSymm B)
    (hd : Dense (A.domain : Set E)) (t : ℝ) (x : E) : ι (Ga.S t x) = Gb.S t (ι x) := by
  have fwd : ∀ s, 0 ≤ s → ∀ y : A.domain, ι (Ga.S s y) = Gb.S s (ι y) := by
    intro s hs y
    have hU : IsStrongSolution B s (ι y) 0 (fun r => ι (Ga.S r y)) := by
      refine ⟨fun r _ => hdom ⟨_, Ga.mem_domain_apply y r⟩, fun r _ => ?_, by simp [Ga.map_zero]⟩
      simp only [Pi.zero_apply, add_zero]
      have h := (ι.hasFDerivAt.comp_hasDerivAt r (Ga.hasDerivAt_apply y r))
      rw [← Ga.apply_comm y r, hcomm] at h
      exact h.hasDerivWithinAt
    have hV := Constraints.isStrongSolution_orbit Gb s ⟨ι y, hdom y⟩
    exact Constraints.strong_unique B hB hU hV ⟨hs, le_rfl⟩
  have hall : ∀ y : A.domain, ι (Ga.S t y) = Gb.S t (ι y) := by
    intro y
    rcases le_total 0 t with ht | ht
    · exact fwd t ht y
    · have h := fwd (-t) (neg_nonneg.2 ht) ⟨_, Ga.mem_domain_apply y t⟩
      have e1 : Ga.S (-t) (Ga.S t y) = y := by
        have := Constraints.group_apply_neg_apply Ga (-t) (y : E); rwa [neg_neg] at this
      simp only [e1] at h
      rw [h, Constraints.group_apply_neg_apply]
  exact congrFun (Continuous.ext_on hd (ι.continuous.comp (Ga.S t).continuous)
    ((Gb.S t).continuous.comp ι.continuous) (fun y hy => hall ⟨y, hy⟩)) x

end Groups

section Incl

open HilbertComplex2 Constraints

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    {H : HilbertComplex2 W0 W1 W2} {G0 : Refl3 W0} {G1 : Refl3 W1} {G2 : Refl3 W2}
    {h0 : Intertwines G0 G1 H.d0} {h1 : Intertwines G1 G2 H.d1}

variable (G0 G1 G2) in
/-- The inclusion of the fixed state space into the full state space. -/
def incl : Tot G0.fix G1.fix G2.fix →L[ℝ] Tot W0 W1 W2 :=
  (Constraints.totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.toContinuousLinearMap ∘L
    (G0.fix.subtypeL.prodMap (G1.fix.subtypeL.prodMap G2.fix.subtypeL)) ∘L
    (Constraints.totL (W0 := G0.fix) (W1 := G1.fix) (W2 := G2.fix)).toContinuousLinearMap

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
theorem tot_incl (x : Tot G0.fix G1.fix G2.fix) :
    tot W0 W1 W2 (incl G0 G1 G2 x) =
      (((tot _ _ _ x).1 : W0), ((tot _ _ _ x).2.1 : W1), ((tot _ _ _ x).2.2 : W2)) := by
  simp [incl]; rfl

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
theorem incl_injective : Function.Injective (incl G0 G1 G2) := by
  intro x y h
  have := congrArg (tot W0 W1 W2) h
  rw [tot_incl, tot_incl] at this
  simp only [Prod.mk.injEq] at this
  apply (tot G0.fix G1.fix G2.fix).injective
  exact Prod.ext (Subtype.ext this.1) (Prod.ext (Subtype.ext this.2.1) (Subtype.ext this.2.2))

/-- `D(L)` of the restricted complex is the preimage of `D(L)`. -/
theorem mem_domL_res_iff (x : Tot G0.fix G1.fix G2.fix) :
    x ∈ (resComplex H G0 G1 G2 h0 h1).domL ↔ incl G0 G1 G2 x ∈ H.domL := by
  rw [Constraints.mem_domL, Constraints.mem_domL, tot_incl, mem_midDomain_res, mem_adj1_domain_res]
  rfl

/-- **The Hodge wave operator of the restricted complex is the restriction**:
`ι L_box = L ι`. -/
theorem incl_waveOp (x : Tot G0.fix G1.fix G2.fix) (hx : x ∈ (resComplex H G0 G1 G2 h0 h1).domL) :
    incl G0 G1 G2 ((resComplex H G0 G1 G2 h0 h1).waveOp ⟨x, hx⟩) =
      H.waveOp ⟨incl G0 G1 G2 x, (mem_domL_res_iff x).1 hx⟩ := by
  apply (tot W0 W1 W2).injective
  rw [tot_incl, Constraints.tot_waveOp, Constraints.tot_waveOp]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · dsimp only
    rw [Submodule.coe_neg, neg_inj]
    refine (coe_adjoint_res_apply h0 H.dense0 _).trans ?_
    congr 1
  · dsimp only
    rw [Submodule.coe_add]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine congrArg H.d0 (Subtype.ext ?_)
      change ((tot _ _ _ x).1 : W0) = (tot W0 W1 W2 (incl G0 G1 G2 x)).1
      rw [tot_incl]
    · refine (coe_adjoint_res_apply h1 H.dense1 _).trans ?_
      congr 1
  · dsimp only
    rw [Submodule.coe_neg, neg_inj]
    refine congrArg H.d1 (Subtype.ext ?_)
    change ((tot _ _ _ x).2.1 : W1) = (tot W0 W1 W2 (incl G0 G1 G2 x)).2.1
    rw [tot_incl]

/-- **Every group of the restricted complex is the restriction of every group of `H`.** -/
theorem incl_group (Gb : UnitaryGroupGenerator (-(resComplex H G0 G1 G2 h0 h1).waveOp))
    (G : UnitaryGroupGenerator (-H.waveOp)) (t : ℝ) (x : Tot G0.fix G1.fix G2.fix) :
    incl G0 G1 G2 (Gb.S t x) = G.S t (incl G0 G1 G2 x) := by
  refine group_intertwine Gb G (incl G0 G1 G2)
    (fun y => (mem_domL_res_iff (h0 := h0) (h1 := h1) (y : Tot G0.fix G1.fix G2.fix)).1 y.2)
    (fun y => ?_) (isSkewSymm_neg (Constraints.waveOp_isSkewSymm H))
    (resComplex H G0 G1 G2 h0 h1).neg_waveOp_isSkewAdjoint.dense_domain t x
  rw [LinearPMap.neg_apply, LinearPMap.neg_apply, _root_.map_neg]
  congr 1
  exact incl_waveOp (y : Tot G0.fix G1.fix G2.fix) y.2

end Incl

end Feec.Legacy.Box
