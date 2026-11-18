module

public import Solution.Defs
public import Feec.Evolution.WellPosed
public import Feec.Semigroup.Invariance
public import Feec.Semigroup.DissipativeInvariance
public import Feec.ForMathlib.InnerProductSpace.Basic

/-!
# Constraint propagation is reduction: the abstract criterion

The fields `group` and `semigroup` of `FEEC.PropagationCriterion` from `Feec`'s semigroup
theory, over `𝕜 = ℝ` or `ℂ` (a real structure of a `𝕜`-space is the restriction of scalars,
`RCLike.isScalarTower_of_normedSpace`). For a densely defined skew-adjoint `L`, Stone's group
`LinearPMap.IsSkewAdjoint.group` is an evolution of `L` (its orbits from `D(L)` are classical
solutions on `ℝ`, `Feec.C0Group.hasDerivAt_apply`), isometric, and the strong solutions on
`[0, T]` are its orbits (`Feec.C0Semigroup.isStrongSolution_unique`); its invariant subspaces are
the reducing ones (`Feec.C0Group.IsIsometric.isReducing_iff_invariant`), and its invariant core
`Feec.C0Group.invariantCore` is the largest reducing subspace of `K`
(`IsIsometric.isReducing_invariantCore`, `IsIsometric.le_invariantCore_of_isReducing`). For an
m-dissipative `A`, the contraction semigroup of the Lumer–Phillips theorem
(`LinearPMap.IsMDissipative.semigroup`) and `LinearPMap.IsMDissipative.isReducing_iff`; a
skew-adjoint `L` is m-dissipative, with Stone's group as its semigroup at `t ≥ 0`, whence the
forward criterion for groups.

`eq_group_of_isEvolution`: every evolution of a skew-adjoint `L` on `ℝ` is Stone's group, and
`eq_semigroup_of_isEvolution`: every evolution of an m-dissipative `A` on `[0, ∞)` is its
semigroup at `t ≥ 0` (uniqueness of strong solutions, density of the domain, continuity).

## References

* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4, §1.10, §4.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

namespace FEEC

theorem IsStrongSolution.congr' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : SetRel X X} {I : Set ℝ} {u v : ℝ → X} (hu : IsStrongSolution A I u) (h : EqOn v u I) :
    IsStrongSolution A I v :=
  ⟨hu.1.congr h, fun t ht => by
    obtain ⟨w, hw, hd⟩ := hu.2 t ht
    exact ⟨w, h ht ▸ hw, hd.congr h (h ht)⟩⟩

/-- A strong solution on `I` is one on every `J ⊆ I`. -/
theorem IsStrongSolution.mono {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : SetRel X X} {I J : Set ℝ} {u : ℝ → X} (hu : IsStrongSolution A I u) (hJ : J ⊆ I) :
    IsStrongSolution A J u :=
  ⟨hu.1.mono hJ, fun t ht => by
    obtain ⟨v, hv, hd⟩ := hu.2 t (hJ ht)
    exact ⟨v, hv, hd.mono hJ⟩⟩

/-- An evolution on `I` is one on every `J ⊆ I`. -/
theorem IsEvolution.mono {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] {A : SetRel X X} {I J : Set ℝ} {S : ℝ → X →L[𝕜] X}
    (hS : IsEvolution 𝕜 A I S) (hJ : J ⊆ I) : IsEvolution 𝕜 A J S :=
  ⟨hS.1, fun x y hxy => (hS.2 x y hxy).mono hJ⟩

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The strong solutions of the challenge are those of `Feec`** (no forcing). -/
theorem isStrongSolution_graph_iff [NormedSpace ℝ E] {A : E →ₗ.[𝕜] E} {I : Set ℝ}
    {u : ℝ → E} : IsStrongSolution A.graph I u ↔ Feec.Evolution.IsStrongSolution A I 0 u := by
  refine ⟨fun h => ⟨h.1, fun t ht => ?_⟩, fun h => ⟨h.continuousOn, fun t ht => ?_⟩⟩
  · obtain ⟨v, hv, hd⟩ := h.2 t ht
    exact ⟨v, hv, by simpa using hd⟩
  · obtain ⟨v, hv, hd⟩ := h.deriv t ht
    exact ⟨v, hv, by simpa using hd⟩

theorem isReducing_iff (A : E →ₗ.[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    IsReducing A K ↔ A.IsReducing K :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.proj_mem x, h.comm x⟩⟩

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-! ### Groups -/

section Group

variable (G : Feec.C0Group 𝕜 E)

/-- **The orbits of a group are strong solutions on `ℝ`** of its generator. -/
theorem isEvolution_group : IsEvolution 𝕜 G.generator.graph univ G.S := by
  refine ⟨fun x => by rw [G.map_zero]; rfl, fun x y hxy => ⟨(G.strongCont x).continuousOn,
    fun t _ => ?_⟩⟩
  have hx : x ∈ G.generator.domain := LinearPMap.mem_domain_of_mem_graph hxy
  refine ⟨G.generator ⟨_, G.mapsTo_domain ⟨x, hx⟩ t⟩,
    G.generator.mem_graph ⟨G.S t x, G.mapsTo_domain ⟨x, hx⟩ t⟩, ?_⟩
  have h := G.hasDerivAt_apply ⟨x, hx⟩ t
  rw [← G.generator_apply_S ⟨x, hx⟩ t] at h
  exact h.hasDerivWithinAt

/-- **Strong solutions on `[0, T]` are the orbits of the group.** -/
theorem eqOn_group {x : E} (hx : x ∈ G.generator.domain) {T : ℝ} {u : ℝ → E} (hu0 : u 0 = x)
    (hu : IsStrongSolution G.generator.graph (Icc 0 T) u) :
    EqOn u (fun t => G.S t x) (Icc 0 T) := by
  have h1 := isStrongSolution_graph_iff.1 hu
  have h2 := (G.toC0Semigroup.isClassicalSolution_orbit (U₀ := x) hx 0 T).toIsStrongSolution
  have e := G.toC0Semigroup.isStrongSolution_unique (F := 0) h1 h2 continuousOn_const
    (by simp [hu0, G.toC0Semigroup.map_zero])
  intro t ht
  rw [e ht]
  simp [Feec.C0Group.toC0Semigroup]

/-- **Every evolution of a group generator on `ℝ` is the group**, when the generator is densely
defined. -/
theorem eq_group_of_isEvolution (hD : Dense (G.generator.domain : Set E))
    {S : ℝ → E →L[𝕜] E} (hS : IsEvolution 𝕜 G.generator.graph univ S) : S = G.S := by
  funext t
  have hdom : ∀ x ∈ G.generator.domain, S t x = G.S t x := by
    intro x hx
    have hux := hS.2 x _ (G.generator.mem_graph ⟨x, hx⟩)
    -- shift the orbit `s ↦ S s x` so that it starts at `S t x`
    by_cases ht : 0 ≤ t
    · exact eqOn_group G hx (hS.1 x) (hux.mono (subset_univ _)) ⟨ht, le_rfl⟩
    · push Not at ht
      obtain ⟨v, hv, -⟩ := hux.2 t (mem_univ t)
      have hy : S t x ∈ G.generator.domain := LinearPMap.mem_domain_of_mem_graph hv
      have hshift : IsStrongSolution G.generator.graph (Icc 0 (-t)) fun s => S (s + t) x := by
        refine ⟨(hux.1.comp (continuous_id.add continuous_const).continuousOn (mapsTo_univ _ _)),
          fun s _ => ?_⟩
        obtain ⟨w, hw, hd⟩ := hux.2 (s + t) (mem_univ _)
        refine ⟨w, hw, ?_⟩
        have hd' : HasDerivAt (fun r => S r x) w (s + t) := hd.hasDerivAt univ_mem
        exact ((hd'.comp_add_const s t).hasDerivWithinAt)
      have e := eqOn_group G hy (by simp) hshift ⟨neg_nonneg.2 ht.le, le_rfl⟩
      simp only [neg_add_cancel] at e
      rw [hS.1 x] at e
      have e2 : G.S t (G.S (-t) (S t x)) = G.S t x := by rw [← e]
      rw [← G.map_add_apply, add_neg_cancel, G.map_zero] at e2
      exact e2
  have := Continuous.ext_on hD (S t).continuous (G.S t).continuous fun x hx => hdom x hx
  exact ContinuousLinearMap.ext fun x => congrFun this x

end Group

/-! ### Strong solutions on `[0, ∞)` -/

omit [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] in
theorem mem_nhdsWithin_Ici_Icc (t : ℝ) : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t :=
  mem_nhdsWithin.2 ⟨Iio (t + 1), isOpen_Iio, show t < t + 1 by linarith,
    fun _ ⟨h1, h2⟩ => ⟨h2, le_of_lt h1⟩⟩

/-- A strong solution on `[0, ∞)` is one on every `[0, T]`. -/
theorem IsStrongSolution.mono_Icc {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {L : SetRel X X} {U : ℝ → X} (hU : IsStrongSolution L (Ici 0) U) (T : ℝ) :
    IsStrongSolution L (Icc 0 T) U :=
  hU.mono Icc_subset_Ici_self

/-- Strong solutions on every `[0, T]` are one on `[0, ∞)`. -/
theorem isStrongSolution_Ici {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {L : SetRel X X} {U : ℝ → X} (hU : ∀ T, IsStrongSolution L (Icc 0 T) U) :
    IsStrongSolution L (Ici 0) U := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact ((hU (t + 1)).1 t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_Ici_Icc t)
  · obtain ⟨V, hV, hd⟩ := (hU (t + 1)).2 t ⟨ht, by linarith⟩
    exact ⟨V, hV, hd.mono_of_mem_nhdsWithin (mem_nhdsWithin_Ici_Icc t)⟩

/-! ### Semigroups -/

section Semigroup

variable (G : Feec.C0Semigroup 𝕜 E)

/-- **Strong solutions on `[0, T]` are the orbits of the semigroup.** -/
theorem eqOn_semigroup {x : E} (hx : x ∈ G.generator.domain) {T : ℝ} {u : ℝ → E} (hu0 : u 0 = x)
    (hu : IsStrongSolution G.generator.graph (Icc 0 T) u) :
    EqOn u (fun t => G.S t x) (Icc 0 T) := by
  have h1 := isStrongSolution_graph_iff.1 hu
  have h2 := (G.isClassicalSolution_orbit (U₀ := x) hx 0 T).toIsStrongSolution
  have e := G.isStrongSolution_unique (F := 0) h1 h2 continuousOn_const
    (by simp [hu0, G.map_zero])
  intro t ht
  rw [e ht]
  simp

/-- **The orbits of a semigroup are strong solutions on `[0, ∞)`** of its generator. -/
theorem isEvolution_semigroup : IsEvolution 𝕜 G.generator.graph (Ici 0) G.S := by
  refine ⟨fun x => by rw [G.map_zero]; rfl, fun x y hxy => isStrongSolution_Ici fun T => ?_⟩
  have hx : x ∈ G.generator.domain := LinearPMap.mem_domain_of_mem_graph hxy
  have h := (G.isClassicalSolution_orbit (U₀ := x) hx 0 T).toIsStrongSolution
  refine (isStrongSolution_graph_iff.2 h).congr' fun t _ => ?_
  simp

/-- **Every evolution of a semigroup generator on `[0, ∞)` is the semigroup** at `t ≥ 0`, when the
generator is densely defined. -/
theorem eq_semigroup_of_isEvolution (hD : Dense (G.generator.domain : Set E))
    {S : ℝ → E →L[𝕜] E} (hS : IsEvolution 𝕜 G.generator.graph (Ici 0) S) {t : ℝ} (ht : 0 ≤ t) :
    S t = G.S t := by
  have hdom : ∀ x ∈ G.generator.domain, S t x = G.S t x := fun x hx =>
    eqOn_semigroup G hx (hS.1 x) ((hS.2 x _ (G.generator.mem_graph ⟨x, hx⟩)).mono_Icc t)
      ⟨ht, le_rfl⟩
  have := Continuous.ext_on hD (S t).continuous (G.S t).continuous fun x hx => hdom x hx
  exact ContinuousLinearMap.ext fun x => congrFun this x

end Semigroup

/-! ### The criterion -/

omit [IsScalarTower ℝ 𝕜 E] in
/-- **Stone's group and its invariant subspaces.** -/
theorem group_of (L : E →ₗ.[𝕜] E) (hL : Dense (L.domain : Set E)) (hskew : L† = -L) :
    ∃ S, IsEvolution 𝕜 L.graph univ S ∧ (∀ S', IsEvolution 𝕜 L.graph univ S' → S' = S) ∧
      (∀ t x, ‖S t x‖ = ‖x‖) ∧
      (∀ x ∈ L.domain, ∀ T (u : ℝ → E), u 0 = x → IsStrongSolution L.graph (Icc 0 T) u →
        EqOn u (fun t => S t x) (Icc 0 T)) ∧
      ∀ (K : Submodule 𝕜 E) [K.HasOrthogonalProjection],
        (IsReducing L K ↔ ∀ t, ∀ x ∈ K, S t x ∈ K) ∧
        (IsReducing L K ↔ (∀ t, 0 ≤ t → ∀ x ∈ K, S t x ∈ K) ∧
          ∀ t, 0 ≤ t → ∀ x ∈ Kᗮ, S t x ∈ Kᗮ) ∧
        ∃ (Ks : Submodule 𝕜 E) (_ : Ks.HasOrthogonalProjection),
          (Ks : Set E) = invariantCore S K ∧ IsReducing L Ks ∧
          ∀ (M : Submodule 𝕜 E) [M.HasOrthogonalProjection], M ≤ K → IsReducing L M → M ≤ Ks := by
  have := RCLike.isScalarTower_of_normedSpace (𝕜 := 𝕜) (E := E)
  have hA : L.IsSkewAdjoint := hskew
  set G := hA.group
  have hG : G.IsIsometric := hA.isIsometric_group
  have hgen : G.generator = L := hA.generator_group
  have hD : Dense (G.generator.domain : Set E) := hgen ▸ hL
  -- Stone's group is the Lumer–Phillips semigroup of `L` at `t ≥ 0`
  have hM : L.IsMDissipative := hA.isMDissipative
  have hMgen : hM.semigroup.generator = L := hM.generator_semigroup
  have hSS : ∀ t, 0 ≤ t → G.S t = hM.semigroup.S t := by
    intro t ht
    have hev : IsEvolution 𝕜 hM.semigroup.generator.graph (Ici 0) G.S := by
      rw [hMgen, ← hgen]; exact (isEvolution_group G).mono (subset_univ _)
    have hD' : Dense (hM.semigroup.generator.domain : Set E) := by rw [hMgen]; exact hL
    exact eq_semigroup_of_isEvolution hM.semigroup hD' hev ht
  refine ⟨G.S, hgen ▸ isEvolution_group G, fun S' hS' => eq_group_of_isEvolution G hD
    (hgen ▸ hS'), hG, fun x hx T u hu0 hu => eqOn_group G (hgen ▸ hx) hu0 (hgen ▸ hu),
    fun K _ => ⟨?_, ?_, ?_⟩⟩
  · rw [isReducing_iff, ← hgen, hG.isReducing_iff_invariant, Feec.C0Group.map_le_iff_forall]
  · rw [isReducing_iff, hM.isReducing_iff]
    refine and_congr (forall₂_congr fun t ht => ?_) (forall₂_congr fun t ht => ?_) <;>
      rw [hSS t ht]
  · refine ⟨G.invariantCore K, inferInstance, ?_, ?_, fun M _ hMK hM => ?_⟩
    · ext x; exact Feec.C0Group.mem_invariantCore
    · rw [isReducing_iff, ← hgen]; exact hG.isReducing_invariantCore
    · exact hG.le_invariantCore_of_isReducing hMK (by rw [hgen, ← isReducing_iff]; exact hM)

omit [IsScalarTower ℝ 𝕜 E] in
/-- **The Lumer–Phillips semigroup and its reducing subspaces.** -/
theorem semigroup_of (A : E →ₗ.[𝕜] E) (hdiss : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hsurj : ∀ y, ∃ x : A.domain, (x : E) - A x = y) :
    ∃ S, IsEvolution 𝕜 A.graph (Ici 0) S ∧
      (∀ S', IsEvolution 𝕜 A.graph (Ici 0) S' → ∀ t, 0 ≤ t → S' t = S t) ∧
      (∀ t, 0 ≤ t → ∀ x, ‖S t x‖ ≤ ‖x‖) ∧
      (∀ x ∈ A.domain, ∀ T (u : ℝ → E), u 0 = x → IsStrongSolution A.graph (Icc 0 T) u →
        EqOn u (fun t => S t x) (Icc 0 T)) ∧
      ∀ (K : Submodule 𝕜 E) [K.HasOrthogonalProjection],
        IsReducing A K ↔ (∀ t, 0 ≤ t → ∀ x ∈ K, S t x ∈ K) ∧
          ∀ t, 0 ≤ t → ∀ x ∈ Kᗮ, S t x ∈ Kᗮ := by
  have := RCLike.isScalarTower_of_normedSpace (𝕜 := 𝕜) (E := E)
  have hA : A.IsMDissipative := ⟨hdiss, ⟨1, one_pos, fun y => by
    obtain ⟨x, hx⟩ := hsurj y; exact ⟨x, by simpa using hx⟩⟩⟩
  set G := hA.semigroup
  have hgen : G.generator = A := hA.generator_semigroup
  refine ⟨G.S, hgen ▸ isEvolution_semigroup G, fun S' hS' t ht =>
    eq_semigroup_of_isEvolution G G.dense_domain_generator (hgen ▸ hS') ht,
    fun t ht x => ?_, fun x hx T u hu0 hu => eqOn_semigroup G (hgen ▸ hx) hu0 (hgen ▸ hu),
    fun K _ => ?_⟩
  · exact ((G.S t).le_opNorm x).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hA.isContraction_semigroup t ht))
  · rw [isReducing_iff, hA.isReducing_iff]

end FEEC
