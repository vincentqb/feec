module

public import Solution.Absorbing
public import Feec.Semigroup.Invariance
public import Feec.Semigroup.DissipativeInvariance
public import Feec.Semigroup.LumerPhillips
public import Feec.Semigroup.Stone
public import Feec.Evolution.Solution

/-!
# The general criterion (solution)

The mild solutions of `u' = A u` are the orbits of the group (skew-adjoint `A`, Stone) or of the
semigroup (m-dissipative `A`, Lumer–Phillips) that `A` generates (`isMildSolution_univ_iff`,
`isMildSolution_Ici_iff`): an orbit is a mild solution (`∫₀ᵗ S τ x ∈ D(A)` with
`A ∫₀ᵗ S τ x = S t x - x`, for `t < 0` through `∫₀ᵗ S τ x = -S t ∫₀^{-t} S σ x`), and the
difference `w = ∫₀^· u - ∫₀^· S τ (u 0)` of the primitives of a mild solution and of the orbit
solves `w' = A w`, `w 0 = 0`, so vanishes (the energy argument, resp. uniqueness for a dissipative
generator). The criterion is then that of `Feec`: `C0Group.IsIsometric.isReducing_iff_invariant`,
the invariant core `C0Group.invariantCore` and `LinearPMap.IsMDissipative.isReducing_iff`.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4, §1.10, §4.2
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Filter LinearPMap

@[expose] public noncomputable section

namespace FEEC.ConstraintPropagation

open Feec

/-! ### Mild solutions under an isomorphism -/

/-- **Mild solutions are carried by an isomorphism of the graphs.** -/
theorem isMildSolution_congr {𝕜' X Y : Type*} [RCLike 𝕜'] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedSpace 𝕜' X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedSpace 𝕜' Y] (e : X ≃L[𝕜'] Y) {L : X → X → Prop}
    {M : Y → Y → Prop} (hLM : ∀ x y, L x y ↔ M (e x) (e y)) {I : Set ℝ} {U : ℝ → X} :
    IsMildSolution L I U ↔ IsMildSolution M I fun t => e (U t) := by
  have hint : ∀ t, ∫ τ in (0 : ℝ)..t, e (U τ) = e (∫ τ in (0 : ℝ)..t, U τ) := fun t => by
    simp only [intervalIntegral, e.integral_comp_comm, _root_.map_sub]
  constructor
  · rintro ⟨hc, hm⟩
    refine ⟨e.continuous.comp_continuousOn hc, fun t ht => ?_⟩
    rw [hint, ← _root_.map_sub]
    exact (hLM _ _).1 (hm t ht)
  · rintro ⟨hc, hm⟩
    refine ⟨by simpa [Function.comp_def] using e.symm.continuous.comp_continuousOn hc,
      fun t ht => (hLM _ _).2 ?_⟩
    rw [← hint, _root_.map_sub]
    exact hm t ht

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

/-! ### The definitions are those of `Feec` -/

omit [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
theorem isSkewAdjoint_iff {A : H →ₗ.[𝕜] H} : IsSkewAdjoint A ↔ A.IsSkewAdjoint := Iff.rfl

omit [CompleteSpace H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
theorem isReducing_iff {A : H →ₗ.[𝕜] H} {K : Submodule 𝕜 H} [K.HasOrthogonalProjection] :
    IsReducing A K ↔ A.IsReducing K :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.proj_mem x, h.comm x⟩⟩

omit [CompleteSpace H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
theorem IsMDissipative.toFeec {A : H →ₗ.[𝕜] H} (h : IsMDissipative A) : A.IsMDissipative :=
  ⟨h.1, 1, one_pos, fun y => by
    obtain ⟨x, hx⟩ := h.2 y
    exact ⟨x, by rwa [RCLike.ofReal_one, one_smul]⟩⟩

/-! ### Groups: mild solutions are orbits -/

omit [CompleteSpace H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
theorem mem_graph_iff'' {A : H →ₗ.[𝕜] H} {x y : H} :
    (x, y) ∈ A.graph ↔ ∃ h : x ∈ A.domain, A ⟨x, h⟩ = y :=
  ⟨fun h => ⟨LinearPMap.mem_domain_of_mem_graph h,
    ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph h)).2 h).symm⟩,
   fun ⟨h, e⟩ => e ▸ A.mem_graph ⟨x, h⟩⟩

/-- `∫₀ᵗ S τ x ∈ D(A)` with `A ∫₀ᵗ S τ x = S t x - x`, for every `t ∈ ℝ`. -/
theorem orbit_integral_mem_graph (G : C0Group 𝕜 H) (x : H) (t : ℝ) :
    (∫ τ in (0 : ℝ)..t, G.S τ x, G.S t x - x) ∈ G.generator.graph := by
  rcases le_total 0 t with ht | ht
  · exact G.toC0Semigroup.integral_mem_graph_S ht x
  · set y := ∫ σ in (0 : ℝ)..-t, G.S σ x
    have hgr : (y, G.S (-t) x - x) ∈ G.generator.graph :=
      G.toC0Semigroup.integral_mem_graph_S (neg_nonneg.2 ht) x
    obtain ⟨hy, ey⟩ := mem_graph_iff''.1 hgr
    have hi : IntervalIntegrable (fun σ => G.S σ x) MeasureTheory.volume 0 (-t) :=
      (G.strongCont x).intervalIntegrable _ _
    have e1 : G.S t y = ∫ τ in t..0, G.S τ x := by
      rw [← (G.S t).intervalIntegral_comp_comm hi]
      have := intervalIntegral.integral_comp_add_left (fun τ => G.S τ x) t (a := 0) (b := -t)
      rw [add_zero, add_neg_cancel] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      rw [G.map_add]; rfl
    have e2 : ∫ τ in (0 : ℝ)..t, G.S τ x = -G.S t y := by
      rw [e1, intervalIntegral.integral_symm]
    have hA : G.generator ⟨G.S t y, G.mapsTo_domain ⟨y, hy⟩ t⟩ = x - G.S t x := by
      rw [G.generator_apply_S ⟨y, hy⟩ t, ey, _root_.map_sub, G.S_apply_S_neg]
    rw [e2, show G.S t x - x = -(x - G.S t x) by abel]
    have := G.generator.graph.neg_mem (G.generator.mem_graph ⟨_, G.mapsTo_domain ⟨y, hy⟩ t⟩)
    rwa [hA] at this

/-- **For an isometric group the mild solutions on `ℝ` are the orbits.** -/
theorem isMildSolution_univ_iff {G : C0Group 𝕜 H} (hG : G.IsIsometric) {A : H →ₗ.[𝕜] H}
    (hgen : G.generator = A) {u : ℝ → H} :
    IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u ↔ ∀ t, u t = G.S t (u 0) := by
  subst hgen
  constructor
  · rintro ⟨hc, hm⟩ t
    have hc' : Continuous u := continuousOn_univ.1 hc
    set x := u 0
    set w : ℝ → H := fun s => (∫ τ in (0 : ℝ)..s, u τ) - ∫ τ in (0 : ℝ)..s, G.S τ x
    have hg : ∀ s, (w s, u s - G.S s x) ∈ G.generator.graph := fun s => by
      have := G.generator.graph.sub_mem (hm s (mem_univ s)) (orbit_integral_mem_graph G x s)
      simpa only [Prod.mk_sub_mk, sub_sub_sub_cancel_right] using this
    have hmem : ∀ s, w s ∈ G.generator.domain := fun s => (mem_graph_iff''.1 (hg s)).1
    have hval : ∀ s, G.generator ⟨w s, hmem s⟩ = u s - G.S s x := fun s =>
      (mem_graph_iff''.1 (hg s)).2
    have hde : ∀ s, HasDerivAt w (G.generator ⟨w s, hmem s⟩) s := fun s => by
      rw [hval]
      exact (hc'.integral_hasStrictDerivAt 0 s).hasDerivAt.sub
        ((G.strongCont x).integral_hasStrictDerivAt 0 s).hasDerivAt
    have h0 := hG.isSkewSymmetric_generator.eq_zero_of_hasDerivAt hmem hde
      (by simp [w]) t
    have : (⟨w t, hmem t⟩ : G.generator.domain) = 0 := Subtype.ext h0
    rw [← sub_eq_zero, ← hval, this, LinearPMap.map_zero]
  · intro h
    have hu : u = fun t => G.S t (u 0) := funext h
    rw [hu]
    refine ⟨(G.strongCont _).continuousOn, fun t _ => ?_⟩
    change (∫ τ in (0 : ℝ)..t, G.S τ (u 0), G.S t (u 0) - G.S 0 (u 0)) ∈ G.generator.graph
    rw [G.map_zero, one_apply_eq_self]
    exact orbit_integral_mem_graph G _ t

/-! ### Semigroups with a dissipative generator: mild solutions are orbits -/

/-- **For a semigroup with dissipative generator the mild solutions on `[0, ∞)` are the
orbits.** -/
theorem isMildSolution_Ici_iff {G : C0Semigroup 𝕜 H} {A : H →ₗ.[𝕜] H} (hgen : G.generator = A)
    (hA : A.IsDissipative) {u : ℝ → H} :
    IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u ↔
      ∀ t ∈ Ici (0 : ℝ), u t = G.S t (u 0) := by
  subst hgen
  constructor
  · rintro ⟨hc, hm⟩ t ht
    set x := u 0
    have hsol : ∀ w : ℝ → H, ContinuousOn w (Ici 0) →
        (∀ τ ∈ Ici (0 : ℝ), ((∫ s in (0 : ℝ)..τ, w s), w τ - x) ∈ G.generator.graph) →
        Evolution.IsStrongSolution G.generator (Icc 0 t) (fun _ => x)
          (fun τ => ∫ s in (0 : ℝ)..τ, w s) := fun w hw hg =>
      Evolution.IsStrongSolution.of_deriv fun τ hτ => ⟨w τ - x, hg τ hτ.1, by
        simpa using hasDerivWithinAt_integral_of_continuousOn (hw.mono Icc_subset_Ici_self) hτ⟩
    have hgS : ∀ τ ∈ Ici (0 : ℝ), ((∫ s in (0 : ℝ)..τ, G.S s x), G.S τ x - x) ∈ G.generator.graph :=
      fun τ hτ => G.integral_mem_graph_S hτ x
    have e := (hsol _ hc hm).unique hA (hsol _ (G.strongCont x) hgS) (by simp) ⟨ht, le_rfl⟩
    exact sub_left_inj.1 (G.generator.mem_graph_snd_inj (hm t ht) (hgS t ht) e)
  · intro h
    have hc : ContinuousOn u (Ici 0) := (G.strongCont (u 0)).congr fun t ht => h t ht
    refine ⟨hc, fun t ht => ?_⟩
    have e1 : ∫ τ in (0 : ℝ)..t, u τ = ∫ τ in (0 : ℝ)..t, G.S τ (u 0) :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [uIcc_of_le ht] at hτ
        exact h τ hτ.1
    rw [e1, h t ht]
    exact G.integral_mem_graph_S ht _

/-- Propagation of a set by the mild solutions is its invariance under the orbits. -/
theorem forall_isMildSolution_univ_iff {G : C0Group 𝕜 H} (hG : G.IsIsometric)
    {A : H →ₗ.[𝕜] H} (hgen : G.generator = A) (P : Set H) :
    (∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u → u 0 ∈ P → ∀ t, u t ∈ P) ↔
      ∀ t, ∀ x ∈ P, G.S t x ∈ P := by
  constructor
  · intro h t x hx
    have hm := (isMildSolution_univ_iff hG hgen (u := fun t => G.S t x)).2 fun t => by
      simp [G.map_zero]
    exact h _ hm (by simpa [G.map_zero] using hx) t
  · intro h u hu h0 t
    rw [(isMildSolution_univ_iff hG hgen).1 hu t]
    exact h t _ h0

theorem forall_isMildSolution_Ici_iff {G : C0Semigroup 𝕜 H} {A : H →ₗ.[𝕜] H}
    (hgen : G.generator = A) (hA : A.IsDissipative) (P : Set H) :
    (∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u → u 0 ∈ P →
        ∀ t ∈ Ici (0 : ℝ), u t ∈ P) ↔ ∀ t, 0 ≤ t → ∀ x ∈ P, G.S t x ∈ P := by
  constructor
  · intro h t ht x hx
    have hm := (isMildSolution_Ici_iff hgen hA (u := fun t => G.S t x)).2 fun t _ => by simp
    exact h _ hm (by simpa using hx) t ht
  · intro h u hu h0 t ht
    rw [(isMildSolution_Ici_iff hgen hA).1 hu t ht]
    exact h t ht _ h0

/-! ### The criterion -/

theorem existsUnique_mild {A : H →ₗ.[𝕜] H} (hA : IsSkewAdjoint A) (x : H) :
    ∃! u : ℝ → H, u 0 = x ∧ IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u := by
  have hA' : A.IsSkewAdjoint := hA
  have hm : ∀ u : ℝ → H, _ ↔ _ := fun u =>
    isMildSolution_univ_iff (u := u) hA'.isIsometric_group hA'.generator_group
  refine ⟨fun t => hA'.group.S t x, ⟨by simp [C0Group.map_zero], (hm _).2 fun t => by
    simp [C0Group.map_zero]⟩, fun v ⟨hv0, hv⟩ => funext fun t => ?_⟩
  rw [(hm v).1 hv t, hv0]

theorem isReducing_iff_propagates {A : H →ₗ.[𝕜] H} (hA : IsSkewAdjoint A) (K : Submodule 𝕜 H)
    [K.HasOrthogonalProjection] :
    IsReducing A K ↔ ∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u →
      u 0 ∈ K → ∀ t, u t ∈ K := by
  have hA' : A.IsSkewAdjoint := hA
  obtain ⟨G, hG, rfl⟩ : ∃ G : C0Group 𝕜 H, G.IsIsometric ∧ G.generator = A :=
    ⟨hA'.group, hA'.isIsometric_group, hA'.generator_group⟩
  rw [isReducing_iff, hG.isReducing_iff_invariant, C0Group.map_le_iff_forall]
  exact (forall_isMildSolution_univ_iff hG rfl (K : Set H)).symm

theorem exists_invariantCore {A : H →ₗ.[𝕜] H} (hA : IsSkewAdjoint A) (K : Submodule 𝕜 H)
    [K.HasOrthogonalProjection] :
    ∃ (Ks : Submodule 𝕜 H) (_ : Ks.HasOrthogonalProjection),
      (∀ x, x ∈ Ks ↔ ∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u →
        u 0 = x → ∀ t, u t ∈ K) ∧
      Ks ≤ K ∧ IsReducing A Ks ∧
      (∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) univ u →
        u 0 ∈ Ks → ∀ t, u t ∈ Ks) ∧
      (∀ x : A.domain, (x : H) ∈ Ks → A x ∈ Ks) ∧
      (Ks : Set H) ⊆ closure ((A.domain : Set H) ∩ Ks) ∧
      ∀ (M : Submodule 𝕜 H) [M.HasOrthogonalProjection], M ≤ K → IsReducing A M → M ≤ Ks := by
  have hA' : A.IsSkewAdjoint := hA
  obtain ⟨G, hG, rfl⟩ : ∃ G : C0Group 𝕜 H, G.IsIsometric ∧ G.generator = A :=
    ⟨hA'.group, hA'.isIsometric_group, hA'.generator_group⟩
  refine ⟨G.invariantCore K, inferInstance, fun x => ?_, C0Group.invariantCore_le,
    isReducing_iff.2 hG.isReducing_invariantCore, fun u hu h0 t => ?_,
    fun x hx => hG.apply_mem_invariantCore x hx,
    fun k hk => hG.mem_closure_domain_inter_invariantCore hk,
    fun M _ hMK hM => hG.le_invariantCore_of_isReducing hMK (isReducing_iff.1 hM)⟩
  · rw [C0Group.mem_invariantCore]
    constructor
    · intro h u hu h0 t
      rw [(isMildSolution_univ_iff hG rfl).1 hu t, h0]
      exact h t
    · intro h t
      exact h (fun t => G.S t x) ((isMildSolution_univ_iff hG rfl).2 fun t => by
        simp [C0Group.map_zero]) (by simp [C0Group.map_zero]) t
  · rw [(isMildSolution_univ_iff hG rfl).1 hu t]
    exact C0Group.S_mem_invariantCore h0 t

theorem existsUnique_mild_of_isMDissipative {A : H →ₗ.[𝕜] H} (hA : IsMDissipative A) (x : H) :
    (∃ u : ℝ → H, u 0 = x ∧ IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u) ∧
      ∀ u v : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u →
        IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) v → u 0 = v 0 →
          EqOn u v (Ici 0) := by
  have hA' := hA.toFeec
  have hm : ∀ u : ℝ → H, _ ↔ _ := fun u =>
    isMildSolution_Ici_iff (u := u) hA'.generator_semigroup hA'.dissipative
  refine ⟨⟨fun t => hA'.semigroup.S t x, by simp, (hm _).2 fun t _ => by simp⟩,
    fun u v hu hv h0 t ht => ?_⟩
  rw [(hm u).1 hu t ht, (hm v).1 hv t ht, h0]

theorem isReducing_iff_propagates_of_isMDissipative {A : H →ₗ.[𝕜] H} (hA : IsMDissipative A)
    (K : Submodule 𝕜 H) [K.HasOrthogonalProjection] :
    IsReducing A K ↔
      (∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u →
        u 0 ∈ K → ∀ t ∈ Ici (0 : ℝ), u t ∈ K) ∧
      ∀ u : ℝ → H, IsMildSolution (fun v w => (v, w) ∈ A.graph) (Ici 0) u →
        u 0 ∈ Kᗮ → ∀ t ∈ Ici (0 : ℝ), u t ∈ Kᗮ := by
  have hA' := hA.toFeec
  rw [isReducing_iff, hA'.isReducing_iff]
  exact and_congr
    (forall_isMildSolution_Ici_iff hA'.generator_semigroup hA'.dissipative (K : Set H)).symm
    (forall_isMildSolution_Ici_iff hA'.generator_semigroup hA'.dissipative (Kᗮ : Set H)).symm

end FEEC.ConstraintPropagation
