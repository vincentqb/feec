module

public import Feec.ForMathlib.LinearPMap.GraphSpace
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Range, kernel and adjoint; the closed range theorem

For a closed densely defined operator `T` between Hilbert spaces: the orthogonality relations
between the ranges and kernels of `T` and `T†` ([QuennevilleBelair2015], (4.1)), the Poincaré
inequality on `D(T) ∩ N(T)ᗮ` as a characterization of closed range, and the closed range theorem.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem orthogonal_range_eq_ker_adjoint (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) :
    (LinearMap.range T.toFun)ᗮ = T†.ker := by
  ext y
  constructor
  · intro hy
    have key : ∀ x : T.domain, ⟪(0 : E), (x : E)⟫_𝕜 = ⟪y, T x⟫_𝕜 := fun x => by
      rw [inner_zero_left]
      exact (inner_eq_zero_symm.1 ((Submodule.mem_orthogonal _ _).1 hy (T x) ⟨x, rfl⟩)).symm
    have hmem : y ∈ T†.domain := mem_adjoint_domain_of_exists y ⟨0, key⟩
    rw [LinearPMap.mem_ker_iff]
    exact ⟨⟨y, hmem⟩, rfl, adjoint_apply_eq hT ⟨y, hmem⟩ key⟩
  · intro hy
    rw [LinearPMap.mem_ker_iff] at hy
    obtain ⟨y', rfl, hy0⟩ := hy
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    have := (adjoint_isFormalAdjoint hT) y' x
    rw [hy0, inner_zero_left] at this
    exact inner_eq_zero_symm.1 this.symm

theorem orthogonal_ker_adjoint [CompleteSpace F] (T : E →ₗ.[𝕜] F)
    (hT : Dense (T.domain : Set E)) :
    T†.kerᗮ = (LinearMap.range T.toFun).topologicalClosure := by
  rw [← orthogonal_range_eq_ker_adjoint T hT, Submodule.orthogonal_orthogonal_eq_closure]

variable [CompleteSpace F]

theorem orthogonal_range_adjoint (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) : (LinearMap.range T†.toFun)ᗮ = T.ker := by
  ext x
  have hk : x ∈ T.ker ↔ (x, (0 : F)) ∈ T.graph := by
    rw [← SetLike.mem_coe, ker_eq_preimage_graph]; rfl
  rw [hk, mem_graph_iff_of_isClosed hT hc, Submodule.mem_orthogonal]
  simp only [inner_zero_right, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
  rfl

theorem orthogonal_ker (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (hc : T.IsClosed) :
    T.kerᗮ = (LinearMap.range T†.toFun).topologicalClosure := by
  rw [← orthogonal_range_adjoint T hT hc, Submodule.orthogonal_orthogonal_eq_closure]

end LinearPMap

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem exists_mem_orthogonal_ker_eq {T : E →ₗ.[𝕜] F} (hc : T.IsClosed) (x : T.domain) :
    ∃ z : T.domain, (z : E) ∈ T.kerᗮ ∧ T z = T x := by
  have : CompleteSpace T.ker := (isClosed_ker hc).completeSpace_coe
  have hK : T.ker.starProjection (x : E) ∈ T.ker := T.ker.starProjection_apply_mem _
  refine ⟨x - ⟨_, T.ker_le_domain hK⟩, Submodule.sub_starProjection_mem_orthogonal (x : E), ?_⟩
  rw [LinearPMap.map_sub, (LinearPMap.coe_mem_ker_iff (x := ⟨_, T.ker_le_domain hK⟩)).1 hK,
    sub_zero]

omit [CompleteSpace E] [CompleteSpace F] in
theorem eq_of_mem_orthogonal_ker {T : E →ₗ.[𝕜] F} {x x' : T.domain} (hx : (x : E) ∈ T.kerᗮ)
    (hx' : (x' : E) ∈ T.kerᗮ) (h : T x = T x') : x = x' := by
  have h3 : ((x - x' : T.domain) : E) ∈ T.ker ⊓ T.kerᗮ :=
    ⟨(LinearPMap.coe_mem_ker_iff).2 (by rw [LinearPMap.map_sub, h, sub_self]), sub_mem hx hx'⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h3
  exact sub_eq_zero.1 (Subtype.ext h3)

theorem exists_rightInverse_of_isClosed_range (T : E →ₗ.[𝕜] F) (hc : T.IsClosed)
    (hR : _root_.IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ g : LinearMap.range T.toFun →L[𝕜] E,
      ∀ y, g y ∈ T.kerᗮ ∧ ∃ hy : g y ∈ T.domain, T ⟨g y, hy⟩ = y := by
  have : CompleteSpace (LinearMap.range T.toFun) := hR.completeSpace_coe
  let D₀ : Submodule 𝕜 E := T.domain ⊓ T.kerᗮ
  let T₀ : D₀ →ₗ[𝕜] LinearMap.range T.toFun :=
    LinearMap.codRestrict _ (T.toFun.comp (Submodule.inclusion inf_le_left))
      (fun z => LinearMap.mem_range_self _ _)
  have hinj : Function.Injective T₀ := by
    intro z z' hzz'
    have := eq_of_mem_orthogonal_ker (T := T) (x := Submodule.inclusion inf_le_left z)
      (x' := Submodule.inclusion inf_le_left z') z.2.2 z'.2.2 (congrArg Subtype.val hzz')
    exact Subtype.ext (congrArg (fun w : T.domain => (w : E)) this)
  have hsurj : Function.Surjective T₀ := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨z, hz, hTz⟩ := exists_mem_orthogonal_ker_eq hc x
    exact ⟨⟨z, z.2, hz⟩, Subtype.ext hTz⟩
  let e := LinearEquiv.ofBijective T₀ ⟨hinj, hsurj⟩
  let g₀ : LinearMap.range T.toFun →ₗ[𝕜] E := D₀.subtype.comp e.symm.toLinearMap
  have hg₀ : ∀ y, g₀ y ∈ T.kerᗮ ∧ ∃ hy : g₀ y ∈ T.domain, T ⟨g₀ y, hy⟩ = y := fun y =>
    ⟨(e.symm y).2.2, (e.symm y).2.1, congrArg Subtype.val (e.apply_symm_apply y)⟩
  have hgraph : _root_.IsClosed (g₀.graph : Set (LinearMap.range T.toFun × E)) := by
    have hset : (g₀.graph : Set (LinearMap.range T.toFun × E)) =
        {p | (p.2, (p.1 : F)) ∈ T.graph} ∩ {p | p.2 ∈ T.kerᗮ} := by
      ext ⟨y, x⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl
        obtain ⟨hk, hd, hT⟩ := hg₀ y
        exact ⟨(LinearPMap.mem_graph_iff _).2 ⟨⟨_, hd⟩, rfl, hT⟩, hk⟩
      · rintro ⟨hg, hk⟩
        obtain ⟨z, hz, hTz⟩ := (LinearPMap.mem_graph_iff _).1 hg
        simp only at hz hTz
        have hw : x ∈ D₀ := ⟨hz ▸ z.2, hk⟩
        have he : e.symm y = ⟨x, hw⟩ := by
          rw [LinearEquiv.symm_apply_eq]
          apply Subtype.ext
          change (y : F) = T ⟨x, hw.1⟩
          rw [← hTz]
          congr 1
          exact Subtype.ext hz
        change x = ((e.symm y : D₀) : E)
        rw [he]
    rw [hset]
    exact (hc.preimage (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))).inter
      ((Submodule.isClosed_orthogonal _).preimage continuous_snd)
  exact ⟨⟨g₀, g₀.continuous_of_isClosed_graph hgraph⟩, hg₀⟩

/-- **Poincaré inequality** for a closed operator with closed range: `‖x‖ ≤ c ‖T x‖` on
`D(T) ∩ N(T)ᗮ` ([QuennevilleBelair2015], Thm 4.2). -/
theorem exists_norm_le_of_isClosed_range {T : E →ₗ.[𝕜] F} (hc : T.IsClosed)
    (hR : _root_.IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ c, ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖ := by
  obtain ⟨g, hg⟩ := exists_rightInverse_of_isClosed_range T hc hR
  refine ⟨‖g‖, fun x hx => ?_⟩
  have hy : T x ∈ LinearMap.range T.toFun := ⟨x, rfl⟩
  obtain ⟨hk, hd, hT⟩ := hg ⟨T x, hy⟩
  have hgx : (⟨g ⟨T x, hy⟩, hd⟩ : T.domain) = x := eq_of_mem_orthogonal_ker hk hx hT
  have hgx' : g ⟨T x, hy⟩ = (x : E) := congrArg Subtype.val hgx
  calc ‖(x : E)‖ = ‖g ⟨T x, hy⟩‖ := by rw [hgx']
    _ ≤ ‖g‖ * ‖(⟨T x, hy⟩ : LinearMap.range T.toFun)‖ := g.le_opNorm _
    _ = ‖g‖ * ‖T x‖ := rfl

theorem isClosed_range_of_norm_le {T : E →ₗ.[𝕜] F} (hc : T.IsClosed) {c : ℝ}
    (hP : ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) := by
  let G : Submodule 𝕜 (E × F) := T.graph ⊓ T.kerᗮ.comap (LinearMap.fst 𝕜 E F)
  have hG : _root_.IsClosed (G : Set (E × F)) :=
    hc.inter ((Submodule.isClosed_orthogonal _).preimage continuous_fst)
  have : CompleteSpace G := hG.completeSpace_coe
  let π : G →L[𝕜] F := (ContinuousLinearMap.snd 𝕜 E F).comp G.subtypeL
  have hbound : ∀ p : G, ‖p‖ ≤ (max c 1).toNNReal * ‖π p‖ := by
    rintro ⟨⟨a, b⟩, hab, ha⟩
    obtain ⟨x, hx, hTx⟩ := (LinearPMap.mem_graph_iff _).1 hab
    simp only at hx hTx
    have h1 : ‖a‖ ≤ c * ‖b‖ := by rw [← hx, ← hTx]; exact hP x (hx ▸ ha)
    rw [Real.coe_toNNReal _ (le_trans zero_le_one (le_max_right _ _))]
    change ‖((a, b) : E × F)‖ ≤ max c 1 * ‖b‖
    refine norm_prod_le_iff.2 ⟨h1.trans ?_,
      le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hrange : Set.range π = (LinearMap.range T.toFun : Set F) := by
    ext y
    constructor
    · rintro ⟨⟨⟨a, b⟩, hab, ha⟩, rfl⟩
      obtain ⟨x, -, hTx⟩ := (LinearPMap.mem_graph_iff _).1 hab
      exact ⟨x, hTx⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨z, hz, hTz⟩ := exists_mem_orthogonal_ker_eq hc x
      exact ⟨⟨((z : E), T z), T.mem_graph z, hz⟩, hTz⟩
  rw [← hrange]
  exact (π.antilipschitz_of_bound hbound).isClosed_range π.uniformContinuous

theorem isClosed_range_iff_exists_norm_le {T : E →ₗ.[𝕜] F} (hc : T.IsClosed) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) ↔
      ∃ c, ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖ :=
  ⟨exists_norm_le_of_isClosed_range hc, fun ⟨_, h⟩ => isClosed_range_of_norm_le hc h⟩

theorem range_adjoint_eq_orthogonal_ker (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) (hR : _root_.IsClosed (LinearMap.range T.toFun : Set F)) :
    LinearMap.range T†.toFun = T.kerᗮ := by
  apply le_antisymm
  · rw [orthogonal_ker T hT hc]; exact Submodule.le_topologicalClosure _
  · intro f hf
    obtain ⟨g, hg⟩ := exists_rightInverse_of_isClosed_range T hc hR
    have : CompleteSpace (LinearMap.range T.toFun) := hR.completeSpace_coe
    let φ : StrongDual 𝕜 (LinearMap.range T.toFun) := (innerSL 𝕜 f).comp g
    let y₀ : LinearMap.range T.toFun := (InnerProductSpace.toDual 𝕜 _).symm φ
    have key : ∀ x : T.domain, ⟪f, (x : E)⟫_𝕜 = ⟪(y₀ : F), T x⟫_𝕜 := by
      intro x
      have hy : T x ∈ LinearMap.range T.toFun := ⟨x, rfl⟩
      obtain ⟨-, hd, hTg⟩ := hg ⟨T x, hy⟩
      have h1 : ((x - ⟨_, hd⟩ : T.domain) : E) ∈ T.ker :=
        (LinearPMap.coe_mem_ker_iff).2 (by rw [LinearPMap.map_sub, hTg]; exact sub_self _)
      have h2 := Submodule.inner_left_of_mem_orthogonal h1 hf
      have h3 : ⟪(y₀ : F), T x⟫_𝕜 = φ ⟨T x, hy⟩ :=
        (InnerProductSpace.toDual_symm_apply (x := (⟨T x, hy⟩ : LinearMap.range T.toFun)))
      rw [h3]
      change ⟪f, (x : E)⟫_𝕜 = ⟪f, g ⟨T x, hy⟩⟫_𝕜
      change ⟪f, (x : E) - g ⟨T x, hy⟩⟫_𝕜 = 0 at h2
      rw [inner_sub_right] at h2
      linear_combination h2
    have hmem : (y₀ : F) ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨f, key⟩
    exact ⟨⟨_, hmem⟩, adjoint_apply_eq hT ⟨_, hmem⟩ key⟩

theorem isClosed_range_adjoint_iff (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E))
    (hc : T.IsClosed) :
    _root_.IsClosed (LinearMap.range T†.toFun : Set E) ↔
      _root_.IsClosed (LinearMap.range T.toFun : Set F) := by
  constructor
  · intro h
    have := range_adjoint_eq_orthogonal_ker T† (dense_adjoint_domain T hT hc)
      (adjoint_isClosed hT) h
    rw [adjoint_adjoint T hT hc] at this
    rw [this]
    exact Submodule.isClosed_orthogonal _
  · intro h
    rw [range_adjoint_eq_orthogonal_ker T hT hc h]
    exact Submodule.isClosed_orthogonal _

theorem range_eq_orthogonal_ker_adjoint (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E))
    (hR : _root_.IsClosed (LinearMap.range T.toFun : Set F)) :
    LinearMap.range T.toFun = T†.kerᗮ := by
  rw [orthogonal_ker_adjoint T hT, hR.submodule_topologicalClosure_eq]

/-- **Closed range theorem**: for closed densely defined `T`, the closedness of `R(T)` and of
`R(T†)`, the Poincaré inequalities for `T` and `T†`, `R(T†) = N(T)ᗮ` and `R(T) = N(T†)ᗮ` agree. -/
theorem closedRange_tfae (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (hc : T.IsClosed) :
    [_root_.IsClosed (LinearMap.range T.toFun : Set F),
      _root_.IsClosed (LinearMap.range T†.toFun : Set E),
      ∃ c, ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ c * ‖T x‖,
      ∃ c, ∀ y : T†.domain, (y : F) ∈ T†.kerᗮ → ‖(y : F)‖ ≤ c * ‖T† y‖,
      LinearMap.range T†.toFun = T.kerᗮ,
      LinearMap.range T.toFun = T†.kerᗮ].TFAE := by
  tfae_have 1 ↔ 2 := (isClosed_range_adjoint_iff T hT hc).symm
  tfae_have 1 ↔ 3 := isClosed_range_iff_exists_norm_le hc
  tfae_have 2 ↔ 4 := isClosed_range_iff_exists_norm_le (adjoint_isClosed hT)
  tfae_have 1 → 5 := range_adjoint_eq_orthogonal_ker T hT hc
  tfae_have 5 → 2 := fun h => h ▸ Submodule.isClosed_orthogonal _
  tfae_have 1 → 6 := range_eq_orthogonal_ker_adjoint T hT
  tfae_have 6 → 1 := fun h => h ▸ Submodule.isClosed_orthogonal _
  tfae_finish

end LinearPMap
