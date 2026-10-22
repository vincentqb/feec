module

public import Feec.HilbertComplex.Reducing

/-!
# Transport between Hilbert complexes: scaled embeddings

A **scaled embedding** `H → H'` of Hilbert complexes on the same shape is a family of bounded
maps `J i : W i → W' i` with `⟪J x, J y⟫ = s_i ⟪x, y⟫` (`s_i > 0`) that carries each
differential to a nonzero multiple of the other (`d' J = κ_{ij} J d`, the chain-rule factors)
and reflects domains (`J x ∈ D(d') → x ∈ D(d)`). One structure covers:

* **compression** onto a reducing subcomplex (`ReducingSubcomplex.toHilbertComplex`, with the
  inclusion `ReducingSubcomplex.toScaledEmbedding`): restriction to a box, to the fixed vectors
  of a symmetry group (`Feec.HilbertComplex.Equivariant`), to a constraint subspace;
* **transport** along scaled isomorphisms with rescaled differentials
  (`HilbertComplex.transport e κ`): unitary maps
  (`κ = 1`, `s = 1`), rescaling of the differentials (`e = 1`), and pull-back along an affine
  change of variables (`e` the composition operator, `s = |det|⁻¹`, `κ` the chain-rule factors);
* composition (`ScaledEmbedding.comp`) and the identity (`ScaledEmbedding.refl`).

## Main results

* `LinearPMap.IsReducingPair.part`: the part `K → L` of `T : E → F` in a reducing pair, closed
  (`isClosed_part`), densely defined (`dense_part_domain`), with `adjoint_part`:
  `(T|_K)† = (T†)|_L`.
* `ReducingSubcomplex.toHilbertComplex`, `ReducingSubcomplex.wave_toHilbertComplex`: the
  inclusion of the compressed complex intertwines the wave operators, hence the wave groups
  (`ReducingSubcomplex.waveGroup_toHilbertComplex`).
* **`ScaledEmbedding.reducingSubcomplex_comap`**: if `S'` is a reducing subcomplex of `H'` whose
  projections preserve the ranges of `J`, then `J⁻¹ S'` is a reducing subcomplex of `H`
  (`ScaledEmbedding.starProjection_comap`: `J P_{J⁻¹ S'} = P_{S'} J`);
  `ScaledEmbedding.invariantCore_eq`: then `J⁻¹ S'` is its own invariant core.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17 on the cube, by compression of the torus)
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6 (parts of operators in
  reducing subspaces)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

/-! ### Orthogonal projections and closedness -/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace with an orthogonal projection is closed. -/
theorem isClosed_of_hasOrthogonalProjection (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    IsClosed (K : Set E) := by
  rw [← Submodule.orthogonal_orthogonal K]; exact Submodule.isClosed_orthogonal _

/-- A subspace of a Hilbert space with an orthogonal projection is complete. -/
theorem completeSpace_of_hasOrthogonalProjection [CompleteSpace E] (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] : CompleteSpace K :=
  (K.isClosed_of_hasOrthogonalProjection).completeSpace_coe

end Submodule

/-! ### The part of an operator in a reducing pair -/

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {T : E →ₗ.[𝕜] F} {K : Submodule 𝕜 E} {L : Submodule 𝕜 F} [K.HasOrthogonalProjection]
  [L.HasOrthogonalProjection]

/-- The **part** `K → L` of `T : E → F` in a reducing pair `(K, L)`, with domain `D(T) ∩ K`. -/
def IsReducingPair.part (h : T.IsReducingPair K L) : K →ₗ.[𝕜] L where
  domain := T.domain.comap K.subtype
  toFun :=
    { toFun := fun x => ⟨T ⟨(x : K), x.2⟩, h.mapsTo ⟨_, x.2⟩ (x : K).2⟩
      map_add' := fun x y => by ext; simp [← LinearPMap.map_add]; rfl
      map_smul' := fun a x => by ext; simp [← LinearPMap.map_smul]; rfl }

variable (h : T.IsReducingPair K L)

theorem IsReducingPair.mem_part_domain {x : K} : x ∈ h.part.domain ↔ (x : E) ∈ T.domain :=
  Iff.rfl

@[simp] theorem IsReducingPair.part_apply (x : h.part.domain) :
    ((h.part x : L) : F) = T ⟨((x : K) : E), x.2⟩ := rfl

theorem IsReducingPair.mem_part_graph_iff {p : K × L} :
    p ∈ h.part.graph ↔ ((p.1 : E), (p.2 : F)) ∈ T.graph := by
  rw [mem_graph_iff, mem_graph_iff]
  constructor
  · rintro ⟨y, hy1, hy2⟩
    exact ⟨⟨_, y.2⟩, by simp [hy1], by rw [← hy2]; rfl⟩
  · rintro ⟨y, hy1, hy2⟩
    have hy1' : (y : E) = (p.1 : E) := hy1
    have hp : p.1 ∈ h.part.domain := show ((p.1 : K) : E) ∈ T.domain from hy1' ▸ y.2
    refine ⟨⟨p.1, hp⟩, rfl, Subtype.ext ?_⟩
    change T ⟨((p.1 : K) : E), hp⟩ = (p.2 : F)
    rw [← show T y = (p.2 : F) from hy2]
    exact apply_congr' _ _ _ hy1'.symm

/-- The part of a closed operator is closed. -/
theorem IsReducingPair.isClosed_part (hc : T.IsClosed) : h.part.IsClosed := by
  have e : (h.part.graph : Set (K × L)) =
      (fun p : K × L => ((p.1 : E), (p.2 : F))) ⁻¹' (T.graph : Set (E × F)) := by
    ext p; exact h.mem_part_graph_iff
  unfold LinearPMap.IsClosed
  rw [e]
  exact hc.preimage ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

/-- The part of a densely defined operator is densely defined. -/
theorem IsReducingPair.dense_part_domain (hd : Dense (T.domain : Set E)) :
    Dense (h.part.domain : Set K) := by
  have hd' : Dense ((K.orthogonalProjectionOnto) '' (T.domain : Set E)) :=
    (Function.Surjective.denseRange (f := (K.orthogonalProjectionOnto : E → K))
      (fun k : K => ⟨(k : E), K.orthogonalProjectionOnto_mem_subspace_eq_self k⟩)).dense_image
      (K.orthogonalProjectionOnto).continuous hd
  refine hd'.mono ?_
  rintro _ ⟨x, hx, rfl⟩
  change ((K.orthogonalProjectionOnto x : K) : E) ∈ T.domain
  rw [← Submodule.starProjection_apply]
  exact h.proj_mem ⟨x, hx⟩

/-- **The adjoint of the part is the part of the adjoint**: `(T|_K)† = (T†)|_L`. -/
theorem IsReducingPair.adjoint_part [CompleteSpace E] [CompleteSpace K]
    (hd : Dense (T.domain : Set E)) : h.part† = (h.adjoint hd).part := by
  have hdp := h.dense_part_domain hd
  have hle : (h.adjoint hd).part ≤ h.part† := by
    refine IsFormalAdjoint.le_adjoint hdp fun x y => ?_
    simp only [Submodule.coe_inner]
    exact (adjoint_isFormalAdjoint hd).symm ⟨_, x.2⟩ ⟨_, y.2⟩
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  change ((y : L) : F) ∈ T†.domain
  refine mem_adjoint_domain_of_exists _ ⟨((h.part† ⟨y, hy⟩ : K) : E), fun x => ?_⟩
  set px : h.part.domain := ⟨K.orthogonalProjectionOnto x, by
    change ((K.orthogonalProjectionOnto x : K) : E) ∈ T.domain
    rw [← Submodule.starProjection_apply]; exact h.proj_mem x⟩
  have hadj := adjoint_isFormalAdjoint hdp ⟨y, hy⟩ px
  have e1 : ⟪((h.part† ⟨y, hy⟩ : K) : E), (x : E)⟫_𝕜 =
      ⟪((h.part† ⟨y, hy⟩ : K) : E), K.starProjection (x : E)⟫_𝕜 := by
    rw [← sub_eq_zero, ← inner_sub_right]
    exact Submodule.inner_right_of_mem_orthogonal (h.part† ⟨y, hy⟩).2
      (K.sub_starProjection_mem_orthogonal _)
  have e2 : ⟪((y : L) : F), T x⟫_𝕜 = ⟪((y : L) : F), T ⟨_, h.proj_mem x⟩⟫_𝕜 := by
    rw [h.comm x, ← Submodule.inner_starProjection_left_eq_right,
      (L.starProjection_eq_self_iff).2 y.2]
  rw [e1, e2]
  simp only [Submodule.coe_inner] at hadj
  convert hadj using 2 <;> rfl

/-- The part of a partial map equal to `0` is `0`. -/
theorem IsReducingPair.part_eq_zero (hT : T = 0) : h.part = 0 := by
  refine LinearPMap.ext ?_ fun x y hxy => ?_
  · ext x
    change (x : E) ∈ T.domain ↔ x ∈ (⊤ : Submodule 𝕜 K)
    rw [hT]; exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩
  · refine Subtype.ext ?_
    rw [part_apply, apply_eq_zero_of_eq_zero hT, apply_eq_zero_of_eq_zero rfl]; rfl

end LinearPMap

/-! ### Compression onto a reducing subcomplex -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

namespace ReducingSubcomplex

variable {S : ∀ i, Submodule 𝕜 (W i)} [∀ i, CompleteSpace (S i)]

/-- **Compression**: a reducing subcomplex is a Hilbert complex, with differentials the parts
`d i j|_{S i} : S i → S j`. -/
def toHilbertComplex (h : H.ReducingSubcomplex S) : HilbertComplex 𝕜 c fun i => S i where
  d i j := (h.reduces i j).part
  shape i j hij := (h.reduces i j).part_eq_zero (H.shape i j hij)
  dense i j := (h.reduces i j).dense_part_domain (H.dense i j)
  closed i j := (h.reduces i j).isClosed_part (H.closed i j)
  mapsTo i j k x := H.mapsTo i j k ⟨_, x.2⟩
  d_comp_d i j k x := Subtype.ext (H.d_comp_d i j k ⟨_, x.2⟩)

/-- The dual of the compressed complex is the compression of the dual complex. -/
theorem dual_toHilbertComplex_d (h : H.ReducingSubcomplex S) (i j : ι) :
    h.toHilbertComplex.dual.d i j = h.dual.toHilbertComplex.d i j :=
  (h.reduces j i).adjoint_part (H.dense j i)

variable [Fintype ι]

/-- The inclusion `∏ S i → ∏ W i`. -/
def totalIncl (S : ∀ i, Submodule 𝕜 (W i)) : PiLp 2 (fun i => S i) →ₗᵢ[𝕜] PiLp 2 W where
  toFun x := WithLp.toLp 2 fun i => (x i : W i)
  map_add' x y := PiLp.ext fun i => by simp
  map_smul' a x := PiLp.ext fun i => by simp
  norm_map' x := by simp [PiLp.norm_eq_of_L2]

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (S i)] in
theorem totalIncl_apply (x : PiLp 2 fun i => S i) (i : ι) :
    totalIncl S x i = (x i : W i) := rfl

/-- **The inclusion of the compressed complex intertwines the wave operators.** -/
theorem wave_toHilbertComplex (h : H.ReducingSubcomplex S) :
    Intertwines ((totalIncl S).toContinuousLinearMap) h.toHilbertComplex.wave H.wave := by
  have hdual : ∀ i j, h.toHilbertComplex.dual.d i j = h.dual.toHilbertComplex.d i j :=
    h.dual_toHilbertComplex_d
  have hmem : ∀ x : h.toHilbertComplex.wave.domain, totalIncl S (x : PiLp 2 fun i => S i) ∈ H.wave.domain :=
    fun x => H.mem_wave_domain.2 ⟨fun i j => x.2.1 i j, fun i j => by
      have := x.2.2 j i
      change (x : PiLp 2 fun i => S i) j ∈ (h.toHilbertComplex.dual.d j i).domain at this
      rw [hdual] at this
      exact this⟩
  refine ⟨hmem, fun x => PiLp.ext fun j => ?_⟩
  change H.wave ⟨_, hmem x⟩ j = ((h.toHilbertComplex.wave x) j : W j)
  rw [wave_apply, wave_apply, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_sum]
  refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun k _ => ?_)
  exact (congrArg Subtype.val (apply_eq_of_eq (hdual k j) ⟨_, x.2.2 k j⟩
    ⟨_, (hmem x).2 k j⟩ rfl)).symm

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The wave group of the compressed complex is the restriction of the wave group**:
`ι e^{tL_S} = e^{tL} ι`. -/
theorem waveGroup_toHilbertComplex (h : H.ReducingSubcomplex S) (t : ℝ)
    (x : PiLp 2 fun i => S i) :
    totalIncl S (h.toHilbertComplex.waveGroup.S t x) = H.waveGroup.S t (totalIncl S x) := by
  have hJ := h.wave_toHilbertComplex
  rw [← generator_waveGroup, ← generator_waveGroup] at hJ
  exact H.isIsometric_waveGroup.intertwines_S _ hJ t x

end ReducingSubcomplex

/-! ### Scaled embeddings -/

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)]

/-- A **scaled embedding** `H → H'` of Hilbert complexes on the same shape: bounded maps
`J i : W i → W' i` with `⟪J x, J y⟫ = s_i ⟪x, y⟫`, `s_i > 0`, carrying `d` to a nonzero multiple
of `d'` (`d' (J x) = κ_{ij} • J (d x)`, the chain-rule factors) and reflecting domains. -/
structure ScaledEmbedding (H : HilbertComplex 𝕜 c W) (H' : HilbertComplex 𝕜 c W') where
  /-- the embedding -/
  J : ∀ i, W i →L[𝕜] W' i
  /-- the scaling of the inner products -/
  scale : ι → ℝ
  scale_pos : ∀ i, 0 < scale i
  inner_J : ∀ i (x y : W i), ⟪J i x, J i y⟫_𝕜 = (scale i : 𝕜) * ⟪x, y⟫_𝕜
  /-- the chain-rule factors -/
  dScale : ι → ι → 𝕜
  dScale_ne_zero : ∀ i j, dScale i j ≠ 0
  mapsTo : ∀ i j (x : (H.d i j).domain), J i x ∈ (H'.d i j).domain
  comm : ∀ i j (x : (H.d i j).domain),
    H'.d i j ⟨J i x, mapsTo i j x⟩ = dScale i j • J j (H.d i j x)
  mem_domain_of_map : ∀ i j (x : W i), J i x ∈ (H'.d i j).domain → x ∈ (H.d i j).domain

namespace ScaledEmbedding

variable {H' : HilbertComplex 𝕜 c W'} (E : ScaledEmbedding H H')

theorem J_injective (i : ι) : Function.Injective (E.J i) := by
  intro x y hxy
  have h := E.inner_J i (x - y) (x - y)
  rw [_root_.map_sub, hxy, sub_self, inner_zero_left, eq_comm, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd (RCLike.ofReal_eq_zero.1 h) (E.scale_pos i).ne'
  · exact sub_eq_zero.1 (inner_self_eq_zero.1 h)

theorem mem_domain_iff {i j : ι} {x : W i} : J E i x ∈ (H'.d i j).domain ↔ x ∈ (H.d i j).domain :=
  ⟨E.mem_domain_of_map i j x, fun hx => E.mapsTo i j ⟨x, hx⟩⟩

instance comap_hasOrthogonalProjection (i : ι) (S' : Submodule 𝕜 (W' i))
    [S'.HasOrthogonalProjection] :
    (S'.comap (E.J i : W i →ₗ[𝕜] W' i)).HasOrthogonalProjection := by
  have hc : IsClosed (S'.comap (E.J i : W i →ₗ[𝕜] W' i) : Set (W i)) :=
    (S'.isClosed_of_hasOrthogonalProjection).preimage (E.J i).continuous
  have : CompleteSpace (S'.comap (E.J i : W i →ₗ[𝕜] W' i)) := hc.completeSpace_coe
  infer_instance

/-- **The projection onto `J⁻¹ S'`**: if `P_{S'}` maps the range of `J` into itself, then
`J P_{J⁻¹ S'} = P_{S'} J`. -/
theorem starProjection_comap {i : ι} (S' : Submodule 𝕜 (W' i)) [S'.HasOrthogonalProjection]
    (hS : ∀ x, ∃ y, E.J i y = S'.starProjection (E.J i x)) (x : W i) :
    E.J i ((S'.comap (E.J i : W i →ₗ[𝕜] W' i)).starProjection x) = S'.starProjection (E.J i x) := by
  obtain ⟨v, hv⟩ := hS x
  have hvS : v ∈ S'.comap (E.J i : W i →ₗ[𝕜] W' i) := by
    change E.J i v ∈ S'; rw [hv]; exact S'.starProjection_apply_mem _
  have e : (S'.comap (E.J i : W i →ₗ[𝕜] W' i)).starProjection x = v := by
    refine Submodule.eq_starProjection_of_mem_orthogonal hvS ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h0 := Submodule.inner_right_of_mem_orthogonal (K := S') hu
      (S'.sub_starProjection_mem_orthogonal (E.J i x))
    have : (E.scale i : 𝕜) * ⟪u, x - v⟫_𝕜 = 0 := by
      rw [← E.inner_J, _root_.map_sub, hv]; exact h0
    exact (mul_eq_zero.1 this).resolve_left (RCLike.ofReal_ne_zero.2 (E.scale_pos i).ne')
  rw [e, hv]

/-- **Reducing subcomplexes pull back along scaled embeddings**: if `S'` is a reducing subcomplex
of `H'` whose projections preserve the ranges of `J`, then `J⁻¹ S'` is a reducing subcomplex of
`H`. This transfers constraint propagation from a model complex (the torus, `ℝⁿ`) to its
compressions, restrictions and rescalings. [QuennevilleBelair2015], Prop 4.17 -/
theorem reducingSubcomplex_comap {S' : ∀ i, Submodule 𝕜 (W' i)}
    [∀ i, (S' i).HasOrthogonalProjection] (hS' : H'.ReducingSubcomplex S')
    (hS : ∀ i x, ∃ y, E.J i y = (S' i).starProjection (E.J i x)) :
    H.ReducingSubcomplex fun i => (S' i).comap (E.J i : W i →ₗ[𝕜] W' i) := by
  refine ⟨fun i j => ?_⟩
  have hP : ∀ x : (H.d i j).domain,
      E.J i (((S' i).comap (E.J i : W i →ₗ[𝕜] W' i)).starProjection (x : W i)) ∈
        (H'.d i j).domain := fun x => by
    rw [E.starProjection_comap _ (hS i)]
    exact (hS'.reduces i j).proj_mem ⟨_, E.mapsTo i j x⟩
  refine ⟨fun x => E.mem_domain_of_map i j _ (hP x), fun x => E.J_injective j ?_⟩
  have hκ := E.dScale_ne_zero i j
  rw [E.starProjection_comap _ (hS j)]
  apply smul_right_injective _ hκ
  change E.dScale i j • _ = E.dScale i j • _
  rw [← E.comm i j ⟨_, E.mem_domain_of_map i j _ (hP x)⟩,
    ← _root_.map_smul (S' j).starProjection, ← E.comm i j x,
    ← (hS'.reduces i j).comm ⟨_, E.mapsTo i j x⟩]
  exact apply_congr' _ _ _ (E.starProjection_comap _ (hS i) x)

variable [Fintype ι] [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- Under the hypotheses of `reducingSubcomplex_comap`, `J⁻¹ S'` is its own invariant core for
the wave group of `H` (Thesis Prop 4.17, the corrected maximal constraint `K* = K`). -/
theorem invariantCore_eq {S' : ∀ i, Submodule 𝕜 (W' i)} [∀ i, (S' i).HasOrthogonalProjection]
    (hS' : H'.ReducingSubcomplex S') (hS : ∀ i x, ∃ y, E.J i y = (S' i).starProjection (E.J i x)) :
    H.waveGroup.invariantCore (totalSub fun i => (S' i).comap (E.J i : W i →ₗ[𝕜] W' i)) =
      totalSub fun i => (S' i).comap (E.J i : W i →ₗ[𝕜] W' i) :=
  (E.reducingSubcomplex_comap hS' hS).invariantCore_eq

end ScaledEmbedding

/-! ### Instances: identity, composition, compression -/

namespace ScaledEmbedding

/-- The identity embedding. -/
def refl (H : HilbertComplex 𝕜 c W) : ScaledEmbedding H H where
  J i := ContinuousLinearMap.id 𝕜 (W i)
  scale _ := 1
  scale_pos _ := one_pos
  inner_J i x y := by simp
  dScale _ _ := 1
  dScale_ne_zero _ _ := one_ne_zero
  mapsTo _ _ x := x.2
  comm _ _ x := by rw [one_smul]; rfl
  mem_domain_of_map _ _ _ h := h

variable {W'' : ι → Type*} [∀ i, NormedAddCommGroup (W'' i)] [∀ i, InnerProductSpace 𝕜 (W'' i)]
  [∀ i, CompleteSpace (W'' i)] {H' : HilbertComplex 𝕜 c W'} {H'' : HilbertComplex 𝕜 c W''}

/-- The composition of scaled embeddings: scales and chain-rule factors multiply. -/
def comp (E₂ : ScaledEmbedding H' H'') (E₁ : ScaledEmbedding H H') : ScaledEmbedding H H'' where
  J i := (E₂.J i).comp (E₁.J i)
  scale i := E₂.scale i * E₁.scale i
  scale_pos i := mul_pos (E₂.scale_pos i) (E₁.scale_pos i)
  inner_J i x y := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, E₂.inner_J, E₁.inner_J,
      RCLike.ofReal_mul, mul_assoc]
  dScale i j := E₂.dScale i j * E₁.dScale i j
  dScale_ne_zero i j := mul_ne_zero (E₂.dScale_ne_zero i j) (E₁.dScale_ne_zero i j)
  mapsTo i j x := E₂.mapsTo i j ⟨_, E₁.mapsTo i j x⟩
  comm i j x := by
    change H''.d i j ⟨E₂.J i (E₁.J i x), _⟩ = _
    rw [E₂.comm i j ⟨_, E₁.mapsTo i j x⟩, E₁.comm i j x, _root_.map_smul, smul_smul]
    rfl
  mem_domain_of_map i j x h := E₁.mem_domain_of_map i j x (E₂.mem_domain_of_map i j _ h)

end ScaledEmbedding

namespace ReducingSubcomplex

variable {S : ∀ i, Submodule 𝕜 (W i)} [∀ i, CompleteSpace (S i)]

/-- **Compression is a scaled embedding**: the inclusion of a reducing subcomplex. -/
def toScaledEmbedding (h : H.ReducingSubcomplex S) : ScaledEmbedding h.toHilbertComplex H where
  J i := (S i).subtypeL
  scale _ := 1
  scale_pos _ := one_pos
  inner_J i x y := by simp
  dScale _ _ := 1
  dScale_ne_zero _ _ := one_ne_zero
  mapsTo _ _ x := x.2
  comm _ _ x := by rw [one_smul]; rfl
  mem_domain_of_map _ _ _ h := h

end ReducingSubcomplex

/-! ### Transport along scaled isomorphisms -/

section Transport

variable (H) (e : ∀ i, W i ≃L[𝕜] W' i) (κ : ι → ι → 𝕜)

/-- The conjugated differential `κ_{ij} • e_j ∘ d_{ij} ∘ e_i⁻¹`, on `e_i D(d_{ij})`. -/
def transportD (i j : ι) : W' i →ₗ.[𝕜] W' j where
  domain := (H.d i j).domain.comap ((e i).symm : W' i →ₗ[𝕜] W i)
  toFun := κ i j • ((e j : W j →ₗ[𝕜] W' j).comp ((H.d i j).toFun.comp
    (((e i).symm : W' i →ₗ[𝕜] W i).restrict
      (p := (H.d i j).domain.comap ((e i).symm : W' i →ₗ[𝕜] W i)) (q := (H.d i j).domain)
      fun _ hy => hy)))

variable {H e κ}

omit [∀ i, CompleteSpace (W' i)] in
theorem transportD_apply {i j : ι} (y : (transportD H e κ i j).domain) :
    transportD H e κ i j y =
      κ i j • e j (H.d i j ⟨(e i).symm y, show (e i).symm (y : W' i) ∈ _ from y.2⟩) := rfl

omit [∀ i, CompleteSpace (W' i)] in
theorem mem_transportD_domain {i j : ι} {y : W' i} :
    y ∈ (transportD H e κ i j).domain ↔ (e i).symm y ∈ (H.d i j).domain := Iff.rfl

omit [∀ i, CompleteSpace (W' i)] in
theorem mem_transportD_graph_iff {i j : ι} (hκ : κ i j ≠ 0) {p : W' i × W' j} :
    p ∈ (transportD H e κ i j).graph ↔
      ((e i).symm p.1, (κ i j)⁻¹ • (e j).symm p.2) ∈ (H.d i j).graph := by
  rw [mem_graph_iff, mem_graph_iff]
  constructor
  · rintro ⟨y, hy1, hy2⟩
    refine ⟨⟨_, y.2⟩, by simp [← hy1], ?_⟩
    rw [← hy2, transportD_apply, _root_.map_smul, ContinuousLinearEquiv.symm_apply_apply,
      inv_smul_smul₀ hκ]
    rfl
  · rintro ⟨x, hx1, hx2⟩
    have hx1' : (x : W i) = (e i).symm p.1 := hx1
    have hp : p.1 ∈ (transportD H e κ i j).domain := show (e i).symm p.1 ∈ _ from hx1' ▸ x.2
    refine ⟨⟨p.1, hp⟩, rfl, ?_⟩
    have e2 : H.d i j ⟨(e i).symm p.1, hp⟩ = (κ i j)⁻¹ • (e j).symm p.2 := by
      rw [← show H.d i j x = (κ i j)⁻¹ • (e j).symm p.2 from hx2]
      exact apply_congr' _ _ _ hx1'.symm
    change κ i j • e j (H.d i j ⟨(e i).symm p.1, hp⟩) = p.2
    rw [e2, _root_.map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_inv_smul₀ hκ]

omit [∀ i, CompleteSpace (W' i)] in
theorem isClosed_transportD {i j : ι} (hκ : κ i j ≠ 0) : (transportD H e κ i j).IsClosed := by
  have hg : ((transportD H e κ i j).graph : Set (W' i × W' j)) =
      (fun p : W' i × W' j => ((e i).symm p.1, (κ i j)⁻¹ • (e j).symm p.2)) ⁻¹'
        ((H.d i j).graph : Set (W i × W j)) := by
    ext p; exact mem_transportD_graph_iff hκ
  unfold LinearPMap.IsClosed
  rw [hg]
  exact (H.closed i j).preimage (((e i).symm.continuous.comp continuous_fst).prodMk
    ((continuous_const_smul _).comp ((e j).symm.continuous.comp continuous_snd)))

omit [∀ i, CompleteSpace (W' i)] in
theorem dense_transportD_domain (i j : ι) :
    Dense ((transportD H e κ i j).domain : Set (W' i)) :=
  (H.dense i j).preimage (e i).symm.toHomeomorph.isOpenMap

omit [∀ i, CompleteSpace (W' i)] in
theorem transportD_eq_zero {i j : ι} (h : H.d i j = 0) : transportD H e κ i j = 0 := by
  refine LinearPMap.ext ?_ fun x y _ => ?_
  · ext y
    change (e i).symm y ∈ (H.d i j).domain ↔ y ∈ (⊤ : Submodule 𝕜 (W' i))
    rw [h]; exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩
  · rw [transportD_apply, apply_eq_zero_of_eq_zero h, _root_.map_zero, smul_zero,
      apply_eq_zero_of_eq_zero rfl]

variable (H e κ)

/-- **Transport of a Hilbert complex** along continuous linear isomorphisms `e i : W i ≃ W' i`
with the differentials rescaled by nonzero `κ i j`: `d' = κ • e ∘ d ∘ e⁻¹`. Covers unitary
transport (`HilbertComplex.map`), rescaling (`HilbertComplex.smul`), and pull-back along an affine
change of variables. -/
def transport (hκ : ∀ i j, κ i j ≠ 0) : HilbertComplex 𝕜 c W' where
  d := transportD H e κ
  shape i j hij := transportD_eq_zero (H.shape i j hij)
  dense i j := dense_transportD_domain i j
  closed i j := isClosed_transportD (hκ i j)
  mapsTo i j k y := by
    have hy : (e i).symm (y : W' i) ∈ (H.d i j).domain := y.2
    have h1 : (e j).symm (transportD H e κ i j y) = κ i j • H.d i j ⟨_, hy⟩ := by
      rw [transportD_apply, _root_.map_smul, ContinuousLinearEquiv.symm_apply_apply]
    change (e j).symm (transportD H e κ i j y) ∈ (H.d j k).domain
    rw [h1]
    exact Submodule.smul_mem _ _ (H.mapsTo i j k _)
  d_comp_d i j k y := by
    have hy : (e i).symm (y : W' i) ∈ (H.d i j).domain := y.2
    have h1 : (e j).symm (transportD H e κ i j y) = κ i j • H.d i j ⟨_, hy⟩ := by
      rw [transportD_apply, _root_.map_smul, ContinuousLinearEquiv.symm_apply_apply]
    have hm : κ i j • H.d i j ⟨_, hy⟩ ∈ (H.d j k).domain :=
      Submodule.smul_mem _ _ (H.mapsTo i j k _)
    have hm' : (e j).symm (transportD H e κ i j y) ∈ (H.d j k).domain := h1 ▸ hm
    change κ j k • e k (H.d j k ⟨(e j).symm (transportD H e κ i j y), hm'⟩) = 0
    rw [apply_congr' (H.d j k) hm' hm h1]
    have : (⟨κ i j • H.d i j ⟨_, hy⟩, hm⟩ : (H.d j k).domain) =
        κ i j • ⟨_, H.mapsTo i j k ⟨_, hy⟩⟩ := rfl
    rw [this, LinearPMap.map_smul, H.d_comp_d, smul_zero, _root_.map_zero, smul_zero]

@[simp] theorem transport_d (hκ : ∀ i j, κ i j ≠ 0) (i j : ι) :
    (H.transport e κ hκ).d i j = transportD H e κ i j := rfl

/-- Transport along unitary isomorphisms. -/
abbrev map (u : ∀ i, W i ≃ₗᵢ[𝕜] W' i) : HilbertComplex 𝕜 c W' :=
  H.transport (fun i => (u i).toContinuousLinearEquiv) (fun _ _ => 1) fun _ _ => one_ne_zero

/-- Rescaling of the differentials: `d' i j = κ i j • d i j`. -/
abbrev smul (hκ : ∀ i j, κ i j ≠ 0) : HilbertComplex 𝕜 c W :=
  H.transport (fun i => ContinuousLinearEquiv.refl 𝕜 (W i)) κ hκ

end Transport

/-! ### Adjoints of transported complexes -/

section TransportAdjoint

open scoped ComplexConjugate

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)]

/-- Two Hilbert complexes with the same differentials are equal. -/
theorem ext_d {H₁ H₂ : HilbertComplex 𝕜 c W} (h : H₁.d = H₂.d) : H₁ = H₂ := by
  cases H₁; cases H₂; subst h; rfl

variable {e : ∀ i, W i ≃L[𝕜] W' i} {κ : ι → ι → 𝕜} {s : ℝ}

/-- **Adjoints of transported differentials** along uniformly scaled isometries
(`⟪e x, e y⟫ = s ⟪x, y⟫` for all spaces): `(κ e d e⁻¹)† = conj κ · e d† e⁻¹`. -/
theorem adjoint_transportD (hs : 0 < s)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) {i j : ι} (hκ : κ i j ≠ 0) :
    (transportD H e κ i j)† = transportD H.dual e (fun a b => conj (κ b a)) j i := by
  have hs' : (s : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hs.ne'
  have hfa := adjoint_isFormalAdjoint (H.dense i j)
  have hle : transportD H.dual e (fun a b => conj (κ b a)) j i ≤ (transportD H e κ i j)† := by
    refine IsFormalAdjoint.le_adjoint (dense_transportD_domain i j) fun x y => ?_
    rw [transportD_apply, transportD_apply]
    have hy : (y : W' j) = e j ((e j).symm y) := ((e j).apply_symm_apply _).symm
    have hx : (x : W' i) = e i ((e i).symm x) := ((e i).apply_symm_apply _).symm
    have h1 := hfa ⟨(e j).symm y, y.2⟩ ⟨(e i).symm x, x.2⟩
    conv_lhs => rw [hy]
    conv_rhs => rw [hx]
    rw [inner_smul_left, he, inner_smul_right, he]
    change conj (κ i j) * ((s : 𝕜) * ⟪H.d i j _, (e j).symm y⟫_𝕜) =
      conj (κ i j) * ((s : 𝕜) * ⟪(e i).symm x, (H.d i j)† _⟫_𝕜)
    rw [← inner_conj_symm, ← h1, inner_conj_symm]
    rfl
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  change (e j).symm y ∈ ((H.d i j)†).domain
  set z := (transportD H e κ i j)† ⟨y, hy⟩
  refine mem_adjoint_domain_of_exists _ ⟨conj (κ i j)⁻¹ • (e i).symm z, fun x => ?_⟩
  have hx : (e i).symm (e i x) ∈ (H.d i j).domain := by
    rw [ContinuousLinearEquiv.symm_apply_apply]; exact x.2
  have h2 := adjoint_isFormalAdjoint (dense_transportD_domain (H := H) (e := e) (κ := κ) i j)
    ⟨y, hy⟩ ⟨e i x, hx⟩
  rw [transportD_apply, apply_congr' (H.d i j) hx x.2 ((e i).symm_apply_apply x)] at h2
  change ⟪z, e i x⟫_𝕜 = ⟪y, κ i j • e j (H.d i j x)⟫_𝕜 at h2
  rw [inner_smul_right, show (y : W' j) = e j ((e j).symm y) from ((e j).apply_symm_apply _).symm,
    he, show z = e i ((e i).symm z) from ((e i).apply_symm_apply _).symm, he] at h2
  rw [inner_smul_left, RCLike.conj_conj]
  have h3 : ⟪(e i).symm z, (x : W i)⟫_𝕜 = κ i j * ⟪(e j).symm y, H.d i j x⟫_𝕜 :=
    mul_left_cancel₀ hs' (h2.trans (by ring))
  rw [h3, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]

variable [Fintype ι]

/-- The componentwise map `∏ W i → ∏ W' i`. -/
def totalMap (e : ∀ i, W i ≃L[𝕜] W' i) : PiLp 2 W →L[𝕜] PiLp 2 W' :=
  ((PiLp.continuousLinearEquiv 2 𝕜 W').symm : (∀ i, W' i) →L[𝕜] PiLp 2 W').comp
    ((ContinuousLinearMap.pi fun i => ((e i : W i →L[𝕜] W' i)).comp (ContinuousLinearMap.proj i)).comp
      (PiLp.continuousLinearEquiv 2 𝕜 W : PiLp 2 W →L[𝕜] ∀ i, W i))

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (W' i)] [Fintype ι] in
theorem totalMap_apply (e : ∀ i, W i ≃L[𝕜] W' i) (x : PiLp 2 W) (i : ι) :
    totalMap e x i = e i (x i) := rfl

/-- **Transport along uniformly scaled isometries intertwines the wave operators**
(`κ = 1`): `L' (e x) = e (L x)`. -/
theorem wave_transport (hs : 0 < s)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) :
    Intertwines (totalMap e) H.wave (H.transport e (fun _ _ => 1) fun _ _ => one_ne_zero).wave := by
  have hadj : ∀ i j, ((H.transport e (fun _ _ => (1 : 𝕜)) fun _ _ => one_ne_zero).d i j)† =
      transportD H.dual e (fun _ _ => (1 : 𝕜)) j i := fun i j => by
    have := adjoint_transportD (H := H) (e := e) (κ := fun _ _ => (1 : 𝕜)) hs he
      (i := i) (j := j) one_ne_zero
    simpa using this
  have hmem : ∀ x : H.wave.domain, totalMap e (x : PiLp 2 W) ∈
      (H.transport e (fun _ _ => 1) fun _ _ => one_ne_zero).wave.domain := fun x =>
    (mem_wave_domain _).2 ⟨fun i j => by
      change (e i).symm (e i ((x : PiLp 2 W) i)) ∈ (H.d i j).domain
      rw [ContinuousLinearEquiv.symm_apply_apply]; exact x.2.1 i j,
    fun i j => by
      rw [hadj]
      change (e j).symm (e j ((x : PiLp 2 W) j)) ∈ ((H.d i j)†).domain
      rw [ContinuousLinearEquiv.symm_apply_apply]; exact x.2.2 j i⟩
  refine ⟨hmem, fun x => PiLp.ext fun j => ?_⟩
  rw [wave_apply, totalMap_apply, wave_apply, _root_.map_sub, map_sum, map_sum]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun k _ => ?_)
  · change (1 : 𝕜) • e j (H.d i j ⟨(e i).symm (e i ((x : PiLp 2 W) i)), _⟩) = _
    rw [one_smul]
    exact congrArg (e j) (apply_congr' _ _ _ ((e i).symm_apply_apply _))
  · rw [apply_eq_of_eq (hadj j k) _ ⟨_, by
      change (e k).symm (e k ((x : PiLp 2 W) k)) ∈ ((H.d j k)†).domain
      rw [ContinuousLinearEquiv.symm_apply_apply]; exact x.2.2 k j⟩ rfl]
    change (1 : 𝕜) • e j ((H.d j k)† ⟨(e k).symm (e k ((x : PiLp 2 W) k)), _⟩) = _
    rw [one_smul]
    exact congrArg (e j) (apply_congr' _ _ _ ((e k).symm_apply_apply _))

end TransportAdjoint

/-! ### Compression along scaled isometric embeddings -/

section Compression

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)] {J : ∀ i, W' i →L[𝕜] W i} {s : ℝ}

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (W' i)] in
/-- A scaled isometry multiplies norms by `√s`. -/
theorem norm_apply_of_inner (hs : 0 < s) (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (i : ι) (x : W' i) : ‖J i x‖ = Real.sqrt s * ‖x‖ := by
  have h := hJ i x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖J i x‖ ^ 2 = s * ‖x‖ ^ 2 := by exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (J i x)), h', Real.sqrt_mul hs.le, Real.sqrt_sq (norm_nonneg x)]

/-- The scaled isometry onto its range, `x ↦ J x`, as a continuous linear equivalence. -/
def rangeEquiv (hs : 0 < s) (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (i : ι) : W' i ≃L[𝕜] LinearMap.range (J i : W' i →ₗ[𝕜] W i) :=
  have hinj : Function.Injective (J i) := fun x y h => by
    have := norm_apply_of_inner hs hJ i (x - y)
    rw [_root_.map_sub, h, sub_self, norm_zero, eq_comm, mul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 (Real.sqrt_pos.2 hs).ne'
    · exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  (LinearEquiv.ofInjective (J i : W' i →ₗ[𝕜] W i) hinj).toContinuousLinearEquivOfBounds
    (Real.sqrt s) (Real.sqrt s)⁻¹ (fun x => by
      change ‖J i x‖ ≤ _; rw [norm_apply_of_inner hs hJ])
    fun y => by
      obtain ⟨x, hx⟩ := y.2
      have e : (LinearEquiv.ofInjective (J i : W' i →ₗ[𝕜] W i) hinj).symm y = x := by
        rw [LinearEquiv.symm_apply_eq]; exact Subtype.ext hx.symm
      rw [e, ← Submodule.norm_coe, ← hx, ContinuousLinearMap.coe_coe, norm_apply_of_inner hs hJ,
        ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 hs).ne', one_mul]

omit [∀ (i : ι), CompleteSpace (W i)] [∀ (i : ι), CompleteSpace (W' i)] in
@[simp] theorem coe_rangeEquiv (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) (i : ι) (x : W' i) :
    (rangeEquiv hs hJ i x : W i) = J i x := rfl

omit [∀ (i : ι), CompleteSpace (W i)] [∀ (i : ι), CompleteSpace (W' i)] in
theorem J_rangeEquiv_symm (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) (i : ι)
    (y : LinearMap.range (J i : W' i →ₗ[𝕜] W i)) : J i ((rangeEquiv hs hJ i).symm y) = y := by
  rw [← coe_rangeEquiv hs hJ, ContinuousLinearEquiv.apply_symm_apply]

omit [∀ (i : ι), CompleteSpace (W i)] [∀ (i : ι), CompleteSpace (W' i)] in
/-- The inverse of `rangeEquiv` scales inner products by `s⁻¹`. -/
theorem inner_rangeEquiv_symm (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) (i : ι)
    (a b : LinearMap.range (J i : W' i →ₗ[𝕜] W i)) :
    ⟪(rangeEquiv hs hJ i).symm a, (rangeEquiv hs hJ i).symm b⟫_𝕜 = ((s⁻¹ : ℝ) : 𝕜) * ⟪a, b⟫_𝕜 := by
  have hs' : (s : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hs.ne'
  rw [Submodule.coe_inner, ← J_rangeEquiv_symm hs hJ i a, ← J_rangeEquiv_symm hs hJ i b, hJ,
    RCLike.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hs', one_mul]

variable [∀ i, (LinearMap.range (J i : W' i →ₗ[𝕜] W i)).HasOrthogonalProjection]

instance (i : ι) : CompleteSpace (LinearMap.range (J i : W' i →ₗ[𝕜] W i)) :=
  Submodule.completeSpace_of_hasOrthogonalProjection _

variable (H J)

/-- **The compression of `H` along scaled isometric embeddings** `J i : W' i → W i`
(`⟪J x, J y⟫ = s ⟪x, y⟫`) whose ranges form a reducing subcomplex: the reducing subcomplex
`R(J)` transported to `W'`, so that `d' = J⁻¹ d J` on `{x | J x ∈ D(d)}`. -/
def compress (hs : 0 < s) (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) : HilbertComplex 𝕜 c W' :=
  hR.toHilbertComplex.transport (fun i => (rangeEquiv hs hJ i).symm) (fun _ _ => 1)
    fun _ _ => one_ne_zero

variable {H J}

theorem mem_compress_domain_iff (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) {i j : ι} {x : W' i} :
    x ∈ ((H.compress J hs hJ hR).d i j).domain ↔ J i x ∈ (H.d i j).domain := by
  change (rangeEquiv hs hJ i).symm.symm x ∈ ((hR.reduces i j).part).domain ↔ _
  rw [ContinuousLinearEquiv.symm_symm, LinearPMap.IsReducingPair.mem_part_domain]
  rfl

/-- **`J d' = d J`**: the compressed differentials are `J⁻¹ d J`. -/
theorem J_compress_d (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) {i j : ι}
    (x : ((H.compress J hs hJ hR).d i j).domain) :
    J j ((H.compress J hs hJ hR).d i j x) =
      H.d i j ⟨J i x, (mem_compress_domain_iff hs hJ hR).1 x.2⟩ := by
  change J j ((1 : 𝕜) • (rangeEquiv hs hJ j).symm ((hR.reduces i j).part
    ⟨(rangeEquiv hs hJ i).symm.symm x, _⟩)) = _
  rw [one_smul, J_rangeEquiv_symm, LinearPMap.IsReducingPair.part_apply]
  rfl

/-- **The adjoints of the compressed complex are the compressions of the adjoints.** -/
theorem adjoint_compress_d (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) (i j : ι) :
    ((H.compress J hs hJ hR).d i j)† = (H.dual.compress J hs hJ hR.dual).d j i := by
  have he := inner_rangeEquiv_symm hs hJ
  change (transportD hR.toHilbertComplex (fun i => (rangeEquiv hs hJ i).symm)
    (fun _ _ => (1 : 𝕜)) i j)† = transportD hR.dual.toHilbertComplex
      (fun i => (rangeEquiv hs hJ i).symm) (fun _ _ => (1 : 𝕜)) j i
  rw [adjoint_transportD (inv_pos.2 hs) he one_ne_zero]
  have hK : hR.toHilbertComplex.dual = hR.dual.toHilbertComplex :=
    ext_d (funext fun a => funext fun b => hR.dual_toHilbertComplex_d a b)
  have hκ : (fun a b : ι => (starRingEnd 𝕜) ((fun _ _ : ι => (1 : 𝕜)) b a)) = fun _ _ => 1 := by
    funext a b; simp
  rw [hK, hκ]

theorem mem_adjoint_compress_iff (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) {i j : ι} {y : W' j} :
    y ∈ (((H.compress J hs hJ hR).d i j)†).domain ↔ J j y ∈ ((H.d i j)†).domain := by
  rw [adjoint_compress_d]
  exact mem_compress_domain_iff hs hJ hR.dual

/-- **`J d'† = d† J`.** -/
theorem J_adjoint_compress_d (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) {i j : ι}
    (y : (((H.compress J hs hJ hR).d i j)†).domain) :
    J i (((H.compress J hs hJ hR).d i j)† y) =
      (H.d i j)† ⟨J j y, (mem_adjoint_compress_iff hs hJ hR).1 y.2⟩ := by
  have hy : (y : W' j) ∈ ((H.dual.compress J hs hJ hR.dual).d j i).domain := by
    rw [← adjoint_compress_d]; exact y.2
  rw [apply_eq_of_eq (adjoint_compress_d hs hJ hR i j) y ⟨_, hy⟩ rfl]
  exact J_compress_d hs hJ hR.dual ⟨_, hy⟩

/-- **A compression is a scaled embedding** into the original complex (scale `s`, chain-rule
factors `1`). -/
def ScaledEmbedding.ofCompress (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) :
    ScaledEmbedding (H.compress J hs hJ hR) H where
  J := J
  scale _ := s
  scale_pos _ := hs
  inner_J := hJ
  dScale _ _ := 1
  dScale_ne_zero _ _ := one_ne_zero
  mapsTo i j x := (mem_compress_domain_iff hs hJ hR).1 x.2
  comm i j x := by rw [one_smul, J_compress_d]
  mem_domain_of_map i j x h := (mem_compress_domain_iff hs hJ hR).2 h

variable [Fintype ι]

/-- The componentwise map `∏ W' i → ∏ W i`. -/
def totalJ (J : ∀ i, W' i →L[𝕜] W i) : PiLp 2 W' →L[𝕜] PiLp 2 W :=
  ((PiLp.continuousLinearEquiv 2 𝕜 W).symm : (∀ i, W i) →L[𝕜] PiLp 2 W).comp
    ((ContinuousLinearMap.pi fun i => (J i).comp (ContinuousLinearMap.proj i)).comp
      (PiLp.continuousLinearEquiv 2 𝕜 W' : PiLp 2 W' →L[𝕜] ∀ i, W' i))

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (W' i)]
  [∀ i, (LinearMap.range (J i : W' i →ₗ[𝕜] W i)).HasOrthogonalProjection] [Fintype ι] in
theorem totalJ_apply (x : PiLp 2 W') (i : ι) : totalJ J x i = J i (x i) := rfl

/-- **The compression intertwines the wave operators**: `J L' = L J`. -/
theorem wave_compress (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) :
    Intertwines (totalJ J) (H.compress J hs hJ hR).wave H.wave := by
  have hmem : ∀ x : (H.compress J hs hJ hR).wave.domain, totalJ J (x : PiLp 2 W') ∈ H.wave.domain :=
    fun x => (mem_wave_domain _).2 ⟨fun i j => (mem_compress_domain_iff hs hJ hR).1 (x.2.1 i j),
      fun i j => (mem_adjoint_compress_iff hs hJ hR).1 (x.2.2 j i)⟩
  refine ⟨hmem, fun x => PiLp.ext fun j => ?_⟩
  rw [wave_apply, totalJ_apply, wave_apply, _root_.map_sub, map_sum, map_sum]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun k _ => ?_)
  · exact (J_compress_d hs hJ hR ⟨_, x.2.1 i j⟩).symm
  · exact (J_adjoint_compress_d hs hJ hR ⟨_, x.2.2 k j⟩).symm

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  [∀ i, NormedSpace ℝ (W' i)] [∀ i, IsScalarTower ℝ 𝕜 (W' i)]

/-- **The wave group of a compression is the restriction of the wave group**:
`J e^{tL'} = e^{tL} J`. -/
theorem waveGroup_compress (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) (t : ℝ) (x : PiLp 2 W') :
    totalJ J ((H.compress J hs hJ hR).waveGroup.S t x) = H.waveGroup.S t (totalJ J x) := by
  have h := wave_compress hs hJ hR
  rw [← generator_waveGroup, ← generator_waveGroup] at h
  exact H.isIsometric_waveGroup.intertwines_S _ h t x

end Compression

end Feec.HilbertComplex
