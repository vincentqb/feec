module

public import Feec.HilbertComplex.Compactness
public import Feec.HilbertComplex.Equivariant
public import Feec.HilbertComplex.InvariantCoreSpectral

/-!
# Compactness, closed range, harmonic forms and eigenbases of compressed complexes

A reducing subcomplex `S` of a Hilbert complex `H` is a Hilbert complex
(`Feec.HilbertComplex.ReducingSubcomplex.toHilbertComplex`), whose differentials and adjoints are
the parts of those of `H` (`LinearPMap.IsReducingPair.adjoint_part`). This file shows that the
Hodge-theoretic and spectral properties of `H` pass to the compression:

* **the compactness property** (`ReducingSubcomplex.hasCompactPropertyAt_toHilbertComplex`):
  the box `‖x‖, ‖d x‖, ‖d† x‖ ≤ 1` of `S` is the box of `H` intersected with `S`, a closed
  subspace; more generally compactness pulls back along closed embeddings with bounded
  distortion of `d` and `d†` (`HasCompactPropertyAt.of_isClosedEmbedding`), e.g. along
  transport (`hasCompactPropertyAt_transport`) and compression along scaled isometries
  (`hasCompactPropertyAt_compress`);
* **closed range** and the **Poincaré inequality** with the same constant
  (`ReducingSubcomplex.norm_le_of_mem_orthogonal`): `R(d|_S) = R(d) ∩ S` and
  `N(d|_S)ᗮ ⊆ N(d)ᗮ`;
* **the harmonic forms of the compression are the harmonic forms lying in `S`**
  (`ReducingSubcomplex.mem_harmonic_toHilbertComplex_iff`);
* **`EigenDense`** (`ReducingSubcomplex.eigenDense_toHilbertComplex`): the projection onto `S`
  commutes with the wave operator, so it maps eigenvectors of `L²` to eigenvectors of `L_S²`,
  and it is onto; the same for transport along uniformly scaled isometries
  (`eigenDense_transport`) and compressions (`eigenDense_compress`). The abstract statement is
  `LinearPMap.dense_span_isEigenSq_of_map`: a map with dense range intertwining the generators
  up to a real factor transports a dense set of eigenvectors.

For a finite unitary action (`Feec.HilbertComplex.Action`) all of this applies to the fixed
complex of the method of images (`Action.hasCompactPropertyAt_fixedComplex`,
`Action.eigenDense_fixedComplex`, …).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1.3 (compactness property), §4.3 (compactness of the de Rham complex)
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6 (parts of operators in
  reducing subspaces)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (compactness property), §4.10 (the cube by compression of the torus)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

/-! ### Eigenvectors of `A²` along intertwining maps -/

namespace LinearPMap

variable {𝕜 E E' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedSpace ℝ E'] [IsScalarTower ℝ 𝕜 E']
  {A : E →ₗ.[𝕜] E} {B : E' →ₗ.[𝕜] E'}

/-- **Eigenvectors of `A²` map to eigenvectors of `B²`** under `Q` with `Q D(A) ⊆ D(B)` and
`B Q = c Q A` (`c` real): `A² v = -ω² v ⇒ B² (Q v) = -(c ω)² Q v`. -/
theorem IsEigenSq.of_map (Q : E →L[𝕜] E') (c : ℝ)
    (hQ : ∀ x : A.domain, ∃ h : Q x ∈ B.domain, B ⟨Q x, h⟩ = (c : 𝕜) • Q (A x))
    {ω : ℝ} {v : E} (hv : A.IsEigenSq ω v) : B.IsEigenSq (c * ω) (Q v) := by
  obtain ⟨h, h', e⟩ := hv
  obtain ⟨h1, e1⟩ := hQ ⟨v, h⟩
  obtain ⟨h2, e2⟩ := hQ ⟨_, h'⟩
  have hm : B ⟨Q v, h1⟩ ∈ B.domain := by rw [e1]; exact B.domain.smul_mem _ h2
  refine ⟨h1, hm, ?_⟩
  have hx : (⟨B ⟨Q v, h1⟩, hm⟩ : B.domain) = (c : 𝕜) • ⟨Q (A ⟨v, h⟩), h2⟩ := Subtype.ext e1
  rw [hx, LinearPMap.map_smul, e2, e, ContinuousLinearMap.map_smul_of_tower,
    ← RCLike.real_smul_eq_coe_smul (K := 𝕜), ← RCLike.real_smul_eq_coe_smul (K := 𝕜),
    smul_smul, smul_smul]
  congr 1
  ring

/-- **A dense set of eigenvectors transports along a map with dense range** intertwining the
operators up to a real factor. -/
theorem dense_span_isEigenSq_of_map
    (hD : Dense (Submodule.span 𝕜 {v | ∃ ω, A.IsEigenSq ω v} : Set E))
    (Q : E →L[𝕜] E') (hQd : DenseRange Q) (c : ℝ)
    (hQ : ∀ x : A.domain, ∃ h : Q x ∈ B.domain, B ⟨Q x, h⟩ = (c : 𝕜) • Q (A x)) :
    Dense (Submodule.span 𝕜 {v | ∃ ω, B.IsEigenSq ω v} : Set E') := by
  have hle : (Submodule.span 𝕜 {v | ∃ ω, A.IsEigenSq ω v}).map (Q : E →ₗ[𝕜] E') ≤
      Submodule.span 𝕜 {v | ∃ ω, B.IsEigenSq ω v} := by
    rw [Submodule.map_span_le]
    rintro v ⟨ω, hv⟩
    exact Submodule.subset_span ⟨c * ω, hv.of_map Q c hQ⟩
  refine Dense.mono hle ?_
  rw [Submodule.map_coe]
  exact hQd.dense_image Q.continuous hD

end LinearPMap

namespace Feec.C0Group

variable {𝕜 E E' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedSpace ℝ E'] [IsScalarTower ℝ 𝕜 E']
  [CompleteSpace E']

omit [CompleteSpace E] [CompleteSpace E'] in
/-- **`EigenDense` transports along intertwining maps with dense range.** -/
theorem EigenDense.of_map {G : C0Group 𝕜 E} {G' : C0Group 𝕜 E'} (hD : G.EigenDense)
    (Q : E →L[𝕜] E') (hQd : DenseRange Q) (c : ℝ)
    (hQ : ∀ x : G.generator.domain, ∃ h : Q x ∈ G'.generator.domain,
      G'.generator ⟨Q x, h⟩ = (c : 𝕜) • Q (G.generator x)) : G'.EigenDense :=
  LinearPMap.dense_span_isEigenSq_of_map hD Q hQd c hQ

end Feec.C0Group

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

/-! ### The compactness property along closed embeddings -/

section Embedding

variable {ι' : Type*} {c' : ComplexShape ι'} {W' : ι' → Type*}
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)] [∀ i, CompleteSpace (W' i)]
  {H' : HilbertComplex 𝕜 c' W'}

/-- **The compactness property pulls back along closed embeddings** `J : Wⁱ → W'ⁱ'` mapping
`D(d) ∩ D(d†)` into `D(d') ∩ D(d'†)` with `‖d' J x‖ ≤ C ‖d x‖` and `‖d'† J x‖ ≤ C' ‖d† x‖`. -/
theorem HasCompactPropertyAt.of_isClosedEmbedding {i : ι} {i' : ι'}
    (h : H'.HasCompactPropertyAt i') (J : W i →L[𝕜] W' i') (hJ : Topology.IsClosedEmbedding J)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hd : ∀ x : (H.d i (c.next i)).domain, ∃ hx : J x ∈ (H'.d i' (c'.next i')).domain,
      ‖H'.d i' (c'.next i') ⟨J x, hx⟩‖ ≤ C * ‖H.d i (c.next i) x‖)
    (hd' : ∀ x : ((H.d (c.prev i) i)†).domain, ∃ hx : J x ∈ ((H'.d (c'.prev i') i')†).domain,
      ‖(H'.d (c'.prev i') i')† ⟨J x, hx⟩‖ ≤ C' * ‖(H.d (c.prev i) i)† x‖) :
    H.HasCompactPropertyAt i := by
  set R : ℝ := max (max ‖J‖ C) (max C' 1)
  obtain ⟨K, hK, hsub⟩ := h.exists_isCompact R
  refine ⟨J ⁻¹' K, hJ.isCompact_preimage hK, fun x hx hx' h1 h2 h3 => ?_⟩
  obtain ⟨hy, ey⟩ := hd ⟨x, hx⟩
  obtain ⟨hy', ey'⟩ := hd' ⟨x, hx'⟩
  refine hsub (J x) hy hy' ?_ (ey.trans ?_) (ey'.trans ?_)
  · refine (J.le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) h1).trans ?_)
    exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (mul_le_of_le_one_right hC h2).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (mul_le_of_le_one_right hC' h3).trans ((le_max_left _ _).trans (le_max_right _ _))

end Embedding

/-! ### Compression onto a reducing subcomplex -/

namespace ReducingSubcomplex

variable {S : ∀ i, Submodule 𝕜 (W i)} [∀ i, CompleteSpace (S i)]

/-- The adjoints of the compressed differentials are the parts of the adjoints. -/
theorem adjoint_toHilbertComplex_d (h : H.ReducingSubcomplex S) (i j : ι) :
    (h.toHilbertComplex.d i j)† = (h.dual.reduces j i).part :=
  h.dual_toHilbertComplex_d j i

theorem mem_adjoint_toHilbertComplex_d_domain_iff (h : H.ReducingSubcomplex S) {i j : ι}
    {x : S j} : x ∈ ((h.toHilbertComplex.d i j)†).domain ↔ (x : W j) ∈ ((H.d i j)†).domain := by
  rw [adjoint_toHilbertComplex_d]; exact Iff.rfl

theorem coe_adjoint_toHilbertComplex_d (h : H.ReducingSubcomplex S) {i j : ι}
    (x : ((h.toHilbertComplex.d i j)†).domain) :
    (((h.toHilbertComplex.d i j)† x : S i) : W i) =
      (H.d i j)† ⟨(x : S j), (mem_adjoint_toHilbertComplex_d_domain_iff h).1 x.2⟩ := by
  have hx : (x : S j) ∈ ((h.dual.reduces j i).part).domain := by
    rw [← adjoint_toHilbertComplex_d]; exact x.2
  rw [apply_eq_of_eq (adjoint_toHilbertComplex_d h i j) x ⟨_, hx⟩ rfl,
    IsReducingPair.part_apply]
  rfl

/-- **The compactness property passes to the compression**: the box of `S` is the box of `H`
intersected with the closed subspace `S`. -/
theorem hasCompactPropertyAt_toHilbertComplex (h : H.ReducingSubcomplex S) {i : ι}
    (hc : H.HasCompactPropertyAt i) : h.toHilbertComplex.HasCompactPropertyAt i := by
  have hiso : Isometry ((S i).subtypeL : S i →L[𝕜] W i) := isometry_subtype_coe
  refine hc.of_isClosedEmbedding (S i).subtypeL hiso.isClosedEmbedding zero_le_one zero_le_one
    (fun x => ⟨x.2, ?_⟩) fun x => ⟨(mem_adjoint_toHilbertComplex_d_domain_iff h).1 x.2, ?_⟩
  · rw [one_mul]; rfl
  · rw [one_mul, ← Submodule.norm_coe, coe_adjoint_toHilbertComplex_d]; rfl

theorem mem_ker_part_iff (h : H.ReducingSubcomplex S) {i j : ι} {x : S i} :
    x ∈ (h.toHilbertComplex.d i j).ker ↔ (x : W i) ∈ (H.d i j).ker := by
  rw [LinearPMap.mem_ker_iff, LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact ⟨⟨_, y.2⟩, rfl, congrArg Subtype.val hy⟩
  · rintro ⟨y, hyx, hy⟩
    refine ⟨⟨x, show (x : W i) ∈ (H.d i j).domain from hyx ▸ y.2⟩, rfl, Subtype.ext ?_⟩
    change H.d i j ⟨(x : W i), _⟩ = 0
    rw [← hy]; exact apply_congr' _ _ _ hyx

theorem mem_ker_adjoint_part_iff (h : H.ReducingSubcomplex S) {i j : ι} {x : S j} :
    x ∈ ((h.toHilbertComplex.d i j)†).ker ↔ (x : W j) ∈ ((H.d i j)†).ker := by
  rw [adjoint_toHilbertComplex_d]
  exact (h.dual.mem_ker_part_iff (i := j) (j := i))

/-- **The harmonic forms of the compression are the harmonic forms of `H` lying in `S`.** -/
theorem mem_harmonic_toHilbertComplex_iff (h : H.ReducingSubcomplex S) {i : ι} {x : S i} :
    x ∈ h.toHilbertComplex.harmonic i ↔ (x : W i) ∈ H.harmonic i := by
  change x ∈ (h.toHilbertComplex.d i (c.next i)).ker ⊓ ((h.toHilbertComplex.d (c.prev i) i)†).ker ↔
    (x : W i) ∈ (H.d i (c.next i)).ker ⊓ ((H.d (c.prev i) i)†).ker
  rw [Submodule.mem_inf, Submodule.mem_inf, h.mem_ker_part_iff, h.mem_ker_adjoint_part_iff]

/-- **The Poincaré inequality passes to the compression, with the same constant**:
`N(d|_S)ᗮ ⊆ N(d)ᗮ` inside `S`. -/
theorem norm_le_of_mem_orthogonal (h : H.ReducingSubcomplex S) {i j : ι} {C : ℝ}
    (hP : ∀ u : (H.d i j).domain, (u : W i) ∈ (H.d i j).kerᗮ → ‖(u : W i)‖ ≤ C * ‖H.d i j u‖)
    (u : (h.toHilbertComplex.d i j).domain)
    (hu : (u : S i) ∈ (h.toHilbertComplex.d i j).kerᗮ) :
    ‖(u : S i)‖ ≤ C * ‖h.toHilbertComplex.d i j u‖ := by
  have hu' : ((u : S i) : W i) ∈ (H.d i j).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hz
    have hPy : (⟨(S i).starProjection (y : W i), (S i).starProjection_apply_mem _⟩ : S i) ∈
        (h.toHilbertComplex.d i j).ker := by
      rw [h.mem_ker_part_iff, LinearPMap.mem_ker_iff]
      refine ⟨⟨_, (h.reduces i j).proj_mem y⟩, rfl, ?_⟩
      rw [(h.reduces i j).comm y, hy, _root_.map_zero]
    have h0 := Submodule.inner_right_of_mem_orthogonal hPy hu
    rw [Submodule.coe_inner] at h0
    change ⟪(y : W i), ((u : S i) : W i)⟫_𝕜 = 0
    rw [← (S i).starProjection_eq_self_iff.2 (u : S i).2,
      ← Submodule.inner_starProjection_left_eq_right]
    exact h0
  exact hP ⟨_, u.2⟩ hu'

variable [Fintype ι]

/-- **The wave domain of the compression** is the preimage of the wave domain. -/
theorem mem_wave_domain_toHilbertComplex_iff (h : H.ReducingSubcomplex S)
    {y : PiLp 2 fun i => S i} :
    y ∈ h.toHilbertComplex.wave.domain ↔ totalIncl S y ∈ H.wave.domain := by
  rw [mem_wave_domain, mem_wave_domain]
  refine and_congr (forall_congr' fun i => forall_congr' fun j => ?_)
    (forall_congr' fun i => forall_congr' fun j => ?_)
  · exact (h.reduces i j).mem_part_domain
  · exact h.mem_adjoint_toHilbertComplex_d_domain_iff

/-- The orthogonal projection `∏ W i → ∏ S i`. -/
def totalOrthProj (S : ∀ i, Submodule 𝕜 (W i)) [∀ i, (S i).HasOrthogonalProjection] :
    PiLp 2 W →L[𝕜] PiLp 2 fun i => S i :=
  ((PiLp.continuousLinearEquiv 2 𝕜 fun i => S i).symm : (∀ i, S i) →L[𝕜] _).comp
    ((ContinuousLinearMap.pi fun i => (S i).orthogonalProjectionOnto.comp
      (ContinuousLinearMap.proj i)).comp
      (PiLp.continuousLinearEquiv 2 𝕜 W : PiLp 2 W →L[𝕜] ∀ i, W i))

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (S i)] [Fintype ι] in
theorem totalOrthProj_apply [∀ i, (S i).HasOrthogonalProjection] (x : PiLp 2 W) (i : ι) :
    totalOrthProj S x i = (S i).orthogonalProjectionOnto (x i) := rfl

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (S i)] in
theorem totalIncl_totalOrthProj [∀ i, (S i).HasOrthogonalProjection] (x : PiLp 2 W) :
    totalIncl S (totalOrthProj S x) = (totalSub S).starProjection x :=
  PiLp.ext fun i => by rw [totalIncl_apply, totalOrthProj_apply, totalSub_starProjection_apply]; rfl

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (S i)] in
theorem totalOrthProj_totalIncl [∀ i, (S i).HasOrthogonalProjection]
    (y : PiLp 2 fun i => S i) : totalOrthProj S (totalIncl S y) = y :=
  PiLp.ext fun i => by
    rw [totalOrthProj_apply, totalIncl_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (S i)] in
theorem surjective_totalOrthProj [∀ i, (S i).HasOrthogonalProjection] :
    Function.Surjective (totalOrthProj S) := fun y => ⟨_, totalOrthProj_totalIncl y⟩

/-- **The projection onto a reducing subcomplex intertwines the wave operators**:
`P D(L) ⊆ D(L_S)` and `L_S P = P L`. -/
theorem wave_totalOrthProj (h : H.ReducingSubcomplex S) (x : H.wave.domain) :
    ∃ hx : totalOrthProj S x ∈ h.toHilbertComplex.wave.domain,
      h.toHilbertComplex.wave ⟨_, hx⟩ = ((1 : ℝ) : 𝕜) • totalOrthProj S (H.wave x) := by
  have hR := h.isReducing_wave
  have hP : totalIncl S (totalOrthProj S x) ∈ H.wave.domain := by
    rw [totalIncl_totalOrthProj]; exact hR.proj_mem x
  have hx := h.mem_wave_domain_toHilbertComplex_iff.2 hP
  refine ⟨hx, (totalIncl S).injective ?_⟩
  rw [RCLike.ofReal_one, one_smul]
  have e := h.wave_toHilbertComplex.comm ⟨_, hx⟩
  calc totalIncl S (h.toHilbertComplex.wave ⟨_, hx⟩)
      = H.wave ⟨totalIncl S (totalOrthProj S x), hP⟩ := e.symm
    _ = H.wave ⟨(totalSub S).starProjection x, hR.proj_mem x⟩ :=
        apply_congr' _ _ _ (totalIncl_totalOrthProj _)
    _ = (totalSub S).starProjection (H.wave x) := hR.comm x
    _ = totalIncl S (totalOrthProj S (H.wave x)) := (totalIncl_totalOrthProj _).symm

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **`EigenDense` passes to the compression**: the projection onto `∏ S i` commutes with the
generator, so it maps eigenvectors of `L²` onto eigenvectors of `L_S²`, and it is onto. -/
theorem eigenDense_toHilbertComplex (h : H.ReducingSubcomplex S) (hD : H.waveGroup.EigenDense) :
    h.toHilbertComplex.waveGroup.EigenDense := by
  unfold C0Group.EigenDense at hD ⊢
  rw [generator_waveGroup] at hD ⊢
  exact LinearPMap.dense_span_isEigenSq_of_map hD (totalOrthProj S)
    surjective_totalOrthProj.denseRange 1 h.wave_totalOrthProj

end ReducingSubcomplex

/-! ### Transport and compression along scaled isometries -/

section Transport

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)] {e : ∀ i, W i ≃L[𝕜] W' i} {s : ℝ}

omit [∀ i, CompleteSpace (W' i)] in
/-- A transported differential distorts norms by at most `|κ|⁻¹ ‖e⁻¹‖`. -/
theorem norm_d_le_transport {κ : ι → ι → 𝕜} (hκ : ∀ i j, κ i j ≠ 0) {i j : ι}
    (x : (transportD H e κ i j).domain) :
    ‖H.d i j ⟨((e i).symm : W' i →L[𝕜] W i) x, x.2⟩‖ ≤
      (‖κ i j‖⁻¹ * ‖((e j).symm : W' j →L[𝕜] W j)‖) * ‖transportD H e κ i j x‖ := by
  have h1 : transportD H e κ i j x =
      κ i j • e j (H.d i j ⟨((e i).symm : W' i →L[𝕜] W i) x, x.2⟩) := transportD_apply x
  have h2 : H.d i j ⟨((e i).symm : W' i →L[𝕜] W i) x, x.2⟩ =
      (κ i j)⁻¹ • (e j).symm (transportD H e κ i j x) := by
    rw [h1, _root_.map_smul, ContinuousLinearEquiv.symm_apply_apply, inv_smul_smul₀ (hκ i j)]
  rw [h2, norm_smul, norm_inv, mul_assoc]
  gcongr
  exact ContinuousLinearMap.le_opNorm ((e j).symm : W' j →L[𝕜] W j) _

/-- **The compactness property passes to transports** along uniformly scaled isometries, with
any nonzero chain-rule factors. -/
theorem hasCompactPropertyAt_transport (hs : 0 < s)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) {κ : ι → ι → 𝕜}
    (hκ : ∀ i j, κ i j ≠ 0) {i : ι} (hc : H.HasCompactPropertyAt i) :
    (H.transport e κ hκ).HasCompactPropertyAt i := by
  have hκ' : ∀ a b, (fun a b => (starRingEnd 𝕜) (κ b a)) a b ≠ 0 := fun a b => by
    simpa using hκ b a
  refine hc.of_isClosedEmbedding ((e i).symm : W' i →L[𝕜] W i)
    (e i).symm.toHomeomorph.isClosedEmbedding
    (C := ‖κ i (c.next i)‖⁻¹ * ‖((e (c.next i)).symm : W' (c.next i) →L[𝕜] W (c.next i))‖)
    (C' := ‖κ (c.prev i) i‖⁻¹ * ‖((e (c.prev i)).symm : W' (c.prev i) →L[𝕜] W (c.prev i))‖)
    (by positivity) (by positivity) (fun x => ⟨x.2, norm_d_le_transport hκ x⟩) fun x => ?_
  have hadj := adjoint_transportD (H := H) hs he (hκ (c.prev i) i)
  have hx : (x : W' i) ∈
      (transportD H.dual e (fun a b => (starRingEnd 𝕜) (κ b a)) i (c.prev i)).domain := by
    rw [← hadj]; exact x.2
  refine ⟨hx, ?_⟩
  have e0 := apply_eq_of_eq hadj x ⟨_, hx⟩ rfl
  have hb := norm_d_le_transport (H := H.dual) hκ' ⟨_, hx⟩
  change ‖(H.d (c.prev i) i)† ⟨_, hx⟩‖ ≤ _ * ‖(transportD H e κ (c.prev i) i)† x‖
  rw [e0]
  simpa using hb

variable [Fintype ι] [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  [∀ i, NormedSpace ℝ (W' i)] [∀ i, IsScalarTower ℝ 𝕜 (W' i)]

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (W' i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ 𝕜 (W i)] [∀ i, NormedSpace ℝ (W' i)] [∀ i, IsScalarTower ℝ 𝕜 (W' i)]
  [Fintype ι] in
theorem surjective_totalMap : Function.Surjective (totalMap e) := fun y =>
  ⟨WithLp.toLp 2 fun i => (e i).symm (y i), PiLp.ext fun i => (e i).apply_symm_apply (y i)⟩

/-- **`EigenDense` passes to transports** along uniformly scaled isometries (chain-rule
factors `1`). -/
theorem eigenDense_transport (hs : 0 < s)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) (hD : H.waveGroup.EigenDense) :
    (H.transport e (fun _ _ => 1) fun _ _ => one_ne_zero).waveGroup.EigenDense := by
  unfold C0Group.EigenDense at hD ⊢
  rw [generator_waveGroup] at hD ⊢
  have hI := wave_transport (H := H) hs he
  refine LinearPMap.dense_span_isEigenSq_of_map hD (totalMap e) surjective_totalMap.denseRange 1
    fun x => ⟨hI.mapsTo x, ?_⟩
  rw [hI.comm x, RCLike.ofReal_one, one_smul]

end Transport

section Compression

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)] {J : ∀ i, W' i →L[𝕜] W i} {s : ℝ}
  [∀ i, (LinearMap.range (J i : W' i →ₗ[𝕜] W i)).HasOrthogonalProjection]

/-- **The compactness property passes to compressions** along scaled isometric embeddings. -/
theorem hasCompactPropertyAt_compress (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i)) {i : ι}
    (hc : H.HasCompactPropertyAt i) : (H.compress J hs hJ hR).HasCompactPropertyAt i :=
  hasCompactPropertyAt_transport (inv_pos.2 hs) (inner_rangeEquiv_symm hs hJ) _
    (hR.hasCompactPropertyAt_toHilbertComplex hc)

theorem hasCompactProperty_compress (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i))
    (hc : H.HasCompactProperty) : (H.compress J hs hJ hR).HasCompactProperty := fun _ =>
  hasCompactPropertyAt_compress hs hJ hR (hc _)

variable [Fintype ι] [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  [∀ i, NormedSpace ℝ (W' i)] [∀ i, IsScalarTower ℝ 𝕜 (W' i)]

/-- **`EigenDense` passes to compressions** along scaled isometric embeddings. -/
theorem eigenDense_compress (hs : 0 < s)
    (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i))
    (hD : H.waveGroup.EigenDense) : (H.compress J hs hJ hR).waveGroup.EigenDense :=
  eigenDense_transport (inv_pos.2 hs) (inner_rangeEquiv_symm hs hJ)
    (hR.eigenDense_toHilbertComplex hD)

end Compression

/-! ### The method of images -/

namespace Action

variable {Γ : Type*} [Group Γ] [Fintype Γ] (A : H.Action Γ)

/-- **The compactness property passes to the fixed complex** of a finite unitary action. -/
theorem hasCompactPropertyAt_fixedComplex {i : ι} (hc : H.HasCompactPropertyAt i) :
    A.fixedComplex.HasCompactPropertyAt i :=
  A.reducingSubcomplex_fixed.hasCompactPropertyAt_toHilbertComplex hc

theorem hasCompactProperty_fixedComplex (hc : H.HasCompactProperty) :
    A.fixedComplex.HasCompactProperty := fun _ => A.hasCompactPropertyAt_fixedComplex (hc _)

/-- **The harmonic forms of the fixed complex are the fixed harmonic forms.** -/
theorem mem_harmonic_fixedComplex_iff {i : ι} {x : A.fixed i} :
    x ∈ A.fixedComplex.harmonic i ↔ (x : W i) ∈ H.harmonic i :=
  A.reducingSubcomplex_fixed.mem_harmonic_toHilbertComplex_iff

variable [Fintype ι] [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **`EigenDense` passes to the fixed complex** of a finite unitary action. -/
theorem eigenDense_fixedComplex (hD : H.waveGroup.EigenDense) :
    A.fixedComplex.waveGroup.EigenDense :=
  A.reducingSubcomplex_fixed.eigenDense_toHilbertComplex hD

end Action

end Feec.HilbertComplex
