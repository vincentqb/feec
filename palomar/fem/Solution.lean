module

public import Solution.Complex
public import Solution.Forms
public import Solution.Spaces
public import Solution.Regularity
public import Feec.Models.Parallelepiped.StarShaped

/-!
# Finite element exterior calculus on polyhedral domains (solution)

The compared theorems of `Challenge.lean`. `FEEC.fem` and `FEEC.femMin` from the finite element
theory of `Feec.Models.StarShaped.PolyFiniteElement` on the star domain and the mesh family of the
challenge (`starDomainOf`, `meshFamilyOf`): the complexes `MeshFamily.poly` and
`MeshFamily.polyMin` of the admissible sequence (whose spaces are the challenge's,
`mem_V_iff`, `mem_V₀_iff`), the uniformly bounded smoothed projections
(`MeshFamily.exists_uniform_polyProj`, `_Min`), the graph-norm density
(`MeshFamily.eventually_exists_poly_graph`, `_Min`) and the interpolation error
(`MeshFamily.exists_mem_poly_le_of_isCsForm`, `_Min`); the complexes are `Feec`'s `HΛ(Ω)` and
`H̊Λ(Ω)` (`dMax_eq`, `dMin_eq`). `FEEC.fem_parallelepiped` from
`Feec.Models.StarShaped.ParallelepipedWitness` (the star domain and the image Freudenthal meshes
of `A (0, ½)ⁿ + b`, here with the matrix `2 A`) and `Feec.Models.Parallelepiped.closedRangeAt`,
`closedRangeAt_min`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2, §5.5
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Filter Topology Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.StarShaped HilbertComplex

variable {n : ℕ}

theorem dMax_eq_complex [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) (k : ℤ) :
    (starDomainOf hΩ).complex.d k (k + 1) = dMax Ω k := by
  rw [deRham_maximalComplex_d, dMax_eq]; rfl

theorem dMin_eq_complex [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) (k : ℤ) :
    (starDomainOf hΩ).complexMin.d k (k + 1) = dMin Ω k := by
  rw [deRham_minimalComplex_d, dMin_eq]; rfl

theorem fem [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMax Ω k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpace Ω (M N) S k) ∧
      (∃ C : ℝ, ∀ N i (x : (H.d i (i + 1)).domain),
        ‖((F.π N).π i x : L2Form Ω i)‖ ≤ C * ‖(x : L2Form Ω i)‖) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      ∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsCsForm Ω s j L x := by
  set D := starDomainOf hΩ
  set Fm := meshFamilyOf hΩ hM
  obtain ⟨K, hK1, hK⟩ := Fm.exists_uniform_polyProj S.toFeec
  choose π hπ1 hπ2 using hK
  let H : HilbertComplex ℝ (L2Form Ω) := HilbertComplex.ofFeec D.complex
  let F : H.SubcomplexFamily ℕ :=
    { l := atTop
      V := fun N => Subcomplex.ofFeec (Fm.poly S.toFeec N)
      finiteDimensional := fun N i =>
        inferInstanceAs (FiniteDimensional ℝ ((Fm.poly S.toFeec N).V i))
      π := fun N => CochainProjection.ofFeec (π N) }
  let J : F.Jackson ℕ :=
    { meshSize := fun N => meshSize (M N)
      meshSize_nonneg := fun N => (hM.2.2.1 N).le
      tendsto_meshSize := hM.2.2.2
      Reg := fun s j L x => S.PolyOrderAt n s j ∧ IsCsForm Ω s j L x
      ord := fun s => s + 1
      B := fun _ => Fm.polyInterpBound S.toFeec
      jackson := fun s N i L x hL hx => by
        obtain ⟨v, hv, h1, h2⟩ := Fm.exists_mem_poly_le_of_isCsForm S.toFeec
          ((S.polyOrderAt_iff s i).1 hx.1) ((isCsForm_iff hΩ s i L x).1 hx.2) hL N
        have e : Fm.polyInterpBound S.toFeec i * L * (Fm.mesh N).meshSize ^ (s + 1) =
            Fm.polyInterpBound S.toFeec i * (L * meshSize (M N) ^ ((s : ℝ) + 1)) := by
          rw [show ((s : ℝ) + 1) = ((s + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            meshFamilyOf_mesh, SimplicialMesh.meshSize_toFeec]
          ring
        exact ⟨v, hv, e ▸ h1, fun j hxj => e ▸ h2 j hxj⟩ }
  refine ⟨H, F, J, fun k => dMax_eq_complex hΩ k, rfl, fun N k => ?_, ⟨K, fun N i x => ?_⟩,
    fun i => ⟨K, fun N x => ?_⟩, fun i => ?_, fun N => rfl, fun s => rfl, fun s j L x => Iff.rfl⟩
  · ext u
    exact mem_V_iff S (M N) Ω (hM.1 N) u
  · exact hπ1 N i x.1
  · refine H.graphNorm_le_of_sq (by linarith) ?_
    exact hπ2 N i (i + 1) x
  · refine H.approximates_of_eventually F i fun x ε hε => ?_
    exact Fm.eventually_exists_poly_graph S.toFeec i x.1 x.2 hε

theorem femMin [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMin Ω k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpaceMin Ω (M N) S k) ∧
      (∃ C : ℝ, ∀ N i (x : (H.d i (i + 1)).domain),
        ‖((F.π N).π i x : L2Form Ω i)‖ ≤ C * ‖(x : L2Form Ω i)‖) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      ∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsCsFormMin Ω s j L x := by
  set D := starDomainOf hΩ
  set Fm := meshFamilyOf hΩ hM
  obtain ⟨K, hK1, hK⟩ := Fm.exists_uniform_polyProjMin S.toFeec
  choose π hπ1 hπ2 using hK
  let H : HilbertComplex ℝ (L2Form Ω) := HilbertComplex.ofFeec D.complexMin
  let F : H.SubcomplexFamily ℕ :=
    { l := atTop
      V := fun N => Subcomplex.ofFeec (Fm.polyMin S.toFeec N)
      finiteDimensional := fun N i =>
        inferInstanceAs (FiniteDimensional ℝ ((Fm.polyMin S.toFeec N).V i))
      π := fun N => CochainProjection.ofFeec (π N) }
  let J : F.Jackson ℕ :=
    { meshSize := fun N => meshSize (M N)
      meshSize_nonneg := fun N => (hM.2.2.1 N).le
      tendsto_meshSize := hM.2.2.2
      Reg := fun s j L x => S.PolyOrderAt n s j ∧ IsCsFormMin Ω s j L x
      ord := fun s => s + 1
      B := fun _ => Fm.polyInterpBound S.toFeec
      jackson := fun s N i L x hL hx => by
        obtain ⟨v, hv, h1, h2⟩ := Fm.exists_mem_polyMin_le_of_isCsFormMin S.toFeec
          ((S.polyOrderAt_iff s i).1 hx.1) ((isCsFormMin_iff hΩ s i L x).1 hx.2) hL N
        have e : Fm.polyInterpBound S.toFeec i * L * (Fm.mesh N).meshSize ^ (s + 1) =
            Fm.polyInterpBound S.toFeec i * (L * meshSize (M N) ^ ((s : ℝ) + 1)) := by
          rw [show ((s : ℝ) + 1) = ((s + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            meshFamilyOf_mesh, SimplicialMesh.meshSize_toFeec]
          ring
        exact ⟨v, hv, e ▸ h1, fun j hxj => e ▸ h2 j hxj⟩ }
  refine ⟨H, F, J, fun k => dMin_eq_complex hΩ k, rfl, fun N k => ?_, ⟨K, fun N i x => ?_⟩,
    fun i => ⟨K, fun N x => ?_⟩, fun i => ?_, fun N => rfl, fun s => rfl, fun s j L x => Iff.rfl⟩
  · ext u
    exact mem_V₀_iff S (M N) Ω (hM.1 N) u
  · exact hπ1 N i x.1
  · refine H.graphNorm_le_of_sq (by linarith) ?_
    exact hπ2 N i (i + 1) x
  · refine H.approximates_of_eventually F i fun x ε hε => ?_
    exact Fm.eventually_exists_polyMin_graph S.toFeec i x.1 x.2 hε

/-! ### Parallelepipeds -/

/-- A `Feec` mesh as a mesh of the challenge. -/
def SimplicialMesh.ofFeec (M : Feec.Mesh.SimplicialMesh n) : SimplicialMesh n where
  simplices := M.simplices
  domain := M.domain
  biUnion_closedInterior := M.biUnion_closedInterior
  pairwise_disjoint_interior := M.pairwise_disjoint_interior
  inter_closedInterior T hT T' hT' := by
    rw [vertexSet_eq, vertexSet_eq]; exact M.inter_closedInterior T hT T' hT'

/-- A `Feec` mesh family is a mesh family of the challenge. -/
theorem isMeshFamily_ofFeec {D : StarDomain n} (F : MeshFamily D) :
    IsMeshFamily D.Ω fun N => SimplicialMesh.ofFeec (F.mesh N) := by
  refine ⟨F.domain_eq, ⟨F.C, F.c, F.q, F.C_nonneg, F.c_pos, F.q_pos, fun N => ⟨?_, ?_⟩⟩,
    fun N => (F.data N).meshSize_pos, F.tendsto_meshSize⟩
  · intro T hT
    obtain ⟨h1, h2, h3⟩ := (F.data N).shape T hT
    refine ⟨fun x => ?_, fun x => ?_, h3⟩
    · calc ‖edgeMap T x‖ = ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x‖ := rfl
        _ ≤ ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ F.C * diam T * ‖x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · calc ‖x‖ = ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (T.linearEquiv x)‖ := by
            rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
        _ ≤ ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ * ‖T.linearEquiv x‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ F.C / diam T * ‖edgeMap T x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  · exact (F.data N).quasi

theorem parallelepiped_eq (A : Matrix (Fin n) (Fin n) ℝ) (hA2 : IsUnit ((2 : ℝ) • A).det)
    (b : Fin n → ℝ) :
    parallelepiped A b = Feec.Models.Parallelepiped.domain ((2 : ℝ) • A) b := by
  rw [Feec.Models.Parallelepiped.domain_eq_image _ hA2]
  ext z
  simp only [parallelepiped, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
    Feec.Models.Cube.FEM.cubeDomain, Feec.Domain.affMap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(1 / 2 : ℝ) • x, fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      constructor <;> linarith [(hx i).1, (hx i).2]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
      norm_num
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(2 : ℝ) • y, fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      constructor <;> linarith [(hy i).1, (hy i).2]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul]

theorem fem_parallelepiped [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (b : Fin n → ℝ) :
    IsStarShapedBall (parallelepiped A b) ∧ (∃ M, IsMeshFamily (parallelepiped A b) M) ∧
      ∀ k, IsClosed (LinearMap.range (dMax (parallelepiped A b) k).toFun :
          Set (L2Form (parallelepiped A b) (k + 1))) ∧
        IsClosed (LinearMap.range (dMin (parallelepiped A b) k).toFun :
          Set (L2Form (parallelepiped A b) (k + 1))) := by
  have hA2 : IsUnit ((2 : ℝ) • A).det := by
    rw [Matrix.det_smul, isUnit_iff_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hA.ne_zero
  rw [parallelepiped_eq A hA2 b]
  set D := ParallelepipedWitness.starDomain ((2 : ℝ) • A) hA2 b
  refine ⟨⟨D.isOpen, D.isBounded, D.x₀, D.s₀, D.s₀_pos, D.starBall⟩,
    ⟨_, isMeshFamily_ofFeec (ParallelepipedWitness.meshFamily ((2 : ℝ) • A) hA2 b)⟩,
    fun k => ⟨?_, ?_⟩⟩
  · have h := Feec.Models.Parallelepiped.closedRangeAt ((2 : ℝ) • A) hA2 b (k + 1)
    rw [Feec.HilbertComplex.ClosedRangeAt, Feec.HilbertComplex.boundaries_eq _ rfl,
      deRham_maximalComplex_d, ← dMax_eq] at h
    exact h
  · have h := Feec.Models.Parallelepiped.closedRangeAt_min ((2 : ℝ) • A) hA2 b (k + 1)
    rw [Feec.HilbertComplex.ClosedRangeAt, Feec.HilbertComplex.boundaries_eq _ rfl,
      deRham_minimalComplex_d, ← dMin_eq] at h
    exact h

end FEEC
