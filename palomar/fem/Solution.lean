module

public import Solution.Complex
public import Solution.Dynamic
public import Solution.Forms
public import Solution.Spaces
public import Solution.Regularity
public import Solution.Maxwell
public import Feec.Models.Parallelepiped.StarShaped
public import Feec.Models.Cube.SobolevRestriction

/-!
# Finite element exterior calculus on polyhedral domains (solution)

The compared theorems of `Challenge.lean`. `FEEC.fem` and `FEEC.femMin` from the finite element
theory of `Feec.Models.StarShaped.PolyFiniteElement` on the star domain and the mesh family of the
challenge (`starDomainOf`, `meshFamilyOf`): the complexes `MeshFamily.poly` and
`MeshFamily.polyMin` of the admissible sequence (whose spaces are the challenge's,
`mem_V_iff`, `mem_V₀_iff`), the uniformly bounded smoothed projections
(`MeshFamily.exists_uniform_polyProj`, `_Min`; defined on all of `L²`, so their `L²` extensions
are themselves), the graph-norm density (`MeshFamily.eventually_exists_poly_graph`, `_Min`) and
the interpolation error (`MeshFamily.exists_mem_poly_le_of_isCsForm`, `_Min`); the complexes are
`Feec`'s `HΛ(Ω)` and `H̊Λ(Ω)` (`dMax_eq`, `dMin_eq`). The wave and heat verdicts on every window
from `Feec`'s crown through `Solution.Dynamic` (`HilbertComplex.SubcomplexFamily.waveVerdict`,
`heatVerdict`, as in `palomar/feec`), the window approximating by the graph-norm density
(`approximates_window`, `tendsto_infDist`). `FEEC.fem_parallelepiped` from
`Feec.Models.StarShaped.ParallelepipedWitness` (the star domain and the image Freudenthal meshes
of `A (0, ½)ⁿ + b`, here with the matrix `2 A`) and `Feec.Models.Parallelepiped.closedRangeAt`,
`closedRangeAt_min`. `FEEC.fem_cube`: the family of `FEEC.fem` on the cube with the Freudenthal
meshes (`CubeWitness`), whose spaces are the cube's `Feec.Models.Cube.FEM.poly` (`poly_V_eq`); the
best approximation of `H^{s+1}` data (`exists_infDist_le_of_isSobolevForm`, from
`Feec.Models.Cube.FEM.infDist_poly_le_sobolevQ_high` and
`Feec.Models.Cube.SobolevRestriction.exists_qNorm_le`) passes to the graph
norm through the uniformly bounded projections.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2, §5.5
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 4

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set MeasureTheory LinearPMap

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
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i)) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧ (∀ a m, F.DynamicVerdict a m) ∧
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
  have hA : ∀ i, F.Approximates i := fun i =>
    H.approximates_of_eventually F i fun x ε hε =>
      Fm.eventually_exists_poly_graph S.toFeec i x.1 x.2 hε
  refine ⟨H, F, J, fun k => dMax_eq_complex hΩ k, rfl, fun N k => ?_, ⟨K, fun N i =>
    ⟨(π N).π i |>.mkContinuous K (hπ1 N i), LinearMap.mkContinuous_norm_le _ (by linarith) _,
      (π N).mem i, fun x => rfl⟩⟩, fun i => ⟨K, fun N x => ?_⟩, hA, fun a m => ?_, fun N => rfl,
    fun s => rfl, fun s j L x => Iff.rfl⟩
  · ext u
    exact mem_V_iff S (M N) Ω (hM.1 N) u
  · refine H.graphNorm_le_of_sq (by linarith) ?_
    exact hπ2 N i (i + 1) x
  · have happ := F.approximates_window a m (fun i _ => hA _) fun i _ x =>
      H.tendsto_infDist F (hA _) x
    exact ⟨F.waveVerdict a m happ, fun hπ hπ' hcr => F.heatVerdict a m happ hπ hπ' hcr⟩

theorem femMin [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMin Ω k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpaceMin Ω (M N) S k) ∧
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i)) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧ (∀ a m, F.DynamicVerdict a m) ∧
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
  have hA : ∀ i, F.Approximates i := fun i =>
    H.approximates_of_eventually F i fun x ε hε =>
      Fm.eventually_exists_polyMin_graph S.toFeec i x.1 x.2 hε
  refine ⟨H, F, J, fun k => dMin_eq_complex hΩ k, rfl, fun N k => ?_, ⟨K, fun N i =>
    ⟨(π N).π i |>.mkContinuous K (hπ1 N i), LinearMap.mkContinuous_norm_le _ (by linarith) _,
      (π N).mem i, fun x => rfl⟩⟩, fun i => ⟨K, fun N x => ?_⟩, hA, fun a m => ?_, fun N => rfl,
    fun s => rfl, fun s j L x => Iff.rfl⟩
  · ext u
    exact mem_V₀_iff S (M N) Ω (hM.1 N) u
  · refine H.graphNorm_le_of_sq (by linarith) ?_
    exact hπ2 N i (i + 1) x
  · have happ := F.approximates_window a m (fun i _ => hA _) fun i _ x =>
      H.tendsto_infDist F (hA _) x
    exact ⟨F.waveVerdict a m happ, fun hπ hπ' hcr => F.heatVerdict a m happ hπ hπ' hcr⟩

/-! ### Parallelepipeds -/

/-- A `Feec` mesh as a mesh of the challenge. -/
def SimplicialMesh.ofFeec (M : Feec.Mesh.SimplicialMesh n) : SimplicialMesh n where
  simplices := M.simplices
  domain := M.domain
  biUnion_closedInterior := M.biUnion_closedInterior
  pairwise_disjoint_interior := M.pairwise_disjoint_interior
  inter_closedInterior T hT T' hT' := by
    rw [vertexSet_eq, vertexSet_eq]; exact M.inter_closedInterior T hT T' hT'

/-- A `Feec` mesh family is a mesh family of the challenge: its simplices contain balls of radius
`h_T / (2 n C)` (`Feec.Mesh.exists_ball_of_isShapeRegular`). -/
theorem isMeshFamily_ofFeec [NeZero n] {D : StarDomain n} (F : MeshFamily D) :
    IsMeshFamily D.Ω fun N => SimplicialMesh.ofFeec (F.mesh N) :=
  ⟨F.domain_eq, ⟨2 * n * F.C, F.q, F.q_pos, fun N =>
    ⟨Feec.Mesh.exists_ball_of_isShapeRegular (F.data N).shape, (F.data N).quasi⟩⟩,
    fun N => (F.data N).meshSize_pos, F.tendsto_meshSize⟩

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

/-! ### Sobolev rates on the cube -/

/-- The cube's finite element spaces (`Feec.Models.Cube.FEM.poly`, transported from the domain of
the mesh to the cube) are the challenge's. -/
theorem maximalSubcomplexOfEq_V [NeZero n] (S : PolySeq) (m : Feec.Mesh.SimplicialMesh n)
    {Ω : Set (Fin n → ℝ)} (h : m.domain = Ω) (hm : IsOpen m.domain) (hΩ : IsOpen Ω) (k : ℤ) :
    (SetLike.coe (((deRham ℝ n).maximalSubcomplexOfEq h hm hΩ (S.toFeec.subcomplex m hm)).V k) :
      Set (L2Form Ω k)) = femSpace Ω (SimplicialMesh.ofFeec m) S k := by
  obtain ⟨T, d, h1, h2, h3⟩ := m
  subst h
  ext u
  exact mem_V_iff S (SimplicialMesh.ofFeec ⟨T, d, h1, h2, h3⟩) _ rfl u

theorem poly_V_eq [NeZero n] (S : PolySeq) (N : ℕ) (k : ℤ) :
    (SetLike.coe ((Feec.Models.Cube.FEM.poly n S.toFeec N).V k) : Set (L2Form (cube n) k)) =
      femSpace (cube n) (SimplicialMesh.ofFeec (Feec.Models.Cube.FEM.mesh n N)) S k :=
  maximalSubcomplexOfEq_V S _ _ _ _ k

theorem meshSize_cube [NeZero n] (N : ℕ) :
    meshSize (SimplicialMesh.ofFeec (Feec.Models.Cube.FEM.mesh n N)) =
      Feec.Models.Cube.FEM.meshSize N :=
  (Feec.Models.Cube.FEM.meshSize_mesh N).trans (Feec.Models.Cube.FEM.hN_eq_meshSize N)

open Feec.Models.Cube Feec.Models.Cube.Sobolev Feec.Models.Cube.FEM in
/-- **Best approximation of `H^{s+1}` forms on the cube**, `dist(x, S_j(M_N)) ≤ c L h_N^{s+1}`
(`Feec.Models.Cube.FEM.infDist_poly_le_sobolevQ_high` with `SobolevRestriction.exists_qNorm_le`). -/
theorem exists_infDist_le_of_isSobolevForm [NeZero n] (S : PolySeq) (s : ℕ) (j : ℤ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (N : ℕ) {L : ℝ} (x : L2Form (cube n) j), 0 ≤ L →
      (∀ k : ℕ, (k : ℤ) = j → polySpace n s k ≤ S.toFeec.space n k) →
      IsSobolevForm (cube n) (s + 1) j L x →
      Metric.infDist x (femSpace (cube n) (SimplicialMesh.ofFeec (Feec.Models.Cube.FEM.mesh n N))
        S j) ≤ c * (L * meshSize (SimplicialMesh.ofFeec (Feec.Models.Cube.FEM.mesh n N)) ^
          ((s : ℝ) + 1)) := by
  rcases lt_or_ge j 0 with hj | hj
  · refine ⟨0, le_rfl, fun N L x _ _ _ => ?_⟩
    have := Feec.FiniteElement.LocalElement.subsingleton_L2F_of_neg (cube n) (n := n) hj
    rw [Subsingleton.elim x 0, Metric.infDist_zero_of_mem, zero_mul]
    rw [← poly_V_eq S N]
    exact SetLike.mem_coe.2 (Submodule.zero_mem _)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  obtain ⟨C, hC0, hC⟩ := SobolevRestriction.exists_qNorm_le (n := n) k s
  refine ⟨sobConstHigh n S.toFeec k s * C,
    mul_nonneg (sobConstHigh_nonneg S.toFeec k s) hC0, fun N L x hL hS hx => ?_⟩
  obtain ⟨D, hD, hsum, hxD⟩ := hx
  have hD' : ∀ t l, l.length ≤ s + 1 → MemLp (D t l) 2 volume ∧
      SobolevRestriction.IsWeakDeriv l (D t []) (D t l) ∧ ∫ y, D t l y ^ 2 ≤ L ^ 2 :=
        fun t l hl => by
    refine ⟨(hD t l hl).1, fun φ hφ => by
      rw [Sobolev.iterPartial_eq_foldr]; exact (hD t l hl).2 φ (isTestFn_of hφ), ?_⟩
    have hle : ∀ t' l', 0 ≤ ∫ y, D t' l' y ^ 2 := fun _ _ => integral_nonneg fun _ => sq_nonneg _
    refine le_trans ?_ hsum
    have h1 := Finset.single_le_sum (f := fun p : ℕ => (∑ r : Fin p → Fin n,
        ∫ y, D t (List.ofFn r) y ^ 2 : ℝ)) (fun _ _ => Finset.sum_nonneg fun _ _ => hle _ _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
    have h2 := Finset.single_le_sum (f := fun r : Fin l.length → Fin n =>
        (∫ y, D t (List.ofFn r) y ^ 2 : ℝ)) (fun _ _ => hle _ _) (Finset.mem_univ l.get)
    have h3 := Finset.single_le_sum (f := fun t' : FormIdx n k => (∑ p ∈ Finset.range (s + 1 + 1),
        ∑ r : Fin p → Fin n, ∫ y, D t' (List.ofFn r) y ^ 2 : ℝ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hle _ _)
      (Finset.mem_univ t)
    simp only [List.ofFn_get] at h2
    exact h2.trans (h1.trans h3)
  obtain ⟨hmem, hq⟩ := hC (toQ k x) D L hL hD' fun t =>
    (castL2F_apply_ae _ x t).trans (by rw [← cubeDomain_eq_Q]; exact hxD t)
  have h := infDist_poly_le_sobolevQ_high S.toFeec k s (hS k rfl) (by positivity) N x hmem
  rw [← poly_V_eq S N k, meshSize_cube]
  have e : min (((s + 1 : ℕ) : ℝ)) ((s : ℝ) + 1) = (s : ℝ) + 1 := by push_cast; exact min_self _
  rw [e] at h
  refine h.trans ?_
  have h1 := Real.rpow_nonneg (FEM.meshSize_pos N).le ((s : ℝ) + 1)
  have h2 := sobConstHigh_nonneg (n := n) S.toFeec k s
  calc sobConstHigh n S.toFeec k s * FEM.meshSize N ^ ((s : ℝ) + 1) *
        qNorm k (((s + 1 : ℕ) : ℝ)) (toQ k x)
      ≤ sobConstHigh n S.toFeec k s * FEM.meshSize N ^ ((s : ℝ) + 1) * (C * L) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg h2 h1)
    _ = _ := by ring

/-- `T x = T' x` along `T = T'`. -/
theorem LinearPMap.apply_of_eq {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T T' : E →ₗ.[ℝ] F} (h : T = T') (x : T.domain) :
    T x = T' ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

theorem fem_cube [NeZero n] : ∃ M : ℕ → SimplicialMesh n, IsMeshFamily (cube n) M ∧
    (∀ N, ∀ T ∈ (M N).simplices, ∃ (z : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n)), ∀ j i,
      T.points j i = ((z i : ℝ) + if (σ.symm i : ℕ) < (j : ℕ) then 1 else 0) / (2 * (N + 1))) ∧
    ∀ S : PolySeq, ∃ (H : HilbertComplex ℝ (L2Form (cube n))) (F : H.SubcomplexFamily ℕ)
      (J : F.Jackson ℕ), (∀ k, H.d k (k + 1) = dMax (cube n) k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form (cube n) k)) = femSpace (cube n) (M N) S k) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      ∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsSobolevForm (cube n) (s + 1) j L x ∧
        ∀ hx : x ∈ (dMax (cube n) j).domain,
          IsSobolevForm (cube n) (s + 1) (j + 1) L (dMax (cube n) j ⟨x, hx⟩) := by
  set D := CubeWitness.starDomain n
  have hΩ : IsStarShapedBall (cube n) := ⟨D.isOpen, D.isBounded, D.x₀, D.s₀, D.s₀_pos, D.starBall⟩
  have hM := isMeshFamily_ofFeec (CubeWitness.meshFamily n)
  refine ⟨_, hM, fun N T hT => ?_, fun S => ?_⟩
  · -- the Freudenthal simplices `h (z + K_σ)`, `h = (1 / 2) / (N + 1)`
    obtain ⟨z, σ, hzσ⟩ :=
      (Feec.Mesh.mem_freudenthalMesh_simplices (hs := by norm_num)).1 hT
    refine ⟨z, σ, fun j i => ?_⟩
    rw [← hzσ]
    simp only [Feec.Mesh.mapEquiv_points, Feec.Mesh.freudenthalSimplex_points,
      Feec.Mesh.boxMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add,
      Feec.Mesh.latticePoint_apply, Feec.Mesh.finLattice, Feec.Mesh.kuhnVertex]
    push_cast
    field_simp
  obtain ⟨H, F, -, hd, hl, hV, ⟨C, hP⟩, -⟩ := fem hΩ hM S
  choose P hPC hPV hPπ using hP
  have hC : 0 ≤ C := (norm_nonneg _).trans (hPC 0 0)
  choose c hc0 hc using fun s j => exists_infDist_le_of_isSobolevForm (n := n) S s j
  -- the distance bound through the uniformly bounded projections
  have key : ∀ (N : ℕ) (i : ℤ) (x : L2Form (cube n) i),
      ‖x - P N i x‖ ≤ (1 + C) * Metric.infDist x ((F.V N).V i : Set (L2Form (cube n) i)) := by
    intro N i x
    have hne : ((F.V N).V i : Set (L2Form (cube n) i)).Nonempty := ⟨0, Submodule.zero_mem _⟩
    have h1 : 0 < 1 + C := by linarith
    have hb : ‖x - P N i x‖ / (1 + C) ≤ Metric.infDist x ((F.V N).V i : Set (L2Form (cube n) i)) :=
      (Metric.le_infDist hne).2 fun w hw => by
        rw [div_le_iff₀ h1, dist_eq_norm]
        have hPw : P N i w = w := by
          have := hPπ N i ⟨w, (F.V N).le_domain i (i + 1) hw⟩
          simp only at this
          rw [this]
          exact (F.π N).proj i _ hw
        have e : x - P N i x = (x - w) - P N i (x - w) := by rw [_root_.map_sub, hPw]; abel
        rw [e]
        calc ‖(x - w) - P N i (x - w)‖ ≤ ‖x - w‖ + ‖P N i (x - w)‖ := norm_sub_le _ _
          _ ≤ ‖x - w‖ + C * ‖x - w‖ := by gcongr; exact (P N i).le_of_opNorm_le (hPC N i) _
          _ = ‖x - w‖ * (1 + C) := by ring
    calc ‖x - P N i x‖ = (1 + C) * (‖x - P N i x‖ / (1 + C)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hb h1.le
  let J : F.Jackson ℕ :=
    { meshSize := fun N => meshSize (SimplicialMesh.ofFeec (Feec.Models.Cube.FEM.mesh n N))
      meshSize_nonneg := fun N => (hM.2.2.1 N).le
      tendsto_meshSize := by rw [hl]; exact hM.2.2.2
      Reg := fun s j L x => S.PolyOrderAt n s j ∧ IsSobolevForm (cube n) (s + 1) j L x ∧
        ∀ hx : x ∈ (dMax (cube n) j).domain,
          IsSobolevForm (cube n) (s + 1) (j + 1) L (dMax (cube n) j ⟨x, hx⟩)
      ord := fun s => s + 1
      B := fun s i => (1 + C) * (c s i + c s (i + 1))
      jackson := fun s N i L x hL hx => by
        have hh := Real.rpow_nonneg (hM.2.2.1 N).le ((s : ℝ) + 1)
        have hc1 := hc0 s i
        have hc2 := hc0 s (i + 1)
        have h1 : 0 ≤ 1 + C := by linarith
        rcases lt_or_ge i 0 with hi | hi
        · have := Feec.FiniteElement.LocalElement.subsingleton_L2F_of_neg (cube n) (n := n) hi
          have hx0 : x - P N i x = 0 := Subsingleton.elim _ _
          have hB : 0 ≤ (1 + C) * (c s i + c s (i + 1)) * (L * meshSize
              (SimplicialMesh.ofFeec (Feec.Models.Cube.FEM.mesh n N)) ^ ((s : ℝ) + 1)) :=
            mul_nonneg (mul_nonneg h1 (add_nonneg hc1 hc2)) (mul_nonneg hL hh)
          refine ⟨P N i x, hPV N i x, by rw [hx0, norm_zero]; exact hB, fun j hxj => ?_⟩
          have e : (⟨x - P N i x, Submodule.sub_mem _ hxj ((F.V N).le_domain i j (hPV N i x))⟩ :
              (H.d i j).domain) = 0 := Subtype.ext hx0
          rw [e, LinearPMap.map_zero, norm_zero]
          exact hB
        obtain ⟨k₀, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        have hS := (S.polyOrderAt_iff s k₀).1 hx.1
        refine ⟨P N k₀ x, hPV N k₀ x, ?_, fun j hxj => ?_⟩
        · refine (key N k₀ x).trans ?_
          rw [hV N k₀]
          have := hc s k₀ N x hL (fun k hk => (hS k hk).1) hx.2.1
          refine ((mul_le_mul_of_nonneg_left this h1).trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hc2) (mul_nonneg hL hh))
              h1)).trans_eq ?_
          ring
        · by_cases hij : (k₀ : ℤ) + 1 = j
          · subst hij
            have hx' : x ∈ (dMax (cube n) k₀).domain := hd k₀ ▸ hxj
            set y : (H.d k₀ (k₀ + 1)).domain := ⟨x, hxj⟩
            have e0 : (⟨x - P N k₀ x, Submodule.sub_mem _ hxj
                ((F.V N).le_domain k₀ (k₀ + 1) (hPV N k₀ x))⟩ : (H.d k₀ (k₀ + 1)).domain) =
                y - ⟨_, (F.V N).le_domain k₀ (k₀ + 1) ((F.π N).π k₀ y).2⟩ :=
              Subtype.ext (by simp [y, hPπ N k₀ y])
            rw [e0, LinearPMap.map_sub, (F.π N).comm k₀ y]
            have e1 : (((F.π N).π (k₀ + 1) ⟨H.d k₀ (k₀ + 1) y,
                H.mapsTo k₀ (k₀ + 1) (k₀ + 1 + 1) y⟩ : (F.V N).V (k₀ + 1)) : L2Form (cube n) _) =
                P N (k₀ + 1) (H.d k₀ (k₀ + 1) y) :=
              (hPπ N (k₀ + 1) ⟨_, H.mapsTo k₀ (k₀ + 1) (k₀ + 1 + 1) y⟩).symm
            rw [e1]
            refine (key N (k₀ + 1) _).trans ?_
            rw [hV N (k₀ + 1)]
            have hdy : H.d k₀ (k₀ + 1) y = dMax (cube n) k₀ ⟨x, hx'⟩ :=
              LinearPMap.apply_of_eq (hd k₀) y
            have hsd : IsSobolevForm (cube n) (s + 1) ((k₀ : ℤ) + 1) L (H.d k₀ (k₀ + 1) y) := by
              rw [hdy]; exact hx.2.2 hx'
            have := hc s (k₀ + 1) N (H.d k₀ (k₀ + 1) y) hL (fun k hk => by
              obtain rfl : k = k₀ + 1 := by omega
              exact (hS k₀ rfl).2) hsd
            refine ((mul_le_mul_of_nonneg_left this h1).trans (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc1) (mul_nonneg hL hh))
                h1)).trans_eq ?_
            ring
          · rw [LinearPMap.apply_of_eq (H.shape _ _ hij), LinearPMap.zero_apply, norm_zero]
            exact mul_nonneg (mul_nonneg h1 (add_nonneg hc1 hc2)) (mul_nonneg hL hh) }
  exact ⟨H, F, J, hd, hl, hV, fun N => rfl, fun s => rfl, fun s j L x => Iff.rfl⟩

/-! ### Maxwell's equations -/

theorem maxwell {Ω : Set (Fin 3 → ℝ)} (hΩ : IsStarShapedBall Ω) {M : ℕ → SimplicialMesh 3}
    (hM : IsMeshFamily Ω M) (S : PolySeq) :
    (∀ N, proxy0 '' femSpace Ω (M N) S 0 ⊆ (grad Ω).domain ∧
      proxy1 '' femSpace Ω (M N) S 1 ⊆ (curl Ω).domain ∧
      proxy2 '' femSpace Ω (M N) S 2 ⊆ (div Ω).domain) ∧
    (∀ N T σh₀ Eh₀ Bh₀, σh₀ ∈ proxy0 '' femSpace Ω (M N) S 0 →
      Eh₀ ∈ proxy1 '' femSpace Ω (M N) S 1 → Bh₀ ∈ proxy2 '' femSpace Ω (M N) S 2 →
      ∃ σh Eh Bh, σh 0 = σh₀ ∧ Eh 0 = Eh₀ ∧ Bh 0 = Bh₀ ∧
        IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S 0) (proxy1 '' femSpace Ω (M N) S 1)
          (proxy2 '' femSpace Ω (M N) S 2) T σh Eh Bh ∧
        ∀ σ₁ E₁ B₁, σ₁ 0 = σh₀ → E₁ 0 = Eh₀ → B₁ 0 = Bh₀ →
          IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S 0) (proxy1 '' femSpace Ω (M N) S 1)
            (proxy2 '' femSpace Ω (M N) S 2) T σ₁ E₁ B₁ →
          ∀ t ∈ Icc 0 T, σ₁ t = σh t ∧ E₁ t = Eh t ∧ B₁ t = Bh t) ∧
    ∀ σ₀ E₀ B₀, σ₀ ∈ (grad Ω).domain → E₀ ∈ (curl Ω).domain → E₀ ∈ (grad Ω)†.domain →
      B₀ ∈ (curl Ω)†.domain → ∀ T, ∃ σ E B, σ 0 = σ₀ ∧ E 0 = E₀ ∧ B 0 = B₀ ∧
        IsMaxwellSolution Ω T σ E B ∧
        (∀ σ₁ E₁ B₁, σ₁ 0 = σ₀ → E₁ 0 = E₀ → B₁ 0 = B₀ → IsMaxwellSolution Ω T σ₁ E₁ B₁ →
          ∀ t ∈ Icc 0 T, σ₁ t = σ t ∧ E₁ t = E t ∧ B₁ t = B t) ∧
        (∀ t ∈ Icc 0 T, ‖σ t‖ ^ 2 + ‖E t‖ ^ 2 + ‖B t‖ ^ 2 = ‖σ₀‖ ^ 2 + ‖E₀‖ ^ 2 + ‖B₀‖ ^ 2) ∧
        (σ₀ = 0 → (E₀, 0) ∈ (grad Ω)†.graph → (B₀, 0) ∈ (div Ω).graph → ∀ t ∈ Icc 0 T,
          σ t = 0 ∧ (E t, 0) ∈ (grad Ω)†.graph ∧ (B t, 0) ∈ (div Ω).graph) ∧
        (∀ (σh : ℕ → ℝ → L2Field Ω (Fin 1)) (Eh Bh : ℕ → ℝ → L2Field Ω (Fin 3)),
          (∀ N, IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S 0)
            (proxy1 '' femSpace Ω (M N) S 1) (proxy2 '' femSpace Ω (M N) S 2) T
            (σh N) (Eh N) (Bh N)) →
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) → Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) →
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) →
          TendstoUniformlyOn σh σ atTop (Icc 0 T) ∧ TendstoUniformlyOn Eh E atTop (Icc 0 T) ∧
            TendstoUniformlyOn Bh B atTop (Icc 0 T)) ∧
        ∃ (σh : ℕ → ℝ → L2Field Ω (Fin 1)) (Eh Bh : ℕ → ℝ → L2Field Ω (Fin 3)),
          (∀ N, IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S 0)
            (proxy1 '' femSpace Ω (M N) S 1) (proxy2 '' femSpace Ω (M N) S 2) T
            (σh N) (Eh N) (Bh N)) ∧
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) ∧ Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) ∧
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) := by
  have hO : IsOpen Ω := hΩ.1
  let F : Feec.HilbertComplex.ConformingFamily ((deRham ℝ 3).maximalComplex hO) ℕ :=
    (meshFamilyOf hΩ hM).polyFamily S.toFeec
  let G := vFamily hO F
  have V := Feec.Instances.Maxwell.maxwellFEEC G 0
  have hA₀ : ∀ N u, u ∈ proxy0 '' femSpace Ω (M N) S 0 ↔ u ∈ (G.V N).V 0 := fun N =>
    mem_proxy0_iff hO F N fun w => (mem_V_iff S (M N) Ω (hM.1 N) w).symm
  have hA₁ : ∀ N u, u ∈ proxy1 '' femSpace Ω (M N) S 1 ↔ u ∈ (G.V N).V 1 := fun N =>
    mem_proxy1_iff hO F N fun w => (mem_V_iff S (M N) Ω (hM.1 N) w).symm
  have hA₂ : ∀ N u, u ∈ proxy2 '' femSpace Ω (M N) S 2 ↔ u ∈ (G.V N).V 2 := fun N =>
    mem_proxy2_iff hO F N fun w => (mem_V_iff S (M N) Ω (hM.1 N) w).symm
  refine ⟨fun N => ⟨fun u hu => (mem_grad_domain hO).2 ((G.V N).le_domain 0 1 ((hA₀ N u).1 hu)),
    fun u hu => (mem_curl_domain hO).2 ((G.V N).le_domain 1 2 ((hA₁ N u).1 hu)),
    fun u hu => (mem_div_domain hO).2 ((G.V N).le_domain 2 3 ((hA₂ N u).1 hu))⟩,
    fun N T _ _ _ hσ hE hB => galerkin_wellPosed hO G (hA₀ N) (hA₁ N) (hA₂ N) T hσ hE hB,
    fun σ₀ E₀ B₀ hσ₀ hE₀ hE₀' hB₀ T => ?_⟩
  set x : MX Ω := pack σ₀ E₀ B₀
  have hx : x ∈ (Win hO).wave.domain :=
    Feec.HilbertComplex.mem_wave_domain_fin3 (Win hO) ((mem_grad_domain hO).1 hσ₀)
      ((mem_curl_domain hO).1 hE₀) ((mem_grad_adj_domain hO).1 hE₀')
      ((mem_curl_adj_domain hO).1 hB₀)
  obtain ⟨hcl, huniq, -, hnorm⟩ := V.wellPosed hx T
  set Sg := (Win hO).waveGroup.S
  have h0 : Sg 0 x = x := by
    rw [show Sg 0 = 1 from (Win hO).waveGroup.map_zero]; rfl
  refine ⟨fun t => (Sg t x : MX Ω) 0, fun t => (Sg t x : MX Ω) 1, fun t => (Sg t x : MX Ω) 2,
    congrArg (fun z : MX Ω => z 0) h0, congrArg (fun z : MX Ω => z 1) h0,
    congrArg (fun z : MX Ω => z 2) h0, isMaxwellSolution_of hO hcl.toIsStrongSolution, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro σ₁ E₁ B₁ h0σ h0E h0B hsol t ht
    have hU := isStrongSolution_of hO hsol
    have hU0 : pack (σ₁ 0) (E₁ 0) (B₁ 0) = x := by rw [h0σ, h0E, h0B]
    have e := huniq _ hU0 hU ht
    exact ⟨congrArg (fun z : MX Ω => z 0) e, congrArg (fun z : MX Ω => z 1) e,
      congrArg (fun z : MX Ω => z 2) e⟩
  · intro t _
    calc _ = ‖(Sg t x : MX Ω)‖ ^ 2 := (norm_sq_MX _).symm
      _ = ‖x‖ ^ 2 := by rw [show ‖(Sg t x : MX Ω)‖ = ‖x‖ from hnorm t]
      _ = _ := norm_sq_MX x
  · intro hσ0 hEg hBg t ht
    have hK : Sg 0 x ∈ (Feec.Instances.Maxwell.feec G 0).K := by
      rw [h0]; exact (mem_windowGauss_iff hO x).2 ⟨hσ0, hEg, hBg⟩
    exact (mem_windowGauss_iff hO _).1 (V.gauss_propagates_strong hK hcl.toIsStrongSolution t ht)
  · intro σh Eh Bh hgal h0σ h0E h0B
    rcases lt_or_ge T 0 with hT | hT
    · rw [Set.Icc_eq_empty (not_le.2 hT)]
      exact ⟨tendstoUniformlyOn_empty, tendstoUniformlyOn_empty, tendstoUniformlyOn_empty⟩
    choose ξ ξ' hsemi hfst using fun N =>
      semidiscrete_of_galerkin hO G (hA₀ N) (hA₁ N) (hA₂ N) (hgal N)
    have hξ0 : Tendsto (fun N => (Win hO).totalD.graphFst (ξ N 0)) atTop (𝓝 x) :=
      (tendsto_pack h0σ h0E h0B).congr fun N => (hfst N 0 ⟨le_rfl, hT⟩).symm
    have hc : TendstoUniformlyOn (fun N t => pack (σh N t) (Eh N t) (Bh N t)) (fun t => Sg t x)
        atTop (Icc 0 T) :=
      (V.converges_of_tendsto x ξ ξ' hsemi hξ0).congr
        (Eventually.of_forall fun N t ht => hfst N t ht)
    exact ⟨tendstoUniformlyOn_apply_MX hc 0, tendstoUniformlyOn_apply_MX hc 1,
      tendstoUniformlyOn_apply_MX hc 2⟩
  · obtain ⟨ξ, ξ', hsemi, hξ0⟩ := V.exists_tendsto x T
    exact ⟨fun N t => (Win hO).totalD.graphFst (ξ N t) 0,
      fun N t => (Win hO).totalD.graphFst (ξ N t) 1,
      fun N t => (Win hO).totalD.graphFst (ξ N t) 2,
      fun N => galerkin_of_semidiscrete hO G (hA₀ N) (hA₁ N) (hA₂ N) (hsemi N),
      tendsto_apply_MX hξ0 0, tendsto_apply_MX hξ0 1, tendsto_apply_MX hξ0 2⟩

end FEEC
