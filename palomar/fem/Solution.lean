module

public import Solution.Complex
public import Solution.Forms
public import Solution.Spaces
public import Solution.Regularity
public import Feec.Models.Parallelepiped.StarShaped
public import Feec.Models.Cube.SobolevRestriction

/-!
# Uniformly bounded commuting projections for the finite element de Rham complexes (solution)

The compared theorems of `Challenge.lean`. `FEEC.fem` (`fem_dMax`, `fem_dMin` for the two
boundary conditions) from the finite element theory of `Feec.Models.StarShaped.PolyFiniteElement`
on the star domain and the mesh family of the challenge (`starDomainOf`, `meshFamilyOf`): the
complexes `MeshFamily.poly` and `MeshFamily.polyMin` of the admissible sequence (whose spaces are
the challenge's, `mem_V_iff`, `mem_V₀_iff`), the uniformly bounded smoothed projections
(`MeshFamily.exists_uniform_polyProj`, `_Min`; defined on all of `L²`, so their `L²` extensions
are themselves), the graph-norm density (`MeshFamily.eventually_exists_poly_graph`, `_Min`) and
the interpolation error (`MeshFamily.exists_mem_poly_le_of_isCsForm`, `_Min`); the complexes are
`Feec`'s `HΛ(Ω)` and `H̊Λ(Ω)` (`dMax_eq`, `dMin_eq`); the uniformly bounded projections attain
the Jackson rate (`HilbertComplex.SubcomplexFamily.Jackson.projRate`).

`FEEC.fem_parallelepiped` from `Feec.Models.StarShaped.ParallelepipedWitness` (the star domain and
the image Freudenthal meshes of `A (0, ½)ⁿ + b`, here with the matrix `2 A`), the compactness
property of `HΛ` and `H̊Λ` there (`Feec.Models.Parallelepiped.hasCompactProperty`, `_min`), which
gives the closed ranges and the finite-dimensional harmonic forms (`HilbertComplex.hodge_ofFeec`),
and their dimensions (`Feec.Models.Parallelepiped.finrank_harmonic`, `_min`).

`FEEC.fem_cube`: the family of `FEEC.fem` on the cube with the Freudenthal meshes (`CubeWitness`),
whose spaces are the cube's `Feec.Models.Cube.FEM.poly` (`poly_V_eq`); the best approximation of
`H^{s+1}` data (`exists_infDist_le_of_isSobolevForm`, from
`Feec.Models.Cube.FEM.infDist_poly_le_sobolevQ_high` and
`Feec.Models.Cube.SobolevRestriction.exists_qNorm_le`) passes to the graph norm through the
uniformly bounded projections.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4, §5.2, §5.5
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]

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

/-- `FEEC.fem` for `HΛ(Ω)`. -/
theorem fem_dMax [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMax Ω k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpace Ω (M N) S ∅ k) ∧
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i)) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      (∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsCsForm Ω s j L x) ∧ J.ProjRate := by
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
  have hP : ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ K ∧ (∀ x, P x ∈ (F.V N).V i) ∧
      ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i) := fun N i =>
    ⟨(π N).π i |>.mkContinuous K (hπ1 N i), LinearMap.mkContinuous_norm_le _ (by linarith) _,
      (π N).mem i, fun x => rfl⟩
  refine ⟨H, F, J, fun k => dMax_eq_complex hΩ k, rfl, fun N k => ?_, ⟨K, hP⟩,
    fun i => ⟨K, fun N x => ?_⟩, hA, fun N => rfl, fun s => rfl, fun s j L x => Iff.rfl,
    J.projRate hP⟩
  · ext u
    exact mem_V_iff S (M N) Ω (hM.1 N) u
  · refine H.graphNorm_le_of_sq (by linarith) ?_
    exact hπ2 N i (i + 1) x

/-- `FEEC.fem` for `H̊Λ(Ω)`. -/
theorem fem_dMin [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = dMin Ω k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) = femSpace Ω (M N) S (M N).boundaryFacets k) ∧
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i)) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      (∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsCsFormMin Ω s j L x) ∧ J.ProjRate := by
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
  have hP : ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ K ∧ (∀ x, P x ∈ (F.V N).V i) ∧
      ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i) := fun N i =>
    ⟨(π N).π i |>.mkContinuous K (hπ1 N i), LinearMap.mkContinuous_norm_le _ (by linarith) _,
      (π N).mem i, fun x => rfl⟩
  refine ⟨H, F, J, fun k => dMin_eq_complex hΩ k, rfl, fun N k => ?_, ⟨K, hP⟩,
    fun i => ⟨K, fun N x => ?_⟩, hA, fun N => rfl, fun s => rfl, fun s j L x => Iff.rfl,
    J.projRate hP⟩
  · ext u
    exact mem_V₀_iff S (M N) Ω (hM.1 N) u
  · refine H.graphNorm_le_of_sq (by linarith) ?_
    exact hπ2 N i (i + 1) x

theorem fem [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) (b : Bool) :
    ∃ (H : HilbertComplex ℝ (L2Form Ω)) (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ),
      (∀ k, H.d k (k + 1) = if b then dMin Ω k else dMax Ω k) ∧ F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form Ω k)) =
        femSpace Ω (M N) S (if b then (M N).boundaryFacets else ∅) k) ∧
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form Ω i →L[ℝ] L2Form Ω i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form Ω i)) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      (∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧
        (if b then IsCsFormMin Ω else IsCsForm Ω) s j L x) ∧ J.ProjRate := by
  cases b
  · exact fem_dMax hΩ hM S
  · exact fem_dMin hΩ hM S

/-! ### Parallelepipeds -/

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
      ∀ bc : Bool, ∃ H : HilbertComplex ℝ (L2Form (parallelepiped A b)),
        (∀ k, H.d k (k + 1) =
          if bc then dMin (parallelepiped A b) k else dMax (parallelepiped A b) k) ∧
        ∀ k, IsClosed (LinearMap.range (H.d k (k + 1)).toFun :
            Set (L2Form (parallelepiped A b) (k + 1))) ∧
          FiniteDimensional ℝ ↥((H.d k (k + 1)).ker ⊓ (H.d (k - 1) k)†.ker) ∧
          Module.finrank ℝ ↥((H.d k (k + 1)).ker ⊓ (H.d (k - 1) k)†.ker) =
            (if k = (if bc then (n : ℤ) else 0) then 1 else 0) ∧
          IsCompact (closure {x : L2Form (parallelepiped A b) k |
            ∃ (hx : x ∈ (H.d k (k + 1)).domain) (hx' : x ∈ (H.d (k - 1) k)†.domain),
              ‖x‖ ^ 2 + ‖H.d k (k + 1) ⟨x, hx⟩‖ ^ 2 + ‖(H.d (k - 1) k)† ⟨x, hx'⟩‖ ^ 2 ≤ 1}) := by
  have hA2 : IsUnit ((2 : ℝ) • A).det := by
    rw [Matrix.det_smul, isUnit_iff_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hA.ne_zero
  rw [parallelepiped_eq A hA2 b]
  set D := ParallelepipedWitness.starDomain ((2 : ℝ) • A) hA2 b
  refine ⟨⟨D.isOpen, D.isBounded, D.x₀, D.s₀, D.s₀_pos, D.starBall⟩,
    ⟨_, isMeshFamily_ofFeec (ParallelepipedWitness.meshFamily ((2 : ℝ) • A) hA2 b)⟩,
    fun bc => ?_⟩
  cases bc
  · refine ⟨HilbertComplex.ofFeec (Feec.Models.Parallelepiped.complex ((2 : ℝ) • A) b),
      fun k => ?_, HilbertComplex.hodge_ofFeec
        (Feec.Models.Parallelepiped.hasCompactProperty _ hA2 b)
        (Feec.Models.Parallelepiped.finrank_harmonic _ hA2 b)⟩
    rw [HilbertComplex.ofFeec_d, deRham_maximalComplex_d, dMax_eq]
    rfl
  · refine ⟨HilbertComplex.ofFeec (Feec.Models.Parallelepiped.complexMin ((2 : ℝ) • A) b),
      fun k => ?_, HilbertComplex.hodge_ofFeec
        (Feec.Models.Parallelepiped.hasCompactProperty_min _ hA2 b)
        (Feec.Models.Parallelepiped.finrank_harmonic_min _ hA2 b)⟩
    rw [HilbertComplex.ofFeec_d, deRham_minimalComplex_d, dMin_eq]
    rfl

/-! ### Sobolev rates on the cube -/

theorem poly_V_eq [NeZero n] (S : PolySeq) (N : ℕ) (k : ℤ) :
    (SetLike.coe ((Feec.Models.Cube.FEM.poly n S.toFeec N).V k) : Set (L2Form (cube n) k)) =
      femSpace (cube n) (SimplicialMesh.ofFeec (Feec.Models.Cube.FEM.mesh n N)) S ∅ k :=
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
        S ∅ j) ≤ c * (L * meshSize (SimplicialMesh.ofFeec (Feec.Models.Cube.FEM.mesh n N)) ^
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
    IsFreudenthal M ∧ ∀ S : PolySeq, ∃ (H : HilbertComplex ℝ (L2Form (cube n)))
      (F : H.SubcomplexFamily ℕ) (J : F.Jackson ℕ), (∀ k, H.d k (k + 1) = dMax (cube n) k) ∧
      F.l = atTop ∧
      (∀ N k, ((F.V N).V k : Set (L2Form (cube n) k)) = femSpace (cube n) (M N) S ∅ k) ∧
      (∃ C : ℝ, ∀ N i, ∃ P : L2Form (cube n) i →L[ℝ] L2Form (cube n) i, ‖P‖ ≤ C ∧
        (∀ x, P x ∈ (F.V N).V i) ∧
          ∀ x : (H.d i (i + 1)).domain, P x = ((F.π N).π i x : L2Form (cube n) i)) ∧
      (∀ i, F.IsGraphBounded i) ∧ (∀ i, F.Approximates i) ∧
      (∀ N, J.meshSize N = meshSize (M N)) ∧ (∀ s, J.ord s = s + 1) ∧
      (∀ s j L x, J.Reg s j L x ↔ S.PolyOrderAt n s j ∧ IsSobolevForm (cube n) (s + 1) j L x ∧
        ∀ hx : x ∈ (dMax (cube n) j).domain,
          IsSobolevForm (cube n) (s + 1) (j + 1) L (dMax (cube n) j ⟨x, hx⟩)) ∧ J.ProjRate := by
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
  obtain ⟨H, F, -, hd, hl, hV, hPex, hGB, hA, -⟩ := fem_dMax hΩ hM S
  obtain ⟨C, hP⟩ := hPex
  choose P hPC hPV hPπ using hP
  have hC : 0 ≤ C := (norm_nonneg _).trans (hPC 0 0)
  choose c hc0 hc using fun s j => exists_infDist_le_of_isSobolevForm (n := n) S s j
  -- the distance bound through the uniformly bounded projections
  have key : ∀ (N : ℕ) (i : ℤ) (x : L2Form (cube n) i),
      ‖x - P N i x‖ ≤ (1 + C) * Metric.infDist x ((F.V N).V i : Set (L2Form (cube n) i)) := by
    intro N i x
    have h1 : 0 < 1 + C := by linarith
    have hb : ‖x - P N i x‖ / (1 + C) ≤ Metric.infDist x ((F.V N).V i : Set (L2Form (cube n) i)) :=
      (Metric.le_infDist ⟨0, Submodule.zero_mem _⟩).2 fun w hw => by
        rw [div_le_iff₀ h1, dist_eq_norm, mul_comm]
        refine (P N i).norm_sub_apply_le_of_apply_eq (hPC N i) ?_ x
        rw [hPπ N i ⟨w, (F.V N).le_domain i (i + 1) hw⟩]
        exact (F.π N).proj i _ hw
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
  exact ⟨H, F, J, hd, hl, hV, ⟨C, fun N i => ⟨P N i, hPC N i, hPV N i, hPπ N i⟩⟩, hGB, hA,
    fun N => rfl, fun s => rfl, fun s j L x => Iff.rfl,
    J.projRate fun N i => ⟨P N i, hPC N i, hPV N i, hPπ N i⟩⟩

end FEEC
