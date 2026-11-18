module

public import Solution.Complex
public import Solution.Forms
public import Solution.Spaces
public import Solution.Regularity
public import Solution.Maxwell
public import Solution.Affine
public import Solution.Dof
public import Solution.Whitney
public import Feec.Models.Parallelepiped.StarShaped
public import Feec.Models.Cube.SobolevRestriction

/-!
# Finite element de Rham complexes: uniform stability and the fully discrete wave equation (solution)

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

`FEEC.inverse_estimate` is `Feec.FiniteElement.PolySeq.exists_mul_norm_d_le` on the `Feec`
meshes. `FEEC.fem_wave` is a consequence of `FEEC.fem` and `FEEC.inverse_estimate`: the complex
of `FEEC.fem` is the given one (`HilbertComplex.ext_of_d`), the comparison fields are the `L²`
projections of the exact solution, componentwise (`‖P U - U‖` by the quasi-optimality of a
bounded projection and the Jackson estimate, `‖𝐝 (P U - U)‖` by `Jackson.ProjRate`, both at
`h^{s+1}`, through `HilbertComplex.norm_totalD_le`), and `HilbertComplex.wave_error`
(`Solution.Wave`) gives the Crank–Nicolson and leapfrog errors, the CFL condition from the
inverse estimate on the window.

`FEEC.fem_parallelepiped` from `Feec.Models.StarShaped.ParallelepipedWitness` (the star domain and
the image Freudenthal meshes of `A (0, ½)ⁿ + b`, here with the matrix `2 A`) and
`Feec.Models.Parallelepiped.closedRangeAt`, `closedRangeAt_min`. `FEEC.fem_cube`: the family of
`FEEC.fem` on the cube with the Freudenthal meshes (`CubeWitness`), whose spaces are the cube's
`Feec.Models.Cube.FEM.poly` (`poly_V_eq`); the best approximation of `H^{s+1}` data
(`exists_infDist_le_of_isSobolevForm`, from `Feec.Models.Cube.FEM.infDist_poly_le_sobolevQ_high`
and `Feec.Models.Cube.SobolevRestriction.exists_qNorm_le`) passes to the graph norm through the
uniformly bounded projections. `FEEC.crankNicolson_cube` and `FEEC.leapfrog_cube` are
`Feec.Models.Cube.Inhomogeneous.RowSolution.whitney_cn_error_le_row` and
`RowSolution.whitney_leapfrog_error_le_row` (the latter for every constant of the inverse
estimate), with the well-posedness of the steps, the unisolvence of the face integrals and
`V̊ₕ¹ ≠ 0`, through `Solution.Whitney`; `FEEC.rowSolution_nonvacuous` is row `0` of `Feec`'s
plane wave. `FEEC.maxwell` through `Solution.Maxwell`. `FEEC.unisolvent` from
`Feec.FiniteElement.LocalDof` through `Solution.Dof`; `FEEC.affineInvariantForms` and the
characteristic-`0` theorems from `Feec.FiniteElement.AffineInvariantForm` and
`Feec.Counterexamples.PositiveCharacteristic` through `Solution.Affine`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.4, §4
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2, §5.5
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 4, 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set MeasureTheory LinearPMap

@[expose] public noncomputable section

universe u

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

/-! ### Maxwell's equations -/

/-- `FEEC.maxwell` with the spaces written out. -/
theorem maxwell_proxy {Ω : Set (Fin 3 → ℝ)} (hΩ : IsStarShapedBall Ω) {M : ℕ → SimplicialMesh 3}
    (hM : IsMeshFamily Ω M) (S : PolySeq) :
    (∀ N, proxy0 '' femSpace Ω (M N) S ∅ 0 ⊆ (grad Ω).domain ∧
      proxy1 '' femSpace Ω (M N) S ∅ 1 ⊆ (curl Ω).domain ∧
      proxy2 '' femSpace Ω (M N) S ∅ 2 ⊆ (div Ω).domain) ∧
    (∀ N T σh₀ Eh₀ Bh₀, σh₀ ∈ proxy0 '' femSpace Ω (M N) S ∅ 0 →
      Eh₀ ∈ proxy1 '' femSpace Ω (M N) S ∅ 1 → Bh₀ ∈ proxy2 '' femSpace Ω (M N) S ∅ 2 →
      ∃ σh Eh Bh, σh 0 = σh₀ ∧ Eh 0 = Eh₀ ∧ Bh 0 = Bh₀ ∧
        IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S ∅ 0) (proxy1 '' femSpace Ω (M N) S ∅ 1)
          (proxy2 '' femSpace Ω (M N) S ∅ 2) T σh Eh Bh ∧
        ∀ σ₁ E₁ B₁, σ₁ 0 = σh₀ → E₁ 0 = Eh₀ → B₁ 0 = Bh₀ →
          IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S ∅ 0) (proxy1 '' femSpace Ω (M N) S ∅ 1)
            (proxy2 '' femSpace Ω (M N) S ∅ 2) T σ₁ E₁ B₁ →
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
          (∀ N, IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S ∅ 0)
            (proxy1 '' femSpace Ω (M N) S ∅ 1) (proxy2 '' femSpace Ω (M N) S ∅ 2) T
            (σh N) (Eh N) (Bh N)) →
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) → Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) →
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) →
          TendstoUniformlyOn σh σ atTop (Icc 0 T) ∧ TendstoUniformlyOn Eh E atTop (Icc 0 T) ∧
            TendstoUniformlyOn Bh B atTop (Icc 0 T)) ∧
        ∃ (σh : ℕ → ℝ → L2Field Ω (Fin 1)) (Eh Bh : ℕ → ℝ → L2Field Ω (Fin 3)),
          (∀ N, IsMaxwellGalerkin Ω (proxy0 '' femSpace Ω (M N) S ∅ 0)
            (proxy1 '' femSpace Ω (M N) S ∅ 1) (proxy2 '' femSpace Ω (M N) S ∅ 2) T
            (σh N) (Eh N) (Bh N)) ∧
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) ∧ Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) ∧
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) := by
  have hO : IsOpen Ω := hΩ.1
  let F : Feec.HilbertComplex.ConformingFamily ((deRham ℝ 3).maximalComplex hO) ℕ :=
    (meshFamilyOf hΩ hM).polyFamily S.toFeec
  let G := vFamily hO F
  have V := Feec.Instances.Maxwell.maxwellFEEC G 0
  have hA₀ : ∀ N u, u ∈ proxy0 '' femSpace Ω (M N) S ∅ 0 ↔ u ∈ (G.V N).V 0 := fun N =>
    mem_proxy0_iff hO F N fun w => (mem_V_iff S (M N) Ω (hM.1 N) w).symm
  have hA₁ : ∀ N u, u ∈ proxy1 '' femSpace Ω (M N) S ∅ 1 ↔ u ∈ (G.V N).V 1 := fun N =>
    mem_proxy1_iff hO F N fun w => (mem_V_iff S (M N) Ω (hM.1 N) w).symm
  have hA₂ : ∀ N u, u ∈ proxy2 '' femSpace Ω (M N) S ∅ 2 ↔ u ∈ (G.V N).V 2 := fun N =>
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

theorem maxwell {Ω : Set (Fin 3 → ℝ)} (hΩ : IsStarShapedBall Ω) {M : ℕ → SimplicialMesh 3}
    (hM : IsMeshFamily Ω M) (S : PolySeq) :
    let V₀ := fun N => proxy0 '' femSpace Ω (M N) S ∅ 0
    let V₁ := fun N => proxy1 '' femSpace Ω (M N) S ∅ 1
    let V₂ := fun N => proxy2 '' femSpace Ω (M N) S ∅ 2
    (∀ N, V₀ N ⊆ (grad Ω).domain ∧ V₁ N ⊆ (curl Ω).domain ∧ V₂ N ⊆ (div Ω).domain) ∧
    (∀ N T σh₀ Eh₀ Bh₀, σh₀ ∈ V₀ N → Eh₀ ∈ V₁ N → Bh₀ ∈ V₂ N →
      ∃ σh Eh Bh, σh 0 = σh₀ ∧ Eh 0 = Eh₀ ∧ Bh 0 = Bh₀ ∧
        IsMaxwellGalerkin Ω (V₀ N) (V₁ N) (V₂ N) T σh Eh Bh ∧
        ∀ σ₁ E₁ B₁, σ₁ 0 = σh₀ → E₁ 0 = Eh₀ → B₁ 0 = Bh₀ →
          IsMaxwellGalerkin Ω (V₀ N) (V₁ N) (V₂ N) T σ₁ E₁ B₁ →
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
          (∀ N, IsMaxwellGalerkin Ω (V₀ N) (V₁ N) (V₂ N) T (σh N) (Eh N) (Bh N)) →
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) → Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) →
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) →
          TendstoUniformlyOn σh σ atTop (Icc 0 T) ∧ TendstoUniformlyOn Eh E atTop (Icc 0 T) ∧
            TendstoUniformlyOn Bh B atTop (Icc 0 T)) ∧
        ∃ (σh : ℕ → ℝ → L2Field Ω (Fin 1)) (Eh Bh : ℕ → ℝ → L2Field Ω (Fin 3)),
          (∀ N, IsMaxwellGalerkin Ω (V₀ N) (V₁ N) (V₂ N) T (σh N) (Eh N) (Bh N)) ∧
          Tendsto (fun N => σh N 0) atTop (𝓝 σ₀) ∧ Tendsto (fun N => Eh N 0) atTop (𝓝 E₀) ∧
          Tendsto (fun N => Bh N 0) atTop (𝓝 B₀) :=
  maxwell_proxy hΩ hM S

/-! ### The fully discrete Hodge wave equation -/

theorem inverse_estimate [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M)
    (hint : ∀ N, ∀ T ∈ (M N).simplices, interior T.closedInterior ⊆ Ω) (S : PolySeq) (k : ℕ) :
    ∃ C, ∀ N, ∀ v ∈ femSpace Ω (M N) S ∅ k, ∃ hv : v ∈ (dMax Ω k).domain,
      meshSize (M N) * ‖dMax Ω k ⟨v, hv⟩‖ ≤ C * ‖v‖ := by
  obtain ⟨hdom, ⟨σ, q, hq, hsq⟩, hpos, -⟩ := hM
  obtain ⟨T₀, hT₀⟩ := exists_mem_simplices (hpos 0)
  have hσ := pos_of_isShapeRegular (hsq 0).1 hT₀
  obtain ⟨K, -, hK⟩ := S.toFeec.exists_mul_norm_d_le (n := n) k (C := max n σ)
    (c := 1 / ((n.factorial : ℝ) * σ ^ n)) (le_max_of_le_right hσ.le) (by positivity)
  refine ⟨K / q, fun N v hv => ?_⟩
  set m := (M N).toFeec Ω (hdom N)
  have hv' : v ∈ (S.toFeec.subcomplex m hΩ).V k := (mem_V_iff S (M N) Ω (hdom N) v).2 hv
  have hd : v ∈ ((extDerivOp ℝ n k).maximal m.domain).domain :=
    (polyElement n S.toFeec).V_le_maximal_domain m hΩ k hv'
  have hdM : dMax Ω k = (extDerivOp ℝ n k).maximal Ω := dMax_eq Ω k
  refine ⟨hdM ▸ hd, ?_⟩
  have hb := hK m hΩ (hint N) (isShapeRegular_toFeec (hdom N) (hsq N).1)
    (h := q * meshSize (M N)) (mul_pos hq (hpos N)) (fun T hT => (hsq N).2 T hT) ⟨v, hd⟩ hv'
  have e : dMax Ω k ⟨v, hdM ▸ hd⟩ = (extDerivOp ℝ n k).maximal m.domain ⟨v, hd⟩ :=
    LinearPMap.apply_of_eq hdM _
  have hb' : q * meshSize (M N) * ‖(extDerivOp ℝ n k).maximal m.domain ⟨v, hd⟩‖ ≤ K * ‖v‖ := hb
  rw [e, div_mul_eq_mul_div, le_div_iff₀ hq, mul_comm _ q, ← mul_assoc]
  exact hb'

theorem fem_wave [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (S : PolySeq) (b : Bool)
    (H : HilbertComplex ℝ (L2Form Ω)) (hH : ∀ k, H.d k (k + 1) = if b then dMin Ω k else dMax Ω k)
    (a : ℤ) (m : ℕ) :
    let X : ℕ → Set (Total (L2Form Ω) a m) := fun N =>
      femTotal Ω (M N) S (if b then (M N).boundaryFacets else ∅) a m
    let Reg := if b then IsCsFormMin Ω else IsCsForm Ω
    let IsInv C₀ := ∀ N, ∀ x ∈ X N, meshSize (M N) * ‖H.dApply a m x‖ ≤ C₀ * ‖x‖
    (∃ C₀, IsInv C₀) ∧
    ∀ s : ℕ, (∀ i : Fin m, S.PolyOrderAt n s (a + (i : ℕ))) → ∃ C : ℝ,
      ∀ (T L : ℝ) (U U₁ U₂ U₃ : ℝ → Total (L2Form Ω) a m),
      (∀ t, HasDerivAt U (U₁ t) t ∧ HasDerivAt U₁ (U₂ t) t ∧ HasDerivAt U₂ (U₃ t) t) →
      (∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L ∧ (U t, U₁ t) ∈ (H.wave a m).graph) →
      (∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ∀ i : Fin m, Reg s (a + (i : ℕ)) L (U t i) ∧
        Reg s (a + (i : ℕ)) (L * |t' - t|) (U t' i - U t i)) →
      ∀ N (Δt : ℝ) (K : ℕ) (u : ℕ → Total (L2Form Ω) a m), 0 < Δt → K * Δt ≤ T →
        ((∀ k < K, H.IsCNStep a m (X N) (X N) Δt 0 (u k) (u (k + 1))) → u 0 ∈ X N →
          ‖u K - U (K * Δt)‖ ≤
            ‖u 0 - U 0‖ + C * (1 + T) * L * (meshSize (M N) ^ (s + 1) + Δt ^ 2)) ∧
        ∀ C₀ c : ℝ, 0 ≤ C₀ → IsInv C₀ → c < 1 → 2 * C₀ * Δt ≤ c * meshSize (M N) →
          (∀ k, k + 2 ≤ K → H.IsLeapfrogStep a m (X N) (X N) Δt 0 (u k) (u (k + 1)) (u (k + 2))) →
          u 0 ∈ X N → u 1 ∈ X N → (1 - c) * ‖u K - U (K * Δt)‖ ≤
            ‖u 0 - U 0‖ + ‖u 1 - U Δt‖ + C * (1 + T) * L * (meshSize (M N) ^ (s + 1) + Δt ^ 2) := by
  intro X Reg IsInv
  obtain ⟨H', F, J, hd, -, hV, ⟨C, hP⟩, -, -, hms, hord, hreg, ⟨B', hB'⟩⟩ := fem hΩ hM S b
  obtain rfl : H = H' := (HilbertComplex.ext_of_d fun k => (hd k).trans (hH k).symm).symm
  choose P hPC hPV hPπ using hP
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hPC 0 0)
  have hXV : ∀ N (x : Total (L2Form Ω) a m),
      x ∈ X N ↔ ∀ i : Fin m, x i ∈ (F.V N).V (a + (i : ℕ)) :=
    fun N x => forall_congr' fun i => by rw [← SetLike.mem_coe, hV N]
  have hint : ∀ N, ∀ T ∈ (M N).simplices, interior T.closedInterior ⊆ Ω := fun N T hT => by
    have hsub : T.closedInterior ⊆ closure Ω := by
      rw [← hM.1 N, ← (M N).biUnion_closedInterior]
      exact Set.subset_iUnion₂ (s := fun T (_ : T ∈ (M N).simplices) => T.closedInterior) T hT
    exact (interior_mono hsub).trans
      ((starDomainOf hΩ).starBall.interior_closure_subset (starDomainOf hΩ).s₀_pos)
  have hle : ∀ k, dMin Ω k ≤ dMax Ω k := fun k => by
    rw [dMin_eq, dMax_eq]; exact extDerivOp_minimal_le_maximal hΩ.1 k
  -- the inverse estimate in every degree
  have hinv : ∀ k : ℤ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ N, ∀ y ∈ (F.V N).V k,
      ∀ hy : y ∈ (H.d k (k + 1)).domain,
        meshSize (M N) * ‖H.d k (k + 1) ⟨y, hy⟩‖ ≤ Ck * ‖y‖ := by
    intro k
    rcases lt_or_ge k 0 with hk | hk
    · refine ⟨0, le_rfl, fun N y _ hy => ?_⟩
      have h0 : y = 0 := PiLp.ext fun s => absurd s.2 (by omega)
      subst h0
      rw [show (⟨0, hy⟩ : (H.d k (k + 1)).domain) = 0 from rfl, LinearPMap.map_zero, norm_zero,
        mul_zero, zero_mul]
    · obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
      obtain ⟨Ck, hCk⟩ := inverse_estimate hΩ.1 hM hint S k'
      refine ⟨max Ck 0, le_max_right _ _, fun N y hy hyd => ?_⟩
      have hy₁ : y ∈ femSpace Ω (M N) S (if b then (M N).boundaryFacets else ∅) k' := by
        rw [← hV N]; exact hy
      have hy' : y ∈ femSpace Ω (M N) S ∅ k' := by
        obtain ⟨p, hp, -⟩ := hy₁
        exact ⟨p, hp, fun _ _ _ _ _ h => absurd h (Set.notMem_empty _)⟩
      obtain ⟨hv, hbd⟩ := hCk N y hy'
      have e : H.d k' (k' + 1) ⟨y, hyd⟩ = dMax Ω k' ⟨y, hv⟩ := by
        have hk := hH k'
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at hk
          exact LinearPMap.apply_of_eq hk ⟨y, hyd⟩
        · simp only [↓reduceIte] at hk
          rw [LinearPMap.apply_of_eq hk ⟨y, hyd⟩]
          exact (hle k').2 rfl
      rw [e]
      exact hbd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  choose Ck hCk0 hCk using hinv
  have hinv' : ∀ N (k k' : ℤ) (hk : k + 1 = k') (y : L2Form Ω k) (hy : y ∈ (F.V N).V k)
      (hyd : y ∈ (H.d k k').domain), meshSize (M N) * ‖H.d k k' ⟨y, hyd⟩‖ ≤ Ck k * ‖y‖ := by
    intro N k k' hk; subst hk; exact hCk k N
  have hdom : ∀ N (x : Total (L2Form Ω) a m), x ∈ X N → x ∈ (H.totalD a m).domain :=
    fun N x hx i j => (F.V N).le_domain _ _ ((hXV N x).1 hx i)
  -- the inverse estimate on the window
  set Cw : ℝ := m * ∑ i : Fin m, Ck (a + (i : ℕ))
  have hwin : ∀ N, ∀ x ∈ X N, meshSize (M N) * ‖H.dApply a m x‖ ≤ Cw * ‖x‖ := by
    intro N x hx
    have hh := hM.2.2.1 N
    rw [HilbertComplex.dApply_eq (hdom N x hx)]
    have key := H.norm_totalD_le a m (hdom N x hx)
      (β := fun i => Ck (a + (i : ℕ)) / meshSize (M N) * ‖x‖)
      (fun i => by have := hCk0 (a + (i : ℕ)); positivity) fun i j hij => by
        have h1 := hinv' N (a + (i : ℕ)) (a + (j : ℕ)) (by omega) (x i)
          ((hXV N x).1 hx i) (hdom N x hx i j)
        have h2 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
        rw [div_mul_eq_mul_div, le_div_iff₀ hh, mul_comm]
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (hCk0 _))
    have e : meshSize (M N) * (m * ∑ i : Fin m, Ck (a + (i : ℕ)) / meshSize (M N) * ‖x‖) =
        Cw * ‖x‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      simp only [Cw]
      field_simp
    exact (mul_le_mul_of_nonneg_left key hh.le).trans_eq e
  refine ⟨⟨Cw, hwin⟩, fun s hs => ?_⟩
  set A : ℝ := (1 + C) * ∑ i : Fin m, |J.B s (a + (i : ℕ))| +
    m * ∑ i : Fin m, |B' s (a + (i : ℕ))|
  have hA1 : 0 ≤ (1 + C) * ∑ i : Fin m, |J.B s (a + (i : ℕ))| := by positivity
  have hA2 : 0 ≤ (m : ℝ) * ∑ i : Fin m, |B' s (a + (i : ℕ))| := by positivity
  refine ⟨4 * (A + 1), fun T L U U₁ U₂ U₃ hU hU' hreg' N Δt K u hΔt hK => ?_⟩
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg K) hΔt.le).trans hK
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hU' 0 ⟨le_rfl, hT0⟩).1
  have hh := hM.2.2.1 N
  have hpow : J.meshSize N ^ J.ord s = meshSize (M N) ^ (s + 1) := by
    rw [hms, hord, show ((s : ℝ) + 1) = ((s + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hhp : 0 ≤ meshSize (M N) ^ (s + 1) := by positivity
  -- the Jackson estimate attained by the `L²` projection, and its differential
  have hjack : ∀ (k : ℤ) (L' : ℝ) (x : L2Form Ω k), 0 ≤ L' → S.PolyOrderAt n s k →
      Reg s k L' x → ‖P N k x - x‖ ≤ (1 + C) * |J.B s k| * (L' * meshSize (M N) ^ (s + 1)) := by
    intro k L' x hL' hpo hx
    obtain ⟨v, hv, h1, -⟩ := J.jackson s N k x hL' ((hreg s k L' x).2 ⟨hpo, hx⟩)
    have hfix : P N k v = v := by
      rw [hPπ N k ⟨v, (F.V N).le_domain k (k + 1) hv⟩]; exact (F.π N).proj k _ hv
    have q := (P N k).norm_sub_apply_le_of_apply_eq (hPC N k) hfix x
    have h1' : ‖x - v‖ ≤ |J.B s k| * (L' * meshSize (M N) ^ (s + 1)) := by
      rw [← hpow]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by rw [hpow]; positivity))
    rw [norm_sub_rev]
    calc ‖x - P N k x‖ ≤ (1 + C) * ‖x - v‖ := q
      _ ≤ (1 + C) * (|J.B s k| * (L' * meshSize (M N) ^ (s + 1))) :=
          mul_le_mul_of_nonneg_left h1' (by linarith)
      _ = _ := by ring
  have hdproj : ∀ (k k' : ℤ) (hk : k + 1 = k') (L' : ℝ) (x : L2Form Ω k)
      (hx : x ∈ (H.d k k').domain), 0 ≤ L' → S.PolyOrderAt n s k → Reg s k L' x →
      ‖H.d k k' ⟨P N k x - x, Submodule.sub_mem _ ((F.V N).le_domain k k' (hPV N k x)) hx⟩‖ ≤
        |B' s k| * (L' * meshSize (M N) ^ (s + 1)) := by
    intro k k' hk L' x hx hL' hpo hrx
    subst hk
    have hb := (hB' s N k (L := L') ⟨x, hx⟩ hL' ((hreg s k L' x).2 ⟨hpo, hrx⟩)).2
    have e : (⟨P N k x - x, Submodule.sub_mem _ ((F.V N).le_domain k (k + 1) (hPV N k x)) hx⟩ :
        (H.d k (k + 1)).domain) =
        ⟨_, (F.V N).le_domain k (k + 1) ((F.π N).π k ⟨x, hx⟩).2⟩ - ⟨x, hx⟩ :=
      Subtype.ext (by rw [Submodule.coe_sub, ← hPπ N k ⟨x, hx⟩])
    rw [e, LinearPMap.map_sub, norm_sub_rev, ← hpow]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by rw [hpow]; positivity))
  -- the projection onto the window
  let Pt : Total (L2Form Ω) a m →ₗ[ℝ] Total (L2Form Ω) a m :=
    { toFun := fun x => WithLp.toLp 2 fun i => P N (a + (i : ℕ)) (x i)
      map_add' := fun x y => PiLp.ext fun i => by simp
      map_smul' := fun c x => PiLp.ext fun i => by simp }
  have hPt : ∀ x (i : Fin m), Pt x i ∈ (F.V N).V (a + (i : ℕ)) := fun x i => hPV N _ (x i)
  have hsum : ∀ (L' : ℝ) (x : Total (L2Form Ω) a m), 0 ≤ L' →
      (∀ i : Fin m, Reg s (a + (i : ℕ)) L' (x i)) →
      ‖Pt x - x‖ ≤ A * (L' * meshSize (M N) ^ (s + 1)) := by
    intro L' x hL' hx
    refine (PiLp.norm_le_sum_norm _).trans ?_
    calc ∑ i, ‖(Pt x - x) i‖ ≤ ∑ i : Fin m,
          (1 + C) * |J.B s (a + (i : ℕ))| * (L' * meshSize (M N) ^ (s + 1)) :=
          Finset.sum_le_sum fun i _ => hjack _ L' (x i) hL' (hs i) (hx i)
      _ = (1 + C) * (∑ i : Fin m, |J.B s (a + (i : ℕ))|) * (L' * meshSize (M N) ^ (s + 1)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ A * (L' * meshSize (M N) ^ (s + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  set ε := A * (L * meshSize (M N) ^ (s + 1))
  have h1 : ∀ t ∈ Icc 0 T, ‖Pt (U t) - U t‖ ≤ ε := fun t ht =>
    hsum L (U t) hL0 fun i => (hreg' t ht t ht i).1
  have h3 : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T,
      ‖(Pt (U t') - U t') - (Pt (U t) - U t)‖ ≤ ε * |t' - t| := fun t ht t' ht' => by
    have e : (Pt (U t') - U t') - (Pt (U t) - U t) = Pt (U t' - U t) - (U t' - U t) := by
      rw [_root_.map_sub]; abel
    rw [e]
    refine (hsum (L * |t' - t|) _ (by positivity) fun i => (hreg' t ht t' ht' i).2).trans_eq ?_
    simp only [ε]; ring
  have h2 : ∀ t ∈ Icc 0 T, ‖H.dApply a m (Pt (U t)) - H.dApply a m (U t)‖ ≤ ε := by
    intro t ht
    obtain ⟨hD, -⟩ := HilbertComplex.inner_of_mem_graph_wave (F.V N) (hU' t ht).2
    have hPD : Pt (U t) ∈ (H.totalD a m).domain := fun i j => (F.V N).le_domain _ _ (hPt _ i)
    have hzD : Pt (U t) - U t ∈ (H.totalD a m).domain := Submodule.sub_mem _ hPD hD
    rw [HilbertComplex.dApply_eq hPD, HilbertComplex.dApply_eq hD, ← LinearPMap.map_sub]
    have key := H.norm_totalD_le a m hzD
      (β := fun i => |B' s (a + (i : ℕ))| * (L * meshSize (M N) ^ (s + 1)))
      (fun i => by positivity) fun i j hij =>
        hdproj _ _ (by omega) L (U t i) (hD i j) hL0 (hs i) (hreg' t ht t ht i).1
    refine (le_of_eq (congrArg _ (congrArg _ (Subtype.ext rfl)))).trans (key.trans ?_)
    rw [← Finset.sum_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hw := HilbertComplex.wave_error (F.V N) Pt hPt hΔt hU hU' h1 h2 h3 hK u
  have hXeq : X N = {x | ∀ i : Fin m, x i ∈ (F.V N).V (a + (i : ℕ))} := Set.ext (hXV N)
  have hε0 : 0 ≤ ε := by positivity
  have hd2 : 0 ≤ Δt ^ 2 := sq_nonneg _
  have hA0 : 0 ≤ A := by linarith
  set E := L * meshSize (M N) ^ (s + 1) with hE
  have hE0 : 0 ≤ E := by positivity
  have t1 : 0 ≤ A * E := by positivity
  have t2 : 0 ≤ T * (A * E) := by positivity
  have t3 : 0 ≤ T * E := by positivity
  have t4 : 0 ≤ L * Δt ^ 2 := by positivity
  have t5 : 0 ≤ A * (L * Δt ^ 2) := by positivity
  have t6 : 0 ≤ T * (A * (L * Δt ^ 2)) := by positivity
  have t7 : 0 ≤ T * (L * Δt ^ 2) := by positivity
  have hrhs : 4 * (A + 1) * (1 + T) * L * (meshSize (M N) ^ (s + 1) + Δt ^ 2) =
      4 * (A * E) + 4 * E + 4 * (T * (A * E)) + 4 * (T * E) + 4 * (A * (L * Δt ^ 2)) +
        4 * (L * Δt ^ 2) + 4 * (T * (A * (L * Δt ^ 2))) + 4 * (T * (L * Δt ^ 2)) := by
    simp only [hE]; ring
  have hl1 : 3 * ε + T * (L * Δt ^ 2 / 2 + 2 * ε) =
      3 * (A * E) + (T * (L * Δt ^ 2)) / 2 + 2 * (T * (A * E)) := by simp only [ε]; ring
  have hl2 : 3 * ε + T * (L * Δt ^ 2 / 3 + 4 * ε) =
      3 * (A * E) + (T * (L * Δt ^ 2)) / 3 + 4 * (T * (A * E)) := by simp only [ε]; ring
  have hfin : 3 * ε + T * (L * Δt ^ 2 / 2 + 2 * ε) ≤
      4 * (A + 1) * (1 + T) * L * (meshSize (M N) ^ (s + 1) + Δt ^ 2) ∧
      3 * ε + T * (L * Δt ^ 2 / 3 + 4 * ε) ≤
      4 * (A + 1) * (1 + T) * L * (meshSize (M N) ^ (s + 1) + Δt ^ 2) := by
    rw [hrhs, hl1, hl2]
    constructor <;> linarith
  refine ⟨fun hstep hu0 => ?_, fun C₀ c hC₀ hinvC hc1 hcfl hstep hu0 hu1 => ?_⟩
  · have := hw.1 (fun k hk => hXeq ▸ hstep k hk) ((hXV N _).1 hu0)
    linarith [hfin.1]
  · have hc0 : 0 ≤ c := by
      have h0 : 0 * meshSize (M N) ≤ c * meshSize (M N) := by
        rw [zero_mul]; exact (by positivity : (0 : ℝ) ≤ 2 * C₀ * Δt).trans hcfl
      exact le_of_mul_le_mul_right h0 hh
    have hcfl' : ∀ x, (∀ i : Fin m, x i ∈ (F.V N).V (a + (i : ℕ))) →
        2 * Δt * ‖H.dApply a m x‖ ≤ c * ‖x‖ := fun x hx => by
      have h1 := hinvC N x ((hXV N x).2 hx)
      refine le_of_mul_le_mul_left ?_ hh
      calc meshSize (M N) * (2 * Δt * ‖H.dApply a m x‖) =
            2 * Δt * (meshSize (M N) * ‖H.dApply a m x‖) := by ring
        _ ≤ 2 * Δt * (C₀ * ‖x‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2 * C₀ * Δt) * ‖x‖ := by ring
        _ ≤ (c * meshSize (M N)) * ‖x‖ := mul_le_mul_of_nonneg_right hcfl (norm_nonneg _)
        _ = meshSize (M N) * (c * ‖x‖) := by ring
    have := hw.2 c hc0 hc1 hcfl' (fun k hk => hXeq ▸ hstep k hk) ((hXV N _).1 hu0)
      ((hXV N _).1 hu1)
    linarith [hfin.2]

/-! ### The Whitney schemes of the cube -/

section Cube

open Feec.Models.Cube.Inhomogeneous Feec.Models.Cube.FEM HilbertComplex

theorem crankNicolson_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧ ∀ H : HilbertComplex ℝ (L2Form (cube 3)),
      (∀ k, H.d k (k + 1) = dMax (cube 3) k) →
    let V : ℕ → Set (Total (L2Form (cube 3)) 0 3) := fun N => femTotal (cube 3) (𝒯 N) topSeq ∅ 0 3
    let V₀ : ℕ → Set (Total (L2Form (cube 3)) 0 3) := fun N =>
      femTotal (cube 3) (𝒯 N) topSeq (𝒯 N).boundaryFacets 0 3
    (∀ N m (w : Fin m → FormField 3), (∀ i, Continuous (w i)) →
      ∃! x, IsWhitneyInterp (cube 3) (𝒯 N) 0 m w x) ∧
    (∀ N Δt g u, g ∈ V N → u ∈ V N → ∃! u', H.IsCNStep 0 3 (V N) (V₀ N) Δt g u u') ∧
    (∀ N, ∃ v ∈ femSpace (cube 3) (𝒯 N) topSeq (𝒯 N).boundaryFacets 1, v ≠ 0) ∧
    ∀ N T L (X : RowSolution T L) (Δt : ℝ) (M : ℕ) (u g : ℕ → Total (L2Form (cube 3)) 0 3),
      0 < Δt → M * Δt ≤ T →
      (∀ k < M, H.IsCNStep 0 3 (V N) (V₀ N) Δt (g (k + 1)) (u k) (u (k + 1))) →
      (∀ k < M, ∃ w, IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u ((k + 1 : ℕ) * Δt)) w ∧
        g (k + 1) - w ∈ V₀ N) →
      IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u 0) (u 0) → ∀ U, IsRepr (cube 3) 0 3 (X.u (M * Δt)) U →
        ‖u M - U‖ ≤ C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) := by
  refine ⟨cubeMesh, cnConst, isMeshFamily_cube, points_cube, fun H hH => ?_⟩
  obtain rfl := eq_ofFeec_complex hH
  intro V V₀
  refine ⟨fun N m w hw => ?_, fun N Δt g u hg hu => ?_, fun N => ?_,
    fun N T L X Δt M u g hΔt hM hstep hg hu0 U hU => ?_⟩
  · refine ⟨WithLp.toLp 2 fun i => FEMInterp.canonicalInterp N (0 + (i : ℕ)) ⟨w i, hw i⟩,
      fun i => (isWhitneyInterpAt_cube_iff N _ ⟨w i, hw i⟩ _).2 rfl, fun x hx =>
        PiLp.ext fun i => (isWhitneyInterpAt_cube_iff N _ ⟨w i, hw i⟩ (x i)).1 (hx i)⟩
  · obtain ⟨g', rfl⟩ := (mem_whitney_iff N g).1 hg
    obtain ⟨u', rfl⟩ := (mem_whitney_iff N u).1 hu
    obtain ⟨a, ha, hau⟩ := whitney_existsUnique_cnStep N (Δt / 2) 0 g' u'
    refine ⟨ofD N a, (isCNStep_iff N Δt g' u' _).2 ⟨a, rfl, ha⟩, fun x hx => ?_⟩
    obtain ⟨b, rfl, hb⟩ := (isCNStep_iff N Δt g' u' x).1 hx
    rw [hau b hb]
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (whitneyMin_one_ne_bot N)
    refine ⟨v, ?_, hv0⟩
    rw [← whitneyMin_V_eq N]
    exact hv
  · have hL0 := X.zero_le_L hΔt hM
    have hu : ∀ k ≤ M, u k ∈ V N := by
      intro k hk
      rcases k with _ | k
      · rw [X.eq_interp hu0]; exact (mem_whitney_iff N _).2 ⟨_, rfl⟩
      · exact (hstep k hk).1
    obtain ⟨a, ha⟩ := exists_seq_ofD N hu
    have hgm : ∀ k < M, ∃ c ∈ whitneyInterior N,
        g (k + 1) = ofD N (c + X.toFeec.interp N ((k + 1 : ℕ) * Δt)) := by
      intro k hk
      obtain ⟨w, hw, hgw⟩ := hg k hk
      obtain ⟨c, hc, hce⟩ := (mem_whitneyMin_iff N _).1 hgw
      refine ⟨c, hc, ?_⟩
      rw [show ofD N (c + X.toFeec.interp N ((k + 1 : ℕ) * Δt)) =
        ofD N c + ofD N (X.toFeec.interp N ((k + 1 : ℕ) * Δt)) from _root_.map_add _ _ _, ← hce,
        ← X.eq_interp hw, sub_add_cancel]
    choose! c hc hgc using hgm
    obtain ⟨gD, hgD⟩ : ∃ gD : ℕ → DState (whitneyRow N),
        ∀ k, gD (k + 1) = c k + X.toFeec.interp N ((k + 1 : ℕ) * Δt) :=
      ⟨fun j => c (j - 1) + X.toFeec.interp N (j * Δt), fun k => by simp only [Nat.add_sub_cancel]⟩
    have hstep' : ∀ k < M, Feec.TimeStepping.IsDirichletCNStep (whitneyInterior N)
        (discreteWave (whitneyRow N)) (Δt / 2) 0 (gD (k + 1)) (a k) (a (k + 1)) := by
      intro k hk
      have h := hstep k hk
      rw [hgc k hk, ha k hk.le, ha (k + 1) hk] at h
      obtain ⟨u', hu', h'⟩ := (isCNStep_iff N Δt _ _ _).1 h
      rw [← ofD_injective N hu'] at h'
      rwa [hgD]
    have hg' : ∀ k < M, gD (k + 1) - X.toFeec.interp N ((k + 1 : ℕ) * Δt) ∈ whitneyInterior N :=
      fun k hk => by rw [hgD, add_sub_cancel_right]; exact hc k hk
    have hu0' : a 0 = X.toFeec.interp N 0 :=
      ofD_injective N ((ha 0 (Nat.zero_le M)).symm.trans (X.eq_interp hu0))
    have key := X.toFeec.whitney_cn_error_le_row N hΔt hL0 hM hstep' hg' hu0'
    rw [X.eq_field hU, ha M le_rfl, meshSize_cubeMesh]
    exact key

set_option maxHeartbeats 800000 in
theorem leapfrog_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧ ∀ H : HilbertComplex ℝ (L2Form (cube 3)),
      (∀ k, H.d k (k + 1) = dMax (cube 3) k) →
    let V : ℕ → Set (Total (L2Form (cube 3)) 0 3) := fun N => femTotal (cube 3) (𝒯 N) topSeq ∅ 0 3
    let V₀ : ℕ → Set (Total (L2Form (cube 3)) 0 3) := fun N =>
      femTotal (cube 3) (𝒯 N) topSeq (𝒯 N).boundaryFacets 0 3
    let IsInv C₀ := ∀ N, ∀ v ∈ V N, meshSize (𝒯 N) * ‖H.dApply 0 3 v‖ ≤ C₀ * ‖v‖
    (∃ C₀, IsInv C₀) ∧ (∀ N Δt g u u', g ∈ V N → u ∈ V N → u' ∈ V N →
      ∃! u'', H.IsLeapfrogStep 0 3 (V N) (V₀ N) Δt g u u' u'') ∧ ∀ C₀, 0 ≤ C₀ → IsInv C₀ →
    (∀ N Δt c (u : ℕ → Total (L2Form (cube 3)) 0 3) m, 0 ≤ Δt → c < 1 →
      2 * C₀ * Δt ≤ c * meshSize (𝒯 N) →
      (∀ k < m, H.IsLeapfrogStep 0 3 (V N) (V₀ N) Δt 0 (u k) (u (k + 1)) (u (k + 2))) →
      u 0 ∈ V₀ N → u 1 ∈ V₀ N → √(1 - c) * ‖u (m + 1)‖ ≤ √((1 + c) * (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2))) ∧
    ∀ N T L (X : RowSolution T L) (Δt c : ℝ) (M : ℕ) (u g : ℕ → Total (L2Form (cube 3)) 0 3),
      0 < Δt → c < 1 → 2 * C₀ * Δt ≤ c * meshSize (𝒯 N) → M * Δt ≤ T →
      (∀ k, k + 2 ≤ M → H.IsLeapfrogStep 0 3 (V N) (V₀ N) Δt (g (k + 2)) (u k) (u (k + 1))
        (u (k + 2))) →
      (∀ k, k + 2 ≤ M → ∃ w, IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u ((k + 2 : ℕ) * Δt)) w ∧
        g (k + 2) - w ∈ V₀ N) →
      IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u 0) (u 0) →
      IsWhitneyInterp (cube 3) (𝒯 N) 0 3 (X.u Δt) (u 1) →
      ∀ U, IsRepr (cube 3) 0 3 (X.u (M * Δt)) U →
        ‖u M - U‖ ≤ C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) / (1 - c) := by
  obtain ⟨K, -, hK⟩ := exists_mul_norm_discreteD_whitneyRow_le
  refine ⟨cubeMesh, leapfrogConst, isMeshFamily_cube, points_cube, fun H hH => ?_⟩
  obtain rfl := eq_ofFeec_complex hH
  intro V V₀ IsInv
  have hnorm : ∀ N (a : DState (whitneyRow N)),
      ‖(HilbertComplex.ofFeec (complex 3)).dApply 0 3 (ofD N a)‖ =
        ‖discreteD (whitneyRow N) a‖ := fun N a => by
    rw [dApply_ofD, norm_emb (inner_dEmb (whitneyRow N))]
  refine ⟨⟨K, fun N v hv => ?_⟩, fun N Δt g u u' hg hu hu' => ?_, fun C₀ hC₀ hC₀' => ?_⟩
  · obtain ⟨a, rfl⟩ := (mem_whitney_iff N v).1 hv
    calc meshSize (cubeMesh N) * ‖(HilbertComplex.ofFeec (complex 3)).dApply 0 3 (ofD N a)‖ =
          Feec.Models.Cube.FEM.meshSize N * ‖discreteD (whitneyRow N) a‖ := by
          rw [meshSize_cubeMesh]; exact congrArg _ (hnorm N a)
      _ ≤ K * ‖a‖ := hK N a
      _ = K * ‖ofD N a‖ := by rw [norm_ofD]
  · obtain ⟨g', rfl⟩ := (mem_whitney_iff N g).1 hg
    obtain ⟨u₀, rfl⟩ := (mem_whitney_iff N u).1 hu
    obtain ⟨u₁, rfl⟩ := (mem_whitney_iff N u').1 hu'
    obtain ⟨a, ha, hau⟩ := Feec.TimeStepping.existsUnique_isDirichletLeapfrogStep
      (V₀ := whitneyInterior N) (A := discreteWave (whitneyRow N)) Δt g' u₀ u₁
    refine ⟨ofD N a, (isLeapfrogStep_iff N Δt g' u₀ u₁ _).2 ⟨a, rfl, ha⟩, fun x hx => ?_⟩
    obtain ⟨b, rfl, hb⟩ := (isLeapfrogStep_iff N Δt g' u₀ u₁ x).1 hx
    rw [hau b hb]
  have hC : ∀ N (x : DState (whitneyRow N)),
      Feec.Models.Cube.FEM.meshSize N * ‖discreteD (whitneyRow N) x‖ ≤ C₀ * ‖x‖ := fun N x => by
    have := hC₀' N (ofD N x) ((mem_whitney_iff N _).2 ⟨x, rfl⟩)
    calc Feec.Models.Cube.FEM.meshSize N * ‖discreteD (whitneyRow N) x‖ =
          meshSize (cubeMesh N) * ‖(HilbertComplex.ofFeec (complex 3)).dApply 0 3 (ofD N x)‖ := by
          rw [meshSize_cubeMesh]; exact congrArg _ (hnorm N x).symm
      _ ≤ C₀ * ‖ofD N x‖ := this
      _ = C₀ * ‖x‖ := by rw [norm_ofD]
  refine ⟨?_, ?_⟩
  · intro N Δt c u m hΔt hc1 hcfl hstep hu0 hu1
    have hmem : ∀ k ≤ m + 1, u k ∈ V N := by
      intro k hk
      rcases k with _ | _ | k
      · exact mem_whitney_of_mem_whitneyMin N hu0
      · exact mem_whitney_of_mem_whitneyMin N hu1
      · exact (hstep k (by omega)).1
    obtain ⟨a, ha⟩ := exists_seq_ofD N hmem
    have hstep' : ∀ k < m, Feec.TimeStepping.IsDirichletLeapfrogStep (whitneyInterior N)
        (discreteWave (whitneyRow N)) Δt 0 (a k) (a (k + 1)) (a (k + 2)) := by
      intro k hk
      have h := hstep k hk
      rw [← ofD_zero N, ha k (by omega), ha (k + 1) (by omega), ha (k + 2) (by omega)] at h
      obtain ⟨u', hu', h'⟩ := (isLeapfrogStep_iff N Δt _ _ _ _).1 h
      rwa [← ofD_injective N hu'] at h'
    have ha0 : a 0 ∈ whitneyInterior N := by
      have h := hu0; rw [ha 0 (by omega)] at h; exact (ofD_mem_whitneyMin_iff N _).1 h
    have ha1 : a 1 ∈ whitneyInterior N := by
      have h := hu1; rw [ha 1 (by omega)] at h; exact (ofD_mem_whitneyMin_iff N _).1 h
    rw [meshSize_cubeMesh] at hcfl
    have key := whitney_leapfrog_stable N hC₀ (hC N) hΔt hc1 hcfl hstep' ha0 ha1
    rwa [ha 0 (by omega), ha 1 (by omega), ha (m + 1) le_rfl, norm_ofD, norm_ofD, norm_ofD]
  · intro N T L X Δt c M u g hΔt hc1 hcfl hM hstep hg hu0 hu1 U hU
    have hL0 := X.zero_le_L hΔt hM
    have hmem : ∀ k ≤ M, u k ∈ V N := by
      intro k hk
      rcases k with _ | _ | k
      · rw [X.eq_interp hu0]; exact (mem_whitney_iff N _).2 ⟨_, rfl⟩
      · rw [X.eq_interp hu1]; exact (mem_whitney_iff N _).2 ⟨_, rfl⟩
      · exact (hstep k hk).1
    obtain ⟨a, ha⟩ := exists_seq_ofD N hmem
    have hgm : ∀ k, k + 2 ≤ M → ∃ e ∈ whitneyInterior N,
        g (k + 2) = ofD N (e + X.toFeec.interp N ((k + 2 : ℕ) * Δt)) := by
      intro k hk
      obtain ⟨w, hw, hgw⟩ := hg k hk
      obtain ⟨e, he, hee⟩ := (mem_whitneyMin_iff N _).1 hgw
      refine ⟨e, he, ?_⟩
      rw [show ofD N (e + X.toFeec.interp N ((k + 2 : ℕ) * Δt)) =
        ofD N e + ofD N (X.toFeec.interp N ((k + 2 : ℕ) * Δt)) from _root_.map_add _ _ _, ← hee,
        ← X.eq_interp hw, sub_add_cancel]
    choose! e he hge using hgm
    obtain ⟨gD, hgD⟩ : ∃ gD : ℕ → DState (whitneyRow N),
        ∀ k, gD (k + 2) = e k + X.toFeec.interp N ((k + 2 : ℕ) * Δt) :=
      ⟨fun j => e (j - 2) + X.toFeec.interp N (j * Δt), fun k => by simp only [Nat.add_sub_cancel]⟩
    have hstep' : ∀ k, k + 2 ≤ M → Feec.TimeStepping.IsDirichletLeapfrogStep (whitneyInterior N)
        (discreteWave (whitneyRow N)) Δt (gD (k + 2)) (a k) (a (k + 1)) (a (k + 2)) := by
      intro k hk
      have h := hstep k hk
      rw [hge k hk, ha k (by omega), ha (k + 1) (by omega), ha (k + 2) hk] at h
      obtain ⟨u', hu', h'⟩ := (isLeapfrogStep_iff N Δt _ _ _ _).1 h
      rw [← ofD_injective N hu'] at h'
      rwa [hgD]
    have hg' : ∀ k, k + 2 ≤ M →
        gD (k + 2) - X.toFeec.interp N ((k + 2 : ℕ) * Δt) ∈ whitneyInterior N := by
      intro k hk
      rw [hgD, add_sub_cancel_right]
      exact he k hk
    have hu0' : a 0 = X.toFeec.interp N 0 :=
      ofD_injective N ((ha 0 (Nat.zero_le M)).symm.trans (X.eq_interp hu0))
    rw [meshSize_cubeMesh] at hcfl
    rw [X.eq_field hU, meshSize_cubeMesh]
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · subst hM0
      set a' := Function.update a 1 (X.toFeec.interp N Δt)
      have h0 : a' 0 = a 0 := Function.update_of_ne (by decide) _ _
      have key := X.toFeec.whitney_leapfrog_error_le_row N hC₀ (hC N) hΔt hc1 hcfl hL0 hM
        (u := a') (g := gD) (fun k hk => absurd hk (by omega)) (fun k hk => absurd hk (by omega))
        (h0.trans hu0') (Function.update_self _ _ _)
      rw [h0] at key
      rw [ha 0 le_rfl]
      exact key
    have hu1' : a 1 = X.toFeec.interp N Δt :=
      ofD_injective N ((ha 1 hM0).symm.trans (X.eq_interp hu1))
    have key := X.toFeec.whitney_leapfrog_error_le_row N hC₀ (hC N) hΔt hc1 hcfl hL0 hM hstep'
      hg' hu0' hu1'
    rw [ha M le_rfl]
    exact key

theorem rowSolution_nonvacuous (T : ℝ) :
    ∃ L, ∃ X : RowSolution T L, ∀ t, ∃ y ∈ cube 3, X.u t 1 y ≠ 0 ∧ X.u₁ t 1 y ≠ 0 :=
  exists_rowSolution T

end Cube

/-! ### The shape functions -/

theorem unisolvent (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (∀ w ∈ (polyForm ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyFormMinus ℝ m (r + k - m) (m - k)).map evalForm,
        faceMoment T.points e η w = 0) → w = 0) ∧
    (∀ w ∈ (polyFormMinus ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyForm ℝ m (r + k - m - 1) (m - k)).map evalForm,
        faceMoment T.points e η w = 0) → w = 0) ∧
    Module.finrank ℝ (polyForm ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyFormMinus ℝ m (r + k - m) (m - k)) else 0) ∧
    Module.finrank ℝ (polyFormMinus ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyForm ℝ m (r + k - m - 1) (m - k))
        else 0) :=
  unisolvent_of_feec T hr k

theorem affineInvariantForms (K : Type u) [Field K] [CharZero K] (n : ℕ) :
    AffineInvariantForms K n :=
  affineInvariantForms_of_feec K n

theorem charZero_iff_classification (K : Type u) [Field K] :
    CharZero K ↔ ∀ (n r k : ℕ) (W : Submodule K (PolyForm K n)), IsGLInvariant K n W →
      W ≤ homForm K n (r + 1) (k + 1) →
        W = ⊥ ∨ W = (homForm K n (r + 2) k).map (polyExtDeriv K n) ∨
          W = (homForm K n r (k + 2)).map (koszul K n) ∨ W = homForm K n (r + 1) (k + 1) :=
  charZero_iff_classification_of_feec K

theorem charZero_iff_closed_eq_exact (K : Type u) [Field K] :
    CharZero K ↔ ∀ n r k : ℕ, LinearMap.ker (polyExtDeriv K n) ⊓ homForm K n r (k + 1) =
      (homForm K n (r + 1) k).map (polyExtDeriv K n) :=
  charZero_iff_closed_eq_exact_of_feec K

end FEEC
