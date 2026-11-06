module

public import Solution.Complex
public import Solution.Forms
public import Solution.Spaces
public import Solution.Regularity
public import Solution.Maxwell
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
