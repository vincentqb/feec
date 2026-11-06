module

public import Solution.Defs
public import Feec.Models.StarShaped.FiniteElement

/-!
# Meshes and domains of the challenge in `Feec`

A mesh of the challenge is a `Feec.Mesh.SimplicialMesh` with the same simplices
(`SimplicialMesh.toFeec`, its domain replaced by an equal set), with the same diameters, mesh
size; shape regularity by inscribed balls gives that of `Feec` by edge matrices
(`isShapeRegular_toFeec`, from `Feec.Mesh.isShapeRegular_of_ball`) and quasi-uniformity is that
of `Feec` (`isQuasiUniform_toFeec`). A domain star-shaped with respect to a ball
is a `Feec.Models.StarShaped.StarDomain` (`starDomainOf`) and a mesh family of the challenge is a
`Feec.Models.StarShaped.MeshFamily` (`meshFamilyOf`).

## References

* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5, §4, §5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Filter Topology Set

@[expose] public noncomputable section

namespace FEEC

variable {n : ℕ}

theorem vertexSet_eq {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    vertexSet T = Feec.Mesh.vertexSet T := by
  ext x
  simp [vertexSet, Feec.Mesh.mem_vertexSet]

theorem coe_vertexSet {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    (vertexSet T : Set (Fin n → ℝ)) = Set.range T.points := by
  rw [vertexSet_eq, Feec.Mesh.coe_vertexSet]

namespace SimplicialMesh

/-- A mesh of the challenge as a `Feec` mesh of the set `Ω = M.domain`. -/
def toFeec (M : SimplicialMesh n) (Ω : Set (Fin n → ℝ)) (h : M.domain = Ω) :
    Feec.Mesh.SimplicialMesh n where
  simplices := M.simplices
  domain := Ω
  biUnion_closedInterior := h ▸ M.biUnion_closedInterior
  pairwise_disjoint_interior := M.pairwise_disjoint_interior
  inter_closedInterior T hT T' hT' := by
    rw [← vertexSet_eq, ← vertexSet_eq]; exact M.inter_closedInterior T hT T' hT'

variable (M : SimplicialMesh n) (Ω : Set (Fin n → ℝ)) (h : M.domain = Ω)

@[simp] theorem toFeec_simplices : (M.toFeec Ω h).simplices = M.simplices := rfl

@[simp] theorem toFeec_domain : (M.toFeec Ω h).domain = Ω := rfl

theorem meshSize_toFeec : (M.toFeec Ω h).meshSize = meshSize M := rfl

end SimplicialMesh

theorem diam_eq {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) : diam T = Feec.Mesh.diam T := rfl

/-- A mesh shape regular with constant `σ` (inscribed balls) is shape regular in the sense of
`Feec` (edge matrices), with constants `max n σ` and `1 / (n! σⁿ)`
(`Feec.Mesh.isShapeRegular_of_ball`). -/
theorem isShapeRegular_toFeec [NeZero n] {M : SimplicialMesh n} {Ω : Set (Fin n → ℝ)}
    (h : M.domain = Ω) {σ : ℝ} (hM : IsShapeRegular M σ) :
    Feec.Mesh.IsShapeRegular ((M.toFeec Ω h).simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n))
      (max n σ) (1 / ((n.factorial : ℝ) * σ ^ n)) :=
  Feec.Mesh.isShapeRegular_of_ball hM

/-- The shape-regularity constant of a mesh with a simplex is positive. -/
theorem pos_of_isShapeRegular [NeZero n] {M : SimplicialMesh n} {σ : ℝ} (hM : IsShapeRegular M σ)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) : 0 < σ := by
  obtain ⟨-, ρ, hρ, -, hd⟩ := hM T hT
  exact pos_of_mul_pos_left ((Feec.Mesh.diam_pos T).trans_le hd) hρ.le

/-- A mesh of positive mesh size has a simplex. -/
theorem exists_mem_simplices {M : SimplicialMesh n} (hM : 0 < meshSize M) :
    ∃ T, T ∈ M.simplices := by
  by_contra h
  have : IsEmpty M.simplices := ⟨fun T => h ⟨T, T.2⟩⟩
  simp [meshSize] at hM

theorem isQuasiUniform_toFeec {M : SimplicialMesh n} {Ω : Set (Fin n → ℝ)} (h : M.domain = Ω)
    {q : ℝ} (hM : IsQuasiUniform M q) : Feec.FiniteElement.IsQuasiUniform (M.toFeec Ω h) q :=
  hM

/-- A domain star-shaped with respect to a ball as a `Feec` star domain. -/
def starDomainOf {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) :
    Feec.Models.StarShaped.StarDomain n where
  Ω := Ω
  isOpen := hΩ.1
  x₀ := hΩ.2.2.choose
  s₀ := hΩ.2.2.choose_spec.choose
  R := max 1 (hΩ.2.1.closure.subset_closedBall hΩ.2.2.choose).choose
  s₀_pos := hΩ.2.2.choose_spec.choose_spec.1
  R_pos := lt_of_lt_of_le one_pos (le_max_left _ _)
  starBall := hΩ.2.2.choose_spec.choose_spec.2
  norm_sub_le y hy := by
    have := (hΩ.2.1.closure.subset_closedBall hΩ.2.2.choose).choose_spec hy
    rw [Metric.mem_closedBall, dist_eq_norm] at this
    exact this.trans (le_max_right _ _)

@[simp] theorem starDomainOf_Ω {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) :
    (starDomainOf hΩ).Ω = Ω := rfl

/-- A mesh family of the challenge as a `Feec` mesh family of the star domain. -/
def meshFamilyOf [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) :
    Feec.Models.StarShaped.MeshFamily (starDomainOf hΩ) where
  mesh N := (M N).toFeec Ω (hM.1 N)
  C := max n hM.2.1.choose
  c := 1 / ((n.factorial : ℝ) * hM.2.1.choose ^ n)
  q := hM.2.1.choose_spec.choose
  C_nonneg := le_trans n.cast_nonneg (le_max_left _ _)
  c_pos := by
    obtain ⟨T, hT⟩ := exists_mem_simplices (hM.2.2.1 0)
    have := pos_of_isShapeRegular (hM.2.1.choose_spec.choose_spec.2 0).1 hT
    positivity
  q_pos := hM.2.1.choose_spec.choose_spec.1
  domain_eq _ := rfl
  data N :=
    ⟨isShapeRegular_toFeec (hM.1 N) (hM.2.1.choose_spec.choose_spec.2 N).1,
      isQuasiUniform_toFeec (hM.1 N) (hM.2.1.choose_spec.choose_spec.2 N).2, hM.2.2.1 N⟩
  tendsto_meshSize := hM.2.2.2

@[simp] theorem meshFamilyOf_mesh [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (N : ℕ) :
    (meshFamilyOf hΩ hM).mesh N = (M N).toFeec Ω (hM.1 N) := rfl

end FEEC
