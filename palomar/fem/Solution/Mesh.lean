module

public import Solution.Defs
public import Feec.Models.StarShaped.FiniteElement

/-!
# Meshes and domains of the challenge in `Feec`

A mesh of the challenge is a `Feec.Mesh.SimplicialMesh` with the same simplices
(`SimplicialMesh.toFeec`, its domain replaced by an equal set), with the same diameters, mesh
size and edge matrices; shape regularity and quasi-uniformity are those of `Feec`
(`isShapeRegular_toFeec`, `isQuasiUniform_toFeec`). A domain star-shaped with respect to a ball
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

theorem edgeMap_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) : edgeMap T = T.linearPart := rfl

theorem isShapeRegular_toFeec {M : SimplicialMesh n} {Ω : Set (Fin n → ℝ)} (h : M.domain = Ω)
    {C c : ℝ} (hC : 0 ≤ C) (hM : IsShapeRegular M C c) :
    Feec.Mesh.IsShapeRegular ((M.toFeec Ω h).simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n))
      C c := by
  intro T hT
  obtain ⟨h1, h2, h3⟩ := hM T hT
  have hd : 0 ≤ diam T := Metric.diam_nonneg
  refine ⟨?_, ?_, h3⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hd) fun x => ?_
    exact h1 x
  · refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hC hd) fun y => ?_
    have e : T.linearEquiv (T.linearEquiv.symm y) = y := T.linearEquiv.apply_symm_apply y
    have := h2 (T.linearEquiv.symm y)
    rw [edgeMap_eq, ← Affine.Simplex.linearEquiv_apply, e] at this
    exact this

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
def meshFamilyOf {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) {M : ℕ → SimplicialMesh n}
    (hM : IsMeshFamily Ω M) : Feec.Models.StarShaped.MeshFamily (starDomainOf hΩ) where
  mesh N := (M N).toFeec Ω (hM.1 N)
  C := hM.2.1.choose
  c := hM.2.1.choose_spec.choose
  q := hM.2.1.choose_spec.choose_spec.choose
  C_nonneg := hM.2.1.choose_spec.choose_spec.choose_spec.1
  c_pos := hM.2.1.choose_spec.choose_spec.choose_spec.2.1
  q_pos := hM.2.1.choose_spec.choose_spec.choose_spec.2.2.1
  domain_eq _ := rfl
  data N :=
    ⟨isShapeRegular_toFeec (hM.1 N) hM.2.1.choose_spec.choose_spec.choose_spec.1
      (hM.2.1.choose_spec.choose_spec.choose_spec.2.2.2 N).1,
      isQuasiUniform_toFeec (hM.1 N) (hM.2.1.choose_spec.choose_spec.choose_spec.2.2.2 N).2,
      hM.2.2.1 N⟩
  tendsto_meshSize := hM.2.2.2

@[simp] theorem meshFamilyOf_mesh {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M) (N : ℕ) :
    (meshFamilyOf hΩ hM).mesh N = (M N).toFeec Ω (hM.1 N) := rfl

end FEEC
