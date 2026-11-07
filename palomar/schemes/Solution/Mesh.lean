module

public import Solution.Defs
public import Feec.Models.StarShaped.FiniteElement

/-!
# Meshes and domains of the challenge in `Feec`

A mesh of the challenge is a `Feec.Mesh.SimplicialMesh` with the same simplices
(`SimplicialMesh.toFeec`, its domain replaced by an equal set), with the same diameters, mesh
size; shape regularity by inscribed balls gives that of `Feec` by edge matrices
(`isShapeRegular_toFeec`, from `Feec.Mesh.isShapeRegular_of_ball`) and quasi-uniformity is that
of `Feec` (`isQuasiUniform_toFeec`).

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

end SimplicialMesh

/-- A mesh shape regular with constant `σ` (inscribed balls) is shape regular in the sense of
`Feec` (edge matrices), with constants `max n σ` and `1 / (n! σⁿ)`
(`Feec.Mesh.isShapeRegular_of_ball`). -/
theorem isShapeRegular_toFeec [NeZero n] {M : SimplicialMesh n} {Ω : Set (Fin n → ℝ)}
    (h : M.domain = Ω) {σ : ℝ} (hM : IsShapeRegular M σ) :
    Feec.Mesh.IsShapeRegular ((M.toFeec Ω h).simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n))
      (max n σ) (1 / ((n.factorial : ℝ) * σ ^ n)) :=
  Feec.Mesh.isShapeRegular_of_ball hM

theorem isQuasiUniform_toFeec {M : SimplicialMesh n} {Ω : Set (Fin n → ℝ)} (h : M.domain = Ω)
    {q : ℝ} (hM : IsQuasiUniform M q) : Feec.FiniteElement.IsQuasiUniform (M.toFeec Ω h) q :=
  hM

end FEEC
