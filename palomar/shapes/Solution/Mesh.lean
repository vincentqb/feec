module

public import Solution.Defs
public import Feec.Mesh.Basic

/-!
# Meshes of the challenge in `Feec`

A mesh of the challenge is a `Feec.Mesh.SimplicialMesh` with the same simplices
(`SimplicialMesh.toFeec`, its domain replaced by an equal set), the vertex sets being those of
`Feec` (`vertexSet_eq`), and its `m`-faces are those of `Feec` (`faces_eq`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace FEEC

variable {n : ℕ}

theorem vertexSet_eq {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    vertexSet T = Feec.Mesh.vertexSet T := by
  ext x
  simp [vertexSet, Feec.Mesh.mem_vertexSet]

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

/-- **The `m`-faces of the challenge are those of `Feec`.** -/
theorem faces_eq (m : ℕ) : (M.faces m : Set (Finset (Fin n → ℝ))) = (M.toFeec Ω h).faces m := by
  ext g
  rw [Finset.mem_coe, faces, Finset.mem_biUnion]
  change _ ↔ #g = m + 1 ∧ ∃ T ∈ M.simplices, g ⊆ Feec.Mesh.vertexSet T
  simp only [mem_powersetCard, vertexSet_eq]
  exact ⟨fun ⟨T, hT, hg, hc⟩ => ⟨hc, T, hT, hg⟩, fun ⟨hc, T, hT, hg⟩ => ⟨T, hT, hg, hc⟩⟩

end SimplicialMesh

end FEEC
