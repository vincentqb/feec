module

public import Solution.Defs
public import Feec.Models.Cube.FiniteDifferenceHeat
public import Feec.FiniteElement.LumpedConsistency

/-!
# Meshes and the lumped-mass `P₁` Laplacian of the challenge are those of `Feec`

A mesh of the challenge is a `Feec.Mesh.SimplicialMesh` with the same fields
(`TimeStepping.SimplicialMesh.toFeec`, `TimeStepping.SimplicialMesh.ofFeec`, inverse to each
other). The `P₁` gradient of the challenge, by the edge matrix, is
`Feec.FiniteElement.p1Grad` (`TimeStepping.p1Grad_eq`, from
`Feec.FiniteElement.p1Grad_eq_vecMul`), so the stiffness form, the lumped mass and the
lumped-mass Laplacian are those of `Feec` (`TimeStepping.lumpedLaplacian_eq`), and the gradients
of the barycentric coordinates are `Feec.FiniteElement.baryGrad`
(`Feec.FiniteElement.p1Grad_nodalIndicator`): non-obtuse meshes are those of `Feec`
(`TimeStepping.isNonobtuse_iff`), and translation invariance is that of `Feec`
(`TimeStepping.isTranslationInvariantAt_iff`).

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace TimeStepping

variable {n : ℕ}

theorem vertexSet_eq {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    vertexSet T = Feec.Mesh.vertexSet T := by
  ext x
  simp [vertexSet, Feec.Mesh.mem_vertexSet]

namespace SimplicialMesh

/-- A mesh of the challenge as a mesh of `Feec`. -/
def toFeec (M : SimplicialMesh n) : Feec.Mesh.SimplicialMesh n where
  simplices := M.simplices
  domain := M.domain
  biUnion_closedInterior := M.biUnion_closedInterior
  pairwise_disjoint_interior := M.pairwise_disjoint_interior
  inter_closedInterior T hT T' hT' := by
    rw [← vertexSet_eq, ← vertexSet_eq]; exact M.inter_closedInterior T hT T' hT'

/-- A mesh of `Feec` as a mesh of the challenge. -/
def ofFeec (M : Feec.Mesh.SimplicialMesh n) : SimplicialMesh n where
  simplices := M.simplices
  domain := M.domain
  biUnion_closedInterior := M.biUnion_closedInterior
  pairwise_disjoint_interior := M.pairwise_disjoint_interior
  inter_closedInterior T hT T' hT' := by
    rw [vertexSet_eq, vertexSet_eq]; exact M.inter_closedInterior T hT T' hT'

@[simp] theorem toFeec_ofFeec (M : Feec.Mesh.SimplicialMesh n) : (ofFeec M).toFeec = M := rfl

@[simp] theorem ofFeec_domain (M : Feec.Mesh.SimplicialMesh n) : (ofFeec M).domain = M.domain :=
  rfl

end SimplicialMesh

/-- The `P₁` gradient of the challenge is `Feec.FiniteElement.p1Grad`. -/
theorem p1Grad_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : (Fin n → ℝ) → ℝ) :
    p1Grad T u = Feec.FiniteElement.p1Grad T.points u := by
  rw [Feec.FiniteElement.p1Grad_eq_vecMul]
  rfl

theorem p1Stiffness_eq (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    p1Stiffness M u w = Feec.FiniteElement.p1Stiffness M.toFeec u w := by
  simp only [p1Stiffness, Feec.FiniteElement.p1Stiffness, p1Grad_eq]
  rfl

theorem lumpedMass_eq (M : SimplicialMesh n) (y : Fin n → ℝ) :
    lumpedMass M y = Feec.FiniteElement.lumpedMass M.toFeec y :=
  rfl

/-- The lumped-mass Laplacian of the challenge is `Feec.FiniteElement.lumpedLaplacianOn`. -/
theorem lumpedLaplacian_eq (M : SimplicialMesh n) {ι : Type*} [Fintype ι]
    (x : ι → Fin n → ℝ) : lumpedLaplacian M x = Feec.FiniteElement.lumpedLaplacianOn M.toFeec x := by
  simp only [lumpedLaplacian, p1Stiffness_eq, lumpedMass_eq]
  rfl

/-- Non-obtuse meshes of the challenge are those of `Feec`. -/
theorem isNonobtuse_iff (M : SimplicialMesh n) :
    IsNonobtuse M ↔ Feec.FiniteElement.IsNonobtuse M.toFeec := by
  refine forall₂_congr fun T _ => forall₃_congr fun j k _ => ?_
  have e : ∀ j, p1Grad T (fun z => if z = T.points j then 1 else 0) =
      Feec.FiniteElement.baryGrad T.points j := fun j => by
    rw [p1Grad_eq]
    exact Feec.FiniteElement.p1Grad_nodalIndicator T.independent.injective j
  rw [e, e]

/-- Translation invariance of the challenge is that of `Feec`. -/
theorem isTranslationInvariantAt_iff (M : SimplicialMesh n) (y : Fin n → ℝ) :
    IsTranslationInvariantAt M y ↔ Feec.FiniteElement.IsTranslationInvariantAt M.toFeec y := by
  simp only [IsTranslationInvariantAt, Feec.FiniteElement.IsTranslationInvariantAt, vertexSet_eq]
  refine forall₂_congr fun T _ => imp_congr_right fun _ =>
    ⟨fun h v hv => ?_, fun h j => h _ (Feec.Mesh.points_mem_vertexSet T j)⟩
  obtain ⟨j, rfl⟩ := Feec.Mesh.mem_vertexSet.1 hv
  exact h j

end TimeStepping
