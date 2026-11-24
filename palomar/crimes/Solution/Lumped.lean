module

public import Solution.Defs
public import Feec.FiniteElement.LumpedMassDefect
public import Feec.FiniteElement.LumpedLaplacian

/-!
# Meshes, the `P₁` forms and the lumped mass of the challenge are those of `Feec`

A mesh of the challenge is a `Feec.Mesh.SimplicialMesh` with the same fields
(`FEEC.SimplicialMesh.toFeec`). The `P₁` gradient of the challenge, by the edge matrix, is
`Feec.FiniteElement.p1Grad` (`FEEC.p1Grad_eq`, from `Feec.FiniteElement.p1Grad_eq_vecMul`), and
its `P₁` interpolant `u(v₀) + ∇Π_T u · (x - v₀)` is `Feec.FiniteElement.p1Interp`
(`FEEC.p1Interp_eq`: both are affine with gradient `∇Π_T u` and the value `u(v₀)` at `v₀`); so
the stiffness form, the consistent mass and the lumped mass of the challenge are
`Feec.FiniteElement.p1Stiffness`, `Feec.FiniteElement.p1Mass` and
`Feec.FiniteElement.lumpedInner` (`FEEC.p1Stiffness_eq`, `FEEC.p1Mass_eq`, `FEEC.lumpedInner_eq`).
The lumped readings of `FEEC.crime_massLumping` exist on every mesh with every hat function
(`FEEC.exists_lumpedReading`, from `Feec.FiniteElement.exists_isLumpedReading`; not compared).

## References

* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

namespace FEEC

variable {n : ℕ}

theorem vertexSet_eq {k : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) k) :
    vertexSet T = Feec.Mesh.vertexSet T := by
  ext x
  simp [vertexSet, Feec.Mesh.mem_vertexSet]

/-- A mesh of the challenge as a mesh of `Feec`. -/
def SimplicialMesh.toFeec (M : SimplicialMesh n) : Feec.Mesh.SimplicialMesh n where
  simplices := M.simplices
  domain := M.domain
  biUnion_closedInterior := M.biUnion_closedInterior
  pairwise_disjoint_interior := M.pairwise_disjoint_interior
  inter_closedInterior T hT T' hT' := by
    rw [← vertexSet_eq, ← vertexSet_eq]; exact M.inter_closedInterior T hT T' hT'

/-- The `P₁` gradient of the challenge is `Feec.FiniteElement.p1Grad`. -/
theorem p1Grad_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : (Fin n → ℝ) → ℝ) :
    p1Grad T u = Feec.FiniteElement.p1Grad T.points u := by
  rw [Feec.FiniteElement.p1Grad_eq_vecMul]
  rfl

/-- The `P₁` interpolant of the challenge is `Feec.FiniteElement.p1Interp`
(`Feec.FiniteElement.p1Interp_sub`, `Feec.FiniteElement.p1Interp_vertex`). -/
theorem p1Interp_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : p1Interp T u x = Feec.FiniteElement.p1Interp T.points u x := by
  have h := Feec.FiniteElement.p1Interp_sub T.points u x (T.points 0)
  rw [Feec.FiniteElement.p1Interp_vertex (Feec.FiniteElement.isUnit_det_edgeMatrix T)] at h
  rw [p1Interp, p1Grad_eq]
  linarith

theorem p1Stiffness_eq (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    p1Stiffness M u w = Feec.FiniteElement.p1Stiffness M.toFeec u w := by
  simp only [p1Stiffness, Feec.FiniteElement.p1Stiffness, p1Grad_eq]
  rfl

theorem p1Mass_eq (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    p1Mass M u w = Feec.FiniteElement.p1Mass M.toFeec u w := by
  simp only [p1Mass, Feec.FiniteElement.p1Mass, p1Interp_eq]
  rfl

theorem lumpedInner_eq (M : SimplicialMesh n) (u w : (Fin n → ℝ) → ℝ) :
    lumpedInner M u w = Feec.FiniteElement.lumpedInner M.toFeec u w :=
  rfl

/-- **The lumped readings of `FEEC.crime_massLumping` exist with every hat function** on every
mesh: the lumped-mass method on all the vertices, read in `L²` of the meshed region
(`Feec.FiniteElement.exists_isLumpedReading`). -/
theorem exists_lumpedReading (M : SimplicialMesh n) :
    ∃ (X E : Type) (_ : NormedAddCommGroup X) (_ : InnerProductSpace ℝ X) (_ : CompleteSpace X)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (ν : X → (Fin n → ℝ) → ℝ) (ι : X →L[ℝ] E),
      (∀ v w, ⟪v, w⟫_ℝ = lumpedInner M (ν v) (ν w)) ∧
      (∀ v w, ⟪ι v, ι w⟫_ℝ = p1Mass M (ν v) (ν w)) ∧
      ∀ T ∈ M.simplices, ∀ x ∈ vertexSet T, ∃ v, ν v = fun z => if z = x then 1 else 0 := by
  obtain ⟨κ, _, y, i, hr, hhat⟩ := Feec.FiniteElement.exists_isLumpedReading M.toFeec
  exact ⟨EuclideanSpace ℝ κ,
    Feec.Domain.L2F ℝ (closure M.domain) (Feec.Domain.formIdx n ((0 : ℕ) : ℤ)),
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Feec.FiniteElement.lumpedNodal M.toFeec y, i,
    fun v w => (hr.inner_eq v w).trans (lumpedInner_eq M _ _).symm,
    fun v w => (hr.inner_apply_eq v w).trans (p1Mass_eq M _ _).symm,
    fun T hT x hx => hhat T hT x (by rwa [← vertexSet_eq])⟩

end FEEC
