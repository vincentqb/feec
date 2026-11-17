module

public import Solution.Spaces
public import Feec.Models.Parallelepiped.StarShaped

/-!
# The Freudenthal meshes of the cube

The Freudenthal meshes of `Feec.Models.Cube.FEM.mesh` are a mesh family of the challenge
(`isMeshFamily_cube`, from `Feec.Models.StarShaped.CubeWitness.meshFamily`) named by their
vertices (`points_cube`), and the finite element spaces with vanishing boundary DOFs of a `Feec`
mesh are the challenge's `femSpaceMin` (`minimalSubcomplexOfEq_V`, from `mem_V₀_iff`).

## References

* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set Filter

@[expose] public noncomputable section

namespace TimeStepping

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.StarShaped

variable {n : ℕ}

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

/-- The Freudenthal meshes of the cube. -/
abbrev cubeMesh (N : ℕ) : SimplicialMesh 3 := SimplicialMesh.ofFeec (mesh 3 N)

theorem isMeshFamily_cube : IsMeshFamily (cubeDomain 3) cubeMesh :=
  isMeshFamily_ofFeec (CubeWitness.meshFamily 3)

theorem meshSize_cubeMesh (N : ℕ) :
    TimeStepping.meshSize (cubeMesh N) = Feec.Models.Cube.FEM.meshSize N :=
  (Feec.Models.Cube.FEM.meshSize_mesh N).trans (Feec.Models.Cube.FEM.hN_eq_meshSize N)

/-- The simplices of the Freudenthal meshes are the Kuhn simplices `h (z + K_σ)`. -/
theorem points_cube (N : ℕ) : ∀ T ∈ (cubeMesh N).simplices, ∃ (z : Fin 3 → Fin (N + 1))
    (σ : Equiv.Perm (Fin 3)), ∀ j i,
      T.points j i = ((z i : ℝ) + if (σ.symm i : ℕ) < (j : ℕ) then 1 else 0) / (2 * (N + 1)) := by
  intro T hT
  obtain ⟨z, σ, hzσ⟩ := (Feec.Mesh.mem_freudenthalMesh_simplices (hs := by norm_num)).1 hT
  refine ⟨z, σ, fun j i => ?_⟩
  rw [← hzσ]
  simp only [Feec.Mesh.mapEquiv_points, Feec.Mesh.freudenthalSimplex_points,
    Feec.Mesh.boxMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add,
    Feec.Mesh.latticePoint_apply, Feec.Mesh.finLattice, Feec.Mesh.kuhnVertex]
  push_cast
  field_simp

/-- The finite element spaces with vanishing boundary DOFs of a `Feec` mesh, transported to its
domain, are the challenge's. -/
theorem minimalSubcomplexOfEq_V (S : PolySeq) (m : Feec.Mesh.SimplicialMesh 3)
    {Ω : Set (Fin 3 → ℝ)} (h : m.domain = Ω) (hm : IsOpen m.domain) (hΩ : IsOpen Ω)
    (x₀ : Fin 3 → ℝ)
    (hstar : ∀ x ∈ closure m.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ m.domain)
    (k : ℤ) :
    (SetLike.coe (((deRham ℝ 3).minimalSubcomplexOfEq h hm hΩ
      (S.toFeec.subcomplexMin m hm x₀ hstar)).V k) : Set (L2Form Ω k)) =
      femSpaceMin Ω (SimplicialMesh.ofFeec m) S k := by
  obtain ⟨T, d, h1, h2, h3⟩ := m
  subst h
  ext u
  exact mem_V₀_iff S (SimplicialMesh.ofFeec ⟨T, d, h1, h2, h3⟩) _ rfl u

end TimeStepping
