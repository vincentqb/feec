module

public import Feec.Models.Parallelepiped.StarShaped
public import Feec.FiniteElement.AffinePieces

/-!
# The pieces of finite element forms on the Kuhn simplices of the cube

Conforming finite element forms are elementwise form fields of the local space
(`Feec.FiniteElement.PolySeq.exists_piece_of_mem_subcomplex`), and the Kuhn simplices are the
elements of the Freudenthal mesh of `(0, ½)ⁿ`
(`Feec.Models.Cube.FEM.exists_mem_simplices_points_eq`).

## References

* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory

public section

namespace Feec.FiniteElement.PolySeq

open Feec.Domain

variable {n : ℕ}

/-- **The pieces of a conforming finite element form**: a form of the subcomplex of `S` on the mesh
`m` is, a.e. on each element `Ω ∩ T`, a form field of `S.space n k`. -/
theorem exists_piece_of_mem_subcomplex [NeZero n] {Ω : Set (Fin n → ℝ)}
    (m : Feec.Mesh.SimplicialMesh n) (h : m.domain = Ω) (hm : IsOpen m.domain) (hΩ : IsOpen Ω)
    (S : PolySeq) {k : ℤ} {u : L2F ℝ Ω (formIdx n k)}
    (hu : u ∈ ((deRham ℝ n).maximalSubcomplexOfEq h hm hΩ (S.subcomplex m hm)).V k)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ m.simplices) :
    ∃ w ∈ S.space n k.toNat, ∀ s : formIdx n k,
      ⇑(u s) =ᵐ[volume.restrict (Ω ∩ T.closedInterior)] fun x => w x s.1 := by
  obtain ⟨Ts, d, h1, h2, h3⟩ := m
  subst h
  exact (polyElement n S).exists_piece_of_mem_V _ hu hT

end Feec.FiniteElement.PolySeq

namespace Feec.Models.Cube.FEM

variable {n : ℕ}

/-- **The Kuhn simplices are the elements of the Freudenthal mesh** ([Freudenthal1942]): the
simplex with vertices `h (z + e_{σ 0} + ⋯ + e_{σ (j - 1)})` is an element of `mesh n N`. -/
theorem exists_mem_simplices_points_eq [NeZero n] (N : ℕ) (z : Fin n → Fin (N + 1))
    (σ : Equiv.Perm (Fin n)) :
    ∃ T ∈ (mesh n N).simplices, ∀ j i,
      T.points j i = ((z i : ℝ) + if (σ.symm i : ℕ) < (j : ℕ) then 1 else 0) / (2 * (N + 1)) := by
  refine ⟨_, (Feec.Mesh.mem_freudenthalMesh_simplices (hs := by norm_num)).2 ⟨z, σ, rfl⟩,
    fun j i => ?_⟩
  simp only [Feec.Mesh.mapEquiv_points, Feec.Mesh.freudenthalSimplex_points,
    Feec.Mesh.boxMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add,
    Feec.Mesh.latticePoint_apply, Feec.Mesh.finLattice, Feec.Mesh.kuhnVertex]
  push_cast
  field_simp

end Feec.Models.Cube.FEM
