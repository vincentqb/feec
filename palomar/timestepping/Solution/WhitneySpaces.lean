module

public import Solution.CubeSpaces
public import Feec.Models.Cube.InhomogeneousError

/-!
# The Whitney spaces of the challenge are `Feec`'s

The Whitney sequence `topSeq` (`P₁Λ⁰ → P₁⁻Λ¹ → ⋯`) has the spaces of the trimmed sequence
`P₁⁻Λ` (`P₁⁻Λ⁰ = P₁Λ⁰`, `Feec.Koszul.polyFormMinus_zero_right`), whose element is equivalent to the
Whitney element (`Feec.FiniteElement.whitneyElement_equivalent_trimmed`). So on the Freudenthal
meshes of the cube the spaces `femSpace` of `topSeq` without boundary condition and with
vanishing traces on the boundary facets are the spaces of `Feec`'s Whitney complexes
`Feec.Models.Cube.FEM.whitney` and `whitneyMin` (`whitney_V_eq`, `whitneyMin_V_eq`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3–4
* [H. Whitney, *Geometric Integration Theory*][Whitney1957], Ch. IV

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

namespace TimeStepping

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM

variable {n : ℕ}

/-- The trimmed sequence `P₁⁻Λ` in every degree. -/
def whitneySeq : PolySeq where
  full _ := false
  deg _ := 1
  one_le_deg _ := le_rfl
  transition _ := Or.inl ⟨rfl, rfl⟩

theorem whitneySeq_toFeec :
    whitneySeq.toFeec = Feec.FiniteElement.PolySeq.trimmed 1 le_rfl := by
  unfold PolySeq.toFeec Feec.FiniteElement.PolySeq.trimmed
  congr 1

theorem topSeq_space (k : ℕ) : topSeq.space n k = whitneySeq.space n k := by
  rcases k with _ | k
  · change (polyForm ℝ n 1 0).map evalForm = (polyFormMinus ℝ n 1 0).map evalForm
    rw [polyForm_eq, polyFormMinus_eq, Feec.Koszul.polyFormMinus_zero_right le_rfl]
  · rfl

theorem isFemPieces_topSeq {Ω : Set (Fin n → ℝ)} {M : SimplicialMesh n} {k : ℤ} {u : L2Form Ω k}
    {p : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n} :
    IsFemPieces Ω M topSeq k u p ↔ IsFemPieces Ω M whitneySeq k u p := by
  unfold IsFemPieces
  rw [topSeq_space]

theorem femSpace_topSeq (Ω : Set (Fin n → ℝ)) (M : SimplicialMesh n)
    (Γ : Set (Finset (Fin n → ℝ))) (k : ℤ) :
    femSpace Ω M topSeq Γ k = femSpace Ω M whitneySeq Γ k := by
  ext u
  exact exists_congr fun p => and_congr_left' isFemPieces_topSeq

/-- The finite element spaces of a `Feec` mesh, transported to its domain, are the challenge's. -/
theorem maximalSubcomplexOfEq_V [NeZero n] (S : PolySeq) (m : Feec.Mesh.SimplicialMesh n)
    {Ω : Set (Fin n → ℝ)} (h : m.domain = Ω) (hm : IsOpen m.domain) (hΩ : IsOpen Ω) (k : ℤ) :
    (SetLike.coe (((deRham ℝ n).maximalSubcomplexOfEq h hm hΩ (S.toFeec.subcomplex m hm)).V k) :
      Set (L2Form Ω k)) = femSpace Ω (SimplicialMesh.ofFeec m) S ∅ k := by
  obtain ⟨T, d, h1, h2, h3⟩ := m
  subst h
  ext u
  exact mem_V_iff S (SimplicialMesh.ofFeec ⟨T, d, h1, h2, h3⟩) _ rfl u

/-- **The Whitney spaces `Vₕᵏ` of the Freudenthal meshes are the challenge's.** -/
theorem whitney_V_eq (N : ℕ) (k : ℤ) :
    (SetLike.coe ((whitney 3 N).V k) : Set (L2Form (cube 3) k)) =
      femSpace (cube 3) (cubeMesh N) topSeq ∅ k := by
  have h := maximalSubcomplexOfEq_V whitneySeq (mesh 3 N) (mesh_domain 3 N)
    (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3) k
  have e : whitney 3 N = (deRham ℝ 3).maximalSubcomplexOfEq (mesh_domain 3 N)
      (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3)
      (whitneySeq.toFeec.subcomplex (mesh 3 N) (isOpen_mesh_domain 3 N)) := by
    rw [whitneySeq_toFeec]
    unfold whitney whitneySubcomplex Feec.FiniteElement.PolySeq.subcomplex
    rw [whitneyElement_equivalent_trimmed.subcomplex_eq]
  rw [femSpace_topSeq, e]
  exact h

/-- **The Whitney spaces `V̊ₕᵏ` with vanishing boundary DOFs are the challenge's.** -/
theorem whitneyMin_V_eq (N : ℕ) (k : ℤ) :
    (SetLike.coe ((whitneyMin 3 N).V k) : Set (L2Form (cube 3) k)) =
      femSpace (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets k := by
  have h := minimalSubcomplexOfEq_V whitneySeq (mesh 3 N) (mesh_domain 3 N)
    (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3) (center 3) (strictStar_mesh 3 N) k
  have e : whitneyMin 3 N = (deRham ℝ 3).minimalSubcomplexOfEq (mesh_domain 3 N)
      (isOpen_mesh_domain 3 N) (isOpen_cubeDomain 3)
      (whitneySeq.toFeec.subcomplexMin (mesh 3 N) (isOpen_mesh_domain 3 N) (center 3)
        (strictStar_mesh 3 N)) := by
    rw [whitneySeq_toFeec]
    unfold whitneyMin whitneySubcomplexMin Feec.FiniteElement.PolySeq.subcomplexMin
    rw [whitneyElement_equivalent_trimmed.subcomplexMin_eq]
  rw [femSpace_topSeq, e]
  exact h

end TimeStepping
