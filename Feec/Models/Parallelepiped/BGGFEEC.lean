module

public import Feec.Models.Cube.BGGFEEC
public import Feec.Models.Parallelepiped.FiniteElement

/-!
# The FEEC theorem for the Hessian, elasticity and div-div complexes on parallelepipeds

On every open parallelepiped and every open box of `ℝ³`, the FEEC theorem holds with no hypothesis
for every stacked conforming family of the discrete Hessian, elasticity and div-div complexes.

## Main results

* `deRham_hasRegularDecomposition_affine`: the regular decompositions of `HΛ(Ω)`.
* `hessianFEEC_affine`, `elasticityFEEC_affine`, `divDivFEEC_affine`: the FEEC theorems.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Parallelepiped

open Feec.Domain
open Feec.Models.Cube.Geometry (Q isOpen_Q)

theorem preimage_Q_domain {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    affMap A⁻¹ (affInvShift A b) ⁻¹' Q (Fin n) = domain A b := by
  rw [← Cube.FEM.cubeDomain_eq_Q]; rfl

theorem preimage_Q_box {n : ℕ} {a c : Fin n → ℝ} (h : ∀ i, a i < c i) :
    affMap (boxMatrix a c)⁻¹ (affInvShift (boxMatrix a c) a) ⁻¹' Q (Fin n) =
      Set.univ.pi fun i => Set.Ioo (a i) (c i) := by
  rw [preimage_Q_domain, domain_boxMatrix h]

section Forms

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) (b : Fin n → ℝ)
  {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hT : affMap A b ⁻¹' Q (Fin n) = Ω)
include hA hT

/-- The `H¹`-regular decompositions of `HΛ(Ω)` on the preimage `Ω = T⁻¹(Q)` of the cube under an
invertible affine map. [ArnoldHu2021], §2, Theorem 3 -/
theorem deRham_hasRegularDecomposition_affine : (deRham ℝ n).HasRegularDecomposition Ω 0 :=
  (formPullData A hA).hasRegularDecomposition hA b (hT ▸ isOpen_Q.preimage (continuous_affMap _ _))
    isOpen_Q hT Cube.Sobolev.deRham_hasRegularDecomposition_Q

theorem finiteDimensional_cohomology_deRham_affine (i : ℤ) :
    FiniteDimensional ℝ (((deRham ℝ n).maximalComplex hΩ).cohomology i) :=
  (formPullData A hA).finiteDimensional_cohomology hA b hΩ isOpen_Q hT i

end Forms

section BGG

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsUnit A.det)
  (b : Fin 3 → ℝ) {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) (hT : affMap A b ⁻¹' Q (Fin 3) = Ω)
include hA hT

theorem deRhamVec_hasRegularDecomposition_affine (m : ℕ) :
    (deRhamVec 𝕜 m).HasRegularDecomposition Ω 0 :=
  have hΩ : IsOpen Ω := hT ▸ isOpen_Q.preimage (continuous_affMap _ _)
  deRhamVec_ofReal (𝕜 := 𝕜) m ▸ (Feec.Domain.deRhamVec_hasRegularDecomposition hΩ
    (deRham_hasRegularDecomposition_affine hA b hT) m).ofReal hΩ

theorem finiteDimensional_cohomology_deRhamVec_affine (m : ℕ) (i : ℤ) :
    FiniteDimensional 𝕜 (((deRhamVec 𝕜 m).maximalComplex hΩ).cohomology i) :=
  have := finiteDimensional_cohomology_deRham_affine hA b hΩ hT i
  have := deRhamVec_finiteDimensional_cohomology hΩ m i
  deRhamVec_ofReal (𝕜 := 𝕜) m ▸ (deRhamVec ℝ m).finiteDimensional_cohomology_ofReal hΩ i

variable {κ : Type*}

/-- The FEEC theorem for discrete Hessian complexes on parallelepipeds `Ω = T⁻¹(Q) ⊆ ℝ³`, with no
hypothesis (the complexes of [ArnoldHu2021], §4.1). -/
theorem hessianFEEC_affine (G : (hessianMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (0 < ·) (· < 0) :=
  have := finiteDimensional_cohomology_deRhamVec_affine (𝕜 := 𝕜) hA b hΩ hT 1
  have := finiteDimensional_cohomology_deRhamVec_affine (𝕜 := 𝕜) hA b hΩ hT 3
  Feec.Domain.hessianFEEC hΩ (hessianMaximalData_regularDecomposition hΩ
    (deRhamVec_hasRegularDecomposition_affine hA b hT 1)) G

/-- The FEEC theorem for discrete elasticity complexes on parallelepipeds, with no hypothesis. -/
theorem elasticityFEEC_affine (G : (elasticityMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (1 < ·) (· < 1) :=
  have := finiteDimensional_cohomology_deRhamVec_affine (𝕜 := 𝕜) hA b hΩ hT 3
  Feec.Domain.elasticityFEEC hΩ (elasticityMaximalData_regularDecomposition hΩ
    ((deRhamVec_hasRegularDecomposition_affine hA b hT 3).mono zero_le_one)) G

/-- The FEEC theorem for discrete div-div complexes on parallelepipeds, with no hypothesis. -/
theorem divDivFEEC_affine (G : (divDivMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (2 < ·) (· < 2) :=
  have := finiteDimensional_cohomology_deRhamVec_affine (𝕜 := 𝕜) hA b hΩ hT 1
  have := finiteDimensional_cohomology_deRhamVec_affine (𝕜 := 𝕜) hA b hΩ hT 3
  Feec.Domain.divDivFEEC hΩ (divDivMaximalData_regularDecomposition hΩ
    ((deRhamVec_hasRegularDecomposition_affine hA b hT 3).mono zero_le_two)) G

end BGG

section Box

variable {𝕜 : Type*} [RCLike 𝕜] {a c : Fin 3 → ℝ} (h : ∀ i, a i < c i)
  (hΩ : IsOpen (Set.univ.pi fun i => Set.Ioo (a i) (c i))) {κ : Type*}
include h

theorem hessianFEEC_box (G : (hessianMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (0 < ·) (· < 0) :=
  hessianFEEC_affine (isUnit_det_inv (isUnit_det_boxMatrix h)) _ hΩ (preimage_Q_box h) G

theorem elasticityFEEC_box (G : (elasticityMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (1 < ·) (· < 1) :=
  elasticityFEEC_affine (isUnit_det_inv (isUnit_det_boxMatrix h)) _ hΩ (preimage_Q_box h) G

theorem divDivFEEC_box (G : (divDivMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (2 < ·) (· < 2) :=
  divDivFEEC_affine (isUnit_det_inv (isUnit_det_boxMatrix h)) _ hΩ (preimage_Q_box h) G

end Box

end Feec.Models.Parallelepiped
