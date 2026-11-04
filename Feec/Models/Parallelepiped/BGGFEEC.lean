module

public import Feec.Models.Cube.BGGFEEC
public import Feec.Models.Parallelepiped.FiniteElement

/-!
# The FEEC theorem for the Hessian, elasticity and div-div complexes on parallelepipeds

Let `T x = A x + b` be an invertible affine map of `ℝⁿ` and `Ω = T⁻¹(Q)` the preimage of the
cube `Q = (0, ½)ⁿ`, i.e. an open parallelepiped (`Feec.Models.Parallelepiped.domain A b` is one,
`preimage_Q_domain`; every open box is one, `preimage_Q_box`). The two hypotheses of the FEEC
theorems for discrete Hessian, elasticity and div-div complexes (`Feec.Domain.hessianFEEC`,
`elasticityFEEC`, `divDivFEEC`) are properties of the rows only, the de Rham complexes of `Ω` with
values in `𝕜ᵐ`, and both reduce to the de Rham complex `HΛ(Ω)` in forms
(`Feec.Domain.deRhamVec_hasRegularDecomposition`, `deRhamVec_finiteDimensional_cohomology`, and
from `ℝ` to `𝕜` through the real and imaginary parts). On `HΛ(Ω)` they are transported from the
cube along the pullback of forms `T^*` (the minors of `A`, `formPullData`):

* **the `H¹`-regular decompositions** `HΛᵏ⁺¹(Ω) = d HΛᵏ(Ω) + H¹Λᵏ⁺¹(Ω)` ([ArnoldHu2021], §2,
  Theorem 3; `deRham_hasRegularDecomposition`, from
  `Feec.Domain.FormPullData.hasRegularDecomposition` and
  `Feec.Models.Cube.Sobolev.deRham_hasRegularDecomposition_Q`);
* **the finite-dimensional cohomology** of `HΛ(Ω)` (`finiteDimensional_cohomology_deRham`, from
  `Feec.Domain.FormPullData.finiteDimensional_cohomology` and the cube).

So **the FEEC theorem holds for every stacked conforming family of the discrete Hessian,
elasticity and div-div complexes on every open parallelepiped and every open box `⊆ ℝ³`**, over
every `RCLike 𝕜`, with no hypothesis (`hessianFEEC`, `elasticityFEEC`, `divDivFEEC`;
`hessianFEEC_box`, …). The BGG data are the same constant-coefficient diagrams on every `Ω`
(`hessianMaximalData 𝕜 hΩ`, …); nothing of them is transported, only the hypotheses on the rows.
As on the cube, no stacked conforming family of these diagrams is constructed
(`Feec.Domain.BGGFEEC`).

Not covered: bi-Lipschitz images of `Q`. `Feec.Domain.LipschitzPullback` carries `H̊(curl)` and
`H(div)` (rows of `3 × 3` matrix fields), but not `H¹` nor the maximal domains in every degree,
which the transport of the regular decompositions needs.

## Main results

* `preimage_Q_domain`, `preimage_Q_box`.
* **`deRham_hasRegularDecomposition`**, **`finiteDimensional_cohomology_deRham`**;
  `deRhamVec_hasRegularDecomposition`, `finiteDimensional_cohomology_deRhamVec`.
* **`hessianFEEC`**, **`elasticityFEEC`**, **`divDivFEEC`**; `hessianFEEC_box`,
  `elasticityFEEC_box`, `divDivFEEC_box`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2 (Theorem 3), §4.1 ((32)),
  Theorem 6
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
  (affine-equivalent domains, change of variables)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Parallelepiped

open Feec.Domain
open Feec.Models.Cube.Geometry (Q isOpen_Q)

/-- **The parallelepiped `A · Q + b` is the preimage of `Q` under `T⁻¹ y = A⁻¹ y - A⁻¹ b`.** -/
theorem preimage_Q_domain {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    affMap A⁻¹ (affInvShift A b) ⁻¹' Q (Fin n) = domain A b := by
  rw [← Cube.FEM.cubeDomain_eq_Q]; rfl

/-- **The open box `∏ᵢ (aᵢ, cᵢ)` is the preimage of `Q`** under the inverse of
`x ↦ diag(2 (c - a)) x + a` (`domain_boxMatrix`). -/
theorem preimage_Q_box {n : ℕ} {a c : Fin n → ℝ} (h : ∀ i, a i < c i) :
    affMap (boxMatrix a c)⁻¹ (affInvShift (boxMatrix a c) a) ⁻¹' Q (Fin n) =
      Set.univ.pi fun i => Set.Ioo (a i) (c i) := by
  rw [preimage_Q_domain, domain_boxMatrix h]

section Forms

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) (b : Fin n → ℝ)
  {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hT : affMap A b ⁻¹' Q (Fin n) = Ω)
include hA hT

/-- **The regular decompositions of `HΛ(Ω)`** on the preimage `Ω = T⁻¹(Q)` of the cube under an
invertible affine map ([ArnoldHu2021], §2, Theorem 3): every `u ∈ HΛᵏ⁺¹(Ω)` is `d p + w` with
`p ∈ HΛᵏ(Ω)` and `w` an `H¹` field (transported from `Q` along `T^*`). -/
theorem deRham_hasRegularDecomposition : (deRham ℝ n).HasRegularDecomposition Ω 0 :=
  (formPullData A hA).hasRegularDecomposition hA b (hT ▸ isOpen_Q.preimage (continuous_affMap _ _))
    isOpen_Q hT Cube.Sobolev.deRham_hasRegularDecomposition_Q

/-- **The cohomology of `HΛ(Ω)` is finite-dimensional** in every degree on the preimage
`Ω = T⁻¹(Q)` of the cube under an invertible affine map (transported from `Q` along `T^*`). -/
theorem finiteDimensional_cohomology_deRham (i : ℤ) :
    FiniteDimensional ℝ (((deRham ℝ n).maximalComplex hΩ).cohomology i) :=
  (formPullData A hA).finiteDimensional_cohomology hA b hΩ isOpen_Q hT i

end Forms

section BGG

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsUnit A.det)
  (b : Fin 3 → ℝ) {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) (hT : affMap A b ⁻¹' Q (Fin 3) = Ω)
include hA hT

/-- **The regular decompositions of the de Rham complexes of `Ω = T⁻¹(Q) ⊆ ℝ³` with values in
`𝕜ᵐ`** (from the forms, row by row, and from `ℝ` to `𝕜`). -/
theorem deRhamVec_hasRegularDecomposition (m : ℕ) :
    (deRhamVec 𝕜 m).HasRegularDecomposition Ω 0 :=
  have hΩ : IsOpen Ω := hT ▸ isOpen_Q.preimage (continuous_affMap _ _)
  deRhamVec_ofReal (𝕜 := 𝕜) m ▸ (Feec.Domain.deRhamVec_hasRegularDecomposition hΩ
    (deRham_hasRegularDecomposition hA b hT) m).ofReal hΩ

/-- **The de Rham complexes of `Ω = T⁻¹(Q) ⊆ ℝ³` with values in `𝕜ᵐ` have finite-dimensional
cohomology** in every degree. -/
theorem finiteDimensional_cohomology_deRhamVec (m : ℕ) (i : ℤ) :
    FiniteDimensional 𝕜 (((deRhamVec 𝕜 m).maximalComplex hΩ).cohomology i) :=
  have := finiteDimensional_cohomology_deRham hA b hΩ hT i
  have := deRhamVec_finiteDimensional_cohomology hΩ m i
  deRhamVec_ofReal (𝕜 := 𝕜) m ▸ (deRhamVec ℝ m).finiteDimensional_cohomology_ofReal hΩ i

variable {κ : Type*}

/-- **The FEEC theorem for discrete Hessian complexes on parallelepipeds**: on the preimage
`Ω = T⁻¹(Q)` of the cube under an invertible affine map `T x = A x + b`, for every stacked
conforming family of the scalar and `𝕜³`-valued `L²` de Rham complexes of `Ω` linked by `I`,
`2 vskw`, `tr`, the FEEC theorem holds for the discrete Hessian complexes `bgg 0`, with no
hypothesis (`Feec.Domain.hessianFEEC`; the complexes of [ArnoldHu2021], §4.1). -/
theorem hessianFEEC (G : (hessianMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (0 < ·) (· < 0) :=
  have := finiteDimensional_cohomology_deRhamVec (𝕜 := 𝕜) hA b hΩ hT 1
  have := finiteDimensional_cohomology_deRhamVec (𝕜 := 𝕜) hA b hΩ hT 3
  Feec.Domain.hessianFEEC hΩ
    (hessianMaximalData_regularDecomposition hΩ (deRhamVec_hasRegularDecomposition hA b hT 1)) G

/-- **The FEEC theorem for discrete elasticity complexes on parallelepipeds** `Ω = T⁻¹(Q)`
(`bgg 1` of two `𝕜³`-valued de Rham complexes linked by `-mskw`, `T - tr`, `2 vskw`;
[ArnoldHu2021], §4.1), with no hypothesis. -/
theorem elasticityFEEC (G : (elasticityMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (1 < ·) (· < 1) :=
  have := finiteDimensional_cohomology_deRhamVec (𝕜 := 𝕜) hA b hΩ hT 3
  Feec.Domain.elasticityFEEC hΩ (elasticityMaximalData_regularDecomposition hΩ
    ((deRhamVec_hasRegularDecomposition hA b hT 3).mono zero_le_one)) G

/-- **The FEEC theorem for discrete div-div complexes on parallelepipeds** `Ω = T⁻¹(Q)` (`bgg 2`
of the `𝕜³`-valued and scalar de Rham complexes linked by `· I`, `-mskw`, `I`; [ArnoldHu2021],
§4.1), with no hypothesis. -/
theorem divDivFEEC (G : (divDivMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (2 < ·) (· < 2) :=
  have := finiteDimensional_cohomology_deRhamVec (𝕜 := 𝕜) hA b hΩ hT 1
  have := finiteDimensional_cohomology_deRhamVec (𝕜 := 𝕜) hA b hΩ hT 3
  Feec.Domain.divDivFEEC hΩ (divDivMaximalData_regularDecomposition hΩ
    ((deRhamVec_hasRegularDecomposition hA b hT 3).mono zero_le_two)) G

end BGG

section Box

variable {𝕜 : Type*} [RCLike 𝕜] {a c : Fin 3 → ℝ} (h : ∀ i, a i < c i)
  (hΩ : IsOpen (Set.univ.pi fun i => Set.Ioo (a i) (c i))) {κ : Type*}
include h

/-- **The FEEC theorem for discrete Hessian complexes on every open box** `∏ᵢ (aᵢ, cᵢ) ⊆ ℝ³`
(`hessianFEEC` with `preimage_Q_box`). -/
theorem hessianFEEC_box (G : (hessianMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (0 < ·) (· < 0) :=
  hessianFEEC (isUnit_det_inv (isUnit_det_boxMatrix h)) _ hΩ (preimage_Q_box h) G

/-- **The FEEC theorem for discrete elasticity complexes on every open box** `∏ᵢ (aᵢ, cᵢ)`. -/
theorem elasticityFEEC_box (G : (elasticityMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (1 < ·) (· < 1) :=
  elasticityFEEC (isUnit_det_inv (isUnit_det_boxMatrix h)) _ hΩ (preimage_Q_box h) G

/-- **The FEEC theorem for discrete div-div complexes on every open box** `∏ᵢ (aᵢ, cᵢ)`. -/
theorem divDivFEEC_box (G : (divDivMaximalData 𝕜 hΩ).StackedFamily κ) :
    G.Verdict (2 < ·) (· < 2) :=
  divDivFEEC (isUnit_det_inv (isUnit_det_boxMatrix h)) _ hΩ (preimage_Q_box h) G

end Box

end Feec.Models.Parallelepiped
