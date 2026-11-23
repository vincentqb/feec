module

public import Feec.FiniteElement.FormBGGElasticity
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Cube.MaximalRegularDecomposition

/-!
# The Hessian, elasticity and div–div complexes of forms on the cube: closed range and cohomology

On the cube `Q = (0, ½)ⁿ` (`Feec.Models.Cube.FEM.cubeDomain n`) the analytic BGG theorem for
Hilbert complexes (`Feec.BGG.HilbertData.bggVerdict`, Theorem 6 of [ArnoldHu2021]) applies to the
BGG diagrams of differential forms of `Feec.FiniteElement.FormBGG` and
`Feec.FiniteElement.FormBGGElasticity` with no hypothesis left:

* **the regular decompositions**: `HΛ(Q)` has the `H¹`-regular decompositions from `0` on
  (`deRham_hasRegularDecomposition_cube`, from
  `Feec.Models.Cube.Sobolev.deRham_hasRegularDecomposition_Q`, Gaffney's identity on the torus), so
  the Hessian diagram (`J = 0`), the elasticity diagram (`n = 3`, `J = 1`) and the div–div diagram
  (`J = n − 1`) have the regular decompositions of [ArnoldHu2021], §2, Theorem 3;
* **the cohomology of the rows is that of a point**: `dim Hᵏ(HΛ(Q)) = [k = 0]`
  (`Feec.Models.Cube.FEM.finrank_cohomology`), and `dim Hᵏ(HΛ(Q) ⊗ ℝⁿ) = n [k = 0]`
  (`Feec.HilbertComplex.finrank_pi_cohomology`).

So **the Hessian, elasticity and div–div complexes of `Q` have closed range in every degree and
finite-dimensional cohomology, concentrated in degree `0`**: `S` induces zero on cohomology, so
(27) of [ArnoldHu2021], Theorem 6 is an equality
(`Feec.BGG.HilbertData.finrank_bgg_homology_eq_ite`), and `dim H⁰ = n + 1` for the Hessian and
div–div complexes (the dimension of the affine functions, resp. of the fields `a + b x`), `6` for
the elasticity complex on `Q ⊆ ℝ³` (the dimension of the rigid motions), `Hⁱ = 0` for `i ≠ 0`
(`hessianBGG_Q`, `elasticityBGG_Q`, `divDivBGG_Q`). These are the dimension counts only: the
cohomology is not identified with the affine functions, the rigid motions or the fields `a + b x`.

## Main results

* `deRham_hasRegularDecomposition_cube`, `finrank_formRow_cohomology`,
  `finrank_vecRow_cohomology`.
* **`hessianBGG_Q`**, **`elasticityBGG_Q`**, **`divDivBGG_Q`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2 (Theorem 3), §4.1, Theorem 6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (closed range, harmonic forms and cohomology)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.FormBGG

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex
open Feec.Models.Cube.FEM (cubeDomain isOpen_cubeDomain cubeDomain_eq_Q)

variable {n : ℕ}

/-- **The `H¹`-regular decompositions of `HΛ(Q)`** from `0` on, on `cubeDomain n`. -/
theorem deRham_hasRegularDecomposition_cube :
    (deRham ℝ n).HasRegularDecomposition (cubeDomain n) 0 :=
  (cubeDomain_eq_Q n) ▸ Sobolev.deRham_hasRegularDecomposition_Q

instance finiteDimensional_formRow_cohomology (k : ℤ) :
    FiniteDimensional ℝ ((formRow n (isOpen_cubeDomain n)).cohomology k) :=
  ((FEM.complex n).cohomologyEquivHarmonic (FEM.closedRangeAt k)).symm.finiteDimensional

/-- `dim Hᵏ(HΛ(Q)) = [k = 0]`. -/
theorem finrank_formRow_cohomology (k : ℤ) :
    Module.finrank ℝ ((formRow n (isOpen_cubeDomain n)).cohomology k) = if k = 0 then 1 else 0 :=
  FEM.finrank_cohomology k

/-- `dim Hᵏ(HΛ(Q) ⊗ ℝⁿ) = n [k = 0]`. -/
theorem finrank_vecRow_cohomology (k : ℤ) :
    Module.finrank ℝ ((vecRow n (isOpen_cubeDomain n)).cohomology k) = if k = 0 then n else 0 := by
  rw [finrank_pi_cohomology, finrank_formRow_cohomology, Fintype.card_fin]
  split_ifs <;> simp

/-- **The Hessian complex of forms on the cube** `Q = (0, ½)ⁿ` ([ArnoldHu2021], §4.1,
Theorem 6): the BGG complex `bgg 0` of the domain complexes of `HΛ(Q)` over `HΛ(Q) ⊗ ℝⁿ` has
closed range and finite-dimensional cohomology (`Feec.BGG.HilbertData.BGGVerdict`), of dimension
`n + 1` in degree `0` and `0` in the other degrees. -/
theorem hessianBGG_Q (i : ℤ) :
    (hessianFormData (isOpen_cubeDomain n)).BGGVerdict 0 i ∧
      Module.finrank ℝ (((hessianFormData (isOpen_cubeDomain n)).domainData.bgg 0).homology i) =
        if i = 0 then n + 1 else 0 := by
  set D := hessianFormData (isOpen_cubeDomain n)
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := finiteDimensional_formRow_cohomology
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow n (isOpen_cubeDomain n)).cohomology k))
  have hS := hessianFormData_antilipschitz (isOpen_cubeDomain n)
  have htop := hessianFormData_regularDecomposition (isOpen_cubeDomain n)
    deRham_hasRegularDecomposition_cube
  refine ⟨D.bggVerdict hS htop i, ?_⟩
  rw [D.finrank_bgg_homology_eq_ite hS htop finrank_formRow_cohomology finrank_vecRow_cohomology,
    Nat.add_comm]

/-- **The elasticity complex of forms on the cube** `Q = (0, ½)³` ([ArnoldHu2021], §4.1,
Theorem 6): the BGG complex `bgg 1` of `HΛ(Q) ⊗ ℝ³` over itself has closed range and
finite-dimensional cohomology, of dimension `6` in degree `0` and `0` in the other degrees. -/
theorem elasticityBGG_Q (i : ℤ) :
    (elasticityFormData (isOpen_cubeDomain 3)).BGGVerdict 1 i ∧
      Module.finrank ℝ (((elasticityFormData (isOpen_cubeDomain 3)).domainData.bgg 1).homology i) =
        if i = 0 then 6 else 0 := by
  set D := elasticityFormData (isOpen_cubeDomain 3)
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 (isOpen_cubeDomain 3)).cohomology k))
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 (isOpen_cubeDomain 3)).cohomology k))
  have hS := elasticityFormData_antilipschitz (isOpen_cubeDomain 3)
  have htop := elasticityFormData_regularDecomposition (isOpen_cubeDomain 3)
    (deRham_hasRegularDecomposition_cube.mono zero_le_one)
  exact ⟨D.bggVerdict hS htop i,
    D.finrank_bgg_homology_eq_ite hS htop finrank_vecRow_cohomology finrank_vecRow_cohomology i⟩

/-- **The div–div complex of forms on the cube** `Q = (0, ½)ⁿ`, `n ≥ 1` ([ArnoldHu2021], §4.1,
Theorem 6): the BGG complex `bgg (n - 1)` of `HΛ(Q) ⊗ ℝⁿ` over `HΛ(Q)` has closed range and
finite-dimensional cohomology, of dimension `n + 1` in degree `0` and `0` in the other degrees. -/
theorem divDivBGG_Q [NeZero n] (i : ℤ) :
    (divDivFormData (isOpen_cubeDomain n)).BGGVerdict ((n : ℤ) - 1) i ∧
      Module.finrank ℝ
        (((divDivFormData (isOpen_cubeDomain n)).domainData.bgg ((n : ℤ) - 1)).homology i) =
          if i = 0 then n + 1 else 0 := by
  set D := divDivFormData (isOpen_cubeDomain n)
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := finiteDimensional_formRow_cohomology
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow n (isOpen_cubeDomain n)).cohomology k))
  have hn := NeZero.pos n
  have hS := divDivFormData_antilipschitz (isOpen_cubeDomain n)
  have htop := divDivFormData_regularDecomposition (isOpen_cubeDomain n)
    ((deRham_hasRegularDecomposition_cube (n := n)).mono (by omega))
  exact ⟨D.bggVerdict hS htop i,
    D.finrank_bgg_homology_eq_ite hS htop finrank_vecRow_cohomology finrank_formRow_cohomology i⟩

end Feec.Models.Cube.FormBGG
