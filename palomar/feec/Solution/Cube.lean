module

public import Solution.Rates
public import Solution.Forms
public import Solution.OfFeec
public import Feec.Models.Parallelepiped.StarShaped
public import Feec.Models.Cube.KuhnPieces

/-!
# The Whitney forms on the cube meet the hypotheses of the FEEC theorem

`FEEC.feec_cube` from the finite element theory of `Feec.Models.StarShaped.PolyFiniteElement`
on the cube `(0, ½)ⁿ` with its Freudenthal meshes (`Feec.Models.StarShaped.CubeWitness`) for the
trimmed sequence `P₁⁻Λ` (`Feec.FiniteElement.PolySeq.trimmed 1`, the Whitney forms): the complex
`MeshFamily.poly` with the uniformly bounded smoothed projections
(`MeshFamily.exists_uniform_polyProj`), the graph-norm density
(`MeshFamily.eventually_exists_poly_graph`), the interpolation error
(`MeshFamily.exists_mem_poly_le_of_isCsForm`, a Jackson estimate of order `h`), the closed ranges
from the Poincaré inequality (`CubeWitness.hasPoincare`), the static rate of `Solution.Rates`, and
the affine pieces (`Feec.FiniteElement.PolySeq.exists_piece_of_mem_subcomplex`,
`Feec.Models.Cube.FEM.exists_mem_simplices_points_eq`,
`Feec.FiniteElement.exists_affine_of_mem_polySpace_one`). As in `palomar/fem/Solution.lean`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2, §5.5
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set MeasureTheory LinearPMap

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.StarShaped Feec.Models.Cube Feec.ExteriorFibre

variable {n : ℕ}

theorem isDeg_iff {j : ℤ} {k : ℕ} (hk : (k : ℤ) = j) (w : FormField n) :
    (∀ y, IsDeg k (w y)) ↔ ∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0 := by
  subst hk
  exact forall_congr' fun y => forall_congr' fun t => by
    rw [Ne, Ne, Nat.cast_inj]

theorem eq_formL2_iff {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    {j : ℤ} (x : L2Form Ω j) (w : contForms n) :
    x = formL2 hΩ hb j w ↔ ∀ t : FormIdx n j,
      ⇑(x t) =ᵐ[volume.restrict Ω] fun y => (w : FormField n) y t.1 := by
  constructor
  · rintro rfl t; exact coeFn_formL2 hΩ hb j w t
  · intro h
    refine PiLp.ext fun t => Lp.ext ?_
    exact (h t).trans (coeFn_formL2 hΩ hb j w t).symm

/-- `IsCsForm` of the challenge is `Feec`'s on the cube's star domain. -/
theorem isCsForm_cube (s : ℕ) (j : ℤ) (L : ℝ) (x : L2Form (cube n) j) :
    IsCsForm (cube n) s j L x ↔ (CubeWitness.starDomain n).IsCsForm s j L x := by
  unfold IsCsForm Feec.Models.StarShaped.StarDomain.IsCsForm
  by_cases hj : j < 0
  · simp [hj]
  · simp only [hj, false_or]
    constructor
    · rintro ⟨w, hw, hdeg, h1, h2, hx⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg (not_lt.1 hj)⟩
      exact ⟨k, hk, w, hw, (isDeg_iff hk w).2 hdeg, h1, h2,
        (eq_formL2_iff _ _ x ⟨w, hw.continuous⟩).2 hx⟩
    · rintro ⟨k, hk, w, hw, hdeg, h1, h2, hx⟩
      exact ⟨w, hw, (isDeg_iff hk w).1 hdeg, h1, h2, (eq_formL2_iff _ _ x _).1 hx⟩

/-- The trimmed sequence `P₁⁻Λ` of the Whitney forms. -/
abbrev whitney : PolySeq := PolySeq.trimmed 1 le_rfl

theorem whitney_polyOrderAt (j : ℤ) : PolyOrderAt n whitney 0 j := fun k _ =>
  ⟨polySpace_le_polyMinusSpace le_rfl k, polySpace_le_polyMinusSpace le_rfl (k + 1)⟩

theorem dMax_cube (k : ℤ) : (CubeWitness.starDomain n).complex.d k (k + 1) = dMax (cube n) k := by
  rw [deRham_maximalComplex_d, dMax_eq]; rfl

end FEEC
