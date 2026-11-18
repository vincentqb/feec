module

public import Solution.Mesh
public import Feec.Models.StarShaped.PolyFiniteElement

/-!
# The smooth classes of the challenge are those of `Feec`

`IsCsForm Ω s j L x` (resp. `IsCsFormMin`) is `Feec.Models.StarShaped.StarDomain.IsCsForm`
(resp. `IsCsFormMin`) of the star domain of `Ω` (`isCsForm_iff`, `isCsFormMin_iff`): the form
field `w` is a `j`-form, and `x` is the `L²` class of `w` iff its coefficients agree with those
of `w` almost everywhere (`Feec.FiniteElement.coeFn_formL2`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5, §4, §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.ExteriorFibre

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

theorem isCsForm_iff {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) (s : ℕ) (j : ℤ) (L : ℝ)
    (x : L2Form Ω j) : IsCsForm Ω s j L x ↔ (starDomainOf hΩ).IsCsForm s j L x := by
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

theorem isCsFormMin_iff {Ω : Set (Fin n → ℝ)} (hΩ : IsStarShapedBall Ω) (s : ℕ) (j : ℤ) (L : ℝ)
    (x : L2Form Ω j) : IsCsFormMin Ω s j L x ↔ (starDomainOf hΩ).IsCsFormMin s j L x := by
  unfold IsCsFormMin Feec.Models.StarShaped.StarDomain.IsCsFormMin
  by_cases hj : j < 0
  · simp [hj]
  · simp only [hj, false_or]
    constructor
    · rintro ⟨w, hw, hdeg, h0, h1, h2, hx⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg (not_lt.1 hj)⟩
      exact ⟨k, hk, w, hw, (isDeg_iff hk w).2 hdeg, h0, h1, h2,
        (eq_formL2_iff _ _ x ⟨w, hw.continuous⟩).2 hx⟩
    · rintro ⟨k, hk, w, hw, hdeg, h0, h1, h2, hx⟩
      exact ⟨w, hw, (isDeg_iff hk w).1 hdeg, h0, h1, h2, (eq_formL2_iff _ _ x _).1 hx⟩

end FEEC
