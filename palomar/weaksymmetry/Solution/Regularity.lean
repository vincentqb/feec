module

public import Solution.Forms
public import Feec.Models.Cube.TangentialRate

/-!
# The smooth classes of the challenge are those of `Feec`

`IsTangentialC2 j L x` is `Feec.Models.Cube.FEM.IsCsFormTr 0 j L x` (`isTangentialC2_iff`): the
form field `w` is a `j`-form, and `x` is the `L²` class of `w` iff its coefficients agree with
those of `w` almost everywhere (`Feec.FiniteElement.coeFn_formL2`).

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

/-- **The challenge's tangential `C²` class is `Feec`'s `IsCsFormTr 0`** on the cube, in the
degrees `j ≥ 0`. -/
theorem isTangentialC2_iff {j : ℤ} (hj : 0 ≤ j) (L : ℝ) (x : L2Form (cube n) j) :
    IsTangentialC2 j L x ↔ Feec.Models.Cube.FEM.IsCsFormTr 0 j L x := by
  unfold IsTangentialC2 Feec.Models.Cube.FEM.IsCsFormTr
  have hj' : ¬ j < 0 := not_lt.2 hj
  simp only [hj', false_or]
  have h2 : ((0 + 2 : ℕ) : WithTop ℕ∞) = 2 := rfl
  constructor
  · rintro ⟨w, hw, hdeg, htan, hL, hx⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg hj⟩
    have hw' : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) w := by rw [h2]; exact hw
    exact ⟨k, hk, w, hw', (isDeg_iff hk w).2 hdeg, htan, fun i hi y hy => hL i hi y hy,
      (eq_formL2_iff _ _ x ⟨w, hw'.continuous⟩).2 hx⟩
  · rintro ⟨k, hk, w, hw, hdeg, htan, hL, hx⟩
    exact ⟨w, by rw [← h2]; exact hw, (isDeg_iff hk w).1 hdeg, htan, fun i hi y hy => hL i hi y hy,
      (eq_formL2_iff _ _ x _).1 hx⟩

end FEEC
