module

public import Feec.Models.Cube.TangentialRate
public import Feec.Domain.H1Lipschitz

/-!
# `C²` forms with vanishing tangential traces are of class `H¹`

A form of the class `Feec.Models.Cube.FEM.IsCsFormTr 0 j L` on the cube `Q = (0, ½)ⁿ` (a `C²` form
on `ℝⁿ` whose tangential components vanish on `∂Q`, the values and first derivatives of the form
and of its exterior derivative bounded by `L` on `cl Q`) has `H¹(ℝⁿ)` data with bound `c L`, and
so has its minimal exterior derivative (`IsCsFormTr.exists_h1Data`, from
`Feec.Domain.exists_h1Data_closedBall` applied to the coefficients on `cl Q`, the closed ball of
radius `¼` about the centre); `c` depends only on `n`. So the `C²` classes of the rates of the
methods on the cube lie in their `H¹` classes, and the `C²` rates are corollaries of the `H¹`
ones.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.FiniteElement

variable {n : ℕ}

/-- The closed cube `[0, ½]ⁿ` is the closed ball of radius `¼` of the sup norm about the
centre. -/
theorem closure_cubeDomain_eq_closedBall :
    closure (cubeDomain n) = Metric.closedBall (center n) (1 / 4) := by
  rw [closure_cubeDomain]
  ext y
  rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
  refine ⟨fun hy i => ?_, fun hy i _ => ?_⟩
  · obtain ⟨h0, h1⟩ := hy i (mem_univ i)
    rw [Real.dist_eq, abs_le]; simp only [center]; constructor <;> linarith
  · have := hy i
    rw [Real.dist_eq, abs_le] at this; simp only [center] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The coefficient bounds of a form field from the bounds of `w` and `Dw` on `cl Q`. -/
theorem coeff_bounds {w : FormField n} (hw : ContDiff ℝ 1 w) {L : ℝ}
    (h0 : ∀ y ∈ closure (cubeDomain n), ‖w y‖ ≤ L)
    (h1 : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) (t : Finset (Fin n)) :
    ContDiff ℝ 1 (fun y => w y t) ∧ (∀ y ∈ Metric.closedBall (center n) (1 / 4), |w y t| ≤ L) ∧
      ∀ y ∈ Metric.closedBall (center n) (1 / 4), ‖fderiv ℝ (fun y => w y t) y‖ ≤ L := by
  rw [← closure_cubeDomain_eq_closedBall]
  refine ⟨contDiff_pi.1 hw t, fun y hy => (norm_le_pi_norm (w y) t).trans (h0 y hy),
    fun y hy => ?_⟩
  have hd : HasFDerivAt (fun y => w y t)
      ((ContinuousLinearMap.proj t).comp (fderiv ℝ w y)) y :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset (Fin n) => ℝ) t).hasFDerivAt.comp y
      ((hw.differentiable one_ne_zero) y).hasFDerivAt
  rw [hd.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (h1 y hy)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x t

/-- **A `C¹` form bounded with its derivative on `cl Q` has `H¹(ℝⁿ)` data**, with bound `c L`. -/
theorem exists_h1Data_formL2 (n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ {j : ℤ} {L : ℝ} {w : FormField n}
    (hw : ContDiff ℝ 1 w), 0 ≤ L → (∀ y ∈ closure (cubeDomain n), ‖w y‖ ≤ L) →
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) →
    Nonempty (H1Data (cubeDomain n) (formL2 (isOpen_cubeDomain n).measurableSet
      (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩) (c * L)) := by
  obtain ⟨c, hc, H⟩ := exists_h1Data_closedBall (center n) (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨c, hc, fun {j L w} hw hL0 h0 h1 => ?_⟩
  exact H (isOpen_cubeDomain n).measurableSet (subset_closure.trans
    closure_cubeDomain_eq_closedBall.le) (fun t : formIdx n j => fun y => w y t.1) hL0
    (fun t => (coeff_bounds hw h0 h1 t.1).1) (fun t => (coeff_bounds hw h0 h1 t.1).2.1)
    (fun t => (coeff_bounds hw h0 h1 t.1).2.2)
    (fun t => coeFn_formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) _ _ t)

/-- **`C²` forms with vanishing tangential traces are of class `H¹`**: a form of the class
`IsCsFormTr 0 k L` and its minimal exterior derivative have `H¹(ℝⁿ)` data with bound `c L`. -/
theorem IsCsFormTr.exists_h1Data (n : ℕ) [NeZero n] : ∃ c : ℝ, 0 ≤ c ∧ ∀ {k : ℕ} {L : ℝ}
    {x : L2F ℝ (cubeDomain n) (formIdx n k)}, IsCsFormTr 0 k L x →
    Nonempty (H1Data (cubeDomain n) x (c * L)) ∧
      ∀ h : x ∈ ((complexMin n).d k (k + 1)).domain,
        Nonempty (H1Data (cubeDomain n) ((complexMin n).d k (k + 1) ⟨x, h⟩) (c * L)) := by
  obtain ⟨c, hc, H⟩ := exists_h1Data_formL2 n
  refine ⟨c, hc, fun {k L x} hx => ?_⟩
  rcases hx with hj | ⟨k', hk', w, hw, hdeg, -, hL, he⟩
  · exact absurd hj (by omega)
  obtain rfl : k' = k := by exact_mod_cast hk'
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hdw : ContDiff ℝ 1 (extDeriv w) := contDiff_extDeriv (m := 1) (hw.of_le (by norm_num))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (by
    simpa using (hL 0 (Nat.zero_le _) _ (subset_closure (center_mem_cubeDomain n))).1)
  have b0 : ∀ y ∈ closure (cubeDomain n), ‖w y‖ ≤ L := fun y hy => by
    simpa using (hL 0 (Nat.zero_le _) y hy).1
  have b1 : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L := fun y hy => by
    simpa [norm_iteratedFDeriv_one] using (hL 1 le_rfl y hy).1
  have b0' : ∀ y ∈ closure (cubeDomain n), ‖extDeriv w y‖ ≤ L := fun y hy => by
    simpa using (hL 0 (Nat.zero_le _) y hy).2
  have b1' : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L := fun y hy => by
    simpa [norm_iteratedFDeriv_one] using (hL 1 le_rfl y hy).2
  subst he
  refine ⟨H hw1 hL0 b0 b1, fun h => ?_⟩
  rw [complexMin_d_formL2 k' hw1 hdeg ⟨_, h⟩ rfl]
  exact H hdw hL0 b0' b1'

end Feec.Models.Cube.FEM
