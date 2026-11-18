module

public import Solution.Poly
public import Feec.FiniteElement.LocalDof

/-!
# The bridge for the degrees of freedom

The moment `faceMoment` of the challenge is `Feec.FiniteElement.faceMoment` (`faceMoment_eq`):
the integrand is the top coefficient of the wedge `Feec.ExteriorFibre.wedgeForm` of the face trace
`Feec.FiniteElement.faceTrace` with the test form, the value `covEval α v` of a covector on the
edge vectors of the face being the coefficient of the fibre pullback
(`covEval_eq_pullback_apply`, through `Feec.ExteriorFibre.wedgeProd_apply_eq_det_submatrix`).
Unisolvence is then `Feec.FiniteElement.eq_zero_of_faceMoment_eq_zero_simplex`,
`eq_zero_of_faceMoment_eq_zero_minus_simplex` and the counts
`Feec.FiniteElement.PolyKind.finrank_form_eq_sum` (`unisolvent_of_feec`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4 (Theorems 4.10, 4.14)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace FEEC

variable {n : ℕ}

/-- **The value of a covector on the columns `t` of `B` is the `t`-coefficient of its pullback
by `B`.** -/
theorem covEval_eq_pullback_apply {m : ℕ} (B : Fin n → Fin m → ℝ) (α : Finset (Fin n) → ℝ)
    (t : Finset (Fin m)) :
    covEval α (fun j i => B i (t.orderEmbOfFin rfl j)) = Feec.ExteriorFibre.pullback B α t := by
  rw [Feec.ExteriorFibre.pullback_apply, covEval]
  refine sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · rw [Feec.ExteriorFibre.wedgeProd_apply_eq_det_submatrix B hs rfl]
  · rw [Feec.ExteriorFibre.isDeg_wedgeProd B s t (Ne.symm hs), mul_zero]

/-- **The moment of the challenge is `Feec`'s.** -/
theorem faceMoment_eq (p : Fin (n + 1) → Fin n → ℝ) {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1))
    (η : FormField m) (w : FormField n) :
    faceMoment p e η w = Feec.FiniteElement.faceMoment p e η w := by
  rw [Feec.FiniteElement.faceMoment_eq_integral, faceMoment]
  have hS : {y : Fin m → ℝ | (∀ l, 0 ≤ y l) ∧ ∑ l, y l ≤ 1} = Feec.FiniteElement.refSimplex m :=
    Set.ext fun y => Feec.FiniteElement.mem_refSimplex_iff.symm
  rw [hS]
  refine setIntegral_congr_fun (Feec.FiniteElement.measurableSet_refSimplex m) fun y _ => ?_
  simp only [Feec.FiniteElement.wedgeField, Feec.ExteriorFibre.wedgeForm_apply, powerset_univ,
    ← compl_eq_univ_sdiff, Feec.FiniteElement.faceTrace_apply,
    Feec.FiniteElement.affinePullback_apply]
  refine sum_congr rfl fun s _ => ?_
  have hφ : (fun i => p (e 0) i + ∑ l, y l * (p (e l.succ) i - p (e 0) i)) =
      Feec.FiniteElement.affine (Feec.FiniteElement.simplexMatrix (p ∘ e)) (p (e 0)) y := by
    funext i
    simp only [Feec.FiniteElement.affine_apply, Feec.FiniteElement.simplexMatrix,
      Function.comp_apply, mul_comm (y _)]
    ring
  rw [hφ, ← covEval_eq_pullback_apply]
  rfl

theorem unisolvent_of_feec (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (∀ w ∈ (polyForm ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyFormMinus ℝ m (r + k - m) (m - k)).map evalForm,
        faceMoment T.points e η w = 0) → w = 0) ∧
    (∀ w ∈ (polyFormMinus ℝ n r k).map evalForm, (∀ m (e : Fin (m + 1) ↪o Fin (n + 1)), k ≤ m →
      m < r + k → ∀ η ∈ (polyForm ℝ m (r + k - m - 1) (m - k)).map evalForm,
        faceMoment T.points e η w = 0) → w = 0) ∧
    Module.finrank ℝ (polyForm ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyFormMinus ℝ m (r + k - m) (m - k)) else 0) ∧
    Module.finrank ℝ (polyFormMinus ℝ n r k) = ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) *
      (if k ≤ m ∧ m < r + k then Module.finrank ℝ (polyForm ℝ m (r + k - m - 1) (m - k))
        else 0) := by
  have hp := Feec.FiniteElement.isUnit_det_edgeMatrix T
  refine ⟨fun w hw h => ?_, fun w hw h => ?_, ?_, ?_⟩
  · refine Feec.FiniteElement.eq_zero_of_faceMoment_eq_zero_simplex hp hr k
      (by rwa [Feec.FiniteElement.polySpace, ← polyForm_eq, ← evalForm_eq]) fun m e η hη => ?_
    rw [← faceMoment_eq]
    unfold Feec.FiniteElement.testSpace at hη
    split_ifs at hη with hm
    · exact h m e hm.1 hm.2 η (by
        rwa [Feec.FiniteElement.polyMinusSpace, ← polyFormMinus_eq, ← evalForm_eq] at hη)
    · rw [(Submodule.mem_bot ℝ).1 hη]
      simp [faceMoment, covEval]
  · refine Feec.FiniteElement.eq_zero_of_faceMoment_eq_zero_minus_simplex hp k
      (by rwa [Feec.FiniteElement.polyMinusSpace, ← polyFormMinus_eq, ← evalForm_eq])
      fun m e η hη => ?_
    rw [← faceMoment_eq]
    unfold Feec.FiniteElement.testSpaceMinus at hη
    split_ifs at hη with hm
    · exact h m e hm.1 hm.2 η (by
        rwa [Feec.FiniteElement.polySpace, ← polyForm_eq, ← evalForm_eq] at hη)
    · rw [(Submodule.mem_bot ℝ).1 hη]
      simp [faceMoment, covEval]
  · rw [polyForm_eq, ← Feec.FiniteElement.PolyKind.form_full,
      Feec.FiniteElement.PolyKind.finrank_form_eq_sum _ hr]
    refine sum_congr rfl fun m _ => congrArg _ ?_
    by_cases h : k ≤ m ∧ m < r + k
    · rw [Feec.FiniteElement.PolyKind.testForm_full h, ← polyFormMinus_eq]
      simp only [h, and_self, ↓reduceIte]
    · rw [Feec.FiniteElement.PolyKind.testForm_eq_bot _ h, finrank_bot]
      simp only [h, ↓reduceIte]
  · rw [polyFormMinus_eq, ← Feec.FiniteElement.PolyKind.form_trimmed,
      Feec.FiniteElement.PolyKind.finrank_form_eq_sum _ hr]
    refine sum_congr rfl fun m _ => congrArg _ ?_
    by_cases h : k ≤ m ∧ m < r + k
    · rw [Feec.FiniteElement.PolyKind.testForm_trimmed h, ← polyForm_eq]
      simp only [h, and_self, ↓reduceIte]
    · rw [Feec.FiniteElement.PolyKind.testForm_eq_bot _ h, finrank_bot]
      simp only [h, ↓reduceIte]

end FEEC
