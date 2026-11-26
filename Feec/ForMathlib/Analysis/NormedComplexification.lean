module

public import Feec.ForMathlib.Analysis.Complexification
public import Mathlib.Analysis.Complex.Circle

/-!
# The complexification of a normed space with the Taylor norm

The complexification `E × E` of a normed space `E` over `𝕜 = ℝ` or `ℂ` with the Taylor norm
`‖x + i y‖ = sup_θ ‖cos θ x - sin θ y‖` ([MunozSarantopoulosTonge1999]).

## References

* [G. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces, polynomials and multilinear maps*][MunozSarantopoulosTonge1999]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

/-- The complexification `E × E` of `E` with the Taylor norm, `(x, y)` read as `x + i y`. -/
abbrev NormedComplexification (𝕜 E : Type*) : Type _ := Complexification .taylor 𝕜 E

namespace NormedComplexification

open Complexification

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The Taylor norm `‖x + i y‖ = sup_{|w| = 1} ‖re (w (x + i y))‖`. -/
instance : Norm (NormedComplexification 𝕜 E) := ⟨fun p => ⨆ w : Circle, ‖((w : ℂ) • p).re‖⟩

theorem norm_def (p : NormedComplexification 𝕜 E) : ‖p‖ = ⨆ w : Circle, ‖((w : ℂ) • p).re‖ :=
  rfl

theorem norm_re_smul_le_add (w : Circle) (p : NormedComplexification 𝕜 E) :
    ‖((w : ℂ) • p).re‖ ≤ ‖p.re‖ + ‖p.im‖ := by
  have h1 : |(w : ℂ).re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq w.norm_coe
  have h2 : |(w : ℂ).im| ≤ 1 := (Complex.abs_im_le_norm _).trans_eq w.norm_coe
  rw [re_smul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, RCLike.norm_ofReal]
  exacts [mul_le_of_le_one_left (norm_nonneg _) h1, mul_le_of_le_one_left (norm_nonneg _) h2]

theorem bddAbove_norm_re_smul (p : NormedComplexification 𝕜 E) :
    BddAbove (Set.range fun w : Circle => ‖((w : ℂ) • p).re‖) :=
  ⟨_, Set.forall_mem_range.2 fun w => norm_re_smul_le_add w p⟩

theorem norm_re_smul_le (w : Circle) (p : NormedComplexification 𝕜 E) :
    ‖((w : ℂ) • p).re‖ ≤ ‖p‖ :=
  le_ciSup (bddAbove_norm_re_smul p) w

theorem norm_le_of_forall {p : NormedComplexification 𝕜 E} {C : ℝ}
    (h : ∀ w : Circle, ‖((w : ℂ) • p).re‖ ≤ C) : ‖p‖ ≤ C :=
  ciSup_le h

instance : NormCore .taylor 𝕜 E where
  norm_add_le p q := norm_le_of_forall fun w => by
    rw [smul_add, re_add]
    exact (norm_add_le _ _).trans (add_le_add (norm_re_smul_le w p) (norm_re_smul_le w q))
  norm_smul_le z p := by
    rcases eq_or_ne z 0 with rfl | hz
    · refine norm_le_of_forall fun w => ?_
      simp
    refine norm_le_of_forall fun w => ?_
    set u : Circle := ⟨(w : ℂ) * (z / ‖z‖), by
      simp [Submonoid.unitSphere, norm_ne_zero_iff.2 hz]⟩
    have hwz : (w : ℂ) * z = ((‖z‖ : ℝ) : ℂ) * (u : ℂ) := by
      change _ = _ * ((w : ℂ) * (z / ‖z‖))
      field_simp [norm_ne_zero_iff.2 hz]
    rw [smul_smul, hwz, mul_smul, re_ofReal_smul, norm_smul, RCLike.norm_ofReal, abs_norm]
    exact mul_le_mul_of_nonneg_left (norm_re_smul_le u p) (norm_nonneg _)
  norm_re_le p := by simpa using norm_re_smul_le 1 p
  norm_mk_zero x := le_antisymm (norm_le_of_forall fun w => (norm_re_smul_le_add w _).trans
    (by simp)) (by simpa using norm_re_smul_le 1 (mk x 0 : NormedComplexification 𝕜 E))
  norm_mk_map_le T p := norm_le_of_forall fun w => by
    have e : ((w : ℂ) • mk (T p.re) (T p.im) : NormedComplexification 𝕜 E).re =
        T (((w : ℂ) • p).re) := by simp
    rw [e]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_re_smul_le w p) (norm_nonneg _))

end NormedComplexification
