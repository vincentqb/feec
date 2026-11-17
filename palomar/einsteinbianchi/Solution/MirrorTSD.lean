module

public import Solution.MirrorData

/-!
# Real and complex TSD fields on the cube

The mirror complex of `Feec` has complex coefficients; the challenge's fields are real. A complex
matrix field that is symmetric, trace-free and weakly divergence-free (against complex test
fields) has a TSD real part (`reF_mem_tsd`), and a real TSD field is such a complex field
(`ofRealF_tsd`): the test fields split into real and imaginary parts, and the pairing of real
parts is the real part of the complex pairing (`re_inner_ofRealL`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.17

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate ContDiff
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.RowWise (ofRealL reL ofRealF reF ofRealF_apply ofRealL_toL2 fderiv_ofReal
  reL_ofRealL inner_ofRealL)
open Feec.Models.Cube.Geometry (Q)
open Feec.Models.Cube.MirrorWeakSymmetry (re_inner_ofRealL)

theorem toL2_congr {𝕜 : Type*} [RCLike 𝕜] {Ω : Set R3} {f g : R3 → 𝕜} (h : f = g)
    (hf : IsTest Ω f) (hg : IsTest Ω g) : toL2 hf = toL2 hg := by
  subst h; rfl

/-- The gradient of a real test field, as a complex field, is the gradient of the complex test
field. -/
theorem ofRealF_testField_grad {φ : Fin 3 → R3 → ℝ} (hφ : IsTestField (Q (Fin 3)) φ) :
    ofRealF (testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)) =
      testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply
        (φ := fun i x => (φ i x : ℂ)) fun i => (hφ i).ofReal) := by
  refine PiLp.ext fun p => ?_
  rw [ofRealF_apply, testField_apply, testField_apply, ofRealL_toL2]
  refine toL2_congr ?_ _ _
  funext x
  rw [gradOp_apply, gradOp_apply, fderiv_ofReal (hφ p.1).differentiable]
  rfl

/-- `Re ⟪E, ofReal G⟫ = ⟪Re E, G⟫` for fields. -/
theorem re_inner_ofRealF {ι : Type*} [Fintype ι] (E : L2F ℂ (Q (Fin 3)) ι)
    (G : L2F ℝ (Q (Fin 3)) ι) : RCLike.re ⟪E, ofRealF G⟫_ℂ = ⟪reF E, G⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
  exact Finset.sum_congr rfl fun p _ => re_inner_ofRealL _ _

/-- **The real part of a complex TSD field is TSD.** -/
theorem reF_mem_tsd {E : L2F ℂ (Q (Fin 3)) Ix} (hsym : ∀ i j, E (i, j) = E (j, i))
    (htr : ∑ i, E (i, i) = 0)
    (hdiv : ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : IsTestField (Q (Fin 3)) φ,
      ⟪E, testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ)⟫_ℂ = 0) :
    reF E ∈ tsd (Q (Fin 3)) := by
  refine mem_tsd.2 ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · change reL _ (E (i, j)) = reL _ (E (j, i)); rw [hsym]
  · change ∑ i, reL _ (E (i, i)) = 0; rw [← map_sum, htr, map_zero]
  · rw [← re_inner_ofRealF, ofRealF_testField_grad hφ, hdiv _ fun i => (hφ i).ofReal, map_zero]

/-- **A real TSD field is a complex TSD field.** -/
theorem ofRealF_tsd {u : L2F ℝ (Q (Fin 3)) Ix} (hu : u ∈ tsd (Q (Fin 3))) :
    (∀ i j, ofRealF u (i, j) = ofRealF u (j, i)) ∧ ∑ i, ofRealF u (i, i) = 0 ∧
      ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : IsTestField (Q (Fin 3)) φ,
        ⟪ofRealF u, testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ)⟫_ℂ =
          0 := by
  obtain ⟨hsym, htr, hdiv⟩ := mem_tsd.1 hu
  refine ⟨fun i j => by rw [ofRealF_apply, ofRealF_apply, hsym], ?_, fun φ hφ => ?_⟩
  · simp only [ofRealF_apply]; rw [← map_sum, htr, map_zero]
  · have hre : IsTestField (Q (Fin 3)) fun i x => (φ i x).re := fun i =>
      (hφ i).comp_clm Complex.reCLM
    have him : IsTestField (Q (Fin 3)) fun i x => (φ i x).im := fun i =>
      (hφ i).comp_clm Complex.imCLM
    have e : testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ) =
        ofRealF (testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hre)) +
          Complex.I • ofRealF (testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply
            him)) := by
      rw [ofRealF_testField_grad hre, ofRealF_testField_grad him, ← testField_smul, ← testField_add]
      refine testField_congr _ _ ?_
      have hr : ∀ i, ContDiff ℝ ∞ (fun x => ((φ i x).re : ℂ)) := fun i =>
        ((hre i).ofReal (𝕜 := ℂ)).contDiff
      have hi : ∀ i, ContDiff ℝ ∞ (fun x => ((φ i x).im : ℂ)) := fun i =>
        ((him i).ofReal (𝕜 := ℂ)).contDiff
      rw [← ConstCoeffOp.apply_smul _ _ hi, ← ConstCoeffOp.apply_add _ hr
        (g := Complex.I • fun i x => ((φ i x).im : ℂ)) (fun i => (hi i).const_smul Complex.I)]
      congr 1
      funext i x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact (Complex.re_add_im _).symm
    have h1 : ⟪ofRealF u, ofRealF (testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply
        hre))⟫_ℂ = 0 := by
      rw [PiLp.inner_apply]
      simp only [ofRealF_apply, inner_ofRealL]
      rw [← Complex.ofReal_sum, ← PiLp.inner_apply, hdiv _ hre, Complex.ofReal_zero]
    have h2 : ⟪ofRealF u, ofRealF (testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply
        him))⟫_ℂ = 0 := by
      rw [PiLp.inner_apply]
      simp only [ofRealF_apply, inner_ofRealL]
      rw [← Complex.ofReal_sum, ← PiLp.inner_apply, hdiv _ him, Complex.ofReal_zero]
    rw [e, inner_add_right, inner_smul_right, h1, h2, mul_zero, add_zero]

end FEEC
