module

public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Plancherel's theorem for integrable square-integrable functions

Mathlib defines the Fourier transform on `L²` (`MeasureTheory.Lp.fourierTransformₗᵢ`) by
extension from Schwartz functions, and proves it is an isometry. This file identifies it with
the Fourier integral on `L¹ ∩ L²`: both define the same tempered distribution, and tempered
distributions given by locally integrable functions determine them almost everywhere.

## Main results

* `MeasureTheory.MemLp.fourier_toLp_ae_eq`: for `f ∈ L¹ ∩ L²`, the `L²` Fourier transform of
  `f` is `𝓕 f` almost everywhere;
* **`MeasureTheory.MemLp.integral_norm_fourier_sq`** (Plancherel): `∫ ‖𝓕 f‖² = ∫ ‖f‖²` for
  `f ∈ L¹ ∩ L²`, and `𝓕 f ∈ L²` (`MeasureTheory.MemLp.fourier`).

## References

* [E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*][SteinWeiss1971]
  (the `L²` theory of the Fourier transform)

Bibliography: [references.bib](../../../../docs/references.bib)
-/

open MeasureTheory SchwartzMap FourierTransform

@[expose] public noncomputable section

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace MeasureTheory.MemLp

/-- **On `L¹ ∩ L²` the `L²` Fourier transform is the Fourier integral**, almost everywhere. -/
theorem fourier_toLp_ae_eq {f : V → F} (hf : Integrable f) (hf2 : MemLp f 2) :
    ((𝓕 (hf2.toLp f) : Lp F 2 (volume : Measure V)) : V → F) =ᵐ[volume] 𝓕 f := by
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable one_le_two)
    (VectorFourier.fourierIntegral_continuous (L := innerₗ V) Real.continuous_fourierChar
      continuous_inner hf).locallyIntegrable fun g hg hgc => ?_
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  set φ : 𝓢(V, ℂ) := hc.toSchwartzMap (by fun_prop)
  have hφ : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 : ∀ h : V → F, ∫ x, g x • h x = ∫ x, φ x • h x := fun h => by
    simp_rw [hφ, Complex.coe_smul]
  rw [h1, h1]
  calc ∫ x, φ x • ((𝓕 (hf2.toLp f) : Lp F 2 (volume : Measure V)) : V → F) x
      = Lp.toTemperedDistribution (𝓕 (hf2.toLp f)) φ := (Lp.toTemperedDistribution_apply _ _).symm
    _ = 𝓕 (Lp.toTemperedDistribution (hf2.toLp f)) φ := by
        rw [Lp.fourier_toTemperedDistribution_eq]
    _ = ∫ x, 𝓕 φ x • (hf2.toLp f : V → F) x := by
        rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
    _ = ∫ x, 𝓕 φ x • f x := integral_congr_ae (by
        filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx])
    _ = ∫ x, φ x • 𝓕 f x := by
        rw [SchwartzMap.fourier_coe]
        simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
          Real.continuous_fourierChar continuous_inner (φ.integrable (μ := volume)) hf

/-- `𝓕 f ∈ L²` for `f ∈ L¹ ∩ L²`. -/
theorem fourier {f : V → F} (hf : Integrable f) (hf2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (Lp.memLp _).ae_eq (fourier_toLp_ae_eq hf hf2)

/-- **Plancherel's theorem**: `∫ ‖𝓕 f‖² = ∫ ‖f‖²` for `f ∈ L¹ ∩ L²`. [SteinWeiss1971] -/
theorem integral_norm_fourier_sq {f : V → F} (hf : Integrable f) (hf2 : MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have key : ∀ h : Lp F 2 (volume : Measure V), ∫ x, ‖h x‖ ^ 2 = ‖h‖ ^ 2 := fun h => by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) h
    rw [L2.inner_def] at this
    simp_rw [inner_self_eq_norm_sq_to_K] at this
    rw [← this]
    norm_cast
  rw [← integral_congr_ae ((fourier_toLp_ae_eq hf hf2).mono fun x hx => by simp only [hx] :
      (fun ξ => ‖((𝓕 (hf2.toLp f) : Lp F 2 (volume : Measure V)) : V → F) ξ‖ ^ 2) =ᵐ[volume]
        fun ξ => ‖𝓕 f ξ‖ ^ 2), key, Lp.norm_fourier_eq, ← key]
  exact integral_congr_ae (hf2.coeFn_toLp.mono fun x hx => by simp only [hx])

end MeasureTheory.MemLp
