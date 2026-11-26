module

public import Feec.Models.Cube.DeRhamIdentPoincare
public import Feec.Models.Cube.FiniteElementMethod

/-!
# The Poincaré hypotheses of the finite element method on the cube are theorems

`HΛ(Q)` and `H̊Λ(Q)` on `Q = (0, ½)ⁿ` have the Poincaré inequality, closed range and compactness in
every degree, with `dim Hᵏ(HΛ(Q)) = [k = 0]` and `dim Hᵏ(H̊Λ(Q)) = [k = n]`.
-/

open scoped InnerProductSpace Topology Finset
open Set MeasureTheory Filter LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.HilbertComplex
open Feec.Models.Cube.DeRhamIdent (Hmax Hmin)

variable (n : ℕ)

theorem cubeDomain_eq_Q : cubeDomain n = Geometry.Q (Fin n) := by
  ext y; simp [cubeDomain, Geometry.mem_Q]

theorem cubeDomain_subset_Q : cubeDomain n ⊆ Geometry.Q (Fin n) := (cubeDomain_eq_Q n).le

variable {n}

/-- **The Poincaré inequality of `HΛ(Q)`**: `‖z‖ ≤ (2π)⁻¹ ‖d z‖` on `D(d) ∩ (𝔷ⁱ)ᗮ`. -/
theorem norm_le_of_mem_orthogonal_cycles {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (z : ((complex n).d i j).domain)
    (hz : (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈ ((complex n).cycles i)ᗮ) :
    ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤ (2 * Real.pi)⁻¹ * ‖(complex n).d i j z‖ := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω)
      (z : (((deRham ℝ n).maximalComplex hΩ).d i j).domain),
      z.1 ∈ (((deRham ℝ n).maximalComplex hΩ).cycles i)ᗮ →
      ‖z.1‖ ≤
        (2 * Real.pi)⁻¹ * ‖((deRham ℝ n).maximalComplex hΩ).d i j z‖ := by
    rintro Ω rfl hΩ z hz
    exact DeRhamIdent.Hmax_norm_le hij z hz
  exact key _ (cubeDomain_eq_Q n) _ z hz

/-- **The Poincaré inequality of `H̊Λ(Q)`**: `‖z‖ ≤ (2π)⁻¹ ‖d z‖` on `D(d) ∩ (𝔷ⁱ)ᗮ`. -/
theorem norm_le_of_mem_orthogonal_cycles_min {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (z : ((complexMin n).d i j).domain)
    (hz : (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈ ((complexMin n).cycles i)ᗮ) :
    ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤ (2 * Real.pi)⁻¹ * ‖(complexMin n).d i j z‖ := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω)
      (z : (((deRham ℝ n).minimalComplex hΩ).d i j).domain),
      z.1 ∈ (((deRham ℝ n).minimalComplex hΩ).cycles i)ᗮ →
      ‖z.1‖ ≤
        (2 * Real.pi)⁻¹ * ‖((deRham ℝ n).minimalComplex hΩ).d i j z‖ := by
    rintro Ω rfl hΩ z hz
    exact DeRhamIdent.Hmin_norm_le hij z hz
  exact key _ (cubeDomain_eq_Q n) _ z hz

/-- **Closed range of `HΛ(Q)` in every degree.** -/
theorem closedRangeAt (j : ℤ) : (complex n).ClosedRangeAt j :=
  ((complex n).closedRangeAt_iff_poincare_of_rel (DeRhamIdent.rel_sub_one j)).2
    ⟨_, norm_le_of_mem_orthogonal_cycles (DeRhamIdent.rel_sub_one j)⟩

/-- **Closed range of `H̊Λ(Q)` in every degree.** -/
theorem closedRangeAt_min (j : ℤ) : (complexMin n).ClosedRangeAt j :=
  ((complexMin n).closedRangeAt_iff_poincare_of_rel (DeRhamIdent.rel_sub_one j)).2
    ⟨_, norm_le_of_mem_orthogonal_cycles_min (DeRhamIdent.rel_sub_one j)⟩

/-- **The compactness property of `HΛ(Q)`**, every degree. -/
theorem hasCompactProperty : (complex n).HasCompactProperty := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω),
      ((deRham ℝ n).maximalComplex hΩ).HasCompactProperty := by
    rintro Ω rfl hΩ
    exact DeRhamIdent.Hmax_hasCompactProperty
  exact key _ (cubeDomain_eq_Q n) _

/-- **The compactness property of `H̊Λ(Q)`**, every degree. -/
theorem hasCompactProperty_min : (complexMin n).HasCompactProperty := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω),
      ((deRham ℝ n).minimalComplex hΩ).HasCompactProperty := by
    rintro Ω rfl hΩ
    exact DeRhamIdent.Hmin_hasCompactProperty
  exact key _ (cubeDomain_eq_Q n) _

/-! ### Harmonic forms and cohomology -/

variable (n) in
/-- The constant function `1` on `Q`, as a `0`-form. -/
abbrev oneForm : L2F ℝ (cubeDomain n) (formIdx n 0) :=
  DeRhamIdent.constForm (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ⟨∅, by simp⟩

variable (n) in
/-- The constant volume form `dx₁ ∧ ⋯ ∧ dxₙ` on `Q`. -/
abbrev volForm : L2F ℝ (cubeDomain n) (formIdx n n) :=
  DeRhamIdent.constForm (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n)
    ⟨Finset.univ, DeRhamIdent.card_univ_eq n⟩

theorem harmonic_eq_bot {k : ℤ} (hk : k ≠ 0) : (complex n).harmonic k = ⊥ := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω),
      ((deRham ℝ n).maximalComplex hΩ).harmonic k = ⊥ := by
    rintro Ω rfl hΩ
    exact DeRhamIdent.Hmax_harmonic_eq_bot hk
  exact key _ (cubeDomain_eq_Q n) _

theorem harmonic_zero_eq_span : (complex n).harmonic 0 = ℝ ∙ oneForm n := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω)
      (hm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω),
      ((deRham ℝ n).maximalComplex hΩ).harmonic 0 =
        ℝ ∙ DeRhamIdent.constForm hm hb (⟨∅, by simp⟩ : formIdx n 0) := by
    rintro Ω rfl hΩ hm hb
    exact DeRhamIdent.Hmax_harmonic_zero
  exact key _ (cubeDomain_eq_Q n) _ _ _

theorem harmonic_eq_bot_min {k : ℤ} (hk : k ≠ n) : (complexMin n).harmonic k = ⊥ := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω),
      ((deRham ℝ n).minimalComplex hΩ).harmonic k = ⊥ := by
    rintro Ω rfl hΩ
    exact DeRhamIdent.Hmin_harmonic_eq_bot hk
  exact key _ (cubeDomain_eq_Q n) _

theorem harmonic_top_eq_span_min : (complexMin n).harmonic n = ℝ ∙ volForm n := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω)
      (hm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω),
      ((deRham ℝ n).minimalComplex hΩ).harmonic n =
        ℝ ∙ DeRhamIdent.constForm hm hb
          (⟨Finset.univ, DeRhamIdent.card_univ_eq n⟩ : formIdx n n) := by
    rintro Ω rfl hΩ hm hb
    exact DeRhamIdent.Hmin_harmonic_top
  exact key _ (cubeDomain_eq_Q n) _ _ _

theorem oneForm_ne_zero : oneForm n ≠ 0 :=
  DeRhamIdent.constForm_ne_zero _ _ (by rw [cubeDomain_eq_Q]; exact DeRhamIdent.volume_Q_ne_zero) _

/-- The harmonic forms of `HΛ(Q)` are finite-dimensional in every degree. -/
instance finiteDimensional_harmonic (k : ℤ) : FiniteDimensional ℝ ((complex n).harmonic k) := by
  by_cases hk : k = 0
  · subst hk; rw [harmonic_zero_eq_span]; infer_instance
  · rw [harmonic_eq_bot hk]; infer_instance

/-- The harmonic forms of `H̊Λ(Q)` are finite-dimensional in every degree. -/
instance finiteDimensional_harmonic_min (k : ℤ) :
    FiniteDimensional ℝ ((complexMin n).harmonic k) := by
  by_cases hk : k = n
  · subst hk; rw [harmonic_top_eq_span_min]; infer_instance
  · rw [harmonic_eq_bot_min hk]; infer_instance

theorem finrank_harmonic (k : ℤ) :
    Module.finrank ℝ ((complex n).harmonic k) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk; rw [harmonic_zero_eq_span, finrank_span_singleton oneForm_ne_zero]; simp
  · rw [harmonic_eq_bot hk, finrank_bot]; simp [hk]

/-- **The cohomology of `HΛ(Q)`**: `Hᵏ ≅ ℝ` for `k = 0`, `0` otherwise. -/
theorem finrank_cohomology (k : ℤ) :
    Module.finrank ℝ ((complex n).cohomology k) = if k = 0 then 1 else 0 := by
  rw [((complex n).cohomologyEquivHarmonic (closedRangeAt k)).finrank_eq, finrank_harmonic]

theorem volForm_ne_zero : volForm n ≠ 0 :=
  DeRhamIdent.constForm_ne_zero _ _ (by rw [cubeDomain_eq_Q]; exact DeRhamIdent.volume_Q_ne_zero) _

theorem finrank_harmonic_min (k : ℤ) :
    Module.finrank ℝ ((complexMin n).harmonic k) = if k = n then 1 else 0 := by
  by_cases hk : k = n
  · subst hk; rw [harmonic_top_eq_span_min, finrank_span_singleton volForm_ne_zero]; simp
  · rw [harmonic_eq_bot_min hk, finrank_bot]; simp [hk]

/-- **The cohomology of `H̊Λ(Q)`**: `Hᵏ ≅ ℝ` for `k = n`, `0` otherwise. -/
theorem finrank_cohomology_min (k : ℤ) :
    Module.finrank ℝ ((complexMin n).cohomology k) = if k = n then 1 else 0 := by
  rw [((complexMin n).cohomologyEquivHarmonic (closedRangeAt_min k)).finrank_eq,
    finrank_harmonic_min]

variable [NeZero n]

namespace SmoothingEstimates

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : SmoothingEstimates n p C)
include hE

end SmoothingEstimates

namespace SmoothingEstimatesMin

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : SmoothingEstimatesMin n p C)
include hE

end SmoothingEstimatesMin

end Feec.Models.Cube.FEM
