module

public import Feec.Models.Cube.DeRhamIdentPoincare
public import Feec.Models.Cube.FiniteElementMethod

/-!
# The Poincaré hypotheses of the finite element method on the cube are theorems

On the cube `Q = (0, ½)ⁿ` of `Feec.Models.Cube.FiniteElementMethod` (`FEM.cubeDomain n`), the
de Rham complexes `FEM.complex n = HΛ(Q)` and `FEM.complexMin n = H̊Λ(Q)` satisfy, in every
dimension and degree (from the identification with the parity classes of the torus de Rham
complex, `Feec.Models.Cube.DeRhamIdent`):

* **the Poincaré inequality** `‖z‖ ≤ (2π)⁻¹ ‖d z‖` on `D(d) ∩ (𝔷ⁱ)ᗮ`, in the exact form of the
  hypotheses `hP`, `hPi`, `hPj` of `FEM.SmoothingEstimates` (`norm_le_of_mem_orthogonal_cycles`,
  `norm_le_of_mem_orthogonal_cycles_min`; with any constant `c_P ≥ (2π)⁻¹`:
  `poincare`, `poincare_min`);
* **closed range** in every degree (`closedRangeAt`, `closedRangeAt_min`);
* **the harmonic forms**: `ℌᵏ(HΛ(Q)) = 0` for `k ≠ 0` and `ℌ⁰(HΛ(Q)) = ℝ · 1`
  (`harmonic_eq_bot`, `harmonic_zero_eq_span`); `ℌᵏ(H̊Λ(Q)) = 0` for `k ≠ n` and
  `ℌⁿ(H̊Λ(Q)) = ℝ · dx₁ ∧ ⋯ ∧ dxₙ` (`harmonic_eq_bot_min`, `harmonic_top_eq_span_min`); they are
  finite-dimensional (instances), and so is the cohomology: `dim Hᵏ(HΛ(Q)) = [k = 0]`
  (`finrank_cohomology`);
* **the compactness property** (`hasCompactProperty`, `hasCompactProperty_min`).

Consequently the finite element results of `Feec.Models.Cube.FiniteElementMethod` hold with the
Poincaré hypotheses discharged: the uniform discrete Poincaré inequality
(`SmoothingEstimates.norm_le_of_forall_inner_eq_zero'`), uniform well-posedness and stability of
the discrete mixed Hodge Laplacian (`SmoothingEstimates.existsUnique_mixed'`,
`SmoothingEstimates.norm_le_of_mixed'`), quasi-optimality and the `O(h)` rate
(`SmoothingEstimates.norm_sub_le_infDist'`, `SmoothingEstimates.norm_sub_le_meshSize'`), and the
vanishing-trace versions (`SmoothingEstimatesMin.norm_le_of_forall_inner_eq_zero'`,
`SmoothingEstimatesMin.existsUnique_mixed'`, `SmoothingEstimatesMin.norm_le_of_mixed'`); the
finite-dimensionality of `ℌ` needed by `SmoothingEstimates.tendsto_harmonicGap` is an instance.
These results keep `FEM.SmoothingEstimates` (resp. `FEM.SmoothingEstimatesMin`) as a hypothesis;
the `O(h)` rates for `C²` solutions of `Feec.Models.Cube.WhitneyRate` with the Poincaré
hypotheses discharged are in `Feec.Models.Cube.DeRhamIdentRate`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (Poincaré inequality), §4.3 (the de Rham complex), Thm 3.8, Thm 3.9
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (harmonic forms and
  cohomology)

Bibliography: [references.bib](../../../docs/references.bib)
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

variable {n}

/-- **The Poincaré inequality of `HΛ(Q)`**: `‖z‖ ≤ (2π)⁻¹ ‖d z‖` for `z ∈ D(d) ∩ (𝔷ⁱ)ᗮ`, in every
degree; the hypothesis `hP` of `FEM.SmoothingEstimates` with `c_P = (2π)⁻¹`. -/
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

/-- **The Poincaré inequality of `H̊Λ(Q)`**: `‖z‖ ≤ (2π)⁻¹ ‖d z‖` for `z ∈ D(d) ∩ (𝔷ⁱ)ᗮ`, in every
degree; the hypothesis `hP` of `FEM.SmoothingEstimatesMin` with `c_P = (2π)⁻¹`. -/
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

/-- The Poincaré inequality of `HΛ(Q)` with any constant `c_P ≥ (2π)⁻¹`. -/
theorem poincare {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) {cP : ℝ}
    (hcP : (2 * Real.pi)⁻¹ ≤ cP) :
    ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖ := fun z hz =>
  (norm_le_of_mem_orthogonal_cycles hij z hz).trans
    (mul_le_mul_of_nonneg_right hcP (norm_nonneg _))

/-- The Poincaré inequality of `H̊Λ(Q)` with any constant `c_P ≥ (2π)⁻¹`. -/
theorem poincare_min {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) {cP : ℝ}
    (hcP : (2 * Real.pi)⁻¹ ≤ cP) :
    ∀ z : ((complexMin n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complexMin n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complexMin n).d i j z‖ := fun z hz =>
  (norm_le_of_mem_orthogonal_cycles_min hij z hz).trans
    (mul_le_mul_of_nonneg_right hcP (norm_nonneg _))

theorem inv_two_pi_le_one : (2 * Real.pi)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by nlinarith [Real.two_le_pi])

/-- **Closed range of `HΛ(Q)` in every degree.** -/
theorem closedRangeAt (j : ℤ) : (complex n).ClosedRangeAt j :=
  ((complex n).closedRangeAt_iff_poincare_of_rel (DeRhamIdent.rel_sub_one j)).2
    ⟨_, norm_le_of_mem_orthogonal_cycles (DeRhamIdent.rel_sub_one j)⟩

/-- **Closed range of `H̊Λ(Q)` in every degree.** -/
theorem closedRangeAt_min (j : ℤ) : (complexMin n).ClosedRangeAt j :=
  ((complexMin n).closedRangeAt_iff_poincare_of_rel (DeRhamIdent.rel_sub_one j)).2
    ⟨_, norm_le_of_mem_orthogonal_cycles_min (DeRhamIdent.rel_sub_one j)⟩

/-- **The compactness property of `HΛ(Q)`** (Rellich and Gaffney on the cube), every degree. -/
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

/-- **`HΛ(Q)` has no harmonic forms in degrees `k ≠ 0`.** -/
theorem harmonic_eq_bot {k : ℤ} (hk : k ≠ 0) : (complex n).harmonic k = ⊥ := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω),
      ((deRham ℝ n).maximalComplex hΩ).harmonic k = ⊥ := by
    rintro Ω rfl hΩ
    exact DeRhamIdent.Hmax_harmonic_eq_bot hk
  exact key _ (cubeDomain_eq_Q n) _

/-- **The harmonic `0`-forms of `HΛ(Q)` are the constants.** -/
theorem harmonic_zero_eq_span : (complex n).harmonic 0 = ℝ ∙ oneForm n := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω)
      (hm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω),
      ((deRham ℝ n).maximalComplex hΩ).harmonic 0 =
        ℝ ∙ DeRhamIdent.constForm hm hb (⟨∅, by simp⟩ : formIdx n 0) := by
    rintro Ω rfl hΩ hm hb
    exact DeRhamIdent.Hmax_harmonic_zero
  exact key _ (cubeDomain_eq_Q n) _ _ _

/-- **`H̊Λ(Q)` has no harmonic forms in degrees `k ≠ n`.** -/
theorem harmonic_eq_bot_min {k : ℤ} (hk : k ≠ n) : (complexMin n).harmonic k = ⊥ := by
  have key : ∀ (Ω : Set (Fin n → ℝ)) (_ : Ω = Geometry.Q (Fin n)) (hΩ : IsOpen Ω),
      ((deRham ℝ n).minimalComplex hΩ).harmonic k = ⊥ := by
    rintro Ω rfl hΩ
    exact DeRhamIdent.Hmin_harmonic_eq_bot hk
  exact key _ (cubeDomain_eq_Q n) _

/-- **The harmonic `n`-forms of `H̊Λ(Q)` are the constant volume forms.** -/
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

theorem volForm_ne_zero : volForm n ≠ 0 :=
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

theorem finrank_harmonic_min (k : ℤ) :
    Module.finrank ℝ ((complexMin n).harmonic k) = if k = n then 1 else 0 := by
  by_cases hk : k = n
  · subst hk; rw [harmonic_top_eq_span_min, finrank_span_singleton volForm_ne_zero]; simp
  · rw [harmonic_eq_bot_min hk, finrank_bot]; simp [hk]

/-- **The cohomology of `HΛ(Q)`**: `Hᵏ ≅ ℝ` for `k = 0`, `0` otherwise. -/
theorem finrank_cohomology (k : ℤ) :
    Module.finrank ℝ ((complex n).cohomology k) = if k = 0 then 1 else 0 := by
  rw [((complex n).cohomologyEquivHarmonic (closedRangeAt k)).finrank_eq, finrank_harmonic]

/-! ### The finite element method with the Poincaré hypotheses discharged -/

variable [NeZero n]

namespace SmoothingEstimates

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : SmoothingEstimates n p C)
include hE

/-- **Uniform discrete Poincaré inequality** on the Freudenthal meshes of the cube, with the
Poincaré constant of `HΛ(Q)`: `‖x‖ ≤ 2 C (2π)⁻¹ ‖d x‖` for `x ∈ Vₕⁱ ⊥ 𝔷ₕⁱ`. -/
theorem norm_le_of_forall_inner_eq_zero' {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitney n N).V i)
    (hxo : ∀ y ∈ (whitney n N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * (2 * Real.pi)⁻¹ *
      ‖(complex n).d i j ⟨x, (whitney n N).le_domain i j hx⟩‖ :=
  hE.norm_le_of_forall_inner_eq_zero hij (norm_le_of_mem_orthogonal_cycles hij) N hx hxo

/-- **Uniform well-posedness of the discrete mixed Hodge Laplacian** on the cube meshes. -/
theorem existsUnique_mixed' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) (f : (whitney n N).V j) :
    ∃! x, (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f :=
  hE.existsUnique_mixed hij hjk le_rfl (poincare hij inv_two_pi_le_one)
    (poincare hjk inv_two_pi_le_one) N f

/-- **Uniform stability of the discrete mixed Hodge Laplacian** on the cube meshes:
`‖xₕ‖ ≤ 64 C² ‖fₕ‖`. -/
theorem norm_le_of_mixed' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) {f : (whitney n N).V j}
    {x : (whitney n N).toHilbertComplex.MixedSpace i j}
    (hx : (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * 1) ^ 2 * ‖f‖ :=
  hE.norm_le_of_mixed hij hjk le_rfl (poincare hij inv_two_pi_le_one)
    (poincare hjk inv_two_pi_le_one) N hx

/-- **Quasi-optimality of the mixed method on the cube meshes**, with the Poincaré constant
`(2π)⁻¹` of `HΛ(Q)`. -/
theorem norm_sub_le_infDist' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complex n).domainSpace i} {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) (N : ℕ) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) *
        (Metric.infDist σ ((whitney n N).domainSub i) + Metric.infDist u ((whitney n N).domainSub j) +
          Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) +
          (hE.proj N).harmonicGap j *
            Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
              ((whitney n N).domainSub j)) :=
  hE.norm_sub_le_infDist hij hjk (norm_le_of_mem_orthogonal_cycles hij)
    (norm_le_of_mem_orthogonal_cycles hjk) hs N

/-- **`O(h)` convergence of the mixed method on the cube meshes** for solutions approximable at
rate `h`, with the Poincaré constant `(2π)⁻¹` of `HΛ(Q)`. -/
theorem norm_sub_le_meshSize' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {f : L2F ℝ (cubeDomain n) (formIdx n j)}
    {σ : (complex n).domainSpace i} {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {K : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((whitney n N).domainSub i) ≤ K * meshSize N)
    (hu : Metric.infDist u ((whitney n N).domainSub j) ≤ K * meshSize N)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) ≤
      K * meshSize N)
    (hB : Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
      ((whitney n N).domainSub j) ≤ K * meshSize N) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
        meshSize N :=
  hE.norm_sub_le_meshSize hij hjk (norm_le_of_mem_orthogonal_cycles hij)
    (norm_le_of_mem_orthogonal_cycles hjk) hs N hσ hu hq hB

end SmoothingEstimates

namespace SmoothingEstimatesMin

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : SmoothingEstimatesMin n p C)
include hE

/-- **Uniform discrete Poincaré inequality** for the Whitney spaces with vanishing boundary DOFs,
with the Poincaré constant of `H̊Λ(Q)`. -/
theorem norm_le_of_forall_inner_eq_zero' {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitneyMin n N).V i)
    (hxo : ∀ y ∈ (whitneyMin n N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * (2 * Real.pi)⁻¹ *
      ‖(complexMin n).d i j ⟨x, (whitneyMin n N).le_domain i j hx⟩‖ :=
  hE.norm_le_of_forall_inner_eq_zero hij (norm_le_of_mem_orthogonal_cycles_min hij) N hx hxo

/-- **Uniform well-posedness of the discrete mixed Hodge Laplacian with vanishing traces.** -/
theorem existsUnique_mixed' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) (f : (whitneyMin n N).V j) :
    ∃! x, (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin n N).toHilbertComplex.mixedRHS i j f :=
  hE.existsUnique_mixed hij hjk le_rfl (poincare_min hij inv_two_pi_le_one)
    (poincare_min hjk inv_two_pi_le_one) N f

/-- **Uniform stability of the discrete mixed problem with vanishing traces**:
`‖xₕ‖ ≤ 64 C² ‖fₕ‖`. -/
theorem norm_le_of_mixed' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) (N : ℕ) {f : (whitneyMin n N).V j}
    {x : (whitneyMin n N).toHilbertComplex.MixedSpace i j}
    (hx : (whitneyMin n N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin n N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * 1) ^ 2 * ‖f‖ :=
  hE.norm_le_of_mixed hij hjk le_rfl (poincare_min hij inv_two_pi_le_one)
    (poincare_min hjk inv_two_pi_le_one) N hx

end SmoothingEstimatesMin

end Feec.Models.Cube.FEM
