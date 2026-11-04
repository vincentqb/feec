module

public import Feec.Domain.FormPullback

/-!
# Regression test: the pullback along affine maps for every constant-coefficient operator

The `L²` statements of `Feec.Domain.FormPullback` (`fieldPull_mem_testGraph`,
`fieldPull_mem_graph_minimal`, `fieldPull_mem_minimal_domain`, `minimal_fieldPull`,
`testField_push_formalAdj`, `fieldPull_mem_maximal_domain`) were stated for the exterior
derivative `d` under `IsDIntertwining A C`, degree by degree; they now hold for every
constant-coefficient operator with a classical intertwining (`IsPullIntertwining`), and
`IsDIntertwining.isPullIntertwining` gives back `d`. `ConstCoeffComplex.maximalComplex_comm` took
one domain; it now takes two. The theorems below state the old results verbatim and derive them
from the new ones.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

public section

namespace FeecCheck.AffineTransport

open Feec Feec.Domain MeasureTheory
open scoped InnerProductSpace ContDiff

section Intertwining

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {C : ∀ k : ℤ, formIdx n k → formIdx n k → ℝ}
  (hC : IsDIntertwining A C) (hA : IsUnit A.det) (b : Fin n → ℝ) {Ω Ω' : Set (Fin n → ℝ)}
  (hΩo : IsOpen Ω) (hΩo' : IsOpen Ω') (hT : affMap A b ⁻¹' Ω' = Ω)
include hC

/-- The earlier `Domain.fieldPull_mem_testGraph`. -/
theorem fieldPull_mem_testGraph_old (k : ℤ)
    {p : L2F ℝ Ω' (formIdx n k) × L2F ℝ Ω' (formIdx n (k + 1))}
    (hp : p ∈ (extDerivOp ℝ n k).testGraph Ω') :
    (fieldPull hA b hΩo'.measurableSet hT (C k) p.1,
      fieldPull hA b hΩo'.measurableSet hT (C (k + 1)) p.2) ∈
        (extDerivOp ℝ n k).testGraph Ω :=
  fieldPull_mem_testGraph (hC.isPullIntertwining k) hA b hΩo' hT hp

include hΩo in
/-- The earlier `Domain.fieldPull_mem_graph_minimal`. -/
theorem fieldPull_mem_graph_minimal_old (k : ℤ)
    {p : L2F ℝ Ω' (formIdx n k) × L2F ℝ Ω' (formIdx n (k + 1))}
    (hp : p ∈ ((extDerivOp ℝ n k).minimal Ω').graph) :
    (fieldPull hA b hΩo'.measurableSet hT (C k) p.1,
      fieldPull hA b hΩo'.measurableSet hT (C (k + 1)) p.2) ∈
        ((extDerivOp ℝ n k).minimal Ω).graph :=
  fieldPull_mem_graph_minimal (hC.isPullIntertwining k) hA b hΩo hΩo' hT hp

include hΩo in
/-- The earlier `Domain.fieldPull_mem_minimal_domain`. -/
theorem fieldPull_mem_minimal_domain_old (k : ℤ) (u : ((extDerivOp ℝ n k).minimal Ω').domain) :
    fieldPull hA b hΩo'.measurableSet hT (C k) u ∈ ((extDerivOp ℝ n k).minimal Ω).domain :=
  fieldPull_mem_minimal_domain (hC.isPullIntertwining k) hA b hΩo hΩo' hT u

include hΩo in
/-- The earlier `Domain.minimal_fieldPull`. -/
theorem minimal_fieldPull_old (k : ℤ) (u : ((extDerivOp ℝ n k).minimal Ω').domain) :
    (extDerivOp ℝ n k).minimal Ω ⟨_, fieldPull_mem_minimal_domain_old hC hA b hΩo hΩo' hT k u⟩ =
      fieldPull hA b hΩo'.measurableSet hT (C (k + 1)) ((extDerivOp ℝ n k).minimal Ω' u) :=
  minimal_fieldPull (hC.isPullIntertwining k) hA b hΩo hΩo' hT u

include hΩo' in
/-- The earlier `Domain.testField_push_formalAdj`. -/
theorem testField_push_formalAdj_old (k : ℤ) {ψ : formIdx n (k + 1) → (Fin n → ℝ) → ℝ}
    (hψ : IsTestField Ω ψ) :
    testField ((extDerivOp ℝ n k).formalAdj.isTestField_apply
        (hψ.pushFun b hA hT (C (k + 1)))) =
      testField (((extDerivOp ℝ n k).formalAdj.isTestField_apply hψ).pushFun b hA hT (C k)) :=
  testField_push_formalAdj (hC.isPullIntertwining k) hA b hΩo' hT hψ

include hΩo in
/-- The earlier `Domain.fieldPull_mem_maximal_domain`. -/
theorem fieldPull_mem_maximal_domain_old (k : ℤ) (u : ((extDerivOp ℝ n k).maximal Ω').domain) :
    ∃ h : fieldPull hA b hΩo'.measurableSet hT (C k) u ∈ ((extDerivOp ℝ n k).maximal Ω).domain,
      (extDerivOp ℝ n k).maximal Ω ⟨_, h⟩ =
        fieldPull hA b hΩo'.measurableSet hT (C (k + 1)) ((extDerivOp ℝ n k).maximal Ω' u) :=
  fieldPull_mem_maximal_domain (hC.isPullIntertwining k) hA b hΩo hΩo' hT u

end Intertwining

section Comm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {Ω : Set E}

/-- The earlier `Domain.ConstCoeffComplex.maximalComplex_comm` (one domain). -/
theorem maximalComplex_comm_old {𝕜₁ 𝕜₂ : Type*} [RCLike 𝕜₁] [RCLike 𝕜₂]
    (hΩ : IsOpen Ω) {C : ConstCoeffComplex E 𝕜₁} {C' : ConstCoeffComplex E 𝕜₂}
    {T : ∀ k, L2F 𝕜₁ Ω (C.ι k) → L2F 𝕜₂ Ω (C'.ι k)}
    (h : ∀ k (x : ((C.A k).maximal Ω).domain), ∃ hx : T k x ∈ ((C'.A k).maximal Ω).domain,
      (C'.A k).maximal Ω ⟨_, hx⟩ = T (k + 1) ((C.A k).maximal Ω x))
    (j k : ℤ) (hjk : (ComplexShape.up ℤ).Rel j k) (x : ((C.maximalComplex hΩ).d j k).domain) :
    ∃ hx : T j x ∈ ((C'.maximalComplex hΩ).d j k).domain,
      (C'.maximalComplex hΩ).d j k ⟨_, hx⟩ = T k ((C.maximalComplex hΩ).d j k x) :=
  ConstCoeffComplex.maximalComplex_comm hΩ hΩ h j k hjk x

end Comm

end FeecCheck.AffineTransport
