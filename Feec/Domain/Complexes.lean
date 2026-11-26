module

public import Feec.Domain.ConstCoeffOp
public import Feec.HilbertComplex.Short
public import Feec.HilbertComplex.Dual

/-!
# Hilbert complexes of constant-coefficient operators on a domain

A complex of constant-coefficient operators gives on every open `Ω ⊆ E` a minimal complex
`d k = (A k)_min` and a maximal complex `d k = (A k)_max`; the dual of the minimal complex is the
maximal complex of the formal adjoints, and conversely.

## Main results

* `ConstCoeffComplex.dual_minimalComplex_d`, `ConstCoeffComplex.dual_maximalComplex_d`: duality.
* `ConstCoeffComplex.maximalComplex_comm`: intertwining maps are cochain maps of maximal complexes.
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Domain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {𝕜 : Type*} [RCLike 𝕜] {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {Ω : Set E}

namespace ConstCoeffOp

variable (A : ConstCoeffOp E 𝕜 ι κ) (B : ConstCoeffOp E 𝕜 κ μ)

/-- `B ∘ A = 0` on smooth fields. -/
def IsComplexPair : Prop :=
  ∀ f : ι → E → 𝕜, (∀ i, ContDiff ℝ ∞ (f i)) → B.apply (A.apply f) = 0

variable {A B}

theorem minimal_graph_mem (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) (x : (A.minimal Ω).domain) :
    (A.minimal Ω x, (0 : L2F 𝕜 Ω μ)) ∈ (B.minimal Ω).graph := by
  let S : Set (L2F 𝕜 Ω ι × L2F 𝕜 Ω κ) := {p | (p.2, (0 : L2F 𝕜 Ω μ)) ∈ (B.minimal Ω).graph}
  have hS : IsClosed S :=
    (B.isClosed_minimal hΩ).preimage (continuous_snd.prodMk continuous_const)
  have hsub : (A.testGraph Ω : Set _) ⊆ S := by
    rintro _ ⟨φ, hφ, rfl⟩
    have h := B.testField_mem_graph_minimal hΩ (A.isTestField_apply hφ)
    have h0 : testField (B.isTestField_apply (A.isTestField_apply hφ)) = 0 := by
      rw [testField_congr _ IsTestField.zero (hAB φ fun i => (hφ i).contDiff), testField_zero]
    rw [h0] at h
    exact h
  exact closure_minimal hsub hS (A.mem_closure_minimal hΩ x)

theorem minimal_mapsTo (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) (x : (A.minimal Ω).domain) :
    (A.minimal Ω x : L2F 𝕜 Ω κ) ∈ (B.minimal Ω).domain :=
  LinearPMap.mem_domain_of_mem_graph (minimal_graph_mem hΩ hAB x)

theorem minimal_comp (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) (x : (A.minimal Ω).domain) :
    B.minimal Ω ⟨_, minimal_mapsTo hΩ hAB x⟩ = 0 :=
  ((LinearPMap.image_iff _).2 (minimal_graph_mem hΩ hAB x)).symm

theorem formalAdj_comp_testField (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) {ψ : μ → E → 𝕜}
    (hψ : IsTestField Ω ψ) :
    testField (A.formalAdj.isTestField_apply (B.formalAdj.isTestField_apply hψ)) = 0 := by
  refine L2F.eq_zero_of_forall_inner_testField hΩ _ fun φ hφ => ?_
  have e1 := A.inner_testField_apply_testField hφ (B.formalAdj.isTestField_apply hψ)
  have e2 := B.inner_testField_apply_testField (A.isTestField_apply hφ) hψ
  have h0 : testField (B.isTestField_apply (A.isTestField_apply hφ)) = 0 := by
    rw [testField_congr _ IsTestField.zero (hAB φ fun i => (hφ i).contDiff), testField_zero]
  rw [h0, inner_zero_left] at e2
  rw [← inner_conj_symm, ← e1, ← e2, map_zero]

theorem maximal_mapsTo_and_comp (hΩ : IsOpen Ω) (hAB : IsComplexPair A B)
    (x : (A.maximal Ω).domain) :
    ∃ h : (A.maximal Ω x : L2F 𝕜 Ω κ) ∈ (B.maximal Ω).domain, B.maximal Ω ⟨_, h⟩ = 0 := by
  have key : ∀ ψ : μ → E → 𝕜, ∀ hψ : IsTestField Ω ψ, ⟪(0 : L2F 𝕜 Ω μ), testField hψ⟫_𝕜 =
      ⟪(A.maximal Ω x : L2F 𝕜 Ω κ), testField (B.formalAdj.isTestField_apply hψ)⟫_𝕜 := by
    intro ψ hψ
    rw [A.maximal_inner_testField hΩ x (B.formalAdj.isTestField_apply hψ),
      formalAdj_comp_testField hΩ hAB hψ, inner_zero_left, inner_zero_right]
  have hmem := (B.mem_maximal_domain_iff hΩ).2 ⟨0, key⟩
  exact ⟨hmem, B.maximal_apply_eq hΩ ⟨_, hmem⟩ key⟩

theorem maximal_mapsTo (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) (x : (A.maximal Ω).domain) :
    (A.maximal Ω x : L2F 𝕜 Ω κ) ∈ (B.maximal Ω).domain :=
  (maximal_mapsTo_and_comp hΩ hAB x).1

theorem maximal_comp (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) (x : (A.maximal Ω).domain) :
    B.maximal Ω ⟨_, maximal_mapsTo hΩ hAB x⟩ = 0 :=
  (maximal_mapsTo_and_comp hΩ hAB x).2

variable (A B) in
/-- The short **minimal** complex `A_min`, `B_min` (the `H̊` boundary conditions). -/
def shortMinimal (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) :
    ShortHilbertComplex 𝕜 (L2F 𝕜 Ω ι) (L2F 𝕜 Ω κ) (L2F 𝕜 Ω μ) where
  d₀ := A.minimal Ω
  d₁ := B.minimal Ω
  dense₀ := A.dense_minimal_domain hΩ
  dense₁ := B.dense_minimal_domain hΩ
  closed₀ := A.isClosed_minimal hΩ
  closed₁ := B.isClosed_minimal hΩ
  mapsTo := minimal_mapsTo hΩ hAB
  comp := minimal_comp hΩ hAB

variable (A B) in
/-- The short **maximal** complex `A_max`, `B_max` (no boundary conditions). -/
def shortMaximal (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) :
    ShortHilbertComplex 𝕜 (L2F 𝕜 Ω ι) (L2F 𝕜 Ω κ) (L2F 𝕜 Ω μ) where
  d₀ := A.maximal Ω
  d₁ := B.maximal Ω
  dense₀ := A.dense_maximal_domain hΩ
  dense₁ := B.dense_maximal_domain hΩ
  closed₀ := A.isClosed_maximal hΩ
  closed₁ := B.isClosed_maximal hΩ
  mapsTo := maximal_mapsTo hΩ hAB
  comp := maximal_comp hΩ hAB

@[simp] theorem shortMinimal_d₀ (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) :
    (shortMinimal A B hΩ hAB).d₀ = A.minimal Ω := rfl

@[simp] theorem shortMinimal_d₁ (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) :
    (shortMinimal A B hΩ hAB).d₁ = B.minimal Ω := rfl

@[simp] theorem shortMaximal_d₀ (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) :
    (shortMaximal A B hΩ hAB).d₀ = A.maximal Ω := rfl

@[simp] theorem shortMaximal_d₁ (hΩ : IsOpen Ω) (hAB : IsComplexPair A B) :
    (shortMaximal A B hΩ hAB).d₁ = B.maximal Ω := rfl

end ConstCoeffOp

/-! ## Complexes of any length -/

variable (E 𝕜) in
/-- A complex of constant-coefficient operators `A k : 𝕜^{ι k} → 𝕜^{ι (k+1)}`, indexed by `ℤ`. -/
structure ConstCoeffComplex where
  ι : ℤ → Type
  [fintype : ∀ k, Fintype (ι k)]
  A : ∀ k, ConstCoeffOp E 𝕜 (ι k) (ι (k + 1))
  comp : ∀ k, (A k).IsComplexPair (A (k + 1))

namespace ConstCoeffComplex

attribute [instance] ConstCoeffComplex.fintype

variable (C : ConstCoeffComplex E 𝕜)

/-- The **minimal complex** (`H̊` boundary conditions) on an open `Ω`. -/
def minimalComplex (hΩ : IsOpen Ω) :
    HilbertComplex 𝕜 (ComplexShape.up ℤ) (fun k => L2F 𝕜 Ω (C.ι k)) :=
  HilbertComplex.ofSucc (fun k => (C.A k).minimal Ω) (fun k => (C.A k).dense_minimal_domain hΩ)
    (fun k => (C.A k).isClosed_minimal hΩ) (fun k => ConstCoeffOp.minimal_mapsTo hΩ (C.comp k))
    (fun k => ConstCoeffOp.minimal_comp hΩ (C.comp k))

/-- The **maximal complex** (no boundary conditions) on an open `Ω`. -/
def maximalComplex (hΩ : IsOpen Ω) :
    HilbertComplex 𝕜 (ComplexShape.up ℤ) (fun k => L2F 𝕜 Ω (C.ι k)) :=
  HilbertComplex.ofSucc (fun k => (C.A k).maximal Ω) (fun k => (C.A k).dense_maximal_domain hΩ)
    (fun k => (C.A k).isClosed_maximal hΩ) (fun k => ConstCoeffOp.maximal_mapsTo hΩ (C.comp k))
    (fun k => ConstCoeffOp.maximal_comp hΩ (C.comp k))

theorem minimalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    (C.minimalComplex hΩ).d k (k + 1) = (C.A k).minimal Ω :=
  HilbertComplex.ofSuccD_succ (fun k => (C.A k).minimal Ω) k

theorem maximalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    (C.maximalComplex hΩ).d k (k + 1) = (C.A k).maximal Ω :=
  HilbertComplex.ofSuccD_succ (fun k => (C.A k).maximal Ω) k

/-- **Degreewise intertwining maps are cochain maps of the maximal complexes.** -/
theorem maximalComplex_comm {𝕜₁ 𝕜₂ : Type*} [RCLike 𝕜₁] [RCLike 𝕜₂] {Ω' : Set E}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') {C : ConstCoeffComplex E 𝕜₁} {C' : ConstCoeffComplex E 𝕜₂}
    {T : ∀ k, L2F 𝕜₁ Ω (C.ι k) → L2F 𝕜₂ Ω' (C'.ι k)}
    (h : ∀ k (x : ((C.A k).maximal Ω).domain), ∃ hx : T k x ∈ ((C'.A k).maximal Ω').domain,
      (C'.A k).maximal Ω' ⟨_, hx⟩ = T (k + 1) ((C.A k).maximal Ω x))
    (j k : ℤ) (hjk : (ComplexShape.up ℤ).Rel j k) (x : ((C.maximalComplex hΩ).d j k).domain) :
    ∃ hx : T j x ∈ ((C'.maximalComplex hΩ').d j k).domain,
      (C'.maximalComplex hΩ').d j k ⟨_, hx⟩ = T k ((C.maximalComplex hΩ).d j k x) := by
  obtain rfl : j + 1 = k := hjk
  have hx : (x : L2F 𝕜₁ Ω (C.ι j)) ∈ ((C.A j).maximal Ω).domain := by
    rw [← C.maximalComplex_d hΩ j]; exact x.2
  obtain ⟨h', hv⟩ := h j ⟨_, hx⟩
  have h'' : T j x ∈ ((C'.maximalComplex hΩ').d j (j + 1)).domain := by
    rw [C'.maximalComplex_d hΩ' j]; exact h'
  refine ⟨h'', ((LinearPMap.apply_eq_of_eq (C'.maximalComplex_d hΩ' j) _ ⟨_, h'⟩ rfl).trans
    hv).trans ?_⟩
  exact congrArg _ (LinearPMap.apply_eq_of_eq (C.maximalComplex_d hΩ j) x ⟨_, hx⟩ rfl).symm

/-- **Duality**: the dual of the minimal complex is the maximal complex of the formal adjoints. -/
theorem dual_minimalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    (C.minimalComplex hΩ).dual.d (k + 1) k = (C.A k).formalAdj.maximal Ω := by
  rw [HilbertComplex.dual_d, minimalComplex_d, ConstCoeffOp.adjoint_minimal]

/-- The dual of the maximal complex is the minimal complex of the formal adjoints. -/
theorem dual_maximalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    (C.maximalComplex hΩ).dual.d (k + 1) k = (C.A k).formalAdj.minimal Ω := by
  rw [HilbertComplex.dual_d, maximalComplex_d, ConstCoeffOp.adjoint_maximal _ hΩ]

end ConstCoeffComplex

end Feec.Domain
