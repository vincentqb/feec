module

public import Feec.Domain.ConstCoeffOp
public import Feec.HilbertComplex.Short
public import Feec.HilbertComplex.Dual

/-!
# Hilbert complexes of constant-coefficient operators on a domain

A sequence of constant-coefficient operators `A k : 𝕜^{ι k} → 𝕜^{ι (k+1)}` with
`A (k+1) ∘ A k = 0` on smooth fields (`Feec.Domain.ConstCoeffComplex`) gives two Hilbert
complexes on any open `Ω ⊆ E`, of any length:

* the **minimal complex** (`minimalComplex`, "`H̊`", the electric / Dirichlet boundary
  conditions): `d k = (A k)_min`;
* the **maximal complex** (`maximalComplex`, "`H`", no boundary condition): `d k = (A k)_max`;

and the two families are dual to each other: the adjoint of the minimal complex is the maximal
complex of the formal adjoints and vice versa (`dual_minimalComplex_d`, `dual_maximalComplex_d`).
The three-term versions are `ShortHilbertComplex`es (`ConstCoeffOp.shortMinimal`,
`ConstCoeffOp.shortMaximal`).

Instances on `ℝⁿ` (`Feec.Domain.Ops`): grad, the row-wise curl, grad–curl–div, the Hessian; the
bounded-domain models of the thesis are minimal complexes
(`Feec.Models.BoundedDomain.GradCurl`).

## Main results

* `ConstCoeffOp.minimal_mapsTo`, `minimal_comp`: `R((A)_min) ⊆ N((B)_min)` when `B A = 0`
  (closure argument);
* `ConstCoeffOp.maximal_mapsTo`, `maximal_comp`: `R((A)_max) ⊆ N((B)_max)` (distributional
  `Aᵗ Bᵗ = 0`, `formalAdj_comp_testField`);
* `ConstCoeffComplex.minimalComplex`, `maximalComplex`, and their duality.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (the two boundary-condition
  families and their duality)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992] (minimal and maximal ideal boundary
  conditions)
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

/-- `R(A_min) ⊆ D(B_min)` and `B_min A_min = 0`, as a graph membership. -/
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

/-- The formal adjoints compose to zero in `L²(Ω)`: `Aᵗ Bᵗ ψ = 0` for `ψ ∈ C_c^∞(Ω)`. -/
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

/-- `R(A_max) ⊆ D(B_max)` and `B_max A_max = 0`. -/
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
/-- The short **minimal** complex `L²(Ω; 𝕜^ι) --A_min--> L²(Ω; 𝕜^κ) --B_min--> L²(Ω; 𝕜^μ)`
(the `H̊` boundary conditions). -/
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
/-- The short **maximal** complex `L²(Ω; 𝕜^ι) --A_max--> L²(Ω; 𝕜^κ) --B_max--> L²(Ω; 𝕜^μ)`
(no boundary conditions). -/
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
/-- A complex of constant-coefficient operators indexed by `ℤ`: component types `ι k` and
operators `A k : 𝕜^{ι k} → 𝕜^{ι (k+1)}` with `A (k+1) ∘ A k = 0` on smooth fields. Finite
complexes are padded with empty component types. -/
structure ConstCoeffComplex where
  /-- the component index types -/
  ι : ℤ → Type
  [fintype : ∀ k, Fintype (ι k)]
  /-- the operators -/
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

/-- **Duality of the two boundary-condition families**: the dual of the minimal complex is the
maximal complex of the formal adjoints, `(d_min)ᵏ† = (A kᵗ)_max`. -/
theorem dual_minimalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    (C.minimalComplex hΩ).dual.d (k + 1) k = (C.A k).formalAdj.maximal Ω := by
  rw [HilbertComplex.dual_d, minimalComplex_d, ConstCoeffOp.adjoint_minimal]

/-- The dual of the maximal complex is the minimal complex of the formal adjoints. -/
theorem dual_maximalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    (C.maximalComplex hΩ).dual.d (k + 1) k = (C.A k).formalAdj.minimal Ω := by
  rw [HilbertComplex.dual_d, maximalComplex_d, ConstCoeffOp.adjoint_maximal _ hΩ]

end ConstCoeffComplex

end Feec.Domain
