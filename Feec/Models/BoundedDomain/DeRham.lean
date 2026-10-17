module

public import Feec.Domain.Operators

/-!
# The `L²` de Rham complex of `ℝ³` on an open set

`0 → L²(Ω) --grad--> L²(Ω; 𝕜³) --curl--> L²(Ω; 𝕜³) --div--> L²(Ω) → 0` as a complex of
constant-coefficient operators indexed by `ℤ` (`deRham3`), so that on every open `Ω ⊆ ℝ³` it has
the two boundary-condition families of `Feec.Domain.ConstCoeffComplex`:

* the minimal complex `H̊¹ → H̊(curl) → H̊(div) → L²` (`deRham3.minimalComplex`),
* the maximal complex `H¹ → H(curl) → H(div) → L²` (`deRham3.maximalComplex`),

and each is the dual of the other through the formal adjoints `gradᵗ = -div`, `curlᵗ = curl`,
`divᵗ = -grad` (`Feec.Domain.ConstCoeffComplex.dual_minimalComplex_d`,
`Feec.Domain.ConstCoeffComplex.dual_maximalComplex_d`).

## References

* [Arnold2018], §6.2 (the `L²` de Rham complex and its two boundary-condition families)
-/

@[expose] public noncomputable section

open Feec.Domain

namespace Feec.Models.BoundedDomain

/-- The component index types of the de Rham complex of `ℝ³` (scalars as `Fin 1`, vectors as
`Fin 1 × Fin 3`). -/
def deRhamIdx : ℤ → Type
  | 0 => Fin 1
  | 1 => Fin 1 × Fin 3
  | 2 => Fin 1 × Fin 3
  | 3 => Fin 1
  | _ => Empty

instance instFintypeDeRhamIdx : ∀ k, Fintype (deRhamIdx k)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | 1 => inferInstanceAs (Fintype (Fin 1 × Fin 3))
  | 2 => inferInstanceAs (Fintype (Fin 1 × Fin 3))
  | 3 => inferInstanceAs (Fintype (Fin 1))
  | (_ : ℤ) => by
      unfold deRhamIdx
      split <;> infer_instance

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The zero operator between any component types. -/
def zeroOp (ι κ : Type*) : ConstCoeffOp (Fin 3 → ℝ) 𝕜 ι κ := ⟨fun _ _ => []⟩

theorem zeroOp_apply {ι κ : Type*} [Fintype ι] (f : ι → (Fin 3 → ℝ) → 𝕜) :
    (zeroOp 𝕜 ι κ).apply f = 0 := by
  funext j x
  simp [zeroOp, ConstCoeffOp.apply, ConstCoeffOp.applyEntry]

/-- The operators of the de Rham complex: `grad`, `curl`, `div`, and `0` elsewhere. -/
def deRhamOp : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (deRhamIdx k) (deRhamIdx (k + 1))
  | 0 => gradOp 3 1
  | 1 => curlOp 1
  | 2 => divOp 3 1
  | _ => zeroOp 𝕜 _ _

theorem deRhamIdx_eq_empty {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    deRhamIdx k = Empty :=
  deRhamIdx.eq_5 k h0 h1 h2 h3

theorem isEmpty_deRhamIdx {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    IsEmpty (deRhamIdx k) := by
  rw [deRhamIdx_eq_empty h0 h1 h2 h3]; infer_instance

/-- `curl ∘ grad = 0`, `div ∘ curl = 0`. -/
theorem deRhamOp_comp (k : ℤ) : (deRhamOp 𝕜 k).IsComplexPair (deRhamOp 𝕜 (k + 1)) := by
  intro f hf
  by_cases h0 : k = 0
  · subst h0
    exact isComplexPair_grad_curl f hf
  by_cases h1 : k = 1
  · subst h1
    exact isComplexPair_curl_div f hf
  by_cases hneg : k < 0
  · -- the source is empty: `A k f = 0`
    have : IsEmpty (deRhamIdx k) := isEmpty_deRhamIdx (by omega) (by omega) (by omega) (by omega)
    have e : (deRhamOp 𝕜 k).apply f = 0 := by
      funext j x
      simp [ConstCoeffOp.apply]
    rw [e]
    exact (deRhamOp 𝕜 (k + 1)).apply_zero
  · -- the target of the second operator is empty
    have : IsEmpty (deRhamIdx (k + 1 + 1)) :=
      isEmpty_deRhamIdx (by omega) (by omega) (by omega) (by omega)
    funext j
    exact isEmptyElim j

/-- **The `L²` de Rham complex of `ℝ³`** as a complex of constant-coefficient operators; its
minimal and maximal realizations on an open `Ω` are the two boundary-condition families,
dual to each other. -/
def deRham3 : ConstCoeffComplex (Fin 3 → ℝ) 𝕜 where
  ι := deRhamIdx
  A := deRhamOp 𝕜
  comp := deRhamOp_comp 𝕜

variable {𝕜}

/-- On an open `Ω`: `H̊¹ → H̊(curl) → H̊(div) → L²`, dual to `H¹ → H(curl) → H(div) → L²`. -/
theorem deRham3_dual_minimal {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) (k : ℤ) :
    ((deRham3 𝕜).minimalComplex hΩ).dual.d (k + 1) k = (deRhamOp 𝕜 k).formalAdj.maximal Ω :=
  (deRham3 𝕜).dual_minimalComplex_d hΩ k

theorem deRham3_dual_maximal {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) (k : ℤ) :
    ((deRham3 𝕜).maximalComplex hΩ).dual.d (k + 1) k = (deRhamOp 𝕜 k).formalAdj.minimal Ω :=
  (deRham3 𝕜).dual_maximalComplex_d hΩ k

end Feec.Models.BoundedDomain
