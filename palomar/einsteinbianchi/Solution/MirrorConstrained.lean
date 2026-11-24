module

public import Solution.MirrorFEM
public import Solution.Constrained

/-!
# The mirror scheme: hypotheses of well-posedness, and constrained initial values

For the mirror discretizations `mirrorQ`: `d̃⁰` is injective (`norm_le_dt0m`), `π¹S⁰` maps `Ṽₕ⁰`
onto `Vₕ¹` (`Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave_S0_surjective`), and some `ψ ∈ Ṽₕ⁰`
has `π¹S⁰ψ = 0`, `d̃ψ ≠ 0` (`mirrorQ_exists_ker`), by dimension: `dim Vₕ¹ < dim Ṽₕ⁰`
(`Feec.Models.Cube.FEM.finrank_polyPartial_lt`, `finrank_famSub`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2, Prop 6.2, §6.3
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4, §5 (degrees of freedom and dimensions)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
  Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)

/-! ### Dimensions -/

/-- `dim ∏ₐ Pₐ = Σₐ dim Pₐ`. -/
theorem finrank_famSub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : Fin 3 → Submodule ℝ V) [∀ a, FiniteDimensional ℝ (P a)] :
    Module.finrank ℝ (famSub P) = ∑ a, Module.finrank ℝ (P a) := by
  let e : famSub P ≃ₗ[ℝ] (∀ a, P a) :=
    { toFun := fun x a => ⟨(x : Wv V) a, x.2 a⟩
      invFun := fun y => ⟨WithLp.toLp 2 fun a => (y a : V), fun a => (y a).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

section FEM

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) (N : ℕ)

/-- **`dim Vₕ¹ < dim Ṽₕ⁰`** for the mirror discretizations. -/
theorem finrank_mirrorQ_V1_lt :
    Module.finrank ℝ (mirrorQ hT hB N).V1 < Module.finrank ℝ (mirrorQ hT hB N).Vt0 := by
  change Module.finrank ℝ ((polyPartial 3 PolySeq.lowestOrder N ∅).V 1) <
    Module.finrank ℝ (famSub fun a => (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 0)
  rw [finrank_famSub]
  exact finrank_polyPartial_lt N

/-- **`d̃⁰` is injective** on the mirror bottom row (the Poincaré inequality `norm_le_dt0m`). -/
theorem mirror_dt0_eq_zero (ψ : 𝒟m.dt0.domain) (h : 𝒟m.dt0 ψ = 0) : (ψ : Wv W0) = 0 := by
  have := norm_le_dt0m ψ
  rw [h, norm_zero] at this
  exact norm_le_zero_iff.1 this

/-- **`π¹S⁰` maps `Ṽₕ⁰` onto `Vₕ¹`** for the mirror discretizations
(`mirrorWave_S0_surjective`). -/
theorem mirrorQ_S0_onto : ∀ μ ∈ (mirrorQ hT hB N).V1, ∃ ψ : 𝒟m.dt0.domain,
    (ψ : Wv W0) ∈ (mirrorQ hT hB N).Vt0 ∧ (mirrorQ hT hB N).π1 (𝒟m.S0 ψ) = μ := by
  intro μ hμ
  obtain ⟨ψ, hψ⟩ := mirrorWave_S0_surjective hT hB N ⟨⟨μ, (mirrorQ hT hB N).le1 hμ⟩, hμ⟩
  exact ⟨e0m.symm (ψ : BU0), fun a => ψ.2 a,
    congrArg (fun x : (mirrorFEM hT hB N).V1h => ((x : TU1) : W1)) hψ⟩

/-- **(C2) restricts the initial values** of the mirror discretizations. -/
theorem mirrorQ_exists_ker : ∃ ψ : 𝒟m.dt0.domain, (ψ : Wv W0) ∈ (mirrorQ hT hB N).Vt0 ∧
    (mirrorQ hT hB N).π1 (𝒟m.S0 ψ) = 0 ∧ 𝒟m.dt0 ψ ≠ 0 := by
  obtain ⟨ψ, hψ, hψ0, hne⟩ :=
    (mirrorQ hT hB N).exists_ker_of_finrank_lt (finrank_mirrorQ_V1_lt hT hB N)
  exact ⟨ψ, hψ, hψ0, fun h => hne (mirror_dt0_eq_zero ψ h)⟩

end FEM

end FEEC
