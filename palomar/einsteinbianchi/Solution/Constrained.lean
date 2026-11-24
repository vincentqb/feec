module

public import Solution.CubeMain
public import Solution.WellPosed
public import Feec.Models.Cube.WeakSymmetryDimension

/-!
# The initial values of (6.5) on the cube are constrained

The hypotheses of the well-posedness clause of `FEEC.bggWeakSymmetry` for the electric
discretizations `cubeQ`, and the restriction (C2) imposes on their initial values.

* `cubeQ_S0_onto`: `π¹S⁰` maps `Ṽₕ⁰` onto `Vₕ¹`
  (`Feec.Models.Cube.WeakSymmetry.cubeWave_S0_surjective`: `π¹S⁰` is onto from `H̊Λ⁰(Q)³`, by
  density, and (5.4)).
* `cubeQ_exists_ker`: some `ψ ∈ Ṽₕ⁰` has `π¹S⁰ψ = 0` and `d̃ψ ≠ 0`, so `u₀ = d̃ψ` violates (C2).
  By dimension (`exists_ker_of_finrank_lt`): `dim Vₕ¹ < dim Ṽₕ⁰`
  (`Feec.Models.Cube.FEM.finrank_polyMin_lt`, `Feec.Models.Cube.WeakSymmetry.finrank_tsub`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.2, (5.4), §6.2, Prop 6.2, §6.3, Table 6.1
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4, §5 (degrees of freedom and dimensions)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

namespace WeakSymmetryData.Discretization

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2}

/-- **`π¹S⁰` has a nonzero kernel on `Ṽₕ⁰` when `dim Vₕ¹ < dim Ṽₕ⁰`.** -/
theorem exists_ker_of_finrank_lt (Q : D.Discretization)
    (h : Module.finrank ℝ Q.V1 < Module.finrank ℝ Q.Vt0) :
    ∃ ψ : D.dt0.domain, (ψ : Wt0) ∈ Q.Vt0 ∧ Q.π1 (D.S0 ψ) = 0 ∧ (ψ : Wt0) ≠ 0 := by
  have := Q.fd1; have := Q.fdt0
  let T : Q.Vt0 →ₗ[ℝ] Q.V1 :=
    LinearMap.codRestrict Q.V1 (Q.π1.toLinearMap ∘ₗ D.S0.toLinearMap ∘ₗ Q.Vt0.subtype)
      fun x => Q.π1_mem _
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := T) h)
  exact ⟨⟨x, Q.let0 x.2⟩, x.2, congrArg Subtype.val (LinearMap.mem_ker.1 hx),
    fun h0 => hx0 (Subtype.ext h0)⟩

end WeakSymmetryData.Discretization

section FEM

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) (N : ℕ)

/-- **`dim Vₕ¹ < dim Ṽₕ⁰`** for the electric discretizations. -/
theorem finrank_cubeQ_V1_lt :
    Module.finrank ℝ (cubeQ hT hB N).V1 < Module.finrank ℝ (cubeQ hT hB N).Vt0 := by
  change Module.finrank ℝ ((polyMin 3 PolySeq.lowestOrder N).V 1) <
    Module.finrank ℝ (tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 0))
  rw [finrank_tsub]
  exact finrank_polyMin_lt N

/-- **`π¹S⁰` maps `Ṽₕ⁰` onto `Vₕ¹`** for the electric discretizations
(`cubeWave_S0_surjective`). -/
theorem cubeQ_S0_onto : ∀ μ ∈ (cubeQ hT hB N).V1, ∃ ψ : 𝒟.dt0.domain,
    (ψ : Wv W0) ∈ (cubeQ hT hB N).Vt0 ∧ (cubeQ hT hB N).π1 (𝒟.S0 ψ) = μ := by
  intro μ hμ
  obtain ⟨ψ, hψ⟩ := cubeWave_S0_surjective hT hB N ⟨⟨μ, (cubeQ hT hB N).le1 hμ⟩, hμ⟩
  exact ⟨e0.symm (ψ : Wv U0), fun a => ψ.2 a,
    congrArg (fun x : (cubeFEM hT hB N).V1h => ((x : U1) : W1)) hψ⟩

/-- **(C2) restricts the initial values** of the electric discretizations: some `ψ ∈ Ṽₕ⁰` has
`π¹S⁰ψ = 0` and `d̃ψ ≠ 0`. -/
theorem cubeQ_exists_ker {C' : ℝ} (hS : 𝒟.IsStable C') : ∃ ψ : 𝒟.dt0.domain,
    (ψ : Wv W0) ∈ (cubeQ hT hB N).Vt0 ∧ (cubeQ hT hB N).π1 (𝒟.S0 ψ) = 0 ∧ 𝒟.dt0 ψ ≠ 0 := by
  obtain ⟨ψ, hψ, hψ0, hne⟩ :=
    (cubeQ hT hB N).exists_ker_of_finrank_lt (finrank_cubeQ_V1_lt hT hB N)
  refine ⟨ψ, hψ, hψ0, fun h => hne ?_⟩
  have := hS.poincare_t ψ
  rw [h, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

end FEM

end FEEC
