module

public import Solution.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Hodge wave operator of the challenge: linearity, skewness, uniqueness

For any data `D`, the relation `D.IsWave` is linear (`IsWave.sub`, `IsWave.zero`) and skew,
`⟪L U, U⟫ = 0` (`IsWave.inner_eq_zero`: the terms of the four equations cancel in pairs), so the
energy `‖U(t)‖²` of a strong solution is conserved and strong solutions are determined by their
initial value (`isStrongSolution_unique`). `isStrongSolution_setOf_iff`: the strong solutions of
the graph `{(U, V) | L U V}` of a relation are those of the relation.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1 ((6.1))

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace FEEC

/-- **Strong solutions of an operator given by a relation** `L`: `IsStrongSolution` of its graph
`{(U, V) | L U V}` is the relation form, continuity on `I` and, at every `t ∈ I`, a derivative
`V` of `U` within `I` with `L (U t) V`. -/
theorem isStrongSolution_setOf_iff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {L : X → X → Prop} {I : Set ℝ} {U : ℝ → X} :
    IsStrongSolution {p | L p.1 p.2} I U ↔
      ContinuousOn U I ∧ ∀ t ∈ I, ∃ V, L (U t) V ∧ HasDerivWithinAt U V I t :=
  Iff.rfl

end FEEC

namespace FEEC.WeakSymmetryData

variable {W0 W1 W2 Wt0 Wt1 Wt2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [NormedAddCommGroup Wt2]
  [InnerProductSpace ℝ Wt2] {D : WeakSymmetryData W0 W1 W2 Wt0 Wt1 Wt2}

theorem IsWave.zero : D.IsWave 0 0 :=
  ⟨0, 0, 0, rfl, rfl, by rw [LinearPMap.map_zero, Submodule.coe_zero, map_zero],
    fun _ _ _ => by simp, fun v => by simp,
    by simp, by simp⟩

theorem IsWave.sub {U V U' V' : W0 × Wt1 × W2 × Wt2} (h : D.IsWave U V) (h' : D.IsWave U' V') :
    D.IsWave (U - U') (V - V') := by
  obtain ⟨σ, φ, u, hσ, hu, hc, h1, h2, h3, h4⟩ := h
  obtain ⟨σ', φ', u', hσ', hu', hc', h1', h2', h3', h4'⟩ := h'
  refine ⟨σ - σ', φ - φ', u - u', by simp [hσ, hσ'], by simp [hu, hu'],
    by rw [LinearPMap.map_sub, Submodule.coe_sub, map_sub, hc, hc'], fun τ ψ hτ => ?_, fun v => ?_,
    ?_, ?_⟩
  · change ⟪V.1 - V'.1, (τ : W0)⟫ = ⟪(u : Wt1) - u', D.dt0 ψ⟫
    rw [inner_sub_left, inner_sub_left, h1 τ ψ hτ, h1' τ ψ hτ]
  · change ⟪V.2.1 - V'.2.1, (v : Wt1)⟫ = -⟪D.dt0 (φ - φ'), (v : Wt1)⟫ -
      ⟪U.2.2.1 - U'.2.2.1, D.S1 v⟫ - ⟪U.2.2.2 - U'.2.2.2, D.dt1 v⟫
    rw [inner_sub_left, h2 v, h2' v, LinearPMap.map_sub, inner_sub_left, inner_sub_left,
      inner_sub_left]
    ring
  · change V.2.2.1 - V'.2.2.1 = D.S1 ((u : Wt1) - u')
    rw [h3, h3', map_sub]
  · change V.2.2.2 - V'.2.2.2 = D.dt1 (u - u')
    rw [h4, h4', LinearPMap.map_sub]

/-- **The wave operator is skew**: `⟪L U, U⟫ = 0`. -/
theorem IsWave.inner_eq_zero {U V : W0 × Wt1 × W2 × Wt2} (h : D.IsWave U V) :
    ⟪V.1, U.1⟫ + ⟪V.2.1, U.2.1⟫ + ⟪V.2.2.1, U.2.2.1⟫ + ⟪V.2.2.2, U.2.2.2⟫ = 0 := by
  obtain ⟨σ, φ, u, hσ, hu, hc, h1, h2, h3, h4⟩ := h
  rw [← hσ, ← hu, h1 σ φ hc, h2 u, h3, h4, real_inner_comm (D.S1 u), real_inner_comm (D.dt1 u),
    real_inner_comm (D.dt0 φ)]
  ring

/-- The energy `‖σ‖² + ‖u‖² + ‖M‖² + ‖ρ‖²` as a sum of inner products. -/
def energy (U : W0 × Wt1 × W2 × Wt2) : ℝ :=
  ⟪U.1, U.1⟫ + ⟪U.2.1, U.2.1⟫ + ⟪U.2.2.1, U.2.2.1⟫ + ⟪U.2.2.2, U.2.2.2⟫

theorem eq_zero_of_energy_eq_zero {U : W0 × Wt1 × W2 × Wt2} (h : energy U = 0) : U = 0 := by
  have a := real_inner_self_nonneg (x := U.1)
  have b := real_inner_self_nonneg (x := U.2.1)
  have c := real_inner_self_nonneg (x := U.2.2.1)
  have d := real_inner_self_nonneg (x := U.2.2.2)
  unfold energy at h
  refine Prod.ext ((inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)) (Prod.ext
    ((inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith))
    (Prod.ext ((inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith))
      ((inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith))))

/-- The derivative of the energy along a path. -/
theorem hasDerivWithinAt_energy {U : ℝ → W0 × Wt1 × W2 × Wt2} {V : W0 × Wt1 × W2 × Wt2}
    {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt U V s t) :
    HasDerivWithinAt (fun r => energy (U r))
      (2 * (⟪V.1, (U t).1⟫ + ⟪V.2.1, (U t).2.1⟫ + ⟪V.2.2.1, (U t).2.2.1⟫ +
        ⟪V.2.2.2, (U t).2.2.2⟫)) s t := by
  have h1 := (ContinuousLinearMap.fst ℝ W0 (Wt1 × W2 × Wt2)).hasFDerivAt.comp_hasDerivWithinAt t h
  have h' := (ContinuousLinearMap.snd ℝ W0 (Wt1 × W2 × Wt2)).hasFDerivAt.comp_hasDerivWithinAt t h
  have h2 := (ContinuousLinearMap.fst ℝ Wt1 (W2 × Wt2)).hasFDerivAt.comp_hasDerivWithinAt t h'
  have h'' := (ContinuousLinearMap.snd ℝ Wt1 (W2 × Wt2)).hasFDerivAt.comp_hasDerivWithinAt t h'
  have h3 := (ContinuousLinearMap.fst ℝ W2 Wt2).hasFDerivAt.comp_hasDerivWithinAt t h''
  have h4 := (ContinuousLinearMap.snd ℝ W2 Wt2).hasFDerivAt.comp_hasDerivWithinAt t h''
  have := (((h1.inner ℝ h1).add (h2.inner ℝ h2)).add (h3.inner ℝ h3)).add (h4.inner ℝ h4)
  refine this.congr_deriv ?_
  simp only [Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [real_inner_comm (U t).1 V.1, real_inner_comm (U t).2.1 V.2.1,
    real_inner_comm (U t).2.2.1 V.2.2.1, real_inner_comm (U t).2.2.2 V.2.2.2]
  ring

/-- **Strong solutions are determined by their initial value**: the energy of the difference is
conserved (`IsWave.inner_eq_zero`). -/
theorem isStrongSolution_unique {T : ℝ} {U U' : ℝ → W0 × Wt1 × W2 × Wt2}
    (hU : IsStrongSolution {p | D.IsWave p.1 p.2} (Icc 0 T) U)
    (hU' : IsStrongSolution {p | D.IsWave p.1 p.2} (Icc 0 T) U') (h0 : U 0 = U' 0) :
    EqOn U U' (Icc 0 T) := by
  have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun r => energy (U r - U' r)) 0 (Icc 0 T) t := by
    intro t ht
    obtain ⟨V, hV, hdV⟩ := (isStrongSolution_setOf_iff.1 hU).2 t ht
    obtain ⟨V', hV', hdV'⟩ := (isStrongSolution_setOf_iff.1 hU').2 t ht
    have := hasDerivWithinAt_energy (hdV.sub hdV')
    rw [show (U - U') t = U t - U' t from rfl, (hV.sub hV').inner_eq_zero, mul_zero] at this
    exact this
  have hc : ContinuousOn (fun r => energy (U r - U' r)) (Icc 0 T) := fun t ht =>
    (hd t ht).continuousWithinAt
  intro t ht
  have hconst := constant_of_has_deriv_right_zero hc (fun x hx =>
    (hd x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)) t ht
  rw [h0, sub_self] at hconst
  have e0 : energy (0 : W0 × Wt1 × W2 × Wt2) = 0 := by simp [energy]
  exact sub_eq_zero.1 (eq_zero_of_energy_eq_zero (hconst.trans e0))

end FEEC.WeakSymmetryData
