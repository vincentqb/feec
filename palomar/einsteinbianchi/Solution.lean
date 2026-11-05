module

public import Solution.Bridge
public import Feec.Semigroup.Spectral
public import Feec.Semigroup.Invariance

/-!
# Constraint propagation for the linearized Einstein–Bianchi system on a cube (solution)

`FEEC.EinsteinBianchi.tsd_propagates`, `FEEC.EinsteinBianchi.tsd_existsUnique` and
`FEEC.EinsteinBianchi.exists_nonstationary` of `Challenge.lean`, proved through the bridge
`Solution.Bridge` (`isWave_iff`, `constraint_iff`, `isStrongSolution_iff`,
`isClassicalSolution_iff`, `isAdmissible_iff`) from `Feec.Models.Cube.Mirror.propagatesCube`,
`Feec.Models.Cube.Mirror.existsUnique_memCube` and
`Feec.Models.Cube.Mirror.exists_nonstationaryCube`: the TSD constraint is a reducing subcomplex of
the mirror complex on the cube, the pull-back of the torus constraint along the mirror extensions
([QuennevilleBelair2015], Prop 4.17).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set

@[expose] public noncomputable section

namespace FEEC.EinsteinBianchi

open Feec Feec.Models.Cube.Mirror

variable (b : Fin 3 → ℝ) (s : ℝ)

/-- **The TSD constraints propagate on the cube with mirror boundary conditions**
([QuennevilleBelair2015], Prop 4.17): a strong solution of the linearized Einstein–Bianchi system
on `[t₀, t₁]` whose initial value and forcing lie in the constraint stays in the constraint. -/
theorem tsd_propagates (hs : 0 < s) {t₀ t₁ : ℝ} {F U : ℝ → State b s}
    (hU : IsStrongSolution b s (Icc t₀ t₁) F U) (h0 : Constraint b s (U t₀))
    (hF : ∀ t ∈ Icc t₀ t₁, Constraint b s (F t)) : ∀ t ∈ Icc t₀ t₁, Constraint b s (U t) :=
  fun t ht => (constraint_iff hs _).2 (propagatesCube hs ((isStrongSolution_iff hs).1 hU)
    ((constraint_iff hs _).1 h0) (fun t ht => (constraint_iff hs _).1 (hF t ht)) t ht)

/-- **Well-posedness in the constraint** ([QuennevilleBelair2015], Prop 4.17): for `U₀ ∈ D(L)` in
the constraint and admissible forcing in the constraint, the linearized Einstein–Bianchi system
with mirror boundary conditions has a classical solution on `[t₀, t₁]` with `U t₀ = U₀`, it stays
in the constraint, and every strong solution with the same initial value agrees with it. -/
theorem tsd_existsUnique (hs : 0 < s) {U₀ : State b s} (hU₀ : ∃ V, IsWave b s U₀ V)
    (hU₀K : Constraint b s U₀) {t₀ t₁ : ℝ} {F : ℝ → State b s} (hF : IsAdmissible b s t₀ t₁ F)
    (hFK : ∀ t ∈ Icc t₀ t₁, Constraint b s (F t)) :
    ∃ U, U t₀ = U₀ ∧ IsClassicalSolution b s (Icc t₀ t₁) F U ∧
      (∀ t ∈ Icc t₀ t₁, Constraint b s (U t)) ∧
      ∀ V, V t₀ = U₀ → IsStrongSolution b s (Icc t₀ t₁) F V → EqOn V U (Icc t₀ t₁) := by
  obtain ⟨V₀, hV₀⟩ := hU₀
  have hd := (LinearPMap.mem_graph_iff_exists.1 ((isWave_iff hs _ _).1 hV₀)).1
  obtain ⟨W, hW0, hWc, hWK, hWu⟩ := existsUnique_memCube hs hd ((constraint_iff hs _).1 hU₀K)
    ((isAdmissible_iff hs).1 hF) fun t ht => (constraint_iff hs _).1 (hFK t ht)
  have hW : (fun t => toPi (toPi.symm (W t))) = W := funext fun t => toPi.apply_symm_apply _
  refine ⟨fun t => toPi.symm (W t), ?_, ?_, fun t ht => ?_, fun V hV0 hV t ht => ?_⟩
  · simp only [hW0, ContinuousLinearEquiv.symm_apply_apply]
  · rw [isClassicalSolution_iff hs, hW]
    exact hWc
  · rw [constraint_iff hs, ContinuousLinearEquiv.apply_symm_apply]
    exact hWK t ht
  · have e := hWu (fun t => toPi (V t)) (by simp only [hV0]) ((isStrongSolution_iff hs).1 hV) ht
    simp only at e
    change V t = toPi.symm (W t)
    rw [← e, ContinuousLinearEquiv.symm_apply_apply]

/-- **The constraint has dynamical content**: on every open cube some datum `U₀ ∈ D(L)` in the
constraint has `L U₀ ≠ 0`, so the solution from it is not stationary. -/
theorem exists_nonstationary (hs : 0 < s) :
    ∃ U₀ V, IsWave b s U₀ V ∧ Constraint b s U₀ ∧ V ≠ 0 := by
  obtain ⟨y, hy, hyK, hns⟩ := exists_nonstationaryCube (b := b) hs
  refine ⟨toPi.symm y, toPi.symm ((complexCube b s hs).wave ⟨y, hy⟩), (isWave_iff hs _ _).2 ?_,
    (constraint_iff hs _).2 ?_, fun h => hns ?_⟩
  · simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact (complexCube b s hs).wave.mem_graph ⟨y, hy⟩
  · rwa [ContinuousLinearEquiv.apply_symm_apply]
  · have h0 : (complexCube b s hs).wave ⟨y, hy⟩ = 0 := by
      simpa using congrArg toPi h
    have key : ∀ (A : PiLp 2 (SpaceCube b s) →ₗ.[ℂ] PiLp 2 (SpaceCube b s))
        (_ : A = (complexCube b s hs).wave), ∃ hx : y ∈ A.domain, A ⟨_, hx⟩ = 0 := by
      rintro _ rfl; exact ⟨hy, h0⟩
    obtain ⟨hx, e⟩ := key _ (complexCube b s hs).generator_waveGroup
    exact C0Group.mem_stationary.2 fun t => C0Group.S_apply_eq_of_generator_eq_zero ⟨_, hx⟩ e t

end FEEC.EinsteinBianchi
