module

public import Solution.Absorbing
public import Feec.Semigroup.Spectral
public import Feec.Semigroup.Invariance

/-!
# Which boundary conditions preserve the constraints of the linearized Einstein–Bianchi system (solution)

The theorems of `Challenge.lean`, proved through the bridges to `Feec`:

* mirror conditions (`Solution.Bridge`): `tsd_propagates`, `tsd_existsUnique` and
  `exists_nonstationary` from `Feec.Models.Cube.Mirror.propagatesCube`,
  `Feec.Models.Cube.Mirror.existsUnique_memCube` and
  `Feec.Models.Cube.Mirror.exists_nonstationaryCube`: the TSD constraint is a reducing subcomplex
  of the mirror complex on the cube, the pull-back of the torus constraint along the mirror
  extensions ([QuennevilleBelair2015], Prop 4.17);
* electric conditions (`Solution.Electric`): `electric_forward_iff` from
  `Feec.Counterexamples.CubeStationary.forward_iff_stationary` (the minimal complex on the cube is
  a compression of the torus complex, whose wave group has pure point spectrum) and uniqueness of
  strong solutions; `electric_tsd_leaves` from
  `Feec.Counterexamples.BoundedDomainTSD.exists_isStrongSolution_tsd_not_propagates`;
* absorbing conditions (`Solution.Absorbing`): `absorbing_not_propagates` from
  `Feec.Models.Cube.Absorbing.not_invariant_tsdPair` (TSD states in the domain are not dense in
  the TSD states).

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
theorem tsd_propagates (hs : 0 < s) {t₀ t₁ : ℝ} {F U : ℝ → State ℂ b s}
    (hU : IsStrongSolution (IsWave b s) (Icc t₀ t₁) F U) (h0 : Constraint b s (U t₀))
    (hF : ∀ t ∈ Icc t₀ t₁, Constraint b s (F t)) : ∀ t ∈ Icc t₀ t₁, Constraint b s (U t) :=
  fun t ht => (constraint_iff hs _).2 (propagatesCube hs ((isStrongSolution_iff hs).1 hU)
    ((constraint_iff hs _).1 h0) (fun t ht => (constraint_iff hs _).1 (hF t ht)) t ht)

/-- **Well-posedness in the constraint** ([QuennevilleBelair2015], Prop 4.17): for `U₀ ∈ D(L)` in
the constraint and admissible forcing in the constraint, the linearized Einstein–Bianchi system
with mirror boundary conditions has a classical solution on `[t₀, t₁]` with `U t₀ = U₀`, it stays
in the constraint, and every strong solution with the same initial value agrees with it. -/
theorem tsd_existsUnique (hs : 0 < s) {U₀ : State ℂ b s} (hU₀ : ∃ V, IsWave b s U₀ V)
    (hU₀K : Constraint b s U₀) {t₀ t₁ : ℝ} {F : ℝ → State ℂ b s}
    (hF : IsAdmissible (IsWave b s) t₀ t₁ F) (hFK : ∀ t ∈ Icc t₀ t₁, Constraint b s (F t)) :
    ∃ U, U t₀ = U₀ ∧ IsClassicalSolution (IsWave b s) (Icc t₀ t₁) F U ∧
      (∀ t ∈ Icc t₀ t₁, Constraint b s (U t)) ∧
      ∀ V, V t₀ = U₀ → IsStrongSolution (IsWave b s) (Icc t₀ t₁) F V → EqOn V U (Icc t₀ t₁) := by
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
    ∃ U₀ V : State ℂ b s, IsWave b s U₀ V ∧ Constraint b s U₀ ∧ V ≠ 0 := by
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

/-! ### Electric conditions -/

section Electric

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.Models.Cube.Geometry (isOpen_openCube isBounded_openCube)

theorem isStrongSolution₀_zero_iff {b : Fin 3 → ℝ} {s : ℝ} {I : Set ℝ} {U : ℝ → State ℝ b s} :
    IsStrongSolution (IsWave₀ b s) I 0 U ↔
      Evolution.IsStrongSolution (elec b s).wave I 0 (fun t => toPiR (U t)) := by
  rw [isStrongSolution₀_iff]
  have : (fun t => toPiR ((0 : ℝ → State ℝ b s) t)) = 0 := funext fun _ => _root_.map_zero _
  rw [this]

/-- **With electric boundary conditions only stationary data propagate**: for every
`U₀ ∈ D(L)` the system `U' = L U` has a strong solution on `[0, ∞)` from `U₀`, and a strong
solution from `U₀` stays in the constraint `{0} × TSD × TSD` iff `U₀` lies in it and
`L U₀ = 0`. -/
theorem electric_forward_iff (hs : 0 < s) {U₀ : State ℝ b s} (hU₀ : ∃ V, IsWave₀ b s U₀ V) :
    (∃ U, U 0 = U₀ ∧ IsStrongSolution (IsWave₀ b s) (Ici 0) 0 U) ∧
      ∀ U, U 0 = U₀ → IsStrongSolution (IsWave₀ b s) (Ici 0) 0 U →
        ((∀ t ∈ Ici (0 : ℝ), Constraint₀ b s (U t)) ↔ Constraint₀ b s U₀ ∧ IsWave₀ b s U₀ 0) := by
  obtain ⟨V₀, hV₀⟩ := hU₀
  have hx := (mem_graph_iff'.1 ((isWave₀_iff _ _).1 hV₀)).1
  have hdiss : (elec b s).wave.IsDissipative := (elec b s).isSkewAdjoint_wave.isDissipative
  have horbit : Evolution.IsStrongSolution (elec b s).wave (Ici 0) 0
      (fun t => (elec b s).waveGroup.S t (toPiR U₀)) := by
    refine ⟨((elec b s).waveGroup.strongCont _).continuousOn, fun t ht => ?_⟩
    obtain ⟨v, hv, hd⟩ := ((elec b s).isStrongSolution_waveGroup hx (t + 1)).deriv t
      ⟨ht, by simp only [mem_Ici] at ht; linarith⟩
    refine ⟨v, hv, hd.mono_of_mem_nhdsWithin ?_⟩
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  have huniq : ∀ U : ℝ → State ℝ b s, U 0 = U₀ → IsStrongSolution (IsWave₀ b s) (Ici 0) 0 U →
      ∀ t ∈ Ici (0 : ℝ), toPiR (U t) = (elec b s).waveGroup.S t (toPiR U₀) := by
    intro U hU0 hU t ht
    exact ((isStrongSolution₀_zero_iff.1 hU).mono Icc_subset_Ici_self).unique hdiss
      (horbit.mono Icc_subset_Ici_self) (by simp [hU0]) ⟨ht, le_rfl⟩
  have hK := fun y : State ℝ b s => (constraint₀_iff y).1
  refine ⟨⟨fun t => toPiR.symm ((elec b s).waveGroup.S t (toPiR U₀)), by simp,
    isStrongSolution₀_zero_iff.2 (by simpa using horbit)⟩, fun U hU0 hU => ⟨fun hall => ?_, ?_⟩⟩
  · have hst := ((Feec.Counterexamples.CubeStationary.forward_iff_stationary hs le_rfl le_rfl
      (toPiR U₀)).1 fun t ht => (huniq U hU0 hU t ht) ▸ hK _ (hall t ht)).2
    have hconst : ∀ t ∈ Ici (0 : ℝ), U t = U₀ := fun t ht =>
      toPiR.injective ((huniq U hU0 hU t ht).trans (C0Group.mem_stationary.1 hst t))
    refine ⟨hU0 ▸ hall 0 (mem_Ici.2 le_rfl), ?_⟩
    obtain ⟨V, hV, hd⟩ := hU.2 0 (mem_Ici.2 le_rfl)
    have h0 : HasDerivWithinAt U 0 (Ici 0) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Ici 0) U₀).congr (fun t ht => hconst t ht)
        (hconst 0 (mem_Ici.2 le_rfl))
    have e := (uniqueDiffWithinAt_Ici 0).eq_deriv _ hd h0
    simp only [Pi.zero_apply, add_zero] at e
    rw [hU0, e] at hV
    exact hV
  · rintro ⟨hK0, hW0⟩ t ht
    have hgraph := (isWave₀_iff U₀ 0).1 hW0
    rw [_root_.map_zero] at hgraph
    have hc : Evolution.IsStrongSolution (elec b s).wave (Icc 0 t) 0 (fun _ => toPiR U₀) :=
      ⟨continuousOn_const, fun τ _ => ⟨0, hgraph, by
        simpa using hasDerivWithinAt_const τ (Icc 0 t) (toPiR U₀)⟩⟩
    have e := ((isStrongSolution₀_zero_iff.1 hU).mono Icc_subset_Ici_self).unique hdiss hc
      (by simp [hU0]) ⟨ht, le_rfl⟩
    have hUt : U t = U₀ := toPiR.injective e
    rw [hUt]
    exact hK0

/-- **With electric boundary conditions TSD data leave the constraint at once**: some datum
`U₀ ∈ D(L)` in the constraint has, for every `T > 0`, a strong solution on `[0, T]`, and every
strong solution from it on `[0, T]` leaves the constraint. -/
theorem electric_tsd_leaves (hs : 0 < s) :
    ∃ U₀ : State ℝ b s, (∃ V, IsWave₀ b s U₀ V) ∧ Constraint₀ b s U₀ ∧ ∀ T > 0,
      (∃ U, U 0 = U₀ ∧ IsStrongSolution (IsWave₀ b s) (Icc 0 T) 0 U) ∧
      ∀ U, U 0 = U₀ → IsStrongSolution (IsWave₀ b s) (Icc 0 T) 0 U →
        ∃ t ∈ Icc 0 T, ¬Constraint₀ b s (U t) := by
  obtain ⟨y, hD, hK, hall⟩ :=
    Feec.Counterexamples.BoundedDomainTSD.exists_isStrongSolution_tsd_not_propagates
      (isOpen_openCube b s) (isBounded_openCube b s)
      (Feec.Counterexamples.CubeStationary.nonempty_openCube hs)
      (Models.BoundedDomain.gradCurl ℝ (isOpen_openCube b s)) le_rfl
  refine ⟨toPiR.symm y, ⟨toPiR.symm ((elec b s).wave ⟨y, hD⟩), (isWave₀_iff _ _).2 ?_⟩,
    (constraint₀_iff _).2 (by simpa using hK), fun T hT => ⟨⟨fun t => toPiR.symm
      ((elec b s).waveGroup.S t y), by simp, isStrongSolution₀_zero_iff.2 ?_⟩, fun U hU0 hU => ?_⟩⟩
  · simpa using (elec b s).wave.mem_graph ⟨y, hD⟩
  · simpa using (hall T hT).1
  · obtain ⟨t, ht, hn⟩ := (hall T hT).2 (fun t => toPiR (U t)) (by simp [hU0])
      (isStrongSolution₀_zero_iff.1 hU)
    exact ⟨t, ht, fun h => hn ((constraint₀_iff _).1 h)⟩

end Electric

/-! ### Absorbing conditions -/

/-- **The absorbing boundary conditions do not preserve the TSD constraint**: on `Q = (0, ½)³`
some datum `(E₀, B₀)` with `E₀`, `B₀` TSD has a mild solution of `(E, B)' = A (E, B)`, and
every mild solution from it leaves the TSD constraint. -/
theorem absorbing_not_propagates :
    ∃ U₀ : Mat ℝ 0 (1 / 2) × Mat ℝ 0 (1 / 2), IsTSD₀ 0 (1 / 2) U₀.1 ∧ IsTSD₀ 0 (1 / 2) U₀.2 ∧
      (∃ U, U 0 = U₀ ∧ IsMildSolution IsAbsorbing U) ∧
      ∀ U, U 0 = U₀ → IsMildSolution IsAbsorbing U →
        ∃ t ∈ Ici (0 : ℝ), ¬(IsTSD₀ 0 (1 / 2) (U t).1 ∧ IsTSD₀ 0 (1 / 2) (U t).2) := by
  have h := Feec.Models.Cube.Absorbing.not_invariant_tsdPair
  push Not at h
  obtain ⟨t, ht, x, hx, hn⟩ := h
  have h0 : Feec.Models.Cube.Absorbing.absorbingSemigroup.S 0 x = x := by
    rw [Feec.Models.Cube.Absorbing.absorbingSemigroup.map_zero]; rfl
  refine ⟨eAbs.symm x, (isTSD₀_iff _).2 hx.1, (isTSD₀_iff _).2 hx.2,
    ⟨fun τ => eAbs.symm (Feec.Models.Cube.Absorbing.absorbingSemigroup.S τ x),
      congrArg eAbs.symm h0, isMildSolution_orbit x⟩, fun U hU0 hU => ⟨t, ht, fun h' => hn ?_⟩⟩
  have e : eAbs (U t) = Feec.Models.Cube.Absorbing.absorbingSemigroup.S t x := by
    rw [isMildSolution_eq_orbit hU ht, hU0, ContinuousLinearEquiv.apply_symm_apply]
  rw [← e]
  exact ⟨(isTSD₀_iff _).1 h'.1, (isTSD₀_iff _).1 h'.2⟩

end FEEC.EinsteinBianchi
