module

public import Solution.Bridge
public import Solution.Lumped

/-!
# A-stable rational time stepping for `C₀`-semigroups (solution)

The theorems of `Challenge.lean`, proved from `Feec` through the bridges `Solution.Bridge` (the
rational schemes, semigroups, bounded generators and sub-Markov generators) and `Solution.Lumped`
(meshes and the lumped-mass `P₁` Laplacian).

* The input: the Hille–Yosida estimates from `Feec.C0Semigroup.isResolvent_resolvent` and
  `Feec.C0Semigroup.norm_resolvent_pow_le`; backward Euler from
  `Feec.TimeStepping.norm_pow_le_of_generator` and
  `Feec.TimeStepping.RationalScheme.norm_backwardEuler_pow_sub_S_le`.
* Banach spaces: Brenner–Thomée's stability bound from
  `Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable`
  (the Hille–Phillips calculus on the complexification) and the sharp error from
  `Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`
  (Brenner–Thomée's error kernel, `Feec.HalfLineAlgebra.integral_norm_errorKernel_le`).
* Hilbert spaces: `ContinuousLinearMap.norm_aeval_mul_inverse_le`,
  `Feec.TimeStepping.RationalScheme.norm_step_le` with
  `Feec.TimeStepping.RationalScheme.step_eq_resolventEval`.
* Families: the bounded-generator bounds of `Feec.TimeStepping.StableFamily` for a one-member
  family (`TimeStepping.norm_rationalApply_pow_le`, `TimeStepping.norm_rationalApply_pow_sub_le`);
  the convergence theorem `Feec.TimeStepping.BanachFEEC.TimeScheme.converges`, with
  `Feec.TimeStepping.StableFamily.backwardEuler` for backward Euler.
* The maximum norm: `IsSubMarkovGenerator.norm_exp_smul_le_one` and the other sub-Markov facts of
  `Feec.ForMathlib.Analysis.SubMarkov`; the discrete maximum principle
  `Feec.FiniteElement.isSubMarkovGenerator_lumpedLaplacianOn` and
  `FiniteDifference.isSubMarkovGenerator_laplacian`; the Freudenthal mesh
  `Feec.Mesh.freudenthalMesh`, non-obtuse by `Feec.FiniteElement.isNonobtuse_freudenthalMesh`,
  whose lumped-mass Laplacian is the finite difference Laplacian
  (`Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian_eq`); and the compatible-data estimate
  `Feec.Models.Cube.FiniteDifferenceHeat.rational_compatible`.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024],
  Thm 1.1
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.11
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.5, §3.4
* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7, 15
* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Polynomial Asymptotics Filter Set Feec.TimeStepping

@[expose] public noncomputable section

namespace TimeStepping

/-! ### The input: Hille–Yosida -/

/-- **The Hille–Yosida estimates** ([Pazy1983], §1.5). Let `S` be a strongly continuous
semigroup of a complex Banach space (real ones are covered by complexification in `Feec`, not
here) with `‖S t‖ ≤ M e^{ωt}`, generator `A`. Every `z` with
`re z > ω` is in the resolvent set of `A`: there is a bounded `R` with `R (z x - A x) = x` on
`D(A)`, `R y ∈ D(A)` with `A R y = z R y - y`, and `‖Rᵐ‖ ≤ M/(re z - ω)ᵐ` for every `m`. -/
theorem hilleYosida {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : ℝ → E →L[ℂ] E) (hS : IsC0Semigroup S) {M ω : ℝ}
    (hSb : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) :
    ∃ R : E →L[ℂ] E, (∀ x y : E, (x, y) ∈ generatorGraph S → R (z • x - y) = x) ∧
      (∀ y : E, (R y, z • R y - y) ∈ generatorGraph S) ∧
      ∀ m : ℕ, ‖R ^ m‖ ≤ M / (z.re - ω) ^ m := by
  set G := hS.toC0
  have hR := G.isResolvent_resolvent hSb hz
  refine ⟨Feec.Operator.resolvent G.generator z, fun x y h => ?_, fun y => ?_,
    G.norm_resolvent_pow_le hSb hz⟩
  · obtain ⟨hx, rfl⟩ := LinearPMap.mem_graph_iff_exists.1 ((mem_graph_iff G).2 h)
    exact hR.apply_sub ⟨x, hx⟩
  · rw [← hR.apply_resolvent y]
    exact G.hasDerivWithinAt_generator (hR.toDomain y)

/-- **Backward Euler on Banach spaces**: `Feec.TimeStepping.norm_pow_le_of_generator` and
`Feec.TimeStepping.RationalScheme.norm_backwardEuler_pow_sub_S_le`. -/
theorem backwardEuler {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E)
    (hS : IsC0Semigroup S) {M ω : ℝ} (hω : 0 ≤ ω)
    (hSb : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t)) {τ : ℝ} (hτ : 0 < τ)
    (hωτ : ω * τ < 1) (R : E →L[𝕜] E)
    (hR : ∀ x y : E, (x, y) ∈ generatorGraph S → R (x - (τ : 𝕜) • y) = x) :
    (∀ k : ℕ, ‖R ^ k‖ ≤ M / (1 - ω * τ) ^ k) ∧
      ∀ (n : ℕ) (u : ℕ → E), (∀ j < 2, (u j, u (j + 1)) ∈ generatorGraph S) →
        ‖(R ^ n) (u 0) - S (n * τ) (u 0)‖ ≤ M / (1 - ω * τ) ^ n *
          (M / (1 - ω * τ) + M * Real.exp (ω * (n * τ)) / 2) * (M * Real.exp (ω * (n * τ))) *
            (n * τ) * τ * ‖u 2‖ := by
  set G := hS.toC0
  have hR' : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x :=
    fun x y hxy => hR x y ((mem_graph_iff G).1 hxy)
  exact ⟨norm_pow_le_of_generator G hSb hτ hωτ hR', fun n u hu =>
    RationalScheme.norm_backwardEuler_pow_sub_S_le G hω hSb hτ hωτ hR' n
      fun j hj => (mem_graph_iff G).2 (hu j hj)⟩

/-! ### Banach spaces: Brenner–Thomée -/

/-- **Brenner–Thomée's stability bound** ([BrennerThomee1979]). For every A-stable `r = p/q`
(`|r(∞)| = 1` allowed) there is `C ≥ 0`, depending on `r` only, such that for every strongly
continuous semigroup `S` of a real or complex Banach space with `‖S t‖ ≤ M` (`t ≥ 0`), generator
`A`, and every `τ > 0`: exactly one bounded `R` satisfies `R (x - τAx) = x` on `D(A)` (the
resolvent `(1 - τA)⁻¹`), `Q(R)` is invertible, and `‖r(τA)ⁿ‖ ≤ M (1 + C √n)` for every `n`. -/
theorem stable (p q : ℝ[X]) (hr : IsAStable p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
      [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (M : ℝ),
      IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) → ∀ τ : ℝ, 0 < τ → ∃ R : E →L[𝕜] E,
        (∀ T : E →L[𝕜] E,
          (∀ x y : E, (x, y) ∈ generatorGraph S → T (x - (τ : 𝕜) • y) = x) ↔ T = R) ∧
        IsUnit (resolventPoly q.natDegree q R) ∧
        ∀ n : ℕ, ‖rationalOfResolvent p q R ^ n‖ ≤ M * (1 + C * √n) := by
  refine ⟨hr.scheme.sqrtConst, hr.scheme.sqrtConst_nonneg, ?_⟩
  intro 𝕜 E _ _ _ _ _ _ S M hS hM τ hτ
  set G := hS.toC0
  have hM' : ∀ t, 0 ≤ t → ‖G.S t‖ ≤ M := hM
  have hres := G.isResolvent_resolvent_ofReal (M := M) (ω := 0) (by simpa using hM')
    (inv_pos.2 hτ)
  rw [RCLike.ofReal_inv] at hres
  set R := (τ : 𝕜)⁻¹ • Feec.Operator.resolvent G.generator (τ : 𝕜)⁻¹
  have hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x :=
    fun x y hxy => hres.inv_smul_apply_sub hτ.ne' hxy
  refine ⟨R, fun T => ⟨fun hT => hres.eq_inv_smul_of_apply_sub hτ.ne'
    fun x y hxy => hT x y ((mem_graph_iff G).1 hxy), fun hT => ?_⟩, ?_, fun n => ?_⟩
  · subst hT
    exact fun x y hxy => hR x y ((mem_graph_iff G).2 hxy)
  · have := hr.scheme.isUnit_resolventEval_den_of_resolvent G hM' hτ hR
    rwa [resolventPoly_eq] at this
  · rw [← resolventStep_eq hr]
    exact RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable G hM'
      hr.scheme_isAStable hτ hR n

/-- **Brenner–Thomée's smooth-data error estimate** ([BrennerThomee1979]; [GomilkoTomilov2024],
Thm 1.1(ii)). For every A-stable `r = p/q` of order `m` (`|r(∞)| = 1` allowed) there is `K`,
depending on `r` and `m` only, such that for every strongly continuous semigroup `S` of a real or
complex Banach space with `‖S t‖ ≤ M` (`t ≥ 0`), generator `A`, every `τ > 0` and the resolvent
`R` (as in `stable`), `‖r(τA)ⁿ x - S(nτ) x‖ ≤ K M nτ τᵐ ‖A^{m+1} x‖` for every `n` and
`x ∈ D(A^{m+1})` (a chain `u 0 = x, …, u (m + 1) = A^{m+1} x` in the graph of `A`): order `m`
at fixed `T = nτ`, without the `√n` of the stability bound. -/
theorem error (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    ∃ K : ℝ, ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
      [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (M : ℝ),
      IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) → ∀ τ : ℝ, 0 < τ → ∀ R : E →L[𝕜] E,
        (∀ x y : E, (x, y) ∈ generatorGraph S → R (x - (τ : 𝕜) • y) = x) →
        ∀ (n : ℕ) (u : ℕ → E), (∀ j < m + 1, (u j, u (j + 1)) ∈ generatorGraph S) →
          ‖(rationalOfResolvent p q R ^ n) (u 0) - S (n * τ) (u 0)‖ ≤
            K * M * (n * τ) * τ ^ m * ‖u (m + 1)‖ := by
  refine ⟨hr.scheme.sharpConst m, ?_⟩
  intro 𝕜 E _ _ _ _ _ _ S M hS hM τ hτ R hR n u hu
  set G := hS.toC0
  have h := RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent G hM
    hr.scheme_isAStable (hr.scheme_hasOrder hm) hτ
    (fun x y hxy => hR x y ((mem_graph_iff G).1 hxy)) n (u := u)
    fun j hj => (mem_graph_iff G).2 (hu j hj)
  rwa [resolventStep_eq hr] at h

/-! ### Hilbert spaces: von Neumann -/

/-- **Von Neumann's inequality** ([VonNeumann1951]), for rational functions. -/
theorem vonNeumann {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) (p q : ℂ[X])
    (hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0) :
    IsUnit (aeval T q) ∧
      ‖aeval T p * Ring.inverse (aeval T q)‖ₑ ≤
        ⨆ ζ ∈ Metric.sphere (0 : ℂ) 1, ‖p.eval ζ / q.eval ζ‖ₑ := by
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun z => p.eval z / q.eval z) (p.continuous.continuousOn.div q.continuous.continuousOn
      fun z hz => hq z (mem_sphere_zero_iff_norm.1 hz).le)
  refine ⟨(ContinuousLinearMap.norm_aeval_mul_inverse_le hT hq
    fun ζ hζ _ => hK ζ (mem_sphere_zero_iff_norm.2 hζ)).1, ?_⟩
  rw [iSup_subtype']
  exact enorm_le_iSup _ _ fun C hC =>
    (ContinuousLinearMap.norm_aeval_mul_inverse_le hT hq
      fun ζ hζ _ => hC ⟨ζ, mem_sphere_zero_iff_norm.2 hζ⟩).2

/-- **Rational schemes for m-dissipative operators: von Neumann's theorem** ([HairerWanner1996],
§IV.11; [Pazy1983], §1.4). Let `A` be a possibly unbounded operator of a real or complex Hilbert
space, dissipative (`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A` onto for some `μ > 0`
(m-dissipative), `r = p/q` a real rational function with `q` free of zeros in the closed left
half-plane, and `τ > 0`. Exactly one bounded `R` satisfies `R (x - τAx) = x` on `D(A)` (the
resolvent `(1 - τA)⁻¹`), `Q(R)` is invertible, and `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every `n`
(suprema in `[0, ∞]`; infinite when `deg p > deg q`). For A-stable `r` this is `≤ 1`:
A-stable schemes are contractive. -/
theorem contractive {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {A : E →ₗ.[𝕜] E} (hA : ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0)
    (hA' : ∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y)
    (p q : ℝ[X]) (hq : ∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ R : E →L[𝕜] E,
      (∀ T : E →L[𝕜] E, (∀ x : A.domain, T ((x : E) - (τ : 𝕜) • A x) = x) ↔ T = R) ∧
      IsUnit (resolventPoly q.natDegree q R) ∧ ∀ n : ℕ, ‖rationalOfResolvent p q R ^ n‖ₑ ≤
        (⨆ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ₑ) ^ n := by
  have hAm : A.IsMDissipative := ⟨hA, hA'⟩
  refine ⟨(τ : 𝕜)⁻¹ • Feec.Operator.resolvent A (τ : 𝕜)⁻¹, apply_sub_smul_eq_iff hAm hτ, ?_⟩
  refine ⟨?_, enorm_pow_le_iSup_pow ContinuousLinearMap.norm_id_le _ _ fun C hC => ?_⟩
  · have := (RationalScheme.ofBounded 0 q hq (C := 0) (by simp)).isUnit_resolventEval_den hAm hτ
    rwa [resolventPoly_eq] at this
  have h := ((RationalScheme.ofBounded p q hq hC).norm_step_le hAm hτ).2
  rw [RationalScheme.step_eq_resolventEval] at h
  have e : (RationalScheme.ofBounded p q hq hC).resolventStep
      ((τ : 𝕜)⁻¹ • Feec.Operator.resolvent A (τ : 𝕜)⁻¹) =
      rationalOfResolvent p q ((τ : 𝕜)⁻¹ • Feec.Operator.resolvent A (τ : 𝕜)⁻¹) := by
    show resolventEval q.natDegree (p.map (algebraMap ℝ 𝕜)) _ *
      Ring.inverse (resolventEval q.natDegree (q.map (algebraMap ℝ 𝕜)) _) = _
    rw [resolventPoly_eq, resolventPoly_eq]; rfl
  rw [← e]
  exact h.trans (RationalScheme.supNorm_ofBounded_le hq hC)

/-! ### Families of space discretizations -/

/-- **Brenner–Thomée's stability bound for bounded generators**:
`TimeStepping.norm_rationalApply_pow_le`. -/
theorem stable_of_bounded (p q : ℝ[X]) (hr : IsAStable p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [CompleteSpace X] (L : X →L[𝕜] X) (M : ℝ),
      (∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ M) → ∀ τ : ℝ, 0 < τ →
        IsUnit (aeval ((τ : 𝕜) • L) (q.map (algebraMap ℝ 𝕜))) ∧
        ∀ n : ℕ, ‖rationalApply p q ((τ : 𝕜) • L) ^ n‖ ≤ M * (1 + C * √n) := by
  refine ⟨hr.scheme.sqrtConst, hr.scheme.sqrtConst_nonneg, ?_⟩
  intro 𝕜 X _ _ _ _ L M hL τ hτ
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have : IsScalarTower ℝ 𝕜 X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact norm_rationalApply_pow_le hτ L hL hr

/-- **The error of A-stable schemes for bounded generators**:
`TimeStepping.norm_rationalApply_pow_sub_le`. -/
theorem error_of_bounded (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    ∃ K : ℝ, ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [CompleteSpace X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] (L : X →L[𝕜] X) (M : ℝ),
      (∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ M) → ∀ τ : ℝ, 0 < τ →
      ∀ (n : ℕ) (v : X),
        ‖(rationalApply p q ((τ : 𝕜) • L) ^ n) v - NormedSpace.exp (((n * τ : ℝ) : 𝕜) • L) v‖ ≤
          K * M * (n * τ) * τ ^ m * ‖(L ^ (m + 1)) v‖ ∧
        ∀ (U U' : ℝ → X) (D : ℝ), (∀ s ∈ Icc 0 (n * τ), HasDerivAt U (U' s) s) →
          (∀ s ∈ Icc 0 (n * τ), ‖U' s - L (U s)‖ ≤ D) →
          ‖U (n * τ) - (rationalApply p q ((τ : 𝕜) • L) ^ n) v‖ ≤
            M * ‖U 0 - v‖ + M * (n * τ) * D + K * M * (n * τ) * τ ^ m * ‖(L ^ (m + 1)) v‖ :=
  ⟨hr.scheme.sharpConst m, fun L _ hL _ hτ n v => norm_rationalApply_pow_sub_le hτ L hL hr hm n v⟩

/-- **Stability and consistency give convergence for every datum**:
`Feec.TimeStepping.BanachFEEC.TimeScheme.converges`. -/
theorem converges {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E)
    (hS : IsC0Semigroup S) {κ : Type*} (l : Filter κ) (X : κ → Type*)
    [∀ h, NormedAddCommGroup (X h)] [∀ h, NormedSpace 𝕜 (X h)] [∀ h, CompleteSpace (X h)]
    [∀ h, NormedSpace ℝ (X h)] [∀ h, IsScalarTower ℝ 𝕜 (X h)] (L : ∀ h, X h →L[𝕜] X h) (M : ℝ)
    (hL : ∀ h (t : ℝ), 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L h)‖ ≤ M)
    (hSM : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) (ι : ∀ h, X h →L[𝕜] E) (π : ∀ h, E →L[𝕜] X h)
    (hπι : ∀ h x, π h (ι h x) = x) (hC : ∃ C, ∀ h, ‖ι h‖ ≤ C ∧ ‖π h‖ ≤ C) (τ : κ → ℝ)
    (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0)) (P : ∀ h, X h →L[𝕜] X h) (Ms : ℝ → ℝ)
    (hP : ∀ (T : ℝ) (h : κ) (n : ℕ), n * τ h ≤ T → ‖P h ^ n‖ ≤ Ms T) {p : ℕ} (hp : 0 < p)
    {K : ℝ} (hK : 0 ≤ K) (hcons : ∀ h (y : X h), ‖P h y - NormedSpace.exp ((τ h : 𝕜) • L h) y‖ ≤
      K * τ h ^ (p + 1) * ‖(L h ^ (p + 1)) y‖) (x : E) (v : ∀ h, X h)
    (hsd : ∀ T : ℝ, TendstoUniformlyOn
      (fun h (t : ℝ) => ι h (NormedSpace.exp ((t : 𝕜) • L h) (v h))) (fun t => S t x) l (Icc 0 T))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T → ‖S (n * τ h) x - ι h ((P h ^ n) (v h))‖ < ε := by
  let B : BanachFEEC hS.toC0 κ :=
    { X := X, L := L, M := M, norm_exp_le := hL, l := l, incl := ι, proj := π,
      proj_incl := hπι, bound := hC, norm_S_le := hSM }
  let Θ : B.TimeScheme :=
    { τ := τ, τ_pos := hτ, P := P, M := Ms, stable := hP, p := p, p_pos := hp, K := K,
      K_nonneg := hK, consistent := hcons }
  exact Θ.converges (x := x) (v := v) hsd hτ0 T hε

/-- **Backward Euler converges for every datum**: `Feec.TimeStepping.StableFamily.backwardEuler`
in `Feec.TimeStepping.BanachFEEC.TimeScheme.converges`. -/
theorem converges_backwardEuler {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (S : ℝ → E →L[𝕜] E) (hS : IsC0Semigroup S) {κ : Type*} (l : Filter κ) (X : κ → Type*)
    [∀ h, NormedAddCommGroup (X h)] [∀ h, NormedSpace 𝕜 (X h)] [∀ h, CompleteSpace (X h)]
    [∀ h, NormedSpace ℝ (X h)] [∀ h, IsScalarTower ℝ 𝕜 (X h)] (L : ∀ h, X h →L[𝕜] X h) (M : ℝ)
    (hL : ∀ h (t : ℝ), 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L h)‖ ≤ M)
    (hSM : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) (ι : ∀ h, X h →L[𝕜] E) (π : ∀ h, E →L[𝕜] X h)
    (hπι : ∀ h x, π h (ι h x) = x) (hC : ∃ C, ∀ h, ‖ι h‖ ≤ C ∧ ‖π h‖ ≤ C) (τ : κ → ℝ)
    (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0)) (x : E) (v : ∀ h, X h)
    (hsd : ∀ T : ℝ, TendstoUniformlyOn
      (fun h (t : ℝ) => ι h (NormedSpace.exp ((t : 𝕜) • L h) (v h))) (fun t => S t x) l (Icc 0 T))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T →
      ‖S (n * τ h) x - ι h ((Ring.inverse (1 - (τ h : 𝕜) • L h) ^ n) (v h))‖ < ε := by
  let B : BanachFEEC hS.toC0 κ :=
    { X := X, L := L, M := M, norm_exp_le := hL, l := l, incl := ι, proj := π,
      proj_incl := hπι, bound := hC, norm_S_le := hSM }
  let Θ : B.TimeScheme := B.toStableFamily.backwardEuler τ hτ
  filter_upwards [Θ.converges (x := x) (v := v) hsd hτ0 T hε] with h hh n hn
  have e : Ring.inverse (1 - (τ h : 𝕜) • L h) = Θ.P h :=
    (inverse_eq_res B.toStableFamily (hτ h) h).trans
      (B.toStableFamily.step_theta_one (τ h) h).symm
  rw [e]
  exact hh n hn

/-! ### The heat equation in the maximum norm -/

/-- **Sub-Markov generators are contractive in the maximum norm**: the sub-Markov facts of
`Feec.ForMathlib.Analysis.SubMarkov`, backward Euler through `TimeStepping.exists_res`. -/
theorem subMarkov {ι : Type*} [Fintype ι] {L : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hL : IsSubMarkovGenerator L) :
    (∀ t : ℝ, 0 ≤ t → (∀ v, 0 ≤ v → 0 ≤ NormedSpace.exp (t • L) v) ∧
      ‖NormedSpace.exp (t • L)‖ ≤ 1) ∧
    ∀ τ : ℝ, 0 < τ → IsUnit (1 - τ • L) ∧ (∀ v, 0 ≤ v → 0 ≤ Ring.inverse (1 - τ • L) v) ∧
      ‖Ring.inverse (1 - τ • L)‖ ≤ 1 := by
  have hL' := hL.toFeec
  refine ⟨fun t ht => ⟨fun v hv => hL'.exp_smul_apply_nonneg ht hv,
    hL'.norm_exp_smul_le_one ht⟩, fun τ hτ => ?_⟩
  obtain ⟨R, h1, h2, h3⟩ := exists_res (𝕜 := ℝ) L (M := 1)
    (fun t ht => by simpa using hL'.norm_exp_smul_le_one ht) hτ
  simp only [RCLike.ofReal_real_eq_id, id] at h1 h2
  rw [show Ring.inverse (1 - τ • L) = R from Ring.inverse_unit ⟨_, R, h2, h1⟩]
  refine ⟨⟨⟨_, R, h2, h1⟩, rfl⟩, fun v hv => hL'.nonneg_of_sub_smul_apply_nonneg hτ.le ?_, h3⟩
  have e : R v - τ • L (R v) = v := by simpa using ContinuousLinearMap.ext_iff.1 h2 v
  rw [e]
  exact hv

/-- **The lumped-mass heat equation on non-obtuse meshes**: the discrete maximum principle
`Feec.FiniteElement.isSubMarkovGenerator_lumpedLaplacianOn`, then `subMarkov` and the
bounded-generator bounds with `M = 1`. -/
theorem maxNormHeat (p q : ℝ[X]) (hr : IsAStable p q) :
    ∃ (C : ℝ) (K : ℕ → ℝ), 0 ≤ C ∧ ∀ (n : ℕ) (M : SimplicialMesh n), IsNonobtuse M →
      ∀ {ι : Type*} [Fintype ι] (x : ι → Fin n → ℝ), Function.Injective x →
        IsSubMarkovGenerator (lumpedLaplacian M x) ∧
        (∀ τ : ℝ, 0 < τ → ∀ k : ℕ,
          ‖rationalApply p q (τ • lumpedLaplacian M x) ^ k‖ ≤ 1 + C * √k) ∧
        (∀ τ : ℝ, 0 < τ → ∀ (k : ℕ) (u u₁ u₂ : ℝ → (Fin n → ℝ) → ℝ) (B ε : ℝ) (v : ι → ℝ),
          (∀ s ∈ Icc 0 (k * τ), ∀ i, HasDerivAt (fun s => u s (x i)) (u₁ s (x i)) s) →
          (∀ s ∈ Icc 0 (k * τ), ∀ i, HasDerivAt (fun s => u₁ s (x i)) (u₂ s (x i)) s) →
          (∀ s ∈ Icc 0 (k * τ), ‖u₂ s ∘ x‖ ≤ B) →
          (∀ s ∈ Icc 0 (k * τ), ‖u₁ s ∘ x - lumpedLaplacian M x (u s ∘ x)‖ ≤ ε) →
          ‖u (k * τ) ∘ x - (Ring.inverse (1 - τ • lumpedLaplacian M x) ^ k) v‖ ≤
            ‖u 0 ∘ x - v‖ + k * τ * (3 / 2 * τ * B + ε)) ∧
        ∀ m : ℕ, HasOrder p q m → ∀ τ : ℝ, 0 < τ → ∀ (k : ℕ) (u u₁ : ℝ → (Fin n → ℝ) → ℝ)
          (ε : ℝ) (v : ι → ℝ),
          (∀ s ∈ Icc 0 (k * τ), ∀ i, HasDerivAt (fun s => u s (x i)) (u₁ s (x i)) s) →
          (∀ s ∈ Icc 0 (k * τ), ‖u₁ s ∘ x - lumpedLaplacian M x (u s ∘ x)‖ ≤ ε) →
          ‖u (k * τ) ∘ x - (rationalApply p q (τ • lumpedLaplacian M x) ^ k) v‖ ≤
            ‖u 0 ∘ x - v‖ + k * τ * ε +
              K m * (k * τ) * τ ^ m * ‖(lumpedLaplacian M x ^ (m + 1)) v‖ := by
  refine ⟨hr.scheme.sqrtConst, hr.scheme.sharpConst, hr.scheme.sqrtConst_nonneg, ?_⟩
  intro n M hM ι _ x hx
  have hL : IsSubMarkovGenerator (lumpedLaplacian M x) := by
    rw [lumpedLaplacian_eq]
    exact .ofFeec (Feec.FiniteElement.isSubMarkovGenerator_lumpedLaplacianOn
      ((isNonobtuse_iff M).1 hM) hx)
  have h1 : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((RCLike.ofReal t : ℝ) • lumpedLaplacian M x)‖ ≤ 1 :=
    fun t ht => by simpa using hL.toFeec.norm_exp_smul_le_one ht
  refine ⟨hL, fun τ hτ k => ?_, fun τ hτ k u u₁ u₂ B ε v hu hu₁ hB hε => ?_,
    fun m hm τ hτ k u u₁ ε v hu hε => ?_⟩
  · simpa using (norm_rationalApply_pow_le (𝕜 := ℝ) hτ (lumpedLaplacian M x) h1 hr).2 k
  · have h := norm_sub_inverse_pow_le (𝕜 := ℝ) hτ (lumpedLaplacian M x) h1
      (U := fun s => u s ∘ x) (U₁ := fun s => u₁ s ∘ x) (U₂ := fun s => u₂ s ∘ x)
      (fun s hs => hasDerivAt_pi.2 (hu s hs)) (fun s hs => hasDerivAt_pi.2 (hu₁ s hs)) hB hε v
    simpa using h
  · have h := (norm_rationalApply_pow_sub_le (𝕜 := ℝ) hτ (lumpedLaplacian M x) h1 hr hm k v).2
      (fun s => u s ∘ x)
      (fun s => u₁ s ∘ x) ε (fun s hs => hasDerivAt_pi.2 (hu s hs)) hε
    simpa using h

/-- **The discrete maximum principle for finite differences**:
`FiniteDifference.isSubMarkovGenerator_laplacian`. -/
theorem isSubMarkovGenerator_fdLaplacian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset (ι → ℤ)) (h : ℝ) : IsSubMarkovGenerator (fdLaplacian G h) := by
  rw [fdLaplacian_eq]
  exact .ofFeec (FiniteDifference.isSubMarkovGenerator_laplacian G h)

/-- **The heat equation in the maximum norm by finite differences**: the Freudenthal mesh
`Feec.Mesh.freudenthalMesh`, whose lumped-mass Laplacian is the finite difference Laplacian
(`Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian_eq`), and the compatible-data estimate
`Feec.Models.Cube.FiniteDifferenceHeat.rational_compatible`, the classical solution as a
`Feec.Models.Cube.MaxNormHeat.HeatSolution`. -/
theorem fdHeat :
    (∀ (n N : ℕ) (b : Fin n → ℝ) (s : ℝ), 0 < s → ∃ M : SimplicialMesh n,
      M.domain = univ.pi (fun i => Ioo (b i) (b i + s)) ∧ IsNonobtuse M ∧
      lumpedLaplacian M (fun g : gridNodes n N => gridPoint b (s / (N + 1 : ℕ)) g) =
        fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ))) ∧
    ∀ p q : ℝ[X], IsAStable p q → ∀ m : ℕ, HasOrder p q m →
    ∃ K : ℝ, ∀ (n : ℕ) (b : Fin n → ℝ) (s T B B' : ℝ) (u u₁ : ℝ → (Fin n → ℝ) → ℝ)
      (ũ : (Fin n → ℝ) → ℝ), 0 < s →
      (∀ t ∈ Icc 0 T, ContDiff ℝ 4 (u t)) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Ioo (b i) (b i + s),
        HasDerivAt (fun t => u t x) (u₁ t x) t ∧
          u₁ t x = ∑ i, partialDeriv i (partialDeriv i (u t)) x) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s),
        x ∉ univ.pi (fun i => Ioo (b i) (b i + s)) → u t x = 0) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ∀ i,
        |(partialDeriv i)^[4] (u t) x| ≤ B) →
      ContDiff ℝ (2 * m + 2) ũ → (∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ũ x = u 0 x) →
      (∀ i x, ũ (Function.update x i (2 * b i - x i)) = -ũ x ∧
        ũ (Function.update x i (2 * (b i + s) - x i)) = -ũ x) →
      (∀ (l : Fin (m + 1) → Fin n) x,
        |(List.ofFn l).foldr (fun i f => partialDeriv i (partialDeriv i f)) ũ x| ≤ B') →
      ∀ (N : ℕ) (τ : ℝ), 0 < τ → ∀ k : ℕ, k * τ ≤ T →
        ‖gridInterp b (s / (N + 1 : ℕ)) N (u (k * τ)) -
            (rationalApply p q (τ • fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ))) ^ k)
              (gridInterp b (s / (N + 1 : ℕ)) N (u 0))‖ ≤
          k * τ * (n * B * (s / (N + 1 : ℕ)) ^ 2 / 12 + K * n ^ (m + 1) * B' * τ ^ m) := by
  refine ⟨fun n N b s hs => ⟨SimplicialMesh.ofFeec (Feec.Mesh.freudenthalMesh b s hs (N + 1)),
    Feec.Mesh.freudenthalMesh_domain b s hs (N + 1), ?_, ?_⟩, fun p q hr m hm => ?_⟩
  · rw [isNonobtuse_iff, SimplicialMesh.toFeec_ofFeec]
    exact Feec.FiniteElement.isNonobtuse_freudenthalMesh b hs (N + 1)
  · rw [lumpedLaplacian_eq, SimplicialMesh.toFeec_ofFeec, fdLaplacian_eq]
    exact (Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian_eq b hs N).symm
  refine ⟨hr.scheme.sharpConst m, ?_⟩
  intro n b s T B B' u u₁ ũ hs hu hh hbd hB hũ hũu hodd hB' N τ hτ k hk
  let S : Feec.Models.Cube.MaxNormHeat.HeatSolution b s T :=
    { u := u, u₁ := u₁, contDiff := hu, hasDerivAt := fun t ht x hx => (hh t ht x hx).1,
      heat := fun t ht x hx => (hh t ht x hx).2, boundary := hbd, B₄ := B, bound₄ := hB }
  have H := Feec.Models.Cube.FiniteDifferenceHeat.rational_compatible hs S hr.scheme_isAStable
    (hr.scheme_hasOrder hm) hũ (fun i => ⟨fun x => (hodd i x).1, fun x => (hodd i x).2⟩) hũu hB'
    N hτ hk
  have e := (step_eq (Feec.Models.Cube.FiniteDifferenceHeat.family n s) hτ N hr.scheme).2
  simp only [RCLike.ofReal_real_eq_id, id] at e
  rw [e, show Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian s N =
    fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ)) from (fdLaplacian_eq _ _).symm] at H
  exact H

/-! ### The hypotheses on `r` are met -/

/-- **Backward Euler** `r(z) = 1/(1 - z)` is A-stable of order `1`. -/
theorem backwardEuler_isAStable : IsAStable 1 (1 - X) ∧ HasOrder 1 (1 - X) 1 := by
  refine ⟨fun z hz => ?_, hasOrder_of_dvd (by simp) ⟨1, by
    simp [expTaylor, Finset.sum_range_succ]; ring⟩⟩
  have h1 : 1 ≤ ‖1 - z‖ := by
    have := Complex.re_le_norm (1 - z)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  have h0 : (1 : ℂ) - z ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  simp only [map_one, map_sub, aeval_X]
  refine ⟨h0, ?_⟩
  rw [norm_div, norm_one, div_le_one (by positivity)]
  exact h1

/-- **Crank–Nicolson** `r(z) = (2 + z)/(2 - z)` is A-stable (with `|r(∞)| = 1`) of order `2`. -/
theorem crankNicolson_isAStable : IsAStable (2 + X) (2 - X) ∧ HasOrder (2 + X) (2 - X) 2 := by
  refine ⟨fun z hz => ?_, hasOrder_of_dvd (by rw [map_sub, aeval_X, map_ofNat]; norm_num)
    ⟨C (1 / 2), Polynomial.funext fun x => by
      simp [expTaylor, Finset.sum_range_succ, Nat.factorial]; ring⟩⟩
  have hsq : ‖2 + z‖ ^ 2 ≤ ‖2 - z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, Complex.re_ofNat,
      Complex.im_ofNat]
    nlinarith
  have h2 : 2 ≤ ‖2 - z‖ := by
    have := Complex.re_le_norm (2 - z)
    simp only [Complex.sub_re, Complex.re_ofNat] at this
    linarith
  have h0 : (2 : ℂ) - z ≠ 0 := fun h => by rw [h, norm_zero] at h2; linarith
  simp only [map_add, map_sub, map_ofNat, aeval_X]
  refine ⟨h0, ?_⟩
  rw [norm_div, div_le_one (by positivity)]
  nlinarith [norm_nonneg ((2 : ℂ) + z), norm_nonneg ((2 : ℂ) - z)]

end TimeStepping
