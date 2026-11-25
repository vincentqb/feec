module

public import Solution.Bridge
public import Solution.Lumped

/-!
# A-stable rational time stepping for `C₀`-semigroups (solution)

The theorems of `Challenge.lean`, proved from `Feec` through the bridges `Solution.Bridge` (the
rational schemes, semigroups, bounded generators and sub-Markov generators) and `Solution.Lumped`
(meshes and the lumped-mass `P₁` Laplacian).

* Banach spaces: Brenner–Thomée's stability bound from
  `Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable`
  (the Hille–Phillips calculus on the complexification) and the sharp error from
  `Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`
  (Brenner–Thomée's error kernel, `Feec.HalfLineAlgebra.integral_norm_errorKernel_le`); for
  bounded generators, the bounds of `Feec.TimeStepping.StableFamily` for a one-member family
  (`TimeStepping.norm_rationalApply_pow_le`, `TimeStepping.norm_rationalApply_pow_sub_le`);
  backward Euler from the resolvent `Feec.C0Semigroup.isResolvent_resolvent_ofReal`,
  `Feec.TimeStepping.norm_pow_le_of_generator` and
  `Feec.TimeStepping.RationalScheme.norm_backwardEuler_pow_sub_S_le`.
* Hilbert spaces: `Feec.TimeStepping.RationalScheme.norm_step_le` with
  `Feec.TimeStepping.RationalScheme.step_eq_resolventEval`.
* Convergence: `Feec.TimeStepping.BanachFEEC.TimeScheme.converges`, with
  `Feec.TimeStepping.StableFamily.backwardEuler` for backward Euler and, on Hilbert spaces, the
  inner product of the parallelogram law (`InnerProductSpace.ofNorm`), in which a generator of
  contractions is dissipative (`Feec.TimeStepping.re_inner_le_zero_of_norm_exp_le_one`), so that
  `Feec.TimeStepping.RationalScheme.norm_apply_le_one` bounds the scheme.
* The maximum norm: `IsSubMarkovGenerator.norm_exp_smul_le_one` and the other sub-Markov facts of
  `Feec.ForMathlib.Analysis.SubMarkov`; the second-order nodal consistency of the lumped-mass
  Laplacian where the mesh is translation invariant,
  `Feec.FiniteElement.abs_lumpedLaplacianOn_sub_laplacian_le`, and its failure on the
  cross-polytope mesh `Feec.FiniteElement.crossMesh`; the discrete maximum principle
  `Feec.FiniteElement.isSubMarkovGenerator_lumpedLaplacianOn` and
  `FiniteDifference.isSubMarkovGenerator_laplacian`; the Freudenthal mesh
  `Feec.Mesh.freudenthalMesh`, non-obtuse by `Feec.FiniteElement.isNonobtuse_freudenthalMesh`
  and translation invariant at the interior nodes by
  `Feec.FiniteElement.isTranslationInvariantAt_freudenthalMesh`, whose lumped-mass Laplacian is
  the finite difference Laplacian
  (`Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian_eq`); the derivatives of the challenge as
  partial derivatives (`iteratedFDeriv_apply_single_eq_iterate`,
  `FiniteDifference.iteratedFDeriv_apply_pairs`); and the compatible-data estimate
  `Feec.Models.Cube.FiniteDifferenceHeat.rational_compatible`.
* The schemes that meet the hypotheses: the maximum principle
  `Feec.TimeStepping.RationalScheme.isAStable_iff_forall_re_nonpos` (`TimeStepping.isAStable_iff`),
  the θ-schemes exactly (`Feec.TimeStepping.X_pow_dvd_theta_iff`), the symmetric schemes
  (`Feec.TimeStepping.RationalScheme.IsSymmetric.norm_apply_apply`); the Runge–Kutta methods from
  `Feec.TimeStepping.ButcherTableau.existsUnique_isStage` and
  `Feec.TimeStepping.ButcherTableau.IsStage.add_smul_sum_eq`, and the instances of
  `Feec.TimeStepping.RungeKutta` with their exact orders (`Feec.TimeStepping.AStableSchemes`).
* The inputs: the Hille–Yosida estimates from `Feec.C0Semigroup.isResolvent_resolvent` and
  `Feec.C0Semigroup.norm_resolvent_pow_le`; von Neumann's inequality from
  `ContinuousLinearMap.norm_aeval_mul_inverse_le`; the Lumer–Phillips theorem from
  `LinearPMap.IsMDissipative.semigroup` and
  `Feec.C0Semigroup.IsContraction.isMDissipative_generator`.

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Gomilko, Y. Tomilov, *Rational Approximation of Operator Semigroups via the B-Calculus*][GomilkoTomilov2024],
  Thm 1.1
* [E. Hairer, G. Wanner, *Solving Ordinary Differential Equations II*][HairerWanner1996], §IV.3,
  §IV.5, §IV.6, §IV.11
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4, §1.5, §3.4
* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7, 15
* [P. G. Ciarlet, P.-A. Raviart, *Maximum principle and uniform convergence for the finite element method*][CiarletRaviart1973]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Polynomial Asymptotics Filter Set Feec.TimeStepping

@[expose] public noncomputable section

namespace TimeStepping

/-! ### Banach spaces: Brenner–Thomée -/

/-- **Brenner–Thomée's stability bound** ([BrennerThomee1979]), with the constant `sqrtConst` of
`Feec` for semigroups and for bounded generators. -/
theorem stable (p q : ℝ[X]) (hr : IsAStable p q) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
        [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (M : ℝ),
        IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) → ∀ τ : ℝ, 0 < τ → ∃ R : E →L[𝕜] E,
          (∀ T : E →L[𝕜] E,
            (∀ x y : E, (x, y) ∈ generatorGraph S → T (x - (τ : 𝕜) • y) = x) ↔ T = R) ∧
          IsUnit (resolventPoly q.natDegree q R) ∧
          ∀ n : ℕ, ‖rationalOfResolvent p q R ^ n‖ ≤ M * (1 + C * √n)) ∧
      ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
        (L : X →L[𝕜] X) (M : ℝ), (∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ M) →
        ∀ τ : ℝ, 0 < τ → IsUnit (aeval ((τ : 𝕜) • L) (q.map (algebraMap ℝ 𝕜))) ∧
          ∀ n : ℕ, ‖rationalApply p q ((τ : 𝕜) • L) ^ n‖ ≤ M * (1 + C * √n) := by
  refine ⟨hr.scheme.sqrtConst, hr.scheme.sqrtConst_nonneg, ?_, ?_⟩
  · intro 𝕜 E _ _ _ _ _ _ S M hS hM τ hτ
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
  · intro 𝕜 X _ _ _ _ L M hL τ hτ
    let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
    have : IsScalarTower ℝ 𝕜 X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact norm_rationalApply_pow_le hτ L hL hr

/-- **Brenner–Thomée's smooth-data error estimate** ([BrennerThomee1979]; [GomilkoTomilov2024],
Thm 1.1(ii)), with the constant `sharpConst` of `Feec` for semigroups and for bounded generators,
and along trajectories. -/
theorem error (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
    ∃ K : ℝ,
      (∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
        [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E) (M : ℝ),
        IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) → ∀ τ : ℝ, 0 < τ → ∀ R : E →L[𝕜] E,
          (∀ x y : E, (x, y) ∈ generatorGraph S → R (x - (τ : 𝕜) • y) = x) →
          ∀ (n : ℕ) (u : ℕ → E), (∀ j < m + 1, (u j, u (j + 1)) ∈ generatorGraph S) →
            ‖(rationalOfResolvent p q R ^ n) (u 0) - S (n * τ) (u 0)‖ ≤
              K * M * (n * τ) * τ ^ m * ‖u (m + 1)‖) ∧
      ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
        [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] (L : X →L[𝕜] X) (M : ℝ),
        (∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L)‖ ≤ M) → ∀ τ : ℝ, 0 < τ →
        ∀ (n : ℕ) (v : X),
          ‖(rationalApply p q ((τ : 𝕜) • L) ^ n) v -
              NormedSpace.exp (((n * τ : ℝ) : 𝕜) • L) v‖ ≤
            K * M * (n * τ) * τ ^ m * ‖(L ^ (m + 1)) v‖ ∧
          ∀ (U U' : ℝ → X) (D : ℝ), (∀ s ∈ Icc 0 (n * τ), HasDerivAt U (U' s) s) →
            (∀ s ∈ Icc 0 (n * τ), ‖U' s - L (U s)‖ ≤ D) →
            ‖U (n * τ) - (rationalApply p q ((τ : 𝕜) • L) ^ n) v‖ ≤
              M * ‖U 0 - v‖ + M * (n * τ) * D + K * M * (n * τ) * τ ^ m * ‖(L ^ (m + 1)) v‖ := by
  refine ⟨hr.scheme.sharpConst m, ?_,
    fun L _ hL _ hτ n v => norm_rationalApply_pow_sub_le hτ L hL hr hm n v⟩
  intro 𝕜 E _ _ _ _ _ _ S M hS hM τ hτ R hR n u hu
  set G := hS.toC0
  have h := RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent G hM
    hr.scheme_isAStable (hr.scheme_hasOrder hm) hτ
    (fun x y hxy => hR x y ((mem_graph_iff G).1 hxy)) n (u := u)
    fun j hj => (mem_graph_iff G).2 (hu j hj)
  rwa [resolventStep_eq hr] at h

/-- **Backward Euler is power bounded on every Banach space**: the resolvent of
`Feec.C0Semigroup.isResolvent_resolvent_ofReal`, `Feec.TimeStepping.norm_pow_le_of_generator`
and `Feec.TimeStepping.RationalScheme.norm_backwardEuler_pow_sub_S_le`. -/
theorem backwardEuler {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E)
    (hS : IsC0Semigroup S) {M ω : ℝ} (hω : 0 ≤ ω)
    (hSb : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t)) {τ : ℝ} (hτ : 0 < τ)
    (hωτ : ω * τ < 1) :
    ∃ R : E →L[𝕜] E,
      (∀ T : E →L[𝕜] E,
        (∀ x y : E, (x, y) ∈ generatorGraph S → T (x - (τ : 𝕜) • y) = x) ↔ T = R) ∧
      (∀ k : ℕ, ‖R ^ k‖ ≤ M / (1 - ω * τ) ^ k) ∧
      ∀ (n : ℕ) (u : ℕ → E), (∀ j < 2, (u j, u (j + 1)) ∈ generatorGraph S) →
        ‖(R ^ n) (u 0) - S (n * τ) (u 0)‖ ≤ M / (1 - ω * τ) ^ n *
          (M / (1 - ω * τ) + M * Real.exp (ω * (n * τ)) / 2) * (M * Real.exp (ω * (n * τ))) *
            (n * τ) * τ * ‖u 2‖ := by
  set G := hS.toC0
  have hres := G.isResolvent_resolvent_ofReal hSb
    (show ω < τ⁻¹ by rw [← one_div]; exact (lt_div_iff₀ hτ).2 hωτ)
  rw [RCLike.ofReal_inv] at hres
  set R := (τ : 𝕜)⁻¹ • Feec.Operator.resolvent G.generator (τ : 𝕜)⁻¹
  have hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x :=
    fun x y hxy => hres.inv_smul_apply_sub hτ.ne' hxy
  refine ⟨R, fun T => ⟨fun hT => hres.eq_inv_smul_of_apply_sub hτ.ne'
    fun x y hxy => hT x y ((mem_graph_iff G).1 hxy), fun hT => ?_⟩,
    norm_pow_le_of_generator G hSb hτ hωτ hR, fun n u hu =>
    RationalScheme.norm_backwardEuler_pow_sub_S_le G hω hSb hτ hωτ hR n
      fun j hj => (mem_graph_iff G).2 (hu j hj)⟩
  subst hT
  exact fun x y hxy => hR x y ((mem_graph_iff G).2 hxy)

/-! ### Hilbert spaces: von Neumann -/

/-- **Rational schemes for m-dissipative operators: von Neumann's theorem** ([HairerWanner1996],
§IV.11; [Pazy1983], §1.4). Let `A` be a possibly unbounded operator of a real or complex Hilbert
space, dissipative (`re ⟪A x, x⟫ ≤ 0` on its domain) with `μ - A` onto for some `μ > 0`
(m-dissipative: by `lumerPhillips`, the generator of a contraction semigroup), `r = p/q` a real
rational function with `q` free of zeros in the closed left half-plane, and `τ > 0`. Exactly one
bounded `R` satisfies `R (x - τAx) = x` on `D(A)` (the resolvent `(1 - τA)⁻¹`), `Q(R)` is
invertible, and `‖r(τA)ⁿ‖ ≤ (sup_y |r(iy)|)ⁿ` for every `n` (suprema in `[0, ∞]`; infinite when
`deg p > deg q`). For A-stable `r` this is `≤ 1`:
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

/-! ### Convergence for every datum: Lax -/

/-- **Stability and consistency give convergence for every datum**:
`Feec.TimeStepping.BanachFEEC.TimeScheme.converges`, for a time scheme of the challenge, for
backward Euler (`Feec.TimeStepping.StableFamily.backwardEuler`) and, on Hilbert spaces, for the
rational time scheme `Feec.TimeStepping.StableFamily.rationalScheme`, power bounded by
`Feec.TimeStepping.RationalScheme.norm_apply_le_one` in the inner product of the parallelogram
law. -/
theorem converges {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (S : ℝ → E →L[𝕜] E)
    (hS : IsC0Semigroup S) {κ : Type*} (l : Filter κ) (X : κ → Type*)
    [∀ h, NormedAddCommGroup (X h)] [∀ h, NormedSpace 𝕜 (X h)] [∀ h, CompleteSpace (X h)]
    [∀ h, NormedSpace ℝ (X h)] [∀ h, IsScalarTower ℝ 𝕜 (X h)] (L : ∀ h, X h →L[𝕜] X h) (M : ℝ)
    (hL : ∀ h (t : ℝ), 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • L h)‖ ≤ M)
    (hSM : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M) (ι : ∀ h, X h →L[𝕜] E) (π : ∀ h, E →L[𝕜] X h)
    (hπι : ∀ h x, π h (ι h x) = x) (hC : ∃ C, ∀ h, ‖ι h‖ ≤ C ∧ ‖π h‖ ≤ C) (τ : κ → ℝ)
    (hτ : ∀ h, 0 < τ h) (hτ0 : Tendsto τ l (𝓝 0)) (x : E) (v : ∀ h, X h)
    (hsd : ∀ T : ℝ, TendstoUniformlyOn
      (fun h (t : ℝ) => ι h (NormedSpace.exp ((t : 𝕜) • L h) (v h))) (fun t => S t x) l (Icc 0 T))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∀ (P : ∀ h, X h →L[𝕜] X h) (Ms : ℝ → ℝ),
      (∀ (t : ℝ) (h : κ) (n : ℕ), n * τ h ≤ t → ‖P h ^ n‖ ≤ Ms t) → ∀ {m : ℕ}, 0 < m →
      ∀ {K : ℝ}, 0 ≤ K → (∀ h (y : X h), ‖P h y - NormedSpace.exp ((τ h : 𝕜) • L h) y‖ ≤
        K * τ h ^ (m + 1) * ‖(L h ^ (m + 1)) y‖) →
      ∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T → ‖S (n * τ h) x - ι h ((P h ^ n) (v h))‖ < ε) ∧
    (∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T →
      ‖S (n * τ h) x - ι h ((Ring.inverse (1 - (τ h : 𝕜) • L h) ^ n) (v h))‖ < ε) ∧
    ((∀ h, InnerProductSpaceable (X h)) → M ≤ 1 → ∀ p q : ℝ[X], IsAStable p q →
      ∀ m : ℕ, HasOrder p q m → 0 < m →
      ∀ᶠ h in l, ∀ n : ℕ, n * τ h ∈ Icc 0 T →
        ‖S (n * τ h) x - ι h ((rationalApply p q ((τ h : 𝕜) • L h) ^ n) (v h))‖ < ε) := by
  let B : BanachFEEC hS.toC0 κ :=
    { X := X, L := L, M := M, norm_exp_le := hL, l := l, incl := ι, proj := π,
      proj_incl := hπι, bound := hC, norm_S_le := hSM }
  refine ⟨fun P Ms hP m hm K hK hcons => ?_, ?_, fun hX hM1 p q hr m hm hm0 => ?_⟩
  · let Θ : B.TimeScheme :=
      { τ := τ, τ_pos := hτ, P := P, M := Ms, stable := hP, p := m, p_pos := hm, K := K,
        K_nonneg := hK, consistent := hcons }
    exact Θ.converges (x := x) (v := v) hsd hτ0 T hε
  · let Θ : B.TimeScheme := B.toStableFamily.backwardEuler τ hτ
    filter_upwards [Θ.converges (x := x) (v := v) hsd hτ0 T hε] with h hh n hn
    have e : Ring.inverse (1 - (τ h : 𝕜) • L h) = Θ.P h :=
      (inverse_eq_res B.toStableFamily (hτ h) h).trans
        (B.toStableFamily.step_theta_one (τ h) h).symm
    rw [e]
    exact hh n hn
  · have e : ∀ h, B.toStableFamily.step hr.scheme (τ h) h =
        rationalApply p q ((τ h : 𝕜) • L h) :=
      fun h => (step_eq B.toStableFamily (hτ h) h hr.scheme).2
    have hP : ∀ h (n : ℕ), ‖B.toStableFamily.step hr.scheme (τ h) h ^ n‖ ≤ 1 := by
      intro h n
      rw [e h]
      let : InnerProductSpace 𝕜 (X h) := InnerProductSpace.ofNorm 𝕜 (hX h).parallelogram_identity
      have hd : ∀ y : X h, RCLike.re ⟪L h y, y⟫_𝕜 ≤ 0 :=
        re_inner_le_zero_of_norm_exp_le_one fun t ht => (hL h t ht).trans hM1
      exact Feec.TimeStepping.norm_pow_le_one (hr.scheme.norm_apply_le_one
        (RationalScheme.dissipative_smul hd (hτ h).le) hr.scheme_isAStable) n
    let Θ : B.TimeScheme := B.toStableFamily.rationalScheme hr.scheme hr.scheme_isAStable
      (hr.scheme_hasOrder hm) hm0 τ hτ (fun _ => 1) fun _ h n _ => hP h n
    filter_upwards [Θ.converges (x := x) (v := v) hsd hτ0 T hε] with h hh n hn
    rw [← e h]
    exact hh n hn

/-! ### Where the Banach theory is needed: the heat equation in the maximum norm -/

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
        (∀ τ : ℝ, 0 < τ → IsUnit (aeval (τ • lumpedLaplacian M x) q) ∧ ∀ k : ℕ,
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
  refine ⟨hL, fun τ hτ => ?_, fun τ hτ k u u₁ u₂ B ε v hu hu₁ hB hε => ?_,
    fun m hm τ hτ k u u₁ ε v hu hε => ?_⟩
  · have h := norm_rationalApply_pow_le (𝕜 := ℝ) hτ (lumpedLaplacian M x) h1 hr
    exact ⟨by simpa using h.1, fun k => by simpa using h.2 k⟩
  · have h := norm_sub_inverse_pow_le (𝕜 := ℝ) hτ (lumpedLaplacian M x) h1
      (U := fun s => u s ∘ x) (U₁ := fun s => u₁ s ∘ x) (U₂ := fun s => u₂ s ∘ x)
      (fun s hs => hasDerivAt_pi.2 (hu s hs)) (fun s hs => hasDerivAt_pi.2 (hu₁ s hs)) hB hε v
    simpa using h
  · have h := (norm_rationalApply_pow_sub_le (𝕜 := ℝ) hτ (lumpedLaplacian M x) h1 hr hm k v).2
      (fun s => u s ∘ x)
      (fun s => u₁ s ∘ x) ε (fun s hs => hasDerivAt_pi.2 (hu s hs)) hε
    simpa using h

/-- **The rate where the mesh is translation invariant at the nodes**: the second-order nodal
consistency `Feec.FiniteElement.abs_lumpedLaplacianOn_sub_laplacian_le`, then `maxNormHeat` with
the consistency error `n B h²/12`; the cross-polytope mesh `Feec.FiniteElement.crossMesh`
(`Feec.FiniteElement.isNonobtuse_crossMesh`), on which the error is `n (n - 1)/2`
(`Feec.FiniteElement.abs_lumpedLaplacianOn_crossMesh_sub_laplacian`). -/
theorem maxNormRate (p q : ℝ[X]) (hr : IsAStable p q) :
    (∃ K : ℕ → ℝ, ∀ (n : ℕ) (M : SimplicialMesh n), IsNonobtuse M →
      ∀ {ι : Type*} [Fintype ι] (x : ι → Fin n → ℝ), Function.Injective x →
      (∀ i, (∃ T ∈ M.simplices, x i ∈ vertexSet T) ∧ IsTranslationInvariantAt M (x i)) →
      ∀ h : ℝ, (∀ T ∈ M.simplices, ∀ j k, T.points j ∈ range x →
        (T.points k - T.points j) ⬝ᵥ (T.points k - T.points j) ≤ h ^ 2) →
      (∀ (u : (Fin n → ℝ) → ℝ) (B : ℝ), ContDiff ℝ 4 u →
        (∀ T ∈ M.simplices, ∀ j, T.points j ∉ range x → u (T.points j) = 0) →
        (∀ T ∈ M.simplices, ∀ y ∈ T.closedInterior, ∀ d,
          |iteratedFDeriv ℝ 4 u y (fun _ => d)| ≤ B * (d ⬝ᵥ d) ^ 2) →
        ∀ i, |∑ l, iteratedFDeriv ℝ 2 u (x i) (fun _ => Pi.single l 1) -
          lumpedLaplacian M x (u ∘ x) i| ≤ n * B * h ^ 2 / 12) ∧
      ∀ τ : ℝ, 0 < τ → ∀ (k : ℕ) (u : ℝ → (Fin n → ℝ) → ℝ) (B : ℝ) (v : ι → ℝ), 0 ≤ B →
        (∀ s ∈ Icc 0 (k * τ), ContDiff ℝ 4 (u s)) →
        (∀ s ∈ Icc 0 (k * τ), ∀ T ∈ M.simplices, ∀ j, T.points j ∉ range x →
          u s (T.points j) = 0) →
        (∀ s ∈ Icc 0 (k * τ), ∀ T ∈ M.simplices, ∀ y ∈ T.closedInterior, ∀ d,
          |iteratedFDeriv ℝ 4 (u s) y (fun _ => d)| ≤ B * (d ⬝ᵥ d) ^ 2) →
        (∀ s ∈ Icc 0 (k * τ), ∀ i, HasDerivAt (fun s => u s (x i))
          (∑ l, iteratedFDeriv ℝ 2 (u s) (x i) (fun _ => Pi.single l 1)) s) →
        (∀ (u₂ : ℝ → (Fin n → ℝ) → ℝ) (B₂ : ℝ),
          (∀ s ∈ Icc 0 (k * τ), ∀ i, HasDerivAt
            (fun s => ∑ l, iteratedFDeriv ℝ 2 (u s) (x i) (fun _ => Pi.single l 1))
            (u₂ s (x i)) s) →
          (∀ s ∈ Icc 0 (k * τ), ‖u₂ s ∘ x‖ ≤ B₂) →
          ‖u (k * τ) ∘ x - (Ring.inverse (1 - τ • lumpedLaplacian M x) ^ k) v‖ ≤
            ‖u 0 ∘ x - v‖ + k * τ * (3 / 2 * τ * B₂ + n * B * h ^ 2 / 12)) ∧
        ∀ m : ℕ, HasOrder p q m →
          ‖u (k * τ) ∘ x - (rationalApply p q (τ • lumpedLaplacian M x) ^ k) v‖ ≤
            ‖u 0 ∘ x - v‖ + k * τ * (n * B * h ^ 2 / 12) +
              K m * (k * τ) * τ ^ m * ‖(lumpedLaplacian M x ^ (m + 1)) v‖) ∧
    ∀ (n : ℕ) (h : ℝ), 0 < h → ∃ M : SimplicialMesh n,
      M.domain = {z | ∑ i, |z i| < h} ∧ IsNonobtuse M ∧
      (∃ T ∈ M.simplices, (0 : Fin n → ℝ) ∈ vertexSet T) ∧
      (∀ T ∈ M.simplices, ∀ j, T.points j ≠ 0 → T.points j ⬝ᵥ T.points j = h ^ 2) ∧
      |∑ l, iteratedFDeriv ℝ 2 (fun z : Fin n → ℝ => (z ⬝ᵥ z - h ^ 2) / 2) 0
          (fun _ => Pi.single l 1) -
        lumpedLaplacian M (fun _ : Unit => (0 : Fin n → ℝ))
          ((fun z : Fin n → ℝ => (z ⬝ᵥ z - h ^ 2) / 2) ∘ fun _ => 0) ()| = n * (n - 1) / 2 := by
  obtain ⟨C, K, -, hK⟩ := maxNormHeat p q hr
  refine ⟨⟨K, fun n M hM ι _ x hx hV h hh => ?_⟩, fun n h hh => ?_⟩
  swap
  · refine ⟨SimplicialMesh.ofFeec (Feec.FiniteElement.crossMesh hh), rfl, ?_, ?_, ?_, ?_⟩
    · rw [isNonobtuse_iff, SimplicialMesh.toFeec_ofFeec]
      exact Feec.FiniteElement.isNonobtuse_crossMesh hh
    · refine ⟨Feec.FiniteElement.orthantSimplex hh.ne' fun _ => true,
        (Feec.FiniteElement.mem_crossMesh_simplices hh).2 ⟨_, rfl⟩, ?_⟩
      rw [vertexSet_eq]
      exact Feec.Mesh.mem_vertexSet.2 ⟨0, Feec.FiniteElement.orthantSimplex_points_zero _ _⟩
    · intro T hT j hj
      obtain ⟨s, rfl⟩ := (Feec.FiniteElement.mem_crossMesh_simplices hh).1 hT
      induction j using Fin.cases with
      | zero => exact absurd (Feec.FiniteElement.orthantSimplex_points_zero _ _) hj
      | succ l =>
        rw [Feec.FiniteElement.orthantSimplex_points_succ, dotProduct_single, Pi.single_eq_same]
        linear_combination h ^ 2 * Feec.FiniteElement.boolSign_mul_self (s l)
    · have hu : ContDiff ℝ 2 fun z : Fin n → ℝ => (z ⬝ᵥ z - h ^ 2) / 2 := by
        simp only [dotProduct]
        fun_prop
      have hΔ : ∑ l, iteratedFDeriv ℝ 2 (fun z : Fin n → ℝ => (z ⬝ᵥ z - h ^ 2) / 2) 0
          (fun _ => Pi.single l 1) = laplacian (fun z : Fin n → ℝ => (z ⬝ᵥ z - h ^ 2) / 2) 0 := by
        rw [laplacian_apply]
        exact Finset.sum_congr rfl fun l _ =>
          iteratedFDeriv_apply_single_eq_iterate hu l (by norm_num) 0
      rw [hΔ, lumpedLaplacian_eq, SimplicialMesh.toFeec_ofFeec, abs_sub_comm]
      exact Feec.FiniteElement.abs_lumpedLaplacianOn_crossMesh_sub_laplacian hh
  have hcons : ∀ (u : (Fin n → ℝ) → ℝ) (B : ℝ), ContDiff ℝ 4 u →
      (∀ T ∈ M.simplices, ∀ j, T.points j ∉ range x → u (T.points j) = 0) →
      (∀ T ∈ M.simplices, ∀ y ∈ T.closedInterior, ∀ d,
        |iteratedFDeriv ℝ 4 u y (fun _ => d)| ≤ B * (d ⬝ᵥ d) ^ 2) →
      ∀ i, |∑ l, iteratedFDeriv ℝ 2 u (x i) (fun _ => Pi.single l 1) -
        lumpedLaplacian M x (u ∘ x) i| ≤ n * B * h ^ 2 / 12 := by
    intro u B hu hbd hB i
    have hΔ : ∑ l, iteratedFDeriv ℝ 2 u (x i) (fun _ => Pi.single l 1) = laplacian u (x i) := by
      rw [laplacian_apply]
      exact Finset.sum_congr rfl fun l _ =>
        iteratedFDeriv_apply_single_eq_iterate hu l (by norm_num) (x i)
    obtain ⟨T₀, hT₀, hy₀⟩ := (hV i).1
    rw [hΔ, lumpedLaplacian_eq, abs_sub_comm]
    refine Feec.FiniteElement.abs_lumpedLaplacianOn_sub_laplacian_le ((isNonobtuse_iff M).1 hM)
      hx ⟨T₀, hT₀, by rwa [← vertexSet_eq]⟩ ((isTranslationInvariantAt_iff M _).1 (hV i).2) hu
      (fun T hT _ v hv hvx => ?_) (fun T hT hy v hv => ?_)
      (fun T hT _ z hz d => hB T hT z hz d)
    · obtain ⟨j, rfl⟩ := Feec.Mesh.mem_vertexSet.1 hv
      exact hbd T hT j hvx
    · obtain ⟨j₀, hj₀⟩ := Feec.Mesh.mem_vertexSet.1 hy
      obtain ⟨k, rfl⟩ := Feec.Mesh.mem_vertexSet.1 hv
      have := hh T hT j₀ k ⟨i, hj₀.symm⟩
      rwa [hj₀] at this
  refine ⟨hcons, fun τ hτ k u B v hB0 hu hbd hB hd => ?_⟩
  have hε0 : (0 : ℝ) ≤ n * B * h ^ 2 / 12 := by positivity
  have hε : ∀ s ∈ Icc 0 (k * τ), ‖(fun z => ∑ l, iteratedFDeriv ℝ 2 (u s) z
      (fun _ => Pi.single l 1)) ∘ x - lumpedLaplacian M x (u s ∘ x)‖ ≤ n * B * h ^ 2 / 12 :=
    fun s hs => (pi_norm_le_iff_of_nonneg hε0).2 fun i => by
      rw [Real.norm_eq_abs]
      exact hcons (u s) B (hu s hs) (hbd s hs) (hB s hs) i
  have H := hK n M hM x hx
  exact ⟨fun u₂ B₂ hu₂ hB₂ => H.2.2.1 τ hτ k u _ u₂ B₂ _ v hd hu₂ hB₂ hε,
    fun m hm => H.2.2.2 m hm τ hτ k u _ _ v hd hε⟩

/-- **The heat equation in the maximum norm by finite differences**: the discrete maximum
principle `FiniteDifference.isSubMarkovGenerator_laplacian`; the Freudenthal mesh
`Feec.Mesh.freudenthalMesh`, whose lumped-mass Laplacian is the finite difference Laplacian
(`Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian_eq`), and the compatible-data estimate
`Feec.Models.Cube.FiniteDifferenceHeat.rational_compatible`, the classical solution as a
`Feec.Models.Cube.MaxNormHeat.HeatSolution` and its derivatives as partial derivatives
(`iteratedFDeriv_apply_single_eq_iterate`, `FiniteDifference.iteratedFDeriv_apply_pairs`); the
first eigenmode `Feec.Models.Cube.MaxNormHeat.sineSolution`, compatible to every order by
`Feec.Models.Cube.FiniteDifferenceHeat.sineSolution_compatible`. -/
theorem fdHeat :
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Finset (ι → ℤ)) (h : ℝ),
      IsSubMarkovGenerator (fdLaplacian G h)) ∧
    (∀ (n N : ℕ) (b : Fin n → ℝ) (s : ℝ), 0 < s → ∃ M : SimplicialMesh n,
      M.domain = univ.pi (fun i => Ioo (b i) (b i + s)) ∧ IsNonobtuse M ∧
      (∀ g : gridNodes n N, (∃ T ∈ M.simplices, gridPoint b (s / (N + 1 : ℕ)) g ∈ vertexSet T) ∧
        IsTranslationInvariantAt M (gridPoint b (s / (N + 1 : ℕ)) g)) ∧
      (∀ T ∈ M.simplices, ∀ j k,
        (T.points k - T.points j) ⬝ᵥ (T.points k - T.points j) ≤ n * (s / (N + 1 : ℕ)) ^ 2) ∧
      lumpedLaplacian M (fun g : gridNodes n N => gridPoint b (s / (N + 1 : ℕ)) g) =
        fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ))) ∧
    (∀ p q : ℝ[X], IsAStable p q → ∀ m : ℕ, HasOrder p q m →
    ∃ K : ℝ, ∀ (n : ℕ) (b : Fin n → ℝ) (s T B B' : ℝ) (u u₁ : ℝ → (Fin n → ℝ) → ℝ)
      (ũ : (Fin n → ℝ) → ℝ), 0 < s →
      (∀ t ∈ Icc 0 T, ContDiff ℝ 4 (u t)) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Ioo (b i) (b i + s),
        HasDerivAt (fun t => u t x) (u₁ t x) t ∧
          u₁ t x = ∑ i, iteratedFDeriv ℝ 2 (u t) x fun _ => Pi.single i 1) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s),
        x ∉ univ.pi (fun i => Ioo (b i) (b i + s)) → u t x = 0) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ∀ i,
        |iteratedFDeriv ℝ 4 (u t) x fun _ => Pi.single i 1| ≤ B) →
      ContDiff ℝ (2 * m + 2) ũ → (∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ũ x = u 0 x) →
      (∀ i x, ũ (Function.update x i (2 * b i - x i)) = -ũ x ∧
        ũ (Function.update x i (2 * (b i + s) - x i)) = -ũ x) →
      (∀ (l : ℕ → Fin n) x,
        |iteratedFDeriv ℝ (2 * m + 2) ũ x fun j => Pi.single (l ((j : ℕ) / 2)) 1| ≤ B') →
      ∀ (N : ℕ) (τ : ℝ), 0 < τ → ∀ k : ℕ, k * τ ≤ T →
        ‖gridInterp b (s / (N + 1 : ℕ)) N (u (k * τ)) -
            (rationalApply p q (τ • fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ))) ^ k)
              (gridInterp b (s / (N + 1 : ℕ)) N (u 0))‖ ≤
          k * τ * (n * B * (s / (N + 1 : ℕ)) ^ 2 / 12 + K * n ^ (m + 1) * B' * τ ^ m)) ∧
    ∀ (n m : ℕ) (b : Fin n → ℝ) (s T : ℝ), 0 < s →
      (∀ t ∈ Icc 0 T, ContDiff ℝ 4 (sineMode b s t)) ∧
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Ioo (b i) (b i + s),
        HasDerivAt (fun t => sineMode b s t x) (-(n * (Real.pi / s) ^ 2) * sineMode b s t x) t ∧
          -(n * (Real.pi / s) ^ 2) * sineMode b s t x =
            ∑ i, iteratedFDeriv ℝ 2 (sineMode b s t) x fun _ => Pi.single i 1) ∧
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s),
        x ∉ univ.pi (fun i => Ioo (b i) (b i + s)) → sineMode b s t x = 0) ∧
      (∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ∀ i,
        |iteratedFDeriv ℝ 4 (sineMode b s t) x fun _ => Pi.single i 1| ≤ (Real.pi / s) ^ 4) ∧
      ContDiff ℝ (2 * m + 2) (sineMode b s 0) ∧
      (∀ i x, sineMode b s 0 (Function.update x i (2 * b i - x i)) = -sineMode b s 0 x ∧
        sineMode b s 0 (Function.update x i (2 * (b i + s) - x i)) = -sineMode b s 0 x) ∧
      (∀ (l : ℕ → Fin n) x, |iteratedFDeriv ℝ (2 * m + 2) (sineMode b s 0) x
        fun j => Pi.single (l ((j : ℕ) / 2)) 1| ≤ (Real.pi / s) ^ (2 * m + 2)) ∧
      sineMode b s 0 (b + (s / 2) • fun _ => 1) = 1 := by
  refine ⟨fun G h => ?_, fun n N b s hs =>
    ⟨SimplicialMesh.ofFeec (Feec.Mesh.freudenthalMesh b s hs (N + 1)),
    Feec.Mesh.freudenthalMesh_domain b s hs (N + 1), ?_, fun g => ⟨?_, ?_⟩,
    fun T hT j k => Feec.FiniteElement.dotProduct_sub_le_freudenthalMesh b hs N hT j k, ?_⟩,
    fun p q hr m hm => ?_, fun n m b s T hs => ?_⟩
  · rw [fdLaplacian_eq]
    exact .ofFeec (FiniteDifference.isSubMarkovGenerator_laplacian G h)
  · rw [isNonobtuse_iff, SimplicialMesh.toFeec_ofFeec]
    exact Feec.FiniteElement.isNonobtuse_freudenthalMesh b hs (N + 1)
  · obtain ⟨T, hT, hy⟩ := Feec.FiniteElement.exists_mem_vertexSet_of_lumpedMass_pos _
      (Feec.Models.Cube.MaxNormHeat.lumpedMass_node_pos b hs ⟨g, g.2⟩)
    exact ⟨T, hT, by rw [vertexSet_eq]; exact hy⟩
  · rw [isTranslationInvariantAt_iff, SimplicialMesh.toFeec_ofFeec]
    exact Feec.FiniteElement.isTranslationInvariantAt_freudenthalMesh b hs N g.2
  · rw [lumpedLaplacian_eq, SimplicialMesh.toFeec_ofFeec, fdLaplacian_eq]
    exact (Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian_eq b hs N).symm
  swap
  · let S := Feec.Models.Cube.MaxNormHeat.sineSolution b hs T
    have hc := Feec.Models.Cube.FiniteDifferenceHeat.sineSolution_compatible b hs T
    refine ⟨fun t ht => S.contDiff t ht, fun t ht x hx => ⟨S.hasDerivAt t ht x hx, ?_⟩,
      fun t ht x hx hno => S.boundary t ht x hx hno, fun t ht x hx i => ?_,
      by exact_mod_cast contDiff_infty.1 hc.1 (2 * m + 2),
      fun i x => ⟨(hc.2.1 i).1 x, (hc.2.1 i).2 x⟩,
      fun l x => ?_, Feec.Models.Cube.MaxNormHeat.sineSolution_u_zero_center b hs T⟩
    · change S.u₁ t x = _
      rw [S.heat t ht x hx, laplacian_apply]
      exact Finset.sum_congr rfl fun i _ =>
        (iteratedFDeriv_apply_single_eq_iterate (S.contDiff t ht) i (p := 2) (by norm_num) x).symm
    · change |iteratedFDeriv ℝ 4 (S.u t) x _| ≤ _
      rw [iteratedFDeriv_apply_single_eq_iterate (S.contDiff t ht) i (by norm_num) x]
      exact S.bound₄ t ht x hx i
    · have h := hc.2.2 (List.ofFn fun i : Fin (m + 1) => l i) x
      rw [← FiniteDifference.iteratedFDeriv_apply_pairs (m := m + 1)
        (by exact_mod_cast contDiff_infty.1 hc.1 (2 * (m + 1))) l x, List.length_ofFn] at h
      exact h
  refine ⟨hr.scheme.sharpConst m, ?_⟩
  intro n b s T B B' u u₁ ũ hs hu hh hbd hB hũ hũu hodd hB' N τ hτ k hk
  have hheat : ∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Ioo (b i) (b i + s),
      u₁ t x = laplacian (u t) x := by
    intro t ht x hx
    rw [(hh t ht x hx).2, laplacian_apply]
    exact Finset.sum_congr rfl fun i _ =>
      iteratedFDeriv_apply_single_eq_iterate (hu t ht) i (by norm_num) x
  have hB₄ : ∀ t ∈ Icc 0 T, ∀ x ∈ univ.pi fun i => Icc (b i) (b i + s), ∀ i,
      |(partialDeriv i)^[4] (u t) x| ≤ B := fun t ht x hx i => by
    rw [← iteratedFDeriv_apply_single_eq_iterate (hu t ht) i (by norm_num) x]
    exact hB t ht x hx i
  have hB'' : ∀ (l : Fin (m + 1) → Fin n) x,
      |FiniteDifference.secondPartials (List.ofFn l) ũ x| ≤ B' := by
    intro l x
    set l' : ℕ → Fin n := fun j => l ⟨min j m, by omega⟩
    have e : List.ofFn l = List.ofFn fun i : Fin (m + 1) => l' i := by
      congr 1
      funext i
      congr 1
      ext
      exact (min_eq_left (Nat.lt_succ_iff.1 i.2)).symm
    rw [e, ← FiniteDifference.iteratedFDeriv_apply_pairs (m := m + 1) (by exact_mod_cast hũ) l' x]
    exact hB' l' x
  let S : Feec.Models.Cube.MaxNormHeat.HeatSolution b s T :=
    { u := u, u₁ := u₁, contDiff := hu, hasDerivAt := fun t ht x hx => (hh t ht x hx).1,
      heat := hheat, boundary := hbd, B₄ := B, bound₄ := hB₄ }
  have H := Feec.Models.Cube.FiniteDifferenceHeat.rational_compatible hs S hr.scheme_isAStable
    (hr.scheme_hasOrder hm) hũ (fun i => ⟨fun x => (hodd i x).1, fun x => (hodd i x).2⟩) hũu hB''
    N hτ hk
  have e := (step_eq (Feec.Models.Cube.FiniteDifferenceHeat.family n s) hτ N hr.scheme).2
  simp only [RCLike.ofReal_real_eq_id, id] at e
  rw [e, show Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian s N =
    fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ)) from (fdLaplacian_eq _ _).symm] at H
  exact H

/-! ### The hypotheses on `r` are met -/

/-- **The rational schemes that meet the hypotheses**: A-stability on the imaginary axis by the
maximum principle (`TimeStepping.isAStable_iff`), the θ-schemes exactly
(`Feec.TimeStepping.one_half_le_of_norm_theta_le`,
`Feec.TimeStepping.RationalScheme.isAStable_theta`, `Feec.TimeStepping.X_pow_dvd_theta_iff`), and
the symmetric schemes (`Feec.TimeStepping.RationalScheme.IsSymmetric.norm_eval`,
`Feec.TimeStepping.RationalScheme.IsSymmetric.norm_apply_apply`). -/
theorem schemes :
    (∀ p q : ℝ[X], IsAStable p q ↔ (∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) ∧
      ∀ y : ℝ, ‖aeval (y * Complex.I) p / aeval (y * Complex.I) q‖ ≤ 1) ∧
    (∀ θ : ℝ, (IsAStable (1 + C (1 - θ) * X) (1 - C θ * X) ↔ 1 / 2 ≤ θ) ∧
      ∀ m : ℕ, HasOrder (1 + C (1 - θ) * X) (1 - C θ * X) m ↔ m ≤ 1 ∨ θ = 1 / 2 ∧ m = 2) ∧
    ∀ q : ℝ[X], (∀ z : ℂ, z.re ≤ 0 → aeval z q ≠ 0) →
      IsAStable (q.comp (-X)) q ∧
      (∀ y : ℝ, ‖aeval (y * Complex.I) (q.comp (-X)) / aeval (y * Complex.I) q‖ = 1) ∧
      ∀ {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
        [CompleteSpace E] (L : E →L[𝕜] E), (∀ x, RCLike.re ⟪L x, x⟫_𝕜 = 0) →
        IsUnit (aeval L (q.map (algebraMap ℝ 𝕜))) ∧
          ∀ x, ‖rationalApply (q.comp (-X)) q L x‖ = ‖x‖ := by
  refine ⟨isAStable_iff, fun θ => ⟨⟨fun h => one_half_le_of_norm_theta_le (h _ (by simp)).2,
    fun hθ => (isAStable_iff _ _).2 ⟨(RationalScheme.theta θ (by linarith)).aeval_den_ne_zero,
      RationalScheme.isAStable_theta hθ⟩⟩, fun m => ?_⟩, fun q hq => ?_⟩
  · rw [hasOrder_iff_dvd (by simp)]
    exact X_pow_dvd_theta_iff θ m
  · let r : RationalScheme := ⟨q.comp (-X), q, by simp [natDegree_comp], hq⟩
    have hs : r.IsSymmetric := rfl
    exact ⟨(isAStable_iff _ _).2 ⟨hq, fun y => (hs.norm_eval y).le⟩, hs.norm_eval,
      fun L hL => ⟨r.isUnit_aeval_den fun x => (hL x).le, hs.norm_apply_apply hL⟩⟩

/-- **Runge–Kutta methods are rational schemes**: the stages and the step from
`Feec.TimeStepping.ButcherTableau.existsUnique_isStage` and
`Feec.TimeStepping.ButcherTableau.IsStage.add_smul_sum_eq`; the instances of
`Feec.TimeStepping.RungeKutta`, with their exact orders from `Feec.TimeStepping.AStableSchemes`. -/
theorem rungeKutta :
    (∀ {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) {𝕜 E : Type*} [RCLike 𝕜]
        [NormedAddCommGroup E] [NormedSpace 𝕜 E] (L : E →L[𝕜] E) (τ : ℝ),
        IsUnit (aeval ((τ : 𝕜) • L) ((stabilityDen A).map (algebraMap ℝ 𝕜))) →
        (∀ u : E, ∃! k : Fin s → E, ∀ i, k i = L (u + (τ : 𝕜) • ∑ j, (A i j : 𝕜) • k j)) ∧
        ∀ (u : E) (k : Fin s → E), (∀ i, k i = L (u + (τ : 𝕜) • ∑ j, (A i j : 𝕜) • k j)) →
          u + (τ : 𝕜) • ∑ i, (b i : 𝕜) • k i =
            rationalApply (stabilityNum A b) (stabilityDen A) ((τ : 𝕜) • L) u) ∧
    (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ),
      A = !![1 / 4, 1 / 4 - √3 / 6; 1 / 4 + √3 / 6, 1 / 4] → b = ![1 / 2, 1 / 2] →
      stabilityNum A b = 1 + C (1 / 2) * X + C (1 / 12) * X ^ 2 ∧
      stabilityDen A = 1 - C (1 / 2) * X + C (1 / 12) * X ^ 2 ∧
      stabilityNum A b = (stabilityDen A).comp (-X) ∧
      IsAStable (stabilityNum A b) (stabilityDen A) ∧
      HasOrder (stabilityNum A b) (stabilityDen A) 4 ∧
      ¬ HasOrder (stabilityNum A b) (stabilityDen A) 5) ∧
    (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ),
      A = !![5 / 12, -1 / 12; 3 / 4, 1 / 4] → b = ![3 / 4, 1 / 4] →
      stabilityNum A b = 1 + C (1 / 3) * X ∧
      stabilityDen A = 1 - C (2 / 3) * X + C (1 / 6) * X ^ 2 ∧
      IsAStable (stabilityNum A b) (stabilityDen A) ∧
      (stabilityNum A b).natDegree < (stabilityDen A).natDegree ∧
      HasOrder (stabilityNum A b) (stabilityDen A) 3 ∧
      ¬ HasOrder (stabilityNum A b) (stabilityDen A) 4) ∧
    ∀ (γ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ),
      γ = 1 - √2 / 2 → A = !![γ, 0; 1 - γ, γ] → b = ![1 - γ, γ] →
      stabilityNum A b = 1 + C (1 - 2 * γ) * X ∧
      stabilityDen A = (1 - C γ * X) ^ 2 ∧
      IsAStable (stabilityNum A b) (stabilityDen A) ∧
      (stabilityNum A b).natDegree < (stabilityDen A).natDegree ∧
      HasOrder (stabilityNum A b) (stabilityDen A) 2 ∧
      ¬ HasOrder (stabilityNum A b) (stabilityDen A) 3 := by
  refine ⟨fun A b 𝕜 E _ _ _ L τ h =>
    ⟨(ButcherTableau.mk A b).existsUnique_isStage h, fun u k hk =>
      ButcherTableau.IsStage.add_smul_sum_eq (T := ⟨A, b⟩) hk h⟩,
    ?_, ?_, ?_⟩
  · rintro A b rfl rfl
    have h0 := RationalScheme.gaussLegendre2.aeval_den_ne_zero 0 (by simp)
    exact ⟨ButcherTableau.gaussLegendre2_stabilityNum, ButcherTableau.gaussLegendre2_stabilityDen,
      RationalScheme.isSymmetric_gaussLegendre2,
      (isAStable_iff _ _).2 ⟨RationalScheme.gaussLegendre2.aeval_den_ne_zero,
        RationalScheme.isSymmetric_gaussLegendre2.isAStable⟩,
      (hasOrder_iff_dvd h0).2 RationalScheme.hasOrder_gaussLegendre2,
      fun h => RationalScheme.not_hasOrder_gaussLegendre2 ((hasOrder_iff_dvd h0).1 h)⟩
  · rintro A b rfl rfl
    have h0 := RationalScheme.radauIIA2.aeval_den_ne_zero 0 (by simp)
    have hn : stabilityNum _ _ = _ := ButcherTableau.radauIIA2_stabilityNum
    exact ⟨hn, ButcherTableau.radauIIA2_stabilityDen,
      (isAStable_iff _ _).2 ⟨RationalScheme.radauIIA2.aeval_den_ne_zero,
        RationalScheme.isAStable_radauIIA2⟩,
      natDegree_lt_natDegree (fun h => by simpa using congrArg (eval 0) (hn.symm.trans h))
        RationalScheme.isLStable_radauIIA2.2,
      (hasOrder_iff_dvd h0).2 RationalScheme.hasOrder_radauIIA2,
      fun h => RationalScheme.not_hasOrder_radauIIA2 ((hasOrder_iff_dvd h0).1 h)⟩
  · rintro γ A b rfl rfl rfl
    have h0 := RationalScheme.sdirk2.aeval_den_ne_zero 0 (by simp)
    have hn : stabilityNum _ _ = _ := ButcherTableau.sdirk2_stabilityNum
    refine ⟨hn, ?_,
      (isAStable_iff _ _).2 ⟨RationalScheme.sdirk2.aeval_den_ne_zero,
        RationalScheme.isAStable_sdirk2⟩,
      natDegree_lt_natDegree (fun h => by simpa using congrArg (eval 0) (hn.symm.trans h))
        RationalScheme.isLStable_sdirk2.2,
      (hasOrder_iff_dvd h0).2 RationalScheme.hasOrder_sdirk2,
      fun h => RationalScheme.not_hasOrder_sdirk2 ((hasOrder_iff_dvd h0).1 h)⟩
    rw [show stabilityDen !![1 - √2 / 2, 0; 1 - (1 - √2 / 2), 1 - √2 / 2] =
      ButcherTableau.sdirk2.stabilityDen from rfl, ButcherTableau.sdirk2_stabilityDen]
    simp only [map_mul, map_pow, map_ofNat, ButcherTableau.sdirk2Coeff]
    ring

/-! ### The classical inputs -/

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

/-- **The Lumer–Phillips theorem**: `LinearPMap.IsMDissipative.semigroup` with
`LinearPMap.IsMDissipative.isContraction_semigroup`, `LinearPMap.IsMDissipative.generator_semigroup`
and `LinearPMap.IsMDissipative.eqOn_semigroup`; conversely
`Feec.C0Semigroup.IsContraction.isMDissipative_generator` and
`LinearPMap.IsMDissipative.surjective`. -/
theorem lumerPhillips {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    (∀ A : E →ₗ.[𝕜] E, (∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0) →
      (∃ μ : ℝ, 0 < μ ∧ ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y) →
      ∃ S : ℝ → E →L[𝕜] E, IsC0Semigroup S ∧ (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ 1) ∧
        generatorGraph S = A.graph ∧
        ∀ S' : ℝ → E →L[𝕜] E, IsC0Semigroup S' → generatorGraph S' = A.graph →
          ∀ t : ℝ, 0 ≤ t → S' t = S t) ∧
    ∀ S : ℝ → E →L[𝕜] E, IsC0Semigroup S → (∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ 1) →
      ∃ A : E →ₗ.[𝕜] E, generatorGraph S = A.graph ∧
        (∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ 0) ∧
        ∀ μ : ℝ, 0 < μ → ∀ y : E, ∃ x : A.domain, (μ : 𝕜) • (x : E) - A x = y := by
  refine ⟨fun A hA hA' => ?_, fun S hS hS1 => ?_⟩
  · have hAm : A.IsMDissipative := ⟨hA, hA'⟩
    refine ⟨hAm.semigroup.S, ⟨hAm.semigroup.map_zero, hAm.semigroup.map_add,
      hAm.semigroup.strongCont⟩, hAm.isContraction_semigroup, ?_, fun S' hS' hg t ht => ?_⟩
    · rw [generatorGraph_eq, hAm.generator_semigroup]
    · have hG : hS'.toC0.generator = A :=
        LinearPMap.eq_of_eq_graph
          (SetLike.coe_injective ((generatorGraph_eq hS'.toC0).symm.trans hg))
      exact hAm.eqOn_semigroup hG ht
  · have hm := (show hS.toC0.IsContraction from hS1).isMDissipative_generator
    exact ⟨hS.toC0.generator, generatorGraph_eq hS.toC0, hm.dissipative,
      fun μ hμ y => hm.surjective hμ y⟩

end TimeStepping
