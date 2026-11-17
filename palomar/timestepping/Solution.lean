module

public import Solution.FdHeat
public import Solution.Leapfrog
public import Solution.PlaneWave

/-!
# Rational time stepping on Banach spaces, with its instances (solution)

The theorems of `Challenge.lean`, proved from `Feec` through the bridges `Solution.Bridge` (the
rational schemes), `Solution.FdHeat` (compatible data for finite differences) and
`Solution.CubeSpaces`, `Solution.WhitneySpaces`, `Solution.WhitneyInterp`,
`Solution.WhitneyScheme` (the Whitney schemes of the cube).

* Banach spaces: the Hille–Yosida estimates from `Feec.C0Semigroup.isResolvent_resolvent` and
  `Feec.C0Semigroup.norm_resolvent_pow_le`; Brenner–Thomée's stability bound from
  `Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_le_of_resolvent_of_isAStable`
  (the Hille–Phillips calculus on the complexification) and the sharp error from
  `Feec.TimeStepping.RationalScheme.norm_resolventStep_pow_sub_S_le_sharp_of_resolvent`
  (Brenner–Thomée's error kernel, `Feec.HalfLineAlgebra.integral_norm_errorKernel_le`); the
  convergence theorem `Feec.TimeStepping.BanachFEEC.TimeScheme.converges`.
* Hilbert spaces: `ContinuousLinearMap.norm_aeval_mul_inverse_le`,
  `Feec.TimeStepping.RationalScheme.norm_step_le` with
  `Feec.TimeStepping.RationalScheme.step_eq_resolventEval`.
* Finite differences: `Feec.Models.Cube.FiniteDifferenceHeat.finiteDifferenceHeat` with
  `TimeStepping.norm_fdLaplacian_pow_gridInterp_le`.
* The Whitney schemes: the Freudenthal meshes are `Feec`'s (`cubeMesh`), the challenge's Whitney
  spaces, interpolant and steps are `Feec`'s, and the errors are
  `Feec.Models.Cube.Inhomogeneous.RowSolution.whitney_cn_error_le_row` and
  `RowSolution.whitney_leapfrog_error_le_row`, the latter for every constant of the inverse
  estimate; the global inverse estimate is `Feec.FiniteElement.PolySeq.exists_mul_norm_d_le`;
  non-vacuity from row `0` of `Feec`'s plane wave (`Solution.PlaneWave`).

## References

* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.5, §3.4
* [J. von Neumann, *Eine Spektraltheorie für allgemeine Operatoren eines unitären Raumes*][VonNeumann1951]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7
* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Polynomial Asymptotics Filter Set Feec.TimeStepping

@[expose] public noncomputable section

namespace TimeStepping

/-! ### Banach spaces -/

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

/-- **Stability and consistency give convergence** (the Lax equivalence theorem in the
Brenner–Thomée form, [BrennerThomee1979]; [Thomee2006], Ch. 7; [Pazy1983], §3.4). Let `S` be a
strongly continuous semigroup of a Banach space `E` over `𝕜 = ℝ` or `ℂ` with `‖S t‖ ≤ M`, and
let Banach spaces `Xₕ` (`h : κ`, refined along a filter `l`) carry bounded generators `Lₕ` with
`‖e^{tLₕ}‖ ≤ M` for `t ≥ 0`, uniformly in `h`, read in `E` by `ιₕ` with left inverses `πₕ`
(`πₕ ιₕ = 1`), `‖ιₕ‖, ‖πₕ‖ ≤ C`. Let `Pₕ` be a time scheme with steps `τₕ > 0`, `τₕ → 0`,
power bounded (`‖Pₕⁿ‖ ≤ Mₛ(T)` for `nτₕ ≤ T`) and consistent of order `p ≥ 1`
(`‖Pₕ y - e^{τₕLₕ} y‖ ≤ K τₕ^{p+1} ‖Lₕ^{p+1} y‖`). If the semidiscrete solutions
`ιₕ e^{tLₕ} vₕ` converge to `S(t) x` uniformly on every `[0, T]`, then the fully discrete
solutions `ιₕ Pₕⁿ vₕ` converge to `S(nτₕ) x` uniformly over the time levels `nτₕ ∈ [0, T]`: no
smoothness of `x` or `vₕ` is assumed. (`S` enters the conclusion only through
`S(nτₕ) x`, the limit of the semidiscrete solutions.) -/
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

/-! ### Hilbert spaces -/

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

/-! ### Finite differences in the maximum norm -/

/-- **The heat equation in the maximum norm by finite differences, from compatible data**:
`Feec.Models.Cube.FiniteDifferenceHeat.finiteDifferenceHeat` at `v = Iₕ u(0)`, whose discrete
term `‖Δₕ^{m+1} Iₕ u(0)‖_∞ ≤ n^{m+1} B'` is `norm_fdLaplacian_pow_gridInterp_le`. -/
theorem fdHeat (p q : ℝ[X]) (hr : IsAStable p q) {m : ℕ} (hm : HasOrder p q m) :
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
  refine ⟨hr.scheme.sharpConst m, ?_⟩
  intro n b s T B B' u u₁ ũ hs hu hh hbd hB hũ hũu hodd hB' N τ hτ k hk
  let S : Feec.Models.Cube.MaxNormHeat.HeatSolution b s T :=
    { u := u, u₁ := u₁, contDiff := hu, hasDerivAt := fun t ht x hx => (hh t ht x hx).1,
      heat := fun t ht x hx => (hh t ht x hx).2, boundary := hbd, B₄ := B, bound₄ := hB }
  set v := gridInterp b (s / (N + 1 : ℕ)) N (u 0) with hvdef
  have H := (Feec.Models.Cube.FiniteDifferenceHeat.finiteDifferenceHeat b hs).rational S
    hr.scheme_isAStable (hr.scheme_hasOrder hm) N hτ hk v
  have e := (step_eq (Feec.Models.Cube.FiniteDifferenceHeat.family n s) hτ N hr.scheme).2
  simp only [RCLike.ofReal_real_eq_id, id] at e
  rw [e, show Feec.Models.Cube.FiniteDifferenceHeat.fdLaplacian s N =
    fdLaplacian (gridNodes n N) (s / (N + 1 : ℕ)) from (fdLaplacian_eq _ _).symm] at H
  have hv : v = gridInterp b (s / (N + 1 : ℕ)) N ũ := funext fun g =>
    (hũu _ (Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self)
      (Feec.Models.Cube.MaxNormHeat.node_mem_openCube (b := b) hs g))).symm
  have hD := norm_fdLaplacian_pow_gridInterp_le b hs N m hũ
    (fun i => ⟨fun x => (hodd i x).1, fun x => (hodd i x).2⟩) hB'
  rw [← hv] at hD
  have hK := RationalScheme.sharpConst_nonneg hr.scheme_isAStable (hr.scheme_hasOrder hm)
  refine H.trans ?_
  calc _ ≤ 0 + k * τ * S.defect N +
        hr.scheme.sharpConst m * (k * τ) * τ ^ m * (n ^ (m + 1) * B') :=
        add_le_add (add_le_add (norm_le_zero_iff.2 (sub_eq_zero.2 rfl)) le_rfl)
          (mul_le_mul_of_nonneg_left hD
            (mul_nonneg (mul_nonneg hK (by positivity)) (by positivity)))
    _ = _ := by
        simp only [Feec.Models.Cube.MaxNormHeat.HeatSolution.defect,
          Feec.Models.Cube.MaxNormHeat.meshSize]
        ring

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

/-! ### The Whitney schemes on the cube -/

section Cube

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM

open Feec.Models.Cube.Inhomogeneous hiding RowSolution in
theorem crankNicolson_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧
    (∀ N k (w : FormField 3), Continuous w → ∃! x, IsWhitneyInterp (cube 3) (𝒯 N) k w x) ∧
    (∀ N Δt g u, RowMem (𝒯 N) false g → RowMem (𝒯 N) false u → ∃! u', IsCNStep (𝒯 N) Δt g u u') ∧
    (∀ N, ∃ v ∈ femSpaceMin (cube 3) (𝒯 N) topSeq 1, v ≠ 0) ∧
    ∀ N T L (X : RowSolution T L) (Δt : ℝ) (M : ℕ) (u g : ℕ → Row), 0 < Δt → M * Δt ≤ T →
      (∀ m < M, IsCNStep (𝒯 N) Δt (g (m + 1)) (u m) (u (m + 1))) →
      (∀ m < M, ∃ w, IsRowInterp (𝒯 N) (X.u ((m + 1 : ℕ) * Δt)) w ∧
        RowMem (𝒯 N) true (g (m + 1) - w)) →
      IsRowInterp (𝒯 N) (X.u 0) (u 0) → ∀ U : Row, IsRepr (cube 3) 0 (X.u (M * Δt) 0) U.1 →
        IsRepr (cube 3) 1 (X.u (M * Δt) 1) U.2.1 → IsRepr (cube 3) 2 (X.u (M * Δt) 2) U.2.2 →
        rowNorm (u M - U) ≤ C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) := by
  refine ⟨cubeMesh, cnConst, isMeshFamily_cube, points_cube, ?_, ?_, ?_, ?_⟩
  · intro N k w hw
    exact ⟨FEMInterp.canonicalInterp N k ⟨w, hw⟩, (isWhitneyInterp_cube_iff N k ⟨w, hw⟩ _).2 rfl,
      fun x hx => (isWhitneyInterp_cube_iff N k ⟨w, hw⟩ _).1 hx⟩
  · intro N Δt g u hg hu
    obtain ⟨g', rfl⟩ := (rowMem_false_iff N g).1 hg
    obtain ⟨u', rfl⟩ := (rowMem_false_iff N u).1 hu
    obtain ⟨a, ha, hau⟩ := whitney_existsUnique_cnStep N (Δt / 2) 0 g' u'
    refine ⟨ofD N a, (isCNStep_ofD_iff N Δt g' u' _).2 ⟨a, rfl, ha⟩, fun x hx => ?_⟩
    obtain ⟨b, rfl, hb⟩ := (isCNStep_ofD_iff N Δt g' u' x).1 hx
    rw [hau b hb]
  · intro N
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (whitneyMin_one_ne_bot N)
    exact ⟨v, (mem_whitneyMin N 1).1 hv, hv0⟩
  · intro N T L X Δt M u g hΔt hM hstep hg hu0 U hU0 hU1 hU2
    have hL0 := zero_le_L X hΔt hM
    have hu : ∀ m ≤ M, RowMem (cubeMesh N) false (u m) := by
      intro m hm
      rcases m with _ | m
      · rw [ofD_interp X hu0]; exact (rowMem_false_iff N _).2 ⟨_, rfl⟩
      · exact (hstep m hm).1
    have hgm : ∀ m < M, ∃ c ∈ whitneyInterior N,
        g (m + 1) = ofD N (c + X.toFeec.interp N ((m + 1 : ℕ) * Δt)) := by
      intro m hm
      obtain ⟨w, hw, hgw⟩ := hg m hm
      obtain ⟨c, hc, hce⟩ := (rowMem_true_iff N _).1 hgw
      refine ⟨c, hc, ?_⟩
      rw [ofD_add, ← hce, ← ofD_interp X hw, sub_add_cancel]
    classical
    set a : ℕ → DState (whitneyRow N) := fun m =>
      if h : RowMem (cubeMesh N) false (u m) then ((rowMem_false_iff N _).1 h).choose else 0
      with hadef
    have ha : ∀ m ≤ M, u m = ofD N (a m) := fun m hm => by
      rw [hadef]; dsimp only; rw [dite_eq_left (hu m hm)]
      exact ((rowMem_false_iff N _).1 (hu m hm)).choose_spec
    set b : ℕ → DState (whitneyRow N) := fun m =>
      if h : RowMem (cubeMesh N) false (g m) then ((rowMem_false_iff N _).1 h).choose else 0
      with hbdef
    have hgM : ∀ m < M, RowMem (cubeMesh N) false (g (m + 1)) := fun m hm => by
      obtain ⟨c, -, hc⟩ := hgm m hm
      exact (rowMem_false_iff N _).2 ⟨_, hc⟩
    have hb : ∀ m < M, g (m + 1) = ofD N (b (m + 1)) := fun m hm => by
      rw [hbdef]; dsimp only; rw [dite_eq_left (hgM m hm)]
      exact ((rowMem_false_iff N _).1 (hgM m hm)).choose_spec
    have hstep' : ∀ m < M, Feec.TimeStepping.IsDirichletCNStep (whitneyInterior N)
        (discreteWave (whitneyRow N)) (Δt / 2) 0 (b (m + 1)) (a m) (a (m + 1)) := by
      intro m hm
      have h := hstep m hm
      rw [hb m hm, ha m hm.le, ha (m + 1) hm] at h
      obtain ⟨u', hu', h'⟩ := (isCNStep_ofD_iff N Δt _ _ _).1 h
      rwa [← ofD_injective N hu'] at h'
    have hg' : ∀ m < M, b (m + 1) - X.toFeec.interp N ((m + 1 : ℕ) * Δt) ∈ whitneyInterior N := by
      intro m hm
      obtain ⟨c, hc, hce⟩ := hgm m hm
      rw [hb m hm] at hce
      rw [ofD_injective N hce, add_sub_cancel_right]
      exact hc
    have hu0' : a 0 = X.toFeec.interp N 0 :=
      ofD_injective N ((ha 0 (Nat.zero_le M)).symm.trans (ofD_interp X hu0))
    have key := X.toFeec.whitney_cn_error_le_row N hΔt hL0 hM hstep' hg' hu0'
    rw [toRow_field X hU0 hU1 hU2, ha M le_rfl, ofD, ← toRow_sub, rowNorm, norm_toRow,
      meshSize_cubeMesh]
    exact key

theorem inverse_estimate {n : ℕ} [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {M : ℕ → SimplicialMesh n} (hM : IsMeshFamily Ω M)
    (hint : ∀ N, ∀ T ∈ (M N).simplices, interior T.closedInterior ⊆ Ω) (S : PolySeq) (k : ℕ) :
    ∃ C, ∀ N, ∀ v ∈ femSpace Ω (M N) S k, ∃ hv : v ∈ (dMax Ω k).domain,
      meshSize (M N) * ‖dMax Ω k ⟨v, hv⟩‖ ≤ C * ‖v‖ := by
  obtain ⟨hdom, ⟨σ, q, hq, hsq⟩, hpos, -⟩ := hM
  obtain ⟨T₀, hT₀⟩ := exists_mem_simplices (hpos 0)
  have hσ := pos_of_isShapeRegular (hsq 0).1 hT₀
  obtain ⟨K, -, hK⟩ := S.toFeec.exists_mul_norm_d_le (n := n) k (C := max n σ)
    (c := 1 / ((n.factorial : ℝ) * σ ^ n)) (le_max_of_le_right hσ.le) (by positivity)
  refine ⟨K / q, fun N v hv => ?_⟩
  set m := (M N).toFeec Ω (hdom N)
  have hv' : v ∈ (S.toFeec.subcomplex m hΩ).V k := (mem_V_iff S (M N) Ω (hdom N) v).2 hv
  have hd : v ∈ ((extDerivOp ℝ n k).maximal m.domain).domain :=
    (polyElement n S.toFeec).V_le_maximal_domain m hΩ k hv'
  have hdM : dMax Ω k = (extDerivOp ℝ n k).maximal Ω := dMax_eq Ω k
  refine ⟨hdM ▸ hd, ?_⟩
  have hb := hK m hΩ (hint N) (isShapeRegular_toFeec (hdom N) (hsq N).1)
    (h := q * meshSize (M N)) (mul_pos hq (hpos N)) (fun T hT => (hsq N).2 T hT) ⟨v, hd⟩ hv'
  have e : dMax Ω k ⟨v, hdM ▸ hd⟩ = (extDerivOp ℝ n k).maximal m.domain ⟨v, hd⟩ :=
    LinearPMap.apply_of_eq' hdM _
  have hb' : q * meshSize (M N) * ‖(extDerivOp ℝ n k).maximal m.domain ⟨v, hd⟩‖ ≤ K * ‖v‖ := hb
  rw [e, div_mul_eq_mul_div, le_div_iff₀ hq]
  rw [mul_comm _ q, ← mul_assoc]
  exact hb'

set_option maxHeartbeats 800000 in
open Feec.Models.Cube.Inhomogeneous hiding RowSolution in
theorem leapfrog_cube : ∃ (𝒯 : ℕ → SimplicialMesh 3) (C : ℝ), IsMeshFamily (cube 3) 𝒯 ∧
    IsFreudenthal 𝒯 ∧
    (∃ C₀, ∀ N v, RowMem (𝒯 N) false v →
      meshSize (𝒯 N) * √(‖wd 0 v.1‖ ^ 2 + ‖wd 1 v.2.1‖ ^ 2) ≤ C₀ * rowNorm v) ∧
    (∀ N Δt g u u', RowMem (𝒯 N) false g → RowMem (𝒯 N) false u → RowMem (𝒯 N) false u' →
      ∃! u'', IsLeapfrogStep (𝒯 N) Δt g u u' u'') ∧
    ∀ C₀, 0 ≤ C₀ → (∀ N v, RowMem (𝒯 N) false v →
      meshSize (𝒯 N) * √(‖wd 0 v.1‖ ^ 2 + ‖wd 1 v.2.1‖ ^ 2) ≤ C₀ * rowNorm v) →
    (∀ N Δt c (u : ℕ → Row) m, 0 ≤ Δt → c < 1 → 2 * C₀ * Δt ≤ c * meshSize (𝒯 N) →
      (∀ k < m, IsLeapfrogStep (𝒯 N) Δt 0 (u k) (u (k + 1)) (u (k + 2))) →
      RowMem (𝒯 N) true (u 0) → RowMem (𝒯 N) true (u 1) →
      √(1 - c) * rowNorm (u (m + 1)) ≤ √((1 + c) * (rowNorm (u 0) ^ 2 + rowNorm (u 1) ^ 2))) ∧
    ∀ N T L (X : RowSolution T L) (Δt c : ℝ) (M : ℕ) (u g : ℕ → Row), 0 < Δt → c < 1 →
      2 * C₀ * Δt ≤ c * meshSize (𝒯 N) → M * Δt ≤ T →
      (∀ m, m + 2 ≤ M → IsLeapfrogStep (𝒯 N) Δt (g (m + 2)) (u m) (u (m + 1)) (u (m + 2))) →
      (∀ m, m + 2 ≤ M → ∃ w, IsRowInterp (𝒯 N) (X.u ((m + 2 : ℕ) * Δt)) w ∧
        RowMem (𝒯 N) true (g (m + 2) - w)) →
      IsRowInterp (𝒯 N) (X.u 0) (u 0) → IsRowInterp (𝒯 N) (X.u Δt) (u 1) →
      ∀ U : Row, IsRepr (cube 3) 0 (X.u (M * Δt) 0) U.1 →
        IsRepr (cube 3) 1 (X.u (M * Δt) 1) U.2.1 → IsRepr (cube 3) 2 (X.u (M * Δt) 2) U.2.2 →
        rowNorm (u M - U) ≤ C * L * (1 + T) * (meshSize (𝒯 N) + Δt ^ 2) / (1 - c) := by
  obtain ⟨K, -, hK⟩ := exists_mul_norm_discreteD_whitneyRow_le
  refine ⟨cubeMesh, leapfrogConst, isMeshFamily_cube, points_cube, ⟨K, ?_⟩, ?_,
    fun C₀ hC₀ hC₀' => ?_⟩
  · intro N v hv
    obtain ⟨a, rfl⟩ := (rowMem_false_iff N v).1 hv
    rw [meshSize_cubeMesh, rowNorm_ofD, ← norm_discreteD_eq]
    exact hK N a
  · intro N Δt g u u' hg hu hu'
    obtain ⟨g', rfl⟩ := (rowMem_false_iff N g).1 hg
    obtain ⟨u₀, rfl⟩ := (rowMem_false_iff N u).1 hu
    obtain ⟨u₁, rfl⟩ := (rowMem_false_iff N u').1 hu'
    obtain ⟨a, ha, hau⟩ := Feec.TimeStepping.existsUnique_isDirichletLeapfrogStep
      (V₀ := whitneyInterior N) (A := discreteWave (whitneyRow N)) Δt g' u₀ u₁
    refine ⟨ofD N a, (isLeapfrogStep_ofD_iff N Δt g' u₀ u₁ _).2 ⟨a, rfl, ha⟩, fun x hx => ?_⟩
    obtain ⟨b, rfl, hb⟩ := (isLeapfrogStep_ofD_iff N Δt g' u₀ u₁ x).1 hx
    rw [hau b hb]
  have hC : ∀ N (x : DState (whitneyRow N)),
      Feec.Models.Cube.FEM.meshSize N * ‖discreteD (whitneyRow N) x‖ ≤ C₀ * ‖x‖ := fun N x => by
    have := hC₀' N (ofD N x) ((rowMem_false_iff N _).2 ⟨x, rfl⟩)
    rwa [meshSize_cubeMesh, rowNorm_ofD, ← norm_discreteD_eq] at this
  refine ⟨?_, ?_⟩
  · intro N Δt c u m hΔt hc1 hcfl hstep hu0 hu1
    have hmem : ∀ k ≤ m + 1, RowMem (cubeMesh N) false (u k) := by
      intro k hk
      rcases k with _ | _ | k
      · exact rowMem_false_of_true N hu0
      · exact rowMem_false_of_true N hu1
      · exact (hstep k (by omega)).1
    obtain ⟨a, ha⟩ := exists_seq_ofD N hmem
    have hstep' : ∀ k < m, Feec.TimeStepping.IsDirichletLeapfrogStep (whitneyInterior N)
        (discreteWave (whitneyRow N)) Δt 0 (a k) (a (k + 1)) (a (k + 2)) := by
      intro k hk
      have h := hstep k hk
      rw [← ofD_zero N, ha k (by omega), ha (k + 1) (by omega), ha (k + 2) (by omega)] at h
      obtain ⟨u', hu', h'⟩ := (isLeapfrogStep_ofD_iff N Δt _ _ _ _).1 h
      rwa [← ofD_injective N hu'] at h'
    have ha0 : a 0 ∈ whitneyInterior N := by
      have h := hu0; rw [ha 0 (by omega)] at h; exact (rowMem_true_ofD_iff N _).1 h
    have ha1 : a 1 ∈ whitneyInterior N := by
      have h := hu1; rw [ha 1 (by omega)] at h; exact (rowMem_true_ofD_iff N _).1 h
    rw [meshSize_cubeMesh] at hcfl
    have key := whitney_leapfrog_stable N hC₀ (hC N) hΔt hc1 hcfl hstep' ha0 ha1
    rwa [ha 0 (by omega), ha 1 (by omega), ha (m + 1) le_rfl, rowNorm_ofD, rowNorm_ofD,
      rowNorm_ofD]
  · intro N T L X Δt c M u g hΔt hc1 hcfl hM hstep hg hu0 hu1 U hU0 hU1 hU2
    have hL0 := zero_le_L X hΔt hM
    have hmem : ∀ k ≤ M, RowMem (cubeMesh N) false (u k) := by
      intro k hk
      rcases k with _ | _ | k
      · rw [ofD_interp X hu0]; exact (rowMem_false_iff N _).2 ⟨_, rfl⟩
      · rw [ofD_interp X hu1]; exact (rowMem_false_iff N _).2 ⟨_, rfl⟩
      · exact (hstep k hk).1
    obtain ⟨a, ha⟩ := exists_seq_ofD N hmem
    have hgm : ∀ k, k + 2 ≤ M → ∃ e ∈ whitneyInterior N,
        g (k + 2) = ofD N (e + X.toFeec.interp N ((k + 2 : ℕ) * Δt)) := by
      intro k hk
      obtain ⟨w, hw, hgw⟩ := hg k hk
      obtain ⟨e, he, hee⟩ := (rowMem_true_iff N _).1 hgw
      refine ⟨e, he, ?_⟩
      rw [ofD_add, ← hee, ← ofD_interp X hw, sub_add_cancel]
    choose! e he hge using hgm
    set gD : ℕ → DState (whitneyRow N) := fun j => e (j - 2) + X.toFeec.interp N (j * Δt)
    have hgD : ∀ k, gD (k + 2) = e k + X.toFeec.interp N ((k + 2 : ℕ) * Δt) := fun k => by
      simp only [gD, Nat.add_sub_cancel]
    have hstep' : ∀ k, k + 2 ≤ M → Feec.TimeStepping.IsDirichletLeapfrogStep (whitneyInterior N)
        (discreteWave (whitneyRow N)) Δt (gD (k + 2)) (a k) (a (k + 1)) (a (k + 2)) := by
      intro k hk
      have h := hstep k hk
      rw [hge k hk, ha k (by omega), ha (k + 1) (by omega), ha (k + 2) hk] at h
      obtain ⟨u', hu', h'⟩ := (isLeapfrogStep_ofD_iff N Δt _ _ _ _).1 h
      rw [← ofD_injective N hu'] at h'
      rwa [hgD]
    have hg' : ∀ k, k + 2 ≤ M →
        gD (k + 2) - X.toFeec.interp N ((k + 2 : ℕ) * Δt) ∈ whitneyInterior N := by
      intro k hk
      rw [hgD, add_sub_cancel_right]
      exact he k hk
    have hu0' : a 0 = X.toFeec.interp N 0 :=
      ofD_injective N ((ha 0 (Nat.zero_le M)).symm.trans (ofD_interp X hu0))
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · subst hM0
      set a' := Function.update a 1 (X.toFeec.interp N Δt)
      have key := X.toFeec.whitney_leapfrog_error_le_row N hC₀ (hC N) hΔt hc1
        (by rwa [meshSize_cubeMesh] at hcfl) hL0 hM (u := a') (g := gD)
        (fun k hk => absurd hk (by omega)) (fun k hk => absurd hk (by omega))
        (by simp [a', hu0']) (by simp [a'])
      rw [toRow_field X hU0 hU1 hU2, ha 0 le_rfl, ofD, ← toRow_sub, rowNorm, norm_toRow,
        meshSize_cubeMesh]
      simpa [a'] using key
    have hu1' : a 1 = X.toFeec.interp N Δt :=
      ofD_injective N ((ha 1 hM0).symm.trans (ofD_interp X hu1))
    have key := X.toFeec.whitney_leapfrog_error_le_row N hC₀ (hC N) hΔt hc1
      (by rwa [meshSize_cubeMesh] at hcfl) hL0 hM hstep' hg' hu0' hu1'
    rw [toRow_field X hU0 hU1 hU2, ha M le_rfl, ofD, ← toRow_sub, rowNorm, norm_toRow,
      meshSize_cubeMesh]
    exact key

/-- **Non-vacuity of the Whitney error bounds**: row `0` of the plane wave
(`Solution.PlaneWave`). -/
theorem rowSolution_nonvacuous (T : ℝ) :
    ∃ L, ∃ X : RowSolution T L, ∀ t, ∃ y ∈ cube 3, X.u t 1 y ≠ 0 ∧ X.u₁ t 1 y ≠ 0 :=
  exists_rowSolution T

end Cube

end TimeStepping
