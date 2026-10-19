module

public import Feec.Models.Cube.WeakSymmetryWave
public import Feec.HilbertComplex.HodgeWave
public import Feec.Models.BoundedDomain.Hessian
public import Feec.Domain.StarShapedSmoothing

/-!
# The Einstein–Bianchi system with weak symmetries: the wave problem on the cube

The linearized EB system with weakly imposed symmetry, [QuennevilleBelair2015], §6.3: the
multiplier problem (6.2) for the complex (4.16) on `Q = (0, ½)³` with the thesis' boundary
conditions, and its semi-discretization (6.5) by the elements of Table 6.1.

## Main results

* `cubeWaveData`: the data of (6.1)/(6.2) on `Q` (`Feec.BGG.WaveData`);
  `exists_multiplierSolution`: every solution of (6.1) has a unique multiplier `Λ(t) ∈ W̌¹`
  (corrected Prop 6.1); `exactWave_toMultiplierSolution`: the classical solutions with `L²`
  multiplier of `Feec.Models.Cube.WeakSymmetry.cubeWave_rate` solve (6.2) (and (6.1)).
* `negNorm_le_tripleNorm`: `|||λ||| = ‖Jλ‖` is equivalent to `‖div λ‖_{H⁻¹} + ‖λ‖_{H⁻¹}`
  (`W̌¹ = H⁻¹(div, V)` of §6.3); `denseRange_B`, `J_injective`: `B = (d, −S)` has dense range, so
  `W̌¹` is the completion of `(L²Λ¹(Q), |||·|||)`; `not_isClosed_range_B`: the range of `B` is not
  closed (it lies in `H̊(curl, Q)`, which misses the constant `1`-forms, `dxZero_not_mem_D1`), so
  the completion is genuinely needed.
* `bgg_wave_existsUnique`: existence and uniqueness for the Hodge wave equation of (5.1) on `Q`
  (Stone), under the regularity hypothesis.
* **`gamma_equiv_hessMin`** (`Γ ≅ H̊²(Q)`, §6.3): `(σ, φ) ↦ σ` is a bijection from
  `Γ = {(σ, φ) ∈ H̊¹ × H̊¹(Q; ℝ³) : grad σ = φ}` onto the domain of the minimal Hessian
  `Feec.Models.BoundedDomain.hessMin` (the first space of `Feec.Models.BoundedDomain.bggComplex`
  on `Q`), and `D₀(σ, φ) = grad φ` is `∇²σ`. `Γ ⊆ H̊²` (`hessMin_of_mem_Γ`) by smoothing
  (dilation towards the centre and mollification: test functions `Rσ` with
  `∇²(Rσ) = c² R(grad φ)`); `H̊² ⊆ Γ` (`mem_Γ_of_hessMin`) by integration by parts on test
  functions, `‖∂ⱼψ‖² ≤ ‖ψ‖ ‖∂ⱼ∂ⱼψ‖` (`inner_toL2_fderiv`), and the closedness of `grad` on
  `H̊¹`.
* **`waveFEM`**: under `CurlPotential`, for one smoother: (5.4) and uniform bounds; `grad`
  injective and `S₀,ₕ` onto; corrected Prop 6.2 for (6.5); energy stability; `O(h)` convergence
  for classical solutions whose states and time derivatives are `C²` and vanish outside `Q`
  (flat at `∂Q`). **`waveFEM_nonvacuous`**: a nontrivial manufactured solution meets
  all hypotheses and its discrete `σₕ(t)` converge and are nonzero for large `N`.
  `CurlPotential` is proved: the unconditional versions are `waveFEM_cube`,
  `waveFEM_nonvacuous_cube` and `bgg_wave_existsUnique_cube`
  (`Feec.Physics.EinsteinBianchi.Unconditional`).

## Gaps

* The identification of (6.1) for `bggHilb` with the matrix model
  `Feec.Models.BoundedDomain.bggComplex` (`Feec.Models.BoundedDomain.bggComplex_eq61`) is
  complete: `gamma_equiv_hessMin` here for the first space, and
  `Feec.EinsteinBianchi.MatrixModel.matrixComplex_eq_map` for the whole complex (the isometry
  `rowsEquiv : H̊Λ¹(Q)³ ≅ H̊(curl, Q; ℝ³ˣ³)`, rows `u_a = Σ_b u_{ab} dx_b`, intertwining
  `(S¹, d)` with `(skwL, curl)`, and the Hodge star on `2`-forms), with conjugate Hodge wave
  operators and groups and corresponding strong and classical solutions
  (`Feec.EinsteinBianchi.MatrixModel.isStrongSolution_iff`). The TSD datum of
  `Feec.Counterexamples.BoundedBGG.bggComplex_verdict` (whose solution leaves `L²(TSD)`) is
  transported to this model in `Feec.EinsteinBianchi.BoundedFailure`. The rate theorem does not
  apply to it (its magnetic datum `β = x₃(e₁e₂ᵀ + e₂e₁ᵀ)` does not vanish on `∂Q`);
  `Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd` proves, with no
  hypothesis, that (6.5) converges to it without rate and that the discrete fields leave TSD
  (convergence for every datum in `D(L)`: `BoundedConvergence.tendsto_of_mem_wave_domain`, from
  the rate-free `Feec.Models.Cube.WeakSymmetry.cubeWave_converges` for multipliers represented by
  `L²` data and the density of `D(L²)`).
* The mirror variant of the scheme is discretized and well posed in
  `Feec.Models.Cube.MirrorWeakSymmetryFEM`; its convergence is open (see there).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1 ((6.1), (6.2), Prop 6.1), §6.2 (Prop 6.2), §6.3 ((6.5), Table 6.1), Thm 4.6
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.10 (Stone's theorem)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.WaveFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

/-! ### The continuous data of §6.1 on the cube -/

theorem incl1_injective : Function.Injective incl1 := fun _ _ h =>
  PiLp.ext fun a => Subtype.ext (congrArg (fun z : Wv W1 => z a) h)


/-- **The continuous data (6.1)/(6.2) of the BGG system (4.16) on `Q = (0, ½)³`** in the model of
`Feec.BGG.WaveData`: `V⁰ = H̊Λ⁰(Q)`, `Ṽ⁰ = H̊Λ⁰(Q)³` (graph norms), `Ṽ¹ = H̊Λ¹(Q)³`, the
`L²` spaces `W⁰ = L²Λ⁰`, `W¹ = L²Λ¹`, `W² = L²Λ²`, `W̃¹ = (L²Λ¹)³`, `W̃² = (L²Λ²)³`, `d = grad`,
`curl`, `S⁰ = I`, `S¹ = 2 vskw`. -/
def cubeWaveData : Feec.BGG.WaveData V0 Vt0 (Wv U1) W0 W1 W2 (Wv W1) (Wv W2) where
  i0 := D0.graphFst
  d0 := D1.graphFst ∘L bggD0
  S0 := D1.graphFst ∘L bggS0
  dt0 := ιt1 ∘L bggDt0
  it1 := incl1
  dt1 := piMap segD1
  S1 := segS1
  i0_injective := LinearPMap.graphFst_injective D0
  it1_injective := incl1_injective

theorem cubeWaveData_d0 (τ : V0) : cubeWaveData.d0 τ = D0.graphSnd τ := graphFst_bggD0 τ

theorem cubeWaveData_S0 (ψ : Vt0) :
    cubeWaveData.S0 ψ = wsL2 (Ω := cubeDomain 3) 0 (ιt0 ψ) := graphFst_bggS0 ψ

/-- **Corrected Prop 6.1 on the cube**: every solution of (6.1) has a unique multiplier
`Λ(t) ∈ W̌¹` solving (6.2) (no hypothesis on `u`, `M` arbitrary, no `λ₀`;
`Feec.BGG.WaveData.Solution.exists_multiplierSolution`). -/
theorem exists_multiplierSolution {T : ℝ} {f : ℝ → Wv W1} (s : cubeWaveData.Solution T f) :
    ∃ s' : cubeWaveData.MultiplierSolution T f, s'.toTrajectory = s.toTrajectory ∧
      ∀ s'' : cubeWaveData.MultiplierSolution T f, s''.toTrajectory = s.toTrajectory →
        ∀ t ∈ Ico 0 T, s''.Λ t = s'.Λ t :=
  s.exists_multiplierSolution

/-! ### `W̌¹` on the cube: the norm `|||λ|||` and the density of the range of `B` -/

/-- The `H⁻¹` norm of `div λ`: the dual norm of `τ ↦ ⟪λ, grad τ⟫` on `H̊¹(Q)`. -/
def negNormDiv (μ : W1) : ℝ := ‖(innerSL ℝ μ).comp cubeWaveData.d0‖

/-- The `H⁻¹(V)` norm of `λ`: the dual norm of `ψ ↦ ⟪λ, S⁰ψ⟫ = Σₐ ⟪λₐ, ψₐ⟫` on `H̊¹(Q; ℝ³)`. -/
def negNorm (μ : W1) : ℝ := ‖(innerSL ℝ μ).comp cubeWaveData.S0‖

theorem norm_toLp_zero_right {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    (a : A) : ‖(WithLp.toLp 2 (a, (0 : B)) : WithLp 2 (A × B))‖ = ‖a‖ := by
  rw [WithLp.prod_norm_eq_of_L2]; simp

theorem norm_toLp_zero_left {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    (b : B) : ‖(WithLp.toLp 2 ((0 : A), b) : WithLp 2 (A × B))‖ = ‖b‖ := by
  rw [WithLp.prod_norm_eq_of_L2]; simp

set_option maxHeartbeats 2000000 in
/-- **`|||λ|||` is equivalent to `‖div λ‖_{H⁻¹} + ‖λ‖_{H⁻¹}`** ([QuennevilleBelair2015], §5.1,
§6.3: `W̌¹ = H⁻¹(div, V)`): `max(‖div λ‖₋₁, ‖λ‖₋₁) ≤ |||λ||| = ‖Jλ‖ ≤ ‖div λ‖₋₁ + ‖λ‖₋₁`. -/
theorem negNorm_le_tripleNorm (μ : W1) :
    negNormDiv μ ≤ ‖cubeWaveData.J μ‖ ∧ negNorm μ ≤ ‖cubeWaveData.J μ‖ ∧
      ‖cubeWaveData.J μ‖ ≤ negNormDiv μ + negNorm μ := by
  have hA : ∀ τ : V0, ((innerSL ℝ μ).comp cubeWaveData.d0) τ =
      cubeWaveData.J μ (WithLp.toLp 2 (τ, (0 : Vt0))) := fun τ => by
    rw [Feec.BGG.WaveData.J_apply, Feec.BGG.WaveData.B_toLp]
    simp
  have hB : ∀ ψ : Vt0, ((innerSL ℝ μ).comp cubeWaveData.S0) ψ =
      -cubeWaveData.J μ (WithLp.toLp 2 ((0 : V0), ψ)) := fun ψ => by
    rw [Feec.BGG.WaveData.J_apply, Feec.BGG.WaveData.B_toLp]
    simp
  have n1 : ∀ τ : V0, ‖(WithLp.toLp 2 (τ, (0 : Vt0)) : WithLp 2 (V0 × Vt0))‖ = ‖τ‖ :=
    norm_toLp_zero_right
  have n2 : ∀ ψ : Vt0, ‖(WithLp.toLp 2 ((0 : V0), ψ) : WithLp 2 (V0 × Vt0))‖ = ‖ψ‖ :=
    norm_toLp_zero_left
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun τ => ?_
    rw [hA, ← n1]
    exact (cubeWaveData.J μ).le_opNorm _
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ => ?_
    rw [hB, norm_neg, ← n2]
    exact (cubeWaveData.J μ).le_opNorm _
  · have h0 : 0 ≤ negNormDiv μ + negNorm μ := by unfold negNormDiv negNorm; positivity
    refine ContinuousLinearMap.opNorm_le_bound _ h0 fun x => ?_
    have hx : cubeWaveData.J μ x = ((innerSL ℝ μ).comp cubeWaveData.d0) (WithLp.ofLp x).1 -
        ((innerSL ℝ μ).comp cubeWaveData.S0) (WithLp.ofLp x).2 := by
      rw [hA, hB, sub_neg_eq_add, ← map_add]
      congr 1
      exact WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simp))
    have h1 := ((innerSL ℝ μ).comp cubeWaveData.d0).le_opNorm (WithLp.ofLp x).1
    have h2 := ((innerSL ℝ μ).comp cubeWaveData.S0).le_opNorm (WithLp.ofLp x).2
    have m1 : ‖(WithLp.ofLp x).1‖ ≤ ‖x‖ := WithLp.norm_fst_le (p := 2) (α := V0) (β := Vt0) x
    have m2 : ‖(WithLp.ofLp x).2‖ ≤ ‖x‖ := WithLp.norm_snd_le (p := 2) (α := V0) (β := Vt0) x
    have a1 : 0 ≤ ‖(innerSL ℝ μ).comp cubeWaveData.d0‖ := norm_nonneg _
    have a2 : 0 ≤ ‖(innerSL ℝ μ).comp cubeWaveData.S0‖ := norm_nonneg _
    rw [hx]
    refine (norm_sub_le _ _).trans ?_
    change _ ≤ (‖(innerSL ℝ μ).comp cubeWaveData.d0‖ + ‖(innerSL ℝ μ).comp cubeWaveData.S0‖) *
      ‖x‖
    nlinarith [mul_le_mul_of_nonneg_left m1 a1, mul_le_mul_of_nonneg_left m2 a2]

/-- **`B = (d, −S) : H̊¹(Q) × H̊¹(Q; ℝ³) → L²Λ¹(Q)` has dense range** (its range contains
`S⁰ C_c^∞(Q; ℝ³) = C_c^∞(Q; Λ¹)`), so `J` is injective, `|||·|||` is a norm on `L²Λ¹(Q)` and
`W̌¹` is the completion of `(L²Λ¹(Q), |||·|||)` (the thesis assumes `S Ṽ⁰` dense in `W¹`). -/
theorem denseRange_B : DenseRange cubeWaveData.B := by
  refine (dense_testFieldSub (𝕜 := ℝ) (isOpen_cubeDomain 3) (formIdx 3 1)).mono ?_
  rintro _ ⟨χ, hχ, rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_segS0_eq_testField hχ
  refine ⟨WithLp.toLp 2 ((0 : V0), -toGraphVec0 ψ), ?_⟩
  rw [Feec.BGG.WaveData.B_toLp, map_zero, zero_sub, map_neg, neg_neg, cubeWaveData_S0,
    ιt0_toGraphVec0, ← hψ, coe_segS0]

theorem J_injective : Function.Injective cubeWaveData.J := by
  intro μ ν h
  have h0 : ∀ x, ⟪μ - ν, cubeWaveData.B x⟫ = 0 := fun x => by
    rw [inner_sub_left, ← Feec.BGG.WaveData.J_apply, ← Feec.BGG.WaveData.J_apply, h, sub_self]
  have hc : Continuous fun z : W1 => ⟪μ - ν, z⟫ := continuous_const.inner continuous_id
  have : ∀ z, ⟪μ - ν, z⟫ = 0 := fun z =>
    denseRange_B.induction_on z (isClosed_eq hc continuous_const) h0
  exact sub_eq_zero.1 (inner_self_eq_zero.1 (this (μ - ν)))

/-- The constant `1`-form `dx₀` on `Q`. -/
abbrev dxZero : W1 :=
  Feec.Models.Cube.DeRhamIdent.constForm (isOpen_cubeDomain 3).measurableSet
    (isBounded_cubeDomain 3) (⟨{0}, by simp⟩ : formIdx 3 1)

theorem dxZero_ne_zero : dxZero ≠ 0 :=
  Feec.Models.Cube.DeRhamIdent.constForm_ne_zero _ _
    ((isOpen_cubeDomain 3).measure_pos MeasureTheory.volume
      ⟨fun _ => 1 / 4, Set.mem_univ_pi.2 fun _ => by norm_num⟩).ne' _

/-- **The constant `1`-form is not in `H̊(curl, Q)`**: if it were, its curl would be its classical
curl `0` (`d_min ≤ d_max`), so by exactness of `H̊Λ(Q)` it would be `grad τ` with `τ ∈ H̊¹(Q)`,
and Green's formula `⟪grad τ, dx₀⟫ = ⟪τ, div dx₀⟫ = 0` would give `‖dx₀‖² = 0`. -/
theorem dxZero_not_mem_D1 : dxZero ∉ D1.domain := by
  intro hc
  obtain ⟨hmax, emax⟩ := Feec.Domain.extDerivOp_smooth_mem_maximal_domain (isOpen_cubeDomain 3)
    (k := 1) (w := Feec.Models.Cube.DeRhamIdent.constFun (⟨{0}, by simp⟩ : formIdx 3 1))
    (fun _ => contDiff_const)
    (Feec.Models.Cube.DeRhamIdent.memLp_constFun (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) _)
    (fun t => Feec.Domain.memLp_of_continuous (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) ((extDerivOp ℝ 3 1).continuous_apply
        (Feec.Domain.extDerivOp_isOrderLE 1) (fun _ => contDiff_const) t))
  have hD : D1 ⟨dxZero, hc⟩ = 0 := by
    have hle := (extDerivOp ℝ 3 1).minimal_le_maximal (isOpen_cubeDomain 3)
    rw [hle.2 (x := ⟨dxZero, hc⟩) (y := ⟨_, hmax⟩) rfl, emax]
    exact Feec.Models.Cube.DeRhamIdent.toL2F_eq_zero
      (fun t y => Feec.Models.Cube.DeRhamIdent.extDerivOp_apply_const _ t y) _
  obtain ⟨x, hx⟩ := exists_D0_eq hD
  have hg := (extDerivOp ℝ 3 0).minimal_green (isOpen_cubeDomain 3)
    (Feec.Domain.extDerivOp_isOrderLE 0) x
    (ψ := Feec.Models.Cube.DeRhamIdent.constFun (⟨{0}, by simp⟩ : formIdx 3 1))
    (fun _ => contDiff_const)
    (Feec.Models.Cube.DeRhamIdent.memLp_constFun (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) _)
    (fun r => Feec.Domain.memLp_of_continuous (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) ((extDerivOp ℝ 3 0).formalAdj.continuous_apply
        (Feec.Domain.formalAdj_extDerivOp_isOrderLE 0) (fun _ => contDiff_const) r))
  rw [Feec.Models.Cube.DeRhamIdent.toL2F_eq_zero
    (fun r y => Feec.Models.Cube.DeRhamIdent.formalAdj_apply_const _ r y), inner_zero_right] at hg
  have hx' : D0 x = dxZero := hx
  change ⟪D0 x, dxZero⟫ = 0 at hg
  rw [hx', real_inner_self_eq_norm_sq] at hg
  exact dxZero_ne_zero (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hg))

/-- **`B = (d, −S)` does not have closed range** on the cube: its range lies in `H̊(curl, Q)`
(`grad H̊¹ + S⁰H̊¹(Q; ℝ³)`), which misses the constant `1`-forms, while it is dense
(`denseRange_B`). This is why the multiplier of (6.2) lives in the completion `W̌¹` (the thesis'
`H⁻¹(div, V)`, [QuennevilleBelair2015], §6.3) and not in `L²Λ¹(Q)`
(`Feec.BGG.WaveData.Wcheck_eq_range_of_isClosed` would apply under closed range); by the closed
range theorem, `|||·|||` is then not equivalent to the `L²` norm (not formalized here). -/
theorem not_isClosed_range_B : ¬ IsClosed (Set.range cubeWaveData.B) := by
  intro hcl
  have huniv : Set.range cubeWaveData.B = Set.univ := by
    rw [← hcl.closure_eq]; exact denseRange_B.closure_range
  obtain ⟨x, hx⟩ : dxZero ∈ Set.range cubeWaveData.B := huniv ▸ Set.mem_univ _
  have hx' : cubeWaveData.B (WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2)) = dxZero := hx
  rw [Feec.BGG.WaveData.B_toLp] at hx'
  refine dxZero_not_mem_D1 ?_
  rw [← hx']
  exact D1.domain.sub_mem (graphFst_mem_domain D1 _) (graphFst_mem_domain D1 _)

/-! ### Classical solutions of (6.2) with `L²` multiplier are solutions of (6.1)/(6.2) -/

set_option maxHeartbeats 4000000 in
/-- **A classical solution of (6.2) with an `L²` multiplier `λ(t)`** (`Feec.BGG.ExactWave`, the
exact solutions of `cubeWave_rate`) **is a solution of the multiplier problem (6.2)** of
`cubeWaveData`, with `Λ(t) = Jλ(t) ∈ W̌¹` and the same trajectories (read in the graph spaces);
in particular (`toSolution`) a solution of (6.1). -/
def exactWave_toMultiplierSolution {T : ℝ} {f : ℝ → Wv W1}
    (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) (lam : ℝ → W1)
    (hℓ : ∀ t μ, s.ℓ t μ = ⟪lam t, (μ : W1)⟫) :
    cubeWaveData.MultiplierSolution T f where
  σ t := D0.toGraphSpace (s.σ t)
  φ t := toGraphVec0 (s.φ t)
  u := s.u
  M := s.M
  ρ := s.ρ
  σ' t := (s.σ' t : W0)
  u' t := incl1 (s.u' t)
  M' := s.M'
  ρ' := s.ρ'
  cσ := (continuous_subtype_val.comp_continuousOn s.cσ).congr fun t _ =>
    LinearPMap.graphFst_toGraphSpace D0 (s.σ t)
  cu := (incl1CLM.continuous.comp_continuousOn s.cu).congr fun t _ => rfl
  cM := s.cM
  cρ := s.cρ
  dσ t ht := by
    have h := (D0.domain.subtypeL.hasFDerivAt).comp_hasDerivWithinAt t (s.dσ t ht)
    exact h.congr (fun r _ => LinearPMap.graphFst_toGraphSpace D0 (s.σ r))
      (LinearPMap.graphFst_toGraphSpace D0 (s.σ t))
  du t ht := by
    have h := incl1CLM.hasFDerivAt.comp_hasDerivWithinAt t (s.du t ht)
    exact h.congr (fun r _ => rfl) rfl
  dM := s.dM
  dρ := s.dρ
  eb t ht v := by
    have h := s.eb t ht v
    change ⟪incl1 (s.u' t), incl1 v⟫ + ⟪ιt1 (bggDt0 (toGraphVec0 (s.φ t))), incl1 v⟫ +
      ⟪s.M t, segS1 v⟫ + ⟪s.ρ t, piMap segD1 v⟫ = ⟪f t, incl1 v⟫
    rw [ιt1_bggDt0_toGraphVec0, ← inner_wv_U1, ← inner_wv_U1]
    exact h
  ec := s.ec
  ed := s.ed
  Λ t := ⟨cubeWaveData.J (lam t), cubeWaveData.J_mem_Wcheck _⟩
  ea t ht τ ψ := by
    have h := s.ea t ht (graphDom D0 τ) (rp ψ)
    rw [hℓ] at h
    change ⟪(s.σ' t : W0), D0.graphFst τ⟫ - ⟪incl1 (s.u t), ιt1 (bggDt0 ψ)⟫ -
      cubeWaveData.J (lam t) (WithLp.toLp 2 (τ, ψ)) = 0
    rw [Feec.BGG.WaveData.J_apply, Feec.BGG.WaveData.B_toLp]
    change ⟪(s.σ' t : W0), D0.graphFst τ⟫ - ⟪incl1 (s.u t), ιt1 (bggDt0 ψ)⟫ -
      ⟪lam t, D1.graphFst (bggD0 τ) - D1.graphFst (bggS0 ψ)⟫ = 0
    have e1 : D1.graphFst (bggD0 τ) - D1.graphFst (bggS0 ψ) =
        ((bggSegment.d0 (graphDom D0 τ) - bggSegment.S0 (rp ψ) : U1) : W1) := by
      rw [graphFst_bggD0, graphFst_bggS0, ← incl0_rp, Submodule.coe_sub, ← apply_graphDom D0 τ]
      rfl
    rw [e1, ιt1_bggDt0, ← inner_wv_U1]
    exact h
  ee t ht ζ := by
    have h := s.ee t ht
    have e : cubeWaveData.d0 (D0.toGraphSpace (s.σ t)) =
        cubeWaveData.S0 (toGraphVec0 (s.φ t)) := by
      rw [cubeWaveData_d0, cubeWaveData_S0, ιt0_toGraphVec0, LinearPMap.graphSnd_toGraphSpace]
      exact congrArg Subtype.val h
    rw [e, sub_self, inner_zero_left]

/-! ### Existence for the Hodge wave equation of (5.1) on the cube (Stone) -/

section Stone

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **Existence and uniqueness for the Hodge wave equation of (5.1) on the cube**
([QuennevilleBelair2015], Thm 4.6 for the complex (4.16) of §6.3; Stone's theorem): under the
regularity hypothesis (`bggHyps`), for data in `D(L)` and admissible forcing, the Hodge wave
equation `U' = L U + F` of the closed Hilbert complex `Γ̄ → (L²Λ¹)³ → L²Λ² × (L²Λ²)³` has a
classical solution, unique among strong and among weak solutions. -/
theorem bgg_wave_existsUnique (hR : CurlPotential)
    {U₀ : PiLp 2 (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2)))}
    (hU₀ : U₀ ∈ (bggHilb.toHilbertComplex (bggHyps hR) bggS0_injective).wave.domain) {a b : ℝ}
    {F : ℝ → PiLp 2 (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2)))}
    (hF : Evolution.ForcingClass.admissible
      (bggHilb.toHilbertComplex (bggHyps hR) bggS0_injective).wave a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution
        (bggHilb.toHilbertComplex (bggHyps hR) bggS0_injective).wave (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution
        (bggHilb.toHilbertComplex (bggHyps hR) bggS0_injective).wave (Icc a b) F V →
          EqOn V U (Icc a b) := by
  exact (bggHilb.toHilbertComplex (bggHyps hR)
    bggS0_injective).isSkewAdjoint_wave.existsUnique_classicalSolution hU₀ hF

end Stone

/-! ### The headline theorems -/

set_option maxHeartbeats 4000000 in
/-- **The Einstein–Bianchi wave system with weak symmetries on the cube: the semi-discrete method
(6.5) of Table 6.1** ([QuennevilleBelair2015], §6.3), under the regularity hypothesis
`CurlPotential`. There are smoothing parameters `p` (one smoother for both rows) and a constant
`C` such that, for the discretizations `cubeFEM hT hB N` (`S₀,ₕ = π¹S⁰`, `S₁,ₕ = π²S¹`):
1. (5.4) holds and the projections are bounded uniformly in `N`;
2. `grad` is injective on `P₂Λ̊⁰ ⊗ ℝ³` and `S₀,ₕ` maps `P₂Λ̊⁰ ⊗ ℝ³` onto `P₁⁻Λ̊¹`;
3. (corrected Prop 6.2) for every `T > 0` and source continuous on `[0,T]`, (6.5) has a solution
   with dynamic data `(σ₀, u₀, M₀, ρ₀)` iff (C2) `u₀ ⊥ grad (ker S₀,ₕ)`;
4. every solution of (6.5) is energy-stable:
   `E(t)^{1/2} ≤ E(0)^{1/2} + ∫₀ᵗ ‖f‖`, `E = ‖σₕ‖² + ‖uₕ‖² + ‖Mₕ‖² + ‖ρₕ‖²`;
5. (`O(h)` convergence) there is `K` such that for every classical solution of (6.2)
   (`Feec.BGG.ExactWave`) with `C²` states and time derivatives that vanish outside `Q` (flat at
   `∂Q`, a class much smaller than the thesis' boundary conditions, which put no condition on
   `M`, `ρ`; bound `L`) and `L²`-bounded multiplier, the solution of (6.5) from the elliptic projection (6.4) of the exact initial
   state satisfies `‖(σ, u, M, ρ)(t) − (σₕ, uₕ, Mₕ, ρₕ)(t)‖ ≤ K L (1 + t) h_N` on `[0,T]`. -/
theorem waveFEM (hR : CurlPotential) :
    ∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      (∀ N, (cubeFEM hT hB N).Compatible ∧ (cubeFEM hT hB N).Bounded (2 * C)) ∧
      (∀ N, Function.Injective (cubeWave hT hB N).dt0 ∧
        Function.Surjective (cubeWave hT hB N).S0) ∧
      (∀ (N : ℕ) {T : ℝ} (_ : 0 < T) {f : ℝ → (cubeFEM hT hB N).Vt1h},
        ContinuousOn f (Icc 0 T) → ∀ σ₀ u₀ M₀ ρ₀,
        (∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T f, s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧
          s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
          ∀ ψ, (cubeWave hT hB N).S0 ψ = 0 → ⟪u₀, (cubeWave hT hB N).dt0 ψ⟫ = 0) ∧
      (∀ (N : ℕ) {T : ℝ} {f : ℝ → (cubeFEM hT hB N).Vt1h}
        (s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T f), ContinuousOn f (Icc 0 T) →
        ∀ t ∈ Icc 0 T, √(‖s.σ t‖ ^ 2 + ‖s.u t‖ ^ 2 + ‖s.M t‖ ^ 2 + ‖s.ρ t‖ ^ 2) ≤
          √(‖s.σ 0‖ ^ 2 + ‖s.u 0‖ ^ 2 + ‖s.M 0‖ ^ 2 + ‖s.ρ 0‖ ^ 2) +
            ∫ r in (0:ℝ)..t, ‖f r‖) ∧
      ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_ : 0 < T) {f : ℝ → Wv W1}
        (_ : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
        0 ≤ L →
        (∀ t ∈ Icc 0 T, IsSmoothState L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
          IsSmoothState L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
        (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
        ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
          (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
            (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
              (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
              (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
                (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
          ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
            ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N := by
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrows := tableRows_uniform_cochainProjection
  obtain ⟨p, C, hT, hB, -⟩ := hrows
  exact ⟨p, C, hT, hB, fun N => ⟨cubeFEM_compatible hT hB N, cubeFEM_bounded hT hB N⟩,
    fun N => ⟨cubeWave_dt0_injective hT hB N, cubeWave_S0_surjective hT hB N⟩,
    fun N _ hT0 _ hf σ₀ u₀ M₀ ρ₀ => cubeWave_exists_iff_compatible_u hT hB N hT0 hf σ₀ u₀ M₀ ρ₀,
    fun N _ _ s hf => s.sqrt_energy_le hf, cubeWave_rate hT hB hCR.1 hCR.2⟩

set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `waveFEM`** (for any common smoother): the manufactured classical solution
`waveManufactured T` of (6.2) on the cube (`σ(t) = t σ̄`, `φ(t) = t φ̄`, `u = ū`, `ρ(t) = t curl ū`,
`λ = dg`, from the coupled static solution) has `σ(t), φ(t) ≠ 0` for `t ∈ (0,T]` and `u, λ ≠ 0`,
meets every hypothesis of item 5 of `waveFEM`, and under `CurlPotential` the discrete solutions of
(6.5) from the elliptic projection of its initial state converge at rate `h_N`, with `σₕ(t) ≠ 0`
for all large `N` at every `t ∈ (0,T]`. -/
theorem waveFEM_nonvacuous {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) (hR : CurlPotential) {T : ℝ}
    (hT0 : 0 < T) :
    (∀ t ∈ Ioc 0 T, (waveManufactured T).σ t ≠ 0 ∧ (waveManufactured T).φ t ≠ 0) ∧
    (∀ t, (waveManufactured T).u t ≠ 0) ∧ coupledMult ≠ 0 ∧
    ∃ (K : ℝ) (sh : (N : ℕ) → Feec.BGG.DiscreteSolution (cubeWave hT hB N) T
        (cubeSource hT hB N fun t => incl1 (t • (bggSegment.dt0 coupledφ + waveCurlCurlU)))),
      (∀ N, ∀ t ∈ Icc 0 T,
        √(‖(waveManufactured T).σ t - (sh N).σ t‖ ^ 2 +
          ‖(waveManufactured T).u t - (sh N).u t‖ ^ 2 +
          ‖(waveManufactured T).M t - (sh N).M t‖ ^ 2 +
          ‖(waveManufactured T).ρ t - (sh N).ρ t‖ ^ 2) ≤ K * (1 + t) * meshSize N) ∧
      ∀ t ∈ Ioc 0 T, ∀ᶠ N in atTop, ((sh N).σ t : U0) ≠ 0 := by
  have hyps := waveManufactured_hyps hT0
  obtain ⟨L, hL⟩ := hyps
  have hL0 := hL.1
  have hsm := hL.2.1
  have hmult := hL.2.2.1
  have hne := hL.2.2.2.1
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrate := cubeWave_rate hT hB hCR.1 hCR.2
  obtain ⟨K, hK0, hK⟩ := hrate
  have hf : ContinuousOn (fun t : ℝ => incl1 (t • (bggSegment.dt0 coupledφ + waveCurlCurlU)))
      (Icc 0 T) := by
    simp only [map_smul]
    exact (continuous_id.smul continuous_const).continuousOn
  have hsol := fun N => hK N hT0 hf (waveManufactured T) hL0 hsm hmult
  choose sh _ hsh using hsol
  refine ⟨hne, hL.2.2.2.2.1, hL.2.2.2.2.2, K * L, sh, fun N t ht => ?_, fun t ht => ?_⟩
  · refine (hsh N t ht).trans (le_of_eq ?_); ring
  · refine eventually_ne_zero_of_le (A := K * L * (1 + t)) (B := 1) (hne t ht).1 fun N => ?_
    have h := hsh N t (Ioc_subset_Icc_self ht)
    refine le_trans ?_ (h.trans (le_of_eq (by ring)))
    have a1 := sq_nonneg (‖(waveManufactured T).u t - (sh N).u t‖)
    have a2 := sq_nonneg (‖(waveManufactured T).M t - (sh N).M t‖)
    have a3 := sq_nonneg (‖(waveManufactured T).ρ t - (sh N).ρ t‖)
    exact Real.le_sqrt_of_sq_le (by nlinarith)

/-! ### `Γ ≅ H̊²(Q)` -/

section GammaH2

open MeasureTheory Topology Feec.Models.BoundedDomain

/-- The index of `0`-forms. -/
abbrev idx0 : formIdx 3 0 := ⟨∅, by simp⟩

/-- The index `{j}` of `dx_j`. -/
abbrev idxSingle (j : Fin 3) : formIdx 3 1 := ⟨{j}, by simp⟩

/-- `0`-forms as scalars. -/
def toScalar : W0 →L[ℝ] L2 ℝ (cubeDomain 3) :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : formIdx 3 0 => L2 ℝ (cubeDomain 3)) idx0

theorem toScalar_apply (σ : W0) : toScalar σ = σ idx0 := rfl

/-- The Hessian matrix `(∂ⱼ φᵢ)ᵢⱼ` of `(σ, φ) ∈ Γ`. -/
def hessOf (φ : Wv U0) : L2F ℝ (cubeDomain 3) Ix :=
  WithLp.toLp 2 fun ij => ((segD0 (φ ij.1) : U1) : W1) (idxSingle ij.2)

theorem smoothExt_grad (p : SmoothingParam (Fin 3 → ℝ)) (σ : U0) (i : Fin 3) (y : Fin 3 → ℝ) :
    fderiv ℝ (smoothExt (cubeDomain 3) p (((σ : W0) idx0 : L2 ℝ (cubeDomain 3)) :
      (Fin 3 → ℝ) → ℝ)) y (coordDir i) =
      p.factor * smoothExt (cubeDomain 3) p
        (((D0 σ : W1) (idxSingle i) : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ) y := by
  have h := apply_smoothExt_of_minimal (p := p) (isOpen_cubeDomain 3)
    (extDerivOp_isRowHomogeneous (n := 3) 0) σ 1 (idxSingle i) y
  rw [extDerivOp_zero_apply] at h
  simpa using h

theorem D0_apply_of_mem_Γ {σ : U0} {φ : Wv U0} (h : segD0 σ = segS0 φ) (i : Fin 3) :
    (D0 σ : W1) (idxSingle i) = (φ i : W0) idx0 := by
  have e : (D0 σ : W1) = wsL2 (Ω := cubeDomain 3) 0 (incl0 φ) := congrArg Subtype.val h
  rw [e, wsL2_zero_apply]
  rfl

theorem smoothExt_hess (p : SmoothingParam (Fin 3 → ℝ)) {σ : U0} {φ : Wv U0}
    (h : segD0 σ = segS0 φ) (i j : Fin 3) (x : Fin 3 → ℝ) :
    (hessOp 3).apply (fun _ => smoothExt (cubeDomain 3) p
        (((σ : W0) idx0 : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ)) (i, j) x =
      p.factor ^ 2 * smoothExt (cubeDomain 3) p
        (((D0 (φ i) : W1) (idxSingle j) : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ) x := by
  rw [hessOp_apply]
  have e1 : (fun y => fderiv ℝ (smoothExt (cubeDomain 3) p
      (((σ : W0) idx0 : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ)) y (coordDir i)) =
      fun y => p.factor * smoothExt (cubeDomain 3) p
        ((((φ i : U0) : W0) idx0 : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ) y := funext fun y => by
    rw [smoothExt_grad, D0_apply_of_mem_Γ h]
  simp only at e1 ⊢
  rw [e1]
  have hd : Differentiable ℝ (smoothExt (cubeDomain 3) p
      ((((φ i : U0) : W0) idx0 : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ)) :=
    (contDiff_smoothExt ((memLp_indicator (isOpen_cubeDomain 3).measurableSet _).locallyIntegrable
      (by norm_num))).differentiable (by simp)
  rw [fderiv_const_mul (hd x)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [smoothExt_grad]
  ring

/-- **`Γ ⊆ H̊²(Q)`**: if `(σ, φ) ∈ Γ` (`σ ∈ H̊¹`, `φ ∈ H̊¹(Q; ℝ³)`, `grad σ = φ`), then `σ` lies
in the domain of the minimal Hessian `H̊²(Q)` (the closure of `grad grad` on `C_c^∞(Q)`) and
`∇²σ = (∂ⱼ φᵢ)ᵢⱼ`. The smoothed functions `R σ` (dilation towards the centre, then
mollification, `Feec.Domain.smoothField`) are test functions with `∇²(R σ) = c² R (∂ⱼ φᵢ)`
(`smoothExt_hess`), and converge to `σ` and `(∂ⱼ φᵢ)` in `L²`. -/
theorem hessMin_of_mem_Γ {σ : U0} {φ : Wv U0} (h : segD0 σ = segS0 φ) :
    ∃ hd : toScalar σ ∈ (hessMin ℝ (isOpen_cubeDomain 3)).domain,
      hessMin ℝ (isOpen_cubeDomain 3) ⟨_, hd⟩ = hessOf φ := by
  have hΩ := isOpen_cubeDomain 3
  have hm := hΩ.measurableSet
  have hb := isBounded_cubeDomain 3
  have hstar := starBall 3
  have hloc : ∀ u : L2 ℝ (cubeDomain 3), LocallyIntegrable ((cubeDomain 3).indicator
      ((u : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ)) volume := fun u =>
    (memLp_indicator hm u).locallyIntegrable (by norm_num)
  have key : (toScalar σ, hessOf φ) ∈ (hessMin ℝ hΩ).graph := by
    rw [hessMin, ConstCoeffOp.minimalVia_graph _ _ _ (denseVia_id hΩ)]
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨η1, hη1, H1⟩ := exists_norm_smoothField_sub_lt hm (center 3) (σ : W0) (half_pos hε)
    obtain ⟨η2, hη2, H2⟩ := exists_norm_smoothField_sub_lt hm (center 3) (hessOf φ)
      (half_pos hε)
    set δ := min (min η1 η2) (min (η2 / 3) 1) with hδ
    have hδ0 : 0 < δ := lt_min (lt_min hη1 hη2) (lt_min (by positivity) one_pos)
    obtain ⟨p, hp, hc, hr⟩ := SmoothingParam.exists_isMinimal (center 3) (s := 1 / 4)
      (by norm_num) hδ0
    have hc1 : |p.factor - 1| < η1 := hc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hc2 : |p.factor - 1| < η2 := hc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hr1 : p.bump.rOut < η1 := hr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hr2 : p.bump.rOut < η2 := hr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hcs : |p.factor ^ 2 - 1| < η2 := by
      have h3 : |p.factor - 1| < η2 / 3 := hc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have h4 : |p.factor - 1| < 1 := hc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have e : p.factor ^ 2 - 1 = (p.factor - 1) * (p.factor + 1) := by ring
      rw [e, abs_mul]
      have h5 : |p.factor + 1| ≤ 3 := by
        rw [abs_le]; constructor <;> linarith [(abs_lt.1 h4).1, (abs_lt.1 h4).2]
      calc |p.factor - 1| * |p.factor + 1| ≤ |p.factor - 1| * 3 :=
            mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
        _ < η2 / 3 * 3 := by linarith
        _ = η2 := by ring
    have hφt : IsTestField (cubeDomain 3) fun _ : Unit =>
        smoothExt (cubeDomain 3) p (((σ : W0) idx0 : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ) :=
      fun _ => isTest_smoothExt hb hstar hp (hloc _)
    refine ⟨(toScalar (smoothField p hm (fun _ => 1) (σ : W0)),
      smoothField p hm (fun _ => p.factor ^ 2) (hessOf φ)), ⟨_, hφt, ?_, ?_⟩, ?_⟩
    · refine (WithLp.ext_iff 2).2 (funext fun _ => ?_)
      change toScalar (smoothField p hm (fun _ => 1) (σ : W0)) = toL2 (hφt ())
      rw [toScalar_apply, smoothField_apply, one_smul, smoothL2_apply]
      rfl
    · refine (WithLp.ext_iff 2).2 (funext fun ij => ?_)
      change smoothField p hm (fun _ => p.factor ^ 2) (hessOf φ) ij =
        toL2 ((hessOp 3).isTestField_apply hφt ij)
      rw [smoothField_apply, smoothL2_apply, ← MemLp.toLp_const_smul]
      refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [smoothExt_hess p h ij.1 ij.2 x]
      rfl
    · rw [Prod.dist_eq, max_lt_iff, dist_comm, dist_eq_norm, dist_comm, dist_eq_norm,
        ← map_sub]
      constructor
      · calc ‖toScalar (smoothField p hm (fun _ => 1) (σ : W0) - (σ : W0))‖
            ≤ ‖smoothField p hm (fun _ => 1) (σ : W0) - (σ : W0)‖ := by
              rw [toScalar_apply]; exact PiLp.norm_apply_le _ _
          _ < ε / 2 := H1 p hp.center_eq hc1 hr1 1 (by simp [hη1])
          _ < ε := half_lt_self hε
      · exact (H2 p hp.center_eq hc2 hr2 _ hcs).trans (half_lt_self hε)
  obtain ⟨y, hy⟩ := (hessMin ℝ hΩ).mem_graph_iff.1 key
  have hy1 : (y : L2 ℝ (cubeDomain 3)) = toScalar σ := hy.1
  refine ⟨hy1 ▸ y.2, ?_⟩
  have hy' : y = ⟨toScalar σ, hy1 ▸ y.2⟩ := Subtype.ext hy1
  rw [← hy']
  exact hy.2

/-! ### `H̊²(Q) ⊆ Γ` -/

/-- **Integration by parts for test functions**:
`⟪∂ⱼψ, ∂ⱼψ'⟫ = -⟪ψ, ∂ⱼ∂ⱼψ'⟫` in `L²(Q)`. -/
theorem inner_toL2_fderiv {ψ ψ' : (Fin 3 → ℝ) → ℝ} (hψ : IsTest (cubeDomain 3) ψ)
    (hψ' : IsTest (cubeDomain 3) ψ') (v : Fin 3 → ℝ) :
    ⟪toL2 (hψ.fderiv_apply v), toL2 (hψ'.fderiv_apply v)⟫_ℝ =
      -⟪toL2 hψ, toL2 ((hψ'.fderiv_apply v).fderiv_apply v)⟫_ℝ := by
  rw [inner_toL2, inner_toL2]
  have e1 : ∫ x, (starRingEnd ℝ) ((toL2 (hψ.fderiv_apply v) : L2 ℝ (cubeDomain 3)) x) *
      fderiv ℝ ψ' x v ∂volume.restrict (cubeDomain 3) =
      ∫ x, (starRingEnd ℝ) (fderiv ℝ ψ x v) * fderiv ℝ ψ' x v ∂volume.restrict (cubeDomain 3) :=
    integral_congr_ae (by
      filter_upwards [coeFn_toL2 (hψ.fderiv_apply v)] with x hx
      rw [hx])
  have e2 : ∫ x, (starRingEnd ℝ) ((toL2 hψ : L2 ℝ (cubeDomain 3)) x) *
      fderiv ℝ (fun y => fderiv ℝ ψ' y v) x v ∂volume.restrict (cubeDomain 3) =
      ∫ x, (starRingEnd ℝ) (ψ x) * fderiv ℝ (fun y => fderiv ℝ ψ' y v) x v
        ∂volume.restrict (cubeDomain 3) :=
    integral_congr_ae (by
      filter_upwards [coeFn_toL2 hψ] with x hx
      rw [hx])
  rw [e1, e2, integral_restrict_of_eq_zero (fun x hx => by
      rw [(hψ.fderiv_apply v).eq_zero_of_notMem hx, map_zero, zero_mul]),
    integral_restrict_of_eq_zero (fun x hx => by
      rw [hψ.eq_zero_of_notMem hx, map_zero, zero_mul])]
  exact integral_conj_fderiv_mul hψ
    ((hψ'.fderiv_apply v).contDiff.of_le (by simp)) v

theorem exists_idxSingle (t : formIdx 3 1) : ∃ j, t = idxSingle j := by
  have h : t.1.card = 1 := by have := t.2; omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h
  exact ⟨j, Subtype.ext hj⟩

theorem idxSingle_injective : Function.Injective idxSingle := fun i j h => by
  have := congrArg Subtype.val h
  simpa using this

/-- The index `j` of `t = {j}`. -/
def idxOfSingle (t : formIdx 3 1) : Fin 3 := (exists_idxSingle t).choose

theorem idxSingle_idxOfSingle (t : formIdx 3 1) : idxSingle (idxOfSingle t) = t := (exists_idxSingle t).choose_spec.symm

theorem idxOfSingle_idxSingle (j : Fin 3) : idxOfSingle (idxSingle j) = j := idxSingle_injective (idxSingle_idxOfSingle _)

/-- A scalar test function as a `0`-form. -/
def form0 {ψ : (Fin 3 → ℝ) → ℝ} (hψ : IsTest (cubeDomain 3) ψ) : W0 :=
  testField (φ := fun _ : formIdx 3 0 => ψ) fun _ => hψ

theorem form0_mem {ψ : (Fin 3 → ℝ) → ℝ} (hψ : IsTest (cubeDomain 3) ψ) : form0 hψ ∈ D0.domain :=
  (extDerivOp ℝ 3 0).testField_mem_minimal_domain (isOpen_cubeDomain 3) _

theorem D0_form0_apply {ψ : (Fin 3 → ℝ) → ℝ} (hψ : IsTest (cubeDomain 3) ψ) (j : Fin 3) :
    (D0 ⟨form0 hψ, form0_mem hψ⟩ : W1) (idxSingle j) = toL2 (hψ.fderiv_apply (coordDir j)) := by
  have e : (D0 ⟨form0 hψ, form0_mem hψ⟩ : W1) = testField ((extDerivOp ℝ 3 0).isTestField_apply
      (φ := fun _ : formIdx 3 0 => ψ) fun _ => hψ) :=
    (extDerivOp ℝ 3 0).minimal_testField (isOpen_cubeDomain 3) _
  rw [e, testField_apply]
  exact toL2_congr _ _ (funext fun x => extDerivOp_zero_apply _ j x)

/-- **`H̊²(Q) ⊆ Γ`**: every `v` in the domain of the minimal Hessian is `σ` of a pair
`(σ, φ) ∈ Γ`. For test functions `ψₙ → v` with `∇²ψₙ → ∇²v`, integration by parts
(`inner_toL2_fderiv`) gives `‖∂ⱼ(ψₙ − ψₘ)‖² ≤ ‖ψₙ − ψₘ‖ ‖∇²(ψₙ − ψₘ)‖`, so `∇ψₙ` converges, and
the closedness of `grad` on `H̊¹` gives `v ∈ H̊¹` and `∂ⱼ v ∈ H̊¹`. -/
theorem mem_Γ_of_hessMin {v : L2 ℝ (cubeDomain 3)}
    (hv : v ∈ (hessMin ℝ (isOpen_cubeDomain 3)).domain) :
    ∃ σ : U0, ∃ φ : Wv U0, toScalar σ = v ∧ segD0 σ = segS0 φ := by
  have hΩ := isOpen_cubeDomain 3
  set H := hessMin ℝ hΩ ⟨v, hv⟩
  have hcl : (v, H) ∈ closure ((hessOp 3).testGraphVia (L2.toL2F ℝ (cubeDomain 3))
      (LinearIsometry.id : L2F ℝ (cubeDomain 3) Ix →ₗᵢ[ℝ] L2F ℝ (cubeDomain 3) Ix) : Set _) := by
    have hgraph : (hessMin ℝ hΩ).graph = ((hessOp 3).testGraphVia (L2.toL2F ℝ (cubeDomain 3))
        (LinearIsometry.id : L2F ℝ (cubeDomain 3) Ix →ₗᵢ[ℝ] L2F ℝ (cubeDomain 3) Ix)).topologicalClosure :=
      ConstCoeffOp.minimalVia_graph _ _ _ (denseVia_id hΩ)
    have := (hessMin ℝ hΩ).mem_graph ⟨v, hv⟩
    rw [hgraph] at this
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at this
  obtain ⟨b, hb, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  choose ψ hψ h1 h2 using hb
  set f : ℕ → (Fin 3 → ℝ) → ℝ := fun n => ψ n ()
  have hf : ∀ n, IsTest (cubeDomain 3) (f n) := fun n => hψ n ()
  have hb1 : ∀ n, (b n).1 = toL2 (hf n) := fun n => congrArg (fun w => w ()) (h1 n)
  have hb2 : ∀ n (i j : Fin 3), (b n).2 (i, j) =
      toL2 (((hf n).fderiv_apply (coordDir i)).fderiv_apply (coordDir j)) := fun n i j => by
    have := congrArg (fun w => w (i, j)) (h2 n)
    simp only [LinearIsometry.id_apply, testField_apply] at this
    rw [this]
    exact toL2_congr _ _ (funext fun x => hessOp_apply _ _ x)
  have ht1 : Tendsto (fun n => (b n).1) atTop (𝓝 v) := (continuous_fst.tendsto _).comp hlim
  have ht2 : Tendsto (fun n => (b n).2) atTop (𝓝 H) := (continuous_snd.tendsto _).comp hlim
  -- the first derivatives converge
  set g : Fin 3 → ℕ → L2 ℝ (cubeDomain 3) := fun j n => toL2 ((hf n).fderiv_apply (coordDir j))
  have hbound : ∀ j n m, ‖g j n - g j m‖ ^ 2 ≤ ‖(b n).1 - (b m).1‖ * ‖(b n).2 - (b m).2‖ := by
    intro j n m
    have e : ∀ n' m', ⟪g j n', g j m'⟫_ℝ = -⟪(b n').1, (b m').2 (j, j)⟫_ℝ := fun n' m' => by
      rw [hb1, hb2]; exact inner_toL2_fderiv (hf n') (hf m') (coordDir j)
    have hn : ‖g j n - g j m‖ ^ 2 = -⟪(b n).1 - (b m).1, (b n).2 (j, j) - (b m).2 (j, j)⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        inner_sub_left, inner_sub_right, inner_sub_right, e, e, e, e]
      ring
    rw [hn]
    calc -⟪(b n).1 - (b m).1, (b n).2 (j, j) - (b m).2 (j, j)⟫_ℝ
        ≤ ‖(b n).1 - (b m).1‖ * ‖(b n).2 (j, j) - (b m).2 (j, j)‖ :=
          (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      _ ≤ ‖(b n).1 - (b m).1‖ * ‖(b n).2 - (b m).2‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have := PiLp.norm_apply_le ((b n).2 - (b m).2) (j, j)
          simpa using this
  have hcauchy : ∀ j, CauchySeq (g j) := by
    intro j
    obtain ⟨R, hR, hRb⟩ := cauchySeq_bdd ht2.cauchySeq
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 ht1.cauchySeq (ε ^ 2 / R) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h3 := hbound j m n
    have h4 := hN m hm n hn
    have h5 := hRb m n
    rw [dist_eq_norm] at h4 h5
    have h6 : ‖g j m - g j n‖ ^ 2 < ε ^ 2 := by
      calc ‖g j m - g j n‖ ^ 2 ≤ ‖(b m).1 - (b n).1‖ * ‖(b m).2 - (b n).2‖ := h3
        _ ≤ ‖(b m).1 - (b n).1‖ * R := mul_le_mul_of_nonneg_left h5.le (norm_nonneg _)
        _ < ε ^ 2 / R * R := mul_lt_mul_of_pos_right h4 hR
        _ = ε ^ 2 := by field_simp
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 h6
  choose gl hgl using fun j => cauchySeq_tendsto_of_complete (hcauchy j)
  have hD0 : D0.IsClosed := (extDerivOp ℝ 3 0).isClosed_minimal hΩ
  have hcl0 : IsClosed (D0.graph : Set (W0 × W1)) := hD0
  -- `v ∈ H̊¹`, `grad v = (gl j)ⱼ`
  set Gl : W1 := WithLp.toLp 2 fun t => gl (idxOfSingle t)
  have hσl : ((WithLp.toLp 2 fun _ => v : W0), Gl) ∈ D0.graph := by
    refine hcl0.mem_of_tendsto (b := atTop) (f := fun n => ((form0 (hf n) : W0),
      (D0 ⟨form0 (hf n), form0_mem (hf n)⟩ : W1))) ?_
      (Eventually.of_forall fun n => D0.mem_graph ⟨form0 (hf n), form0_mem (hf n)⟩)
    refine Tendsto.prodMk_nhds ?_ ?_
    · have e : (fun n => (form0 (hf n) : W0)) = fun n => WithLp.toLp 2 fun _ => (b n).1 :=
        funext fun n => by rw [hb1]; rfl
      rw [e]
      exact ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 fun _ => ht1)
    · have e : (fun n => (D0 ⟨form0 (hf n), form0_mem (hf n)⟩ : W1)) =
          fun n => WithLp.toLp 2 fun t => g (idxOfSingle t) n := funext fun n => by
        refine (WithLp.ext_iff 2).2 (funext fun t => ?_)
        obtain ⟨j, rfl⟩ := exists_idxSingle t
        change (D0 ⟨form0 (hf n), form0_mem (hf n)⟩ : W1) (idxSingle j) = g (idxOfSingle (idxSingle j)) n
        rw [D0_form0_apply, idxOfSingle_idxSingle]
      rw [e]
      exact ((PiLp.continuous_toLp 2 _).tendsto _).comp
        (tendsto_pi_nhds.2 fun t => hgl (idxOfSingle t))
  -- `∂ⱼ v ∈ H̊¹`
  have hτl : ∀ j, ((WithLp.toLp 2 fun _ => gl j : W0),
      (WithLp.toLp 2 fun t => H (j, idxOfSingle t) : W1)) ∈ D0.graph := fun j => by
    refine hcl0.mem_of_tendsto (b := atTop) (f := fun n => ((form0 ((hf n).fderiv_apply (coordDir j)) : W0),
      (D0 ⟨_, form0_mem ((hf n).fderiv_apply (coordDir j))⟩ : W1))) ?_
      (Eventually.of_forall fun n =>
        D0.mem_graph ⟨_, form0_mem ((hf n).fderiv_apply (coordDir j))⟩)
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 fun _ => hgl j)
    · have e : (fun n => (D0 ⟨_, form0_mem ((hf n).fderiv_apply (coordDir j))⟩ : W1)) =
          fun n => WithLp.toLp 2 fun t => (b n).2 (j, idxOfSingle t) := funext fun n => by
        refine (WithLp.ext_iff 2).2 (funext fun t => ?_)
        obtain ⟨k, rfl⟩ := exists_idxSingle t
        change (D0 ⟨_, form0_mem ((hf n).fderiv_apply (coordDir j))⟩ : W1) (idxSingle k) =
          (b n).2 (j, idxOfSingle (idxSingle k))
        rw [D0_form0_apply, idxOfSingle_idxSingle, hb2]
      rw [e]
      exact ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 fun t =>
        ((L2F.continuous_apply (j, idxOfSingle t)).tendsto _).comp ht2)
  obtain ⟨y, hy1, hy2⟩ := D0.mem_graph_iff.1 hσl
  have hτ : ∀ j, (WithLp.toLp 2 fun _ => gl j : W0) ∈ D0.domain := fun j =>
    LinearPMap.mem_domain_of_mem_graph (hτl j)
  refine ⟨y, WithLp.toLp 2 fun j => ⟨_, hτ j⟩, by rw [toScalar_apply, hy1], Subtype.ext ?_⟩
  change (D0 y : W1) = wsL2 (Ω := cubeDomain 3) 0 (incl0 (WithLp.toLp 2 fun j => ⟨_, hτ j⟩))
  rw [hy2]
  refine (WithLp.ext_iff 2).2 (funext fun t => ?_)
  obtain ⟨j, rfl⟩ := exists_idxSingle t
  change gl (idxOfSingle (idxSingle j)) = wsL2 (Ω := cubeDomain 3) 0 (incl0 (WithLp.toLp 2 fun j => ⟨_, hτ j⟩))
    (idxSingle j)
  rw [wsL2_zero_apply, idxOfSingle_idxSingle]
  rfl

theorem toScalar_injective : Function.Injective toScalar := fun x y h => by
  refine (WithLp.ext_iff 2).2 (funext fun t => ?_)
  have ht : t = idx0 := Subtype.ext (Finset.card_eq_zero.1 (by have := t.2; omega))
  rw [ht]
  exact h

theorem segS0_injective : Function.Injective segS0 := fun φ ψ h => by
  refine (WithLp.ext_iff 2).2 (funext fun a => Subtype.ext ((WithLp.ext_iff 2).2
    (funext fun t => ?_)))
  have ht : t = idx0 := Subtype.ext (Finset.card_eq_zero.1 (by have := t.2; omega))
  rw [ht]
  have e := congrArg (fun w : U1 => (w : W1) (idxSingle a)) h
  simp only [coe_segS0, wsL2_zero_apply] at e
  exact e

/-- **`Γ ≅ H̊²(Q)`** ([QuennevilleBelair2015], §6.3): `(σ, φ) ↦ σ` maps
`Γ = {(σ, φ) ∈ H̊¹(Q) × H̊¹(Q; ℝ³) : grad σ = φ}` (`Feec.BGG.Segment.Γ` of the cube data
`bggSegment`) bijectively onto the domain `H̊²(Q)` of the minimal Hessian of
`Feec.Models.BoundedDomain` (the first space of `Feec.Models.BoundedDomain.bggComplex` on `Q`),
and the first BGG operator `D₀(σ, φ) = grad φ` is the Hessian:
`(∇²σ)ᵢⱼ = (grad φᵢ)ⱼ` (`hessOf`). -/
theorem gamma_equiv_hessMin :
    Set.InjOn (fun x : U0 × Wv U0 => toScalar (x.1 : W0)) bggSegment.Γ ∧
      (∀ v, v ∈ (hessMin ℝ (isOpen_cubeDomain 3)).domain ↔
        ∃ x ∈ bggSegment.Γ, toScalar (x.1 : W0) = v) ∧
      ∀ x ∈ bggSegment.Γ, ∃ hd : toScalar (x.1 : W0) ∈ (hessMin ℝ (isOpen_cubeDomain 3)).domain,
        hessMin ℝ (isOpen_cubeDomain 3) ⟨_, hd⟩ = hessOf x.2 := by
  refine ⟨fun x hx y hy hxy => ?_, fun v => ⟨fun hv => ?_, ?_⟩, fun x hx => hessMin_of_mem_Γ (bggSegment.mem_Γ.1 hx)⟩
  · have h1 : x.1 = y.1 := Subtype.ext (toScalar_injective hxy)
    have h2 : x.2 = y.2 := segS0_injective (by
      have ex : bggSegment.d0 x.1 = bggSegment.S0 x.2 := bggSegment.mem_Γ.1 hx
      have ey : bggSegment.d0 y.1 = bggSegment.S0 y.2 := bggSegment.mem_Γ.1 hy
      change segS0 x.2 = segS0 y.2
      rw [← show bggSegment.S0 x.2 = segS0 x.2 from rfl, ← ex, h1, ey]; rfl)
    exact Prod.ext h1 h2
  · obtain ⟨σ, φ, hσ, h⟩ := mem_Γ_of_hessMin hv
    exact ⟨(σ, φ), bggSegment.mem_Γ.2 h, hσ⟩
  · rintro ⟨x, hx, rfl⟩
    exact (hessMin_of_mem_Γ (bggSegment.mem_Γ.1 hx)).1

end GammaH2

end Feec.EinsteinBianchi.WaveFEM
