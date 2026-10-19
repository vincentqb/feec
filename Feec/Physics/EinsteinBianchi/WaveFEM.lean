module

public import Feec.Models.Cube.WeakSymmetryWave
public import Feec.HilbertComplex.HodgeWave

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
* **`waveFEM`**: under `CurlPotential`, for one smoother: (5.4) and uniform bounds; `grad`
  injective and `S₀,ₕ` onto; corrected Prop 6.2 for (6.5); energy stability; `O(h)` convergence
  for `C²` classical solutions. **`waveFEM_nonvacuous`**: a nontrivial manufactured solution meets
  all hypotheses and its discrete `σₕ(t)` converge and are nonzero for large `N`.

## Gaps

* The identification of `Γ` with `H̊²(Q)` and of (6.1) for `bggHilb` with the system
  `Feec.Models.BoundedDomain.bggComplex_eq61` (matrix model) is not built: it needs
  `{σ ∈ H̊¹ | ∇σ ∈ H̊¹(Q; ℝ³)} = H̊²(Q)` and an isometry `L²Λ¹(Q)³ ≅ L²(Q; ℝ³ˣ³)` intertwining
  `(S¹, curl)` with `(skwL, curl)`. Consequently the TSD datum of
  `Feec.Counterexamples.BoundedBGG.bggComplex_verdict` (whose solution leaves `L²(TSD)`) is not
  transported to this model, and the convergence theorem is not applied to it.
* The mirror variant of the scheme (`Feec.Models.Cube.MirrorBGG`) is not discretized.

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

/-- The inclusion `H̊Λ¹(Q)³ → L²Λ¹(Q)³` as a bounded map (an isometry). -/
def incl1L : Wv U1 →L[ℝ] Wv W1 :=
  LinearMap.mkContinuous incl1 1 fun x => by rw [norm_incl1, one_mul]

theorem incl1L_apply (x : Wv U1) : incl1L x = incl1 x := rfl

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
def exactWave_toMultiplierSolution {T : ℝ} {f : ℝ → Wv U1}
    (s : Feec.BGG.ExactWave bggSegment T f) (lam : ℝ → W1)
    (hℓ : ∀ t μ, s.ℓ t μ = ⟪lam t, (μ : W1)⟫) :
    cubeWaveData.MultiplierSolution T (fun t => incl1 (f t)) where
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
  cu := (incl1L.continuous.comp_continuousOn s.cu).congr fun t _ => rfl
  cM := s.cM
  cρ := s.cρ
  dσ t ht := by
    have h := (D0.domain.subtypeL.hasFDerivAt).comp_hasDerivWithinAt t (s.dσ t ht)
    exact h.congr (fun r _ => LinearPMap.graphFst_toGraphSpace D0 (s.σ r))
      (LinearPMap.graphFst_toGraphSpace D0 (s.σ t))
  du t ht := by
    have h := incl1L.hasFDerivAt.comp_hasDerivWithinAt t (s.du t ht)
    exact h.congr (fun r _ => rfl) rfl
  dM := s.dM
  dρ := s.dρ
  eb t ht v := by
    have h := s.eb t ht v
    change ⟪incl1 (s.u' t), incl1 v⟫ + ⟪ιt1 (bggDt0 (toGraphVec0 (s.φ t))), incl1 v⟫ +
      ⟪s.M t, segS1 v⟫ + ⟪s.ρ t, piMap segD1 v⟫ = ⟪incl1 (f t), incl1 v⟫
    rw [ιt1_bggDt0_toGraphVec0, ← inner_wv_U1, ← inner_wv_U1, ← inner_wv_U1]
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
   (`Feec.BGG.ExactWave`) with `C²` states and time derivatives (bound `L`) and `L²`-bounded
   multiplier, the solution of (6.5) from the elliptic projection (6.4) of the exact initial
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
      ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_ : 0 < T) {f : ℝ → Wv U1}
        (_ : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T f) {L : ℝ}, 0 ≤ L →
        (∀ t ∈ Icc 0 T, IsSmoothState L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
          IsSmoothState L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
        (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
        ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T
            (fun t => (cubeFEM hT hB N).Vt1h.orthogonalProjectionOnto (f t)),
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
        (fun t => (cubeFEM hT hB N).Vt1h.orthogonalProjectionOnto
          (t • (bggSegment.dt0 coupledφ + waveCurlCurlU)))),
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
  have hf : ContinuousOn (fun t : ℝ => t • (bggSegment.dt0 coupledφ + waveCurlCurlU)) (Icc 0 T) :=
    (continuous_id.smul continuous_const).continuousOn
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

end Feec.EinsteinBianchi.WaveFEM
