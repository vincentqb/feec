module

public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.HilbertComplex.Approximation.HeatFEEC
public import Feec.HilbertComplex.Approximation.DissipGalerkin
public import Feec.Semigroup.DissipativePerturbation
public import Feec.Evolution.Perturbation
public import Feec.ForMathlib.InnerProductSpace.Isometry

/-!
# The perturbed FEEC theorem

A dissipative FEEC discretization with a dense core keeps its verdicts under a bounded perturbation
`B` with `A + B` dissipative and consistent discrete perturbations `Bₕ`.

## Main results

* `DissipFEEC.tendsto_incl_discreteRes`: a dense core gives consistent discrete resolvents.
* `perturbFEEC`: the perturbed FEEC theorem.
* `constrainedFEEC_perturbed`: the perturbed wave and heat equations.
* `ImpedanceTriple.GalerkinData.perturbed_verdict`: perturbed impedance problems.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

/-! ### Laplace identities of the resolvents, Trotter–Kato -/

section TrotterKato

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {κ : Type*}

namespace DissipFEEC

variable (F : DissipFEEC.{u} A κ)

theorem resolvent_eq_integral_add (z : E) {T : ℝ} (hT : 0 ≤ T) :
    Operator.resolvent A 1 z =
      (∫ s in (0 : ℝ)..T, Real.exp (-s) • F.S s z) +
        Real.exp (-T) • F.S T (Operator.resolvent A 1 z) := by
  have hR := F.isMDissipative.isResolvent_one
  have h := integral_exp_neg_smul_sub_eq hT (F.continuousOn_S (Operator.resolvent A 1 z) T)
    (F.continuousOn_S (A (hR.toDomain z)) T)
    fun s hs => F.isMDissipative.hasDerivWithinAt_semigroup (hR.toDomain z) hs.1
  have e : ∀ s, F.S s (Operator.resolvent A 1 z) - F.S s (A (hR.toDomain z)) = F.S s z :=
    fun s => by rw [← _root_.map_sub]; congr 1; simpa using hR.sub_apply_toDomain z
  simp only [e] at h
  rw [h, sub_add_cancel, F.S_def, C0Semigroup.S_zero_apply]

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem discreteRes_eq_integral_add (h : κ) (v : F.X h) {T : ℝ} (hT : 0 ≤ T) :
    F.discreteRes h v =
      (∫ s in (0 : ℝ)..T, Real.exp (-s) • (F.group h).S s v) +
        Real.exp (-T) • (F.group h).S T (F.discreteRes h v) := by
  set y := F.discreteRes h v
  have hc : Continuous fun s : ℝ => (F.group h).S s y := (F.group h).strongCont y
  have h' := integral_exp_neg_smul_sub_eq (u := fun s => (F.group h).S s y)
    (w := fun s => F.L h ((F.group h).S s y)) hT hc.continuousOn
    ((F.L h).continuous.comp hc).continuousOn fun s _ =>
      (ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply (F.L h) y s).hasDerivWithinAt
  have e : ∀ s, (F.group h).S s y - F.L h ((F.group h).S s y) = (F.group h).S s v := fun s => by
    have hcomm := (ContinuousLinearMap.commute_exp_ofReal_smul (F.L h) s).eq
    have e1 : F.L h ((F.group h).S s y) = (F.group h).S s (F.L h y) :=
      congrArg (fun T : F.X h →L[𝕜] F.X h => T y) hcomm
    rw [e1, ← _root_.map_sub, F.discreteRes_sub h v]
  simp only [e] at h'
  rw [h', sub_add_cancel, (F.group h).map_zero]
  rfl

/-- **Trotter–Kato, the converse direction**: with a dense core, `ιₕ (1 - Lₕ)⁻¹ πₕ z → (1 - A)⁻¹ z`
for every `z`. [Pazy1983], §3.4 -/
theorem tendsto_incl_discreteRes (Z : F.Core) (hZ : Z.Data.topologicalClosure = ⊤) (z : E) :
    Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)) := by
  have hz : z ∈ Z.Data.topologicalClosure := hZ ▸ Submodule.mem_top
  set C := F.boundConst
  have hC := F.boundConst_nonneg
  set M := (C * C + 1) * ‖z‖
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ Real.exp (-T) * M < ε / 2 := by
    have h0 : Tendsto (fun T : ℝ => Real.exp (-T) * M) atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const M
    exact ((eventually_ge_atTop 0).and (h0.eventually (gt_mem_nhds (half_pos hε)))).exists
  set η := ε / (2 * (T + 1))
  have hη : 0 < η := by positivity
  have hηT : η * T < ε / 2 := by
    rw [show η * T = ε / 2 * (T / (T + 1)) by simp only [η]; field_simp]
    exact mul_lt_of_lt_one_right (half_pos hε) ((div_lt_one (by linarith)).2 (by linarith))
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    (dissipFEEC_converges F Z T hz (tendsto_incl_proj F Z hz)) η hη] with h hh
  set v := F.proj h z
  have hsol : Continuous fun s => F.sol h v s :=
    (F.incl h).continuous.comp ((F.group h).strongCont v)
  have hi1 : IntervalIntegrable (fun s => Real.exp (-s) • F.sol h v s) MeasureTheory.volume 0 T :=
    ((Real.continuous_exp.comp continuous_neg).smul hsol).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun s => Real.exp (-s) • F.S s z) MeasureTheory.volume 0 T :=
    ((Real.continuous_exp.comp continuous_neg).continuousOn.smul
      (F.continuousOn_S z T)).intervalIntegrable_of_Icc hT0
  -- the discrete Laplace identity, read in `E`
  have e1 : F.incl h (F.discreteRes h v) =
      (∫ s in (0 : ℝ)..T, Real.exp (-s) • F.sol h v s) +
        Real.exp (-T) • F.incl h ((F.group h).S T (F.discreteRes h v)) := by
    have hi : IntervalIntegrable (fun s => Real.exp (-s) • (F.group h).S s v)
        MeasureTheory.volume 0 T :=
      ((Real.continuous_exp.comp continuous_neg).smul
        ((F.group h).strongCont v)).intervalIntegrable 0 T
    have := ((F.incl h).restrictScalars ℝ).intervalIntegral_comp_comm hi
    nth_rw 1 [F.discreteRes_eq_integral_add h v hT0]
    rw [_root_.map_add, ContinuousLinearMap.map_smul_of_tower]
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul_of_tower]
      at this
    rw [← this]
    rfl
  have hint : ‖(∫ s in (0 : ℝ)..T, Real.exp (-s) • F.sol h v s) -
      ∫ s in (0 : ℝ)..T, Real.exp (-s) • F.S s z‖ ≤ η * T := by
    rw [← intervalIntegral.integral_sub hi1 hi2]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_).trans_eq
      (by rw [sub_zero, abs_of_nonneg hT0])
    rw [uIoc_of_le hT0] at hs
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hs.1])
    have h2 : ‖F.sol h v s - F.S s z‖ ≤ η := by
      rw [norm_sub_rev, ← dist_eq_norm]; exact (hh s ⟨hs.1.le, hs.2⟩).le
    nlinarith [norm_nonneg (F.sol h v s - F.S s z)]
  have hrest : ‖Real.exp (-T) • (F.incl h ((F.group h).S T (F.discreteRes h v)) -
      F.S T (Operator.resolvent A 1 z))‖ ≤ Real.exp (-T) * M := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (Real.exp_pos _).le
    have hv : ‖v‖ ≤ C * ‖z‖ := ((F.proj h).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))
    have ha : ‖F.incl h ((F.group h).S T (F.discreteRes h v))‖ ≤ C * (C * ‖z‖) :=
      (F.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
        (((F.norm_group_apply_le h hT0 _).trans (F.norm_discreteRes_apply_le h v)).trans hv) hC)
    have hb : ‖F.S T (Operator.resolvent A 1 z)‖ ≤ ‖z‖ :=
      (F.norm_S_apply_le hT0 _).trans (by
        simpa using F.isMDissipative.norm_resolvent_apply_le one_pos z)
    simp only [M]
    nlinarith
  rw [dist_eq_norm, e1, F.resolvent_eq_integral_add z hT0]
  calc _ = ‖((∫ s in (0 : ℝ)..T, Real.exp (-s) • F.sol h v s) -
          ∫ s in (0 : ℝ)..T, Real.exp (-s) • F.S s z) +
        Real.exp (-T) • (F.incl h ((F.group h).S T (F.discreteRes h v)) -
          F.S T (Operator.resolvent A 1 z))‖ := by rw [smul_sub]; congr 1; abel
    _ ≤ η * T + Real.exp (-T) * M := (norm_add_le _ _).trans (add_le_add hint hrest)
    _ < ε := by linarith

end DissipFEEC

end TrotterKato

/-! ### Bounded perturbations of dissipative FEEC discretizations -/

section Perturbation

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →ₗ.[𝕜] E} {κ : Type*}

namespace DissipFEEC

variable (F : DissipFEEC.{u} A κ)

/-- A bounded perturbation `B` of `A`, `A + B` dissipative, with consistent discrete `Bₕ`. -/
structure Perturbation where
  /-- the bounded perturbation -/
  B : E →L[𝕜] E
  isDissipative : ((B : E →ₗ[𝕜] E) +ᵥ A).IsDissipative
  /-- the discrete perturbations -/
  Bh : ∀ h, F.X h →L[𝕜] F.X h
  dissipative : ∀ h x, RCLike.re ⟪(F.L h + Bh h) x, x⟫_𝕜 ≤ 0
  bound : ∃ C, ∀ h, ‖Bh h‖ ≤ C
  tendsto : ∀ z, Tendsto (fun h => F.incl h (Bh h (F.proj h z))) F.l (𝓝 (B z))

/-- The perturbed discretization of `A + B`, with the generators `Lₕ + Bₕ`. [Pazy1983], §3.3 -/
abbrev perturb (P : F.Perturbation) : DissipFEEC.{u} ((P.B : E →ₗ[𝕜] E) +ᵥ A) κ where
  isMDissipative := F.isMDissipative.vadd P.B P.isDissipative
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X := F.X
  L h := F.L h + P.Bh h
  dissipative := P.dissipative
  incl := F.incl
  proj := F.proj
  proj_incl := F.proj_incl
  bound := F.bound

variable {F}

namespace Perturbation

variable (P : F.Perturbation)

theorem tendsto_incl_discreteRes
    (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) (z : E) :
    Tendsto (fun h => (F.perturb P).incl h ((F.perturb P).discreteRes h ((F.perturb P).proj h z)))
      F.l (𝓝 (Operator.resolvent ((P.B : E →ₗ[𝕜] E) +ᵥ A) 1 z)) := by
  have hR' := (F.perturb P).isMDissipative.isResolvent_one
  set u := Operator.resolvent ((P.B : E →ₗ[𝕜] E) +ᵥ A) 1 z
  have huA : u ∈ A.domain := hR'.mem_domain z
  have hu : u - (P.B u + A ⟨u, huA⟩) = z := by simpa using hR'.sub_apply z
  set g := z + P.B u
  have hRg : Operator.resolvent A 1 g = u := by
    have e : u - A ⟨u, huA⟩ = g := by simp only [g]; rw [← hu]; abel
    simpa [e] using resolvent_one_apply_sub F.isMDissipative ⟨u, huA⟩
  set w := fun h => F.discreteRes h (F.proj h g)
  set C := F.boundConst
  have hC := F.boundConst_nonneg
  obtain ⟨CB, hCB⟩ := P.bound
  -- the error splits as `ιₕ (uₕ - wₕ) + (ιₕ wₕ - u)`, with `uₕ - wₕ = Rₕ' (Bₕ wₕ - πₕ B u)`
  have hd : ∀ h, (F.perturb P).discreteRes h (F.proj h z) - w h =
      (F.perturb P).discreteRes h (P.Bh h (w h) - F.proj h (P.B u)) := fun h => by
    set r := (F.perturb P).discreteRes h (F.proj h z)
    have h1 : r - (F.L h r + P.Bh h r) = F.proj h z := (F.perturb P).discreteRes_sub h (F.proj h z)
    have h2 : w h - F.L h (w h) = F.proj h z + F.proj h (P.B u) := by
      rw [← _root_.map_add]; exact F.discreteRes_sub h (F.proj h g)
    have e1 : r - w h - (F.perturb P).L h (r - w h) =
        (r - (F.L h r + P.Bh h r)) - (w h - F.L h (w h)) + P.Bh h (w h) := by
      change r - w h - (F.L h (r - w h) + P.Bh h (r - w h)) = _
      rw [_root_.map_sub, _root_.map_sub]; abel
    have e : r - w h - (F.perturb P).L h (r - w h) = P.Bh h (w h) - F.proj h (P.B u) := by
      rw [e1, h1, h2]; abel
    rw [← e]
    exact (boundedRes_apply_sub ((F.perturb P).dissipative h) _).symm
  have hw : Tendsto (fun h => F.incl h (w h)) F.l (𝓝 u) := hRg ▸ hres g
  have ha : Tendsto (fun h => ‖F.incl h (w h) - F.incl h (F.proj h u)‖) F.l (𝓝 0) := by
    simpa using ((hw.sub (happ u)).norm)
  have hb : Tendsto (fun h => ‖F.incl h (P.Bh h (F.proj h u)) - F.incl h (F.proj h (P.B u))‖)
      F.l (𝓝 0) := by
    simpa using ((P.tendsto u).sub (happ (P.B u))).norm
  have hc : Tendsto (fun h => ‖F.incl h (w h) - u‖) F.l (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hw)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_)
    (by simpa using ((ha.const_mul (CB * C)).add (hb.const_mul C)).const_mul C |>.add hc)
  have hCB0 : 0 ≤ CB := (norm_nonneg _).trans (hCB h)
  have e : (F.perturb P).incl h ((F.perturb P).discreteRes h ((F.perturb P).proj h z)) - u =
      F.incl h ((F.perturb P).discreteRes h (F.proj h z) - w h) + (F.incl h (w h) - u) := by
    simp only [_root_.map_sub]; abel
  rw [e, hd]
  refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
  refine (F.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
    (((F.perturb P).norm_discreteRes_apply_le h _).trans ?_) hC)
  have e2 : P.Bh h (w h) - F.proj h (P.B u) =
      P.Bh h (w h - F.proj h u) + (P.Bh h (F.proj h u) - F.proj h (P.B u)) := by
    rw [_root_.map_sub]; abel
  rw [e2]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine ((P.Bh h).le_opNorm _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul (hCB h) ?_ (norm_nonneg _) hCB0
    simpa [_root_.map_sub] using F.norm_le_norm_incl h (w h - F.proj h u)
  · simpa [_root_.map_sub] using F.norm_le_norm_incl h (P.Bh h (F.proj h u) - F.proj h (P.B u))

open ContinuousLinearMap in
/-- The Galerkin perturbation `Bₕ = ιₕ* B ιₕ` of a bounded dissipative `B`. -/
def galerkin (B : E →L[𝕜] E) (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0)
    (hι : ∀ h v, ‖F.incl h v‖ = ‖v‖)
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) : F.Perturbation where
  B := B
  isDissipative := F.isMDissipative.dissipative.vadd hB
  Bh h := ContinuousLinearMap.adjoint (F.incl h) ∘L B ∘L F.incl h
  dissipative h x := by
    rw [_root_.add_apply, inner_add_left, map_add]
    refine add_nonpos (F.dissipative h x) ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    exact hB _
  bound := ⟨‖B‖, fun h => by
    have h1 : ‖F.incl h‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hι, one_mul]
    have h2 : ‖ContinuousLinearMap.adjoint (F.incl h)‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact h1
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_mul h2 (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      zero_le_one).trans ?_
    rw [one_mul]
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg B)).trans_eq (mul_one _)⟩
  tendsto z := by
    -- `ιₕ ιₕ* yₕ → y` for `yₕ = B ιₕ πₕ z → y = B z`
    have hy : Tendsto (fun h => B (F.incl h (F.proj h z))) F.l (𝓝 (B z)) :=
      (B.continuous.tendsto z).comp (happ z)
    have h0 : Tendsto (fun h => ‖B (F.incl h (F.proj h z)) - B z‖ +
        ‖B z - F.incl h (F.proj h (B z))‖) F.l (𝓝 0) := by
      have h1 := tendsto_iff_norm_sub_tendsto_zero.1 hy
      have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (happ (B z))
      simpa [norm_sub_rev (B z)] using h1.add h2
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) h0
    set ι := F.incl h
    set y := B (ι (F.proj h z))
    change ‖ι (adjoint ι y) - B z‖ ≤ ‖y - B z‖ + ‖B z - ι (F.proj h (B z))‖
    have e : ι (adjoint ι y) - B z = ι (adjoint ι (y - B z)) - (B z - ι (adjoint ι (B z))) := by
      simp only [_root_.map_sub]; abel
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (norm_apply_adjoint_apply_le (hι h) _)
      (norm_sub_apply_adjoint_apply_le (hι h) _ _))

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The perturbed core: the Trotter–Kato core of the perturbed discretization. -/
def core (Z : F.Core) (hZ : Z.Data.topologicalClosure = ⊤) : (F.perturb P).Core :=
  Core.ofResolvent (F.perturb P)
    (P.tendsto_incl_discreteRes (F.tendsto_incl_discreteRes Z hZ)
      fun _ => tendsto_incl_proj F Z (hZ ▸ Submodule.mem_top))
    fun _ => tendsto_incl_proj F Z (hZ ▸ Submodule.mem_top)

/-- The conclusions of the perturbed FEEC theorem for a core `Z` of the perturbed discretization. -/
structure Verdict (Z : (F.perturb P).Core) : Prop where
  /-- the exact flow of `A + B` is the Dyson–Phillips perturbation of that of `A` -/
  eq_perturb : ∀ t, 0 ≤ t → (F.perturb P).S t = (F.isMDissipative.semigroup.perturb P.B).S t
  /-- the core is dense -/
  dense : Z.Data.topologicalClosure = ⊤
  /-- the dissipative FEEC theorem for `A + B` -/
  semidiscrete : (F.perturb P).Verdict Z
  /-- the fully discrete FEEC theorem for `A + B`, for every time scheme -/
  full (Θ : (F.perturb P).TimeScheme) : Θ.Verdict Z
  /-- the fully discrete FEEC theorem on Banach spaces for `A + B` -/
  banach : (F.perturb P).toBanachFEEC.Verdict

end Perturbation

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **The perturbed FEEC theorem**: for a dense core of `F` and a perturbation `P`, `Lₕ + Bₕ` has
the perturbed verdict on the perturbed core. [Pazy1983], §3.1, §3.3, §3.4 -/
theorem _root_.Feec.HilbertComplex.perturbFEEC (Z : F.Core) (hZ : Z.Data.topologicalClosure = ⊤)
    (P : F.Perturbation) :
    P.Verdict (P.core Z hZ) where
  eq_perturb t ht := by
    refine C0Semigroup.eqOn_perturb _ P.B (G' := (F.perturb P).isMDissipative.semigroup) ?_ ht
    rw [LinearPMap.IsMDissipative.generator_semigroup,
      LinearPMap.IsMDissipative.generator_semigroup]
  dense := resData_closure (F.perturb P).isMDissipative
  semidiscrete := dissipFEEC (F.perturb P) (P.core Z hZ)
  full Θ := dissipFEEC_fullyDiscrete (P.core Z hZ) Θ
  banach := TimeStepping.banachFEEC _

end DissipFEEC

end Perturbation

/-! ### Perturbed conforming windows -/

section Conforming

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  {κ : Type*}

namespace ConstrainedFEEC

variable (G : ConstrainedFEEC H κ) (B : PiLp 2 W →L[𝕜] PiLp 2 W)
  (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0)

theorem toCore_closure_eq_top : G.toCore.Data.topologicalClosure = ⊤ :=
  Submodule.eq_top_iff'.2 G.mem_toCore_closure

/-- The perturbed wave discretization `Lₕ + Pₕ B ιₕ` of `ξ' = (L + B) ξ`. -/
def wavePerturbation : G.toApprox.Perturbation :=
  DissipFEEC.Perturbation.galerkin B hB (fun _ _ => rfl)
    fun _ => DissipFEEC.tendsto_incl_proj _ G.toCore (G.mem_toCore_closure _)

/-- The perturbed heat discretization `-Δₕ + Pₕ B ιₕ` of `u' = (-Δ + B) u`. -/
def heatPerturbation (hcr : ∀ i, H.ClosedRangeAt i) (hb : ∀ i, G.IsGraphBounded i) :
    G.toHeat.Perturbation :=
  DissipFEEC.Perturbation.galerkin B hB (fun _ _ => rfl)
    fun _ => DissipFEEC.tendsto_incl_proj _ (G.heatCore hcr hb)
      (G.dense_heatCore_data hcr hb ▸ Submodule.mem_top)

/-- The perturbed verdicts of the wave and heat discretizations of `L + B` and `-Δ + B`. -/
structure PerturbedVerdict : Prop where
  /-- the damped wave equation `ξ' = (L + B) ξ` -/
  wave : (G.wavePerturbation B hB).Verdict
    ((G.wavePerturbation B hB).core G.toCore G.toCore_closure_eq_top)
  /-- the perturbed heat equation `u' = (-Δ + B) u` -/
  heat (hcr : ∀ i, H.ClosedRangeAt i) (hb : ∀ i, G.IsGraphBounded i) :
    (G.heatPerturbation B hB hcr hb).Verdict
      ((G.heatPerturbation B hB hcr hb).core (G.heatCore hcr hb) (G.dense_heatCore_data hcr hb))

end ConstrainedFEEC

/-- **The perturbed FEEC theorem for a constrained FEEC discretization**: for every bounded
dissipative `B`, the perturbed wave and heat discretizations have the perturbed verdict. -/
theorem constrainedFEEC_perturbed (G : ConstrainedFEEC H κ) (B : PiLp 2 W →L[𝕜] PiLp 2 W)
    (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) : G.PerturbedVerdict B hB :=
  ⟨perturbFEEC _ G.toCore_closure_eq_top _,
    fun hcr hb => perturbFEEC _ (G.dense_heatCore_data hcr hb) _⟩

end Conforming

end Feec.HilbertComplex

/-! ### Perturbed impedance problems -/

namespace Feec.ImpedanceTriple.GalerkinData

open Feec.HilbertComplex

variable {V H₁ H₂ Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {T : ImpedanceTriple ℝ V H₁ H₂ Y} {κ : Type*} {G : GalerkinData T κ}
  (K : Submodule ℝ (WithLp 2 (H₁ × H₂))) (hK : IsClosed (K : Set (WithLp 2 (H₁ × H₂))))
  (hG : G.Approximates) (B : WithLp 2 (H₁ × H₂) →L[ℝ] WithLp 2 (H₁ × H₂))
  (hB : ∀ x, RCLike.re ⟪B x, x⟫_ℝ ≤ 0)

/-- The perturbed impedance scheme `Lₕ + Pₕ B ιₕ`. -/
def perturbation : (G.galerkin K hK).Perturbation :=
  DissipFEEC.Perturbation.galerkin B hB G.norm_incl_apply (tendsto_incl_proj hG)

/-- **The perturbed impedance verdict**: a bounded dissipative `B` on approximating Galerkin data
gives the perturbed verdict of `Lₕ + Pₕ B ιₕ`. -/
theorem perturbed_verdict :
    (perturbation K hK hG B hB).Verdict
      ((perturbation K hK hG B hB).core (G.galerkinCore K hK hG) (G.galerkin_verdict K hK hG).1) :=
  perturbFEEC _ _ _

end Feec.ImpedanceTriple.GalerkinData
