module

public import Feec.HilbertComplex.Approximation.ApproxFEEC

/-!
# Non-vacuity of the approximating FEEC theorem: a genuine variational crime

On the complex `𝕜 --id--> 𝕜 → 0` (`Feec.HilbertComplex.ConstrainedFEEC.idComplex`, where
`D(L) = W` and `L = L₀` is bounded), the **perturbed discretization**
`Feec.HilbertComplex.ApproxFEEC.perturbed` has, at level `n` with `hₙ = 1/(n+1)` and
`cₙ = 1 + hₙ`,

* the discrete space `Xₙ = W` with the inner product of `W`, read in `W` through the
  non-isometric `ιₙ = cₙ · id` (an **inner-product crime**: the discrete inner product is
  `cₙ⁻²` times the one pulled back from `W`), `πₙ = cₙ⁻¹ · id`;
* the discrete generator `Lₙ = cₙ L₀` (a **differential crime**: the discrete differential is
  `cₙ 𝐝`, which differs from `𝐝` by the small bounded operator `hₙ 𝐝`).

It is not a subcomplex discretization, and its consistency defect along the exact orbit is
`pₙ' - Lₙ pₙ = (cₙ⁻¹ - 1) e^{tL} L₀ x`, nonzero for `x = (1, 0, 0)` at every level and time
(`ApproxFEEC.perturbed_defect_ne_zero`), of order `hₙ`. The approximating FEEC theorem applies
(`ApproxFEEC.perturbed_verdict`), with a core of all data and an `O(h)` rate class
(`ApproxFEEC.perturbedRate`, `C = 0`, `C' = ‖L₀‖`), and both branches of the constraint residual
occur: `K = W` reduces `L`, and for `K = 𝕜 × 0 × 0` a datum of `K` leaves `K` and the residuals of
every convergent discretization of it have a positive limit
(`ApproxFEEC.perturbed_nonvacuous`).

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (variational crimes: non-isometric `iₕ`, discrete differentials differing from `d`)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

namespace ApproxFEEC

open ConstrainedFEEC ShortHilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜]

instance instFiniteDimensionalPiLpW3 : FiniteDimensional 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)) :=
  inferInstance

variable (𝕜) in
/-- The (bounded) wave operator `L₀` of `𝕜 --id--> 𝕜 → 0`. -/
def idWave : (PiLp 2 (W3 𝕜 𝕜 PUnit)) →L[𝕜] (PiLp 2 (W3 𝕜 𝕜 PUnit)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (idComplex 𝕜).wave ⟨x, mem_idComplex_wave_domain x⟩
      map_add' := fun x y => by
        change (idComplex 𝕜).wave (⟨x, mem_idComplex_wave_domain x⟩ +
          ⟨y, mem_idComplex_wave_domain y⟩) = _
        rw [LinearPMap.map_add]
      map_smul' := fun a x => by
        change (idComplex 𝕜).wave (a • ⟨x, mem_idComplex_wave_domain x⟩) = _
        rw [LinearPMap.map_smul]; rfl }

theorem idWave_apply (x : (PiLp 2 (W3 𝕜 𝕜 PUnit))) :
    idWave 𝕜 x = (idComplex 𝕜).wave ⟨x, mem_idComplex_wave_domain x⟩ := rfl

theorem idWave_skew (x y : (PiLp 2 (W3 𝕜 𝕜 PUnit))) : ⟪idWave 𝕜 x, y⟫_𝕜 = -⟪x, idWave 𝕜 y⟫_𝕜 :=
  (idComplex 𝕜).isSkewAdjoint_wave.isSkewSymmetric ⟨x, mem_idComplex_wave_domain x⟩
    ⟨y, mem_idComplex_wave_domain y⟩

/-- `L₀ (1, 0, 0) ≠ 0`: its component of degree `1` is `1`. -/
theorem idWave_firstDatum_ne_zero : idWave 𝕜 (firstDatum 𝕜) ≠ 0 := by
  intro h0
  have e := (idShort 𝕜).wave_apply_one ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩
  have e2 : (idShort 𝕜).d₁† ⟨(firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 2,
      (mem_idComplex_wave_domain (firstDatum 𝕜)).2 2 1⟩ = 0 :=
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero rfl _
  rw [e2, sub_zero] at e
  have e1 : (idShort 𝕜).d₀ ⟨(firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 0,
      (mem_idComplex_wave_domain (firstDatum 𝕜)).1 0 1⟩ = (1 : 𝕜) := rfl
  rw [e1] at e
  have h1 : ((idWave 𝕜 (firstDatum 𝕜) : PiLp 2 (W3 𝕜 𝕜 PUnit)) 1 : 𝕜) = (0 : 𝕜) := by
    rw [h0]; rfl
  have : (1 : 𝕜) = 0 := e.symm.trans h1
  exact one_ne_zero this

/-- The mesh `hₙ = 1/(n+1)`. -/
def perturbMesh (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem perturbMesh_pos (n : ℕ) : 0 < perturbMesh n := by unfold perturbMesh; positivity

theorem perturbMesh_le_one (n : ℕ) : perturbMesh n ≤ 1 := by
  unfold perturbMesh
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The scale `cₙ = 1 + hₙ`. -/
def perturbScale (n : ℕ) : ℝ := 1 + perturbMesh n

theorem one_lt_perturbScale (n : ℕ) : 1 < perturbScale n := by
  unfold perturbScale; linarith [perturbMesh_pos n]

theorem perturbScale_pos (n : ℕ) : 0 < perturbScale n := by linarith [one_lt_perturbScale n]

theorem perturbScale_ne_zero (n : ℕ) : (perturbScale n : 𝕜) ≠ 0 :=
  RCLike.ofReal_ne_zero.2 (perturbScale_pos n).ne'

variable (𝕜) in
/-- **A genuinely non-conforming approximating FEEC discretization** of `𝕜 --id--> 𝕜 → 0`:
`Xₙ = W`, `ιₙ = cₙ · id` (not isometric), `πₙ = cₙ⁻¹ · id`, `Lₙ = cₙ L₀` (`cₙ = 1 + hₙ`). -/
abbrev perturbed (K : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))) (hK : IsClosed (K : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) :
    ApproxFEEC (idComplex 𝕜) ℕ where
  K := K
  isClosed_K := hK
  l := atTop
  X _ := (PiLp 2 (W3 𝕜 𝕜 PUnit))
  L n := (perturbScale n : 𝕜) • idWave 𝕜
  skew n x y := by
    simp only [_root_.smul_apply, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
      idWave_skew, mul_neg]
  incl n := (perturbScale n : 𝕜) • ContinuousLinearMap.id 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))
  proj n := ((perturbScale n : 𝕜))⁻¹ • ContinuousLinearMap.id 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))
  proj_incl n x := by
    rw [_root_.smul_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.id_apply, smul_smul, inv_mul_cancel₀ (perturbScale_ne_zero (𝕜 := 𝕜) n),
      one_smul]
  bound := ⟨2, fun n => by
    have h1 := one_lt_perturbScale n
    have h2 : perturbScale n ≤ 2 := by unfold perturbScale; linarith [perturbMesh_le_one n]
    have hi : (perturbScale n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1.le
    have hc := perturbScale_pos n
    constructor
    · refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
      rw [_root_.smul_apply, ContinuousLinearMap.id_apply, norm_smul, RCLike.norm_ofReal,
        abs_of_pos hc]
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    · refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
      rw [_root_.smul_apply, ContinuousLinearMap.id_apply, norm_smul, norm_inv,
        RCLike.norm_ofReal, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)⟩

variable (Q : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))) (hQ : IsClosed (Q : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))))

theorem perturbed_incl_apply (n : ℕ) (x : (PiLp 2 (W3 𝕜 𝕜 PUnit))) :
    (perturbed 𝕜 Q hQ).incl n x = (perturbScale n : 𝕜) • x := rfl

/-- The comparison `pₙ(t) = cₙ⁻¹ e^{tL} x`, read exactly: `ιₙ pₙ(t) = e^{tL} x`. -/
def perturbedComparison (T : ℝ) : (perturbed 𝕜 Q hQ).Comparison T where
  Data := univ
  p x n t := ((perturbScale n : 𝕜))⁻¹ • (idComplex 𝕜).waveGroup.S t x
  p' x n t := ((perturbScale n : 𝕜))⁻¹ • (idComplex 𝕜).waveGroup.S t (idWave 𝕜 x)
  continuousOn x _ n := (continuousOn_const (c := ((perturbScale n : 𝕜))⁻¹)).smul
    ((idComplex 𝕜).waveGroup.strongCont x).continuousOn
  continuousOn' x _ n := (continuousOn_const (c := ((perturbScale n : 𝕜))⁻¹)).smul
    ((idComplex 𝕜).waveGroup.strongCont (idWave 𝕜 x)).continuousOn
  hasDerivWithinAt x _ n t _ :=
    ((hasDerivAt_waveGroup (idComplex 𝕜) (mem_idComplex_wave_domain x) t).const_smul
      ((perturbScale n : 𝕜))⁻¹).hasDerivWithinAt

/-- The consistency defect is `(cₙ⁻¹ - 1) e^{tL} L₀ x`. -/
theorem perturbedComparison_defect (T : ℝ) (x : (PiLp 2 (W3 𝕜 𝕜 PUnit))) (n : ℕ) (t : ℝ) :
    (perturbedComparison Q hQ T).defect x n t =
      (((perturbScale n : 𝕜))⁻¹ - 1) • (idComplex 𝕜).waveGroup.S t (idWave 𝕜 x) := by
  change ((perturbScale n : 𝕜))⁻¹ • (idComplex 𝕜).waveGroup.S t (idWave 𝕜 x) -
    ((perturbScale n : 𝕜) • idWave 𝕜) (((perturbScale n : 𝕜))⁻¹ •
      (idComplex 𝕜).waveGroup.S t x) = _
  have e : idWave 𝕜 ((idComplex 𝕜).waveGroup.S t x) =
      (idComplex 𝕜).waveGroup.S t (idWave 𝕜 x) :=
    wave_waveGroup (mem_idComplex_wave_domain x) t
  rw [_root_.smul_apply, _root_.map_smul, e, smul_smul, mul_inv_cancel₀ (perturbScale_ne_zero (𝕜 := 𝕜) n),
    one_smul, sub_smul, one_smul]

theorem norm_perturbScale_inv_sub_one (n : ℕ) :
    ‖((perturbScale n : 𝕜))⁻¹ - 1‖ = perturbMesh n / perturbScale n := by
  have hc := perturbScale_pos n
  have e : ((perturbScale n : 𝕜))⁻¹ - 1 = (((perturbScale n)⁻¹ - 1 : ℝ) : 𝕜) := by
    push_cast; rfl
  have hi : (perturbScale n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_lt_perturbScale n).le
  rw [e, RCLike.norm_ofReal, abs_of_nonpos (by linarith)]
  have : perturbMesh n = perturbScale n - 1 := by unfold perturbScale; ring
  rw [this]
  field_simp
  ring

theorem norm_perturbedComparison_defect (T : ℝ) (x : (PiLp 2 (W3 𝕜 𝕜 PUnit))) (n : ℕ) (t : ℝ) :
    ‖(perturbedComparison Q hQ T).defect x n t‖ =
      perturbMesh n / perturbScale n * ‖idWave 𝕜 x‖ := by
  rw [perturbedComparison_defect, norm_smul, (idComplex 𝕜).isIsometric_waveGroup t,
    norm_perturbScale_inv_sub_one]

/-- The core of the perturbed discretization: all data. -/
def perturbedCore : (perturbed 𝕜 Q hQ).Core where
  Data := ⊤
  cmp T := perturbedComparison Q hQ T
  data_eq _ := Submodule.top_coe.symm
  tendsto_approx T x _ := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun n t _ => ?_
    change dist _ ((perturbScale n : 𝕜) • (((perturbScale n : 𝕜))⁻¹ •
      (idComplex 𝕜).waveGroup.S t x)) < ε
    rw [smul_smul, mul_inv_cancel₀ (perturbScale_ne_zero (𝕜 := 𝕜) n), one_smul, dist_self]
    exact hε
  tendsto_defect T x _ := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n => perturbMesh n * (‖idWave 𝕜 x‖ + 1)) atTop (𝓝 0) := by
      have : Tendsto perturbMesh atTop (𝓝 0) := by
        unfold perturbMesh
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this.mul_const (‖idWave 𝕜 x‖ + 1)
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn t _
    rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _),
      norm_perturbedComparison_defect]
    have hc := one_lt_perturbScale n
    have hm := perturbMesh_pos n
    have h1 : perturbMesh n / perturbScale n ≤ perturbMesh n :=
      div_le_self hm.le hc.le
    calc perturbMesh n / perturbScale n * ‖idWave 𝕜 x‖ ≤ perturbMesh n * ‖idWave 𝕜 x‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ perturbMesh n * (‖idWave 𝕜 x‖ + 1) := by nlinarith
      _ < ε := hn

theorem perturbedCore_data : (perturbedCore Q hQ).Data = ⊤ := rfl

/-- An `O(h)` rate class with all data: `C = 0` (exact approximation), `C' = ‖L₀‖`. -/
def perturbedRate (T : ℝ) : (perturbed 𝕜 Q hQ).RateClass T where
  toComparison := perturbedComparison Q hQ T
  classNorm := norm
  meshSize := perturbMesh
  α := 1
  C := 0
  C' := ‖idWave 𝕜‖
  approx x _ n t _ := by
    change ‖_ - (perturbScale n : 𝕜) • (((perturbScale n : 𝕜))⁻¹ •
      (idComplex 𝕜).waveGroup.S t x)‖ ≤ _
    rw [smul_smul, mul_inv_cancel₀ (perturbScale_ne_zero (𝕜 := 𝕜) n), one_smul, sub_self, norm_zero]
    simp
  consistency x _ n t _ := by
    rw [norm_perturbedComparison_defect, Real.rpow_one]
    have hc := one_lt_perturbScale n
    have hm := perturbMesh_pos n
    have h1 : perturbMesh n / perturbScale n ≤ perturbMesh n := div_le_self hm.le hc.le
    calc perturbMesh n / perturbScale n * ‖idWave 𝕜 x‖ ≤ perturbMesh n * (‖idWave 𝕜‖ * ‖x‖) :=
          mul_le_mul h1 ((idWave 𝕜).le_opNorm x) (norm_nonneg _) hm.le
      _ = _ := by ring

/-- **The approximating FEEC theorem applies to the perturbed discretization.** -/
theorem perturbed_verdict : (perturbed 𝕜 Q hQ).Verdict (perturbedCore Q hQ) := approxFEEC _ _

/-- **The consistency defect is genuinely nonzero**: along `(1, 0, 0)`, at every level and time. -/
theorem perturbed_defect_ne_zero (T : ℝ) (n : ℕ) (t : ℝ) :
    (perturbedComparison Q hQ T).defect (firstDatum 𝕜) n t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_perturbedComparison_defect]
  exact mul_ne_zero (div_ne_zero (perturbMesh_pos n).ne' (perturbScale_pos n).ne')
    (norm_ne_zero_iff.2 idWave_firstDatum_ne_zero)

/-- **Non-vacuity of the approximating FEEC theorem under genuine variational crimes.** At every
level the reading map is not isometric, the discrete generator differs from `L₀`, and the
consistency defect along `(1, 0, 0)` is nonzero at every time; the core is all of `W` and the rate
class contains all data with `α = 1`; the constraint `K = W` reduces `L`, and for
`K = 𝕜 × 0 × 0` some datum of `K` leaves `K` at some `t ∈ [0, T]` while the residuals
`dist(ιₙ e^{tLₙ} vₙ, K)` of every convergent discretization tend to `dist(e^{tL} x, K) > 0`. -/
theorem perturbed_nonvacuous :
    (∀ n, (∀ x : (PiLp 2 (W3 𝕜 𝕜 PUnit)), x ≠ 0 → ‖(perturbed 𝕜 Q hQ).incl n x‖ ≠ ‖x‖) ∧
      (perturbed 𝕜 Q hQ).L n ≠ idWave 𝕜 ∧
      ∀ T, ∀ t, (perturbedComparison Q hQ T).defect (firstDatum 𝕜) n t ≠ 0) ∧
    (perturbedCore Q hQ).Data = ⊤ ∧
    (∀ T, (perturbedRate Q hQ T).Data = univ ∧ (perturbedRate Q hQ T).α = 1 ∧
      (perturbedRate Q hQ T).meshSize = perturbMesh ∧ (perturbedRate Q hQ T).C = 0) ∧
    (idComplex 𝕜).wave.IsReducing (⊤ : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))) ∧
    ¬ (idComplex 𝕜).wave.IsReducing (firstSub 𝕜) ∧
    ∀ T : ℝ, 0 < T → ∃ x ∈ firstSub 𝕜, ∃ t ∈ Icc 0 T,
      (idComplex 𝕜).waveGroup.S t x ∉ firstSub 𝕜 ∧
      0 < infDist ((idComplex 𝕜).waveGroup.S t x) (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))) ∧
      ∀ v : ∀ n, (perturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).X n,
        Tendsto (fun n => (perturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).incl n (v n)) atTop
          (𝓝 x) →
        Tendsto (fun n => infDist ((perturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).sol n (v n) t)
          (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) atTop
          (𝓝 (infDist ((idComplex 𝕜).waveGroup.S t x) (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))))) := by
  refine ⟨fun n => ⟨fun x hx => ?_, fun hL => ?_, fun T t => perturbed_defect_ne_zero Q hQ T n t⟩,
    rfl, fun T => ⟨rfl, rfl, rfl, rfl⟩,
    ?_, not_isReducing_firstSub, fun T hT => ?_⟩
  · rw [perturbed_incl_apply, norm_smul, RCLike.norm_ofReal, abs_of_pos (perturbScale_pos n)]
    intro h
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have : perturbScale n = 1 := by
      have := mul_right_cancel₀ hx' (h.trans (one_mul ‖x‖).symm)
      exact this
    linarith [one_lt_perturbScale n]
  · have h1 := congrArg (fun A : (PiLp 2 (W3 𝕜 𝕜 PUnit)) →L[𝕜] (PiLp 2 (W3 𝕜 𝕜 PUnit)) => A (firstDatum 𝕜)) hL
    simp only [_root_.smul_apply] at h1
    have h2 : ((perturbScale n : 𝕜) - 1) • idWave 𝕜 (firstDatum 𝕜) = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · have : (perturbScale n : 𝕜) = ((1 : ℝ) : 𝕜) := by rw [RCLike.ofReal_one]; exact sub_eq_zero.1 h3
      have := RCLike.ofReal_injective this
      linarith [one_lt_perturbScale n]
    · exact idWave_firstDatum_ne_zero h3
  · exact isReducingPair_top _
  · obtain ⟨x, hxK, t, ht, hout, hpos, -⟩ :=
      constrainedFEEC_residual_not_isReducing_of_grading (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub)
        (p := fun i : Fin 3 => decide (Odd i.val)) fin3_parity
        (fun x hx => reversal_mem_totalSub hx)
        (fun k hk => subset_closure ⟨mem_idComplex_wave_domain k, hk⟩) not_isReducing_firstSub hT
    refine ⟨x, hxK, t, ht, hout, hpos, fun v hv => ?_⟩
    have hxc : (x : (PiLp 2 (W3 𝕜 𝕜 PUnit))) ∈ (perturbedCore (firstSub 𝕜) isClosed_totalSub).Data.topologicalClosure :=
      Submodule.le_topologicalClosure _ Submodule.mem_top
    exact (approxFEEC_residual_not_mem _ _ isClosed_totalSub ⟨0, (firstSub 𝕜).zero_mem⟩ hxc hv
      ht.1 hout).2

end ApproxFEEC

end Feec.HilbertComplex
