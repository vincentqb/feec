module

public import Feec.HilbertComplex.Approximation.ApproxConforming

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
(`ApproxFEEC.perturbed_nonvacuous`). The scheme is inexact: its solution from `πₙ (1, 0, 0)` differs
from the exact one at some time (`ApproxFEEC.perturbed_exists_sol_ne`, via the inexactness
criterion `ApproxFEEC.exists_sol_ne`).

Since `perturbed` is a scalar time rescaling, a second witness has a **non-scalar** reading map:
`ApproxFEEC.projPerturbed` has `Xₙ = W`, `Lₙ = L₀` and `ιₙ = 1 + hₙ P`, `πₙ = 1 - bₙ P = ιₙ⁻¹`
(`P` the orthogonal projection onto `𝕜 × 0 × 0`, `bₙ = hₙ / (1 + hₙ)`), so the pulled-back inner
product `⟪ιₙ ·, ιₙ ·⟫` differs from that of `Xₙ` and `ιₙ` does not commute with `L₀`. Its
consistency defect along `pₙ(t) = πₙ e^{tL} x` is the commutator `bₙ [L₀, P] e^{tL} x`, nonzero at
every level and time along `e^{-tL} (1, 0, 0)`; `ιₙ` is neither a scalar multiple of the identity
nor isometric, the scheme is inexact, the rate class is `O(h)` with `C' = 2 ‖L₀‖`, and the graded
non-reducing branch of the residual occurs with its eventual lower bound
(`ApproxFEEC.projPerturbed_nonvacuous`). Finally `ApproxFEEC.idFEEC_approxFEEC_verdict` and
`ApproxFEEC.idFEEC_constrainedFEEC_of_approxFEEC` instantiate the conforming bridge
`ConstrainedFEEC.toApprox` / `ConstrainedFEEC.toCore`.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (variational crimes: non-isometric `iₕ`, discrete differentials differing from `d`)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

namespace ApproxFEEC

open ConstrainedFEEC ShortHilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜]

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

/-- `L₀ (1, 0, 0)` has component `1` in degree `1`. -/
theorem idWave_firstDatum_one :
    ((idWave 𝕜 (firstDatum 𝕜) : PiLp 2 (W3 𝕜 𝕜 PUnit)) 1 : 𝕜) = (1 : 𝕜) := by
  have e := (idShort 𝕜).wave_apply_one ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩
  have e2 : (idShort 𝕜).d₁† ⟨(firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 2,
      (mem_idComplex_wave_domain (firstDatum 𝕜)).2 2 1⟩ = 0 :=
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero rfl _
  rw [e2, sub_zero] at e
  exact e

/-- `L₀ (1, 0, 0) ≠ 0`. -/
theorem idWave_firstDatum_ne_zero : idWave 𝕜 (firstDatum 𝕜) ≠ 0 := by
  intro h0
  have h1 : ((idWave 𝕜 (firstDatum 𝕜) : PiLp 2 (W3 𝕜 𝕜 PUnit)) 1 : 𝕜) = (0 : 𝕜) := by
    rw [h0]; rfl
  have h2 : (1 : 𝕜) = 0 := (idWave_firstDatum_one (𝕜 := 𝕜)).symm.trans h1
  exact one_ne_zero h2

/-- `L₀ (1, 0, 0) ∉ 𝕜 × 0 × 0`. -/
theorem idWave_firstDatum_not_mem : idWave 𝕜 (firstDatum 𝕜) ∉ firstSub 𝕜 := by
  intro hm
  have h1 : ((idWave 𝕜 (firstDatum 𝕜) : PiLp 2 (W3 𝕜 𝕜 PUnit)) 1 : 𝕜) = (0 : 𝕜) :=
    (Submodule.mem_bot (M := 𝕜) 𝕜).1 (mem_totalSub_family3.1 hm).2.1
  have h2 : (1 : 𝕜) = 0 := (idWave_firstDatum_one (𝕜 := 𝕜)).symm.trans h1
  exact one_ne_zero h2

theorem firstDatum_ne_zero : firstDatum 𝕜 ≠ 0 := by
  intro h0
  have h1 : ((firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 0 : 𝕜) = (0 : 𝕜) := by rw [h0]; rfl
  have h2 : ((firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 0 : 𝕜) = (1 : 𝕜) := rfl
  have h3 : (1 : 𝕜) = 0 := h2.symm.trans h1
  exact one_ne_zero h3

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
abbrev perturbed (K : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)))
    (hK : IsClosed (K : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) :
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
  rw [_root_.smul_apply, _root_.map_smul, e, smul_smul,
    mul_inv_cancel₀ (perturbScale_ne_zero (𝕜 := 𝕜) n),
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

/-- **The perturbed scheme is inexact**: at every level, the discrete solution from `πₙ (1, 0, 0)`
differs from the exact one at some time (`ιₙ Lₙ πₙ x = cₙ L₀ x ≠ L₀ x`). -/
theorem perturbed_exists_sol_ne (n : ℕ) :
    ∃ t, (perturbed 𝕜 Q hQ).sol n ((perturbed 𝕜 Q hQ).proj n (firstDatum 𝕜)) t ≠
      (idComplex 𝕜).waveGroup.S t (firstDatum 𝕜) := by
  refine (perturbed 𝕜 Q hQ).exists_sol_ne (mem_idComplex_wave_domain _) n _ fun he => ?_
  have e : (perturbed 𝕜 Q hQ).incl n ((perturbed 𝕜 Q hQ).L n
      ((perturbed 𝕜 Q hQ).proj n (firstDatum 𝕜))) =
      (perturbScale n : 𝕜) • idWave 𝕜 (firstDatum 𝕜) := by
    change (perturbScale n : 𝕜) • ((perturbScale n : 𝕜) • idWave 𝕜
      (((perturbScale n : 𝕜))⁻¹ • firstDatum 𝕜)) = _
    rw [(idWave 𝕜).map_smul, smul_smul, smul_smul, mul_assoc,
      mul_inv_cancel₀ (perturbScale_ne_zero (𝕜 := 𝕜) n), mul_one]
  rw [e] at he
  have h2 : ((perturbScale n : 𝕜) - 1) • idWave 𝕜 (firstDatum 𝕜) = 0 := by
    rw [sub_smul, one_smul]; exact sub_eq_zero.2 he
  rcases smul_eq_zero.1 h2 with h3 | h3
  · have : (perturbScale n : 𝕜) = ((1 : ℝ) : 𝕜) := by
      rw [RCLike.ofReal_one]; exact sub_eq_zero.1 h3
    linarith [one_lt_perturbScale n, RCLike.ofReal_injective this]
  · exact idWave_firstDatum_ne_zero h3

/-- **Non-vacuity of the approximating FEEC theorem under genuine variational crimes.** At every
level the reading map is not isometric, the discrete generator differs from `L₀`, and the
consistency defect along `(1, 0, 0)` is nonzero at every time, and the scheme is inexact (its
solution from `πₙ (1, 0, 0)` differs from the exact one at some time); the core is all of `W` and
the rate
class contains all data with `α = 1`; the constraint `K = W` reduces `L`, and for
`K = 𝕜 × 0 × 0` some datum of `K` leaves `K` at some `t ∈ [0, T]`, `ιₙ πₙ x → x`, and the residuals
`dist(ιₙ e^{tLₙ} vₙ, K)` of every convergent discretization tend to `dist(e^{tL} x, K) > 0`. -/
theorem perturbed_nonvacuous :
    (∀ n, (∀ x : (PiLp 2 (W3 𝕜 𝕜 PUnit)), x ≠ 0 → ‖(perturbed 𝕜 Q hQ).incl n x‖ ≠ ‖x‖) ∧
      (perturbed 𝕜 Q hQ).L n ≠ idWave 𝕜 ∧
      (∃ t, (perturbed 𝕜 Q hQ).sol n ((perturbed 𝕜 Q hQ).proj n (firstDatum 𝕜)) t ≠
        (idComplex 𝕜).waveGroup.S t (firstDatum 𝕜)) ∧
      ∀ T, ∀ t, (perturbedComparison Q hQ T).defect (firstDatum 𝕜) n t ≠ 0) ∧
    (perturbedCore Q hQ).Data = ⊤ ∧
    (∀ T, (perturbedRate Q hQ T).Data = univ ∧ (perturbedRate Q hQ T).α = 1 ∧
      (perturbedRate Q hQ T).meshSize = perturbMesh ∧ (perturbedRate Q hQ T).C = 0) ∧
    (idComplex 𝕜).wave.IsReducing (⊤ : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))) ∧
    ¬ (idComplex 𝕜).wave.IsReducing (firstSub 𝕜) ∧
    ∀ T : ℝ, 0 < T → ∃ x ∈ firstSub 𝕜, ∃ t ∈ Icc 0 T,
      (idComplex 𝕜).waveGroup.S t x ∉ firstSub 𝕜 ∧
      0 < infDist ((idComplex 𝕜).waveGroup.S t x) (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))) ∧
      Tendsto (fun n => (perturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).incl n
        ((perturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).proj n x)) atTop (𝓝 x) ∧
      ∀ v : ∀ n, (perturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).X n,
        Tendsto (fun n => (perturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).incl n (v n)) atTop
          (𝓝 x) →
        Tendsto (fun n => infDist ((perturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).sol n (v n) t)
          (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) atTop
          (𝓝 (infDist ((idComplex 𝕜).waveGroup.S t x)
            (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))))) := by
  refine ⟨fun n => ⟨fun x hx => ?_, fun hL => ?_, perturbed_exists_sol_ne Q hQ n,
      fun T t => perturbed_defect_ne_zero Q hQ T n t⟩,
    rfl, fun T => ⟨rfl, rfl, rfl, rfl⟩,
    ?_, not_isReducing_firstSub, fun T hT => ?_⟩
  · rw [perturbed_incl_apply, norm_smul, RCLike.norm_ofReal, abs_of_pos (perturbScale_pos n)]
    intro h
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have : perturbScale n = 1 := by
      have := mul_right_cancel₀ hx' (h.trans (one_mul ‖x‖).symm)
      exact this
    linarith [one_lt_perturbScale n]
  · have h1 := congrArg (fun A : (PiLp 2 (W3 𝕜 𝕜 PUnit)) →L[𝕜] (PiLp 2 (W3 𝕜 𝕜 PUnit)) =>
      A (firstDatum 𝕜)) hL
    simp only [_root_.smul_apply] at h1
    have h2 : ((perturbScale n : 𝕜) - 1) • idWave 𝕜 (firstDatum 𝕜) = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · have : (perturbScale n : 𝕜) = ((1 : ℝ) : 𝕜) := by
        rw [RCLike.ofReal_one]; exact sub_eq_zero.1 h3
      have := RCLike.ofReal_injective this
      linarith [one_lt_perturbScale n]
    · exact idWave_firstDatum_ne_zero h3
  · exact isReducingPair_top _
  · obtain ⟨x, hxK, t, ht, hout, hpos, -⟩ :=
      constrainedFEEC_residual_not_isReducing_of_grading (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub)
        (p := fun i : Fin 3 => decide (Odd i.val)) fin3_parity
        (fun x hx => reversal_mem_totalSub hx)
        (fun k hk => subset_closure ⟨mem_idComplex_wave_domain k, hk⟩) not_isReducing_firstSub hT
    have hxc : (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) ∈
        (perturbedCore (firstSub 𝕜) isClosed_totalSub).Data.topologicalClosure :=
      Submodule.le_topologicalClosure _ Submodule.mem_top
    refine ⟨x, hxK, t, ht, hout, hpos, tendsto_incl_proj _ _ hxc, fun v hv => ?_⟩
    exact (approxFEEC_residual_not_mem _ _ isClosed_totalSub ⟨0, (firstSub 𝕜).zero_mem⟩ hxc hv
      ht.1 hout).2

/-! ### A non-scalar reading map: an inner-product crime that does not commute with `L` -/

variable (𝕜) in
/-- The orthogonal projection `P` onto `𝕜 × 0 × 0`. -/
abbrev firstProj : PiLp 2 (W3 𝕜 𝕜 PUnit) →L[𝕜] PiLp 2 (W3 𝕜 𝕜 PUnit) :=
  (firstSub 𝕜).starProjection

theorem firstProj_firstProj (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    firstProj 𝕜 (firstProj 𝕜 x) = firstProj 𝕜 x :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)

theorem firstProj_firstDatum : firstProj 𝕜 (firstDatum 𝕜) = firstDatum 𝕜 :=
  Submodule.starProjection_eq_self_iff.2 firstDatum_mem

/-- `P L₀ (1, 0, 0) ≠ L₀ (1, 0, 0)`: `P` does not commute with `L₀`. -/
theorem firstProj_idWave_firstDatum_ne :
    firstProj 𝕜 (idWave 𝕜 (firstDatum 𝕜)) ≠ idWave 𝕜 (firstDatum 𝕜) := fun h =>
  idWave_firstDatum_not_mem (Submodule.starProjection_eq_self_iff.1 h)

/-- `bₙ = hₙ / (1 + hₙ)`, so that `(1 - bₙ P)(1 + hₙ P) = 1`. -/
def projCoeff (n : ℕ) : ℝ := perturbMesh n / perturbScale n

theorem projCoeff_pos (n : ℕ) : 0 < projCoeff n :=
  div_pos (perturbMesh_pos n) (perturbScale_pos n)

theorem projCoeff_le_mesh (n : ℕ) : projCoeff n ≤ perturbMesh n :=
  div_le_self (perturbMesh_pos n).le (one_lt_perturbScale n).le

theorem projCoeff_identity (n : ℕ) :
    ((perturbMesh n : 𝕜) - projCoeff n - projCoeff n * perturbMesh n) = 0 := by
  have hc := perturbScale_pos n
  have e : perturbMesh n - projCoeff n - projCoeff n * perturbMesh n = 0 := by
    unfold projCoeff
    have : perturbScale n = 1 + perturbMesh n := rfl
    field_simp
    rw [this]; ring
  exact_mod_cast e

theorem one_sub_projCoeff_mul (n : ℕ) :
    (1 - (projCoeff n : 𝕜)) * (perturbMesh n : 𝕜) = projCoeff n := by
  have := projCoeff_identity (𝕜 := 𝕜) n
  linear_combination this

variable (𝕜) in
/-- **An approximating FEEC discretization with a non-scalar reading map** of
`𝕜 --id--> 𝕜 → 0`: `Xₙ = W`, `Lₙ = L₀`, `ιₙ = 1 + hₙ P` (not a multiple of an isometry),
`πₙ = 1 - bₙ P = ιₙ⁻¹`. The pulled-back inner product `⟪ιₙ ·, ιₙ ·⟫` differs from that of `Xₙ`,
and `ιₙ` does not commute with `L₀`. -/
abbrev projPerturbed (K : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)))
    (hK : IsClosed (K : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) : ApproxFEEC (idComplex 𝕜) ℕ where
  K := K
  isClosed_K := hK
  l := atTop
  X _ := PiLp 2 (W3 𝕜 𝕜 PUnit)
  L _ := idWave 𝕜
  skew _ := idWave_skew
  incl n := ContinuousLinearMap.id 𝕜 _ + (perturbMesh n : 𝕜) • firstProj 𝕜
  proj n := ContinuousLinearMap.id 𝕜 _ - (projCoeff n : 𝕜) • firstProj 𝕜
  proj_incl n x := by
    change (x + (perturbMesh n : 𝕜) • firstProj 𝕜 x) -
      (projCoeff n : 𝕜) • firstProj 𝕜 (x + (perturbMesh n : 𝕜) • firstProj 𝕜 x) = x
    rw [(firstProj 𝕜).map_add, (firstProj 𝕜).map_smul, firstProj_firstProj]
    calc _ = x + ((perturbMesh n : 𝕜) - projCoeff n - projCoeff n * perturbMesh n) •
          firstProj 𝕜 x := by module
      _ = x := by rw [projCoeff_identity, zero_smul, add_zero]
  bound := ⟨2, fun n => by
    have hP : ‖firstProj 𝕜‖ ≤ 1 := Submodule.starProjection_norm_le _
    have hI := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := PiLp 2 (W3 𝕜 𝕜 PUnit))
    have hm := perturbMesh_le_one n
    have hm0 := (perturbMesh_pos n).le
    have hb := projCoeff_le_mesh n
    have hb0 := (projCoeff_pos n).le
    have hP0 := norm_nonneg (firstProj 𝕜)
    constructor
    · refine (norm_add_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hm0]
      nlinarith
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hb0]
      nlinarith⟩

theorem projPerturbed_incl_apply (n : ℕ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (projPerturbed 𝕜 Q hQ).incl n x = x + (perturbMesh n : 𝕜) • firstProj 𝕜 x := rfl

theorem projPerturbed_proj_apply (n : ℕ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (projPerturbed 𝕜 Q hQ).proj n x = x - (projCoeff n : 𝕜) • firstProj 𝕜 x := rfl

/-- `ιₙ πₙ = 1` as well. -/
theorem projPerturbed_incl_proj (n : ℕ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (projPerturbed 𝕜 Q hQ).incl n ((projPerturbed 𝕜 Q hQ).proj n x) = x := by
  rw [projPerturbed_incl_apply, projPerturbed_proj_apply, (firstProj 𝕜).map_sub,
    (firstProj 𝕜).map_smul, firstProj_firstProj]
  calc _ = x + ((perturbMesh n : 𝕜) - projCoeff n - projCoeff n * perturbMesh n) •
        firstProj 𝕜 x := by module
    _ = x := by rw [projCoeff_identity, zero_smul, add_zero]

/-- The comparison `pₙ(t) = πₙ e^{tL} x`, read exactly: `ιₙ pₙ(t) = e^{tL} x`. -/
def projComparison (T : ℝ) : (projPerturbed 𝕜 Q hQ).Comparison T where
  Data := univ
  p x n t := (projPerturbed 𝕜 Q hQ).proj n ((idComplex 𝕜).waveGroup.S t x)
  p' x n t := (projPerturbed 𝕜 Q hQ).proj n ((idComplex 𝕜).waveGroup.S t (idWave 𝕜 x))
  continuousOn x _ n := ((projPerturbed 𝕜 Q hQ).proj n).continuous.comp_continuousOn
    ((idComplex 𝕜).waveGroup.strongCont x).continuousOn
  continuousOn' x _ n := ((projPerturbed 𝕜 Q hQ).proj n).continuous.comp_continuousOn
    ((idComplex 𝕜).waveGroup.strongCont (idWave 𝕜 x)).continuousOn
  hasDerivWithinAt x _ n t _ :=
    ((((projPerturbed 𝕜 Q hQ).proj n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_waveGroup (idComplex 𝕜) (mem_idComplex_wave_domain x) t)).hasDerivWithinAt

/-- The consistency defect is the commutator `bₙ (L₀ P - P L₀) e^{tL} x`. -/
theorem projComparison_defect (T : ℝ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) (n : ℕ) (t : ℝ) :
    (projComparison Q hQ T).defect x n t = (projCoeff n : 𝕜) •
      (idWave 𝕜 (firstProj 𝕜 ((idComplex 𝕜).waveGroup.S t x)) -
        firstProj 𝕜 (idWave 𝕜 ((idComplex 𝕜).waveGroup.S t x))) := by
  have e : idWave 𝕜 ((idComplex 𝕜).waveGroup.S t x) =
      (idComplex 𝕜).waveGroup.S t (idWave 𝕜 x) :=
    wave_waveGroup (mem_idComplex_wave_domain x) t
  change (projPerturbed 𝕜 Q hQ).proj n ((idComplex 𝕜).waveGroup.S t (idWave 𝕜 x)) -
    idWave 𝕜 ((projPerturbed 𝕜 Q hQ).proj n ((idComplex 𝕜).waveGroup.S t x)) = _
  rw [← e, projPerturbed_proj_apply, projPerturbed_proj_apply, (idWave 𝕜).map_sub,
    (idWave 𝕜).map_smul]
  module

theorem norm_projComparison_defect_le (T : ℝ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) (n : ℕ) (t : ℝ) :
    ‖(projComparison Q hQ T).defect x n t‖ ≤ perturbMesh n * (2 * ‖idWave 𝕜‖ * ‖x‖) := by
  rw [projComparison_defect, norm_smul, RCLike.norm_ofReal, abs_of_pos (projCoeff_pos n)]
  set y := (idComplex 𝕜).waveGroup.S t x
  have hy : ‖y‖ = ‖x‖ := (idComplex 𝕜).isIsometric_waveGroup t x
  have h1 : ‖idWave 𝕜 (firstProj 𝕜 y)‖ ≤ ‖idWave 𝕜‖ * ‖x‖ :=
    ((idWave 𝕜).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((Submodule.norm_starProjection_apply_le _ y).trans hy.le) (norm_nonneg _))
  have h2 : ‖firstProj 𝕜 (idWave 𝕜 y)‖ ≤ ‖idWave 𝕜‖ * ‖x‖ :=
    (Submodule.norm_starProjection_apply_le _ _).trans (((idWave 𝕜).le_opNorm _).trans_eq
      (by rw [hy]))
  have h3 := norm_sub_le (idWave 𝕜 (firstProj 𝕜 y)) (firstProj 𝕜 (idWave 𝕜 y))
  have hb := projCoeff_le_mesh n
  have hb0 := (projCoeff_pos n).le
  have hL : 0 ≤ ‖idWave 𝕜‖ * ‖x‖ := by positivity
  calc projCoeff n * ‖_‖ ≤ projCoeff n * (2 * (‖idWave 𝕜‖ * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (by linarith) hb0
    _ ≤ perturbMesh n * (2 * (‖idWave 𝕜‖ * ‖x‖)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

/-- The core of `projPerturbed`: all data. -/
def projCore : (projPerturbed 𝕜 Q hQ).Core where
  Data := ⊤
  cmp T := projComparison Q hQ T
  data_eq _ := Submodule.top_coe.symm
  tendsto_approx T x _ := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun n t _ => ?_
    change dist _ ((projPerturbed 𝕜 Q hQ).incl n
      ((projPerturbed 𝕜 Q hQ).proj n ((idComplex 𝕜).waveGroup.S t x))) < ε
    rw [projPerturbed_incl_proj, dist_self]
    exact hε
  tendsto_defect T x _ := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n => perturbMesh n * (2 * ‖idWave 𝕜‖ * ‖x‖ + 1)) atTop (𝓝 0) := by
      have : Tendsto perturbMesh atTop (𝓝 0) := by
        unfold perturbMesh
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this.mul_const (2 * ‖idWave 𝕜‖ * ‖x‖ + 1)
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn t _
    rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _)]
    have hm := perturbMesh_pos n
    calc _ ≤ perturbMesh n * (2 * ‖idWave 𝕜‖ * ‖x‖) := norm_projComparison_defect_le Q hQ T x n t
      _ ≤ perturbMesh n * (2 * ‖idWave 𝕜‖ * ‖x‖ + 1) := by nlinarith
      _ < ε := hn

/-- An `O(h)` rate class with all data: `C = 0` (exact approximation), `C' = 2 ‖L₀‖`. -/
def projRate (T : ℝ) : (projPerturbed 𝕜 Q hQ).RateClass T where
  toComparison := projComparison Q hQ T
  classNorm := norm
  meshSize := perturbMesh
  α := 1
  C := 0
  C' := 2 * ‖idWave 𝕜‖
  approx x _ n t _ := by
    change ‖_ - (projPerturbed 𝕜 Q hQ).incl n
      ((projPerturbed 𝕜 Q hQ).proj n ((idComplex 𝕜).waveGroup.S t x))‖ ≤ _
    rw [projPerturbed_incl_proj, sub_self, norm_zero]
    simp
  consistency x _ n t _ := by
    rw [Real.rpow_one]
    exact (norm_projComparison_defect_le Q hQ T x n t).trans_eq (by ring)

/-- **The approximating FEEC theorem applies to `projPerturbed`.** -/
theorem projPerturbed_verdict : (projPerturbed 𝕜 Q hQ).Verdict (projCore Q hQ) := approxFEEC _ _

/-- **The commutator defect is genuinely nonzero**: at every level and time, along the datum
`e^{-tL} (1, 0, 0)`. -/
theorem projComparison_defect_ne_zero (T : ℝ) (n : ℕ) (t : ℝ) :
    (projComparison Q hQ T).defect ((idComplex 𝕜).waveGroup.S (-t) (firstDatum 𝕜)) n t ≠ 0 := by
  rw [projComparison_defect, ← C0Group.map_add_apply, add_neg_cancel, C0Group.S_zero_apply,
    firstProj_firstDatum]
  refine smul_ne_zero (RCLike.ofReal_ne_zero.2 (projCoeff_pos n).ne') fun h => ?_
  exact firstProj_idWave_firstDatum_ne (sub_eq_zero.1 h).symm

/-- **The scheme is inexact**: at every level, the discrete solution from `πₙ (1, 0, 0)` differs
from the exact one at some time. -/
theorem projPerturbed_exists_sol_ne (n : ℕ) :
    ∃ t, (projPerturbed 𝕜 Q hQ).sol n ((projPerturbed 𝕜 Q hQ).proj n (firstDatum 𝕜)) t ≠
      (idComplex 𝕜).waveGroup.S t (firstDatum 𝕜) := by
  refine (projPerturbed 𝕜 Q hQ).exists_sol_ne (mem_idComplex_wave_domain _) n _ fun he => ?_
  set y := idWave 𝕜 (firstDatum 𝕜)
  have hp : (projPerturbed 𝕜 Q hQ).proj n (firstDatum 𝕜) =
      (1 - (projCoeff n : 𝕜)) • firstDatum 𝕜 := by
    rw [projPerturbed_proj_apply, firstProj_firstDatum, sub_smul, one_smul]
  change (projPerturbed 𝕜 Q hQ).incl n (idWave 𝕜 ((projPerturbed 𝕜 Q hQ).proj n
    (firstDatum 𝕜))) = y at he
  rw [hp, (idWave 𝕜).map_smul, projPerturbed_incl_apply, (firstProj 𝕜).map_smul] at he
  have key : (projCoeff n : 𝕜) • (firstProj 𝕜 y - y) = 0 := by
    have e1 := one_sub_projCoeff_mul (𝕜 := 𝕜) n
    calc (projCoeff n : 𝕜) • (firstProj 𝕜 y - y) =
          ((1 - (projCoeff n : 𝕜)) • y +
            (perturbMesh n : 𝕜) • (1 - (projCoeff n : 𝕜)) • firstProj 𝕜 y) - y := by
          rw [smul_smul, mul_comm, e1]; module
      _ = 0 := by rw [he, sub_self]
  rcases smul_eq_zero.1 key with h | h
  · exact (RCLike.ofReal_ne_zero.2 (projCoeff_pos n).ne') h
  · exact firstProj_idWave_firstDatum_ne (sub_eq_zero.1 h)

/-- **Non-vacuity with a non-scalar reading map.** At every level `ιₙ` is not a scalar multiple
of the identity and not isometric, `ιₙ πₙ = 1`, the scheme is inexact, and the consistency defect
(a commutator `bₙ [L₀, P]`) is nonzero at every time; the core is all of `W`, the rate class is
`O(h)`; for `K = 𝕜 × 0 × 0` (graded, `R`-invariant, not reducing) a datum of `D(L) ∩ K` leaves
`K` forward in time, and the residuals of its discretization `πₙ x` tend to a positive limit and
stay eventually above half of it. -/
theorem projPerturbed_nonvacuous :
    (∀ n, (∀ a : 𝕜, (projPerturbed 𝕜 Q hQ).incl n ≠ a • ContinuousLinearMap.id 𝕜 _) ∧
      ‖(projPerturbed 𝕜 Q hQ).incl n (firstDatum 𝕜)‖ ≠ ‖firstDatum 𝕜‖ ∧
      (∀ x, (projPerturbed 𝕜 Q hQ).incl n ((projPerturbed 𝕜 Q hQ).proj n x) = x) ∧
      (∃ t, (projPerturbed 𝕜 Q hQ).sol n ((projPerturbed 𝕜 Q hQ).proj n (firstDatum 𝕜)) t ≠
        (idComplex 𝕜).waveGroup.S t (firstDatum 𝕜)) ∧
      ∀ T t, (projComparison Q hQ T).defect
        ((idComplex 𝕜).waveGroup.S (-t) (firstDatum 𝕜)) n t ≠ 0) ∧
    (projCore Q hQ).Data = ⊤ ∧
    (∀ T, (projRate Q hQ T).Data = univ ∧ (projRate Q hQ T).α = 1 ∧
      (projRate Q hQ T).meshSize = perturbMesh ∧ (projRate Q hQ T).C = 0) ∧
    ∀ T : ℝ, 0 < T → ∃ x : (idComplex 𝕜).wave.domain, (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) ∈ firstSub 𝕜 ∧
      ∃ t ∈ Icc 0 T, (idComplex 𝕜).waveGroup.S t x ∉ firstSub 𝕜 ∧
      0 < infDist ((idComplex 𝕜).waveGroup.S t x) (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))) ∧
      Tendsto (fun n => infDist ((projPerturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).sol n
          ((projPerturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).proj n x) t)
        (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) atTop
        (𝓝 (infDist ((idComplex 𝕜).waveGroup.S t x)
          (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))))) ∧
      ∀ᶠ n in atTop, infDist ((idComplex 𝕜).waveGroup.S t x)
          (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))) / 2 <
        infDist ((projPerturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).sol n
          ((projPerturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).proj n x) t)
          (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))) := by
  have hι : ∀ n, (projPerturbed 𝕜 Q hQ).incl n (firstDatum 𝕜) =
      ((1 + perturbMesh n : ℝ) : 𝕜) • firstDatum 𝕜 := fun n => by
    rw [projPerturbed_incl_apply, firstProj_firstDatum]; push_cast; module
  refine ⟨fun n => ⟨fun a ha => ?_, ?_, projPerturbed_incl_proj Q hQ n,
      projPerturbed_exists_sol_ne Q hQ n, fun T t => projComparison_defect_ne_zero Q hQ T n t⟩,
    rfl, fun T => ⟨rfl, rfl, rfl, rfl⟩, fun T hT => ?_⟩
  · -- not a scalar: compare `(1, 0, 0)` with `L₀ (1, 0, 0)`
    have h1 := congrArg (fun A : PiLp 2 (W3 𝕜 𝕜 PUnit) →L[𝕜] PiLp 2 (W3 𝕜 𝕜 PUnit) =>
      A (firstDatum 𝕜)) ha
    simp only [hι, _root_.smul_apply, ContinuousLinearMap.id_apply] at h1
    have ha' : a = ((1 + perturbMesh n : ℝ) : 𝕜) := by
      have h2 : (a - ((1 + perturbMesh n : ℝ) : 𝕜)) • firstDatum 𝕜 = 0 := by
        rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact (sub_eq_zero.1 h3)
      · exact absurd h3 firstDatum_ne_zero
    set y := idWave 𝕜 (firstDatum 𝕜)
    have h4 : y + (perturbMesh n : 𝕜) • firstProj 𝕜 y = ((1 + perturbMesh n : ℝ) : 𝕜) • y := by
      rw [← projPerturbed_incl_apply Q hQ n y, ha, ha']; rfl
    have h5 : (perturbMesh n : 𝕜) • (firstProj 𝕜 y - y) = 0 := by
      rw [smul_sub]
      push_cast at h4
      calc _ = (y + (perturbMesh n : 𝕜) • firstProj 𝕜 y) - (1 + (perturbMesh n : 𝕜)) • y := by
            module
        _ = 0 := by rw [h4, sub_self]
    rcases smul_eq_zero.1 h5 with h6 | h6
    · exact (RCLike.ofReal_ne_zero.2 (perturbMesh_pos n).ne') h6
    · exact firstProj_idWave_firstDatum_ne (sub_eq_zero.1 h6)
  · rw [hι, norm_smul, RCLike.norm_ofReal, abs_of_pos (by linarith [perturbMesh_pos n])]
    intro h
    have hx' : ‖firstDatum 𝕜‖ ≠ 0 := norm_ne_zero_iff.2 firstDatum_ne_zero
    have := mul_right_cancel₀ hx' (h.trans (one_mul _).symm)
    linarith [perturbMesh_pos n]
  · obtain ⟨x, hxK, t, ht, hout, hpos, hres⟩ :=
      approxFEEC_residual_not_isReducing_of_grading
        (projPerturbed 𝕜 (firstSub 𝕜) isClosed_totalSub) (projCore _ _)
        (p := fun i : Fin 3 => decide (Odd i.val)) fin3_parity
        (fun x hx => reversal_mem_totalSub hx)
        (fun k hk => subset_closure ⟨mem_idComplex_wave_domain k, hk⟩) not_isReducing_firstSub hT
    have hxc : (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) ∈
        (projCore (firstSub 𝕜) isClosed_totalSub).Data.topologicalClosure :=
      Submodule.le_topologicalClosure _ Submodule.mem_top
    have hv : Tendsto (fun n => (projPerturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).incl n
        ((projPerturbed 𝕜 (firstSub 𝕜) isClosed_totalSub).proj n x)) atTop
        (𝓝 (x : PiLp 2 (W3 𝕜 𝕜 PUnit))) :=
      (tendsto_const_nhds (x := (x : PiLp 2 (W3 𝕜 𝕜 PUnit)))).congr fun n =>
        (projPerturbed_incl_proj (𝕜 := 𝕜) (firstSub 𝕜) isClosed_totalSub n
          (x : PiLp 2 (W3 𝕜 𝕜 PUnit))).symm
    obtain ⟨hlim, hev⟩ := hres hxc _ hv
    exact ⟨x, hxK, t, ht, hout, hpos, hlim, hev⟩

/-! ### The conforming bridge, instantiated -/

/-- **The conforming bridge on a concrete discretization**: the approximating FEEC verdict of the
constrained FEEC discretization `idFEEC` of `𝕜 --id--> 𝕜 → 0` (any closed constraint), through
`ConstrainedFEEC.toApprox` / `ConstrainedFEEC.toCore`, whose core is `D(L²)`. -/
theorem idFEEC_approxFEEC_verdict :
    (idFEEC 𝕜 Q hQ).toApprox.Verdict (idFEEC 𝕜 Q hQ).toCore ∧
      (idFEEC 𝕜 Q hQ).toCore.Data = (idComplex 𝕜).wave.domainSq :=
  ⟨approxFEEC _ _, rfl⟩

/-- **`constrainedFEEC` for `idFEEC`, from `approxFEEC`** (the statement of `constrainedFEEC`). -/
theorem idFEEC_constrainedFEEC_of_approxFEEC : type_of% (constrainedFEEC (idFEEC 𝕜 Q hQ)) :=
  ConstrainedFEEC.constrainedFEEC_of_approxFEEC _

end ApproxFEEC

end Feec.HilbertComplex
