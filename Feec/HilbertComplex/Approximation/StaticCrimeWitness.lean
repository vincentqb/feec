module

public import Feec.HilbertComplex.Approximation.ApproxComplexCrimeWitness
public import Feec.HilbertComplex.Approximation.HeatCrime

/-!
# Non-vacuity of the static and heat theorems with variational crimes

On `𝕜 --id--> 𝕜 → 0`, the shifted family `𝐝ₙ = cₙ d`, read by the identity, not a cochain map,
satisfies the hypotheses of the static and heat theorems with crimes, with a positive static error.

## Main results

* `ApproxComplexCrime.shifted_static_nonvacuous`: the witness for the static theorem with crimes.
* `ApproxComplexCrime.shifted_heat`: the heat FEEC theorem with crimes applies.
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

namespace ApproxComplexCrime

open ConstrainedFEEC ShortHilbertComplex ApproxFEEC ApproxComplex

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The differentials on components -/

theorem idTotalD_eq (v : (idComplex 𝕜).totalD.domain) :
    (idComplex 𝕜).totalD v = vec3 0 (c0 (v : PiLp 2 (W3 𝕜 𝕜 PUnit))) :=
  ext3 (c0_idTotalD v) (c1_idTotalD v)

theorem shifted_D_eq (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (shiftedFamily 𝕜).D n v = vec3 0 (sc n * c0 v) :=
  ext3 (c0_scaled_D n v) (c1_scaled_D n v)

theorem c0_total_mixedD0 (Y : (idComplex 𝕜).total.MixedSpace () ()) :
    c0 ((idComplex 𝕜).total.mixedD0 () () Y) = 0 :=
  c0_idTotalD _

theorem total_mixedD1_eq (Y : (idComplex 𝕜).total.MixedSpace () ()) :
    (idComplex 𝕜).total.mixedD1 () () () Y = vec3 0 (c0 ((idComplex 𝕜).total.mixedI1 () () Y)) :=
  idTotalD_eq _

theorem shifted_incl_apply (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (shiftedFamily 𝕜).incl n v = v :=
  rfl

theorem norm_sc_le_two (n : ℕ) : ‖sc (𝕜 := 𝕜) n‖ ≤ 2 := by
  rw [RCLike.norm_ofReal, abs_of_pos (perturbScale_pos n)]
  unfold perturbScale; linarith [perturbMesh_le_one n]

theorem norm_shifted_D_le (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖(shiftedFamily 𝕜).D n v‖ ≤ 2 * ‖v‖ := by
  rw [shifted_D_eq, norm_vec3_zero, norm_mul]
  exact mul_le_mul (norm_sc_le_two n) (norm_c0_le v) (norm_nonneg _) (by norm_num)

/-! ### Closed range and the discrete Poincaré inequality -/

theorem closedRangeAt_idComplex (i : Fin 3) : (idComplex 𝕜).ClosedRangeAt i :=
  Submodule.closed_of_finiteDimensional _

theorem shifted_isPoincare : ∃ cP, 1 ≤ cP ∧ (shiftedFamily 𝕜).IsPoincare cP := by
  obtain ⟨C, hC⟩ := (idComplex 𝕜).exists_poincare_totalD closedRangeAt_idComplex
  have h := (shiftedFamily 𝕜).isPoincare_of_proj (c₀ := max C 0) (C' := 1)
    (fun z hz => (hC z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    (fun _ v => mem_idComplex_totalD_domain v)
    (fun n v => by
      rw [idTotalD_eq, shifted_D_eq, norm_vec3_zero, norm_vec3_zero, norm_mul, one_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) (one_lt_norm_sc n).le)
    (shiftedFamily 𝕜).proj (shiftedFamily 𝕜).proj_incl (shiftedFamily 𝕜).norm_proj_le
    (fun n z hz => by
      have h0 : c0 (z : PiLp 2 (W3 𝕜 𝕜 PUnit)) = 0 := by
        have := congrArg c1 hz
        rwa [idTotalD_eq, c1_vec3] at this
      change (shiftedFamily 𝕜).D n z = 0
      rw [shifted_D_eq, h0, mul_zero]
      exact ext3 rfl rfl)
  exact ⟨_, le_max_right _ 1, h.mono (le_max_left _ _)⟩

/-! ### No harmonic forms -/

theorem eq_zero_of_mem_harmonic_total {q : PiLp 2 (W3 𝕜 𝕜 PUnit)}
    (hq : q ∈ (idComplex 𝕜).total.harmonic ()) : q = 0 := by
  obtain ⟨hz, hb⟩ := (idComplex 𝕜).total.mem_harmonic_iff.1 hq
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hz
  have h0 : c0 q = 0 := by
    rw [hy]; exact (c1_idTotalD y).symm.trans ((congrArg c1 hy0).trans rfl)
  have hd : (idComplex 𝕜).totalD ⟨firstDatum 𝕜, mem_idComplex_totalD_domain _⟩ ∈
      (idComplex 𝕜).total.boundaries () := ⟨⟨firstDatum 𝕜, mem_idComplex_totalD_domain _⟩, rfl⟩
  have h1 : c1 q = 0 := by
    have := Submodule.inner_right_of_mem_orthogonal hd hb
    rw [idTotalD_eq, inner_W3] at this
    simpa [show c0 (firstDatum 𝕜) = (1 : 𝕜) from rfl] using this
  exact ext3 h0 h1

theorem eq_zero_of_mem_shifted_harmonic (n : ℕ) {q : PiLp 2 (W3 𝕜 𝕜 PUnit)}
    (hq : q ∈ ((shiftedFamily 𝕜).cpx n).harmonic ()) : q = 0 := by
  obtain ⟨h1, h2⟩ := (mem_diffComplex_harmonic _ _).1 hq
  have hsc : sc (𝕜 := 𝕜) n ≠ 0 := fun h => by
    have := one_lt_norm_sc (𝕜 := 𝕜) n; rw [h, norm_zero] at this; linarith
  have h0 : c0 q = 0 := by
    have := congrArg c1 h1
    rw [shifted_D_eq, c1_vec3] at this
    exact (mul_eq_zero.1 this).resolve_left hsc
  have h1' : c1 q = 0 := by
    have e : ⟪(shiftedFamily 𝕜).D n (firstDatum 𝕜), q⟫_𝕜 = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, h2, inner_zero_right]
    rw [shifted_D_eq, inner_W3] at e
    simp only [c0_vec3, c1_vec3, _root_.map_zero, zero_mul, zero_add,
      show c0 (firstDatum 𝕜) = (1 : 𝕜) from rfl, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_left ((map_ne_zero _).2 hsc)
  exact ext3 h0 h1'

/-! ### Consistent approximation for every datum -/

/-- The approximant: the continuous `σ`, `u` read in `Xₙ = W`, and `p̃ = 0`. -/
def shiftedApprox (n : ℕ) (f : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ((shiftedFamily 𝕜).cpx n).MixedSpace () () :=
  MixedSpace.mk
    (toDom _ _ ((idComplex 𝕜).total.mixedI0 () () ((idComplex 𝕜).totalMixedSolution
      closedRangeAt_idComplex f)))
    (toDom _ _ ((idComplex 𝕜).total.mixedI1 () () ((idComplex 𝕜).totalMixedSolution
      closedRangeAt_idComplex f))) 0

theorem norm_toDom_le (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖toDom ((shiftedFamily 𝕜).D n) ((shiftedFamily 𝕜).D_D n) v‖ ≤ 3 * ‖v‖ := by
  have e := ((shiftedFamily 𝕜).cpx n).norm_sq_domainSpace ()
    (toDom ((shiftedFamily 𝕜).D n) ((shiftedFamily 𝕜).D_D n) v)
  have e' : ‖toDom ((shiftedFamily 𝕜).D n) ((shiftedFamily 𝕜).D_D n) v‖ ^ 2 =
      ‖v‖ ^ 2 + ‖(shiftedFamily 𝕜).D n v‖ ^ 2 := e
  have h := norm_shifted_D_le n v
  have := norm_nonneg (toDom ((shiftedFamily 𝕜).D n) ((shiftedFamily 𝕜).D_D n) v)
  nlinarith [norm_nonneg v, norm_nonneg ((shiftedFamily 𝕜).D n v)]

theorem shiftedApprox_fst (n : ℕ) (f : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (shiftedApprox n f).fst = toDom ((shiftedFamily 𝕜).D n) ((shiftedFamily 𝕜).D_D n)
      ((idComplex 𝕜).total.mixedI0 () () ((idComplex 𝕜).totalMixedSolution
        closedRangeAt_idComplex f)) := by
  simp only [shiftedApprox, MixedSpace.mk_fst]

theorem shiftedApprox_snd_fst (n : ℕ) (f : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (shiftedApprox n f).snd.fst = toDom ((shiftedFamily 𝕜).D n) ((shiftedFamily 𝕜).D_D n)
      ((idComplex 𝕜).total.mixedI1 () () ((idComplex 𝕜).totalMixedSolution
        closedRangeAt_idComplex f)) := by
  simp only [shiftedApprox, MixedSpace.mk_snd_fst]

theorem shiftedApprox_snd_snd (n : ℕ) (f : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (shiftedApprox n f).snd.snd = 0 := by
  simp only [shiftedApprox, MixedSpace.mk_snd_snd]

theorem norm_shiftedApprox_le (n : ℕ) (f : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖shiftedApprox n f‖ ≤
      3 * ‖(idComplex 𝕜).total.mixedI0 () () ((idComplex 𝕜).totalMixedSolution
        closedRangeAt_idComplex f)‖ +
      3 * ‖(idComplex 𝕜).total.mixedI1 () () ((idComplex 𝕜).totalMixedSolution
        closedRangeAt_idComplex f)‖ := by
  have e := MixedSpace.norm_sq (shiftedApprox (𝕜 := 𝕜) n f)
  rw [shiftedApprox_fst, shiftedApprox_snd_fst, shiftedApprox_snd_snd, ZeroMemClass.coe_zero,
    norm_zero, zero_pow two_ne_zero, add_zero] at e
  have h1 := norm_toDom_le (𝕜 := 𝕜) n ((idComplex 𝕜).total.mixedI0 () ()
    ((idComplex 𝕜).totalMixedSolution closedRangeAt_idComplex f))
  have h2 := norm_toDom_le (𝕜 := 𝕜) n ((idComplex 𝕜).total.mixedI1 () ()
    ((idComplex 𝕜).totalMixedSolution closedRangeAt_idComplex f))
  have := norm_nonneg (shiftedApprox (𝕜 := 𝕜) n f)
  nlinarith [norm_nonneg (toDom ((shiftedFamily 𝕜).D n) ((shiftedFamily 𝕜).D_D n)
      ((idComplex 𝕜).total.mixedI0 () () ((idComplex 𝕜).totalMixedSolution
        closedRangeAt_idComplex f))),
    norm_nonneg (toDom ((shiftedFamily 𝕜).D n) ((shiftedFamily 𝕜).D_D n)
      ((idComplex 𝕜).total.mixedI1 () () ((idComplex 𝕜).totalMixedSolution
        closedRangeAt_idComplex f)))]

theorem readError_shiftedApprox_le (n : ℕ) (f : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (shiftedFamily 𝕜).readError n ((idComplex 𝕜).totalMixedSolution closedRangeAt_idComplex f)
        (shiftedApprox n f) ≤
      perturbMesh n * (‖(idComplex 𝕜).total.mixedI0 () () ((idComplex 𝕜).totalMixedSolution
        closedRangeAt_idComplex f)‖ + ‖(idComplex 𝕜).total.mixedI1 () ()
          ((idComplex 𝕜).totalMixedSolution closedRangeAt_idComplex f)‖) := by
  set X := (idComplex 𝕜).totalMixedSolution closedRangeAt_idComplex f
  have hp : (idComplex 𝕜).total.mixedI2 () () X = 0 :=
    eq_zero_of_mem_harmonic_total (X.snd.snd.2)
  have i0 : ((shiftedFamily 𝕜).cpx n).mixedI0 () () (shiftedApprox n f) =
      (idComplex 𝕜).total.mixedI0 () () X := by
    rw [mixedI0_apply, shiftedApprox_fst, domainIncl_toDom]
  have i1 : ((shiftedFamily 𝕜).cpx n).mixedI1 () () (shiftedApprox n f) =
      (idComplex 𝕜).total.mixedI1 () () X := by
    rw [mixedI1_apply, shiftedApprox_snd_fst, domainIncl_toDom]
  have i2 : ((shiftedFamily 𝕜).cpx n).mixedI2 () () (shiftedApprox n f) = 0 := by
    rw [mixedI2_apply, shiftedApprox_snd_snd, ZeroMemClass.coe_zero]
  have e1 : ‖(idComplex 𝕜).total.mixedD0 () () X - (shiftedFamily 𝕜).incl n
      ((shiftedFamily 𝕜).D n ((idComplex 𝕜).total.mixedI0 () () X))‖ ≤
        perturbMesh n * ‖(idComplex 𝕜).total.mixedI0 () () X‖ :=
    norm_idTotalD_sub_shifted_le n _
  have e3 : ‖(idComplex 𝕜).total.mixedD1 () () () X - (shiftedFamily 𝕜).incl n
      ((shiftedFamily 𝕜).D n ((idComplex 𝕜).total.mixedI1 () () X))‖ ≤
        perturbMesh n * ‖(idComplex 𝕜).total.mixedI1 () () X‖ :=
    norm_idTotalD_sub_shifted_le n _
  have t0 : ‖(idComplex 𝕜).total.mixedI0 () () X - (shiftedFamily 𝕜).incl n
      (((shiftedFamily 𝕜).cpx n).mixedI0 () () (shiftedApprox n f))‖ = 0 := by
    rw [i0, shifted_incl_apply, sub_self, norm_zero]
  have t1 : ‖(idComplex 𝕜).total.mixedD0 () () X - (shiftedFamily 𝕜).incl n
      (((shiftedFamily 𝕜).cpx n).mixedD0 () () (shiftedApprox n f))‖ ≤
        perturbMesh n * ‖(idComplex 𝕜).total.mixedI0 () () X‖ := by
    rw [Family.cpx_mixedD0, i0]; exact e1
  have t2 : ‖(idComplex 𝕜).total.mixedI1 () () X - (shiftedFamily 𝕜).incl n
      (((shiftedFamily 𝕜).cpx n).mixedI1 () () (shiftedApprox n f))‖ = 0 := by
    rw [i1, shifted_incl_apply, sub_self, norm_zero]
  have t3 : ‖(idComplex 𝕜).total.mixedD1 () () () X - (shiftedFamily 𝕜).incl n
      (((shiftedFamily 𝕜).cpx n).mixedD1 () () () (shiftedApprox n f))‖ ≤
        perturbMesh n * ‖(idComplex 𝕜).total.mixedI1 () () X‖ := by
    rw [Family.cpx_mixedD1, i1]; exact e3
  have t4 : ‖(idComplex 𝕜).total.mixedI2 () () X - (shiftedFamily 𝕜).incl n
      (((shiftedFamily 𝕜).cpx n).mixedI2 () () (shiftedApprox n f))‖ = 0 := by
    rw [i2, hp, shifted_incl_apply, sub_self, norm_zero]
  unfold Family.readError
  linarith

theorem shifted_staticConsistent (f : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (shiftedFamily 𝕜).StaticConsistent closedRangeAt_idComplex atTop f := by
  set X := (idComplex 𝕜).totalMixedSolution closedRangeAt_idComplex f
  have hJ : Tendsto (shiftedFamily 𝕜).graphDefect atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun n =>
      (((shiftedFamily 𝕜).graphDefect_eq_zero_iff n).2 (shifted_J n)).symm
  set a := ‖(idComplex 𝕜).total.mixedI0 () () X‖
  set b := ‖(idComplex 𝕜).total.mixedI1 () () X‖
  set g := ‖((idComplex 𝕜).greenWave closedRangeAt_idComplex f : PiLp 2 (W3 𝕜 𝕜 PUnit))‖
  set dg := ‖((idComplex 𝕜).dGreenWave closedRangeAt_idComplex f : PiLp 2 (W3 𝕜 𝕜 PUnit))‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hg : 0 ≤ g := norm_nonneg _
  have hdg : 0 ≤ dg := norm_nonneg _
  refine (shiftedFamily 𝕜).staticConsistent_of_split closedRangeAt_idComplex hJ
    (B := 3 * a + 3 * b) f fun ε hε => ?_
  have hev := (tendsto_perturbMesh.mul_const (a + b + g + dg)).eventually
    (gt_mem_nhds (show (0 : ℝ) * (a + b + g + dg) < ε by rw [zero_mul]; exact hε))
  filter_upwards [hev] with n hn
  have hm := (perturbMesh_pos n).le
  have hab : perturbMesh n * (a + b) ≤ perturbMesh n * (a + b + g + dg) :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  have hgl : perturbMesh n * g ≤ perturbMesh n * (a + b + g + dg) :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  have hdgl : perturbMesh n * dg ≤ perturbMesh n * (a + b + g + dg) :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  refine ⟨shiftedApprox n f, norm_shiftedApprox_le n f,
    (readError_shiftedApprox_le n f).trans (by linarith), fun v => ?_, fun v => ?_,
    fun q hq => ?_⟩
  · refine (norm_inner_shifted_cochainDefect_le n _ v).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith
  · refine (norm_inner_shifted_cochainDefect_le n _ v).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith
  · rw [eq_zero_of_mem_shifted_harmonic n hq, _root_.map_zero, inner_zero_left, norm_zero,
      norm_zero, mul_zero]

theorem shifted_tendsto_staticError (f : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    Tendsto (fun n => (shiftedFamily 𝕜).staticError closedRangeAt_idComplex n f) atTop (𝓝 0) :=
  let ⟨_, hcP, hP⟩ := shifted_isPoincare (𝕜 := 𝕜)
  ((shiftedFamily 𝕜).staticConsistent_iff_tendsto closedRangeAt_idComplex hP hcP atTop f).1
    (shifted_staticConsistent f)

theorem shifted_staticError_pos (n : ℕ) :
    0 < (shiftedFamily 𝕜).staticError closedRangeAt_idComplex n (firstDatum 𝕜) := by
  set X := (idComplex 𝕜).totalMixedSolution closedRangeAt_idComplex (firstDatum 𝕜)
  set x := (shiftedFamily 𝕜).mixedSol n (firstDatum 𝕜)
  -- `u₀ = 1`
  have hs := (idComplex 𝕜).isMixedSolution_totalMixedSolution closedRangeAt_idComplex (firstDatum 𝕜)
  have hu0 : c0 ((idComplex 𝕜).total.mixedI1 () () X) = 1 := by
    have e := hs.snd ((idComplex 𝕜).total.toDomainSpace (loop_rel () ())
      ⟨firstDatum 𝕜, mem_idComplex_totalD_domain _⟩)
    rw [domainIncl_toDomainSpace, d_domainCoord_toDomainSpace] at e
    have hp : (X.snd.snd : PiLp 2 (W3 𝕜 𝕜 PUnit)) = 0 :=
      eq_zero_of_mem_harmonic_total X.snd.snd.2
    rw [hp, inner_zero_right, add_zero] at e
    change ⟪firstDatum 𝕜, (idComplex 𝕜).total.mixedD0 () () X⟫_𝕜 +
      ⟪(idComplex 𝕜).totalD ⟨firstDatum 𝕜, mem_idComplex_totalD_domain _⟩,
        (idComplex 𝕜).total.mixedD1 () () () X⟫_𝕜 = ⟪firstDatum 𝕜, firstDatum 𝕜⟫_𝕜 at e
    rw [inner_firstDatum_left, inner_firstDatum_left, c0_total_mixedD0, zero_add,
      total_mixedD1_eq, idTotalD_eq, inner_W3] at e
    simpa [show c0 (firstDatum 𝕜) = (1 : 𝕜) from rfl] using e
  refine lt_of_le_of_ne ((shiftedFamily 𝕜).staticError_nonneg _ n _) fun h0 => ?_
  have h0' := h0.symm
  unfold Family.staticError Family.readError at h0'
  have hn := fun a b c d e : ℝ => fun (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hs : a + b + c + d + e = 0) => (show c = 0 ∧ d = 0 by
      constructor <;> linarith)
  obtain ⟨hc, hd⟩ := hn _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) h0'
  rw [norm_eq_zero, sub_eq_zero] at hc hd
  -- `uₙ = u` and `𝐝ₙ uₙ = 𝐝 u`
  have hc' : ((shiftedFamily 𝕜).cpx n).mixedI1 () () x = (idComplex 𝕜).total.mixedI1 () () X :=
    hc.symm
  have hd' : (idComplex 𝕜).total.mixedD1 () () () X =
      (shiftedFamily 𝕜).D n ((idComplex 𝕜).total.mixedI1 () () X) := by
    rw [← hc']; exact hd
  have e := congrArg c1 hd'
  rw [total_mixedD1_eq, c1_vec3, shifted_D_eq, c1_vec3] at e
  change c0 ((idComplex 𝕜).total.mixedI1 () () X) =
    sc n * c0 ((idComplex 𝕜).total.mixedI1 () () X) at e
  rw [hu0, mul_one] at e
  have := one_lt_norm_sc (𝕜 := 𝕜) n
  rw [← e, norm_one] at this
  exact lt_irrefl _ this

/-! ### The theorems apply -/

variable (Q : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))) (hQ : IsClosed (Q : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))))

/-- **The heat FEEC theorem with crimes applies to the shifted family.** -/
theorem shifted_heat : ∃ (cP : ℝ) (hcP : 1 ≤ cP) (hP : (shiftedFamily 𝕜).IsPoincare cP),
    (shifted 𝕜 Q hQ).toHeat.Verdict ((shifted 𝕜 Q hQ).heatCore closedRangeAt_idComplex hcP hP
      shifted_tendsto_staticError) :=
  let ⟨cP, hcP, hP⟩ := shifted_isPoincare (𝕜 := 𝕜)
  ⟨cP, hcP, hP, (shifted 𝕜 Q hQ).heatFEEC closedRangeAt_idComplex hcP hP _⟩

variable (𝕜) in
/-- **Non-vacuity of the static FEEC theorem with crimes**: for the shifted family, with a nonzero
cochain defect, the hypotheses hold and the static errors tend to `0`, positive at `(1, 0, 0)`. -/
theorem shifted_static_nonvacuous :
    (∀ i, (idComplex 𝕜).ClosedRangeAt i) ∧
      (∃ cP, 1 ≤ cP ∧ (shiftedFamily 𝕜).IsPoincare cP) ∧
      (∀ n, (shiftedFamily 𝕜).cochainDefect n
        ⟨secondDatum 𝕜, mem_idComplex_wave_domain _⟩ ≠ 0) ∧
      (∀ f, (shiftedFamily 𝕜).StaticConsistent closedRangeAt_idComplex atTop f) ∧
      (∀ f, Tendsto (fun n => (shiftedFamily 𝕜).staticError closedRangeAt_idComplex n f) atTop
        (𝓝 0)) ∧
      ∀ n, 0 < (shiftedFamily 𝕜).staticError closedRangeAt_idComplex n (firstDatum 𝕜) :=
  ⟨closedRangeAt_idComplex, shifted_isPoincare, shifted_cochainDefect_ne_zero,
    shifted_staticConsistent, shifted_tendsto_staticError, shifted_staticError_pos⟩

end ApproxComplexCrime

end Feec.HilbertComplex
