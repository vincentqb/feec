module

public import Feec.Instances.EinsteinBianchiFEMMirrorCore
public import Feec.Instances.EinsteinBianchiFEMElliptic

/-!
# The mirror scheme (6.5): convergence from best approximation plus consistency

For the approximating FEEC discretization `mirrorFEMApprox` of the mirror scheme (6.5)
(`Feec.Instances.EinsteinBianchiFEMMirror`), this file builds the **elliptic core** `mirrorEllCore`
and the **elliptic rate classes** `mirrorEllRate` (TSD data of `D(L³)`, order `1`) and
`mirrorEllRateSobolev` (TSD data in `H^{2+s}`, order `s ≤ 1`), whose comparison trajectory is the
elliptic projection (6.4) of the exact TSD solution (real and imaginary parts,
`Feec.Instances.EinsteinBianchi.FEM.ellTraj`), not the discrete orbit. Its consistency defect
`Πₕ' - Lₕ Πₕ` is bounded by the projection errors of the state and of its time derivative
(`norm_ellDefect_le`). For these TSD data the consistency terms of the Strang bound, which measure
the crime `S - Sₕ`, vanish exactly (`K₀ = K₁ = 0`: `TSDDatum.ell_S0_le_zero`,
`TSDDatum.inner_M_S1_le_zero`), so any defect comes from the elliptic projection not commuting with
the flow; that it is nonzero is not proved. So the convergence of (6.5) comes out of the
approximating FEEC theorem's split "best approximation + consistency" (`ApproxFEEC.norm_sub_sol_le`)
with only the Strang bound of the elliptic projection (6.4) as model input (`norm_sub_ellTraj_le`,
from `Feec.BGG.HarmonicStability.strang_of_isEllipticProjection`, the parity-smoothed projection
errors `eventually_mirrorClose`, and the Sobolev projection errors
`Feec.Models.Cube.MirrorWeakSymmetry.TSDDatum.strangData_le`); the model convergence theorems
`mirror_waveFEM`, `mirror_waveFEM_rate_*` are **not** used.

The comparison of a datum on `[0, T]` uses the exact TSD solution on the horizon `T + 1`, so that
the exact equations hold at `t = T`.

* `einsteinBianchi_mirrorFEM_approxFEEC_elliptic`: the verdict on `mirrorEllCore`;
* `mirrorEllCmp_p_horizon`, `mirrorEllInit`: the comparison trajectory, hence its initial value,
  does not depend on the horizon `T`;
* `einsteinBianchi_mirrorFEM_rate_init`, `einsteinBianchi_mirrorFEM_rate_sobolev_init`: the same
  rates for all `t ≥ 0` from the horizon-free initialization `mirrorEllInit`;
* `einsteinBianchi_mirrorFEM_rate_elliptic`, `einsteinBianchi_mirrorFEM_rate_sobolev_elliptic`: from
  the elliptic projection (6.4) of the initial data (`mirrorEllCmp_p_zero`, `mEll_zero_toEState`,
  the thesis' initialization), `‖e^{tL} ξ₀ - ι' e^{tL'} Πₕ(0)‖ ≤ (C + C' t) hᵅ ‖ξ₀‖_c` with
  `C' = 2C`, constants independent of `T`.

**Faithfulness caveat.** As for `mirrorFEMApprox`: faithful to `mirrorWave` (`S₀,ₕ = π¹S⁰` with
parity-smoothed projections), not to the canonical-interpolant variant. That the defect is
nonzero for some datum is not formalized (it would need an explicit finite element computation
with the smoothed projections).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.4)), §6.3 ((6.5))
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  Thm 3.9, Thm 3.10 (elliptic analogue)
-/

open scoped InnerProductSpace
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.HilbertComplex Feec.Models.Cube.MirrorWeakSymmetry Feec.Models.Cube.RowWise
open Feec.Models.Cube.MirrorBGG (SpaceQ W2Q complexQ tsdQ)
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)
open Feec.Models.Cube.FEM (meshSize meshSize_pos)
open Feec.BGG.Discrete (strangConst)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
    Feec.FiniteElement.PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3,
    Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a} Feec.FiniteElement.PolySeq.lagrangeP2 ρ C)

theorem mirrorSrcFun_zero_apply (t : ℝ) (v : BU1) : mirrorSrcFun 0 t v = 0 := by
  rw [mirrorSrcFun_apply, Pi.zero_apply, inner_zero_left]

/-! ### The elliptic trajectory of a TSD datum -/

/-- The elliptic projection (6.4) at level `N` of the exact TSD solution of `D` (horizon `T + 1`),
as a hidden state. -/
abbrev mEll (N : ℕ) (D : TSDDatum) (T t : ℝ) : mirrorHidden hT hB N :=
  ellTraj (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N)
    (D.exactWave (T + 1)) t

/-- Its time derivative. -/
abbrev mEll' (N : ℕ) (D : TSDDatum) (T t : ℝ) : mirrorHidden hT hB N :=
  ellTraj' (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
    (mirrorWave_S0_surjective hT hB N) (D.exactWave (T + 1)) t

/-- The projection error of the state. -/
abbrev ellErr (N : ℕ) (D : TSDDatum) (T t : ℝ) : ℝ :=
  ‖exState (D.exactWave (T + 1)) t - coeH (mirrorFEM hT hB N) (mEll hT hB N D T t).toEState‖

/-- The projection error of the time derivative. -/
abbrev ellErr' (N : ℕ) (D : TSDDatum) (T t : ℝ) : ℝ :=
  ‖exState' (D.exactWave (T + 1)) t - coeH (mirrorFEM hT hB N) (mEll' hT hB N D T t).toEState‖

theorem ellErr_nonneg (N : ℕ) (D : TSDDatum) (T t : ℝ) : 0 ≤ ellErr hT hB N D T t :=
  norm_nonneg _

theorem ellErr'_nonneg (N : ℕ) (D : TSDDatum) (T t : ℝ) : 0 ≤ ellErr' hT hB N D T t :=
  norm_nonneg _

theorem hg_mirror (T : ℝ) : ∀ t ∈ Ico 0 T, ∀ v, mirrorSrcFun 0 t v = 0 :=
  fun t _ v => mirrorSrcFun_zero_apply t v


set_option maxHeartbeats 1000000 in
/-- **The consistency defect of one real part** is bounded by the projection errors. -/
theorem norm_mEll_defect_le (N : ℕ) (D : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖mEll' hT hB N D T t - waveGen (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) (mEll hT hB N D T t)‖ ≤
      ellErr' hT hB N D T t + ellErr hT hB N D T t := by
  with_reducible_and_instances exact (norm_ellDefect_le (mirrorFEM hT hB N)
    (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N) (D.exactWave (T + 1))
    (hg_mirror (T + 1)) (Icc_sub_Ico_add_one ht))

set_option maxHeartbeats 1000000 in
/-- The four-term error of a discrete energy state against a TSD state is its energy error against
the forms state `(0, Re E, 0, ⋆Re B)` of the TSD solution. -/
theorem tsdErr_eq (N : ℕ) (D : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T)
    (p : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h (mirrorFEM hT hB N).W2h
      (mirrorFEM hT hB N).Wt2h) :
    tsdErr (D.U t) (EState.mk ((p.σ : TU0) : W0) (bIncl1 (p.u : BU1)) (p.M : W2) (p.ρ : Wv W2)) =
      ‖exState (D.exactWave T) t - coeH (mirrorFEM hT hB N) p‖ := by
  have hEq : EqOn D.U D.U (Icc 0 T) := fun _ _ => rfl
  have h1 := (Real.sqrt_sq (norm_nonneg
    (exState (D.exactWave T) t - coeH (mirrorFEM hT hB N) p))).symm
  have h2 := norm_exState_sub_coeH_sq (mirrorFEM hT hB N) (D.exactWave T) t p
  refine Eq.trans ?_ (h1.trans (congrArg Real.sqrt h2)).symm
  have e1 : ‖(D.exactWave T).σ t - (p.σ : TU0)‖ = ‖((p.σ : TU0) : W0)‖ := by
    change ‖(0 : TU0) - _‖ = _
    rw [zero_sub, norm_neg]
    rfl
  have e3 : ‖(D.exactWave T).M t - (p.M : W2)‖ = ‖(p.M : W2)‖ := by
    change ‖(0 : W2) - _‖ = _
    rw [zero_sub, norm_neg]
  have e2 := D.norm_exactWave_u_sub hEq ht p.u
  have e4 := D.norm_exactWave_ρ_sub hEq ht p.ρ
  unfold tsdErr
  refine congrArg Real.sqrt ?_
  -- positional congruence (rewriting would compare norms on unrelated subtypes)
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg (· ^ 2) e1.symm)
    (congrArg (· ^ 2) e2.symm)) (congrArg (· ^ 2) e3.symm)) (congrArg (· ^ 2) e4.symm)

set_option maxHeartbeats 1000000 in
/-- **The approximation error of one real part** is the projection error. -/
theorem tsdErr_mEll (N : ℕ) (D : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    tsdErr (D.U t) (mirrorFE hT hB N (mEll hT hB N D T t)) = ellErr hT hB N D T t :=
  tsdErr_eq hT hB N D (T := T + 1) ⟨ht.1, by linarith [ht.2]⟩ (mEll hT hB N D T t).toEState

/-! ### The comparison of complex data -/

/-- The TSD data of `D(L²)`. -/
abbrev mirrorEllData : Submodule ℝ (PiLp 2 SpaceQ) := tsdQℝ ⊓ complexQℝ.wave.domainSq

theorem continuousOn_mEll (N : ℕ) (D : TSDDatum) (T : ℝ) :
    ContinuousOn (mEll hT hB N D T) (Icc 0 T) := by
  with_reducible_and_instances exact
    ((continuousOn_ellTraj (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) (D.exactWave (T + 1))).mono (Icc_subset_Icc_add_one T))

theorem continuousOn_mEll' (N : ℕ) (D : TSDDatum) (T : ℝ) :
    ContinuousOn (mEll' hT hB N D T) (Icc 0 T) := by
  with_reducible_and_instances exact
    ((continuousOn_ellTraj' (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) (D.exactWave (T + 1))).mono (Icc_subset_Icc_add_one T))

theorem hasDerivWithinAt_mEll (N : ℕ) (D : TSDDatum) {T t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (mEll hT hB N D T) (mEll' hT hB N D T t) (Ici t) t := by
  with_reducible_and_instances exact
    (hasDerivWithinAt_ellTraj (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) (D.exactWave (T + 1)) (Ico_sub_Ico_add_one ht))

open Classical in
/-- The elliptic trajectory of the real part `ξ₀` of a datum (zero off the data). -/
def mirrorEllRe (T : ℝ) (x : PiLp 2 SpaceQ) (N : ℕ) (t : ℝ) : (mirrorFEMReal hT hB).X N :=
  if hx : x ∈ mirrorEllData then mEll hT hB N (tsdDatumOf hx) T t else 0

open Classical in
/-- The elliptic trajectory of the imaginary part `-i ξ₀` of a datum (zero off the data). -/
def mirrorEllIm (T : ℝ) (x : PiLp 2 SpaceQ) (N : ℕ) (t : ℝ) : (mirrorFEMReal hT hB).X N :=
  if hx : x ∈ mirrorEllData then mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t else 0

open Classical in
/-- The time derivative of `mirrorEllRe`. -/
def mirrorEllRe' (T : ℝ) (x : PiLp 2 SpaceQ) (N : ℕ) (t : ℝ) : (mirrorFEMReal hT hB).X N :=
  if hx : x ∈ mirrorEllData then mEll' hT hB N (tsdDatumOf hx) T t else 0

open Classical in
/-- The time derivative of `mirrorEllIm`. -/
def mirrorEllIm' (T : ℝ) (x : PiLp 2 SpaceQ) (N : ℕ) (t : ℝ) : (mirrorFEMReal hT hB).X N :=
  if hx : x ∈ mirrorEllData then mEll' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t else 0

theorem mirrorEllRe_of_mem (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ) :
    mirrorEllRe hT hB T x N = mEll hT hB N (tsdDatumOf hx) T :=
  funext fun _ => dite_eq_left hx

theorem mirrorEllIm_of_mem (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ) :
    mirrorEllIm hT hB T x N = mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T :=
  funext fun _ => dite_eq_left hx

theorem mirrorEllRe'_of_mem (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ) :
    mirrorEllRe' hT hB T x N = mEll' hT hB N (tsdDatumOf hx) T :=
  funext fun _ => dite_eq_left hx

theorem mirrorEllIm'_of_mem (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ) :
    mirrorEllIm' hT hB T x N = mEll' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T :=
  funext fun _ => dite_eq_left hx

set_option maxHeartbeats 1000000 in
/-- **The elliptic comparison** of the mirror scheme on `[0, T]`: the elliptic projections (6.4)
of the exact solutions from the real part `ξ₀` and the imaginary part `-i ξ₀` of the datum. -/
def mirrorEllCmp (T : ℝ) : (mirrorFEMApprox hT hB).Comparison T :=
  ApproxFEEC.complexifyCmp (mirrorFEMReal hT hB) mulI mulI_mulI norm_mulI
    (adjoint_mirrorEmb_mulI hT hB) (inner_mirrorEmb_mulI hT hB) mirrorEllData
    (mirrorEllRe hT hB T) (mirrorEllIm hT hB T) (mirrorEllRe' hT hB T) (mirrorEllIm' hT hB T)
    (fun x hx N => by rw [mirrorEllRe_of_mem hT hB T hx]; exact continuousOn_mEll hT hB N _ T)
    (fun x hx N => by rw [mirrorEllIm_of_mem hT hB T hx]; exact continuousOn_mEll hT hB N _ T)
    (fun x hx N => by rw [mirrorEllRe'_of_mem hT hB T hx]; exact continuousOn_mEll' hT hB N _ T)
    (fun x hx N => by rw [mirrorEllIm'_of_mem hT hB T hx]; exact continuousOn_mEll' hT hB N _ T)
    (fun x hx N t ht => by
      rw [mirrorEllRe_of_mem hT hB T hx, mirrorEllRe'_of_mem hT hB T hx]
      exact hasDerivWithinAt_mEll hT hB N _ ht)
    (fun x hx N t ht => by
      rw [mirrorEllIm_of_mem hT hB T hx, mirrorEllIm'_of_mem hT hB T hx]
      exact hasDerivWithinAt_mEll hT hB N _ ht)

set_option maxHeartbeats 2000000 in
/-- **The consistency defect of the elliptic comparison** is bounded by the projection errors of
the real and imaginary parts and of their time derivatives. -/
theorem norm_mirrorEllCmp_defect_le (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(mirrorEllCmp hT hB T).defect x N t‖ ≤
      (ellErr' hT hB N (tsdDatumOf hx) T t + ellErr hT hB N (tsdDatumOf hx) T t) +
        (ellErr' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t +
          ellErr hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t) := by
  refine (ApproxFEEC.norm_complexifyCmp_defect_le (mirrorFEMReal hT hB) mulI mulI_mulI norm_mulI
    (adjoint_mirrorEmb_mulI hT hB) (inner_mirrorEmb_mulI hT hB) _ _ _ _ _ _ _ _ _ _ _ x N
    t).trans ?_
  rw [mirrorEllRe_of_mem hT hB T hx, mirrorEllIm_of_mem hT hB T hx,
    mirrorEllRe'_of_mem hT hB T hx, mirrorEllIm'_of_mem hT hB T hx]
  exact add_le_add (norm_mEll_defect_le hT hB N _ ht) (norm_mEll_defect_le hT hB N _ ht)

set_option maxHeartbeats 2000000 in
/-- **The approximation error of the elliptic comparison** is at most the projection errors of the
real and imaginary parts. -/
theorem norm_sub_mirrorEllCmp_le (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).incl N
      ((mirrorEllCmp hT hB T).p x N t)‖ ≤
      ellErr hT hB N (tsdDatumOf hx) T t + ellErr hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t := by
  have hyU : complexQℝ.waveGroup.S t x = (tsdDatumOf hx).U t := complexQℝ_waveGroup ht.1 x
  have hyU' : (tsdDatumOf (neg_I_smul_mem hx)).U t = -Complex.I • (tsdDatumOf hx).U t :=
    (complexQ.waveGroup.S t).map_smul (-Complex.I) x
  have e : (mirrorFEMApprox hT hB).incl N ((mirrorEllCmp hT hB T).p x N t) =
      mirrorReEmb (mirrorFE hT hB N (mEll hT hB N (tsdDatumOf hx) T t)) +
        Complex.I • mirrorReEmb (mirrorFE hT hB N
          (mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t)) := by
    have h : (mirrorFEMApprox hT hB).incl N ((mirrorEllCmp hT hB T).p x N t) =
        (mirrorFEMReal hT hB).incl N (mirrorEllRe hT hB T x N t) +
          mulI ((mirrorFEMReal hT hB).incl N (mirrorEllIm hT hB T x N t)) := rfl
    rw [mirrorEllRe_of_mem hT hB T hx, mirrorEllIm_of_mem hT hB T hx] at h
    exact h
  have key := norm_sub_mirrorReEmb_le ((tsdDatumOf hx).U_tsd t)
    (mirrorFE hT hB N (mEll hT hB N (tsdDatumOf hx) T t))
    (mirrorFE hT hB N (mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t))
  have h1 := tsdErr_mEll hT hB N (tsdDatumOf hx) ht
  have h2 := (congrArg (fun y => tsdErr y (mirrorFE hT hB N
    (mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t))) hyU').symm.trans
      (tsdErr_mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) ht)
  have hz : complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).incl N
      ((mirrorEllCmp hT hB T).p x N t) =
        (tsdDatumOf hx).U t - mirrorReEmb (mirrorFE hT hB N (mEll hT hB N (tsdDatumOf hx) T t)) -
          Complex.I • mirrorReEmb (mirrorFE hT hB N
            (mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t)) :=
    (congrArg₂ (· - ·) hyU e).trans (sub_add_eq_sub_sub _ _ _)
  exact (congrArg norm hz).trans_le (key.trans_eq (congrArg₂ (· + ·) h1 h2))

/-! ### Smallness of the projection errors -/

/-- The Strang constant `√(2 (C_p + 1))` of the mirror data. -/
abbrev mirrorStrangK : ℝ := √(2 * (strangConst (2 * Real.pi)⁻¹ + 1))

theorem mirrorStrangK_nonneg : 0 ≤ mirrorStrangK := Real.sqrt_nonneg _

set_option maxHeartbeats 2000000 in
/-- **The projection errors of a TSD datum tend to `0` uniformly on `[0, T]`** (the parity-smoothed
projections converge on the compact trajectories, `eventually_mirrorClose`; `K₀ = K₁ = 0` for TSD
data). -/
theorem eventually_ellErr_le (D : TSDDatum) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, ellErr hT hB N D T t ≤ ε ∧ ellErr' hT hB N D T t ≤ ε := by
  set s := D.exactWave (T + 1)
  have hmc := mirrorCloseConst_nonneg C
  have hK := mirrorStrangK_nonneg
  set θ := ε / (mirrorStrangK * √(mirrorCloseConst C) + 1) with hθ
  have hden : 0 < mirrorStrangK * √(mirrorCloseConst C) + 1 := by positivity
  have hθ0 : 0 < θ := div_pos hε hden
  have hθε : mirrorStrangK * (√(mirrorCloseConst C) * θ) ≤ ε := by
    have e : θ * (mirrorStrangK * √(mirrorCloseConst C) + 1) = ε := div_mul_cancel₀ _ hden.ne'
    nlinarith [Real.sqrt_nonneg (mirrorCloseConst C)]
  have ev3 := eventually_mirrorClose hT hB (σ := s.σ) (φ := s.φ) (u := s.u) (M := s.M)
    (ρ' := s.ρ) s.cσ s.cdφ s.cu s.cdu s.cM s.cρ s.cSu hθ0
  have ev4 := eventually_mirrorClose hT hB (σ := s.σ') (φ := s.φ') (u := s.u') (M := s.M')
    (ρ' := s.ρ') s.cσ' s.cdφ' s.cu' s.cdu' s.cM' s.cρ' s.cSu' hθ0
  filter_upwards [ev3, ev4] with N h3 h4 t ht
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  have hdat : ∀ x : ℝ, x ≤ mirrorCloseConst C * θ ^ 2 + 0 ^ 2 + 0 ^ 2 →
      x ≤ (√(mirrorCloseConst C) * θ) ^ 2 := fun x hx => by
    rw [mul_pow, Real.sq_sqrt hmc]; simpa using hx
  have habs : |√(mirrorCloseConst C) * θ| = √(mirrorCloseConst C) * θ :=
    abs_of_nonneg (by positivity)
  have hb : √(2 * (strangConst (2 * Real.pi)⁻¹ + 1)) * |√(mirrorCloseConst C) * θ| ≤ ε := by
    rw [habs]; exact hθε
  refine ⟨?_, ?_⟩
  · have h := norm_sub_ellTraj_le (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) mirror_harmonicStability (mirrorFEM_compatible hT hB N)
      s (hg_mirror (T + 1)) (Icc_sub_Ico_add_one ht) (D.ell_S0_le_zero hT hB (T + 1) N t ht')
      (D.inner_M_S1_le_zero hT hB (T + 1) N t ht')
      (hdat _ (mirrorFEM_strangData_le_of_close hT hB N (h3 t ht') 0 0))
    with_reducible_and_instances exact h.trans hb
  · have h := norm_sub_ellTraj'_le (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) mirror_harmonicStability (mirrorFEM_compatible hT hB N)
      s (hg_mirror (T + 1)) (Icc_sub_Ico_add_one ht) (D.ell'_S0_le_zero hT hB (T + 1) N t ht')
      (D.inner_M'_S1_le_zero hT hB (T + 1) N t ht')
      (hdat _ (mirrorFEM_strangData_le_of_close hT hB N (h4 t ht') 0 0))
    with_reducible_and_instances exact h.trans hb

/-! ### The elliptic core -/

set_option maxHeartbeats 4000000 in
/-- **The elliptic core of the mirror scheme**: TSD data of `D(L²)`, with the elliptic projection
(6.4) of the exact solution as comparison trajectory (its consistency defect is bounded, not
shown to be nonzero). Its
two hypotheses (uniform approximation and uniform consistency) are discharged by the Strang bound
of (6.4) and the convergence of the parity-smoothed projections; no convergence theorem of the
scheme is used. -/
def mirrorEllCore : (mirrorFEMApprox hT hB).Core where
  Data := mirrorEllData
  cmp T := mirrorEllCmp hT hB T
  data_eq _ := rfl
  tendsto_approx T x hx := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_ellErr_le hT hB (tsdDatumOf hx) T (half_pos (half_pos hε)),
      eventually_ellErr_le hT hB (tsdDatumOf (neg_I_smul_mem hx)) T (half_pos (half_pos hε))]
      with N h1 h2 t ht
    rw [dist_eq_norm]
    have := norm_sub_mirrorEllCmp_le hT hB T hx N ht
    linarith [(h1 t ht).1, (h2 t ht).1]
  tendsto_defect T x hx := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε8 : 0 < ε / 8 := by positivity
    filter_upwards [eventually_ellErr_le hT hB (tsdDatumOf hx) T hε8,
      eventually_ellErr_le hT hB (tsdDatumOf (neg_I_smul_mem hx)) T hε8] with N h1 h2 t ht
    rw [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have := norm_mirrorEllCmp_defect_le hT hB T hx N ht
    linarith [(h1 t ht).1, (h1 t ht).2, (h2 t ht).1, (h2 t ht).2]

theorem mirrorEllCore_data : (mirrorEllCore hT hB).Data = tsdQℝ ⊓ complexQℝ.wave.domainSq := rfl

theorem mirrorEllCore_closure : (mirrorEllCore hT hB).Data.topologicalClosure = tsdQℝ :=
  topologicalClosure_tsdQℝ_inf_domainSq

/-- **The mirror scheme (6.5) is an instance of the approximating FEEC theorem with the elliptic
core**: convergence from best approximation plus consistency. -/
theorem einsteinBianchi_mirrorFEM_approxFEEC_elliptic :
    (mirrorFEMApprox hT hB).Verdict (mirrorEllCore hT hB) :=
  approxFEEC _ _

/-! ### Rates -/

/-- The rate constant `√(2 (C_p + 1)) · √(closeConst) · sobConst` of the elliptic projection. -/
abbrev mirrorEllK : ℝ := mirrorStrangK * √(mirrorCloseConst C) * mirrorSobConst C

include hT in
theorem mirrorEllK_nonneg : 0 ≤ mirrorEllK (C := C) := by
  have := mirrorSobConst_nonneg hT.two_mul_nonneg
  have := mirrorStrangK_nonneg
  positivity

set_option maxHeartbeats 2000000 in
/-- **The projection errors are `O(hˢ)`** for a TSD datum with `U₀`, `LU₀`, `L²U₀` in `Hˢ`
(`TSDDatum.strangData_le`, `K₀ = K₁ = 0`), uniformly on `[0, T]`. -/
theorem ellErr_le_sobolev (D : TSDDatum) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h0 : MemSobState s D.U₀) (h1 : MemSobState s D.LU₀) (h2 : MemSobState s D.LLU₀) (N : ℕ)
    {T t : ℝ} (ht : t ∈ Icc 0 T) :
    ellErr hT hB N D T t ≤ mirrorEllK (C := C) * meshSize N ^ s * D.sobSize s ∧
      ellErr' hT hB N D T t ≤ mirrorEllK (C := C) * meshSize N ^ s * D.sobSize s := by
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  have hd := D.strangData_le hT hB hs0 hs1 N h0 h1 h2 (T + 1)
  have hc : 0 ≤ √(mirrorCloseConst C) * (mirrorSobConst C * meshSize N ^ s * D.sobSize s) * 1 := by
    have := mirrorSobConst_nonneg hT.two_mul_nonneg
    have := D.sobSize_nonneg s
    have := Real.rpow_nonneg (meshSize_pos N).le s
    positivity
  have hb : √(2 * (strangConst (2 * Real.pi)⁻¹ + 1)) *
      |√(mirrorCloseConst C) * (mirrorSobConst C * meshSize N ^ s * D.sobSize s) * 1| =
        mirrorEllK (C := C) * meshSize N ^ s * D.sobSize s := by
    rw [abs_of_nonneg hc]; ring
  refine ⟨?_, ?_⟩
  · have h := norm_sub_ellTraj_le (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) mirror_harmonicStability (mirrorFEM_compatible hT hB N)
      (D.exactWave (T + 1)) (hg_mirror (T + 1)) (Icc_sub_Ico_add_one ht)
      (D.ell_S0_le_zero hT hB (T + 1) N t ht') (D.inner_M_S1_le_zero hT hB (T + 1) N t ht')
      (hd.1 t ht')
    with_reducible_and_instances exact h.trans_eq hb
  · have h := norm_sub_ellTraj'_le (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) mirror_harmonicStability (mirrorFEM_compatible hT hB N)
      (D.exactWave (T + 1)) (hg_mirror (T + 1)) (Icc_sub_Ico_add_one ht)
      (D.ell'_S0_le_zero hT hB (T + 1) N t ht') (D.inner_M'_S1_le_zero hT hB (T + 1) N t ht')
      (hd.2 t ht')
    with_reducible_and_instances exact h.trans_eq hb

theorem tsdDatumOf_negI_U₀ {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) :
    (tsdDatumOf (neg_I_smul_mem hx)).U₀ = -Complex.I • x := rfl

/-- The Sobolev sizes of the real and imaginary parts of an `H^{2+s}` datum. -/
theorem sobSize_le_of_mem {s : ℝ} {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) :
    (MemSobState s (tsdDatumOf hx.1).U₀ ∧ MemSobState s (tsdDatumOf hx.1).LU₀ ∧
      MemSobState s (tsdDatumOf hx.1).LLU₀ ∧
      (tsdDatumOf hx.1).sobSize s ≤ 3 * √(sobState (2 + s) x)) ∧
    (MemSobState s (tsdDatumOf (neg_I_smul_mem hx.1)).U₀ ∧
      MemSobState s (tsdDatumOf (neg_I_smul_mem hx.1)).LU₀ ∧
      MemSobState s (tsdDatumOf (neg_I_smul_mem hx.1)).LLU₀ ∧
      (tsdDatumOf (neg_I_smul_mem hx.1)).sobSize s ≤ 3 * √(sobState (2 + s) x)) := by
  refine ⟨(tsdDatumOf hx.1).memSobState_of_add_two hx.2, ?_⟩
  obtain ⟨c0, c1, c2, c3⟩ := (tsdDatumOf (neg_I_smul_mem hx.1)).memSobState_of_add_two
    (memSobState_negI hx.2)
  refine ⟨c0, c1, c2, c3.trans_eq ?_⟩
  rw [tsdDatumOf_negI_U₀ hx.1, sobState_negI]

set_option maxHeartbeats 2000000 in
/-- **The elliptic rate class of order `s ∈ [0, 1]`** of the mirror scheme: TSD data with mirror
extension in `H^{2+s}`, norm `‖ξ₀‖_{2+s}`, approximation constant `C = 6K` and consistency
constant `C' = 12K` (`K = mirrorEllK`), independent of `T`. -/
def mirrorEllRateSobolev (T s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (mirrorFEMApprox hT hB).RateClass T where
  toComparison := (mirrorEllCmp hT hB T).restrict (mirrorSobData s) fun _ hx => hx.1
  classNorm x := √(sobState (2 + s) x)
  meshSize := meshSize
  α := s
  C := 6 * mirrorEllK (C := C)
  C' := 12 * mirrorEllK (C := C)
  approx x hx N t ht := by
    obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := sobSize_le_of_mem hx
    have e1 := (ellErr_le_sobolev hT hB _ hs0 hs1 a0 a1 a2 N ht).1
    have e2 := (ellErr_le_sobolev hT hB _ hs0 hs1 b0 b1 b2 N ht).1
    have hK := mirrorEllK_nonneg hT (C := C)
    have hm := Real.rpow_nonneg (meshSize_pos N).le s
    have f1 := mul_le_mul_of_nonneg_left a3 (mul_nonneg hK hm)
    have f2 := mul_le_mul_of_nonneg_left b3 (mul_nonneg hK hm)
    refine (norm_sub_mirrorEllCmp_le hT hB T hx.1 N ht).trans ?_
    change _ ≤ 6 * mirrorEllK (C := C) * meshSize N ^ s * √(sobState (2 + s) x)
    nlinarith
  consistency x hx N t ht := by
    obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := sobSize_le_of_mem hx
    have e1 := ellErr_le_sobolev hT hB _ hs0 hs1 a0 a1 a2 N ht
    have e2 := ellErr_le_sobolev hT hB _ hs0 hs1 b0 b1 b2 N ht
    have hK := mirrorEllK_nonneg hT (C := C)
    have hm := Real.rpow_nonneg (meshSize_pos N).le s
    have f1 := mul_le_mul_of_nonneg_left a3 (mul_nonneg hK hm)
    have f2 := mul_le_mul_of_nonneg_left b3 (mul_nonneg hK hm)
    refine (norm_mirrorEllCmp_defect_le hT hB T hx.1 N ht).trans ?_
    change _ ≤ 12 * mirrorEllK (C := C) * meshSize N ^ s * √(sobState (2 + s) x)
    nlinarith [e1.1, e1.2, e2.1, e2.2]

theorem mirrorEllRateSobolev_data (T s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (mirrorEllRateSobolev hT hB T s hs0 hs1).Data = mirrorSobData s := rfl

theorem mirrorEllRateSobolev_C' (T s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (mirrorEllRateSobolev hT hB T s hs0 hs1).C' = 12 * mirrorEllK (C := C) := rfl

/-- The data of `mirrorL3Data` have `U₀`, `LU₀`, `L²U₀` in `H¹` with
`‖·‖_1 + ‖L·‖_1 + ‖L²·‖_1 ≤ 2 ‖ξ₀‖_{L³}`, for the real and imaginary parts. -/
theorem sobSize_le_of_mem_l3 {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorL3Data) :
    (MemSobState 1 (tsdDatumOf hx.1).U₀ ∧ MemSobState 1 (tsdDatumOf hx.1).LU₀ ∧
      MemSobState 1 (tsdDatumOf hx.1).LLU₀ ∧
      (tsdDatumOf hx.1).sobSize 1 ≤ 2 * mirrorL3Norm x) ∧
    (MemSobState 1 (tsdDatumOf (neg_I_smul_mem hx.1)).U₀ ∧
      MemSobState 1 (tsdDatumOf (neg_I_smul_mem hx.1)).LU₀ ∧
      MemSobState 1 (tsdDatumOf (neg_I_smul_mem hx.1)).LLU₀ ∧
      (tsdDatumOf (neg_I_smul_mem hx.1)).sobSize 1 ≤ 2 * mirrorL3Norm x) := by
  obtain ⟨hx1, h3⟩ := hx
  have hN := mirrorL3Norm_of_mem hx1 h3
  have a := (tsdDatumOf hx1).memSobState_one h3
  have b := (tsdDatumOf (neg_I_smul_mem hx1)).memSobState_one (mem_LLU₀_negI hx1 h3)
  have hb := l3Norm_negI hx1 h3
  unfold l3Norm at hb hN
  rw [hN]
  refine ⟨⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩, ⟨b.1, b.2.1, b.2.2.1, b.2.2.2.trans_eq ?_⟩⟩
  rw [hb]

set_option maxHeartbeats 2000000 in
/-- **The elliptic rate class of order `1`** of the mirror scheme: TSD data of `D(L³)`, norm
`‖ξ₀‖ + ‖Lξ₀‖ + ‖L²ξ₀‖ + ‖L³ξ₀‖`, `C = 4K`, `C' = 8K`, independent of `T`. -/
def mirrorEllRate (T : ℝ) : (mirrorFEMApprox hT hB).RateClass T where
  toComparison := (mirrorEllCmp hT hB T).restrict mirrorL3Data fun _ hx => hx.1
  classNorm := mirrorL3Norm
  meshSize := meshSize
  α := 1
  C := 4 * mirrorEllK (C := C)
  C' := 8 * mirrorEllK (C := C)
  approx x hx N t ht := by
    obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := sobSize_le_of_mem_l3 hx
    have e1 := (ellErr_le_sobolev hT hB _ zero_le_one le_rfl a0 a1 a2 N ht).1
    have e2 := (ellErr_le_sobolev hT hB _ zero_le_one le_rfl b0 b1 b2 N ht).1
    have hK := mirrorEllK_nonneg hT (C := C)
    have hm := Real.rpow_nonneg (meshSize_pos N).le (1 : ℝ)
    have f1 := mul_le_mul_of_nonneg_left a3 (mul_nonneg hK hm)
    have f2 := mul_le_mul_of_nonneg_left b3 (mul_nonneg hK hm)
    refine (norm_sub_mirrorEllCmp_le hT hB T hx.1 N ht).trans ?_
    change _ ≤ 4 * mirrorEllK (C := C) * meshSize N ^ (1 : ℝ) * mirrorL3Norm x
    nlinarith
  consistency x hx N t ht := by
    obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := sobSize_le_of_mem_l3 hx
    have e1 := ellErr_le_sobolev hT hB _ zero_le_one le_rfl a0 a1 a2 N ht
    have e2 := ellErr_le_sobolev hT hB _ zero_le_one le_rfl b0 b1 b2 N ht
    have hK := mirrorEllK_nonneg hT (C := C)
    have hm := Real.rpow_nonneg (meshSize_pos N).le (1 : ℝ)
    have f1 := mul_le_mul_of_nonneg_left a3 (mul_nonneg hK hm)
    have f2 := mul_le_mul_of_nonneg_left b3 (mul_nonneg hK hm)
    refine (norm_mirrorEllCmp_defect_le hT hB T hx.1 N ht).trans ?_
    change _ ≤ 8 * mirrorEllK (C := C) * meshSize N ^ (1 : ℝ) * mirrorL3Norm x
    nlinarith [e1.1, e1.2, e2.1, e2.2]

theorem mirrorEllRate_data (T : ℝ) : (mirrorEllRate hT hB T).Data = mirrorL3Data := rfl

theorem mirrorEllRate_C' (T : ℝ) : (mirrorEllRate hT hB T).C' = 8 * mirrorEllK (C := C) := rfl

/-! ### The verdict with the elliptic initialization (6.4) -/

set_option maxHeartbeats 1000000 in
/-- **The comparison initial value is the elliptic projection (6.4) of the exact initial state**,
the initialization of the thesis' scheme (and of `mirror_waveFEM`): for each real part, the
energy state of `Πₕ(0)` is the dynamic part of the elliptic projection of the data
`((D.exactWave T).σ 0, …, (D.exactWave T).ℓ 0)`. -/
theorem mEll_zero_toEState (N : ℕ) (D : TSDDatum) {T : ℝ} (hT0 : 0 ≤ T) :
    (mEll hT hB N D T 0).toEState = EState.mkL (Feec.BGG.ellipticProjection (mirrorWave hT hB N)
      (mirrorWave_dt0_injective hT hB N)
      (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
      (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH ((D.exactWave T).σ 0)
        ((D.exactWave T).φ 0) ((D.exactWave T).u 0) ((D.exactWave T).M 0) ((D.exactWave T).ρ 0)
        ((D.exactWave T).ℓ 0)) 0)).1.1 :=
  toEState_ellTraj (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
    (mirrorWave_S0_surjective hT hB N) (D.exactWave (T + 1)) (hg_mirror (T + 1))
    ⟨le_rfl, by linarith⟩

/-- The comparison initial value of a datum: the elliptic projections of its real and imaginary
parts. -/
theorem mirrorEllCmp_p_zero (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ) :
    (mirrorEllCmp hT hB T).p x N 0 = WithLp.toLp 2 (mEll hT hB N (tsdDatumOf hx) T 0,
      mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T 0) := by
  change WithLp.toLp 2 (mirrorEllRe hT hB T x N 0, mirrorEllIm hT hB T x N 0) = _
  rw [mirrorEllRe_of_mem hT hB T hx, mirrorEllIm_of_mem hT hB T hx]
  rfl

/-- **The elliptic trajectory does not depend on the horizon**: the exact TSD solution
`D.exactWave T` has the same fields for every `T` (only its proofs depend on `T`). -/
theorem mEll_horizon (N : ℕ) (D : TSDDatum) (T T' t : ℝ) :
    mEll hT hB N D T t = mEll hT hB N D T' t := rfl

theorem mirrorEllRe_horizon (T T' : ℝ) (x : PiLp 2 SpaceQ) (N : ℕ) (t : ℝ) :
    mirrorEllRe hT hB T x N t = mirrorEllRe hT hB T' x N t := rfl

theorem mirrorEllIm_horizon (T T' : ℝ) (x : PiLp 2 SpaceQ) (N : ℕ) (t : ℝ) :
    mirrorEllIm hT hB T x N t = mirrorEllIm hT hB T' x N t := rfl

/-- **The comparison trajectory does not depend on the horizon.** -/
theorem mirrorEllCmp_p_horizon (T T' : ℝ) (x : PiLp 2 SpaceQ) (N : ℕ) (t : ℝ) :
    (mirrorEllCmp hT hB T).p x N t = (mirrorEllCmp hT hB T').p x N t := by
  change WithLp.toLp 2 (mirrorEllRe hT hB T x N t, mirrorEllIm hT hB T x N t) =
    WithLp.toLp 2 (mirrorEllRe hT hB T' x N t, mirrorEllIm hT hB T' x N t)
  rw [mirrorEllRe_horizon hT hB T T', mirrorEllIm_horizon hT hB T T']

/-- **The thesis' initialization (6.4) of a datum**, independent of the horizon: the pair of
elliptic projections of the real and imaginary parts of the exact initial state
(`mirrorEllInit_of_mem`, `mEll_zero_toEState`). -/
def mirrorEllInit (x : PiLp 2 SpaceQ) (N : ℕ) : (mirrorFEMApprox hT hB).X N :=
  (mirrorEllCmp hT hB 0).p x N 0

theorem mirrorEllCmp_p_zero_eq_init (T : ℝ) (x : PiLp 2 SpaceQ) (N : ℕ) :
    (mirrorEllCmp hT hB T).p x N 0 = mirrorEllInit hT hB x N :=
  mirrorEllCmp_p_horizon hT hB T 0 x N 0

theorem mirrorEllInit_of_mem {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ) :
    mirrorEllInit hT hB x N = WithLp.toLp 2 (mEll hT hB N (tsdDatumOf hx) 0 0,
      mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) 0 0) :=
  mirrorEllCmp_p_zero hT hB 0 hx N

set_option maxHeartbeats 1000000 in
/-- **The `O(h)` rate of the mirror scheme (6.5) from the elliptic projection (6.4)**, for TSD data
of `D(L³)` (item 3c of the verdict for `mirrorEllRate`, initial value `Πₕ(0)`):
`‖e^{tL} ξ₀ - ι' e^{tL'} Πₕ(0)‖ ≤ (4K + 8K t) h_N ‖ξ₀‖_{L³}` on `[0, T]`, `K = mirrorEllK`,
independent of `T` (cf. `K L (1 + t) h_N` of
`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`). -/
theorem einsteinBianchi_mirrorFEM_rate_elliptic {T : ℝ} {x : PiLp 2 SpaceQ}
    (hx : x ∈ mirrorL3Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x -
        (mirrorFEMApprox hT hB).sol N ((mirrorEllCmp hT hB T).p x N 0) t‖ ≤
      (4 * mirrorEllK (C := C) + 8 * mirrorEllK (C := C) * t) *
        (meshSize N * mirrorL3Norm x) := by
  have h := approxFEEC_rate (mirrorFEMApprox hT hB) (mirrorEllRate hT hB T) hx N
    ((mirrorEllCmp hT hB T).p x N 0) ht
  have hι := (mirrorFEMApprox_isOrthogonal hT hB).norm_incl_le_one N
  have hp : (mirrorEllRate hT hB T).p x N 0 = (mirrorEllCmp hT hB T).p x N 0 := rfl
  rw [hp, sub_self, norm_zero, mul_zero, add_zero] at h
  have hm : (mirrorEllRate hT hB T).meshSize N ^ (mirrorEllRate hT hB T).α *
      (mirrorEllRate hT hB T).classNorm x = meshSize N * mirrorL3Norm x := by
    change meshSize N ^ (1 : ℝ) * mirrorL3Norm x = _
    rw [Real.rpow_one]
  have hC : (mirrorEllRate hT hB T).C = 4 * mirrorEllK (C := C) := rfl
  have hC' : (mirrorEllRate hT hB T).C' = 8 * mirrorEllK (C := C) := rfl
  rw [hm, hC, hC'] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg (meshSize_pos N).le ?_))
  · have hK := mirrorEllK_nonneg hT (C := C)
    have h8 : 0 ≤ 8 * mirrorEllK (C := C) * t := by have := ht.1; positivity
    nlinarith [mul_le_of_le_one_left h8 hι]
  · obtain ⟨hx1, h3⟩ := hx
    rw [mirrorL3Norm_of_mem hx1 h3]
    exact l3Norm_nonneg _ _

set_option maxHeartbeats 1000000 in
/-- **The `O(hˢ)` rate of the mirror scheme (6.5) from the elliptic projection (6.4)**, for TSD data
in `H^{2+s}`, `0 ≤ s ≤ 1`: `‖e^{tL} ξ₀ - ι' e^{tL'} Πₕ(0)‖ ≤ (6K + 12K t) h_Nˢ ‖ξ₀‖_{2+s}`. -/
theorem einsteinBianchi_mirrorFEM_rate_sobolev_elliptic {T s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x -
        (mirrorFEMApprox hT hB).sol N ((mirrorEllCmp hT hB T).p x N 0) t‖ ≤
      (6 * mirrorEllK (C := C) + 12 * mirrorEllK (C := C) * t) *
        (meshSize N ^ s * √(sobState (2 + s) x)) := by
  have h := approxFEEC_rate (mirrorFEMApprox hT hB) (mirrorEllRateSobolev hT hB T s hs0 hs1) hx N
    ((mirrorEllCmp hT hB T).p x N 0) ht
  have hι := (mirrorFEMApprox_isOrthogonal hT hB).norm_incl_le_one N
  have hp : (mirrorEllRateSobolev hT hB T s hs0 hs1).p x N 0 =
      (mirrorEllCmp hT hB T).p x N 0 := rfl
  rw [hp, sub_self, norm_zero, mul_zero, add_zero] at h
  have hm : (mirrorEllRateSobolev hT hB T s hs0 hs1).meshSize N ^
      (mirrorEllRateSobolev hT hB T s hs0 hs1).α *
      (mirrorEllRateSobolev hT hB T s hs0 hs1).classNorm x =
        meshSize N ^ s * √(sobState (2 + s) x) := rfl
  have hC : (mirrorEllRateSobolev hT hB T s hs0 hs1).C = 6 * mirrorEllK (C := C) := rfl
  have hC' : (mirrorEllRateSobolev hT hB T s hs0 hs1).C' = 12 * mirrorEllK (C := C) := rfl
  rw [hm, hC, hC'] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (Real.rpow_nonneg (meshSize_pos N).le s) (Real.sqrt_nonneg _)))
  have hK := mirrorEllK_nonneg hT (C := C)
  have h12 : 0 ≤ 12 * mirrorEllK (C := C) * t := by have := ht.1; positivity
  nlinarith [mul_le_of_le_one_left h12 hι]

/-- **The `O(h)` rate from the thesis' initialization, for all `t ≥ 0`** (horizon-free form of
`einsteinBianchi_mirrorFEM_rate_elliptic`, with `T = t`):
`‖e^{tL} ξ₀ - ι' e^{tL'} Πₕ(0)‖ ≤ (4K + 8K t) h_N ‖ξ₀‖_{L³}` for TSD data of `D(L³)`. -/
theorem einsteinBianchi_mirrorFEM_rate_init {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorL3Data) (N : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
      (4 * mirrorEllK (C := C) + 8 * mirrorEllK (C := C) * t) *
        (meshSize N * mirrorL3Norm x) := by
  rw [← mirrorEllCmp_p_zero_eq_init hT hB t]
  exact einsteinBianchi_mirrorFEM_rate_elliptic hT hB hx N ⟨ht, le_rfl⟩

/-- **The `O(hˢ)` rate from the thesis' initialization, for all `t ≥ 0`** (horizon-free form of
`einsteinBianchi_mirrorFEM_rate_sobolev_elliptic`). -/
theorem einsteinBianchi_mirrorFEM_rate_sobolev_init {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
      (6 * mirrorEllK (C := C) + 12 * mirrorEllK (C := C) * t) *
        (meshSize N ^ s * √(sobState (2 + s) x)) := by
  rw [← mirrorEllCmp_p_zero_eq_init hT hB t]
  exact einsteinBianchi_mirrorFEM_rate_sobolev_elliptic hT hB hs0 hs1 hx N ⟨ht, le_rfl⟩

end Feec.Instances.EinsteinBianchi.FEM
