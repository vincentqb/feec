module

public import Feec.Instances.EinsteinBianchiFEM
public import Feec.HilbertComplex.Approximation.ApproxComplexCrime

/-!
# The scheme (6.5) through the complex-level front end

The source-free scheme (6.3)/(6.5) of [QuennevilleBelair2015], §6.2–6.3, written on the
hidden-constraint space with the skew generator `Lₕ = waveGen` (`Feec.Instances.EinsteinBianchiFEMGenerator`),
is the Hodge wave operator of a **discrete differential space**: `Lₕ = 𝐝ₕ - 𝐝ₕ*`
(`waveGen_eq_diffWave`) for the discrete BGG differential
`𝐝ₕ (σ, u, M, ρ) = (0, -d̃ Φ(σ, 0), S₁,ₕ u, d̃ u)` (`diffGen`; `𝐝ₕ 𝐝ₕ = 0`, `diffGen_diffGen`,
from `S₁,ₕ d̃ = -d S₀,ₕ`, `S₀,ₕ Φ(σ, 0) = dσ`, `d d = 0` and `d̃ d̃ = 0`). Its first differential
uses `S₀,ₕ = π¹S⁰`, which differs from `S⁰` in general; the reading maps of (6.5) are not shown to
be cochain maps, and (6.5) is not formalized as an instance of
`Feec.HilbertComplex.ApproxFEEC.ofComplex`. It is formalized as an instance of the generalized
front end `Feec.HilbertComplex.ApproxFEEC.ofComplexCrime`, through
`Feec.HilbertComplex.ApproxComplexCrime.ofGalerkinCore`: the elliptic projection (6.4) of the exact
solution is a Galerkin projection, `(1 - Lₕ) Πₕ(t) = ιₕ* (1 - L) ξ(t)` (`mEll_galerkin`,
`cEll_galerkin`, from `inner_ellDefect` and the identification of the continuous forms state with
the read state), so it is the approximant of the consistent-approximation hypothesis (residual
`0`), and its convergence is the Strang bound of (6.4) with the weak consistency constants
`K₀`, `K₁` (`Feec.Instances.EinsteinBianchi.FEM.norm_sub_ellTraj_le`). The cochain defect of
(6.5) is not computed here: it is absorbed by the Galerkin identity (it is computed in
`Feec.Instances.EinsteinBianchiFEMDefect`, where it is the pair of consistency functionals of the
Strang bound and vanishes on TSD states for mirror boundary conditions). `ofGalerkinCore` takes the existing
elliptic cores of `Feec.Instances.EinsteinBianchiFEM` as input, so the convergence verdicts below
re-derive, through the complex-level theorem, verdicts already proved there; what is new is the
discrete differential, the complex-level form of the scheme, the exactly preserved discrete
constraint and the rates through `Feec.HilbertComplex.ApproxComplexCrime.rateClass`.

* **Mirror boundary conditions** (`mirrorComplex`, on `complexQℝ`, constraint `tsdQℝ`):
  `einsteinBianchi_mirrorFEM_ofComplexCrime`: the verdict of the complex-level theorem; the
  discrete solutions are those of `mirrorFEMApprox` (the scheme (6.5)); the closure of the core
  is `tsdQℝ`, so the discrete solutions converge to the TSD solution and the residual tends to
  `0`. Rates (`mirrorComplexRate`, `mirrorComplexRateSobolev`): `O(h)` for TSD data of `D(L³)`
  and `O(hˢ)` for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1`, from the complex-level rate constructor
  `Feec.HilbertComplex.ApproxComplexCrime.rateClass`
  (`einsteinBianchi_mirrorFEM_ofComplexCrime_rate`, `_rate_sobolev`).
* **The thesis' boundary conditions** (`standardCubeComplex`, on `matrixComplex`, constraint
  `thesisTSD`): `einsteinBianchi_standardCube_ofComplexCrime`: the verdict; the discrete solutions
  are those of `standardCubeApprox`; the core is dense, so they converge for every datum, and at
  the explicit datum `(0, 0, (0, β))`, which lies in `thesisTSD`, the residuals tend to a positive
  limit: the limit leaves TSD.
* **Exactly preserved discrete constraints** (`hiddenGauss`): with `𝐝ₕ` identified, the discrete
  Gauss (divergence) constraint `σₕ = 0`, `uₕ ⊥ d̃ Φ(Vₕ⁰, 0)` (the degree-`0` component of
  `𝐝ₕ* x` vanishes), a discrete analogue of part of the TSD constraint, is invariant under
  `Lₕ` (`waveGen_mem_hiddenGauss`), hence preserved exactly by the discrete solutions of both
  instances (`mirrorFEM_preserves_hiddenGauss` on real and imaginary parts,
  `standardCube_preserves_hiddenGauss`). For the thesis' boundary conditions the discrete constraint
  is preserved exactly while the limit leaves `thesisTSD`. Neither `ιₕ(hiddenGauss) ⊆ tsdQℝ` nor
  `ιₕ(hiddenGauss) ⊆ thesisTSD` is shown, so the residual-`0` clause of the complex-level theorem
  is not used, and how `hiddenGauss`, read in `W`, sits relative to `thesisTSD` is not formalized.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.3), (6.4)), §6.3 ((6.5))
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (§3.3, Thm 3.10)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.HilbertComplex Feec.BGG

/-! ### The discrete BGG differential on the hidden space -/

section Diff

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  (D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2)
  [FiniteDimensional ℝ P1] [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1]
  (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)

/-- **The discrete BGG differential** on energy states:
`(σ, u, M, ρ) ↦ (0, -d̃ Φ(σ, 0), S₁ u, d̃ u)`, the "upper triangular" part of `waveOp`. -/
def diffOp : EState P0 Pt1 P2 Pt2 →ₗ[ℝ] EState P0 Pt1 P2 Pt2 where
  toFun x := EState.mk 0 (-D.dt0 (phi0 D hdinj hS x.σ)) (D.S1 x.u) (D.dt1 x.u)
  map_add' x y := by
    rw [← EState.mk_add]
    simp only [EState.u_add, EState.σ_add, map_add, add_zero, neg_add]
  map_smul' c x := by
    rw [RingHom.id_apply, ← EState.mk_smul]
    simp only [EState.u_smul, EState.σ_smul, map_smul, smul_neg, smul_zero]

@[simp] theorem diffOp_σ (x : EState P0 Pt1 P2 Pt2) : (diffOp D hdinj hS x).σ = 0 := rfl
@[simp] theorem diffOp_u (x : EState P0 Pt1 P2 Pt2) :
    (diffOp D hdinj hS x).u = -D.dt0 (phiMap D hdinj hS (x.σ, 0)) := rfl
@[simp] theorem diffOp_M (x : EState P0 Pt1 P2 Pt2) : (diffOp D hdinj hS x).M = D.S1 x.u := rfl
@[simp] theorem diffOp_ρ (x : EState P0 Pt1 P2 Pt2) : (diffOp D hdinj hS x).ρ = D.dt1 x.u := rfl

/-- `diffOp` maps into the hidden space: `d̃ Φ(σ, 0) ⊥ d̃ (ker S₀,ₕ)`. -/
theorem diffOp_mem_hiddenSpace (x : EState P0 Pt1 P2 Pt2) :
    diffOp D hdinj hS x ∈ hiddenSpace D := fun ψ hψ => by
  rw [diffOp_u, inner_neg_left, inner_phiMap hdinj hS _ hψ, inner_zero_left, neg_zero]

/-! #### The discrete Gauss constraint -/

/-- **The discrete Gauss (divergence) constraint** of the hidden space: `σ = 0` and
`u ⊥ d̃ Φ(Vₕ⁰, 0)` (the degree-`0` component of `𝐝ₕ* x` vanishes:
`⟪x, 𝐝ₕ (τ, 0, 0, 0)⟫ = -⟪u, d̃ Φ(τ, 0)⟫`). A discrete analogue of part of the TSD constraint;
that its image under the reading map lies in the continuous constraint is not shown. -/
def hiddenGauss : Submodule ℝ (HiddenState D) where
  carrier := {x | x.toEState.σ = 0 ∧ ∀ τ : P0, ⟪x.toEState.u, D.dt0 (phiMap D hdinj hS (τ, 0))⟫ = 0}
  add_mem' {x y} hx hy := ⟨by rw [HiddenState.toEState_add, EState.σ_add, hx.1, hy.1, add_zero],
    fun τ => by rw [HiddenState.toEState_add, EState.u_add, inner_add_left, hx.2 τ, hy.2 τ,
      add_zero]⟩
  zero_mem' := ⟨rfl, fun τ => by rw [HiddenState.toEState_zero, EState.u_zero, inner_zero_left]⟩
  smul_mem' c x hx := ⟨by rw [HiddenState.toEState_smul, EState.σ_smul, hx.1, smul_zero],
    fun τ => by rw [HiddenState.toEState_smul, EState.u_smul, real_inner_smul_left, hx.2 τ,
      mul_zero]⟩

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2]

/-- **The discrete differential `𝐝ₕ`** on the hidden space. -/
def diffGen : HiddenState D →L[ℝ] HiddenState D :=
  LinearMap.toContinuousLinearMap
    ((diffOp D hdinj hS).restrict (p := hiddenSpace D) (q := hiddenSpace D)
      fun x _ => diffOp_mem_hiddenSpace D hdinj hS x)

theorem diffGen_toEState (x : HiddenState D) :
    (diffGen D hdinj hS x).toEState = diffOp D hdinj hS x.toEState := rfl

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
/-- `S₁,ₕ d̃ Φ(σ, 0) = 0` (`S₁ d̃ = -d S₀`, `S₀ Φ(σ, 0) = dσ`, `d d = 0`). -/
theorem S1_dt0_phiMap (σ : P0) : D.S1 (D.dt0 (phiMap D hdinj hS (σ, 0))) = 0 := by
  have h := D.anticomm (phiMap D hdinj hS (σ, 0))
  rw [S0_phiMap hdinj hS, D.d1_d0] at h
  exact neg_eq_zero.1 h.symm

/-- **`𝐝ₕ 𝐝ₕ = 0`**: the hidden space with `𝐝ₕ` is a discrete differential space (from
`S₁,ₕ d̃ Φ(σ, 0) = 0` and `d̃ d̃ = 0`). -/
theorem diffGen_diffGen (x : HiddenState D) : diffGen D hdinj hS (diffGen D hdinj hS x) = 0 := by
  refine HiddenState.toEState_injective ?_
  rw [diffGen_toEState, diffGen_toEState, HiddenState.toEState_zero]
  refine EState.ext rfl ?_ ?_ ?_
  · change -D.dt0 (phiMap D hdinj hS ((0 : P0), (0 : Pt1))) = 0
    rw [show ((0 : P0), (0 : Pt1)) = 0 from rfl, map_zero, map_zero, neg_zero]
  · change D.S1 (-D.dt0 (phiMap D hdinj hS (x.toEState.σ, 0))) = 0
    rw [map_neg, S1_dt0_phiMap, neg_zero]
  · change D.dt1 (-D.dt0 (phiMap D hdinj hS (x.toEState.σ, 0))) = 0
    rw [map_neg, D.dt1_dt0, neg_zero]

theorem inner_diffGen (x y : HiddenState D) :
    ⟪diffGen D hdinj hS x, y⟫ = -⟪D.dt0 (phiMap D hdinj hS (x.toEState.σ, 0)), y.toEState.u⟫ +
      ⟪D.S1 x.toEState.u, y.toEState.M⟫ + ⟪D.dt1 x.toEState.u, y.toEState.ρ⟫ := by
  rw [← HiddenState.inner_toEState, diffGen_toEState, EState.inner_def, diffOp_σ, diffOp_u,
    diffOp_M, diffOp_ρ, inner_zero_left, zero_add, inner_neg_left]

/-- **The generator of (6.5) is the Hodge wave operator of `𝐝ₕ`**: `Lₕ = 𝐝ₕ - 𝐝ₕ*` on the
hidden space. -/
theorem waveGen_eq_diffWave : waveGen D hdinj hS = diffWave (diffGen D hdinj hS) := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
  rw [inner_diffWave, inner_diffGen, real_inner_comm (diffGen D hdinj hS y) x, inner_diffGen,
    ← HiddenState.inner_toEState, waveGen_toEState, inner_waveOp D hdinj hS x.toEState_mem]
  rw [real_inner_comm x.toEState.u (D.dt0 _), real_inner_comm x.toEState.M (D.S1 _),
    real_inner_comm x.toEState.ρ (D.dt1 _)]
  ring

/-- **The discrete Gauss constraint is invariant under the generator of (6.5)**: on it,
`(Lₕ x)_σ = d* λ(u) = 0` (`⟪λ(u), dτ⟫ = ⟪u, d̃ Φ(τ, 0)⟫`), and `(Lₕ x)_u = -S₁* M - d̃* ρ` is
orthogonal to `d̃ Φ(τ, 0)` (`S₁ d̃ Φ(τ, 0) = 0`, `d̃ d̃ = 0`). -/
theorem waveGen_mem_hiddenGauss {x : HiddenState D} (hx : x ∈ hiddenGauss D hdinj hS) :
    waveGen D hdinj hS x ∈ hiddenGauss D hdinj hS := by
  obtain ⟨h0, h1⟩ := hx
  refine ⟨?_, fun τ => ?_⟩
  · rw [waveGen_toEState, waveOp_σ]
    refine ext_inner_right ℝ fun τ => ?_
    rw [LinearMap.adjoint_inner_left, ← S0_phiMap hdinj hS (τ, (0 : Pt1)),
      ← LinearMap.adjoint_inner_left, adjoint_S0_lamMap D hS x.toEState_mem,
      LinearMap.adjoint_inner_left, h1 τ, inner_zero_left]
  · rw [waveGen_toEState, waveOp_u, h0, show ((0 : P0), (0 : Pt1)) = 0 from rfl, map_zero,
      map_zero, neg_zero, zero_sub, inner_sub_left, inner_neg_left,
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, S1_dt0_phiMap, D.dt1_dt0,
      inner_zero_right, inner_zero_right, neg_zero, sub_zero]

end Diff

/-! ### Pairs of subspaces (real and imaginary parts) -/

section Pair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pair of subspaces `K ⊕ K`. -/
def prodSub (K : Submodule ℝ E) : Submodule ℝ (WithLp 2 (E × E)) :=
  (K.prod K).comap (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap

end Pair

/-! ### Mirror boundary conditions -/

section Mirror

open Feec.Models.Cube.MirrorWeakSymmetry Feec.Models.Cube.RowWise
open Feec.Models.Cube.MirrorBGG (SpaceQ W2Q complexQ tsdQ)
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)
open Feec.Models.Cube.FEM (meshSize meshSize_pos)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

set_option maxHeartbeats 1000000 in
/-- **The difference `‖y - Rt a‖² - tsdErr(y, a)²` does not depend on `a`** for a TSD state `y`
(it is the energy of the imaginary part). -/
theorem norm_sq_sub_mirrorReEmb_sub_tsdErr {y : PiLp 2 SpaceQ} (hy : y ∈ totalSub tsdQ)
    (a a' : REnergy) :
    ‖y - mirrorReEmb a‖ ^ 2 - tsdErr y a ^ 2 = ‖y - mirrorReEmb a'‖ ^ 2 - tsdErr y a' ^ 2 := by
  obtain ⟨h0, -, hM, -⟩ := Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hy
  have e0 : slot0 y = 0 := h0
  have eM : slotM y = 0 := hM
  have h1 := norm_sq_sub_mirrorReEmb y a 0
  have h2 := norm_sq_sub_mirrorReEmb y a' 0
  simp only [map_zero, smul_zero, sub_zero] at h1 h2
  rw [e0, eM, map_zero, map_zero, zero_sub, zero_sub, norm_neg, norm_neg] at h1 h2
  have hA : tsdErr y a ^ 2 = ‖a.σ‖ ^ 2 + ‖rowsW1L (slot1 y) - a.u‖ ^ 2 + ‖a.M‖ ^ 2 +
      ‖rowsW2L (slotB y) - a.ρ‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hA' : tsdErr y a' ^ 2 = ‖a'.σ‖ ^ 2 + ‖rowsW1L (slot1 y) - a'.u‖ ^ 2 + ‖a'.M‖ ^ 2 +
      ‖rowsW2L (slotB y) - a'.ρ‖ ^ 2 := Real.sq_sqrt (by positivity)
  linarith

/-- **Polarization**: if `‖a - c‖² - ‖b - d‖²` is the same at `(c, d)` and at `(0, 0)` and
`‖c‖ = ‖d‖`, then `⟪a, c⟫ = ⟪b, d⟫`. -/
theorem real_inner_eq_of_norm {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {a c : E} {b d : E'} (hcd : ‖c‖ = ‖d‖)
    (h : ‖a - c‖ ^ 2 - ‖b - d‖ ^ 2 = ‖a‖ ^ 2 - ‖b‖ ^ 2) : ⟪a, c⟫_ℝ = ⟪b, d⟫_ℝ := by
  have e1 := norm_sub_sq_real a c
  have e2 := norm_sub_sq_real b d
  rw [hcd] at e1
  linarith

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
    Feec.FiniteElement.PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3,
    Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a} Feec.FiniteElement.PolySeq.lagrangeP2 ρ C)

set_option maxHeartbeats 1000000 in
/-- The four-term error of a discrete energy state against the time derivative of a TSD solution
is its energy error against `ξ'` (the time-derivative analogue of `tsdErr_eq`). -/
theorem tsdErr_eq' (N : ℕ) (D : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T)
    (p : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h (mirrorFEM hT hB N).W2h
      (mirrorFEM hT hB N).Wt2h) :
    tsdErr (D.V t) (EState.mk ((p.σ : TU0) : W0) (bIncl1 (p.u : BU1)) (p.M : W2) (p.ρ : Wv W2)) =
      ‖exState' (D.exactWave T) t - coeH (mirrorFEM hT hB N) p‖ := by
  have h1 := (Real.sqrt_sq (norm_nonneg
    (exState' (D.exactWave T) t - coeH (mirrorFEM hT hB N) p))).symm
  have h2 := norm_exState'_sub_coeH_sq (mirrorFEM hT hB N) (D.exactWave T) t p
  refine Eq.trans ?_ (h1.trans (congrArg Real.sqrt h2)).symm
  have e1 : ‖(D.exactWave T).σ' t - (p.σ : TU0)‖ = ‖((p.σ : TU0) : W0)‖ := by
    change ‖(0 : TU0) - _‖ = _
    rw [zero_sub, norm_neg]
    rfl
  have e3 : ‖(D.exactWave T).M' t - (p.M : W2)‖ = ‖(p.M : W2)‖ := by
    change ‖(0 : W2) - _‖ = _
    rw [zero_sub, norm_neg]
  have e2 : ‖(D.exactWave T).u' t - (p.u : BU1)‖ =
      ‖rowsW1L (stEL (D.V t)) - bIncl1 (p.u : BU1)‖ := by
    change ‖rowsBU (stEL (D.V t)) - _‖ = _
    rw [← D.bIncl1_u' ht.1, ← map_sub, norm_bIncl1]
  have e4 : ‖(D.exactWave T).ρ' t - (p.ρ : Wv W2)‖ =
      ‖rowsW2L (stBL (D.V t)) - (p.ρ : Wv W2)‖ := rfl
  unfold tsdErr
  refine congrArg Real.sqrt ?_
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg (· ^ 2) e1.symm)
    (congrArg (· ^ 2) e2.symm)) (congrArg (· ^ 2) e3.symm)) (congrArg (· ^ 2) e4.symm)

/-- At `a' = 0`: `‖y - Rt a‖² - tsdErr(y, a)² = ‖y‖² - tsdErr(y, 0)²`. -/
theorem norm_sq_sub_mirrorReEmb_sub_tsdErr_zero {y : PiLp 2 SpaceQ} (hy : y ∈ totalSub tsdQ)
    (a : REnergy) :
    ‖y - mirrorReEmb a‖ ^ 2 - tsdErr y a ^ 2 = ‖y‖ ^ 2 - tsdErr y 0 ^ 2 := by
  have h := norm_sq_sub_mirrorReEmb_sub_tsdErr hy a 0
  rwa [map_zero, sub_zero] at h

include hT hB in
set_option maxHeartbeats 2000000 in
/-- `tsdErr(U(t), 0) = ‖ξ(t)‖`. -/
theorem tsdErr_zero_eq (N : ℕ) (Dd : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    tsdErr (Dd.U t) 0 = ‖exState (Dd.exactWave T) t‖ := by
  have h := tsdErr_eq hT hB N Dd ht 0
  have z : (EState.mk (((0 : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h
        (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Wt2h).σ : TU0) : W0)
      (bIncl1 ((0 : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h
        (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Wt2h).u : BU1))
      ((0 : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h
        (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Wt2h).M : W2)
      ((0 : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h
        (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Wt2h).ρ : Wv W2) : REnergy) = 0 :=
    EState.ext rfl (map_zero bIncl1) rfl rfl
  rw [z, (coeH (mirrorFEM hT hB N)).map_zero, sub_zero] at h
  exact h

include hT hB in
set_option maxHeartbeats 2000000 in
/-- **The continuous forms state of a TSD solution, tested with a hidden state, is its pairing
with the read state**: `⟪ξ(t), v⟫ = ⟪U(t), ι v⟫_ℝ` (polarization of `tsdErr_eq`). -/
theorem inner_exState_coeH_mirror (N : ℕ) (Dd : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T)
    (v : mirrorHidden hT hB N) :
    ⟪exState (Dd.exactWave T) t, coeH (mirrorFEM hT hB N) v.toEState⟫ =
      ⟪Dd.U t, mirrorEmb hT hB N v⟫_ℝ := by
  have h1 : tsdErr (Dd.U t) (mirrorFE hT hB N v) =
      ‖exState (Dd.exactWave T) t - coeH (mirrorFEM hT hB N) v.toEState‖ :=
    tsdErr_eq hT hB N Dd ht v.toEState
  have h0 := tsdErr_zero_eq hT hB N Dd ht
  have hd := norm_sq_sub_mirrorReEmb_sub_tsdErr_zero (Dd.U_tsd t) (mirrorFE hT hB N v)
  have h1' := congrArg (· ^ 2) h1
  have h0' := congrArg (· ^ 2) h0
  have hn : ‖mirrorReEmb (mirrorFE hT hB N v)‖ = ‖coeH (mirrorFEM hT hB N) v.toEState‖ :=
    (norm_mirrorReEmb _).trans ((norm_mirrorFE hT hB N v).trans
      ((HiddenState.norm_toEState v).symm.trans (norm_coeH _ _).symm))
  have key := real_inner_eq_of_norm (a := Dd.U t) (b := exState (Dd.exactWave T) t) hn
    (by linarith)
  exact key.symm.trans (congrArg (fun z => ⟪Dd.U t, z⟫_ℝ) (mirrorEmb_apply hT hB N v).symm)

include hT hB in
set_option maxHeartbeats 2000000 in
/-- `tsdErr(U'(t), 0) = ‖ξ'(t)‖`. -/
theorem tsdErr_zero_eq' (N : ℕ) (Dd : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    tsdErr (Dd.V t) 0 = ‖exState' (Dd.exactWave T) t‖ := by
  have h := tsdErr_eq' hT hB N Dd ht 0
  have z : (EState.mk (((0 : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h
        (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Wt2h).σ : TU0) : W0)
      (bIncl1 ((0 : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h
        (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Wt2h).u : BU1))
      ((0 : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h
        (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Wt2h).M : W2)
      ((0 : EState (mirrorFEM hT hB N).V0h (mirrorFEM hT hB N).Vt1h
        (mirrorFEM hT hB N).W2h (mirrorFEM hT hB N).Wt2h).ρ : Wv W2) : REnergy) = 0 :=
    EState.ext rfl (map_zero bIncl1) rfl rfl
  rw [z, (coeH (mirrorFEM hT hB N)).map_zero, sub_zero] at h
  exact h

include hT hB in
set_option maxHeartbeats 2000000 in
/-- The same for the time derivative: `⟪ξ'(t), v⟫ = ⟪U'(t), ι v⟫_ℝ`. -/
theorem inner_exState'_coeH_mirror (N : ℕ) (Dd : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T)
    (v : mirrorHidden hT hB N) :
    ⟪exState' (Dd.exactWave T) t, coeH (mirrorFEM hT hB N) v.toEState⟫ =
      ⟪Dd.V t, mirrorEmb hT hB N v⟫_ℝ := by
  have h1 : tsdErr (Dd.V t) (mirrorFE hT hB N v) =
      ‖exState' (Dd.exactWave T) t - coeH (mirrorFEM hT hB N) v.toEState‖ :=
    tsdErr_eq' hT hB N Dd ht v.toEState
  have h0 := tsdErr_zero_eq' hT hB N Dd ht
  have hd := norm_sq_sub_mirrorReEmb_sub_tsdErr_zero (Dd.V_tsd t) (mirrorFE hT hB N v)
  have h1' := congrArg (· ^ 2) h1
  have h0' := congrArg (· ^ 2) h0
  have hn : ‖mirrorReEmb (mirrorFE hT hB N v)‖ = ‖coeH (mirrorFEM hT hB N) v.toEState‖ :=
    (norm_mirrorReEmb _).trans ((norm_mirrorFE hT hB N v).trans
      ((HiddenState.norm_toEState v).symm.trans (norm_coeH _ _).symm))
  have key := real_inner_eq_of_norm (a := Dd.V t) (b := exState' (Dd.exactWave T) t) hn
    (by linarith)
  exact key.symm.trans (congrArg (fun z => ⟪Dd.V t, z⟫_ℝ) (mirrorEmb_apply hT hB N v).symm)

set_option maxHeartbeats 2000000 in
/-- **The elliptic projection (6.4) of a TSD solution is a Galerkin projection**:
`(1 - Lₕ) Πₕ(t) = ιₕ* (U(t) - U'(t))` on `[0, T]` (`inner_ellDefect` and the identification of the
continuous forms state). -/
theorem mEll_galerkin (N : ℕ) (Dd : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    mEll hT hB N Dd T t - waveGen (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) (mEll hT hB N Dd T t) =
      (mirrorEmb hT hB N).adjoint (Dd.U t - Dd.V t) := by
  refine ext_inner_right ℝ fun v => ?_
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  have hd : ⟪mEll' hT hB N Dd T t - waveGen (mirrorWave hT hB N)
      (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N)
        (mEll hT hB N Dd T t), v⟫ =
      ⟪coeH (mirrorFEM hT hB N) (mEll' hT hB N Dd T t).toEState -
        exState' (Dd.exactWave (T + 1)) t, coeH (mirrorFEM hT hB N) v.toEState⟫ +
        ⟪exState (Dd.exactWave (T + 1)) t - coeH (mirrorFEM hT hB N) (mEll hT hB N Dd T t).toEState,
          coeH (mirrorFEM hT hB N) v.toEState⟫ := by
    with_reducible_and_instances exact (inner_ellDefect (mirrorFEM hT hB N)
      (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N)
      (Dd.exactWave (T + 1)) (fun t _ v => mirrorSrcFun_zero_apply t v) (Icc_sub_Ico_add_one ht) v)
  have hd1 := inner_sub_left (𝕜 := ℝ) (coeH (mirrorFEM hT hB N) (mEll' hT hB N Dd T t).toEState)
    (exState' (Dd.exactWave (T + 1)) t) (coeH (mirrorFEM hT hB N) v.toEState)
  have hd2 := inner_sub_left (𝕜 := ℝ) (exState (Dd.exactWave (T + 1)) t)
    (coeH (mirrorFEM hT hB N) (mEll hT hB N Dd T t).toEState) (coeH (mirrorFEM hT hB N) v.toEState)
  have e1 : ⟪mEll' hT hB N Dd T t, v⟫ = ⟪coeH (mirrorFEM hT hB N) (mEll' hT hB N Dd T t).toEState,
      coeH (mirrorFEM hT hB N) v.toEState⟫ :=
    ((inner_coeH _ _ _).trans (HiddenState.inner_toEState _ _)).symm
  have e0 : ⟪mEll hT hB N Dd T t, v⟫ = ⟪coeH (mirrorFEM hT hB N) (mEll hT hB N Dd T t).toEState,
      coeH (mirrorFEM hT hB N) v.toEState⟫ :=
    ((inner_coeH _ _ _).trans (HiddenState.inner_toEState _ _)).symm
  have hs := inner_sub_left (𝕜 := ℝ) (mEll' hT hB N Dd T t) (waveGen (mirrorWave hT hB N)
    (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N)
      (mEll hT hB N Dd T t)) v
  have hs0 := inner_sub_left (𝕜 := ℝ) (mEll hT hB N Dd T t) (waveGen (mirrorWave hT hB N)
    (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N)
      (mEll hT hB N Dd T t)) v
  have hadj := ContinuousLinearMap.adjoint_inner_left (mirrorEmb hT hB N) v (Dd.U t - Dd.V t)
  have hsub := inner_sub_left (𝕜 := ℝ) (Dd.U t) (Dd.V t) (mirrorEmb hT hB N v)
  have iU := inner_exState_coeH_mirror hT hB N Dd ht' v
  have iV := inner_exState'_coeH_mirror hT hB N Dd ht' v
  linarith

/-- The real hidden spaces are finite-dimensional. -/
theorem mirrorFEMReal_finiteDimensional :
    ∀ N, FiniteDimensional ℝ ((mirrorFEMReal hT hB).X N) :=
  fun N => HiddenState.instFiniteDimensional (mirrorWave hT hB N)

instance mirrorFEMApprox_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ ((mirrorFEMApprox hT hB).X N) :=
  (mirrorFEMReal hT hB).complexify_finiteDimensional (hfd := mirrorFEMReal_finiteDimensional hT hB)
    mulI mulI_mulI norm_mulI (adjoint_mirrorEmb_mulI hT hB) (inner_mirrorEmb_mulI hT hB) N

/-- The discrete differential `𝐝ₕ` on the real hidden spaces. -/
abbrev mirrorDiffGen (N : ℕ) : (mirrorFEMReal hT hB).X N →L[ℝ] (mirrorFEMReal hT hB).X N :=
  diffGen (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
    (mirrorWave_S0_surjective hT hB N)

theorem mirrorFEMReal_L_eq (N : ℕ) :
    (mirrorFEMReal hT hB).L N = diffWave (mirrorDiffGen hT hB N) :=
  waveGen_eq_diffWave _ _ _

/-- **The discrete differential of the mirror scheme on complex data**: `𝐝ₕ ⊕ 𝐝ₕ` on real and
imaginary parts. -/
def mirrorD (N : ℕ) : (mirrorFEMApprox hT hB).X N →L[ℝ] (mirrorFEMApprox hT hB).X N :=
  (mirrorFEMReal hT hB).complexifyD mulI mulI_mulI norm_mulI (adjoint_mirrorEmb_mulI hT hB)
    (inner_mirrorEmb_mulI hT hB) (mirrorDiffGen hT hB) N

theorem mirrorD_D (N : ℕ) (v : (mirrorFEMApprox hT hB).X N) :
    mirrorD hT hB N (mirrorD hT hB N v) = 0 :=
  (mirrorFEMReal hT hB).complexifyD_D mulI mulI_mulI norm_mulI (adjoint_mirrorEmb_mulI hT hB)
    (inner_mirrorEmb_mulI hT hB) (mirrorDiffGen hT hB) (fun _ v => diffGen_diffGen _ _ _ v) N v

/-- **The generator of the mirror scheme is the Hodge wave operator of `𝐝ₕ ⊕ 𝐝ₕ`.** -/
theorem mirrorFEMApprox_L_eq (N : ℕ) :
    (mirrorFEMApprox hT hB).L N = diffWave (mirrorD hT hB N) :=
  (mirrorFEMReal hT hB).complexify_L_eq_diffWave mulI mulI_mulI norm_mulI
    (adjoint_mirrorEmb_mulI hT hB) (inner_mirrorEmb_mulI hT hB) (mirrorDiffGen hT hB)
    (mirrorFEMReal_L_eq hT hB) N

theorem complexQℝ_waveGroup_eq_U {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) {t : ℝ}
    (ht : 0 ≤ t) : complexQℝ.waveGroup.S t x = (tsdDatumOf hx).U t :=
  complexQℝ_waveGroup ht x

theorem complexQℝ_waveGroup_eq_V {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) {t : ℝ}
    (ht : 0 ≤ t) : complexQℝ.waveGroup.S t (waveExt complexQℝ x) = (tsdDatumOf hx).V t := by
  rw [waveExt_of_mem (LinearPMap.domainSq_le_domain hx.2), complexQℝ_wave_apply]
  exact complexQℝ_waveGroup ht _

set_option maxHeartbeats 2000000 in
/-- **The Galerkin identity of the elliptic core of the mirror scheme**: real and imaginary parts
of the comparison are the elliptic projections (6.4) of the TSD solutions from `ξ₀` and `-iξ₀`,
and `(1 - Lₕ) pₕ(t) = ιₕ* (e^{tL} ξ₀ - e^{tL} L ξ₀)`. -/
theorem mirrorEllCore_galerkin : ∀ T, ∀ x ∈ (mirrorEllCore hT hB).Data, ∀ N, ∀ t ∈ Ico 0 T,
    ((mirrorEllCore hT hB).cmp T).p x N t -
        (mirrorFEMApprox hT hB).L N (((mirrorEllCore hT hB).cmp T).p x N t) =
      ((mirrorFEMApprox hT hB).incl N).adjoint (complexQℝ.waveGroup.S t x -
        complexQℝ.waveGroup.S t (waveExt complexQℝ x)) := by
  intro T x hx N t ht
  have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have hU := complexQℝ_waveGroup_eq_U hx ht.1
  have hV := complexQℝ_waveGroup_eq_V hx ht.1
  have hU' : (tsdDatumOf (neg_I_smul_mem hx)).U t = -Complex.I • (tsdDatumOf hx).U t :=
    (complexQ.waveGroup.S t).map_smul (-Complex.I) x
  have hV' : (tsdDatumOf (neg_I_smul_mem hx)).V t = -Complex.I • (tsdDatumOf hx).V t := by
    change complexQ.waveGroup.S t (tsdDatumOf (neg_I_smul_mem hx)).LU₀ = _
    rw [LU₀_negI hx]
    exact (complexQ.waveGroup.S t).map_smul (-Complex.I) _
  have e : (tsdDatumOf hx).U t - (tsdDatumOf hx).V t =
      complexQℝ.waveGroup.S t x - complexQℝ.waveGroup.S t (waveExt complexQℝ x) :=
    congrArg₂ (· - ·) hU.symm hV.symm
  have e2 : (tsdDatumOf (neg_I_smul_mem hx)).U t - (tsdDatumOf (neg_I_smul_mem hx)).V t =
      -mulI (complexQℝ.waveGroup.S t x - complexQℝ.waveGroup.S t (waveExt complexQℝ x)) := by
    calc _ = -Complex.I • (tsdDatumOf hx).U t - -Complex.I • (tsdDatumOf hx).V t :=
          congrArg₂ (· - ·) hU' hV'
      _ = -(Complex.I • ((tsdDatumOf hx).U t - (tsdDatumOf hx).V t)) := by
          rw [← smul_sub, neg_smul]
      _ = _ := by rw [e]; rfl
  have g1 := mEll_galerkin hT hB N (tsdDatumOf hx) ht'
  have g2 := mEll_galerkin hT hB N (tsdDatumOf (neg_I_smul_mem hx)) ht'
  have hp : ((mirrorEllCore hT hB).cmp T).p x N t =
      (mirrorFEMReal hT hB).complexifyPair mulI mulI_mulI norm_mulI (adjoint_mirrorEmb_mulI hT hB)
        (inner_mirrorEmb_mulI hT hB) N (mirrorEllRe hT hB T x N t) (mirrorEllIm hT hB T x N t) :=
    rfl
  simp only [hp, mirrorEllRe_of_mem hT hB T hx, mirrorEllIm_of_mem hT hB T hx]
  exact (mirrorFEMReal hT hB).complexify_galerkin mulI mulI_mulI norm_mulI
    (adjoint_mirrorEmb_mulI hT hB) (inner_mirrorEmb_mulI hT hB) (mirrorFEMReal_isOrthogonal hT hB)
    N _ _ _ (g1.trans (congrArg (mirrorEmb hT hB N).adjoint e))
    (g2.trans ((congrArg (mirrorEmb hT hB N).adjoint e2).trans (map_neg _ _)))

/-- **The orbit of `L ξ₀` stays in the closure of the core** (`tsdQℝ`). -/
theorem mirrorEllCore_orbit_closure : ∀ x ∈ (mirrorEllCore hT hB).Data, ∀ t : ℝ, 0 ≤ t →
    complexQℝ.waveGroup.S t (waveExt complexQℝ x) ∈
      (mirrorEllCore hT hB).Data.topologicalClosure := by
  intro x hx t ht
  rw [mirrorEllCore_closure]
  have h := (tsdDatumOf hx).V_tsd t
  rw [← complexQℝ_waveGroup_eq_V hx ht] at h
  exact h

/-- **The mirror scheme (6.5) as an approximating family of discrete differential spaces**
(`ApproxComplexCrime.ofGalerkinCore`): the hidden spaces with `𝐝ₕ ⊕ 𝐝ₕ`, the reading map of
`mirrorFEMApprox`, the elliptic core, the TSD constraint. -/
def mirrorComplex : ApproxComplexCrime complexQℝ ℕ :=
  ApproxComplexCrime.ofGalerkinCore (mirrorFEMApprox hT hB)
    (hfd := mirrorFEMApprox_finiteDimensional hT hB) (mirrorFEMApprox_isOrthogonal hT hB)
    (mirrorD hT hB) (mirrorD_D hT hB) (mirrorFEMApprox_L_eq hT hB) (mirrorEllCore hT hB)
    (fun _ hx => hx.2) (mirrorEllCore_galerkin hT hB) (mirrorEllCore_orbit_closure hT hB)

/-- The discrete solutions of `ofComplexCrime (mirrorComplex)` are those of `mirrorFEMApprox`. -/
theorem mirrorComplex_sol (N : ℕ) (v : (mirrorFEMApprox hT hB).X N) (t : ℝ) :
    (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N v t =
      (mirrorFEMApprox hT hB).sol N v t :=
  ofComplexCrime_ofGalerkinCore_sol (hfd := mirrorFEMApprox_finiteDimensional hT hB) _ _ _ _ _ _ _
    _ _ N v t

/-- **The mirror scheme (6.5) through the complex-level front end**: the verdict of the
approximating FEEC theorem for `ofComplexCrime (mirrorComplex)` (the family is built by
`ofGalerkinCore` from the existing elliptic core `mirrorEllCore`, through the Galerkin identity of
(6.4) and orthogonal reading maps; the convergence of that core, the Strang bound of (6.4) with
weak consistency, is an input, so this re-derives the verdict of
`einsteinBianchi_mirrorFEM_converges` through the complex-level theorem); its discrete solutions
are those of `mirrorFEMApprox` (the scheme (6.5) without source, real and imaginary parts); the
generator is `𝐝ₕ - 𝐝ₕ*`; for
every TSD datum and every family of discrete initial values read convergent to it, the discrete
solutions converge to the TSD solution uniformly on `[0, T]` and the TSD residual tends to `0`. -/
theorem einsteinBianchi_mirrorFEM_ofComplexCrime :
    (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).Verdict
      (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)) ∧
    (∀ N v t, (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N v t =
      (mirrorFEMApprox hT hB).sol N v t) ∧
    (∀ N, (mirrorFEMApprox hT hB).L N = diffWave (mirrorD hT hB N)) ∧
    (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)).Data.topologicalClosure = tsdQℝ ∧
    (∀ x ∈ tsdQℝ, ∀ T : ℝ, ∀ v : ∀ N, (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).X N,
      Tendsto (fun N => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N (v N)) atTop
        (𝓝 x) →
      TendstoUniformlyOn
        (fun N t => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t)
        (fun t => complexQℝ.waveGroup.S t x) atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun N t => infDist
        ((ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t) (tsdQℝ : Set _))
        (fun _ => 0) atTop (Icc 0 T)) := by
  refine ⟨(approxFEEC_ofComplexCrime _).1,
    mirrorComplex_sol hT hB,
    mirrorFEMApprox_L_eq hT hB, mirrorEllCore_closure hT hB, fun x hx T v hv => ?_⟩
  have hx' : x ∈ (ApproxFEEC.ofComplexCrimeCore (mirrorComplex hT hB)).Data.topologicalClosure :=
    (mirrorEllCore_closure hT hB).ge hx
  set F := ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)
  exact ⟨(dissipFEEC_converges _ _ T hx' hv).congr_right fun t ht =>
    DFunLike.congr_fun (ApproxFEEC.S_eq_waveGroup F ht.1) x,
    dissipFEEC_residual F.toDissipFEEC ((dissipFEEC_propagates_iff _).2.2.1 isReducing_tsdQℝ).1 _ T
      hx' hx hv⟩

set_option maxHeartbeats 1000000 in
/-- **The discrete Gauss constraint is preserved exactly by the discrete solutions of the mirror
scheme**, on real and imaginary parts (`hiddenGauss ⊕ hiddenGauss`: `σₕ = 0`, `uₕ ⊥ d̃ Φ(Vₕ⁰, 0)`;
item 3 of `approxFEEC_ofComplexCrime`). -/
theorem mirrorFEM_preserves_hiddenGauss (N : ℕ) {v : (mirrorFEMApprox hT hB).X N}
    (hv : v ∈ prodSub (hiddenGauss (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N))) (t : ℝ) :
    ((ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).group N).S t v ∈
      prodSub (hiddenGauss (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
        (mirrorWave_S0_surjective hT hB N)) :=
  (approxFEEC_ofComplexCrime (mirrorComplex hT hB)).2.2.1 N _ (fun w hw => by
    have e : (mirrorComplex hT hB).toFamily.L N w = (mirrorFEMApprox hT hB).L N w :=
      congrArg (fun A => A w) (mirrorFEMApprox_L_eq hT hB N).symm
    rw [e]
    obtain ⟨⟨a, b⟩⟩ := w
    exact ⟨waveGen_mem_hiddenGauss _ _ _ hw.1, waveGen_mem_hiddenGauss _ _ _ hw.2⟩) v hv t

/-! #### Rates of the mirror scheme through the complex-level front end -/

set_option maxHeartbeats 1000000 in
/-- **The approximation error of the derivative of one real part** is the projection error of the
time derivative. -/
theorem tsdErr_mEll' (N : ℕ) (D : TSDDatum) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    tsdErr (D.V t) (mirrorFE hT hB N (mEll' hT hB N D T t)) = ellErr' hT hB N D T t :=
  tsdErr_eq' hT hB N D (T := T + 1) ⟨ht.1, by linarith [ht.2]⟩ (mEll' hT hB N D T t).toEState

set_option maxHeartbeats 2000000 in
/-- **The approximation error of the derivative of the elliptic comparison**:
`‖e^{tL} L ξ₀ - ιₕ pₕ'(t)‖` is at most the projection errors of the time derivatives of the real and
imaginary parts. -/
theorem norm_sub_mirrorEllCmp_p'_le (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t (waveExt complexQℝ x) - (mirrorFEMApprox hT hB).incl N
      ((mirrorEllCmp hT hB T).p' x N t)‖ ≤
      ellErr' hT hB N (tsdDatumOf hx) T t +
        ellErr' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t := by
  have hyV := complexQℝ_waveGroup_eq_V hx ht.1
  have hyV' : (tsdDatumOf (neg_I_smul_mem hx)).V t = -Complex.I • (tsdDatumOf hx).V t := by
    change complexQ.waveGroup.S t (tsdDatumOf (neg_I_smul_mem hx)).LU₀ = _
    rw [LU₀_negI hx]
    exact (complexQ.waveGroup.S t).map_smul (-Complex.I) _
  have e : (mirrorFEMApprox hT hB).incl N ((mirrorEllCmp hT hB T).p' x N t) =
      mirrorReEmb (mirrorFE hT hB N (mEll' hT hB N (tsdDatumOf hx) T t)) +
        Complex.I • mirrorReEmb (mirrorFE hT hB N
          (mEll' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t)) := by
    have h : (mirrorFEMApprox hT hB).incl N ((mirrorEllCmp hT hB T).p' x N t) =
        (mirrorFEMReal hT hB).incl N (mirrorEllRe' hT hB T x N t) +
          mulI ((mirrorFEMReal hT hB).incl N (mirrorEllIm' hT hB T x N t)) := rfl
    rw [mirrorEllRe'_of_mem hT hB T hx, mirrorEllIm'_of_mem hT hB T hx] at h
    exact h
  have key := norm_sub_mirrorReEmb_le ((tsdDatumOf hx).V_tsd t)
    (mirrorFE hT hB N (mEll' hT hB N (tsdDatumOf hx) T t))
    (mirrorFE hT hB N (mEll' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t))
  have h1 := tsdErr_mEll' hT hB N (tsdDatumOf hx) ht
  have h2 := (congrArg (fun y => tsdErr y (mirrorFE hT hB N
    (mEll' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t))) hyV').symm.trans
      (tsdErr_mEll' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) ht)
  have hz : complexQℝ.waveGroup.S t (waveExt complexQℝ x) - (mirrorFEMApprox hT hB).incl N
      ((mirrorEllCmp hT hB T).p' x N t) =
        (tsdDatumOf hx).V t - mirrorReEmb (mirrorFE hT hB N (mEll' hT hB N (tsdDatumOf hx) T t)) -
          Complex.I • mirrorReEmb (mirrorFE hT hB N
            (mEll' hT hB N (tsdDatumOf (neg_I_smul_mem hx)) T t)) :=
    (congrArg₂ (· - ·) hyV e).trans (sub_add_eq_sub_sub _ _ _)
  exact (congrArg norm hz).trans_le (key.trans_eq (congrArg₂ (· + ·) h1 h2))

set_option maxHeartbeats 4000000 in
/-- **The `O(h)` rate class of the mirror scheme through the complex-level front end**
(`galerkinRateClass` of `mirrorComplex`): TSD data of `D(L³)`, class norm `‖ξ₀‖_{L³}`, order `1`
in `h_N`, with `Cₐ = 4K` (`K = mirrorEllK`) from the Strang bound of (6.4) for the state and its
time derivative (`ellErr_le_sobolev`). -/
def mirrorComplexRate (T : ℝ) :
    (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).RateClass T :=
  galerkinRateClass (hfd := mirrorFEMApprox_finiteDimensional hT hB) (mirrorFEMApprox hT hB)
    (mirrorFEMApprox_isOrthogonal hT hB) (mirrorD hT hB) (mirrorD_D hT hB)
    (mirrorFEMApprox_L_eq hT hB) (mirrorEllCore hT hB) (fun _ hx => hx.2)
    (mirrorEllCore_galerkin hT hB) (mirrorEllCore_orbit_closure hT hB) T mirrorL3Data
    (fun _ hx => hx.1) mirrorL3Norm meshSize 1 (4 * mirrorEllK (C := C)) fun x hx N t ht => by
      have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
      obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := sobSize_le_of_mem_l3 hx
      have e1 := ellErr_le_sobolev hT hB _ zero_le_one le_rfl a0 a1 a2 N ht'
      have e2 := ellErr_le_sobolev hT hB _ zero_le_one le_rfl b0 b1 b2 N ht'
      have hK := mirrorEllK_nonneg hT (C := C)
      have hm := Real.rpow_nonneg (meshSize_pos N).le (1 : ℝ)
      have f1 := mul_le_mul_of_nonneg_left a3 (mul_nonneg hK hm)
      have f2 := mul_le_mul_of_nonneg_left b3 (mul_nonneg hK hm)
      refine ⟨(norm_sub_mirrorEllCmp_le hT hB (T + 1) hx.1 N ht').trans ?_,
        (norm_sub_mirrorEllCmp_p'_le hT hB (T + 1) hx.1 N ht').trans ?_⟩
      · nlinarith [e1.1, e2.1]
      · nlinarith [e1.2, e2.2]

set_option maxHeartbeats 4000000 in
/-- **The `O(hˢ)` rate class of the mirror scheme through the complex-level front end**: TSD data
in `H^{2+s}`, `0 ≤ s ≤ 1`, class norm `‖ξ₀‖_{2+s}`, `Cₐ = 6K`. -/
def mirrorComplexRateSobolev (T s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).RateClass T :=
  galerkinRateClass (hfd := mirrorFEMApprox_finiteDimensional hT hB) (mirrorFEMApprox hT hB)
    (mirrorFEMApprox_isOrthogonal hT hB) (mirrorD hT hB) (mirrorD_D hT hB)
    (mirrorFEMApprox_L_eq hT hB) (mirrorEllCore hT hB) (fun _ hx => hx.2)
    (mirrorEllCore_galerkin hT hB) (mirrorEllCore_orbit_closure hT hB) T (mirrorSobData s)
    (fun _ hx => hx.1) (fun x => √(sobState (2 + s) x)) meshSize s (6 * mirrorEllK (C := C))
    fun x hx N t ht => by
      have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
      obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := sobSize_le_of_mem hx
      have e1 := ellErr_le_sobolev hT hB _ hs0 hs1 a0 a1 a2 N ht'
      have e2 := ellErr_le_sobolev hT hB _ hs0 hs1 b0 b1 b2 N ht'
      have hK := mirrorEllK_nonneg hT (C := C)
      have hm := Real.rpow_nonneg (meshSize_pos N).le s
      have f1 := mul_le_mul_of_nonneg_left a3 (mul_nonneg hK hm)
      have f2 := mul_le_mul_of_nonneg_left b3 (mul_nonneg hK hm)
      refine ⟨(norm_sub_mirrorEllCmp_le hT hB (T + 1) hx.1 N ht').trans ?_,
        (norm_sub_mirrorEllCmp_p'_le hT hB (T + 1) hx.1 N ht').trans ?_⟩
      · nlinarith [e1.1, e2.1]
      · nlinarith [e1.2, e2.2]

set_option maxHeartbeats 2000000 in
/-- **The `O(h)` rate of the mirror scheme (6.5) from the complex-level estimates**, for TSD data
of `D(L³)` and all `t ≥ 0`, from the initialization [QuennevilleBelair2015], (6.4) (`mirrorEllInit`):
`‖e^{tL} ξ₀ - ι e^{tL'} Πₕ(0)‖ ≤ (C + C_ι C' t) h_N ‖ξ₀‖_{L³}` with
`C = (1 + 8 C_ι) 4K`, `C' = 2 (1 + 8 (1 + C_ι²) + C_ι (1 + 8 C_ι)) 4K` (`K = mirrorEllK`), the
discrete solution being that of `mirrorFEMApprox` (the scheme (6.5)). -/
theorem einsteinBianchi_mirrorFEM_ofComplexCrime_rate {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorL3Data)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
      ((mirrorComplex hT hB).toFamily.rateConstA * (4 * mirrorEllK (C := C)) +
        (mirrorComplex hT hB).toFamily.boundConst *
          (2 * (mirrorComplex hT hB).toFamily.rateConstD * (4 * mirrorEllK (C := C))) * t) *
        (meshSize N * mirrorL3Norm x) := by
  have h := (mirrorComplex hT hB).error_le_of_rateClass (mirrorComplexRate hT hB t) hx N
    ⟨ht, le_rfl⟩
  have hp : (mirrorComplexRate hT hB t).p x N 0 = mirrorEllInit hT hB x N :=
    (galerkinRateClass_p (hfd := mirrorFEMApprox_finiteDimensional hT hB) _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ hx N ⟨le_rfl, by linarith⟩).trans
      (mirrorEllCmp_p_zero_eq_init hT hB (t + 1) x N)
  rw [hp, mirrorComplex_sol] at h
  refine h.trans_eq ?_
  change _ * (meshSize N ^ (1 : ℝ) * mirrorL3Norm x) = _
  rw [Real.rpow_one]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The `O(hˢ)` rate of the mirror scheme (6.5) from the complex-level estimates**, for TSD data
in `H^{2+s}`, `0 ≤ s ≤ 1`, and all `t ≥ 0`, from the initialization [QuennevilleBelair2015], (6.4):
`‖e^{tL} ξ₀ - ι e^{tL'} Πₕ(0)‖ ≤ (C + C_ι C' t) h_Nˢ ‖ξ₀‖_{2+s}` (`Cₐ = 6K`). -/
theorem einsteinBianchi_mirrorFEM_ofComplexCrime_rate_sobolev {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
      ((mirrorComplex hT hB).toFamily.rateConstA * (6 * mirrorEllK (C := C)) +
        (mirrorComplex hT hB).toFamily.boundConst *
          (2 * (mirrorComplex hT hB).toFamily.rateConstD * (6 * mirrorEllK (C := C))) * t) *
        (meshSize N ^ s * √(sobState (2 + s) x)) := by
  have h := (mirrorComplex hT hB).error_le_of_rateClass
    (mirrorComplexRateSobolev hT hB t s hs0 hs1) hx N ⟨ht, le_rfl⟩
  have hp : (mirrorComplexRateSobolev hT hB t s hs0 hs1).p x N 0 = mirrorEllInit hT hB x N :=
    (galerkinRateClass_p (hfd := mirrorFEMApprox_finiteDimensional hT hB) _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ hx N ⟨le_rfl, by linarith⟩).trans
      (mirrorEllCmp_p_zero_eq_init hT hB (t + 1) x N)
  rw [hp, mirrorComplex_sol] at h
  exact h


end Mirror

/-! ### The thesis' boundary conditions -/

section Cube

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM
  Feec.EinsteinBianchi.MatrixModel Feec.EinsteinBianchi.BoundedFailure
  Feec.EinsteinBianchi.BoundedConvergence

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

set_option maxHeartbeats 4000000 in
/-- **The energy error of a hidden state against the classical solution is its error through
the reading map**: `‖e^{tL} x - ι v‖ = ‖ξ(t) - v‖` for every hidden `v` (as
`norm_sub_cubeEmb_cEll`, for an arbitrary state). -/
theorem norm_sub_cubeEmb_eq (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    {T t : ℝ} (ht' : t ∈ Icc 0 (T + 1)) (v : cubeHidden hT hB N) :
    ‖matrixComplex.waveGroup.S t x - cubeEmb hT hB N v‖ =
      ‖exState (cubeExact hx (T + 1)) t - coeH (cubeFEM hT hB N) v.toEState‖ := by
  obtain ⟨hV, hW, hX, hEq⟩ := cubeOrbit_spec hx (T + 1)
  have e2 := hEq t ht'
  have e3 : vecL (cubeOrbit hx (T + 1) t) = (exactWave_toSolution (cubeExact hx (T + 1))).vec t :=
    (solutionOfStrong_vec_eq hV ht').symm.trans (exactOfStrong_vec hV hW hX ht').symm
  have h1 := norm_sub_totalE_vecInv (matrixComplex.waveGroup.S t x) (cubeFE hT hB N v)
  have h4 := norm_vec_sub_cubeFE hT hB N (cubeExact hx (T + 1)) t v
  refine ((congrArg (fun y => ‖matrixComplex.waveGroup.S t x - y‖)
    (cubeEmb_apply hT hB N v)).trans h1).trans ?_
  refine (congrArg (fun z => ‖vecL z - cubeFE hT hB N v‖) e2).trans ?_
  refine (congrArg (fun z => ‖z - cubeFE hT hB N v‖) e3).trans ?_
  with_reducible_and_instances exact h4

set_option maxHeartbeats 2000000 in
/-- **The continuous forms state, tested with a hidden state, is the pairing of the exact state
with the read state**: `⟪ξ(t), v⟫ = ⟪e^{tL} x, ι v⟫` (polarization of `norm_sub_cubeEmb_eq`). -/
theorem inner_exState_coeH_cube (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    {T t : ℝ} (ht' : t ∈ Icc 0 (T + 1)) (v : cubeHidden hT hB N) :
    ⟪exState (cubeExact hx (T + 1)) t, coeH (cubeFEM hT hB N) v.toEState⟫ =
      ⟪matrixComplex.waveGroup.S t x, cubeEmb hT hB N v⟫ := by
  have h1 := norm_sub_cubeEmb_eq hT hB N hx ht' v
  have h0 := norm_sub_cubeEmb_eq hT hB N hx ht' 0
  have z2 : coeH (cubeFEM hT hB N) (0 : cubeHidden hT hB N).toEState = 0 :=
    (coeH (cubeFEM hT hB N)).map_zero
  have h0' : ‖matrixComplex.waveGroup.S t x‖ = ‖exState (cubeExact hx (T + 1)) t‖ :=
    ((congrArg (fun z => ‖matrixComplex.waveGroup.S t x - z‖) (cubeEmb hT hB N).map_zero).trans
      (congrArg norm (sub_zero _))).symm.trans (h0.trans
        ((congrArg (fun z => ‖exState (cubeExact hx (T + 1)) t - z‖) z2).trans
          (congrArg norm (sub_zero _))))
  have hn : ‖cubeEmb hT hB N v‖ = ‖coeH (cubeFEM hT hB N) v.toEState‖ :=
    (norm_cubeEmb hT hB N v).trans ((HiddenState.norm_toEState v).symm.trans (norm_coeH _ _).symm)
  have a1 := congrArg (· ^ 2) h1
  have a0 := congrArg (· ^ 2) h0'
  exact (real_inner_eq_of_norm hn (by linarith)).symm

set_option maxHeartbeats 2000000 in
/-- **The same for the time derivative** (uniqueness of one-sided derivatives of
`t ↦ ⟪ξ(t), v⟫ = ⟪e^{tL} x, ι v⟫`): `⟪ξ'(t), v⟫ = ⟪e^{tL} L x, ι v⟫` on `[0, T + 1)`. -/
theorem inner_exState'_coeH_cube (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    {T t : ℝ} (ht : t ∈ Ico 0 (T + 1)) (v : cubeHidden hT hB N) :
    ⟪exState' (cubeExact hx (T + 1)) t, coeH (cubeFEM hT hB N) v.toEState⟫ =
      ⟪matrixComplex.waveGroup.S t (waveExt matrixComplex x), cubeEmb hT hB N v⟫ := by
  have hE : HasDerivWithinAt (exState (cubeExact hx (T + 1))) (exState' (cubeExact hx (T + 1)) t)
      (Ici t) t :=
    EState.hasDerivWithinAt_mk ((cubeExact hx (T + 1)).dσ t ht) ((cubeExact hx (T + 1)).du t ht)
      ((cubeExact hx (T + 1)).dM t ht) ((cubeExact hx (T + 1)).dρ t ht)
  have h1 : HasDerivWithinAt
      (fun r => ⟪coeH (cubeFEM hT hB N) v.toEState, exState (cubeExact hx (T + 1)) r⟫)
      ⟪coeH (cubeFEM hT hB N) v.toEState, exState' (cubeExact hx (T + 1)) t⟫ (Ici t) t :=
    (innerSL ℝ (coeH (cubeFEM hT hB N) v.toEState)).hasFDerivAt.comp_hasDerivWithinAt t hE
  have h2 : HasDerivWithinAt (fun r => ⟪cubeEmb hT hB N v, matrixComplex.waveGroup.S r x⟫)
      ⟪cubeEmb hT hB N v, matrixComplex.waveGroup.S t (waveExt matrixComplex x)⟫ (Ici t) t :=
    ((innerSL ℝ (cubeEmb hT hB N v)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_waveGroup_waveExt matrixComplex (LinearPMap.domainSq_le_domain hx) t)).hasDerivWithinAt
  have heq : (fun r => ⟪cubeEmb hT hB N v, matrixComplex.waveGroup.S r x⟫) =ᶠ[𝓝[Ici t] t]
      fun r => ⟪coeH (cubeFEM hT hB N) v.toEState, exState (cubeExact hx (T + 1)) r⟫ := by
    filter_upwards [Ico_mem_nhdsGE ht.2] with r hr
    exact (real_inner_comm _ _).trans ((inner_exState_coeH_cube hT hB N hx
      ⟨ht.1.trans hr.1, hr.2.le⟩ v).symm.trans (real_inner_comm _ _))
  have h3 := h1.congr_of_eventuallyEq heq ((real_inner_comm _ _).trans
    ((inner_exState_coeH_cube hT hB N hx ⟨ht.1, ht.2.le⟩ v).symm.trans (real_inner_comm _ _)))
  have := (uniqueDiffWithinAt_Ici t).eq_deriv _ h2 h3
  exact (real_inner_comm _ _).trans (this.symm.trans (real_inner_comm _ _))

set_option maxHeartbeats 2000000 in
/-- **The elliptic projection (6.4) of the classical solution is a Galerkin projection** (thesis'
boundary conditions): `(1 - Lₕ) Πₕ(t) = ιₕ* (e^{tL} x - e^{tL} L x)` on `[0, T]`. -/
theorem cEll_galerkin (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    {T t : ℝ} (ht : t ∈ Icc 0 T) :
    cEll hT hB N hx T t - waveGen (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) (cEll hT hB N hx T t) =
      (cubeEmb hT hB N).adjoint (matrixComplex.waveGroup.S t x -
        matrixComplex.waveGroup.S t (waveExt matrixComplex x)) := by
  refine ext_inner_right ℝ fun v => ?_
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  have ht'' : t ∈ Ico 0 (T + 1) := Icc_sub_Ico_add_one ht
  have hd : ⟪cEll' hT hB N hx T t - waveGen (cubeWave hT hB N)
      (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)
        (cEll hT hB N hx T t), v⟫ =
      ⟪coeH (cubeFEM hT hB N) (cEll' hT hB N hx T t).toEState -
        exState' (cubeExact hx (T + 1)) t, coeH (cubeFEM hT hB N) v.toEState⟫ +
        ⟪exState (cubeExact hx (T + 1)) t - coeH (cubeFEM hT hB N) (cEll hT hB N hx T t).toEState,
          coeH (cubeFEM hT hB N) v.toEState⟫ := by
    with_reducible_and_instances exact (inner_ellDefect (cubeFEM hT hB N)
      (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)
      (cubeExact hx (T + 1)) (fun t _ v => srcFun_zero_apply t v) ht'' v)
  have hd1 := inner_sub_left (𝕜 := ℝ) (coeH (cubeFEM hT hB N) (cEll' hT hB N hx T t).toEState)
    (exState' (cubeExact hx (T + 1)) t) (coeH (cubeFEM hT hB N) v.toEState)
  have hd2 := inner_sub_left (𝕜 := ℝ) (exState (cubeExact hx (T + 1)) t)
    (coeH (cubeFEM hT hB N) (cEll hT hB N hx T t).toEState) (coeH (cubeFEM hT hB N) v.toEState)
  have e1 : ⟪cEll' hT hB N hx T t, v⟫ = ⟪coeH (cubeFEM hT hB N) (cEll' hT hB N hx T t).toEState,
      coeH (cubeFEM hT hB N) v.toEState⟫ :=
    ((inner_coeH _ _ _).trans (HiddenState.inner_toEState _ _)).symm
  have e0 : ⟪cEll hT hB N hx T t, v⟫ = ⟪coeH (cubeFEM hT hB N) (cEll hT hB N hx T t).toEState,
      coeH (cubeFEM hT hB N) v.toEState⟫ :=
    ((inner_coeH _ _ _).trans (HiddenState.inner_toEState _ _)).symm
  have hs := inner_sub_left (𝕜 := ℝ) (cEll' hT hB N hx T t) (waveGen (cubeWave hT hB N)
    (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)
      (cEll hT hB N hx T t)) v
  have hs0 := inner_sub_left (𝕜 := ℝ) (cEll hT hB N hx T t) (waveGen (cubeWave hT hB N)
    (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)
      (cEll hT hB N hx T t)) v
  have hadj := ContinuousLinearMap.adjoint_inner_left (cubeEmb hT hB N) v
    (matrixComplex.waveGroup.S t x - matrixComplex.waveGroup.S t (waveExt matrixComplex x))
  have hsub := inner_sub_left (𝕜 := ℝ) (matrixComplex.waveGroup.S t x)
    (matrixComplex.waveGroup.S t (waveExt matrixComplex x)) (cubeEmb hT hB N v)
  have iU := inner_exState_coeH_cube hT hB N hx ht' v
  have iV := inner_exState'_coeH_cube hT hB N hx ht'' v
  linarith

instance standardCubeApprox_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ ((standardCubeApprox hT hB).X N) :=
  HiddenState.instFiniteDimensional (cubeWave hT hB N)

/-- The discrete differential `𝐝ₕ` of the thesis' scheme. -/
abbrev cubeD (N : ℕ) : (standardCubeApprox hT hB).X N →L[ℝ] (standardCubeApprox hT hB).X N :=
  diffGen (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N) (cubeWave_S0_surjective hT hB N)

theorem cubeD_D (N : ℕ) (v : (standardCubeApprox hT hB).X N) : cubeD hT hB N (cubeD hT hB N v) = 0 :=
  diffGen_diffGen _ _ _ v

/-- **The generator of the thesis' scheme is the Hodge wave operator of `𝐝ₕ`.** -/
theorem standardCubeApprox_L_eq (N : ℕ) :
    (standardCubeApprox hT hB).L N = diffWave (cubeD hT hB N) :=
  waveGen_eq_diffWave _ _ _

set_option maxHeartbeats 2000000 in
/-- **The Galerkin identity of the elliptic core of the thesis' scheme.** -/
theorem standardCubeEllCore_galerkin : ∀ T, ∀ x ∈ (standardCubeEllCore hT hB).Data, ∀ N,
    ∀ t ∈ Ico 0 T, ((standardCubeEllCore hT hB).cmp T).p x N t -
        (standardCubeApprox hT hB).L N (((standardCubeEllCore hT hB).cmp T).p x N t) =
      ((standardCubeApprox hT hB).incl N).adjoint (matrixComplex.waveGroup.S t x -
        matrixComplex.waveGroup.S t (waveExt matrixComplex x)) := by
  intro T x hx N t ht
  have hp : ((standardCubeEllCore hT hB).cmp T).p x N t = cEll hT hB N hx T t := by
    change cubeEllP hT hB T x N t = _
    rw [cubeEllP_of_mem hT hB T hx]
  rw [hp]
  exact cEll_galerkin hT hB N hx (Ico_subset_Icc_self ht)

theorem standardCubeEllCore_closure :
    (standardCubeEllCore hT hB).Data.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.1 (dense_standardCubeEllCore hT hB)

/-- **The thesis' scheme (6.5) as an approximating family of discrete differential spaces**
(`ApproxComplexCrime.ofGalerkinCore`): the hidden spaces with `𝐝ₕ`, the reading map `cubeEmb`, the
dense elliptic core, the TSD constraint `thesisTSD`. -/
def standardCubeComplex : ApproxComplexCrime matrixComplex ℕ :=
  ApproxComplexCrime.ofGalerkinCore (standardCubeApprox hT hB)
    (hfd := standardCubeApprox_finiteDimensional hT hB) (standardCubeApprox_isOrthogonal hT hB)
    (cubeD hT hB) (cubeD_D hT hB) (standardCubeApprox_L_eq hT hB) (standardCubeEllCore hT hB)
    le_rfl (standardCubeEllCore_galerkin hT hB)
    (fun _ _ _ _ => by rw [standardCubeEllCore_closure]; trivial)

/-- The discrete solutions of `ofComplexCrime (standardCubeComplex)` are those of
`standardCubeApprox`. -/
theorem standardCubeComplex_sol (N : ℕ) (v : (standardCubeApprox hT hB).X N) (t : ℝ) :
    (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N v t =
      (standardCubeApprox hT hB).sol N v t :=
  ofComplexCrime_ofGalerkinCore_sol (hfd := standardCubeApprox_finiteDimensional hT hB) _ _ _ _ _
    _ _ _ _ N v t

/-- **The thesis' scheme (6.5) through the complex-level front end**: the verdict of the
approximating FEEC theorem for `ofComplexCrime (standardCubeComplex)` (the family is built by
`ofGalerkinCore` from the existing elliptic core `standardCubeEllCore`, through the Galerkin
identity of (6.4) and orthogonal reading maps; the convergence of that core, the Strang bound of
(6.4), is an input, so this re-derives the verdict of `einsteinBianchi_standardCube_converges`
through the complex-level theorem); its discrete solutions are those of `standardCubeApprox` (the scheme (6.5) without source); the
generator is `𝐝ₕ - 𝐝ₕ*`; the core is dense, so for every datum and every family of discrete
initial values read convergent to it the discrete solutions converge uniformly on `[0, T]`; and
from the datum `(0, 0, (0, β))`, which lies in `thesisTSD`, the exact solution leaves TSD at some `t ∈ [0, T]`, where the
TSD residuals of the discrete solutions tend to the positive limit `dist(e^{tL} ξ₀, TSD)`: the
scheme converges to a solution that leaves TSD. -/
theorem einsteinBianchi_standardCube_ofComplexCrime :
    (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).Verdict
      (ApproxFEEC.ofComplexCrimeCore (standardCubeComplex hT hB)) ∧
    (∀ N v t, (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N v t =
      (standardCubeApprox hT hB).sol N v t) ∧
    (∀ N, (standardCubeApprox hT hB).L N = diffWave (cubeD hT hB N)) ∧
    (ApproxFEEC.ofComplexCrimeCore (standardCubeComplex hT hB)).Data.topologicalClosure = ⊤ ∧
    (∀ x T, ∀ v : ∀ N, (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).X N,
      Tendsto (fun N => (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).incl N (v N))
        atTop (𝓝 x) →
      TendstoUniformlyOn
        (fun N t => (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N (v N) t)
        (fun t => matrixComplex.waveGroup.S t x) atTop (Icc 0 T)) ∧
    betaDatum ∈ thesisTSD ∧
    (∀ T : ℝ, 0 < T → ∃ t ∈ Icc 0 T, matrixComplex.waveGroup.S t betaDatum ∉ thesisTSD ∧
      0 < infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) ∧
      ∀ v : ∀ N, (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).X N,
        Tendsto (fun N => (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).incl N (v N))
          atTop (𝓝 betaDatum) →
        Tendsto (fun N => infDist
          ((ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N (v N) t)
            (thesisTSD : Set _))
          atTop (𝓝 (infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _)))) := by
  have hcl : (ApproxFEEC.ofComplexCrimeCore (standardCubeComplex hT hB)).Data.topologicalClosure =
      ⊤ := standardCubeEllCore_closure hT hB
  refine ⟨(approxFEEC_ofComplexCrime _).1, standardCubeComplex_sol hT hB,
    standardCubeApprox_L_eq hT hB, hcl, fun x T v hv => ?_, betaDatum_mem_thesisTSD,
    fun T hT0 => ?_⟩
  · exact (dissipFEEC_converges _ _ T (by rw [hcl]; trivial) hv).congr_right fun t ht =>
      DFunLike.congr_fun (ApproxFEEC.S_eq_waveGroup _ ht.1) x
  · obtain ⟨t, ht, hout⟩ := exists_waveGroup_betaDatum_not_mem hT0
    have hpos := (isClosed_thesisTSD.notMem_iff_infDist_pos ⟨0, thesisTSD.zero_mem⟩).1 hout
    refine ⟨t, ht, hout, hpos, fun v hv => ?_⟩
    have h := dissipFEEC_tendsto_infDist _ _ (thesisTSD : Set _) (by rw [hcl]; trivial) hv ht.1
    rwa [ApproxFEEC.S_eq_waveGroup _ ht.1] at h

/-! #### The discrete Gauss constraint is preserved exactly -/

set_option maxHeartbeats 1000000 in
/-- **The discrete Gauss constraint is preserved exactly by the discrete solutions of the thesis'
scheme** (`hiddenGauss`: `σₕ = 0`, `uₕ ⊥ d̃ Φ(Vₕ⁰, 0)`, invariant under `Lₕ = 𝐝ₕ - 𝐝ₕ*`; item 3 of
`approxFEEC_ofComplexCrime`), although the exact solutions leave `thesisTSD`. -/
theorem standardCube_preserves_hiddenGauss (N : ℕ) {v : (standardCubeApprox hT hB).X N}
    (hv : v ∈ hiddenGauss (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N)) (t : ℝ) :
    ((ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).group N).S t v ∈
      hiddenGauss (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
        (cubeWave_S0_surjective hT hB N) :=
  (approxFEEC_ofComplexCrime (standardCubeComplex hT hB)).2.2.1 N _ (fun w hw => by
      have e : (standardCubeComplex hT hB).toFamily.L N w =
          waveGen (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (cubeWave_S0_surjective hT hB N) w :=
        congrArg (fun A => A w) (waveGen_eq_diffWave _ _ _).symm
      exact e ▸ waveGen_mem_hiddenGauss _ _ _ hw) v hv t

end Cube

end Feec.Instances.EinsteinBianchi.FEM
