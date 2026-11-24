module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.Instances.EinsteinBianchiFEM
public import Feec.Instances.EinsteinBianchiFEMDefect
public import Feec.Physics.EinsteinBianchi.Unconditional
public import Feec.Physics.EinsteinBianchi.WaveFEMRegularity

/-!
# The weak-symmetry scheme (6.5) under the crown

The semi-discrete scheme (6.5) of [QuennevilleBelair2015], §6.3, for the Einstein–Bianchi system
with weakly imposed symmetry (Table 6.1) is not read as a conforming family: its discrete BGG
differential `𝐝ₕ (σ, u, M, ρ) = (0, -d̃ Φ(σ, 0), S₁,ₕ u, d̃ u)` uses `S₀,ₕ = π¹S⁰` and
`S₁,ₕ = π²S¹`, so its reading maps are not shown to be cochain maps. It is an approximating family
of discrete differential spaces with a cochain defect in the sense of [HolstStern2012], §3
(`Feec.Instances.EinsteinBianchi.FEM.mirrorComplex`, `standardCubeComplex`), and so an instance
of the FEEC theorem for approximating families (`Feec.HilbertComplex.ApproxComplexCrime.feec`,
which the crown `ConformingFamily.feec` consumes on its zero-defect instance, the field `crime`).
This file applies it to the scheme under both boundary conditions, with rates, and carries the
verdicts identifying the crime front with (6.5) (`MirrorFEMApprox.Verdict`,
`StandardCubeApprox.Verdict`: the discrete solutions are those of (6.5)).

**Mirror boundary conditions** (`MirrorComplex.Verdict`, `mirrorComplex_verdict`): the verdict
of the crime theorem and that of (6.5),
the inner-product defect `0` (orthogonal reading maps), the cochain defect `0` at every TSD state
(`mirrorComplex_cochainDefect_eq_zero`), so that by the residual splitting of the crown
consistent approximation at TSD states is graph-norm approximation
(`MirrorComplex.Verdict.residual_le_of_tsd`); the rates `O(h)` for TSD data of `D(L³)` and
`O(hˢ)` for TSD data in `H^{2+s}` (the rate classes `mirrorComplexRate`,
`mirrorComplexRateSobolev`), semidiscrete and, through the field `full`, for every time scheme;
and the Gauss residuals of the discrete solutions tend to `0`
(`einsteinBianchi_mirrorFEM_gaussResidual`).

**The thesis' boundary conditions** (`StandardCubeComplex.Verdict`, `standardCubeComplex_verdict`):
the verdict of the crime theorem and that of (6.5) (with a dense core, so the perturbed field
applies), the inner-product defect `0`, the
cochain defect `O(h)` in the dual discrete graph norm at the exact states
(`exists_standardCube_cochainDefect_le_mesh`), so the residual of every approximant is its
graph-norm error plus `O(h)` (`StandardCubeComplex.Verdict.residual_le_mesh`); the **rate class of
relative-class Sobolev data** (`cubeSobRate`, data `cubeSobData`: the hypotheses of
`cubeWave_rate_sobolev` along the classical solution), of order `min(s, 1)`, built from the
elliptic core with the Strang bound of (6.4) and the Strang data of Sobolev states
(`cubeFEM_strangData_le_sobolev`, `cErr_le_of_isCubeSob`), hence the rates
`O(h^{min(s,1)})` of the semidiscrete and of every fully discrete scheme; data of `D(L³)` with the
hypotheses of `waveFEM_rate_of_mem_domain_of_orbit` lie in its class at `s = 1`
(`mem_cubeSobData_of_mem_domain`, from `isSobolevStateTr_of_mem`), so they converge at `O(h)`
(`StandardCubeComplex.Verdict.rate_domain`); and limits of read discrete Gauss data stay in the
continuous Gauss constraint (`standardCube_waveGroup_mem_cubeGauss`).

`einsteinBianchiFEM_crown` collects both with the smoothers: admissible parity smoothers exist,
and smoothers for Table 6.1 exist with (5.4), uniform bounds, `d̃⁰` injective and `S₀,ₕ` onto,
unconditionally (`WaveFEM.waveFEM_cube`).

**Not shown.** The rate classes of the thesis' boundary conditions are not shown nonempty for a
non-stationary datum (the Sobolev witness `cubeWave_rate_sobolev_nonvacuous` is a classical
solution of (6.2), not identified with an orbit of the matrix model here); the cochain defect is
not shown nonzero (`Feec.Instances.EinsteinBianchiFEMDefect`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 6 (§6.2 (6.4), §6.3 (6.5), Table 6.1)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.HilbertComplex

attribute [local instance high] ApproxFEEC.instNormedSpaceRealOfInner

/-- Over `ℝ`, the normed space structure of discrete differential spaces is that of their inner
product, as for `ApproxFEEC.instNormedSpaceRealOfInner`. -/
local instance (priority := high) instNormedSpaceRealOfInnerFamily {ι : Type*} [Fintype ι]
    {c : ComplexShape ι} {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)] {H : HilbertComplex ℝ c W}
    {κ : Type*} (S : ApproxComplexCrime.Family H κ) (h : κ) : NormedSpace ℝ (S.X h) :=
  (S.innerProductSpace h).toNormedSpace

/-! ### Mirror boundary conditions -/

section Mirror

open Feec.Models.Cube.MirrorWeakSymmetry Feec.Models.Cube.RowWise
open Feec.Models.Cube.MirrorBGG (SpaceQ W2Q complexQ tsdQ)
open Feec.Models.Cube.FEM (meshSize meshSize_pos)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
    Feec.FiniteElement.PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3,
    Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a} Feec.FiniteElement.PolySeq.lagrangeP2 ρ C)

/-- **The inner-product defect of the mirror scheme vanishes**: the reading maps are isometric
(`mirrorFEMApprox_isOrthogonal`), `Jₙ = ιₙ* ιₙ = 1`. -/
theorem mirrorComplex_J (N : ℕ) : (mirrorComplex hT hB).toFamily.J N = 1 :=
  ApproxComplexCrime.Family.ofApproxFEEC_J (mirrorFEMApprox hT hB)
    (hfd := mirrorFEMApprox_finiteDimensional hT hB) (mirrorD hT hB)
    (mirrorD_D hT hB) (mirrorFEMApprox_isOrthogonal hT hB) N

/-- **The verdict of the scheme (6.5) with mirror boundary conditions**: the verdict of the crime
theorem for `mirrorComplex`, with both Holst–Stern defects zero on TSD states, the rates of its two
rate classes from every discrete initial value, the Gauss residuals, and the verdict of (6.5)
identifying the crime front with the scheme (`MirrorFEMApprox.Verdict`). -/
structure MirrorComplex.Verdict : Prop extends (mirrorComplex hT hB).Verdict where
  /-- the inner-product defect is `0` -/
  J_eq_one (N : ℕ) : (mirrorComplex hT hB).toFamily.J N = 1
  /-- the cochain defect is `0` at every TSD state of `D(L)` -/
  cochainDefect_eq_zero (N : ℕ) (y : complexQℝ.wave.domain) (hy : (y : PiLp 2 SpaceQ) ∈ tsdQℝ) :
    (mirrorComplex hT hB).toFamily.cochainDefect N y = 0
  /-- at TSD states the residual of an approximant is its graph-norm error: consistent
  approximation is graph-norm approximation -/
  residual_le_of_tsd (N : ℕ) (y : complexQℝ.wave.domain) (hy : (y : PiLp 2 SpaceQ) ∈ tsdQℝ)
    (w v : (mirrorComplex hT hB).toFamily.X N) :
    ‖⟪w - (mirrorComplex hT hB).toFamily.L N w, v⟫_ℝ -
        ⟪(y : PiLp 2 SpaceQ) - complexQℝ.wave y, (mirrorComplex hT hB).toFamily.incl N v⟫_ℝ‖ ≤
      (mirrorComplex hT hB).toFamily.boundConst *
          (‖(y : PiLp 2 SpaceQ) - (mirrorComplex hT hB).toFamily.incl N w‖ +
            ‖complexQℝ.totalD ⟨y, y.2.1⟩ -
              (mirrorComplex hT hB).toFamily.incl N ((mirrorComplex hT hB).toFamily.D N w)‖) *
        (‖v‖ + ‖(mirrorComplex hT hB).toFamily.D N v‖)
  /-- the rate `O(h)` for TSD data of `D(L³)` (`mirrorComplexRate`) -/
  rate (T : ℝ) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorL3Data) (N : ℕ)
    (v : (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).X N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x - (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N v t‖ ≤
      ((mirrorComplexRate hT hB T).C + ‖(ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N‖ *
          (mirrorComplexRate hT hB T).C' * t) *
        ((mirrorComplexRate hT hB T).meshSize N ^ (mirrorComplexRate hT hB T).α *
          (mirrorComplexRate hT hB T).classNorm x) +
      ‖(ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N‖ *
        ‖(mirrorComplexRate hT hB T).p x N 0 - v‖
  /-- the rate `O(hˢ)` for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1` (`mirrorComplexRateSobolev`) -/
  rate_sobolev (T s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {x : PiLp 2 SpaceQ}
    (hx : x ∈ mirrorSobData s) (N : ℕ)
    (v : (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).X N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x - (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N v t‖ ≤
      ((mirrorComplexRateSobolev hT hB T s hs0 hs1).C +
          ‖(ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N‖ *
            (mirrorComplexRateSobolev hT hB T s hs0 hs1).C' * t) *
        ((mirrorComplexRateSobolev hT hB T s hs0 hs1).meshSize N ^
            (mirrorComplexRateSobolev hT hB T s hs0 hs1).α *
          (mirrorComplexRateSobolev hT hB T s hs0 hs1).classNorm x) +
      ‖(ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N‖ *
        ‖(mirrorComplexRateSobolev hT hB T s hs0 hs1).p x N 0 - v‖
  /-- the Gauss residuals of the real and imaginary parts of the discrete solutions from every
  family read convergent to a TSD datum tend to `0` uniformly on `[0, T]` -/
  gaussResidual {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ) (T : ℝ)
    (v : ∀ N, (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).X N)
    (hv : Tendsto (fun N => (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).incl N (v N)) atTop
      (𝓝 x)) :
    TendstoUniformlyOn (fun N t => infDist
        (mirrorRe ((ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t))
        (mirrorGauss : Set REnergy)) (fun _ => 0) atTop (Icc 0 T) ∧
    TendstoUniformlyOn (fun N t => infDist
        (mirrorRe (-Complex.I • (ApproxFEEC.ofComplexCrime (mirrorComplex hT hB)).sol N (v N) t))
        (mirrorGauss : Set REnergy)) (fun _ => 0) atTop (Icc 0 T)
  /-- the verdict of (6.5): the discrete solutions of the crime front are those of (6.5), with the
  thesis' initialization and its rates -/
  scheme : MirrorFEMApprox.Verdict hT hB

set_option maxHeartbeats 1000000 in
/-- **The scheme (6.5) with mirror boundary conditions is an instance of the crime crown**
(`ApproxComplexCrime.feec`), with zero defects on TSD states and rates `O(h)`, `O(hˢ)`.
[QuennevilleBelair2015], §6.3, (6.5); [HolstStern2012], §3 -/
theorem mirrorComplex_verdict : MirrorComplex.Verdict hT hB where
  toVerdict := (mirrorComplex hT hB).feec
  J_eq_one := mirrorComplex_J hT hB
  cochainDefect_eq_zero := mirrorComplex_cochainDefect_eq_zero hT hB
  residual_le_of_tsd N y hy w v := by
    have h := (mirrorComplex hT hB).feec.residual_le N y w (δ := 0) (fun v => by
      rw [mirrorComplex_cochainDefect_eq_zero hT hB N y hy, inner_zero_left, norm_zero, zero_mul])
      v
    simpa only [mirrorComplex_J, sub_self, _root_.zero_apply, norm_zero, zero_add, add_zero] using h
  rate T _ hx N v _ ht := by
    have h := (mirrorComplex hT hB).feec.wave.rate (mirrorComplexRate hT hB T) hx N v ht
    rwa [ApproxFEEC.S_eq_waveGroup _ ht.1] at h
  rate_sobolev T s hs0 hs1 _ hx N v _ ht := by
    have h := (mirrorComplex hT hB).feec.wave.rate (mirrorComplexRateSobolev hT hB T s hs0 hs1) hx
      N v ht
    rwa [ApproxFEEC.S_eq_waveGroup _ ht.1] at h
  gaussResidual hx T v hv := einsteinBianchi_mirrorFEM_gaussResidual hT hB hx T v hv
  scheme := mirrorFEMApprox_verdict hT hB

end Mirror

/-! ### The thesis' boundary conditions -/

section Cube

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry
  Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM Feec.EinsteinBianchi.MatrixModel
  Feec.EinsteinBianchi.BoundedFailure Feec.EinsteinBianchi.BoundedConvergence

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- The states of the matrix model. -/
local notation "MS" => PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
  (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))

/-- **The relative-class `Hˢ` hypotheses along the classical solution** of a datum
`x ∈ D(L²)` on `[0, T]` (the classical solution `cubeExact` of (6.2), horizon `T + 1`): the
states and their time derivatives are `IsSobolevStateTr s L`, the skew fields pair boundedly with
`d¹`, `|⟪M, d v⟫|, |⟪M', d v⟫| ≤ L ‖v‖`, and the multipliers are `L²`-bounded,
`|ℓ μ|, |ℓ' μ| ≤ L ‖μ‖`: the hypotheses of `cubeWave_rate_sobolev`. -/
def IsCubeSob (T s L : ℝ) {x : MS} (hx : x ∈ matrixComplex.wave.domainSq) : Prop :=
  ∀ t ∈ Icc 0 T,
    (IsSobolevStateTr s L ((cubeExact hx (T + 1)).σ t) ((cubeExact hx (T + 1)).φ t)
        ((cubeExact hx (T + 1)).u t) ((cubeExact hx (T + 1)).M t) ((cubeExact hx (T + 1)).ρ t) ∧
      IsSobolevStateTr s L ((cubeExact hx (T + 1)).σ' t) ((cubeExact hx (T + 1)).φ' t)
        ((cubeExact hx (T + 1)).u' t) ((cubeExact hx (T + 1)).M' t)
        ((cubeExact hx (T + 1)).ρ' t)) ∧
    (∀ v : U1, |⟪(cubeExact hx (T + 1)).M t, bggSegment.d1 v⟫| ≤ L * ‖v‖ ∧
      |⟪(cubeExact hx (T + 1)).M' t, bggSegment.d1 v⟫| ≤ L * ‖v‖) ∧
    (∀ μ : U1, |(cubeExact hx (T + 1)).ℓ t μ| ≤ L * ‖μ‖ ∧
      |(cubeExact hx (T + 1)).ℓ' t μ| ≤ L * ‖μ‖)

/-- **The relative-class `Hˢ` data of the thesis' scheme on `[0, T]`** with bound `L`. -/
def cubeSobData (T s L : ℝ) : Set MS :=
  {x | ∃ hx : x ∈ matrixComplex.wave.domainSq, IsCubeSob T s L hx}

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **The rate constant of the Sobolev class**: the Strang constant of the cube data times the
constant of the Strang data of Sobolev states (`cubeFEM_strangData_le_sobolev`), with the
consistency constants `C₀` of `S₀ - S₀,ₕ` (`cubeFEM_happ0`) and `K₁` of `S₁ - S₁,ₕ`
(`exists_cubeFEM_K1`). -/
def cubeSobConst : ℝ :=
  cubeStrangK * √(cubeCloseConst C * sobStateConst C ^ 2 + (cubeFEM_happ0 hT hB).choose ^ 2 +
    (exists_cubeFEM_K1 hT hB).choose ^ 2)

theorem cubeSobConst_nonneg : 0 ≤ cubeSobConst hT hB :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

set_option maxHeartbeats 4000000 in
/-- **The projection errors of the elliptic trajectory are `O(L h^{min(s,1)})`** for data with
the Sobolev hypotheses: the Strang bound of (6.4) (`norm_sub_ellTraj_le`, `norm_sub_ellTraj'_le`)
with the Strang data of Sobolev states (`cubeFEM_strangData_le_sobolev`), `K₀ = L C₀ h` from an
`L²`-bounded multiplier and `K₁ = K h L` from `M ∈ D(d¹*)`. -/
theorem cErr_le_of_isCubeSob (N : ℕ) {T s L : ℝ} (hs0 : 0 ≤ s) (hL : 0 ≤ L) {x : MS}
    {hx : x ∈ matrixComplex.wave.domainSq} (hd : IsCubeSob T s L hx) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    cErr hT hB N hx T t ≤ cubeSobConst hT hB * L * meshSize N ^ min s 1 ∧
      cErr' hT hB N hx T t ≤ cubeSobConst hT hB * L * meshSize N ^ min s 1 := by
  obtain ⟨hsob, hMd, hmult⟩ := hd t ht
  have hC0 := (cubeFEM_happ0 hT hB).choose_spec
  have hK1 := (exists_cubeFEM_K1 hT hB).choose_spec
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have hm0 : 0 ≤ meshSize N ^ min s 1 := rpow_min_nonneg s N
  have ht' : t ∈ Ico 0 (T + 1) := Icc_sub_Ico_add_one ht
  have HS := bggStability_curlPotentialConst.toHarmonicStability
  have hb : ∀ ε : ℝ, ε = √(cubeCloseConst C * sobStateConst C ^ 2 +
      (cubeFEM_happ0 hT hB).choose ^ 2 + (exists_cubeFEM_K1 hT hB).choose ^ 2) * L *
        meshSize N ^ min s 1 → √(2 * (Feec.BGG.Discrete.strangConst (2 * Real.pi)⁻¹ + 1)) * |ε| =
      cubeSobConst hT hB * L * meshSize N ^ min s 1 := fun ε hε => by
    rw [hε, abs_of_nonneg (by positivity), cubeSobConst]
    ring
  refine ⟨?_, ?_⟩
  · have h := norm_sub_ellTraj_le (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) HS (cubeFEM_compatible hT hB N) (cubeExact hx (T + 1))
      (fun t _ v => srcFun_zero_apply t v) ht'
      (Feec.BGG.Discrete.consistency_S0_of_approx hh hC0.1 hL _ (fun μ => (hmult μ).1)
        (hC0.2 N))
      (fun v hv => hK1.2 N _ L hL (hsob.1.2.2.2.2.1.norm_le hs0) (fun w => (hMd w).1) v hv)
      (cubeFEM_strangData_le_sobolev hT hB N hs0 hsob.1 _ _)
    rw [hb _ rfl] at h
    with_reducible_and_instances exact h
  · have h := norm_sub_ellTraj'_le (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) HS (cubeFEM_compatible hT hB N) (cubeExact hx (T + 1))
      (fun t _ v => srcFun_zero_apply t v) ht'
      (Feec.BGG.Discrete.consistency_S0_of_approx hh hC0.1 hL _ (fun μ => (hmult μ).2)
        (hC0.2 N))
      (fun v hv => hK1.2 N _ L hL (hsob.2.2.2.2.2.1.norm_le hs0) (fun w => (hMd w).2) v hv)
      (cubeFEM_strangData_le_sobolev hT hB N hs0 hsob.2 _ _)
    rw [hb _ rfl] at h
    with_reducible_and_instances exact h

set_option maxHeartbeats 600000 in
/-- **The rate class of relative-class Sobolev data of the thesis' scheme** through the crime
front, of order `min(s, 1)` in `h_N`: data `cubeSobData T s L`, class norm `L`, the elliptic
trajectory (6.4) of the classical solution as comparison (the comparison of the elliptic core
`standardCubeEllCore`), approximation constant `cubeSobConst` and consistency constant
`2 cubeSobConst` (`cErr_le_of_isCubeSob`, `norm_cubeEllCmp_defect_le`). -/
def cubeSobRate (T s L : ℝ) (hs0 : 0 ≤ s) (hL : 0 ≤ L) :
    (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).RateClass T where
  Data := cubeSobData T s L
  p := cubeEllP hT hB T
  p' := cubeEllP' hT hB T
  continuousOn x hx N := (cubeEllCmp hT hB T).continuousOn x hx.1 N
  continuousOn' x hx N := (cubeEllCmp hT hB T).continuousOn' x hx.1 N
  hasDerivWithinAt x hx N := (cubeEllCmp hT hB T).hasDerivWithinAt x hx.1 N
  classNorm _ := L
  meshSize := meshSize
  α := min s 1
  C := cubeSobConst hT hB
  C' := 2 * cubeSobConst hT hB
  approx x hx N t ht := by
    obtain ⟨hx2, hd⟩ := hx
    rw [ApproxFEEC.S_eq_waveGroup _ ht.1]
    have h1 := norm_sub_cubeEllCmp_le hT hB T hx2 N ht
    have h2 := (cErr_le_of_isCubeSob hT hB N hs0 hL hd ht).1
    exact h1.trans (h2.trans_eq (by ring))
  consistency x hx N t ht := by
    obtain ⟨hx2, hd⟩ := hx
    have h1 := norm_cubeEllCmp_defect_le hT hB T hx2 N ht
    obtain ⟨h2, h3⟩ := cErr_le_of_isCubeSob hT hB N hs0 hL hd ht
    unfold DissipFEEC.Comparison.defect
    rw [show (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).L N =
      (standardCubeApprox hT hB).L N from (standardCubeApprox_L_eq hT hB N).symm]
    exact h1.trans (by linarith)

/-! #### Data of `D(L³)` -/

set_option maxHeartbeats 400000 in
/-- **Data of `D(L³)` lie in the Sobolev class at `s = 1`**: if along the forms orbit
`z(t)` of `x` (`cubeOrbit`) on `[0, T]` the state `L² z(t)` lies in `D(L)`, the multipliers of
`z, L z, L² z` are `L²`-bounded by `Λ`, their skew fields are in `D(d²) ∩ D(d¹*)` and the
magnetic rows of `z` in `D(d²)` with bounds `Λ`, then `x ∈ cubeSobData T 1 L` for every
`L ≥ 4 (‖z‖ + ‖L z‖ + ‖L² z‖ + ‖L³ z‖ + Λ)` (`isSobolevStateTr_of_mem` for `z` and `L z`; the
hypotheses of `waveFEM_rate_of_mem_domain_of_orbit`). -/
theorem mem_cubeSobData_of_mem_domain {T Λ L : ℝ} {x : MS}
    (hx : x ∈ matrixComplex.wave.domainSq) (hΛ : 0 ≤ Λ)
    (hL3 : ∀ t ∈ Icc 0 T, waveOf (waveOf (cubeOrbit hx (T + 1) t)) ∈ formsShort.wave.domain)
    (hmult : ∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∀ μ : U1,
      |multOf (aOf (waveOf^[j] (cubeOrbit hx (T + 1) t)))
        (bOf (waveOf^[j] (cubeOrbit hx (T + 1) t))) μ| ≤ Λ * ‖μ‖)
    (hM : ∀ t ∈ Icc 0 T, ∀ j ≤ 2,
      ∃ h2 : compML (waveOf^[j] (cubeOrbit hx (T + 1) t)) ∈ D2min.domain,
      ∃ h1 : compML (waveOf^[j] (cubeOrbit hx (T + 1) t)) ∈ (D1†).domain,
        ‖D2min ⟨_, h2⟩‖ ≤ Λ ∧ ‖D1† ⟨_, h1⟩‖ ≤ Λ)
    (hρ : ∀ t ∈ Icc 0 T, ∀ a, ∃ h : compρL (cubeOrbit hx (T + 1) t) a ∈ D2min.domain,
      ‖D2min ⟨_, h⟩‖ ≤ Λ)
    (hLb : ∀ t ∈ Icc 0 T, 4 * (‖cubeOrbit hx (T + 1) t‖ + ‖waveOf (cubeOrbit hx (T + 1) t)‖ +
      ‖waveOf (waveOf (cubeOrbit hx (T + 1) t))‖ +
        ‖waveOf (waveOf (waveOf (cubeOrbit hx (T + 1) t)))‖ + Λ) ≤ L) :
    x ∈ cubeSobData T 1 L := by
  refine ⟨hx, fun t ht => ?_⟩
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  obtain ⟨hV, hW, -, -⟩ := cubeOrbit_spec hx (T + 1)
  have hz : cubeOrbit hx (T + 1) t ∈ formsShort.wave.domain := hV.mem_domain ht'
  have hLz : waveOf (cubeOrbit hx (T + 1) t) ∈ formsShort.wave.domain := hW.mem_domain ht'
  obtain ⟨hM02, hM01, hM02b, hM01b⟩ := hM t ht 0 (by norm_num)
  obtain ⟨hM12, hM11, hM12b, hM11b⟩ := hM t ht 1 (by norm_num)
  obtain ⟨hM22, hM21, hM22b, hM21b⟩ := hM t ht 2 (by norm_num)
  have hLt := hLb t ht
  have n0 := norm_nonneg (cubeOrbit hx (T + 1) t)
  have n1 := norm_nonneg (waveOf (cubeOrbit hx (T + 1) t))
  have n2 := norm_nonneg (waveOf (waveOf (cubeOrbit hx (T + 1) t)))
  have n3 := norm_nonneg (waveOf (waveOf (waveOf (cubeOrbit hx (T + 1) t))))
  have hΛL : Λ ≤ L := by linarith
  have hL0 : 0 ≤ L := hΛ.trans hΛL
  have hρ' : ∀ a, ∃ h : compρL (waveOf (cubeOrbit hx (T + 1) t)) a ∈ D2min.domain,
      ‖D2min ⟨_, h⟩‖ ≤ Λ := fun a => by
    have e : compρL (waveOf (cubeOrbit hx (T + 1) t)) a =
        D1 (uOf (cubeOrbit hx (T + 1) t) a) :=
      (congrArg (fun y : Wv W2 => y a) (dt1_uOf hz)).symm
    have hd : compρL (waveOf (cubeOrbit hx (T + 1) t)) a ∈ D2min.domain := by
      rw [e]; exact D1_mem_D2min _
    refine ⟨hd, ?_⟩
    have : D2min ⟨_, hd⟩ = D2min ⟨_, D1_mem_D2min (uOf (cubeOrbit hx (T + 1) t) a)⟩ :=
      LinearPMap.apply_congr' _ _ _ e
    rw [this, D2min_D1, norm_zero]; exact hΛ
  have k0 := fun v => LinearPMap.adjoint_isFormalAdjoint dense_D1_domain ⟨_, hM01⟩ v
  have k1 := fun v => LinearPMap.adjoint_isFormalAdjoint dense_D1_domain ⟨_, hM11⟩ v
  refine ⟨⟨(isSobolevStateTr_of_mem hz hLz hΛ (hmult t ht 0 (by norm_num))
      (hmult t ht 1 (by norm_num)) hM02 hM02b hM01 hM01b hM12 hM12b hM11 hM11b (hρ t ht)).mono
        (by linarith),
    (isSobolevStateTr_of_mem hLz (hL3 t ht) hΛ (hmult t ht 1 (by norm_num))
      (hmult t ht 2 (by norm_num)) hM12 hM12b hM11 hM11b hM22 hM22b hM21 hM21b hρ').mono
        (by linarith)⟩, fun v => ⟨?_, ?_⟩, fun μ => ⟨?_, ?_⟩⟩
  · change |⟪compML (waveOf^[0] (cubeOrbit hx (T + 1) t)), D1 v⟫| ≤ _
    rw [← k0 v]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hM01b.trans hΛL) le_rfl
      (norm_nonneg _) hL0)
  · change |⟪compML (waveOf^[1] (cubeOrbit hx (T + 1) t)), D1 v⟫| ≤ _
    rw [← k1 v]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hM11b.trans hΛL) le_rfl
      (norm_nonneg _) hL0)
  · exact (hmult t ht 0 (by norm_num) μ).trans (mul_le_mul_of_nonneg_right hΛL (norm_nonneg _))
  · exact (hmult t ht 1 (by norm_num) μ).trans (mul_le_mul_of_nonneg_right hΛL (norm_nonneg _))

/-! #### The verdict -/

/-- **The inner-product defect of the thesis' scheme vanishes**: `cubeEmb` is isometric. -/
theorem standardCubeComplex_J (N : ℕ) : (standardCubeComplex hT hB).toFamily.J N = 1 :=
  ApproxComplexCrime.Family.ofApproxFEEC_J (standardCubeApprox hT hB)
    (hfd := standardCubeApprox_finiteDimensional hT hB) (cubeD hT hB)
    (cubeD_D hT hB) (standardCubeApprox_isOrthogonal hT hB) N

/-- **The verdict of the scheme (6.5) with the thesis' boundary conditions**: the verdict of the
crime theorem for `standardCubeComplex`, the inner-product defect `0`, the residual at the exact
states equal to the graph-norm error plus the `O(h)` cochain defect, the rates `O(h^{min(s,1)})`
on the Sobolev classes and `O(h)` for data of `D(L³)`, the Gauss constraint of the limits of read
discrete Gauss data, and the verdict of (6.5) identifying the crime front with the scheme, with a
dense core (`StandardCubeApprox.Verdict`). -/
structure StandardCubeComplex.Verdict : Prop extends (standardCubeComplex hT hB).Verdict where
  /-- the inner-product defect is `0` -/
  J_eq_one (N : ℕ) : (standardCubeComplex hT hB).toFamily.J N = 1
  /-- the residual of every approximant at an exact state is its graph-norm error plus
  `(C₀ Λ + K c) h_N`, for an `L²`-bounded multiplier (`Λ`) and `M ∈ D(d¹*)` (`c`) -/
  residual_le_mesh : ∃ C₀ K : ℝ, 0 ≤ C₀ ∧ 0 ≤ K ∧ ∀ (N : ℕ) {x : MS}
    (hx : x ∈ matrixComplex.wave.domainSq) {T t : ℝ}, t ∈ Icc 0 T → ∀ {Λ c : ℝ}, 0 ≤ Λ → 0 ≤ c →
      (∀ μ : U1, |(cubeExact hx (T + 1)).ℓ t μ| ≤ Λ * ‖μ‖) →
      ‖(cubeExact hx (T + 1)).M t‖ ≤ c →
      (∀ w : U1, |⟪(cubeExact hx (T + 1)).M t, segD1 w⟫| ≤ c * ‖w‖) →
      ∀ w v : (standardCubeComplex hT hB).toFamily.X N,
        ‖⟪w - (standardCubeComplex hT hB).toFamily.L N w, v⟫_ℝ -
            ⟪matrixComplex.waveGroup.S t x -
                matrixComplex.wave ⟨_, matrix_waveGroup_mem_domain hx t⟩,
              (standardCubeComplex hT hB).toFamily.incl N v⟫_ℝ‖ ≤
          ((standardCubeComplex hT hB).toFamily.boundConst *
              (‖matrixComplex.waveGroup.S t x - (standardCubeComplex hT hB).toFamily.incl N w‖ +
                ‖matrixComplex.totalD ⟨_, (matrix_waveGroup_mem_domain hx t).1⟩ -
                  (standardCubeComplex hT hB).toFamily.incl N
                    ((standardCubeComplex hT hB).toFamily.D N w)‖) +
            (C₀ * Λ + K * c) * meshSize N) *
          (‖v‖ + ‖(standardCubeComplex hT hB).toFamily.D N v‖)
  /-- the rate `O(L h^{min(s,1)})` for relative-class Sobolev data (`cubeSobRate`), from every
  discrete initial value -/
  rate_sobolev (T s L : ℝ) (hs0 : 0 ≤ s) (hL : 0 ≤ L) {x : MS} (hx : x ∈ cubeSobData T s L)
    (N : ℕ) (v : (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).X N) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖matrixComplex.waveGroup.S t x -
        (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N v t‖ ≤
      (cubeSobConst hT hB + ‖(ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).incl N‖ *
          (2 * cubeSobConst hT hB) * t) * (meshSize N ^ min s 1 * L) +
        ‖(ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).incl N‖ *
          ‖(cubeSobRate hT hB T s L hs0 hL).p x N 0 - v‖
  /-- the rate `O(L h)` for data of `D(L³)` (the hypotheses of `mem_cubeSobData_of_mem_domain`)
  -/
  rate_domain {T Λ L : ℝ} {x : MS} (hx : x ∈ matrixComplex.wave.domainSq) (hΛ : 0 ≤ Λ)
    (hL : 0 ≤ L)
    (hL3 : ∀ t ∈ Icc 0 T, waveOf (waveOf (cubeOrbit hx (T + 1) t)) ∈ formsShort.wave.domain)
    (hmult : ∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∀ μ : U1,
      |multOf (aOf (waveOf^[j] (cubeOrbit hx (T + 1) t)))
        (bOf (waveOf^[j] (cubeOrbit hx (T + 1) t))) μ| ≤ Λ * ‖μ‖)
    (hM : ∀ t ∈ Icc 0 T, ∀ j ≤ 2,
      ∃ h2 : compML (waveOf^[j] (cubeOrbit hx (T + 1) t)) ∈ D2min.domain,
      ∃ h1 : compML (waveOf^[j] (cubeOrbit hx (T + 1) t)) ∈ (D1†).domain,
        ‖D2min ⟨_, h2⟩‖ ≤ Λ ∧ ‖D1† ⟨_, h1⟩‖ ≤ Λ)
    (hρ : ∀ t ∈ Icc 0 T, ∀ a, ∃ h : compρL (cubeOrbit hx (T + 1) t) a ∈ D2min.domain,
      ‖D2min ⟨_, h⟩‖ ≤ Λ)
    (hLb : ∀ t ∈ Icc 0 T, 4 * (‖cubeOrbit hx (T + 1) t‖ + ‖waveOf (cubeOrbit hx (T + 1) t)‖ +
      ‖waveOf (waveOf (cubeOrbit hx (T + 1) t))‖ +
        ‖waveOf (waveOf (waveOf (cubeOrbit hx (T + 1) t)))‖ + Λ) ≤ L)
    (N : ℕ) (v : (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).X N) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖matrixComplex.waveGroup.S t x -
        (ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).sol N v t‖ ≤
      (cubeSobConst hT hB + ‖(ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).incl N‖ *
          (2 * cubeSobConst hT hB) * t) * (meshSize N * L) +
        ‖(ApproxFEEC.ofComplexCrime (standardCubeComplex hT hB)).incl N‖ *
          ‖(cubeSobRate hT hB T 1 L zero_le_one hL).p x N 0 - v‖
  /-- the limits of read discrete Gauss data keep the continuous Gauss constraint -/
  gauss {x : MS} {v : ∀ N, cubeHidden hT hB N} (hv : ∀ N, v N ∈ cubeHiddenGauss hT hB N)
    (hconv : Tendsto (fun N => cubeEmb hT hB N (v N)) atTop (𝓝 x)) {t : ℝ} (ht : 0 ≤ t) :
    cubeRead (matrixComplex.waveGroup.S t x) ∈ cubeGauss
  /-- the verdict of (6.5): the discrete solutions of the crime front are those of (6.5), the core
  is dense (so the field `perturbed` applies), and `thesisTSD` is not reducing -/
  scheme : StandardCubeApprox.Verdict hT hB

set_option maxHeartbeats 1200000 in
/-- **The scheme (6.5) with the thesis' boundary conditions is an instance of the crime crown**
(`ApproxComplexCrime.feec`) with a dense core, the cochain defect `O(h)` and rates
`O(h^{min(s,1)})`. [QuennevilleBelair2015], §6.3, (6.5), Table 6.1; [HolstStern2012], §3 -/
theorem standardCubeComplex_verdict : StandardCubeComplex.Verdict hT hB where
  toVerdict := (standardCubeComplex hT hB).feec
  J_eq_one := standardCubeComplex_J hT hB
  residual_le_mesh := by
    obtain ⟨C₀, K, hC₀, hK, hd⟩ := exists_standardCube_cochainDefect_le_mesh hT hB
    refine ⟨C₀, K, hC₀, hK, fun N x hx T t ht Λ c hΛ hc hℓ hM hMd w v => ?_⟩
    have h := (standardCubeComplex hT hB).feec.residual_le N
      ⟨_, matrix_waveGroup_mem_domain hx t⟩ w (δ := (C₀ * Λ + K * c) * meshSize N)
      (fun v => (Real.norm_eq_abs _).trans_le (hd N hx ht hΛ hc hℓ hM hMd v)) v
    simpa only [standardCubeComplex_J, sub_self, _root_.zero_apply, norm_zero, zero_add] using h
  rate_sobolev T s L hs0 hL _ hx N v _ ht := by
    have h := (standardCubeComplex hT hB).feec.wave.rate (cubeSobRate hT hB T s L hs0 hL) hx N v ht
    rw [ApproxFEEC.S_eq_waveGroup _ ht.1] at h
    exact h
  rate_domain hx hΛ hL hL3 hmult hM hρ hLb N v _ ht := by
    have h := (standardCubeComplex hT hB).feec.wave.rate (cubeSobRate hT hB _ 1 _ zero_le_one hL)
      (mem_cubeSobData_of_mem_domain hx hΛ hL3 hmult hM hρ hLb) N v ht
    rw [ApproxFEEC.S_eq_waveGroup _ ht.1] at h
    have e : meshSize N ^ min (1 : ℝ) 1 = meshSize N := by rw [min_self, Real.rpow_one]
    change _ ≤ (cubeSobConst hT hB + _ * (2 * cubeSobConst hT hB) * _) *
      (meshSize N ^ min (1 : ℝ) 1 * _) + _ at h
    rwa [e] at h
  gauss hv hconv _ ht := standardCube_waveGroup_mem_cubeGauss hT hB hv hconv ht
  scheme := standardCubeApprox_verdict hT hB

end Cube

/-! ### Summary -/

set_option maxHeartbeats 800000 in
open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry in
/-- **The scheme (6.5) under the crown** ([QuennevilleBelair2015], §6.3, (6.5), Table 6.1): with
mirror boundary conditions, admissible parity smoothers exist, the non-stationary TSD datum
`cosDatum` lies in the `O(h)` rate class and in every `O(hˢ)` rate class, and for each smoother
the scheme satisfies `MirrorComplex.Verdict`; with the thesis' boundary conditions, smoothers for
Table 6.1 exist with (5.4), uniform bounds `2C`, `d̃⁰` injective and `S₀,ₕ` onto
(`WaveFEM.waveFEM_cube`, unconditional in the regularity hypothesis), and for each smoother the
scheme satisfies `StandardCubeComplex.Verdict` (its rate classes are not shown to contain a
non-stationary datum). Both apply the crime theorem `ApproxComplexCrime.feec`. -/
theorem einsteinBianchiFEM_crown :
    ((∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
        ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
          ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) ∧
      Feec.Models.Cube.MirrorWeakSymmetry.cosDatum.U₀ ∈ mirrorL3Data ∧
      (∀ s, Feec.Models.Cube.MirrorWeakSymmetry.cosDatum.U₀ ∈ mirrorSobData s) ∧
      ∀ {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
        (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
        (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C),
        MirrorComplex.Verdict hT hB) ∧
    ((∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
        (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
        (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
        (∀ N, (cubeFEM hT hB N).Compatible ∧ (cubeFEM hT hB N).Bounded (2 * C)) ∧
        ∀ N, Function.Injective (cubeWave hT hB N).dt0 ∧
          Function.Surjective (cubeWave hT hB N).S0) ∧
      ∀ {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
        (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
        (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
        StandardCubeComplex.Verdict hT hB) := by
  obtain ⟨p, C, hT, hB, h1, h2, -⟩ := Feec.EinsteinBianchi.WaveFEM.waveFEM_cube
  exact ⟨⟨Feec.Models.Cube.MirrorWeakSymmetry.exists_mirror_estimates, cosDatum_mem_mirrorL3Data,
      cosDatum_mem_mirrorSobData, fun hT hB => mirrorComplex_verdict hT hB⟩,
    ⟨⟨p, C, hT, hB, h1, h2⟩, fun hT hB => standardCubeComplex_verdict hT hB⟩⟩

end Feec.Instances.EinsteinBianchi.FEM
