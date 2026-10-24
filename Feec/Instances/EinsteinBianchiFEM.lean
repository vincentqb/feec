module

public import Feec.Instances.EinsteinBianchiFEMMirrorEll
public import Feec.Instances.EinsteinBianchiFEMCubeEll
public import Feec.Instances.EuclideanBand

/-!
# The thesis' scheme (6.5) as an instance of the approximating FEEC theorem

The finite element scheme (6.5) of [QuennevilleBelair2015], §6.3, is not a discretization by
subcomplexes: its discrete complex couples the two rows of the BGG construction by
`S₀,ₕ = π¹S⁰ ≠ S⁰` (a variational crime, [HolstStern2012]), so it is not an instance of the
constrained FEEC theorem (`Feec.HilbertComplex.constrainedFEEC`). It is an instance of the
**approximating FEEC theorem** `Feec.HilbertComplex.approxFEEC` (statement
`Feec.HilbertComplex.ApproxFEEC.Verdict`), with both boundary conditions:

* **mirror boundary conditions**: the discretization
  `Feec.Instances.EinsteinBianchi.FEM.mirrorFEMApprox` of the real mirror BGG complex
  (`complexQℝ`) with the TSD constraint `tsdQℝ`, which reduces `L`;
* **the thesis' boundary conditions**: the discretization
  `Feec.Instances.EinsteinBianchi.FEM.standardCubeApprox` of the matrix model with the TSD
  constraint `thesisTSD`, which does not reduce `L`.

In both instances the discrete solutions of the approximating discretization are the solutions
of (6.5) without source (`mirrorFEMApprox_sol_eq_scheme`, `standardCube_sol_eq_scheme`).

**Elliptic cores: best approximation plus consistency.** The headline cores are `mirrorEllCore` and
`standardCubeEllCore` (`einsteinBianchi_mirrorFEM_approxFEEC_elliptic`,
`einsteinBianchi_standardCube_approxFEEC_elliptic`): the comparison trajectory of a datum is the
elliptic projection (6.4) of its exact solution (`Feec.Instances.EinsteinBianchi.FEM.ellTraj`),
whose consistency defect `Πₕ' - Lₕ Πₕ` is bounded by the projection errors of the state and of its
time derivative (`norm_ellDefect_le`; that it is nonzero is not proved, see below). The core
hypotheses are discharged by the Strang bound of (6.4) and the convergence of the smoothed
projections; the model convergence theorems of (6.5) (`mirror_waveFEM`, `cubeWave_converges`, the
mirror rate theorems) are not used. For mirror data, the elliptic rate classes give, from the
thesis' horizon-free initialization `Πₕ(0)` (`mirrorEllInit`, `mEll_zero_toEState`), for all
`t ≥ 0`, `‖e^{tL} ξ₀ - ι' e^{tL'} Πₕ(0)‖ ≤ (4K + 8K t) h_N ‖ξ₀‖_{L³}` for TSD data of `D(L³)`
and `≤ (6K + 12K t) h_Nˢ ‖ξ₀‖_{2+s}` for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1`
(`einsteinBianchi_mirrorFEM_rate_init`, `einsteinBianchi_mirrorFEM_rate_sobolev_init`;
`K = mirrorEllK`).

**The model verdict of the mirror scheme is a corollary.** Reading off the real part
(`tsdErr_le_norm_sub_mirrorReEmb`) and identifying the discrete solution with (6.5) from (6.4)
(`exists_mirrorScheme_le_of_eq`), the elliptic instance gives the model statements
`MirrorWaveFEMConvergence`, `MirrorWaveFEMRate` (constant `8K`) and `MirrorWaveFEMRateSobolev`
(constant `12K`), hence `MirrorFEMVerdict` (`mirrorFEMVerdict_of_approxFEEC`), without
`mirror_waveFEM` or the model rate theorems. `einsteinBianchi_summary` uses this proof for its
mirror finite element row.

**Orbit cores** (`mirrorFEMCore`, `standardCubeCore`) are kept: the comparison trajectory is the
discrete orbit from the orthogonal projection (zero defect,
`Feec.HilbertComplex.ApproxFEEC.orbitCore`), and the approximation hypothesis is the model
convergence theorem, with which the orthogonal projection competes by best approximation
(`ApproxFEEC.IsOrthogonal.norm_sub_sol_proj_le`); their rate classes have the constants
`6 K' (1 + T)` (a factor `3` from the orthogonal projection, `1 + T` for `1 + t`) and an initial
mismatch `‖π' ξ₀ - v‖` (`einsteinBianchi_mirrorFEM_rate`), weaker than the elliptic rates. The
named convergence and residual corollaries (`einsteinBianchi_mirrorFEM_converges`,
`einsteinBianchi_standardCube_converges`, `standardCube_residual_not_mem`,
`standardCube_residual_not_isReducing`) go through the elliptic cores, which have the same
closures.

What the approximating FEEC theorem adds to the model theorems: complex data (real and imaginary
parts), the closure of the core (all TSD data, resp. all data, not only `D(L²)`), every convergent
family of initial values, and the constraint residual in both directions: for mirror data the
residual tends to `0`; for the thesis' boundary conditions, the non-reducing branch of the verdict
gives a datum of `thesisTSD` or of its complement left by the exact solution, whose residuals tend
to a positive limit (`standardCube_residual_not_isReducing`, which consumes only `¬ IsReducing`,
itself proved from the explicit datum via `not_isReducing_thesisTSD`), and at the explicit TSD datum
`(0, 0, (0, β))` the residuals tend to `dist(e^{tL}(0, 0, (0, β)), TSD) > 0`
(`standardCube_residual_not_mem`). The verdict's clauses for data of `D(L) ∩ K` (a datum of `K`
itself leaving `K`, forward in time on graded complexes) assume `D(L) ∩ K` dense in `K`; for
`K = thesisTSD` this fails by the density gap of Prop 4.17
(`exists_mem_thesisTSD_not_mem_closure`), so they do not apply.

**Faithfulness caveat.** The (6.5) instances are faithful to `cubeWave`/`mirrorWave` (the
scheme (6.5) with `S₀,ₕ = π¹S⁰` for the smoothed, resp. parity-smoothed, cochain projections), not
to the variant with the canonical interpolant `Π`. That the consistency defect is nonzero, or
that `ιₙ Xₙ` is not `L`-invariant, is not proved for any datum (it would need an explicit finite
element computation with the smoothed projections); for mirror TSD data the consistency terms of
the Strang bound vanish (`K₀ = K₁ = 0`), so a defect there could only come from the elliptic
projection not commuting with the flow. Both reading maps are isometric, so the non-isometric
generality of `approxFEEC` is exercised only by the abstract witnesses
(`Feec.HilbertComplex.Approximation.ApproxFEECWitness`). The componentwise failure on the
thesis' boundary conditions (`Eₕ ∉ L²(TSD)`, `Bₕ` not symmetric) enters through the model
`StandardCubeVerdict`.

`einsteinBianchi_summary` is the statement of
`Feec.Instances.EinsteinBianchi.einsteinBianchi_constrainedFEEC_summary` (with its mirror finite
element row proved by `mirrorFEMVerdict_of_approxFEEC`, and its propagation-only `ℝ³` row
`EuclideanVerdict` replaced by the approximating FEEC verdict of the frequency truncation,
`Feec.Instances.EuclideanBand.EuclideanEBVerdict`, from `einsteinBianchi_euclidean_band`) together
with `MirrorFEMApproxVerdict` and `StandardCubeApproxVerdict`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.17, §6.3 ((6.5), Table 6.1)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  Thm 3.9, Thm 3.10 (elliptic analogue)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi

open Feec.HilbertComplex Feec.Instances.EinsteinBianchi.FEM

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### Mirror boundary conditions -/

section MirrorFEM

open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.FEM (ParitySmoothingEstimates meshSize)
open Feec.FiniteElement (PolySeq)
open Feec.Models.Cube.MirrorBGG (SpaceQ)

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **The mirror scheme (6.5) is an instance of the approximating FEEC theorem.**
[QuennevilleBelair2015], §6.3, (6.5) -/
theorem einsteinBianchi_mirrorFEM_approxFEEC :
    (mirrorFEMApprox hT hB).Verdict (mirrorFEMCore hT hB) :=
  approxFEEC _ _

/-- **Convergence of the mirror scheme (6.5) to the TSD solution** (the convergence clause of the
verdict of the elliptic core `mirrorEllCore`, read off its fields, on its
closure `tsdQℝ`, with the propagation and reducing-residual clauses for the reducing
constraint; no model convergence theorem is used): for every TSD datum
`ξ₀ ∈ L²` (complex fields) the exact solution stays TSD for all `t`, the orthogonal projections
`ι' π' ξ₀` converge to `ξ₀`, and for every family of discrete initial values with `ι' vₙ → ξ₀`
the discrete solutions (the real and imaginary parts running (6.5)) converge to `e^{tL} ξ₀` and
the constraint residuals to `0`, uniformly on `[0, T]`. -/
theorem einsteinBianchi_mirrorFEM_converges {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ) (T : ℝ) :
    (∀ t, complexQℝ.waveGroup.S t x ∈ tsdQℝ) ∧
    Tendsto (fun N => (mirrorFEMApprox hT hB).incl N ((mirrorFEMApprox hT hB).proj N x)) atTop
      (𝓝 x) ∧
    ∀ v : ∀ N, (mirrorFEMApprox hT hB).X N,
      Tendsto (fun N => (mirrorFEMApprox hT hB).incl N (v N)) atTop (𝓝 x) →
      TendstoUniformlyOn (fun N t => (mirrorFEMApprox hT hB).sol N (v N) t)
        (fun t => complexQℝ.waveGroup.S t x) atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun N t => infDist ((mirrorFEMApprox hT hB).sol N (v N) t)
        (tsdQℝ : Set (PiLp 2 SpaceQ))) (fun _ => 0) atTop (Icc 0 T) := by
  have V := einsteinBianchi_mirrorFEM_approxFEEC_elliptic hT hB
  have hxc : x ∈ (mirrorEllCore hT hB).Data.topologicalClosure := by
    rw [mirrorEllCore_closure]; exact hx
  refine ⟨fun t => V.isReducing_iff_invariant.1 isReducing_tsdQℝ t x hx, V.tendsto_incl_proj hxc,
    fun v hv => ⟨(V.converges hxc hv T).congr_right fun t ht => ApproxFEEC.S_apply _ ht.1 x,
      V.residual_tendsto (V.isReducing_iff.1 isReducing_tsdQℝ).1 hx hxc hv T⟩⟩

/-- **The `O(h)` rate of the mirror scheme (6.5) for TSD data of `D(L³)`** (the rate clause of the verdict
for the rate class `mirrorFEMRate`): for every discrete initial value `v`,
`‖e^{tL} ξ₀ - ι' e^{tL'} v‖ ≤ 6 K (1 + T) h_N ‖ξ₀‖_{L³} + ‖π' ξ₀ - v‖` on `[0, T]`, where
`‖ξ₀‖_{L³} = ‖ξ₀‖ + ‖Lξ₀‖ + ‖L²ξ₀‖ + ‖L³ξ₀‖` and `K` is the constant of
`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`. -/
theorem einsteinBianchi_mirrorFEM_rate {T : ℝ} (hT0 : 0 < T) {x : PiLp 2 SpaceQ}
    (hx : x ∈ mirrorL3Data) (N : ℕ) (v : (mirrorFEMApprox hT hB).X N) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
      3 * (2 * mirrorRateK hT hB * (1 + T)) * (meshSize N * mirrorL3Norm x) +
        ‖(mirrorFEMApprox hT hB).proj N x - v‖ := by
  have h := (einsteinBianchi_mirrorFEM_approxFEEC hT hB).rate (mirrorFEMRate hT hB T hT0) hx N v ht
  simp only [ApproxFEEC.S_apply (mirrorFEMApprox hT hB) ht.1] at h
  have hp : (mirrorFEMRate hT hB T hT0).p x N 0 = (mirrorFEMApprox hT hB).proj N x :=
    C0Group.S_zero_apply _ _
  have hι := (mirrorFEMApprox_isOrthogonal hT hB).norm_incl_le_one N
  have hC : (mirrorFEMRate hT hB T hT0).C = 3 * (2 * mirrorRateK hT hB * (1 + T)) := rfl
  have hC' : (mirrorFEMRate hT hB T hT0).C' = 0 := rfl
  have hm : (mirrorFEMRate hT hB T hT0).meshSize N ^ (mirrorFEMRate hT hB T hT0).α *
      (mirrorFEMRate hT hB T hT0).classNorm x = meshSize N * mirrorL3Norm x := by
    change meshSize N ^ (1 : ℝ) * mirrorL3Norm x = _
    rw [Real.rpow_one]
  simp only [hC, hC', hm, hp, mul_zero, zero_mul, add_zero] at h
  have hn := norm_nonneg ((mirrorFEMApprox hT hB).proj N x - v)
  linarith [mul_le_of_le_one_left hn hι]

/-- **The `O(hˢ)` rate of the mirror scheme (6.5) for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1`** (the rate clause
of the verdict for the rate class `mirrorFEMRateSobolev`): for every discrete initial value `v`,
`‖e^{tL} ξ₀ - ι' e^{tL'} v‖ ≤ 6 K (1 + T) h_Nˢ ‖ξ₀‖_{2+s} + ‖π' ξ₀ - v‖` on `[0, T]`, `K` the
constant of `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`. -/
theorem einsteinBianchi_mirrorFEM_rate_sobolev {T s : ℝ} (hT0 : 0 < T) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) (N : ℕ)
    (v : (mirrorFEMApprox hT hB).X N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
      3 * (2 * mirrorSobK hT hB * (1 + T)) * (meshSize N ^ s * √(sobState (2 + s) x)) +
        ‖(mirrorFEMApprox hT hB).proj N x - v‖ := by
  have h := (einsteinBianchi_mirrorFEM_approxFEEC hT hB).rate
    (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1) hx N v ht
  simp only [ApproxFEEC.S_apply (mirrorFEMApprox hT hB) ht.1] at h
  have hp : (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).p x N 0 =
      (mirrorFEMApprox hT hB).proj N x := C0Group.S_zero_apply _ _
  have hι := (mirrorFEMApprox_isOrthogonal hT hB).norm_incl_le_one N
  have hC : (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).C =
      3 * (2 * mirrorSobK hT hB * (1 + T)) := rfl
  have hC' : (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).C' = 0 := rfl
  have hm : (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).meshSize N ^
      (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).α *
      (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).classNorm x =
        meshSize N ^ s * √(sobState (2 + s) x) := rfl
  simp only [hC, hC', hm, hp, mul_zero, zero_mul, add_zero] at h
  have hn := norm_nonneg ((mirrorFEMApprox hT hB).proj N x - v)
  linarith [mul_le_of_le_one_left hn hι]

/-- **Non-vacuity of the mirror rate classes**: the TSD datum `cosDatum`
(`E₀ = 2 cos(2π x₃) diag(1, -1, 0)` on `Q`, not stationary) lies in `D(L³)` and in every
`H^{2+s}`. -/
theorem cosDatum_mem_mirrorL3Data : cosDatum.U₀ ∈ mirrorL3Data := by
  have hx : cosDatum.U₀ ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq := by
    refine ⟨cosDatum.tsd, LinearPMap.mem_domainSq.2 ⟨mem_complexQℝ_domain.2 cosDatum.mem, ?_⟩⟩
    rw [complexQℝ_wave_apply]
    exact mem_complexQℝ_domain.2 cosDatum.mem₂
  exact ⟨hx, cosDatum_LLU₀_mem⟩

theorem cosDatum_mem_mirrorSobData (s : ℝ) : cosDatum.U₀ ∈ mirrorSobData s :=
  ⟨cosDatum_mem_mirrorL3Data.1, cosDatum_memSobState (2 + s)⟩

/-! #### The model verdict of the mirror scheme as a corollary -/

section ModelCorollary

open Feec.Models.Cube.RowWise
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)
open Feec.Models.Cube.FEM (meshSize_pos)

/-- Every TSD datum is a datum of the elliptic core. -/
theorem mem_mirrorEllData_of_tsdDatum (D : TSDDatum) : D.U₀ ∈ mirrorEllData :=
  ⟨D.tsd, LinearPMap.mem_domainSq.2 ⟨mem_complexQℝ_domain.2 D.mem, by
    rw [complexQℝ_wave_apply]; exact mem_complexQℝ_domain.2 D.mem₂⟩⟩

/-- The source of (6.5) for `f = 0` vanishes. -/
theorem mirrorSource_zero (N : ℕ) : mirrorSource hT hB N 0 = 0 := by
  funext t
  simp [mirrorSource]

set_option maxHeartbeats 4000000 in
/-- **The real part of the instance is the scheme (6.5) from (6.4)**: for a TSD datum and a source
`f = 0`, the solution of (6.5) from the elliptic projection (6.4) of the exact initial state has,
at each `t ∈ [0, T]`, four-term error against `Re e^{tL} ξ₀` at most the error
`‖e^{tL} ξ₀ - ι' e^{tL'} Πₕ(0)‖` of the approximating FEEC discretization. -/
theorem exists_mirrorScheme_le_of_eq (N : ℕ) (D : TSDDatum) {T : ℝ} (hT0 : 0 < T)
    (f : ℝ → (mirrorFEM hT hB N).Vt1h) (hf : f = 0) :
    ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T f,
      (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
        (Feec.BGG.ellipticProjection (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
          (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
          (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH ((D.exactWave T).σ 0)
            ((D.exactWave T).φ 0) ((D.exactWave T).u 0) ((D.exactWave T).M 0)
            ((D.exactWave T).ρ 0) ((D.exactWave T).ℓ 0)) 0)).1.1 ∧
      ∀ t ∈ Icc 0 T, √(‖(sh.σ t : TU0)‖ ^ 2 +
        ‖rowsW1L (stEL (Models.Cube.MirrorBGG.complexQ.waveGroup.S t D.U₀)) -
          bIncl1 (sh.u t : BU1)‖ ^ 2 + ‖(sh.M t : W2)‖ ^ 2 +
        ‖rowsW2L (stBL (Models.Cube.MirrorBGG.complexQ.waveGroup.S t D.U₀)) -
          (sh.ρ t : Wv W2)‖ ^ 2) ≤
        ‖complexQℝ.waveGroup.S t D.U₀ -
          (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB D.U₀ N) t‖ := by
  subst hf
  have hx := mem_mirrorEllData_of_tsdDatum D
  have key := mirrorFEMApprox_sol_eq_scheme hT hB N hT0 (mEll hT hB N D 0 0)
    (mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) 0 0)
  refine key.elim fun s h1 => h1.elim fun s' h2 => ?_
  have hs := h2.1
  have hsol := h2.2.2
  have hinit : mirrorEllInit hT hB D.U₀ N = WithLp.toLp 2 (mEll hT hB N D 0 0,
      mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) 0 0) := mirrorEllCmp_p_zero hT hB 0 hx N
  refine ⟨s, ?_, fun t ht => ?_⟩
  · apply EState.mkL.injective
    exact (congrArg HiddenState.toEState (hs.trans (mEll_horizon hT hB N D 0 T 0))).trans
      (mEll_zero_toEState hT hB N D (T := T) hT0.le)
  · have e : (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB D.U₀ N) t =
        mirrorReEmb (dState hT hB N s t) + mulI (mirrorReEmb (dState hT hB N s' t)) :=
      (congrArg (fun v => (mirrorFEMApprox hT hB).sol N v t) hinit).trans (hsol t ht)
    rw [e, complexQℝ_waveGroup ht.1, mulI_apply, ← sub_sub]
    refine le_of_eq_of_le ?_ (tsdErr_le_norm_sub_mirrorReEmb (D.U_tsd t) (dState hT hB N s t)
      (dState hT hB N s' t))
    unfold tsdErr
    rw [EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk]
    rfl


set_option maxHeartbeats 4000000 in
/-- **`MirrorWaveFEMRate` from the approximating FEEC theorem** (constant `8 mirrorEllK`), through
`einsteinBianchi_mirrorFEM_rate_init`; the model rate theorem is not used. -/
theorem mirrorWaveFEMRate_of_approxFEEC : MirrorWaveFEMRate hT hB := by
  refine ⟨8 * mirrorEllK (C := C), by have := mirrorEllK_nonneg hT (C := C); positivity, ?_⟩
  intro N D h3 T hT0
  refine (exists_mirrorScheme_le_of_eq hT hB N D hT0 _ (mirrorSource_zero hT hB N)).elim
    fun sh hsh => ⟨sh, hsh.1, fun t ht => (hsh.2 t ht).trans ?_⟩
  have hx := mem_mirrorEllData_of_tsdDatum D
  have hr := einsteinBianchi_mirrorFEM_rate_init hT hB (x := D.U₀) ⟨hx, h3⟩ N ht.1
  rw [mirrorL3Norm_of_mem hx h3] at hr
  refine hr.trans ?_
  have hK := mirrorEllK_nonneg hT (C := C)
  have hn : 0 ≤ l3Norm (tsdDatumOf hx) h3 := l3Norm_nonneg _ _
  have hh := (meshSize_pos N).le
  have e : l3Norm (tsdDatumOf hx) h3 = ‖D.U₀‖ + ‖D.LU₀‖ + ‖D.LLU₀‖ +
      ‖Models.Cube.MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩‖ := rfl
  rw [← e]
  nlinarith [mul_nonneg (mul_nonneg hK hh) hn, mul_nonneg (mul_nonneg (mul_nonneg hK hh) hn) ht.1]

set_option maxHeartbeats 4000000 in
/-- **`MirrorWaveFEMRateSobolev` from the approximating FEEC theorem** (constant `12 mirrorEllK`),
through `einsteinBianchi_mirrorFEM_rate_sobolev_init`. -/
theorem mirrorWaveFEMRateSobolev_of_approxFEEC : MirrorWaveFEMRateSobolev hT hB := by
  refine ⟨12 * mirrorEllK (C := C), by have := mirrorEllK_nonneg hT (C := C); positivity, ?_⟩
  intro N D s hs0 hs1 hD T hT0
  refine (exists_mirrorScheme_le_of_eq hT hB N D hT0 _ (mirrorSource_zero hT hB N)).elim
    fun sh hsh => ⟨sh, hsh.1, fun t ht => (hsh.2 t ht).trans ?_⟩
  have hr := einsteinBianchi_mirrorFEM_rate_sobolev_init hT hB hs0 hs1
    (x := D.U₀) ⟨mem_mirrorEllData_of_tsdDatum D, hD⟩ N ht.1
  refine hr.trans ?_
  have hK := mirrorEllK_nonneg hT (C := C)
  have hh := Real.rpow_nonneg (meshSize_pos N).le s
  have hn := Real.sqrt_nonneg (sobState (2 + s) D.U₀)
  nlinarith [mul_nonneg (mul_nonneg hK hh) hn, mul_nonneg (mul_nonneg (mul_nonneg hK hh) hn) ht.1]

set_option maxHeartbeats 4000000 in
/-- **`MirrorWaveFEMConvergence` from the approximating FEEC theorem**: convergence on the core (`DissipFEEC.Verdict.converges` from the comparison initial
values), for
the elliptic core (`mirror_waveFEM` is not used). -/
theorem mirrorWaveFEMConvergence_of_approxFEEC : MirrorWaveFEMConvergence hT hB := by
  intro D T hT0 ε hε
  refine ⟨fun t _ => D.U_tsd t, ?_⟩
  have hx := mem_mirrorEllData_of_tsdDatum D
  have hconv := ((einsteinBianchi_mirrorFEM_approxFEEC_elliptic hT hB).converges
    (Submodule.le_topologicalClosure _ hx) ((mirrorEllCore hT hB).tendsto_incl_p hT0.le hx)
    T).congr_right fun t ht => ApproxFEEC.S_apply _ ht.1 D.U₀
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  filter_upwards [hconv ε hε] with N hN
  refine (exists_mirrorScheme_le_of_eq hT hB N D hT0 _ (mirrorSource_zero hT hB N)).elim
    fun sh hsh => ⟨sh, hsh.1, fun t ht => ?_⟩
  have h2 : ‖complexQℝ.waveGroup.S t D.U₀ -
      (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB D.U₀ N) t‖ ≤ ε := by
    have h := hN t ht
    rw [dist_eq_norm] at h
    rw [← mirrorEllCmp_p_zero_eq_init hT hB T]
    exact h.le
  exact tsd_bounds ((hsh.2 t ht).trans h2)
    (Models.Cube.MirrorBGG.tsd_of_mem_tsdQ (D.U_tsd t)).2.2.2.1

/-- **The model verdict of the mirror scheme (6.5) is a corollary of the approximating FEEC
theorem.** -/
theorem mirrorFEMVerdict_of_approxFEEC : MirrorFEMVerdict :=
  ⟨exists_mirror_estimates, fun hT hB => ⟨mirrorWaveFEMConvergence_of_approxFEEC hT hB,
    mirrorWaveFEMRate_of_approxFEEC hT hB, mirrorWaveFEMRateSobolev_of_approxFEEC hT hB⟩⟩

end ModelCorollary

/-- **The verdict of the approximating FEEC theorem on the mirror scheme (6.5)**: admissible parity
smoothers exist; the model verdict `MirrorFEMVerdict` holds, as a corollary of the elliptic
instance (`mirrorFEMVerdict_of_approxFEEC`); and for each admissible smoother
1. the full verdict `ApproxFEEC.Verdict` of `mirrorFEMApprox` with the orbit core `mirrorFEMCore`;
2. the closure of the core is the TSD constraint, which reduces `L`;
3. for every TSD datum, the exact solution stays TSD, `ι' π' ξ₀ → ξ₀`, and every convergent family
   of discrete initial values gives discrete solutions converging to `e^{tL} ξ₀` with residuals
   tending to `0`, uniformly on `[0, T]` (proved through the elliptic core);
4. the orbit rates (weaker than item 7): `O(h)` for TSD data of `D(L³)` and `O(hˢ)` for TSD data
   in `H^{2+s}`, `0 ≤ s ≤ 1`, from any initial value `v`, with the constant `6 K' (1 + T)` and the
   mismatch `‖π' ξ₀ - v‖`;
5. the discrete solutions are the solutions of (6.5) without source (real and imaginary parts);
6. **the elliptic core** (best approximation plus consistency with a bounded consistency defect,
   no model convergence theorem used): the full verdict with `mirrorEllCore`, whose closure is the
   TSD constraint;
7. **the elliptic rates from the thesis' initialization (6.4)**: the comparison initial value does
   not depend on the horizon and is the pair of elliptic projections (6.4) of the real and
   imaginary parts of the exact initial state (`mirrorEllInit`), and from it, for all `t ≥ 0`, the
   error is `≤ (4K + 8K t) h_N ‖ξ₀‖_{L³}` for TSD data of `D(L³)` and
   `≤ (6K + 12K t) h_Nˢ ‖ξ₀‖_{2+s}` for TSD data in `H^{2+s}`, `K = mirrorEllK`;
non-vacuity: the non-stationary TSD datum `cosDatum` lies in both rate classes. -/
abbrev MirrorFEMApproxVerdict : Prop :=
  (∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
      ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
        ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) ∧
    (cosDatum.U₀ ∈ mirrorL3Data ∧ (∀ s, cosDatum.U₀ ∈ mirrorSobData s) ∧
      cosDatum.U₀ ∉ Feec.Models.Cube.MirrorBGG.complexQ.waveGroup.stationary) ∧
    -- the model verdict, as a corollary of the elliptic instance
    MirrorFEMVerdict ∧
    ∀ {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
      (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
      (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C),
      -- 1. the verdict
      (mirrorFEMApprox hT hB).Verdict (mirrorFEMCore hT hB) ∧
      -- 2. the closure of the core, the reducing constraint
      (mirrorFEMCore hT hB).Data.topologicalClosure = tsdQℝ ∧ complexQℝ.wave.IsReducing tsdQℝ ∧
      -- 3. convergence to the TSD solution, residual → 0
      (∀ x ∈ tsdQℝ, ∀ T : ℝ, (∀ t, complexQℝ.waveGroup.S t x ∈ tsdQℝ) ∧
        Tendsto (fun N => (mirrorFEMApprox hT hB).incl N ((mirrorFEMApprox hT hB).proj N x))
          atTop (𝓝 x) ∧
        ∀ v : ∀ N, (mirrorFEMApprox hT hB).X N,
          Tendsto (fun N => (mirrorFEMApprox hT hB).incl N (v N)) atTop (𝓝 x) →
          TendstoUniformlyOn (fun N t => (mirrorFEMApprox hT hB).sol N (v N) t)
            (fun t => complexQℝ.waveGroup.S t x) atTop (Icc 0 T) ∧
          TendstoUniformlyOn (fun N t => infDist ((mirrorFEMApprox hT hB).sol N (v N) t)
            (tsdQℝ : Set (PiLp 2 SpaceQ))) (fun _ => 0) atTop (Icc 0 T)) ∧
      -- 4. orbit rates
      (∀ {T : ℝ}, 0 < T → ∀ x ∈ mirrorL3Data, ∀ (N : ℕ) (v : (mirrorFEMApprox hT hB).X N),
        ∀ t ∈ Icc 0 T, ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
          3 * (2 * mirrorRateK hT hB * (1 + T)) * (meshSize N * mirrorL3Norm x) +
            ‖(mirrorFEMApprox hT hB).proj N x - v‖) ∧
      (∀ {T s : ℝ}, 0 < T → 0 ≤ s → s ≤ 1 → ∀ x ∈ mirrorSobData s, ∀ (N : ℕ)
        (v : (mirrorFEMApprox hT hB).X N), ∀ t ∈ Icc 0 T,
        ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
          3 * (2 * mirrorSobK hT hB * (1 + T)) * (meshSize N ^ s * √(sobState (2 + s) x)) +
            ‖(mirrorFEMApprox hT hB).proj N x - v‖) ∧
      -- 5. the discrete solutions are (6.5)
      (∀ (N : ℕ) {T : ℝ} (hT0 : 0 < T) (a b : mirrorHidden hT hB N),
        ∃ s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T 0,
          DiscreteSolution.hiddenInit hT0.le s = a ∧ DiscreteSolution.hiddenInit hT0.le s' = b ∧
          ∀ t ∈ Icc 0 T, (mirrorFEMApprox hT hB).sol N (WithLp.toLp 2 (a, b)) t =
            mirrorReEmb (dState hT hB N s t) + mulI (mirrorReEmb (dState hT hB N s' t))) ∧
      -- 6. the elliptic core
      (mirrorFEMApprox hT hB).Verdict (mirrorEllCore hT hB) ∧
      (mirrorEllCore hT hB).Data.topologicalClosure = tsdQℝ ∧
      -- 7. the elliptic rates from the horizon-free initialization (6.4)
      (∀ {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorEllData) (N : ℕ),
        (∀ T : ℝ, (mirrorEllCmp hT hB T).p x N 0 = mirrorEllInit hT hB x N) ∧
        mirrorEllInit hT hB x N = WithLp.toLp 2 (mEll hT hB N (tsdDatumOf hx) 0 0,
          mEll hT hB N (tsdDatumOf (neg_I_smul_mem hx)) 0 0)) ∧
      (∀ (N : ℕ) (D : TSDDatum) {T : ℝ}, 0 ≤ T →
        (mEll hT hB N D 0 0).toEState = EState.mkL (Feec.BGG.ellipticProjection
          (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
          (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
          (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH ((D.exactWave T).σ 0)
            ((D.exactWave T).φ 0) ((D.exactWave T).u 0) ((D.exactWave T).M 0)
            ((D.exactWave T).ρ 0) ((D.exactWave T).ℓ 0)) 0)).1.1) ∧
      (∀ {x : PiLp 2 SpaceQ}, x ∈ mirrorL3Data → ∀ (N : ℕ) {t : ℝ}, 0 ≤ t →
        ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
          (4 * mirrorEllK (C := C) + 8 * mirrorEllK (C := C) * t) *
            (meshSize N * mirrorL3Norm x)) ∧
      (∀ {s : ℝ}, 0 ≤ s → s ≤ 1 → ∀ {x : PiLp 2 SpaceQ}, x ∈ mirrorSobData s → ∀ (N : ℕ)
        {t : ℝ}, 0 ≤ t →
        ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N (mirrorEllInit hT hB x N) t‖ ≤
          (6 * mirrorEllK (C := C) + 12 * mirrorEllK (C := C) * t) *
            (meshSize N ^ s * √(sobState (2 + s) x)))

set_option maxHeartbeats 4000000 in
theorem mirrorFEMApproxVerdict : MirrorFEMApproxVerdict :=
  ⟨exists_mirror_estimates, ⟨cosDatum_mem_mirrorL3Data, cosDatum_mem_mirrorSobData,
      cosDatum_not_stationary⟩, mirrorFEMVerdict_of_approxFEEC, fun hT hB =>
    ⟨einsteinBianchi_mirrorFEM_approxFEEC hT hB, topologicalClosure_tsdQℝ_inf_domainSq, isReducing_tsdQℝ,
      fun _ hx T => einsteinBianchi_mirrorFEM_converges hT hB hx T,
      fun hT0 _ hx N v _ ht => einsteinBianchi_mirrorFEM_rate hT hB hT0 hx N v ht,
      fun hT0 hs0 hs1 _ hx N v _ ht =>
        einsteinBianchi_mirrorFEM_rate_sobolev hT hB hT0 hs0 hs1 hx N v ht,
      fun N _ hT0 a b => mirrorFEMApprox_sol_eq_scheme hT hB N hT0 a b,
      einsteinBianchi_mirrorFEM_approxFEEC_elliptic hT hB, mirrorEllCore_closure hT hB,
      fun hx N =>
        ⟨fun T => mirrorEllCmp_p_zero_eq_init hT hB T _ N, mirrorEllCmp_p_zero hT hB 0 hx N⟩,
      fun N D _ hT0 => (congrArg HiddenState.toEState (mEll_horizon hT hB N D 0 _ 0)).trans
        (mEll_zero_toEState hT hB N D hT0),
      fun hx N _ ht => einsteinBianchi_mirrorFEM_rate_init hT hB hx N ht,
      fun hs0 hs1 _ hx N _ ht =>
        einsteinBianchi_mirrorFEM_rate_sobolev_init hT hB hs0 hs1 hx N ht⟩⟩

end MirrorFEM

/-! ### The thesis' boundary conditions -/

section StandardBoundary

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry
  Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM Feec.EinsteinBianchi.MatrixModel
  Feec.EinsteinBianchi.BoundedFailure Feec.EinsteinBianchi.BoundedConvergence

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **The thesis' scheme (6.5) on the cube is an instance of the approximating FEEC theorem**,
with the non-reducing TSD constraint `thesisTSD`. [QuennevilleBelair2015], §6.3, (6.5),
Table 6.1 -/
theorem einsteinBianchi_standardCube_approxFEEC :
    (standardCubeApprox hT hB).Verdict (standardCubeCore hT hB) :=
  approxFEEC _ _

/-- The orbit of the TSD datum `(0, 0, (0, β))` is the solution `betaU` of
`Feec.EinsteinBianchi.BoundedFailure.betaU_spec` (uniqueness of strong solutions). -/
theorem waveGroup_betaDatum {T : ℝ} (hT0 : 0 < T) :
    ∀ t ∈ Icc 0 T, matrixComplex.waveGroup.S t betaDatum = betaU hT0 t := by
  obtain ⟨h0, hU, -⟩ := betaU_spec (T := T) hT0
  have hd : betaDatum ∈ matrixComplex.wave.domain := h0 ▸ hU.mem_domain ⟨le_rfl, hT0.le⟩
  exact fun t ht => ((constrainedFEEC_wellPosed hd T).2.1 _ h0 hU ht).symm

/-- **The exact solution from the TSD datum `(0, 0, (0, β))` leaves the TSD constraint**: at some
`t ∈ [0, T]`, `E(t) ∉ L²(TSD)`. -/
theorem exists_waveGroup_betaDatum_not_mem {T : ℝ} (hT0 : 0 < T) :
    ∃ t ∈ Icc 0 T, matrixComplex.waveGroup.S t betaDatum ∉ thesisTSD := by
  obtain ⟨-, -, -, -, ⟨t, ht, hE⟩, -⟩ := betaU_spec (T := T) hT0
  refine ⟨t, ht, fun hmem => hE ?_⟩
  have h1 := (ShortHilbertComplex.mem_totalSub_family3.1 hmem).2.1
  rwa [waveGroup_betaDatum hT0 t ht] at h1

/-- **The residual of the thesis' scheme tends to a positive limit** (the departure clause of the verdict of the
elliptic core `standardCubeEllCore`, the converse part of the approximating FEEC theorem, at the
TSD datum `(0, 0, (0, β))`, which lies in the closure `⊤` of the core; the exact solution leaving
TSD is `betaU_spec`): at some `t ∈ [0, T]` the exact solution has left TSD, and the
residuals `dist(ιₙ e^{tLₙ} vₙ, TSD)` of every family of discrete solutions with
`ιₙ vₙ → (0, 0, (0, β))` tend to `dist(e^{tL}(0, 0, (0, β)), TSD) > 0`, so they stay above half
of it for all large `N`. -/
theorem standardCube_residual_not_mem {T : ℝ} (hT0 : 0 < T) :
    ∃ t ∈ Icc 0 T, matrixComplex.waveGroup.S t betaDatum ∉ thesisTSD ∧
      0 < infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) ∧
      ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
        Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 betaDatum) →
        Tendsto (fun N => infDist ((standardCubeApprox hT hB).sol N (v N) t) (thesisTSD : Set _))
          atTop (𝓝 (infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _))) ∧
        ∀ᶠ N in atTop, infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) / 2 <
          infDist ((standardCubeApprox hT hB).sol N (v N) t) (thesisTSD : Set _) := by
  obtain ⟨t, ht, hout⟩ := exists_waveGroup_betaDatum_not_mem hT0
  have hxc : betaDatum ∈ (standardCubeEllCore hT hB).Data.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      (dense_standardCubeEllCore hT hB).closure_eq]
    trivial
  have V := einsteinBianchi_standardCube_approxFEEC_elliptic hT hB
  have hpos : 0 < infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) :=
    (isClosed_thesisTSD.notMem_iff_infDist_pos ⟨0, thesisTSD.zero_mem⟩).1 hout
  refine ⟨t, ht, hout, hpos, fun v hv => ?_⟩
  have hlim := V.tendsto_infDist (thesisTSD : Set _) hxc hv ht.1
  rw [ApproxFEEC.S_apply _ ht.1] at hlim
  exact ⟨hlim, (tendsto_order.1 hlim).1 _ (half_lt_self hpos)⟩

/-- **Convergence of the thesis' scheme to the exact solution for every datum** (the convergence clause of the
verdict of the elliptic core `standardCubeEllCore`, on its closure `⊤`; `cubeWave_converges` is
not used): `ιₙ πₙ ξ₀ → ξ₀`, and every family of discrete initial
values with `ιₙ vₙ → ξ₀` gives discrete solutions converging to `e^{tL} ξ₀` uniformly on
`[0, T]` (this replaces `Feec.EinsteinBianchi.BoundedConvergence.tendsto_of_isStrongSolution`,
for every datum of `L²`). -/
theorem einsteinBianchi_standardCube_converges (x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) (T : ℝ) :
    Tendsto (fun N => (standardCubeApprox hT hB).incl N ((standardCubeApprox hT hB).proj N x))
      atTop (𝓝 x) ∧
    ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
      Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 x) →
      TendstoUniformlyOn (fun N t => (standardCubeApprox hT hB).sol N (v N) t)
        (fun t => matrixComplex.waveGroup.S t x) atTop (Icc 0 T) := by
  have hxc : x ∈ (standardCubeEllCore hT hB).Data.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      (dense_standardCubeEllCore hT hB).closure_eq]
    trivial
  have V := einsteinBianchi_standardCube_approxFEEC_elliptic hT hB
  exact ⟨V.tendsto_incl_proj hxc, fun v hv =>
    (V.converges hxc hv T).congr_right fun t ht => ApproxFEEC.S_apply _ ht.1 x⟩

/-- **The converse part of the approximating FEEC theorem on the thesis' scheme** (the non-reducing departure clause of the
verdict, non-reducing branch, with the dense elliptic core): since `thesisTSD` does not reduce
`L` (`not_isReducing_thesisTSD`), for every `T > 0` some datum of `thesisTSD` or of its
orthogonal complement is left by the exact solution at some `t ∈ [0, T]`, and the residuals
`dist(ιₙ e^{tLₙ} vₙ, Q)` of every family of discrete solutions with `ιₙ vₙ → ξ₀` tend to the
positive distance `dist(e^{tL} ξ₀, Q)`. This consumes only `¬ IsReducing` (itself proved from
the explicit datum `(0, 0, (0, β))` through `not_isReducing_thesisTSD`). -/
theorem standardCube_residual_not_isReducing {T : ℝ} (hT0 : 0 < T) :
    ∃ Q : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
        (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))),
      (Q = thesisTSD ∨ Q = thesisTSDᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
        matrixComplex.waveGroup.S t x ∉ Q ∧
        0 < infDist (matrixComplex.waveGroup.S t x) (Q : Set _) ∧
        ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
          Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 x) →
          Tendsto (fun N => infDist ((standardCubeApprox hT hB).sol N (v N) t) (Q : Set _))
            atTop (𝓝 (infDist (matrixComplex.waveGroup.S t x) (Q : Set _))) := by
  have V := einsteinBianchi_standardCube_approxFEEC_elliptic hT hB
  obtain ⟨Q, hQ, x, hx, t, ht, hout⟩ := dissipFEEC_leaves_of_not_isReducing
    (standardCubeApprox hT hB).toDissipFEEC not_isReducing_thesisTSD hT0
  rw [ApproxFEEC.S_apply _ ht.1] at hout
  have hQc : IsClosed (SetLike.coe Q) := by
    rcases hQ with rfl | rfl
    exacts [isClosed_thesisTSD, Submodule.isClosed_orthogonal _]
  have hxc : x ∈ (standardCubeEllCore hT hB).Data.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      (dense_standardCubeEllCore hT hB).closure_eq]
    trivial
  refine ⟨Q, hQ, x, hx, t, ht, hout, (hQc.notMem_iff_infDist_pos ⟨0, Q.zero_mem⟩).1 hout,
    fun v hv => ?_⟩
  have hlim := V.tendsto_infDist (SetLike.coe Q) hxc hv ht.1
  rwa [ApproxFEEC.S_apply _ ht.1] at hlim

/-- **`D(L) ∩ thesisTSD` is not dense in `thesisTSD`** (the density gap of [QuennevilleBelair2015],
Prop 4.17): a nonzero `G` of the obstruction `L²(TSD) ⊓ (L²(TSD) ⊓ H̊(curl))ᗮ`
(`Feec.Models.BoundedDomain.not_finiteDimensional_obstruction`) gives the TSD datum `(0, G, 0)`,
orthogonal to every datum of `D(L) ∩ thesisTSD` (the electric slot of `D(L)` lies in
`D(d₁) = H̊(curl)`), hence not in its closure. So the density hypothesis of the clauses
`SkewFEEC.Verdict.leaves_smooth_symm`, `DissipFEEC.Verdict.leaves_smooth` and
`ApproxFEEC.Verdict.isReducing_iff_keeps` of the verdict fails for the thesis' boundary conditions, and those clauses give nothing there; the
converse part comes from the per-datum clause (`standardCube_residual_not_mem`) and from the
`K`-or-`Kᗮ` clause (`standardCube_residual_not_isReducing`). -/
theorem exists_mem_thesisTSD_not_mem_closure :
    ∃ k ∈ thesisTSD, k ∉ closure ((matrixComplex.wave.domain : Set (PiLp 2
      (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
        (W2B ℝ (cubeDomain 3))))) ∩ thesisTSD) := by
  have hΩ := isOpen_cubeDomain 3
  have hb := isBounded_cubeDomain 3
  have hne : obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal (cubeDomain 3)).domain
      (tsd (cubeDomain 3)) ≠ ⊥ := fun h =>
    not_finiteDimensional_obstruction hΩ hb nonempty_cubeDomain (by rw [h]; infer_instance)
  obtain ⟨G, hG, hG0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hGK, hG⟩ := mem_obstruction.1 hG
  set k : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
    (W2B ℝ (cubeDomain 3))) := ShortHilbertComplex.mk3 0 G 0 with hk
  have hkK : k ∈ thesisTSD :=
    ShortHilbertComplex.mem_totalSub_family3.2 ⟨Submodule.zero_mem _, hGK, Submodule.zero_mem _⟩
  refine ⟨k, hkK, fun hcl => hG0 ?_⟩
  have horth : ∀ z ∈ (matrixComplex.wave.domain : Set (PiLp 2
      (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
        (W2B ℝ (cubeDomain 3))))) ∩ thesisTSD, ⟪z, k⟫_ℝ = 0 := by
    rintro z ⟨hzD, hzK⟩
    have h1 : (z 1 : L2F ℝ (cubeDomain 3) Ix) ∈
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal (cubeDomain 3)).domain := by
      rw [← bggComplex_d₁_domain hΩ]
      exact ((bggComplex ℝ hΩ).mem_wave_domain.1 hzD).2.1
    have h2 := hG (z 1) ⟨(ShortHilbertComplex.mem_totalSub_family3.1 hzK).2.1, h1⟩
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    change ⟪(z 0 : L2 ℝ (cubeDomain 3)), 0⟫_ℝ + ⟪(z 1 : L2F ℝ (cubeDomain 3) Ix), G⟫_ℝ +
      ⟪(z 2 : W2B ℝ (cubeDomain 3)), 0⟫_ℝ = 0
    rw [inner_zero_right, inner_zero_right, zero_add, add_zero]
    exact h2
  have hc : IsClosed {z : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
      (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))) | ⟪z, k⟫_ℝ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hkk : ⟪k, k⟫_ℝ = 0 := closure_minimal (t := {z | ⟪z, k⟫_ℝ = 0}) horth hc hcl
  have hk0 : k = 0 := inner_self_eq_zero.1 hkk
  exact congrArg (fun z : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))) => (z 1 : L2F ℝ (cubeDomain 3) Ix)) hk0

/-- The density hypothesis of the `D(L) ∩ K` clauses of the verdict fails for `K = thesisTSD`. -/
theorem not_forall_mem_closure_domain_inf_thesisTSD :
    ¬ ∀ k ∈ thesisTSD, k ∈ closure ((matrixComplex.wave.domain : Set (PiLp 2
      (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
        (W2B ℝ (cubeDomain 3))))) ∩ thesisTSD) := fun h =>
  let ⟨k, hk, hn⟩ := exists_mem_thesisTSD_not_mem_closure
  hn (h k hk)

/-- **The verdict of the approximating FEEC theorem on the thesis' scheme (6.5)**: the TSD
constraint `thesisTSD` contains the datum `(0, 0, (0, β))` and does not reduce `L`; the model
verdict `StandardCubeVerdict` (componentwise: `Eₕ(t₁) ∉ L²(TSD)`, `Bₕ(t₂)` not symmetric, from
the projected data); admissible smoothers exist, and for each of them
1. the full verdict `ApproxFEEC.Verdict` of `standardCubeApprox` with the orbit core
   `standardCubeCore`, which is dense;
2. the discrete solutions are the solutions of (6.5) without source;
3. for every datum, `ιₙ πₙ ξ₀ → ξ₀` and every convergent family of discrete solutions converges
   to `e^{tL} ξ₀` uniformly on `[0, T]`;
4. (the converse part) from `(0, 0, (0, β))` the exact solution leaves TSD at some `t ∈ [0, T]`,
   and the residuals of every convergent family of discrete solutions tend to the positive
   distance `dist(e^{tL}(0, 0, (0, β)), TSD)` and stay above half of it for all large `N`;
5. **the elliptic core** (best approximation plus consistency, no model convergence theorem used):
   the full verdict with the dense `standardCubeEllCore`, and its converse part from
   `¬ IsReducing` alone (`standardCube_residual_not_isReducing`);
6. `D(L) ∩ thesisTSD` is not dense in `thesisTSD` (Prop 4.17), so the verdict's `D(L) ∩ K`
   clauses do not apply (`not_forall_mem_closure_domain_inf_thesisTSD`). -/
abbrev StandardCubeApproxVerdict : Prop :=
  (betaDatum ∈ thesisTSD ∧ ¬ matrixComplex.wave.IsReducing thesisTSD) ∧
    -- the model verdict (componentwise discrete failure of TSD, explicit projected data)
    StandardCubeVerdict ∧
    (∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ),
      PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C ∧
        PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) ∧
    ∀ {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      -- 1. the verdict, dense core
      (standardCubeApprox hT hB).Verdict (standardCubeCore hT hB) ∧
      Dense ((standardCubeCore hT hB).Data : Set (PiLp 2 (ShortHilbertComplex.W3
        (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) ∧
      -- 2. the discrete solutions are (6.5)
      (∀ (N : ℕ) {T : ℝ} (hT0 : 0 < T) (v : cubeHidden hT hB N),
        ∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T 0,
          DiscreteSolution.hiddenInit hT0.le s = v ∧
          ∀ t ∈ Icc 0 T, (standardCubeApprox hT hB).sol N v t =
            totalE (vecInv (cState hT hB N s t))) ∧
      -- 3. convergence for every datum
      (∀ (x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
          (W2B ℝ (cubeDomain 3)))) (T : ℝ),
        Tendsto (fun N => (standardCubeApprox hT hB).incl N ((standardCubeApprox hT hB).proj N x))
          atTop (𝓝 x) ∧
        ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
          Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 x) →
          TendstoUniformlyOn (fun N t => (standardCubeApprox hT hB).sol N (v N) t)
            (fun t => matrixComplex.waveGroup.S t x) atTop (Icc 0 T)) ∧
      -- 4. the residual from `(0, 0, (0, β))` tends to a positive limit
      (∀ {T : ℝ}, 0 < T →
        ∃ t ∈ Icc 0 T, matrixComplex.waveGroup.S t betaDatum ∉ thesisTSD ∧
          0 < infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) ∧
          ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
            Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 betaDatum) →
            Tendsto (fun N => infDist ((standardCubeApprox hT hB).sol N (v N) t)
              (thesisTSD : Set _)) atTop
              (𝓝 (infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _))) ∧
            ∀ᶠ N in atTop, infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) / 2 <
              infDist ((standardCubeApprox hT hB).sol N (v N) t) (thesisTSD : Set _)) ∧
      -- 5. the elliptic core (dense), and the converse part from `¬ IsReducing` alone
      (standardCubeApprox hT hB).Verdict (standardCubeEllCore hT hB) ∧
      Dense ((standardCubeEllCore hT hB).Data : Set (PiLp 2 (ShortHilbertComplex.W3
        (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) ∧
      (∀ {T : ℝ}, 0 < T →
        ∃ Q : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
            (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))),
          (Q = thesisTSD ∨ Q = thesisTSDᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
            matrixComplex.waveGroup.S t x ∉ Q ∧
            0 < infDist (matrixComplex.waveGroup.S t x) (Q : Set _) ∧
            ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
              Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 x) →
              Tendsto (fun N => infDist ((standardCubeApprox hT hB).sol N (v N) t) (Q : Set _))
                atTop (𝓝 (infDist (matrixComplex.waveGroup.S t x) (Q : Set _)))) ∧
      -- 6. the density hypothesis of the `D(L) ∩ K` clauses fails
      ¬ ∀ k ∈ (standardCubeApprox hT hB).K, k ∈ closure ((matrixComplex.wave.domain :
        Set (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
          (W2B ℝ (cubeDomain 3))))) ∩ (standardCubeApprox hT hB).K)

theorem standardCubeApproxVerdict : StandardCubeApproxVerdict := by
  refine ⟨⟨betaDatum_mem_thesisTSD, not_isReducing_thesisTSD⟩, standardCubeVerdict, ?_,
    fun hT hB =>
    ⟨einsteinBianchi_standardCube_approxFEEC hT hB, dense_standardCubeCore hT hB,
      fun N _ hT0 v => standardCube_sol_eq_scheme hT hB N hT0 v,
      fun x T => einsteinBianchi_standardCube_converges hT hB x T,
      fun hT0 => standardCube_residual_not_mem hT hB hT0,
      einsteinBianchi_standardCube_approxFEEC_elliptic hT hB, dense_standardCubeEllCore hT hB,
      fun hT0 => standardCube_residual_not_isReducing hT hB hT0,
      not_forall_mem_closure_domain_inf_thesisTSD⟩⟩
  obtain ⟨p, C, hT, hB, -⟩ := Feec.Models.Cube.FEM.tableRows_H1
  exact ⟨p, C, hT, hB⟩

end StandardBoundary

/-! ### Summary -/

/-- **The verdicts for the linearized Einstein–Bianchi system** ([QuennevilleBelair2015],
Ch. 4–6): the constrained FEEC verdicts on `𝕋³`, the mirror cube (spectral) and the model
verdicts of the scheme (6.5) (as in `einsteinBianchi_constrainedFEEC_summary`, the mirror finite
element row `MirrorFEMVerdict` proved from the approximating FEEC theorem,
`mirrorFEMVerdict_of_approxFEEC`); on `ℝ³` the approximating FEEC verdict of the frequency
truncation `|ξ| ≤ N` (`EuclideanBand.EuclideanEBVerdict`: the full `ApproxFEEC.Verdict`, the error
equal to the truncation error, `Hˢ` rates with sharp exponent, TSD preserved exactly); and the
approximating FEEC verdicts of the scheme (6.5) with mirror boundary conditions
(`MirrorFEMApproxVerdict`) and with the thesis' boundary conditions (`StandardCubeApproxVerdict`). -/
theorem einsteinBianchi_summary :
    -- the constrained FEEC verdicts, with the approximating `ℝ³` row
    ((TorusVerdict ∧ TorusSobolevVerdict ∧ TorusNonvacuous) ∧ EuclideanBand.EuclideanEBVerdict ∧
      (MirrorVerdict ∧ MirrorSobolevVerdict ∧ MirrorNonvacuous) ∧ MirrorFEMVerdict ∧
      StandardCubeVerdict) ∧
    -- the scheme (6.5) as an approximating FEEC discretization
    MirrorFEMApproxVerdict ∧ StandardCubeApproxVerdict :=
  have h := einsteinBianchi_constrainedFEEC_summary
  ⟨⟨h.1, EuclideanBand.einsteinBianchi_euclidean_band, h.2.2.1, mirrorFEMVerdict_of_approxFEEC,
    h.2.2.2.2⟩, mirrorFEMApproxVerdict, standardCubeApproxVerdict⟩

end Feec.Instances.EinsteinBianchi
