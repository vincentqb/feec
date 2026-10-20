module

public import Feec.Instances.EinsteinBianchiFEMMirrorCore
public import Feec.Instances.EinsteinBianchiFEMCubeCore

/-!
# The thesis' scheme (6.5) as an instance of the approximating FEEC theorem

The finite element scheme (6.5) of [QuennevilleBelair2015], §6.3, is not a discretization by
subcomplexes: its discrete complex couples the two rows of the BGG construction by
`S₀,ₕ = π¹S⁰ ≠ S⁰` (a variational crime, [HolstStern2012]), so it is not an instance of the
constrained FEEC theorem (`Feec.HilbertComplex.constrainedFEEC`). It is an instance of the
**approximating FEEC theorem** `Feec.HilbertComplex.approxFEEC` (statement
`Feec.HilbertComplex.ApproxFEEC.Verdict`), with both boundary conditions:

* **mirror boundary conditions** (`einsteinBianchi_mirrorFEM_approxFEEC`): the discretization
  `Feec.Instances.EinsteinBianchi.FEM.mirrorFEMApprox` of the real mirror BGG complex
  (`complexQℝ`) with the TSD constraint `tsdQℝ`, which reduces `L`; its core (TSD data of `D(L²)`)
  has closure the whole TSD constraint, so for every TSD datum and every convergent family of
  discrete initial values the scheme converges to the TSD solution uniformly on `[0, T]` and the
  residual tends to `0`; the rate classes give `O(h)` for TSD data of `D(L³)`
  (`einsteinBianchi_mirrorFEM_rate`) and `O(hˢ)` for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1`
  (`einsteinBianchi_mirrorFEM_rate_sobolev`): the strength of
  `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`, `mirror_waveFEM_rate_of_mem_domain` and
  `mirror_waveFEM_rate_sobolev_of_add_two`, for complex data and every convergent family of
  initial values (`MirrorFEMApproxVerdict`);
* **the thesis' boundary conditions** (`einsteinBianchi_standardCube_approxFEEC`): the
  discretization `Feec.Instances.EinsteinBianchi.FEM.standardCubeApprox` of the matrix model with
  the TSD constraint `thesisTSD`, which does not reduce `L`; its core `D(L²)` is dense, so the
  scheme converges for every datum; from the TSD datum `(0, 0, (0, β))` the exact solution leaves
  TSD and the residuals of every convergent family of discrete solutions tend to the positive
  distance of the exact solution from TSD (`standardCube_residual_not_mem`, the converse part
  of the approximating FEEC theorem; `StandardCubeApproxVerdict`).

In both instances the discrete solutions of the approximating discretization are the solutions
of (6.5) without source (`mirrorFEMApprox_sol_eq_scheme`, `standardCube_sol_eq_scheme`).

**Faithfulness caveat.** The (6.5) instances are faithful to `cubeWave`/`mirrorWave` (the
scheme (6.5) with `S₀,ₕ = π¹S⁰` for the smoothed, resp. parity-smoothed, cochain projections), not
to the variant with the canonical interpolant `Π`.

**The cores are orbit cores**: the comparison trajectory of a datum is the discrete orbit from
its orthogonal projection (zero consistency defect, `ApproxFEEC.orbitCore`); the approximation
hypothesis of the core is the model convergence theorem of (6.5) from the elliptic projection
(6.4), with which the orthogonal projection competes by best approximation
(`ApproxFEEC.IsOrthogonal.norm_sub_sol_proj_le`). What the approximating FEEC theorem adds to
the model theorems: complex data (real and imaginary parts), the closure of the core (all TSD
data, resp. all data, not only `D(L²)`), every convergent family of initial values, and the
constraint residual in both directions.

`einsteinBianchi_summary` is
`Feec.Instances.EinsteinBianchi.einsteinBianchi_constrainedFEEC_summary` together with
`MirrorFEMApproxVerdict` and `StandardCubeApproxVerdict`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.17, §6.3 ((6.5), Table 6.1)
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3
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

/-- The TSD constraint of `mirrorFEMApprox` reduces the real mirror wave operator. -/
theorem mirrorFEMApprox_isReducing : complexQℝ.wave.IsReducing (mirrorFEMApprox hT hB).K :=
  isReducing_tsdQℝ

/-- **Convergence of the mirror scheme (6.5) to the TSD solution** (item 3b of the verdict, on the
closure `tsdQℝ` of the core, items 2 and 4a with the reducing constraint): for every TSD datum
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
  have V := einsteinBianchi_mirrorFEM_approxFEEC hT hB
  have hxc : x ∈ (mirrorFEMCore hT hB).Data.topologicalClosure := by
    rw [mirrorFEMCore_closure]; exact hx
  refine ⟨fun t => (V.2.1.1 isReducing_tsdQℝ) t x hx, (V.2.2.2.1 T x hxc).1, fun v hv =>
    ⟨(V.2.2.2.1 T x hxc).2 v hv, (V.2.2.2.2.2.1 isReducing_tsdQℝ x hx).2 hxc T v hv⟩⟩

/-- **The `O(h)` rate of the mirror scheme (6.5) for TSD data of `D(L³)`** (item 3c of the verdict
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
  have h := (einsteinBianchi_mirrorFEM_approxFEEC hT hB).2.2.2.2.1 T
    (mirrorFEMRate hT hB T hT0) x hx N v t ht
  have hp : (mirrorFEMRate hT hB T hT0).p x N 0 = (mirrorFEMApprox hT hB).proj N x :=
    C0Group.S_zero_apply _ _
  have hι := (mirrorFEMApprox_isOrthogonal hT hB).norm_incl_le_one N
  have hC : (mirrorFEMRate hT hB T hT0).C = 3 * (2 * mirrorRateK hT hB * (1 + T)) := rfl
  have hC' : (mirrorFEMRate hT hB T hT0).C' = 0 := rfl
  have hm : (mirrorFEMRate hT hB T hT0).meshSize N ^ (mirrorFEMRate hT hB T hT0).α *
      (mirrorFEMRate hT hB T hT0).classNorm x = meshSize N * mirrorL3Norm x := by
    change meshSize N ^ (1 : ℝ) * mirrorL3Norm x = _
    rw [Real.rpow_one]
  rw [hC, hC', hm, hp, mul_zero, zero_mul, add_zero] at h
  have hn := norm_nonneg ((mirrorFEMApprox hT hB).proj N x - v)
  linarith [mul_le_of_le_one_left hn hι]

/-- **The `O(hˢ)` rate of the mirror scheme (6.5) for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1`** (item 3c
of the verdict for the rate class `mirrorFEMRateSobolev`): for every discrete initial value `v`,
`‖e^{tL} ξ₀ - ι' e^{tL'} v‖ ≤ 6 K (1 + T) h_Nˢ ‖ξ₀‖_{2+s} + ‖π' ξ₀ - v‖` on `[0, T]`, `K` the
constant of `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`. -/
theorem einsteinBianchi_mirrorFEM_rate_sobolev {T s : ℝ} (hT0 : 0 < T) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {x : PiLp 2 SpaceQ} (hx : x ∈ mirrorSobData s) (N : ℕ)
    (v : (mirrorFEMApprox hT hB).X N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
      3 * (2 * mirrorSobK hT hB * (1 + T)) * (meshSize N ^ s * √(sobState (2 + s) x)) +
        ‖(mirrorFEMApprox hT hB).proj N x - v‖ := by
  have h := (einsteinBianchi_mirrorFEM_approxFEEC hT hB).2.2.2.2.1 T
    (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1) x hx N v t ht
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
  rw [hC, hC', hm, hp, mul_zero, zero_mul, add_zero] at h
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

/-- **The verdict of the approximating FEEC theorem on the mirror scheme (6.5)**: admissible parity
smoothers exist, and for each of them
1. the full verdict `ApproxFEEC.Verdict` of `mirrorFEMApprox` with the core `mirrorFEMCore`;
2. the closure of the core is the TSD constraint, which reduces `L`;
3. for every TSD datum, the exact solution stays TSD, `ι' π' ξ₀ → ξ₀`, and every convergent family
   of discrete initial values gives discrete solutions converging to `e^{tL} ξ₀` with residuals
   tending to `0`, uniformly on `[0, T]`;
4. the `O(h)` rate for TSD data of `D(L³)` and the `O(hˢ)` rate for TSD data in `H^{2+s}`,
   `0 ≤ s ≤ 1`;
5. the discrete solutions are the solutions of (6.5) without source (real and imaginary parts);
6. non-vacuity: the non-stationary TSD datum `cosDatum` lies in both rate classes. -/
abbrev MirrorFEMApproxVerdict : Prop :=
  (∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
      ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
        ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) ∧
    (cosDatum.U₀ ∈ mirrorL3Data ∧ (∀ s, cosDatum.U₀ ∈ mirrorSobData s) ∧
      cosDatum.U₀ ∉ Feec.Models.Cube.MirrorBGG.complexQ.waveGroup.stationary) ∧
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
      -- 4. rates
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
            mirrorReEmb (dState hT hB N s t) + mulI (mirrorReEmb (dState hT hB N s' t)))

set_option maxHeartbeats 4000000 in
theorem mirrorFEMApproxVerdict : MirrorFEMApproxVerdict :=
  ⟨exists_mirror_estimates, ⟨cosDatum_mem_mirrorL3Data, cosDatum_mem_mirrorSobData,
      cosDatum_not_stationary⟩, fun hT hB =>
    ⟨einsteinBianchi_mirrorFEM_approxFEEC hT hB, mirrorFEMCore_closure hT hB, isReducing_tsdQℝ,
      fun _ hx T => einsteinBianchi_mirrorFEM_converges hT hB hx T,
      fun hT0 _ hx N v _ ht => einsteinBianchi_mirrorFEM_rate hT hB hT0 hx N v ht,
      fun hT0 hs0 hs1 _ hx N v _ ht =>
        einsteinBianchi_mirrorFEM_rate_sobolev hT hB hT0 hs0 hs1 hx N v ht,
      fun N _ hT0 a b => mirrorFEMApprox_sol_eq_scheme hT hB N hT0 a b⟩⟩

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

/-- **The residual of the thesis' scheme tends to a positive limit** (item 4b of the verdict, the
converse part of the approximating FEEC theorem, at the TSD datum `(0, 0, (0, β))`, which lies in
the closure `⊤` of the core): at some `t ∈ [0, T]` the exact solution has left TSD, and the
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
  have hxc : betaDatum ∈ (standardCubeCore hT hB).Data.topologicalClosure := by
    rw [standardCubeCore_closure]; trivial
  have V := einsteinBianchi_standardCube_approxFEEC hT hB
  have hpos : 0 < infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) :=
    (isClosed_thesisTSD.notMem_iff_infDist_pos ⟨0, thesisTSD.zero_mem⟩).1 hout
  refine ⟨t, ht, hout, hpos, fun v hv => ?_⟩
  have hlim := (V.2.2.2.2.2.2.1 (thesisTSD : Set _) isClosed_thesisTSD ⟨0, thesisTSD.zero_mem⟩
    betaDatum hxc v hv t ht.1 hout).2
  exact ⟨hlim, (tendsto_order.1 hlim).1 _ (half_lt_self hpos)⟩

/-- **Convergence of the thesis' scheme to the exact solution for every datum** (item 3b of the
verdict on the closure `⊤` of the core): `ιₙ πₙ ξ₀ → ξ₀`, and every family of discrete initial
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
  have hxc : x ∈ (standardCubeCore hT hB).Data.topologicalClosure := by
    rw [standardCubeCore_closure]; trivial
  exact (einsteinBianchi_standardCube_approxFEEC hT hB).2.2.2.1 T x hxc

/-- **The verdict of the approximating FEEC theorem on the thesis' scheme (6.5)**: the TSD
constraint `thesisTSD` contains the datum `(0, 0, (0, β))` and does not reduce `L`; admissible
smoothers exist, and for each of them
1. the full verdict `ApproxFEEC.Verdict` of `standardCubeApprox` with the core `standardCubeCore`,
   which is dense;
2. the discrete solutions are the solutions of (6.5) without source;
3. for every datum, `ιₙ πₙ ξ₀ → ξ₀` and every convergent family of discrete solutions converges
   to `e^{tL} ξ₀` uniformly on `[0, T]`;
4. (the converse part) from `(0, 0, (0, β))` the exact solution leaves TSD at some `t ∈ [0, T]`,
   and the residuals of every convergent family of discrete solutions tend to the positive
   distance `dist(e^{tL}(0, 0, (0, β)), TSD)` and stay above half of it for all large `N`. -/
abbrev StandardCubeApproxVerdict : Prop :=
  (betaDatum ∈ thesisTSD ∧ ¬ matrixComplex.wave.IsReducing thesisTSD) ∧
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
      ∀ {T : ℝ}, 0 < T →
        ∃ t ∈ Icc 0 T, matrixComplex.waveGroup.S t betaDatum ∉ thesisTSD ∧
          0 < infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) ∧
          ∀ v : ∀ N, (standardCubeApprox hT hB).X N,
            Tendsto (fun N => (standardCubeApprox hT hB).incl N (v N)) atTop (𝓝 betaDatum) →
            Tendsto (fun N => infDist ((standardCubeApprox hT hB).sol N (v N) t)
              (thesisTSD : Set _)) atTop
              (𝓝 (infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _))) ∧
            ∀ᶠ N in atTop, infDist (matrixComplex.waveGroup.S t betaDatum) (thesisTSD : Set _) / 2 <
              infDist ((standardCubeApprox hT hB).sol N (v N) t) (thesisTSD : Set _)

theorem standardCubeApproxVerdict : StandardCubeApproxVerdict := by
  refine ⟨⟨betaDatum_mem_thesisTSD, not_isReducing_thesisTSD⟩, ?_, fun hT hB =>
    ⟨einsteinBianchi_standardCube_approxFEEC hT hB, dense_standardCubeCore hT hB,
      fun N _ hT0 v => standardCube_sol_eq_scheme hT hB N hT0 v,
      fun x T => einsteinBianchi_standardCube_converges hT hB x T,
      fun hT0 => standardCube_residual_not_mem hT hB hT0⟩⟩
  obtain ⟨p, C, hT, hB, -⟩ := Feec.Models.Cube.FEM.tableRows_H1
  exact ⟨p, C, hT, hB⟩

end StandardBoundary

/-! ### Summary -/

/-- **The verdicts for the linearized Einstein–Bianchi system** ([QuennevilleBelair2015],
Ch. 4–6): the constrained FEEC verdicts (`einsteinBianchi_constrainedFEEC_summary`: `𝕋³`, `ℝ³`,
the mirror cube spectral and the model verdicts of the scheme (6.5)), and the approximating FEEC
verdicts of the scheme (6.5) with mirror boundary conditions (`MirrorFEMApproxVerdict`) and with
the thesis' boundary conditions (`StandardCubeApproxVerdict`). -/
theorem einsteinBianchi_summary :
    -- the constrained FEEC verdicts
    ((TorusVerdict ∧ TorusSobolevVerdict ∧ TorusNonvacuous) ∧ EuclideanVerdict ∧
      (MirrorVerdict ∧ MirrorSobolevVerdict ∧ MirrorNonvacuous) ∧ MirrorFEMVerdict ∧
      StandardCubeVerdict) ∧
    -- the scheme (6.5) as an approximating FEEC discretization
    MirrorFEMApproxVerdict ∧ StandardCubeApproxVerdict :=
  ⟨einsteinBianchi_constrainedFEEC_summary, mirrorFEMApproxVerdict, standardCubeApproxVerdict⟩

end Feec.Instances.EinsteinBianchi
