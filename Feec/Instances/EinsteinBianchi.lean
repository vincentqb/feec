module

public import Feec.Instances.EinsteinBianchiSobolev
public import Feec.Models.Cube.MirrorWaveRegularity
public import Feec.Physics.EinsteinBianchi.BoundedConvergence

/-!
# The constrained FEEC theorem for the linearized Einstein–Bianchi system

The linearized Einstein–Bianchi (EB) system with weakly imposed symmetry ([QuennevilleBelair2015],
Ch. 5–6) is the Hodge wave equation of the BGG complex (5.1),
`H² --grad grad--> H(curl; ℝ³ˣ³) --(S₁, curl)--> L²(ℝ³) × L²(ℝ³ˣ³)`, with the **TSD constraint**
`K = {0} × L²(TSD) × ({0} × L²(TSD))`: `σ = 0`, the multiplier `M = 0`, and `E`, `B` symmetric,
trace-free and divergence-free. This file reads the constrained FEEC theorem
(`Feec.HilbertComplex.constrainedFEEC`) on its realizations.

* **`𝕋³`** (`einsteinBianchi_torus_constrainedFEEC`): the Fourier spectral discretization
  `torusFEEC` (bands `|n|_∞ ≤ N`, `bandFamily`) is a constrained FEEC
  discretization, `K` reduces `L`, so TSD propagates for all `t ∈ ℝ`, the discrete solutions
  converge uniformly on `[0, T]`, the constraint residual tends to `0`, and for data in the
  approximation class of order `α` the error and the residual are
  `≤ (1 + C_P)(1 + t)² (N + 1)^{-α} ‖ξ₀‖_α`; for TSD data in `H^{2+s}(𝕋³)`, `s ≥ 0`, they are
  `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` (`einsteinBianchi_torus_constrainedFEEC_sobolev`,
  through `mem_rateData_of_memSobStateT`). Non-vacuity (`torus_nonvacuous`): a band-limited
  non-stationary TSD datum lies in every class, and the TSD datum `decayState`, in `H³` but not
  band-limited for any `N`, lies in the class of order `1`.
* **`ℝ³`**: the constrained FEEC theorem needs a family of finite-dimensional subcomplexes with
  uniformly bounded commuting projections approximating `L²(ℝ³)`; no such family is constructed
  here (the Fourier bands of `ℝ³` are infinite-dimensional). The frequency truncation of `ℝ³` is
  a reducing family instead, read through the FEEC theorem for reducing families in
  `Feec.Instances.EuclideanBand` (`EuclideanEBVerdict`).
* **The cube `Q = (0, ½)³` with mirror boundary conditions**:
  - the cosine–sine spectral discretization `mirrorFEEC` (`bandFamilyQ`)
    is a constrained FEEC discretization of `MirrorBGG.complexQ` with the reducing constraint
    `MirrorBGG.tsdQ` (`einsteinBianchi_mirror_constrainedFEEC`: propagation, convergence to the
    TSD solution, residual `→ 0`, rates for the approximation classes; non-vacuity
    `mirror_nonvacuous`), with the **Sobolev rate** `(1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}`
    for TSD data in `H^{2+s}`, `s ≥ 0` (`einsteinBianchi_mirror_constrainedFEEC_sobolev`, through
    `Feec.Instances.EinsteinBianchi.mem_rateData_of_memSobState`);
  - the finite element scheme (6.5) with mirror boundary conditions
    (`Feec.Models.Cube.MirrorWeakSymmetry.mirrorFEM`) discretizes the two rows of the
    BGG construction (`Feec.BGG.Discrete`, coupled by `S₀,ₕ = π¹S⁰`), not the BGG Hilbert complex
    by subcomplexes, so it is not an instance of `ConstrainedFEEC`; the model theorems give its
    convergence to the TSD solution `e^{tL} ξ₀` of the same complex
    (`einsteinBianchi_mirror_waveFEM`), the `O(h)` rate for `D(L³)` data
    (`einsteinBianchi_mirror_waveFEM_rate`) and the `O(hˢ)` rate for `H^{2+s}` data
    (`einsteinBianchi_mirror_waveFEM_rate_sobolev`).
* **The cube with the thesis' boundary conditions** (`einsteinBianchi_thesisCube`,
  `StandardCubeVerdict`): the TSD constraint `thesisTSD = {0} × L²(TSD) × ({0} × L²(TSD))` of the
  matrix model contains the datum `(0, 0, (0, β))` and does not reduce `L`
  (`not_isReducing_thesisTSD`); more generally every closed subspace containing the datum and
  imposing `E ∈ L²(TSD)` fails to reduce `L` (`not_isReducing_thesisCube`); the scheme (6.5) of the
  thesis converges to the exact solution, which leaves TSD, and the discrete fields leave TSD for
  all large `N` (`Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`): the
  failure half of item 4 of the constrained FEEC theorem. This half is read on the finite element
  scheme, not through `ConstrainedFEEC`: no family of finite-dimensional subcomplexes of the thesis'
  complex with commuting projections is constructed here.

**Scope.** The spectral rate classes are approximation classes (truncation errors of
`ξ₀, L ξ₀, L² ξ₀` of order `(N + 1)^{-α}`); they contain the TSD Sobolev data on `𝕋³` and on the
mirror cube. The generic rate keeps the factor `(1 + C_P)(1 + t)²` of `constrainedFEEC_rate`. The
finite element statements and the thesis-BC failure are not applications of `constrainedFEEC`:
they are the model theorems with the exact solution `e^{tL} ξ₀` (the thesis-BC non-reduction is
proved from the explicit solution of the datum `(0, 0, (0, β))` and the propagation of reducing
subspaces). The `ℝ³` row is in `Feec.Instances.EuclideanBand` (`EuclideanEBVerdict`).

`einsteinBianchi_constrainedFEEC_summary` is the conjunction of the full verdicts (`TorusVerdict`,
`TorusSobolevVerdict`, `TorusNonvacuous`, `MirrorVerdict`, `MirrorSobolevVerdict`,
`MirrorNonvacuous`, `MirrorFEMVerdict`, `StandardCubeVerdict`); each headline theorem proves one
of them.

**The scheme (6.5) as an approximating FEEC discretization.** Both finite element rows are
instances of the approximating FEEC theorem, in `Feec.Instances.EinsteinBianchiFEM`, through one
crime front each (`ofComplexCrime` of the Galerkin family of the elliptic core:
`mirrorEllCore`, `standardCubeEllCore`, the elliptic projection (6.4) as comparison trajectory,
from the Strang bound of (6.4) alone, without the model convergence theorems):
`MirrorFEMApprox.Verdict` (convergence to the TSD solution for every TSD datum and every
convergent family of discrete initial values, the `O(h)` and `O(hˢ)` rates, residual `→ 0`) and
`StandardCubeApprox.Verdict` (convergence for every datum; from `(0, 0, (0, β))` the residuals
tend to a positive limit); `einsteinBianchi_summary` there extends
`einsteinBianchi_constrainedFEEC_summary` by these two verdicts and the `ℝ³` row, the verdict of
the frequency truncation (`Feec.Instances.EuclideanBand.EuclideanEBVerdict`). `MirrorFEMVerdict`
and `StandardCubeVerdict` are kept.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 4 (§4.4, §4.6, §4.10, Thm 4.14, Prop 4.17), Ch. 5 ((5.1)), Ch. 6 (§6.1–6.3, (6.5))
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi

open Feec.HilbertComplex

/-! ### `𝕋³`: the Fourier spectral method -/

section Torus

open Feec.Models.Torus.BGG

/-- **The Fourier spectral constrained FEEC discretization of the EB system on `𝕋³`**: the bands
`|n|_∞ ≤ N` of the BGG complex (5.1) with the TSD constraint. [QuennevilleBelair2015], §4.12,
Ch. 6 -/
def torusFEEC : ConstrainedFEEC complex ℕ :=
  bandFamily.toFEEC (totalSub constraint) isClosed_totalSub

/-- The TSD constraint reduces the periodic BGG complex. [QuennevilleBelair2015], Prop 4.17 -/
theorem torusFEEC_isReducing : complex.wave.IsReducing torusFEEC.K :=
  reducingSubcomplex.isReducing_wave

/-- The rate classes of the torus discretization: the approximation class of order `α`. -/
abbrev torusRate (α T : ℝ) : torusFEEC.RateClass T :=
  bandFamily.rateClass (totalSub constraint) isClosed_totalSub α T

/-- **The verdict of the constrained FEEC theorem for the EB system on `𝕋³`** (Fourier spectral
method): the verdict of `constrainedFEEC` for `torusFEEC`, and the instance-only fields: `K`
reduces `L`, so TSD data stay TSD for all `t ∈ ℝ`, and for TSD data in `D(L)` the constraint
residual is bounded by the error, tends to `0` uniformly on `[0, T]` and, on a rate class, is
`≤ (1 + C_P)(1 + t)² C hᵅ ‖ξ₀‖_class`. -/
structure TorusVerdict : Prop extends torusFEEC.Verdict where
  /-- the TSD constraint reduces `L` -/
  isReducing : complex.wave.IsReducing torusFEEC.K
  /-- TSD data stay TSD for all `t ∈ ℝ` -/
  tsd_propagates (t : ℝ) (x : PiLp 2 Space) (hxK : x ∈ torusFEEC.K) :
    complex.waveGroup.S t x ∈ torusFEEC.K
  /-- the TSD residual is bounded by the error -/
  tsd_residual_le (x : complex.wave.domain) (hxK : (x : PiLp 2 Space) ∈ torusFEEC.K) (N : ℕ)
    (t : ℝ) :
    infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
        (torusFEEC.K : Set (PiLp 2 Space)) ≤
      ‖complex.waveGroup.S t x -
        complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t)‖
  /-- the TSD residual tends to `0` uniformly on `[0, T]` -/
  tsd_residual_tendsto (x : complex.wave.domain) (hxK : (x : PiLp 2 Space) ∈ torusFEEC.K)
    (T : ℝ) :
    TendstoUniformlyOn
      (fun N t => infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
        (torusFEEC.K : Set (PiLp 2 Space))) (fun _ => 0) torusFEEC.l (Icc 0 T)
  /-- the TSD residual of data in a rate class is at most the rate of the error -/
  tsd_residual_rate {T : ℝ} (R : torusFEEC.RateClass T) {x : PiLp 2 Space} (hxR : x ∈ R.Data)
    (hxK : x ∈ torusFEEC.K) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (complex.totalD.graphFst
        (torusFEEC.discrete N (waveLift complex ⟨x, R.mem_domain x hxR⟩) t))
        (torusFEEC.K : Set (PiLp 2 Space)) ≤
      (1 + ellipticConst complex) * (1 + t) ^ 2 * (R.C * R.meshSize N ^ R.α * R.classNorm x)

/-- **The constrained FEEC theorem for the EB system on `𝕋³`** (Fourier spectral method):
`TorusVerdict`, the verdict of `constrainedFEEC torusFEEC` with `K` reducing `L`.
[QuennevilleBelair2015], Thm 4.14, Prop 4.17, Ch. 6 -/
theorem einsteinBianchi_torus_constrainedFEEC : TorusVerdict :=
  have V := constrainedFEEC torusFEEC
  { V with
    isReducing := torusFEEC_isReducing
    tsd_propagates := V.propagates_iff.1 torusFEEC_isReducing
    tsd_residual_le := V.residual_le torusFEEC_isReducing
    tsd_residual_tendsto := V.residual_tendsto torusFEEC_isReducing
    tsd_residual_rate := fun R _ hxR hxK N _ ht =>
      (torusFEEC.infDist_le_norm_sub (V.propagates_iff.1 torusFEEC_isReducing _ _ hxK)).trans
        (V.rate R hxR N ht) }

/-- `k₀ = (0, 0, 1)` and `-k₀` lie in the band `|n|_∞ ≤ 1`. -/
theorem mem_bandN_one_of_mem {n : Fin 3 → ℤ}
    (hn : n ∈ ({Models.Cube.Mirror.k0, -Models.Cube.Mirror.k0} : Finset (Fin 3 → ℤ))) :
    n ∈ Fourier.Torus.bandN 1 := by
  intro j
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl <;> fin_cases j <;> simp [Models.Cube.Mirror.k0]

/-- The non-stationary TSD datum `(0, E₀, (0, 0))`, `E₀ = 2 cos(2π x₃) diag(1, -1, 0)`, is
band-limited (`|n|_∞ ≤ 1`). -/
theorem cosState_mem_band : Models.Cube.MirrorBGG.cosState ∈ totalSub (band 1) := fun i => by
  rw [Fourier.mem_band_iff, MeasureTheory.Measure.ae_count_iff]
  intro n hn
  by_contra h
  exact hn (mem_bandN_one_of_mem (not_not.1 fun h' =>
    h (Models.Cube.MirrorWeakSymmetry.cosState_finite i n h')))

/-- **The Sobolev verdict on `𝕋³`**: `TorusVerdict`, and a TSD datum `ξ₀` in `H^{2+s}(𝕋³)`,
`s ≥ 0`, lies in `D(L)`, and the error and the constraint residual of the Fourier spectral
solutions are `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` on `[0, T]`. -/
structure TorusSobolevVerdict : Prop extends TorusVerdict where
  /-- a TSD datum in `H^{2+s}`, `s ≥ 0`, lies in `D(L)` -/
  sobolev_mem_domain {x : PiLp 2 Space} (hxK : x ∈ torusFEEC.K) {s : ℝ} (hs : 0 ≤ s)
    (hx : MemSobStateT (2 + s) x) : x ∈ complex.wave.domain
  /-- the error is `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` -/
  sobolev_rate {x : PiLp 2 Space} (hxK : x ∈ torusFEEC.K) {s : ℝ} (hs : 0 ≤ s)
    (hx : MemSobStateT (2 + s) x) (hD : x ∈ complex.wave.domain) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖complex.waveGroup.S t x -
        complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hD⟩) t)‖ ≤
      (1 + ellipticConst complex) * (1 + t) ^ 2 *
        ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)))
  /-- and so is the constraint residual -/
  sobolev_residual_rate {x : PiLp 2 Space} (hxK : x ∈ torusFEEC.K) {s : ℝ} (hs : 0 ≤ s)
    (hx : MemSobStateT (2 + s) x) (hD : x ∈ complex.wave.domain) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hD⟩) t))
        (torusFEEC.K : Set (PiLp 2 Space)) ≤
      (1 + ellipticConst complex) * (1 + t) ^ 2 *
        ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)))

/-- The band rate `(N + 1)^{-s} ‖ξ₀‖_s` of a TSD datum in `H^{2+s}` is at most
`(N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}`, scaled by `(1 + C_P)(1 + t)²`. -/
theorem torus_rate_le_sobolev {x : PiLp 2 Space} (hxK : x ∈ totalSub constraint) {s : ℝ}
    (hs : 0 ≤ s) (hx : MemSobStateT (2 + s) x) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + ellipticConst complex) * (1 + t) ^ 2 *
        (1 * (1 / ((N : ℝ) + 1)) ^ s * bandFamily.rateNorm s x) ≤
      (1 + ellipticConst complex) * (1 + t) ^ 2 *
        ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x))) := by
  have := ellipticConst_nonneg complex
  rw [one_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mem_rateData_of_memSobStateT hxK hs hx).2 (by positivity)) (by positivity)

/-- **Sobolev rate of the constrained FEEC theorem on `𝕋³`**: `TorusSobolevVerdict`, from the
rate of `einsteinBianchi_torus_constrainedFEEC` for the class of order `s`, which contains the
TSD data of `H^{2+s}` (`mem_rateData_of_memSobStateT`). [QuennevilleBelair2015], Thm 4.14,
Ch. 6 -/
theorem einsteinBianchi_torus_constrainedFEEC_sobolev : TorusSobolevVerdict :=
  have V := einsteinBianchi_torus_constrainedFEEC
  { V with
    sobolev_mem_domain := fun hxK _ hs hx => (mem_rateData_of_memSobStateT hxK hs hx).1.1
    sobolev_rate := fun hxK _ hs hx _ N T _ ht =>
      (V.rate (torusRate _ T) (mem_rateData_of_memSobStateT hxK hs hx).1 N ht).trans
        (torus_rate_le_sobolev hxK hs hx N ht.1)
    sobolev_residual_rate := fun hxK _ hs hx _ N T _ ht =>
      (V.tsd_residual_rate (torusRate _ T) (mem_rateData_of_memSobStateT hxK hs hx).1 hxK N
        ht).trans (torus_rate_le_sobolev hxK hs hx N ht.1) }

/-- **Non-vacuity on `𝕋³`**: (i) the TSD datum `(0, E₀, (0, 0))`,
`E₀ = 2 cos(2π x₃) diag(1, -1, 0)`, lies in `D(L) ∩ K`, is not stationary (`L ξ₀ ≠ 0`), and lies
in the approximation class of every order `α`; (ii) the TSD datum `decayState`,
`E = Σ_k (1 + k²)⁻² e^{2πi k x₃} diag(1, -1, 0)`, lies in `H³`, hence in the class of order `1`
(where the rate is `(N + 1)⁻¹`), is not band-limited for any `N` (the spectral method is not exact
on it), and is not stationary. -/
abbrev TorusNonvacuous : Prop :=
  (∃ x ∈ complex.wave.domain, x ∈ totalSub constraint ∧
      (∀ hx : x ∈ complex.wave.domain, complex.wave ⟨x, hx⟩ ≠ 0) ∧
      ∀ α, x ∈ bandFamily.rateData α) ∧
    ∃ x ∈ totalSub constraint, MemSobStateT (2 + 1) x ∧ x ∈ bandFamily.rateData 1 ∧
      (∀ N, x ∉ totalSub (band N)) ∧
      ∃ hx : x ∈ complex.wave.domain, complex.wave ⟨x, hx⟩ ≠ 0

theorem torus_nonvacuous : TorusNonvacuous := by
  refine ⟨⟨Models.Cube.MirrorBGG.cosState, Models.Cube.MirrorBGG.cosState_mem_domain,
    Models.Cube.MirrorBGG.cosState_mem_constraint, fun _ => Models.Cube.MirrorBGG.wave_cosState_ne,
    fun α => bandFamily.mem_rateData_of_mem cosState_mem_band α⟩, ?_⟩
  obtain ⟨hK, hS, hband, hL⟩ := decayState_nonvacuous
  exact ⟨decayState, hK, hS, (mem_rateData_of_memSobStateT hK zero_le_one hS).1, hband, hL⟩

end Torus

/-! ### The cube with mirror boundary conditions -/

section Mirror

open Feec.Models.Cube.MirrorBGG

/-- **The cosine–sine spectral constrained FEEC discretization of the EB system on the cube with
mirror boundary conditions**: the pull-back of the Fourier bands along the mirror extensions,
with the TSD constraint `tsdQ`. [QuennevilleBelair2015], §4.12, Ch. 6 -/
def mirrorFEEC : ConstrainedFEEC complexQ ℕ :=
  bandFamilyQ.toFEEC (totalSub tsdQ) isClosed_totalSub

/-- The TSD constraint reduces the mirror BGG complex on `Q`. [QuennevilleBelair2015],
Prop 4.17 (corrected) -/
theorem mirrorFEEC_isReducing : complexQ.wave.IsReducing mirrorFEEC.K :=
  reducingSubcomplexQ.isReducing_wave

/-- The rate classes of the mirror spectral discretization. -/
abbrev mirrorRate (α T : ℝ) : mirrorFEEC.RateClass T :=
  bandFamilyQ.rateClass (totalSub tsdQ) isClosed_totalSub α T

/-- **The verdict of the constrained FEEC theorem for the EB system on the cube with mirror
boundary conditions** (cosine–sine spectral method): the verdict of `constrainedFEEC` for
`mirrorFEEC`, and the instance-only fields: `K` reduces `L`, so TSD data stay TSD for all
`t ∈ ℝ`, and for TSD data in `D(L)` the constraint residual is bounded by the error, tends to `0`
uniformly on `[0, T]` and, on a rate class, is `≤ (1 + C_P)(1 + t)² C hᵅ ‖ξ₀‖_class`. -/
structure MirrorVerdict : Prop extends mirrorFEEC.Verdict where
  /-- the TSD constraint reduces `L` -/
  isReducing : complexQ.wave.IsReducing mirrorFEEC.K
  /-- TSD data stay TSD for all `t ∈ ℝ` -/
  tsd_propagates (t : ℝ) (x : PiLp 2 SpaceQ) (hxK : x ∈ mirrorFEEC.K) :
    complexQ.waveGroup.S t x ∈ mirrorFEEC.K
  /-- the TSD residual is bounded by the error -/
  tsd_residual_le (x : complexQ.wave.domain) (hxK : (x : PiLp 2 SpaceQ) ∈ mirrorFEEC.K) (N : ℕ)
    (t : ℝ) :
    infDist (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
        (mirrorFEEC.K : Set (PiLp 2 SpaceQ)) ≤
      ‖complexQ.waveGroup.S t x -
        complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t)‖
  /-- the TSD residual tends to `0` uniformly on `[0, T]` -/
  tsd_residual_tendsto (x : complexQ.wave.domain) (hxK : (x : PiLp 2 SpaceQ) ∈ mirrorFEEC.K)
    (T : ℝ) :
    TendstoUniformlyOn
      (fun N t => infDist
        (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
        (mirrorFEEC.K : Set (PiLp 2 SpaceQ))) (fun _ => 0) mirrorFEEC.l (Icc 0 T)
  /-- the TSD residual of data in a rate class is at most the rate of the error -/
  tsd_residual_rate {T : ℝ} (R : mirrorFEEC.RateClass T) {x : PiLp 2 SpaceQ} (hxR : x ∈ R.Data)
    (hxK : x ∈ mirrorFEEC.K) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (complexQ.totalD.graphFst
        (mirrorFEEC.discrete N (waveLift complexQ ⟨x, R.mem_domain x hxR⟩) t))
        (mirrorFEEC.K : Set (PiLp 2 SpaceQ)) ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * (R.C * R.meshSize N ^ R.α * R.classNorm x)

/-- **The constrained FEEC theorem for the EB system on the cube with mirror boundary
conditions**: `MirrorVerdict`, the verdict of `constrainedFEEC mirrorFEEC` with `K` reducing
`L`. [QuennevilleBelair2015], Thm 4.14, Prop 4.17 (corrected), Ch. 6 -/
theorem einsteinBianchi_mirror_constrainedFEEC : MirrorVerdict :=
  have V := constrainedFEEC mirrorFEEC
  { V with
    isReducing := mirrorFEEC_isReducing
    tsd_propagates := V.propagates_iff.1 mirrorFEEC_isReducing
    tsd_residual_le := V.residual_le mirrorFEEC_isReducing
    tsd_residual_tendsto := V.residual_tendsto mirrorFEEC_isReducing
    tsd_residual_rate := fun R _ hxR hxK N _ ht =>
      (mirrorFEEC.infDist_le_norm_sub (V.propagates_iff.1 mirrorFEEC_isReducing _ _ hxK)).trans
        (V.rate R hxR N ht) }

/-- **The Sobolev verdict on the mirror cube**: `MirrorVerdict`, and for a TSD datum
`ξ₀ ∈ D(L²)` with mirror extension in `H^{2+s}`, `s ≥ 0`, the error and the constraint residual
of the cosine–sine spectral solutions are `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` on
`[0, T]`. -/
structure MirrorSobolevVerdict : Prop extends MirrorVerdict where
  /-- the error is `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` -/
  sobolev_rate (D : Models.Cube.MirrorWeakSymmetry.TSDDatum) {s : ℝ} (hs : 0 ≤ s)
    (hD : Models.Cube.MirrorWeakSymmetry.MemSobState (2 + s) D.U₀) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖complexQ.waveGroup.S t D.U₀ -
        complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨D.U₀, D.mem⟩) t)‖ ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀)))
  /-- and so is the constraint residual -/
  sobolev_residual_rate (D : Models.Cube.MirrorWeakSymmetry.TSDDatum) {s : ℝ} (hs : 0 ≤ s)
    (hD : Models.Cube.MirrorWeakSymmetry.MemSobState (2 + s) D.U₀) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    infDist (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨D.U₀, D.mem⟩) t))
        (mirrorFEEC.K : Set (PiLp 2 SpaceQ)) ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀)))

/-- The band rate `(N + 1)^{-s} ‖ξ₀‖_s` of a mirror TSD datum in `H^{2+s}` is at most
`(N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}`, scaled by `(1 + C_P)(1 + t)²`. -/
theorem mirror_rate_le_sobolev (D : Models.Cube.MirrorWeakSymmetry.TSDDatum) {s : ℝ} (hs : 0 ≤ s)
    (hD : Models.Cube.MirrorWeakSymmetry.MemSobState (2 + s) D.U₀) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + ellipticConst complexQ) * (1 + t) ^ 2 *
        (1 * (1 / ((N : ℝ) + 1)) ^ s * bandFamilyQ.rateNorm s D.U₀) ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀))) := by
  have := ellipticConst_nonneg complexQ
  rw [one_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mem_rateData_of_memSobState D hs hD).2 (by positivity)) (by positivity)

/-- **Sobolev rate of the constrained FEEC theorem on the mirror cube**: `MirrorSobolevVerdict`,
from `constrainedFEEC_rate` for the rate class of order `s`, which contains the datum
(`mem_rateData_of_memSobState`). The cos datum lies in every `H^{2+s}`
(`cosDatum_memSobState`). [QuennevilleBelair2015], Thm 4.14, Ch. 6 -/
theorem einsteinBianchi_mirror_constrainedFEEC_sobolev : MirrorSobolevVerdict :=
  have V := einsteinBianchi_mirror_constrainedFEEC
  { V with
    sobolev_rate := fun D _ hs hD N T _ ht =>
      (V.rate (mirrorRate _ T) (mem_rateData_of_memSobState D hs hD).1 N ht).trans
        (mirror_rate_le_sobolev D hs hD N ht.1)
    sobolev_residual_rate := fun D _ hs hD N T _ ht =>
      (V.tsd_residual_rate (mirrorRate _ T) (mem_rateData_of_memSobState D hs hD).1 D.tsd N
        ht).trans (mirror_rate_le_sobolev D hs hD N ht.1) }

/-- The mirror datum `(0, E₀, (0, 0))` on `Q` is band-limited: its mirror extension is the
torus datum, with modes `±k₀`. -/
theorem cosStateQ_mem_band : cosStateQ ∈ totalSub (bandFamilyQ.B 1) := fun i => by
  change J i (cosStateQ i) ∈ band 1 i
  rw [← HilbertComplex.totalJ_apply, totalJ_cosStateQ]
  exact cosState_mem_band i

/-- **Non-vacuity on the mirror cube**: the TSD datum `(0, E₀, (0, 0))`,
`E₀ = 2 cos(2π x₃) diag(1, -1, 0)` on `Q`, lies in `D(L) ∩ K`, is not stationary, lies in the
approximation class of every order `α`, and, as the TSD datum `cosDatum`, in every `Hʳ`. -/
abbrev MirrorNonvacuous : Prop :=
  (∃ x ∈ complexQ.wave.domain, x ∈ totalSub tsdQ ∧ x ∉ complexQ.waveGroup.stationary ∧
      ∀ α, x ∈ bandFamilyQ.rateData α) ∧
    Models.Cube.MirrorWeakSymmetry.cosDatum.U₀ ∉ complexQ.waveGroup.stationary ∧
    ∀ r, Models.Cube.MirrorWeakSymmetry.MemSobState r Models.Cube.MirrorWeakSymmetry.cosDatum.U₀

theorem mirror_nonvacuous : MirrorNonvacuous :=
  ⟨⟨cosStateQ, Models.Cube.MirrorWeakSymmetry.cosStateQ_mem,
    Models.Cube.MirrorWeakSymmetry.cosStateQ_mem_tsd,
    Models.Cube.MirrorWeakSymmetry.cosDatum_not_stationary,
    fun α => bandFamilyQ.mem_rateData_of_mem cosStateQ_mem_band α⟩,
    Models.Cube.MirrorWeakSymmetry.cosDatum_not_stationary, cosDatum_memSobState⟩

end Mirror

/-! ### The finite element scheme (6.5) with mirror boundary conditions -/

section MirrorFEM

open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)
open Feec.Models.Cube.FEM (ParitySmoothingEstimates meshSize)
open Feec.FiniteElement (PolySeq)

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **Convergence of the mirror finite element scheme (6.5) to the TSD solution `e^{tL} ξ₀`**:
for a TSD datum `ξ₀ ∈ D(L²)` the exact solution `e^{tL} ξ₀` of the mirror BGG complex (the exact
solution of `einsteinBianchi_mirror_constrainedFEEC`) stays TSD on `[0, T]`, and for every
`ε > 0` and all large `N` the scheme (6.5) has a solution from the elliptic projection (6.4) with
`σₕ`, `Mₕ` and the errors of `E` and `B` at most `ε`, and `Bₕ` symmetric up to `2ε`. -/
abbrev MirrorWaveFEMConvergence : Prop :=
  ∀ (D : TSDDatum) {T : ℝ}, 0 < T → ∀ {ε : ℝ}, 0 < ε →
    (∀ t ∈ Icc 0 T, Models.Cube.MirrorBGG.complexQ.waveGroup.S t D.U₀ ∈
      totalSub Models.Cube.MirrorBGG.tsdQ) ∧
    ∀ᶠ N in atTop,
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH ((D.exactWave T).σ 0)
              ((D.exactWave T).φ 0) ((D.exactWave T).u 0) ((D.exactWave T).M 0)
              ((D.exactWave T).ρ 0) ((D.exactWave T).ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, ‖(sh.σ t : TU0)‖ ≤ ε ∧
          ‖rowsW1L (stEL (Models.Cube.MirrorBGG.complexQ.waveGroup.S t D.U₀)) -
            bIncl1 (sh.u t : BU1)‖ ≤ ε ∧ ‖(sh.M t : W2)‖ ≤ ε ∧
          ‖rowsW2L (stBL (Models.Cube.MirrorBGG.complexQ.waveGroup.S t D.U₀)) -
            (sh.ρ t : Wv W2)‖ ≤ ε ∧
          ‖matB (sh.ρ t : Wv W2) - transposeQ (matB (sh.ρ t : Wv W2))‖ ≤ 2 * ε

/-- **The mirror finite element scheme (6.5) converges to the TSD solution `e^{tL} ξ₀`**:
`MirrorWaveFEMConvergence` (`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM` with
`U = e^{tL} ξ₀`; by uniqueness, item 1, this is the only strong solution).
[QuennevilleBelair2015], §6.3, (6.5) -/
theorem einsteinBianchi_mirror_waveFEM : MirrorWaveFEMConvergence hT hB :=
  fun D _ hT0 _ hε => mirror_waveFEM hT hB D hT0 D.U_zero (D.isStrongSolution _) hε

/-- **The `O(h)` rate of the mirror scheme (6.5) for TSD data in `D(L³)`**, measured against the
exact solution `e^{tL} ξ₀`: `≤ K (‖ξ₀‖ + ‖Lξ₀‖ + ‖L²ξ₀‖ + ‖L³ξ₀‖)(1 + t) h_N`, for the solution
from the elliptic projection (6.4). -/
abbrev MirrorWaveFEMRate : Prop :=
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) (D : TSDDatum)
      (h3 : D.LLU₀ ∈ Models.Cube.MirrorBGG.complexQ.wave.domain) {T : ℝ}, 0 < T →
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
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
            K * (‖D.U₀‖ + ‖D.LU₀‖ + ‖D.LLU₀‖ +
              ‖Models.Cube.MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩‖) * (1 + t) * meshSize N

/-- **`O(h)` rate of the mirror scheme (6.5) for TSD data in `D(L³)`**: `MirrorWaveFEMRate`
(`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain` with `U = e^{tL} ξ₀`).
[QuennevilleBelair2015], §6.3, (6.5); [AFW2010], §3.3 -/
theorem einsteinBianchi_mirror_waveFEM_rate : MirrorWaveFEMRate hT hB :=
  (mirror_waveFEM_rate_of_mem_domain hT hB).imp fun _ hK =>
    ⟨hK.1, fun N D h3 _ hT0 => hK.2 N D h3 hT0 (U := D.U) D.U_zero (D.isStrongSolution _)⟩

/-- **The `O(hˢ)` rate of the mirror scheme (6.5) for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1`**,
measured against the exact solution `e^{tL} ξ₀`: `≤ K ‖ξ₀‖_{2+s} (1 + t) h_Nˢ`, for the solution
from the elliptic projection (6.4). -/
abbrev MirrorWaveFEMRateSobolev : Prop :=
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) (D : TSDDatum) {s : ℝ}, 0 ≤ s → s ≤ 1 →
      MemSobState (2 + s) D.U₀ → ∀ {T : ℝ}, 0 < T →
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
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
            K * √(sobState (2 + s) D.U₀) * (1 + t) * meshSize N ^ s

/-- **`O(hˢ)` rate of the mirror scheme (6.5) for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1`**:
`MirrorWaveFEMRateSobolev`
(`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two` with
`U = e^{tL} ξ₀`). [QuennevilleBelair2015], §6.3, (6.5); [AFW2010], §3.3 -/
theorem einsteinBianchi_mirror_waveFEM_rate_sobolev : MirrorWaveFEMRateSobolev hT hB :=
  (mirror_waveFEM_rate_sobolev_of_add_two hT hB).imp fun _ hK =>
    ⟨hK.1, fun N D _ hs0 hs1 hD _ hT0 =>
      hK.2 N D hs0 hs1 hD hT0 (U := D.U) D.U_zero (D.isStrongSolution _)⟩

/-- **The verdict on the mirror finite element scheme (6.5)**: admissible parity smoothers exist,
and for each of them the scheme converges to the TSD solution `e^{tL} ξ₀`
(`MirrorWaveFEMConvergence`), with the `O(h)` rate for `D(L³)` data (`MirrorWaveFEMRate`) and the
`O(hˢ)` rate for `H^{2+s}` data (`MirrorWaveFEMRateSobolev`). The scheme is not an instance of
`ConstrainedFEEC`; its verdict as an approximating FEEC discretization is
`Feec.Instances.EinsteinBianchi.MirrorFEMApprox.Verdict`. -/
structure MirrorFEMVerdict : Prop where
  /-- admissible parity smoothers exist -/
  exists_estimates : ∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
    ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
      ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C
  /-- the scheme converges to the TSD solution -/
  converges {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
    (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
    (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) :
    MirrorWaveFEMConvergence hT hB
  /-- at the rate `O(h)` for TSD data in `D(L³)` -/
  rate {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
    (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
    (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) :
    MirrorWaveFEMRate hT hB
  /-- and `O(hˢ)` for TSD data in `H^{2+s}`, `0 ≤ s ≤ 1` -/
  rate_sobolev {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
    (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
    (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) :
    MirrorWaveFEMRateSobolev hT hB

theorem mirrorFEMVerdict : MirrorFEMVerdict :=
  ⟨exists_mirror_estimates, einsteinBianchi_mirror_waveFEM, einsteinBianchi_mirror_waveFEM_rate,
    einsteinBianchi_mirror_waveFEM_rate_sobolev⟩

end MirrorFEM

/-! ### The cube with the thesis' boundary conditions: the failure half -/

section StandardBoundary

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry
  Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM Feec.EinsteinBianchi.MatrixModel
  Feec.EinsteinBianchi.BoundedFailure Feec.EinsteinBianchi.BoundedConvergence

/-- **The TSD constraint does not reduce `L` on the cube with the thesis' boundary conditions**:
no closed subspace `K` of the matrix model (`H̊²(Q) → H̊(curl, Q) → L²`, (5.1) with the
boundary conditions of [QuennevilleBelair2015], §6.3) that contains the TSD datum
`(0, 0, (0, β))` and imposes `E ∈ L²(TSD)` reduces the wave operator: the solution from the datum
leaves `L²(TSD)` (`Feec.EinsteinBianchi.BoundedFailure.betaU_spec`), while reducing subspaces
propagate. [QuennevilleBelair2015], Prop 4.17, §6.3 -/
theorem not_isReducing_thesisCube
    (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
      (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection]
    (h0 : betaDatum ∈ K) (hE : ∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) :
    ¬ matrixComplex.wave.IsReducing K := by
  intro hK
  obtain ⟨hU0, hU, -, -, ⟨t, ht, hout⟩, -⟩ := betaU_spec (T := 1) one_pos
  exact hout (hE _ (hU.mem_of_isReducing matrixComplex.isSkewAdjoint_wave.isDissipative hK
    (hU0 ▸ h0) (fun _ _ => K.zero_mem) t ht))

/-- **The TSD constraint of the matrix model**
`K = {0} × L²(TSD) × ({0} × L²(TSD)) ⊆ L²(Q) × L²(Q; ℝ³ˣ³) × (L²(Q; ℝ³) × L²(Q; ℝ³ˣ³))`: `σ = 0`,
`E` TSD, the multiplier `M = 0` and `B` TSD ([QuennevilleBelair2015], Prop 4.17, §6.1). -/
abbrev thesisTSD : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) :=
  totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ (cubeDomain 3)))
    (tsd (cubeDomain 3)) (Feec.Counterexamples.BoundedBGG.tsdB (cubeDomain 3)))

theorem isClosed_thesisTSD : IsClosed (thesisTSD : Set (PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) :=
  isClosed_totalSub

/-- The datum `(0, 0, (0, β))` is TSD. -/
theorem betaDatum_mem_thesisTSD : betaDatum ∈ thesisTSD :=
  ShortHilbertComplex.mem_totalSub_family3.2 ⟨Submodule.zero_mem _, Submodule.zero_mem _,
    Feec.Counterexamples.BoundedBGG.mem_tsdB.2 ⟨rfl,
      Feec.Counterexamples.BoundedDomainTSD.betaL2_mem_tsd (isOpen_cubeDomain 3)
        (isBounded_cubeDomain 3)⟩⟩

/-- **The TSD constraint does not reduce `L` on the cube with the thesis' boundary conditions**
(`not_isReducing_thesisCube` at `K = thesisTSD`). [QuennevilleBelair2015], Prop 4.17, §6.3 -/
theorem not_isReducing_thesisTSD : ¬ matrixComplex.wave.IsReducing thesisTSD :=
  not_isReducing_thesisCube thesisTSD betaDatum_mem_thesisTSD fun _ hx =>
    (ShortHilbertComplex.mem_totalSub_family3.1 hx).2.1

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **The failure of the thesis' scheme on the cube**: from the TSD datum `(0, 0, (0, β))` the
exact solution leaves TSD (`E(t) ∉ L²(TSD)`, `B(t)` not symmetric), the scheme (6.5) with the
elements of Table 6.1 has solutions whose initial states converge, every such family converges to
the exact solution uniformly on `[0, T]`, and the discrete fields leave TSD for all large `N`. -/
abbrev StandardCubeFailure {T : ℝ} (hT0 : 0 < T) : Prop :=
    (betaU hT0 0 = betaDatum ∧
      Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 (betaU hT0) ∧
      (∀ V, V 0 = betaDatum → Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 V →
        EqOn V (betaU hT0) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (betaU hT0 t 0 : L2 ℝ (cubeDomain 3)) = 0) ∧
      (∃ t ∈ Icc 0 T, betaE hT0 t ∉ tsd (cubeDomain 3)) ∧
      ∃ t ∈ Icc 0 T, betaB hT0 t ∉ symSub ℝ (cubeDomain 3)) ∧
    (betaW hT0).vec 0 = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) (0, 0, 0, rhoBeta) ∧
    (∃ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      (∀ N, (sh N).σ 0 = 0 ∧ (sh N).u 0 = 0 ∧ (sh N).M 0 = 0 ∧ (sh N).ρ 0 = rhoBetaH hT hB N) ∧
      Tendsto (fun N => ‖(betaW hT0).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0)) ∧
    ∀ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      Tendsto (fun N => ‖(betaW hT0).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0) →
      (∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
        ‖(betaW hT0).vec t - dvec (cubeFEM hT hB N) (sh N) t‖ < ε) ∧
      (∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
        ‖betaE hT0 t - rowsEquiv (incl1 (((sh N).u t : (cubeFEM hT hB N).Vt1h) : Wv U1))‖ < ε ∧
        ‖betaB hT0 t - rows2Equiv (((sh N).ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2)‖ < ε) ∧
      (∃ t ∈ Icc 0 T, ∀ᶠ N in atTop,
        rowsEquiv (incl1 (((sh N).u t : (cubeFEM hT hB N).Vt1h) : Wv U1)) ∉
          tsd (cubeDomain 3)) ∧
      ∃ t ∈ Icc 0 T, ∀ᶠ N in atTop,
        rows2Equiv (((sh N).ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2) ∉
          symSub ℝ (cubeDomain 3)

/-- **The failure half of item 4 on the cube with the thesis' boundary conditions**: the TSD
constraint does not reduce `L` (`not_isReducing_thesisCube`), and the finite element scheme
(6.5) with the elements of Table 6.1 converges to the wrong physics (`StandardCubeFailure`,
`Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`).
[QuennevilleBelair2015], Prop 4.17, §6.3, (6.5), Table 6.1 -/
theorem einsteinBianchi_thesisCube {T : ℝ} (hT0 : 0 < T) :
    (∀ (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
        (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection],
      betaDatum ∈ K → (∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) →
        ¬ matrixComplex.wave.IsReducing K) ∧
    StandardCubeFailure hT hB hT0 :=
  ⟨fun K _ h0 hE => not_isReducing_thesisCube K h0 hE, waveFEM_converges_to_non_tsd hT hB hT0⟩

/-- **The verdict on the cube with the thesis' boundary conditions**: the TSD constraint
`thesisTSD` contains the datum `(0, 0, (0, β))` and does not reduce `L`; more generally no closed
constraint containing the datum and imposing `E ∈ L²(TSD)` reduces `L`; admissible smoothers
exist, and for all of them the full conclusion of `einsteinBianchi_thesisCube` holds: the exact
solution from the datum leaves TSD, the scheme has solutions whose initial states converge, every
such family converges to the exact solution uniformly on `[0, T]`, and its discrete fields leave
TSD at some `t ∈ [0, T]` for all large `N`. [QuennevilleBelair2015], Prop 4.17, §6.3 -/
structure StandardCubeVerdict : Prop where
  /-- the TSD constraint contains the datum `(0, 0, (0, β))` -/
  betaDatum_mem : betaDatum ∈ thesisTSD
  /-- and does not reduce `L` -/
  not_isReducing : ¬ matrixComplex.wave.IsReducing thesisTSD
  /-- no closed constraint containing the datum and imposing `E ∈ L²(TSD)` reduces `L` -/
  not_isReducing_of_mem (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
      (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection]
    (h0 : betaDatum ∈ K) (hE : ∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) :
    ¬ matrixComplex.wave.IsReducing K
  /-- admissible smoothers exist -/
  exists_estimates : ∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ),
    PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C ∧
      PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C
  /-- for each of them, the scheme converges to the exact solution, which leaves TSD, and its
  discrete fields leave TSD -/
  failure {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) {T : ℝ} (hT0 : 0 < T) :
    StandardCubeFailure hT hB hT0

theorem standardCubeVerdict : StandardCubeVerdict :=
  ⟨betaDatum_mem_thesisTSD, not_isReducing_thesisTSD,
    fun K _ h0 hE => not_isReducing_thesisCube K h0 hE,
    have ⟨p, C, hT, hB, _⟩ := Feec.Models.Cube.FEM.tableRows_H1; ⟨p, C, hT, hB⟩,
    fun hT hB _ hT0 => (einsteinBianchi_thesisCube hT hB hT0).2⟩

end StandardBoundary

/-! ### Summary -/

/-- **The constrained FEEC verdicts for the linearized Einstein–Bianchi system**
([QuennevilleBelair2015], Ch. 4–6), each the full statement of the corresponding headline:

1. `𝕋³`, Fourier spectral method (`TorusVerdict`, from `constrainedFEEC torusFEEC`): the TSD
   constraint reduces `L` and propagates for all `t ∈ ℝ`; the discrete solutions converge
   uniformly on `[0, T]` for data in `D(L)`; the residual of data in `D(L) ∩ K` is bounded by the
   error and tends to `0`; error and residual are `≤ (1 + C_P)(1 + t)² (N + 1)^{-α} ‖ξ₀‖_α` on the
   approximation classes; and (`TorusSobolevVerdict`) `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}`
   for TSD data in `H^{2+s}`; non-vacuity (`TorusNonvacuous`) by a band-limited and a
   non-band-limited non-stationary TSD datum;
2. the cube with mirror boundary conditions, cosine–sine spectral method (`MirrorVerdict`,
   `MirrorSobolevVerdict`, `MirrorNonvacuous`): the same conclusions as on `𝕋³`, with the
   Sobolev rate for TSD data with mirror extension in `H^{2+s}`;
3. the mirror finite element scheme (6.5) (`MirrorFEMVerdict`): admissible smoothers exist, and
   for each of them the scheme, started from the elliptic projection (6.4), converges to the TSD
   solution `e^{tL} ξ₀`, at the rate `O(h)` for TSD data in `D(L³)` and `O(hˢ)` for TSD data in
   `H^{2+s}`, `0 ≤ s ≤ 1`;
4. the cube with the thesis' boundary conditions (`StandardCubeVerdict`): the TSD constraint
   `thesisTSD` does not reduce `L`, and the thesis' scheme (6.5) converges to the exact solution,
   which leaves TSD, so its discrete fields leave TSD (the failure half of item 4 of the
   constrained FEEC theorem). -/
theorem einsteinBianchi_constrainedFEEC_summary :
    -- 1. `𝕋³`
    (TorusVerdict ∧ TorusSobolevVerdict ∧ TorusNonvacuous) ∧
    -- 2. the mirror cube, spectral
    (MirrorVerdict ∧ MirrorSobolevVerdict ∧ MirrorNonvacuous) ∧
    -- 3. the mirror cube, finite elements
    MirrorFEMVerdict ∧
    -- 4. the cube with the thesis' boundary conditions
    StandardCubeVerdict :=
  ⟨⟨einsteinBianchi_torus_constrainedFEEC, einsteinBianchi_torus_constrainedFEEC_sobolev,
      torus_nonvacuous⟩,
    ⟨einsteinBianchi_mirror_constrainedFEEC, einsteinBianchi_mirror_constrainedFEEC_sobolev,
      mirror_nonvacuous⟩,
    mirrorFEMVerdict, standardCubeVerdict⟩

end Feec.Instances.EinsteinBianchi
