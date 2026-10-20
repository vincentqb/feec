module

public import Feec.Instances.EinsteinBianchiSobolev
public import Feec.Models.Euclidean.BGG
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
  `torusFEEC` (bands `|n|_∞ ≤ N`, `Feec.Models.Torus.BGG.bandFamily`) is a constrained FEEC
  discretization, `K` reduces `L`, so TSD propagates for all `t ∈ ℝ`, the discrete solutions
  converge uniformly on `[0, T]`, the constraint residual tends to `0`, and for data in the
  approximation class of order `α` the error and the residual are
  `≤ (1 + C_P)(1 + t)² (N + 1)^{-α} ‖ξ₀‖_α`; for TSD data in `H^{2+s}(𝕋³)`, `s ≥ 0`, they are
  `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` (`einsteinBianchi_torus_constrainedFEEC_sobolev`,
  through `mem_rateData_of_memSobStateT`). Non-vacuity (`torus_nonvacuous`): a band-limited
  non-stationary TSD datum lies in every class, and the TSD datum `decayState`, in `H³` but not
  band-limited for any `N`, lies in the class of order `1`.
* **`ℝ³`** (`einsteinBianchi_euclidean`): well-posedness and propagation (`K` reduces `L`). The
  constrained FEEC theorem needs a family of finite-dimensional subcomplexes with uniformly
  bounded commuting projections approximating `L²(ℝ³)`; no such family is constructed here (the
  Fourier bands of `ℝ³` are infinite-dimensional), so items 3–4 are not stated on `ℝ³`.
* **The cube `Q = (0, ½)³` with mirror boundary conditions**:
  - the cosine–sine spectral discretization `mirrorFEEC` (`Feec.Models.Cube.MirrorBGG.bandFamilyQ`)
    is a constrained FEEC discretization of `MirrorBGG.complexQ` with the reducing constraint
    `MirrorBGG.tsdQ` (`einsteinBianchi_mirror_constrainedFEEC`: propagation, convergence to the
    TSD solution, residual `→ 0`, rates for the approximation classes; non-vacuity
    `mirror_nonvacuous`), with the **Sobolev rate** `(1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}`
    for TSD data in `H^{2+s}`, `s ≥ 0` (`einsteinBianchi_mirror_constrainedFEEC_sobolev`, through
    `Feec.Models.Cube.MirrorWeakSymmetry.TSDDatum.mem_rateData_of_memSobState`);
  - the finite element scheme (6.5) with mirror boundary conditions
    (`Feec.Models.Cube.MirrorWeakSymmetry.mirrorFEM`) discretizes the two rows of the
    BGG construction (`Feec.BGG.Discrete`, coupled by `S₀,ₕ = π¹S⁰`), not the BGG Hilbert complex
    by subcomplexes, so it is not an instance of `ConstrainedFEEC`; the model theorems give its
    convergence to the TSD solution `e^{tL} ξ₀` of the same complex
    (`einsteinBianchi_mirror_waveFEM`), the `O(h)` rate for `D(L³)` data
    (`einsteinBianchi_mirror_waveFEM_rate`) and the `O(hˢ)` rate for `H^{2+s}` data
    (`einsteinBianchi_mirror_waveFEM_rate_sobolev`).
* **The cube with the thesis' boundary conditions** (`einsteinBianchi_thesisCube`,
  `ThesisCubeVerdict`): the TSD constraint `thesisTSD = {0} × L²(TSD) × ({0} × L²(TSD))` of the
  matrix model contains the datum `(0, 0, (0, β))` and does not reduce `L`
  (`not_isReducing_thesisTSD`); more generally every closed subspace containing the datum and
  imposing `E ∈ L²(TSD)` fails to reduce `L` (`not_isReducing_thesisCube`);
  the scheme (6.5) of the thesis converges to the exact solution, which leaves TSD, and the
  discrete fields leave TSD for all large `N`
  (`Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`): the failure half of
  item 4. This half is read on the finite element scheme, not through `ConstrainedFEEC`: no
  family of finite-dimensional subcomplexes of the thesis' complex with commuting projections is
  constructed here.

**Scope.** The spectral rate classes are approximation classes (truncation errors of
`ξ₀, L ξ₀, L² ξ₀` of order `(N + 1)^{-α}`); they contain the TSD Sobolev data on `𝕋³` and on the
mirror cube. The generic rate keeps the factor `(1 + C_P)(1 + t)²` of `constrainedFEEC_rate`. The
finite element statements and the thesis-BC failure are not applications of `constrainedFEEC`:
they are the model theorems with the exact solution `e^{tL} ξ₀` (the thesis-BC non-reduction is
proved from the explicit solution of the datum `(0, 0, (0, β))` and the propagation of reducing
subspaces). On `ℝ³` only items 1–2 are stated.

`einsteinBianchi_constrainedFEEC_summary` is the conjunction of the full verdicts (`TorusVerdict`,
`TorusSobolevVerdict`, `TorusNonvacuous`, `EuclideanVerdict`, `MirrorVerdict`,
`MirrorSobolevVerdict`, `MirrorNonvacuous`, `MirrorFEMVerdict`, `ThesisCubeVerdict`); each headline
theorem proves one of them.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 4 (§4.4, §4.6, §4.10, Thm 4.14, Prop 4.17), Ch. 5 ((5.1)), Ch. 6 (§6.1–6.3, (6.5))
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3
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
method): `K` reduces `L`; TSD data stay TSD for all `t ∈ ℝ`; for `ξ₀ ∈ D(L)` the discrete
solutions converge to `e^{tL} ξ₀` uniformly on `[0, T]`; for `ξ₀ ∈ D(L) ∩ K` the constraint
residual is bounded by the error and tends to `0` uniformly on `[0, T]`; for data in the
approximation class of order `α` (`SpectralFamily.rateData`), the error and the residual are
`≤ (1 + C_P)(1 + t)² (N + 1)^{-α} ‖ξ₀‖_α`. -/
abbrev TorusVerdict : Prop :=
    complex.wave.IsReducing (totalSub constraint) ∧
    (∀ t, ∀ x ∈ totalSub constraint, complex.waveGroup.S t x ∈ totalSub constraint) ∧
    (∀ T : ℝ, ∀ x : complex.wave.domain, TendstoUniformlyOn
      (fun N t => complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
      (fun t => complex.waveGroup.S t x) atTop (Icc 0 T)) ∧
    (∀ x : complex.wave.domain, (x : PiLp 2 Space) ∈ totalSub constraint → ∀ T : ℝ,
      (∀ N t, infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
          (totalSub constraint : Set (PiLp 2 Space)) ≤
        ‖complex.waveGroup.S t x -
          complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t)‖) ∧
      TendstoUniformlyOn
        (fun N t => infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
          (totalSub constraint : Set (PiLp 2 Space))) (fun _ => 0) atTop (Icc 0 T)) ∧
    ∀ (α T : ℝ) (x : PiLp 2 Space) (hx : x ∈ bandFamily.rateData α) (N : ℕ), ∀ t ∈ Icc 0 T,
      ‖complex.waveGroup.S t x -
          complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hx.1⟩) t)‖ ≤
        (1 + ellipticConst complex) * (1 + t) ^ 2 *
          (1 * (1 / ((N : ℝ) + 1)) ^ α * bandFamily.rateNorm α x) ∧
      (x ∈ totalSub constraint →
        infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hx.1⟩) t))
            (totalSub constraint : Set (PiLp 2 Space)) ≤
          (1 + ellipticConst complex) * (1 + t) ^ 2 *
            (1 * (1 / ((N : ℝ) + 1)) ^ α * bandFamily.rateNorm α x))

/-- **The constrained FEEC theorem for the EB system on `𝕋³`** (Fourier spectral method):
`TorusVerdict`, read off `constrainedFEEC torusFEEC`. [QuennevilleBelair2015], Thm 4.14,
Prop 4.17, Ch. 6 -/
theorem einsteinBianchi_torus_constrainedFEEC : TorusVerdict := by
  obtain ⟨-, hprop, hconv, hrate, hres, -⟩ := constrainedFEEC torusFEEC
  exact ⟨torusFEEC_isReducing, hprop.1 torusFEEC_isReducing, fun T => (hconv T).1,
    fun x hx T => hres torusFEEC_isReducing x hx T,
    fun α T x hx N t ht => ⟨hrate T (torusRate α T) x hx N t ht,
      fun hxK => constrainedFEEC_residual_rate torusFEEC torusFEEC_isReducing (torusRate α T) hx
        hxK N ht⟩⟩

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

/-- **The Sobolev verdict on `𝕋³`**: a TSD datum `ξ₀` in `H^{2+s}(𝕋³)`, `s ≥ 0`, lies in `D(L)`,
and the error and the constraint residual of the Fourier spectral solutions are
`≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` on `[0, T]`. -/
abbrev TorusSobolevVerdict : Prop :=
  ∀ (x : PiLp 2 Space), x ∈ totalSub constraint → ∀ {s : ℝ}, 0 ≤ s → MemSobStateT (2 + s) x →
    x ∈ complex.wave.domain ∧ ∀ (hx : x ∈ complex.wave.domain) (N : ℕ) {T t : ℝ}, t ∈ Icc 0 T →
      ‖complex.waveGroup.S t x -
          complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hx⟩) t)‖ ≤
        (1 + ellipticConst complex) * (1 + t) ^ 2 *
          ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x))) ∧
      infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hx⟩) t))
          (totalSub constraint : Set (PiLp 2 Space)) ≤
        (1 + ellipticConst complex) * (1 + t) ^ 2 *
          ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)))

/-- **Sobolev rate of the constrained FEEC theorem on `𝕋³`**: `TorusSobolevVerdict`, from the
rate of `einsteinBianchi_torus_constrainedFEEC` for the class of order `s`, which contains the
TSD data of `H^{2+s}` (`mem_rateData_of_memSobStateT`). [QuennevilleBelair2015], Thm 4.14,
Ch. 6 -/
theorem einsteinBianchi_torus_constrainedFEEC_sobolev : TorusSobolevVerdict := by
  intro x hK s hs h
  obtain ⟨hD, hn⟩ := mem_rateData_of_memSobStateT hK hs h
  refine ⟨hD.1, fun hx N T t ht => ?_⟩
  have hrate := einsteinBianchi_torus_constrainedFEEC.2.2.2.2 s T x hD N t ht
  have hC : 0 ≤ (1 + ellipticConst complex) * (1 + t) ^ 2 := by
    have := ellipticConst_nonneg complex
    have : 0 ≤ t := ht.1
    positivity
  have hle : 1 * (1 / ((N : ℝ) + 1)) ^ s * bandFamily.rateNorm s x ≤
      (1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)) := by
    rw [one_mul]; exact mul_le_mul_of_nonneg_left hn (by positivity)
  exact ⟨hrate.1.trans (mul_le_mul_of_nonneg_left hle hC),
    (hrate.2 hK).trans (mul_le_mul_of_nonneg_left hle hC)⟩

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

/-! ### `ℝ³` -/

section Euclidean

open Feec.Models.Euclidean.BGG

/-- **The verdict on `ℝ³`**: well-posed for data in `D(L)` (Stone), and the TSD constraint
reduces `L`, so TSD data stay TSD for all `t ∈ ℝ`. -/
abbrev EuclideanVerdict : Prop :=
    (∀ x ∈ complex.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution complex.wave (Icc 0 T) 0 (fun t => complex.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution complex.wave (Icc 0 T) 0 U →
        EqOn U (fun t => complex.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖complex.waveGroup.S t x‖ = ‖x‖) ∧
    complex.wave.IsReducing (totalSub constraint) ∧
    ∀ t, ∀ x ∈ totalSub constraint, complex.waveGroup.S t x ∈ totalSub constraint

/-- **The EB system on `ℝ³`**: `EuclideanVerdict` (items 1–2 of the constrained FEEC theorem,
`constrainedFEEC_wellPosed` and the reducing subcomplex). [QuennevilleBelair2015], Thm 4.6,
Prop 4.17, Ch. 6 -/
theorem einsteinBianchi_euclidean : EuclideanVerdict :=
  ⟨fun _ hx T => have h := constrainedFEEC_wellPosed hx T; ⟨h.1, h.2.1, h.2.2.2⟩,
    reducingSubcomplex.isReducing_wave, fun t _ hx => waveGroup_mem t hx⟩

end Euclidean

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
boundary conditions** (cosine–sine spectral method): `K` reduces `L`; TSD data stay TSD for all
`t ∈ ℝ`; the discrete solutions converge to the TSD solution uniformly on `[0, T]`; the
constraint residual is bounded by the error and tends to `0`; for data in the approximation class
of order `α` the error and the residual are `≤ (1 + C_P)(1 + t)² (N + 1)^{-α} ‖ξ₀‖_α`. -/
abbrev MirrorVerdict : Prop :=
    complexQ.wave.IsReducing (totalSub tsdQ) ∧
    (∀ t, ∀ x ∈ totalSub tsdQ, complexQ.waveGroup.S t x ∈ totalSub tsdQ) ∧
    (∀ T : ℝ, ∀ x : complexQ.wave.domain, TendstoUniformlyOn
      (fun N t => complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
      (fun t => complexQ.waveGroup.S t x) atTop (Icc 0 T)) ∧
    (∀ x : complexQ.wave.domain, (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ → ∀ T : ℝ,
      (∀ N t, infDist (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
          (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
        ‖complexQ.waveGroup.S t x -
          complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t)‖) ∧
      TendstoUniformlyOn
        (fun N t => infDist
          (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
          (totalSub tsdQ : Set (PiLp 2 SpaceQ))) (fun _ => 0) atTop (Icc 0 T)) ∧
    ∀ (α T : ℝ) (x : PiLp 2 SpaceQ) (hx : x ∈ bandFamilyQ.rateData α) (N : ℕ), ∀ t ∈ Icc 0 T,
      ‖complexQ.waveGroup.S t x -
          complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨x, hx.1⟩) t)‖ ≤
        (1 + ellipticConst complexQ) * (1 + t) ^ 2 *
          (1 * (1 / ((N : ℝ) + 1)) ^ α * bandFamilyQ.rateNorm α x) ∧
      (x ∈ totalSub tsdQ →
        infDist (complexQ.totalD.graphFst
            (mirrorFEEC.discrete N (waveLift complexQ ⟨x, hx.1⟩) t))
            (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
          (1 + ellipticConst complexQ) * (1 + t) ^ 2 *
            (1 * (1 / ((N : ℝ) + 1)) ^ α * bandFamilyQ.rateNorm α x))

/-- **The constrained FEEC theorem for the EB system on the cube with mirror boundary
conditions**: `MirrorVerdict`, read off `constrainedFEEC mirrorFEEC`. [QuennevilleBelair2015],
Thm 4.14, Prop 4.17 (corrected), Ch. 6 -/
theorem einsteinBianchi_mirror_constrainedFEEC : MirrorVerdict := by
  obtain ⟨-, hprop, hconv, hrate, hres, -⟩ := constrainedFEEC mirrorFEEC
  exact ⟨mirrorFEEC_isReducing, hprop.1 mirrorFEEC_isReducing, fun T => (hconv T).1,
    fun x hx T => hres mirrorFEEC_isReducing x hx T,
    fun α T x hx N t ht => ⟨hrate T (mirrorRate α T) x hx N t ht,
      fun hxK => constrainedFEEC_residual_rate mirrorFEEC mirrorFEEC_isReducing (mirrorRate α T)
        hx hxK N ht⟩⟩

/-- **The Sobolev verdict on the mirror cube**: for a TSD datum `ξ₀ ∈ D(L²)` with mirror
extension in `H^{2+s}`, `s ≥ 0`, the error and the constraint residual of the cosine–sine
spectral solutions are `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` on `[0, T]`. -/
abbrev MirrorSobolevVerdict : Prop :=
  ∀ (D : Models.Cube.MirrorWeakSymmetry.TSDDatum) {s : ℝ}, 0 ≤ s →
    Models.Cube.MirrorWeakSymmetry.MemSobState (2 + s) D.U₀ → ∀ (N : ℕ) {T t : ℝ},
    t ∈ Icc 0 T →
    ‖complexQ.waveGroup.S t D.U₀ -
        complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨D.U₀, D.mem⟩) t)‖ ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀))) ∧
    infDist (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨D.U₀, D.mem⟩) t))
        (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀)))

/-- **Sobolev rate of the constrained FEEC theorem on the mirror cube**: `MirrorSobolevVerdict`,
from `constrainedFEEC_rate` for the rate class of order `s`, which contains the datum
(`mem_rateData_of_memSobState`). The cos datum lies in every `H^{2+s}`
(`cosDatum_memSobState`). [QuennevilleBelair2015], Thm 4.14, Ch. 6 -/
theorem einsteinBianchi_mirror_constrainedFEEC_sobolev : MirrorSobolevVerdict := by
  intro D s hs h N T t ht
  obtain ⟨hD, hn⟩ := mem_rateData_of_memSobState D hs h
  have hrate := einsteinBianchi_mirror_constrainedFEEC.2.2.2.2 s T D.U₀ hD N t ht
  have hC : 0 ≤ (1 + ellipticConst complexQ) * (1 + t) ^ 2 := by
    have := ellipticConst_nonneg complexQ
    have : 0 ≤ t := ht.1
    positivity
  have hle : 1 * (1 / ((N : ℝ) + 1)) ^ s * bandFamilyQ.rateNorm s D.U₀ ≤
      (1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀)) := by
    rw [one_mul]; exact mul_le_mul_of_nonneg_left hn (by positivity)
  exact ⟨hrate.1.trans (mul_le_mul_of_nonneg_left hle hC),
    (hrate.2 D.tsd).trans (mul_le_mul_of_nonneg_left hle hC)⟩

/-- The mirror datum `(0, E₀, (0, 0))` on `Q` is band-limited: its mirror extension is the
torus datum, with modes `±k₀`. -/
theorem cosStateQ_mem_band : cosStateQ ∈ totalSub (bandFamilyQ.B 1) := fun i => by
  change J i (cosStateQ i) ∈ Models.Torus.BGG.band 1 i
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
`O(hˢ)` rate for `H^{2+s}` data (`MirrorWaveFEMRateSobolev`). -/
abbrev MirrorFEMVerdict : Prop :=
  (∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
      ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
        ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) ∧
    ∀ {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
      (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
      (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C),
      MirrorWaveFEMConvergence hT hB ∧ MirrorWaveFEMRate hT hB ∧ MirrorWaveFEMRateSobolev hT hB

theorem mirrorFEMVerdict : MirrorFEMVerdict :=
  ⟨exists_mirror_estimates, fun hT hB => ⟨einsteinBianchi_mirror_waveFEM hT hB,
    einsteinBianchi_mirror_waveFEM_rate hT hB, einsteinBianchi_mirror_waveFEM_rate_sobolev hT hB⟩⟩

end MirrorFEM

/-! ### The cube with the thesis' boundary conditions: the failure half -/

section Thesis

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
abbrev ThesisCubeFailure {T : ℝ} (hT0 : 0 < T) : Prop :=
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
(6.5) with the elements of Table 6.1 converges to the wrong physics (`ThesisCubeFailure`,
`Feec.EinsteinBianchi.BoundedConvergence.waveFEM_converges_to_non_tsd`).
[QuennevilleBelair2015], Prop 4.17, §6.3, (6.5), Table 6.1 -/
theorem einsteinBianchi_thesisCube {T : ℝ} (hT0 : 0 < T) :
    (∀ (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
        (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection],
      betaDatum ∈ K → (∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) →
        ¬ matrixComplex.wave.IsReducing K) ∧
    ThesisCubeFailure hT hB hT0 :=
  ⟨fun K _ h0 hE => not_isReducing_thesisCube K h0 hE, waveFEM_converges_to_non_tsd hT hB hT0⟩

/-- **The verdict on the cube with the thesis' boundary conditions**: the TSD constraint
`thesisTSD` contains the datum `(0, 0, (0, β))` and does not reduce `L`; more generally no closed
constraint containing the datum and imposing `E ∈ L²(TSD)` reduces `L`; admissible smoothers
exist, and for all of them the full conclusion of `einsteinBianchi_thesisCube` holds: the exact
solution from the datum leaves TSD, the scheme has solutions whose initial states converge, every
such family converges to the exact solution uniformly on `[0, T]`, and its discrete fields leave
TSD at some `t ∈ [0, T]` for all large `N`. [QuennevilleBelair2015], Prop 4.17, §6.3 -/
abbrev ThesisCubeVerdict : Prop :=
    (betaDatum ∈ thesisTSD ∧ ¬ matrixComplex.wave.IsReducing thesisTSD) ∧
    (∀ (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
        (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection],
      betaDatum ∈ K → (∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) →
        ¬ matrixComplex.wave.IsReducing K) ∧
    ((∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ),
        PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C ∧
          PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) ∧
      ∀ {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
        (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
        (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) {T : ℝ} (hT0 : 0 < T),
        ThesisCubeFailure hT hB hT0)

theorem thesisCubeVerdict : ThesisCubeVerdict := by
  refine ⟨⟨betaDatum_mem_thesisTSD, not_isReducing_thesisTSD⟩,
    fun K _ h0 hE => not_isReducing_thesisCube K h0 hE, ?_, fun hT hB T hT0 =>
      (einsteinBianchi_thesisCube hT hB hT0).2⟩
  obtain ⟨p, C, hT, hB, -⟩ := Feec.Models.Cube.FEM.tableRows_H1
  exact ⟨p, C, hT, hB⟩

end Thesis

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
2. `ℝ³` (`EuclideanVerdict`): well-posedness and propagation (`K` reduces `L`);
3. the cube with mirror boundary conditions, cosine–sine spectral method (`MirrorVerdict`,
   `MirrorSobolevVerdict`, `MirrorNonvacuous`): the same conclusions as on `𝕋³`, with the
   Sobolev rate for TSD data with mirror extension in `H^{2+s}`;
4. the mirror finite element scheme (6.5) (`MirrorFEMVerdict`): admissible smoothers exist, and
   for each of them the scheme, started from the elliptic projection (6.4), converges to the TSD
   solution `e^{tL} ξ₀`, at the rate `O(h)` for TSD data in `D(L³)` and `O(hˢ)` for TSD data in
   `H^{2+s}`, `0 ≤ s ≤ 1`;
5. the cube with the thesis' boundary conditions (`ThesisCubeVerdict`): the TSD constraint
   `thesisTSD` does not reduce `L`, and the thesis' scheme (6.5) converges to the exact solution,
   which leaves TSD, so its discrete fields leave TSD (the failure half of item 4). -/
theorem einsteinBianchi_constrainedFEEC_summary :
    -- 1. `𝕋³`
    (TorusVerdict ∧ TorusSobolevVerdict ∧ TorusNonvacuous) ∧
    -- 2. `ℝ³`
    EuclideanVerdict ∧
    -- 3. the mirror cube, spectral
    (MirrorVerdict ∧ MirrorSobolevVerdict ∧ MirrorNonvacuous) ∧
    -- 4. the mirror cube, finite elements
    MirrorFEMVerdict ∧
    -- 5. the cube with the thesis' boundary conditions
    ThesisCubeVerdict :=
  ⟨⟨einsteinBianchi_torus_constrainedFEEC, einsteinBianchi_torus_constrainedFEEC_sobolev,
      torus_nonvacuous⟩,
    einsteinBianchi_euclidean,
    ⟨einsteinBianchi_mirror_constrainedFEEC, einsteinBianchi_mirror_constrainedFEEC_sobolev,
      mirror_nonvacuous⟩,
    mirrorFEMVerdict, thesisCubeVerdict⟩

end Feec.Instances.EinsteinBianchi
