module

public import Feec.Instances.EinsteinBianchiSobolev
public import Feec.Models.Cube.MirrorWaveRegularity
public import Feec.Physics.EinsteinBianchi.BoundedConvergence

/-!
# The constrained FEEC theorem for the linearized Einstein–Bianchi system

The linearized Einstein–Bianchi system with weakly imposed symmetry ([QuennevilleBelair2015],
Ch. 5–6) is the Hodge wave equation of the BGG complex (5.1) with the TSD constraint; this file
applies the constrained FEEC theorem to its spectral discretizations on `𝕋³` and on the mirror
cube.

## Main results

* `einsteinBianchi_torus_constrainedFEEC_sobolev`: the spectral method on `𝕋³`, with rates.
* `einsteinBianchi_mirror_waveFEM_rate`: the mirror scheme (6.5) converges at the rate `O(h)` for
  TSD data in `D(L³)`.
* `einsteinBianchi_thesisCube`: with the boundary conditions of §6.3, TSD does not reduce `L`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

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

/-- The Fourier spectral discretization of the EB system on `𝕋³`, with the TSD constraint. -/
def torusFEEC : ConstrainedFEEC complex ℕ :=
  bandFamily.toFEEC (totalSub constraint) isClosed_totalSub

theorem torusFEEC_isReducing : complex.wave.IsReducing torusFEEC.K :=
  reducingSubcomplex.isReducing_wave

/-- The rate classes of the torus discretization: the approximation class of order `α`. -/
abbrev torusRate (α T : ℝ) : torusFEEC.RateClass T :=
  bandFamily.rateClass (totalSub constraint) isClosed_totalSub α T

/-- **The constrained FEEC verdict for the EB system on `𝕋³`**, the TSD constraint reducing `L`. -/
structure TorusVerdict : Prop extends torusFEEC.Verdict where
  isReducing : complex.wave.IsReducing torusFEEC.K

/-- **The constrained FEEC theorem for the EB system on `𝕋³`** (Fourier spectral method):
`TorusVerdict`. [QuennevilleBelair2015], Thm 4.14, Prop 4.17, Ch. 6 -/
theorem einsteinBianchi_torus_constrainedFEEC : TorusVerdict :=
  { constrainedFEEC torusFEEC with isReducing := torusFEEC_isReducing }

theorem mem_bandN_one_of_mem {n : Fin 3 → ℤ}
    (hn : n ∈ ({Models.Cube.Mirror.k0, -Models.Cube.Mirror.k0} : Finset (Fin 3 → ℤ))) :
    n ∈ Fourier.Torus.bandN 1 := by
  intro j
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl <;> fin_cases j <;> simp [Models.Cube.Mirror.k0]

theorem cosState_mem_band : Models.Cube.MirrorBGG.cosState ∈ totalSub (band 1) := fun i => by
  rw [Fourier.mem_band_iff, MeasureTheory.Measure.ae_count_iff]
  intro n hn
  by_contra h
  exact hn (mem_bandN_one_of_mem (not_not.1 fun h' =>
    h (Models.Cube.MirrorWeakSymmetry.cosState_finite i n h')))

/-- **The Sobolev verdict on `𝕋³`**: `TorusVerdict`, with the rates of TSD data in `H^{2+s}`. -/
structure TorusSobolevVerdict : Prop extends TorusVerdict where
  /-- a TSD datum in `H^{2+s}`, `s ≥ 0`, lies in `D(L)` -/
  mem_domain_sobolev {x : PiLp 2 Space} (hxK : x ∈ torusFEEC.K) {s : ℝ} (hs : 0 ≤ s)
    (hx : MemSobStateT (2 + s) x) : x ∈ complex.wave.domain
  /-- the error is `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` -/
  rate_sobolev {x : PiLp 2 Space} (hxK : x ∈ torusFEEC.K) {s : ℝ} (hs : 0 ≤ s)
    (hx : MemSobStateT (2 + s) x) (hD : x ∈ complex.wave.domain) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖complex.waveGroup.S t x -
        complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hD⟩) t)‖ ≤
      (1 + ellipticConst complex) * (1 + t) ^ 2 *
        ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)))
  /-- the same bound for the constraint residual -/
  tsd_residual_rate_sobolev {x : PiLp 2 Space} (hxK : x ∈ torusFEEC.K) {s : ℝ} (hs : 0 ≤ s)
    (hx : MemSobStateT (2 + s) x) (hD : x ∈ complex.wave.domain) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨x, hD⟩) t))
        (torusFEEC.K : Set (PiLp 2 Space)) ≤
      (1 + ellipticConst complex) * (1 + t) ^ 2 *
        ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)))

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

/-- **Sobolev rate of the constrained FEEC theorem on `𝕋³`**: `TorusSobolevVerdict`.
[QuennevilleBelair2015], Thm 4.14, Ch. 6 -/
theorem einsteinBianchi_torus_constrainedFEEC_sobolev : TorusSobolevVerdict :=
  have V := einsteinBianchi_torus_constrainedFEEC
  { V with
    mem_domain_sobolev := fun hxK _ hs hx => (mem_rateData_of_memSobStateT hxK hs hx).1.1
    rate_sobolev := fun hxK _ hs hx _ N T _ ht =>
      (V.rate (torusRate _ T) (mem_rateData_of_memSobStateT hxK hs hx).1 N ht).trans
        (torus_rate_le_sobolev hxK hs hx N ht.1)
    tsd_residual_rate_sobolev := fun hxK _ hs hx _ N T _ ht =>
      (V.residual_rate V.isReducing (torusRate _ T) (mem_rateData_of_memSobStateT hxK hs hx).1
        hxK N ht).trans (torus_rate_le_sobolev hxK hs hx N ht.1) }

/-- **Non-vacuity on `𝕋³`**: non-stationary TSD data in the classes, one not band-limited. -/
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

/-- The cosine–sine spectral discretization of the EB system on the cube with mirror conditions. -/
def mirrorFEEC : ConstrainedFEEC complexQ ℕ :=
  bandFamilyQ.toFEEC (totalSub tsdQ) isClosed_totalSub

theorem mirrorFEEC_isReducing : complexQ.wave.IsReducing mirrorFEEC.K :=
  reducingSubcomplexQ.isReducing_wave

/-- The rate classes of the mirror spectral discretization. -/
abbrev mirrorRate (α T : ℝ) : mirrorFEEC.RateClass T :=
  bandFamilyQ.rateClass (totalSub tsdQ) isClosed_totalSub α T

/-- **The constrained FEEC verdict on the mirror cube**, the TSD constraint reducing `L`. -/
structure MirrorVerdict : Prop extends mirrorFEEC.Verdict where
  isReducing : complexQ.wave.IsReducing mirrorFEEC.K

/-- **The constrained FEEC theorem for the EB system on the cube with mirror boundary
conditions**: `MirrorVerdict`. [QuennevilleBelair2015], Thm 4.14, Prop 4.17 (adapted), Ch. 6 -/
theorem einsteinBianchi_mirror_constrainedFEEC : MirrorVerdict :=
  { constrainedFEEC mirrorFEEC with isReducing := mirrorFEEC_isReducing }

/-- **The Sobolev verdict on the mirror cube**: the rates of TSD data in `D(L²) ∩ H^{2+s}`. -/
structure MirrorSobolevVerdict : Prop extends MirrorVerdict where
  /-- the error is `≤ (1 + C_P)(1 + t)² (N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` -/
  rate_sobolev (D : Models.Cube.MirrorWeakSymmetry.TSDDatum) {s : ℝ} (hs : 0 ≤ s)
    (hD : Models.Cube.MirrorWeakSymmetry.MemSobState (2 + s) D.U₀) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖complexQ.waveGroup.S t D.U₀ -
        complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨D.U₀, D.mem⟩) t)‖ ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀)))
  /-- the same bound for the constraint residual -/
  tsd_residual_rate_sobolev (D : Models.Cube.MirrorWeakSymmetry.TSDDatum) {s : ℝ} (hs : 0 ≤ s)
    (hD : Models.Cube.MirrorWeakSymmetry.MemSobState (2 + s) D.U₀) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    infDist (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ ⟨D.U₀, D.mem⟩) t))
        (mirrorFEEC.K : Set (PiLp 2 SpaceQ)) ≤
      (1 + ellipticConst complexQ) * (1 + t) ^ 2 * ((1 / ((N : ℝ) + 1)) ^ s *
        (3 * √(Models.Cube.MirrorWeakSymmetry.sobState (2 + s) D.U₀)))

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

/-- **Sobolev rate of the constrained FEEC theorem on the mirror cube**: `MirrorSobolevVerdict`.
[QuennevilleBelair2015], Thm 4.14, Ch. 6 -/
theorem einsteinBianchi_mirror_constrainedFEEC_sobolev : MirrorSobolevVerdict :=
  have V := einsteinBianchi_mirror_constrainedFEEC
  { V with
    rate_sobolev := fun D _ hs hD N T _ ht =>
      (V.rate (mirrorRate _ T) (mem_rateData_of_memSobState D hs hD).1 N ht).trans
        (mirror_rate_le_sobolev D hs hD N ht.1)
    tsd_residual_rate_sobolev := fun D _ hs hD N T _ ht =>
      (V.residual_rate V.isReducing (mirrorRate _ T) (mem_rateData_of_memSobState D hs hD).1
        D.tsd N ht).trans (mirror_rate_le_sobolev D hs hD N ht.1) }

theorem cosStateQ_mem_band : cosStateQ ∈ totalSub (bandFamilyQ.B 1) := fun i => by
  change J i (cosStateQ i) ∈ band 1 i
  rw [← HilbertComplex.totalJ_apply, totalJ_cosStateQ]
  exact cosState_mem_band i

/-- **Non-vacuity on the mirror cube**: a non-stationary TSD datum in every class, and `cosDatum`
in every `Hʳ`. -/
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

/-- **Convergence of the mirror scheme (6.5) to the TSD solution `e^{tL} ξ₀`** from (6.4), for TSD
data `ξ₀ ∈ D(L²)`. -/
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
`MirrorWaveFEMConvergence`. [QuennevilleBelair2015], §6.3, (6.5) -/
theorem einsteinBianchi_mirror_waveFEM : MirrorWaveFEMConvergence hT hB :=
  fun D _ hT0 _ hε => mirror_waveFEM hT hB D hT0 D.U_zero (D.isStrongSolution _) hε

/-- **The `O(h)` rate of the mirror scheme (6.5)** for TSD data in `D(L³)`, from (6.4). -/
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

/-- **`O(h)` rate of the mirror scheme (6.5) for TSD data in `D(L³)`**: `MirrorWaveFEMRate`.
[QuennevilleBelair2015], §6.3, (6.5); [AFW2010], §3.3 -/
theorem einsteinBianchi_mirror_waveFEM_rate : MirrorWaveFEMRate hT hB :=
  (mirror_waveFEM_rate_of_mem_domain hT hB).imp fun _ hK =>
    ⟨hK.1, fun N D h3 _ hT0 => hK.2 N D h3 hT0 (U := D.U) D.U_zero (D.isStrongSolution _)⟩

/-- **The `O(hˢ)` rate of the mirror scheme (6.5)** for TSD data in `D(L²) ∩ H^{2+s}`,
`0 ≤ s ≤ 1`. -/
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

/-- **`O(hˢ)` rate of the mirror scheme (6.5) for TSD data in `D(L²) ∩ H^{2+s}`, `0 ≤ s ≤ 1`**:
`MirrorWaveFEMRateSobolev`. [QuennevilleBelair2015], §6.3, (6.5); [AFW2010], §3.3 -/
theorem einsteinBianchi_mirror_waveFEM_rate_sobolev : MirrorWaveFEMRateSobolev hT hB :=
  (mirror_waveFEM_rate_sobolev_of_add_two hT hB).imp fun _ hK =>
    ⟨hK.1, fun N D _ hs0 hs1 hD _ hT0 =>
      hK.2 N D hs0 hs1 hD hT0 (U := D.U) D.U_zero (D.isStrongSolution _)⟩

/-- **The verdict on the mirror finite element scheme (6.5)**, for every admissible smoother. -/
structure MirrorFEMVerdict : Prop where
  exists_estimates : ∃ (ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3) (C : ℝ),
    ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
      ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C
  /-- the scheme converges to the TSD solution -/
  converges {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
    (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
    (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) :
    MirrorWaveFEMConvergence hT hB
  /-- the rate `O(h)` for TSD data in `D(L³)` -/
  rate {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
    (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
    (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) :
    MirrorWaveFEMRate hT hB
  /-- the rate `O(hˢ)` for TSD data in `D(L²) ∩ H^{2+s}`, `0 ≤ s ≤ 1` -/
  rate_sobolev {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
    (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
    (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C) :
    MirrorWaveFEMRateSobolev hT hB

theorem mirrorFEMVerdict : MirrorFEMVerdict :=
  ⟨exists_mirror_estimates, einsteinBianchi_mirror_waveFEM, einsteinBianchi_mirror_waveFEM_rate,
    einsteinBianchi_mirror_waveFEM_rate_sobolev⟩

end MirrorFEM

/-! ### The cube with the boundary conditions of [QuennevilleBelair2015], §6.3 -/

section StandardBoundary

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry
  Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM Feec.EinsteinBianchi.MatrixModel
  Feec.EinsteinBianchi.BoundedFailure Feec.EinsteinBianchi.BoundedConvergence

/-- **No TSD constraint reduces `L` on the cube with the boundary conditions of §6.3**: no closed
`K` containing `(0, 0, (0, β))` and imposing `E ∈ L²(TSD)` reduces the wave operator.
[QuennevilleBelair2015], Prop 4.17, §6.3 -/
theorem not_isReducing_thesisCube
    (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
      (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection]
    (h0 : betaDatum ∈ K) (hE : ∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) :
    ¬ matrixComplex.wave.IsReducing K := by
  intro hK
  obtain ⟨hU0, hU, -, -, ⟨t, ht, hout⟩, -⟩ := betaU_spec (T := 1) one_pos
  exact hout (hE _ (hU.mem_of_isReducing matrixComplex.isSkewAdjoint_wave.isDissipative hK
    (hU0 ▸ h0) (fun _ _ => K.zero_mem) t ht))

/-- The TSD constraint `{0} × L²(TSD) × ({0} × L²(TSD))` of the matrix model. -/
abbrev thesisTSD : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) :=
  totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2 ℝ (cubeDomain 3)))
    (tsd (cubeDomain 3)) (Feec.Counterexamples.BoundedBGG.tsdB (cubeDomain 3)))

theorem isClosed_thesisTSD : IsClosed (thesisTSD : Set (PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) :=
  isClosed_totalSub

theorem betaDatum_mem_thesisTSD : betaDatum ∈ thesisTSD :=
  ShortHilbertComplex.mem_totalSub_family3.2 ⟨Submodule.zero_mem _, Submodule.zero_mem _,
    Feec.Counterexamples.BoundedBGG.mem_tsdB.2 ⟨rfl,
      Feec.Counterexamples.BoundedDomainTSD.betaL2_mem_tsd (isOpen_cubeDomain 3)
        (isBounded_cubeDomain 3)⟩⟩

theorem not_isReducing_thesisTSD : ¬ matrixComplex.wave.IsReducing thesisTSD :=
  not_isReducing_thesisCube thesisTSD betaDatum_mem_thesisTSD fun _ hx =>
    (ShortHilbertComplex.mem_totalSub_family3.1 hx).2.1

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **The scheme (6.5) from `(0, 0, (0, β))`**: the exact solution leaves TSD, and so, for all
large `N`, do the discrete solutions whose initial states converge to the datum. -/
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

/-- **The non-reducing branch on the cube with the boundary conditions of §6.3**: no closed
constraint containing `(0, 0, (0, β))` and imposing `E ∈ L²(TSD)` reduces `L`;
`StandardCubeFailure` holds. [QuennevilleBelair2015], §6.3 -/
theorem einsteinBianchi_thesisCube {T : ℝ} (hT0 : 0 < T) :
    (∀ (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
        (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection],
      betaDatum ∈ K → (∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) →
        ¬ matrixComplex.wave.IsReducing K) ∧
    StandardCubeFailure hT hB hT0 :=
  ⟨fun K _ h0 hE => not_isReducing_thesisCube K h0 hE, waveFEM_converges_to_non_tsd hT hB hT0⟩

/-- **The verdict on the cube with the boundary conditions of [QuennevilleBelair2015], §6.3.** -/
structure StandardCubeVerdict : Prop where
  betaDatum_mem : betaDatum ∈ thesisTSD
  not_isReducing : ¬ matrixComplex.wave.IsReducing thesisTSD
  /-- no closed constraint containing the datum and imposing `E ∈ L²(TSD)` reduces `L` -/
  not_isReducing_of_mem (K : Submodule ℝ (PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
      (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))))) [K.HasOrthogonalProjection]
    (h0 : betaDatum ∈ K) (hE : ∀ x ∈ K, (x 1 : L2F ℝ (cubeDomain 3) Ix) ∈ tsd (cubeDomain 3)) :
    ¬ matrixComplex.wave.IsReducing K
  exists_estimates : ∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ),
    PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C ∧
      PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C
  /-- the scheme converges to the exact solution, which leaves TSD, and for large `N` its fields
  leave TSD -/
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

/-- **The constrained FEEC verdicts for the linearized Einstein–Bianchi system** on `𝕋³` and on
the cube. [QuennevilleBelair2015], Ch. 4–6 -/
theorem einsteinBianchi_constrainedFEEC_summary :
    -- 1. `𝕋³`
    (TorusSobolevVerdict ∧ TorusNonvacuous) ∧
    -- 2. the mirror cube, spectral
    (MirrorSobolevVerdict ∧ MirrorNonvacuous) ∧
    -- 3. the mirror cube, finite elements
    MirrorFEMVerdict ∧
    -- 4. the cube with the thesis' boundary conditions
    StandardCubeVerdict :=
  ⟨⟨einsteinBianchi_torus_constrainedFEEC_sobolev, torus_nonvacuous⟩,
    ⟨einsteinBianchi_mirror_constrainedFEEC_sobolev, mirror_nonvacuous⟩,
    mirrorFEMVerdict, standardCubeVerdict⟩

end Feec.Instances.EinsteinBianchi
