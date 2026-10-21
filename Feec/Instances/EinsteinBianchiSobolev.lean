module

public import Feec.Instances.EinsteinBianchiSpectral
public import Feec.Models.Cube.MirrorWaveRegularity

/-!
# Sobolev data lie in the approximation classes of the spectral EB discretizations

**`𝕋³`.** For the Fourier spectral family `Feec.Instances.EinsteinBianchi.bandFamily` (bands
`|n|_∞ ≤ N`), the truncation error of a state in `Hˢ(𝕋³)` (`MemSobStateT s`, the weights
`⟨ξ_m⟩^{2s}` on the energy at each frequency) is `‖X - P_N X‖ ≤ (N + 1)^{-s} ‖X‖_s`
(`norm_sub_P_le_sobStateT`): the modes off the band have `|ξ| ≥ 2π (N + 1)`. On the TSD
constraint `L` multiplies the energy at `m` by `|ξ_m|²` (`fibreEnergy_wave_torus`), so a TSD
state in `H^{2+s}`, `s ≥ 0`, lies in `D(L²)` (`mem_wave_domain_of_summable_torus`) and in the
approximation class of order `s`, with norm at most `3 ‖X‖_{2+s}` (`mem_rateData_of_memSobStateT`).
The TSD state `decayState`, with `E = Σ_k (1 + k²)⁻² e^{2πi k x₃} diag(1, -1, 0)`, lies in `H³`,
is not band-limited for any `N` and is not stationary (`decayState_nonvacuous`): the torus rate
class of order `1` contains data on which the spectral method is not exact.

**The mirror cube `Q = (0, ½)³`.** For the cosine–sine family
`Feec.Instances.EinsteinBianchi.bandFamilyQ`, the truncation error of a state whose mirror extension
lies in `Hˢ(𝕋³)` is `‖x - P_N x‖ ≤ (N + 1)^{-s} ‖x‖_s` (`norm_sub_P_le_sobState`, from the torus
bound through the mirror extension), and a TSD datum in `H^{2+s}` lies in the class of order `s`
with norm at most `3 ‖ξ₀‖_{2+s}` (`mem_rateData_of_memSobState`, from
`TSDDatum.memSobState_of_add_two`).

**Through the approximating FEEC theorem.** The truncation bounds give rate classes of the
spectral approximating FEEC discretizations `torusApprox`, `mirrorApprox`
(`torusSobolevRate`, `mirrorSobolevRate`: `Hˢ` states, order `s`, `C = 1`, `C' = 0`), hence the
**time-uniform** Sobolev rates `‖e^{tL} ξ₀ - ι_N e^{tL_N} π_N ξ₀‖ ≤ (N + 1)^{-s} ‖ξ₀‖_s` for all
`t ≥ 0` and every `ξ₀ ∈ Hˢ`, with the same bound for the TSD residual of TSD data
(`einsteinBianchi_torus_approxFEEC_sobolev`, `einsteinBianchi_mirror_approxFEEC_sobolev`); no TSD
or `D(L)` condition, no factor `(1 + C_P)(1 + t)² · 3`. Non-vacuity: `decayState ∈ H³` is not
reproduced by the spectral solution at `t = 0` for any `N` (`torusApprox_sol_decayState_ne`). For
the constrained FEEC readings `torusFEEC`, `mirrorFEEC` (semi-discrete solutions from `Rₕ ξ₀`),
the conforming rate `(1 + C_P)(1 + 2t)(N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` for TSD data in `H^{2+s}`
replaces the `(1 + t)²` of the constrained FEEC verdicts
(`einsteinBianchi_torus_conforming_sobolev`, `einsteinBianchi_mirror_conforming_sobolev`).
The two readings concern the same trajectories: the elliptic projection onto a reducing band is
the truncation, so the semi-discrete solutions are `ξ_N(t) = P_N e^{tL} ξ₀`
(`SpectralFamily.graphFst_discrete`, `SpectralFamily.graphFst_discrete_eq_sol`), and the
time-uniform bound holds for the semi-discrete solutions of `torusFEEC`, `mirrorFEEC` themselves,
for `ξ₀ ∈ D(L) ∩ Hˢ` and all `t ∈ ℝ` (`einsteinBianchi_torus_discrete_sobolev`,
`einsteinBianchi_mirror_discrete_sobolev`; the error is positive for `decayState`,
`torus_discrete_decayState_error_pos`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.12–4.13, Ch. 6

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology LinearPMap
open Set Filter MeasureTheory

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi

open Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.BGG Feec.HilbertComplex
open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.Sobolev (weight weight_nonneg weight_mono weight_zero)
open Feec.ShortHilbertComplex (W3)

/-! ### Truncation errors on `𝕋³` -/

open Classical in
/-- The Fourier coefficients of the band truncation: `(P_N u)(m) = u(m)` on the band, `0` off. -/
theorem coe_starProjection_band (N : ℕ) (i : Fin 3) (u : Models.Torus.BGG.Space i)
    (m : Fin 3 → ℤ) :
    ((band N i).starProjection u : (Fin 3 → ℤ) → W3 ℂ Mat VM i) m =
      if m ∈ Fourier.Torus.bandN N then (u : (Fin 3 → ℤ) → W3 ℂ Mat VM i) m else 0 := by
  have h := Measure.ae_count_iff.1 (Operator.coeFn_starProjection_fibreSub (μ := Measure.count)
    (bandFibre (𝕜 := ℂ) (E := W3 ℂ Mat VM) (Fourier.Torus.bandN N) i)
    AEStronglyMeasurable.of_discrete u) m
  rw [h]
  dsimp only
  rw [starProjection_bandFibre]
  by_cases hm : m ∈ Fourier.Torus.bandN N
  · rw [ite_eq_left_iff.2 fun h => absurd hm h, Operator.cutoff_apply_of_mem hm]
  · rw [ite_eq_right_iff.2 fun h => absurd h hm, Operator.cutoff_apply_of_notMem hm]

open Classical in
/-- The energy of the truncation error at `m` is the energy of `X` off the band. -/
theorem fibreEnergy_sub_P (N : ℕ) (X : PiLp 2 Models.Torus.BGG.Space) (m : Fin 3 → ℤ) :
    fibreEnergy (X - bandFamily.P N X) m =
      if m ∈ Fourier.Torus.bandN N then 0 else fibreEnergy X m := by
  have e : ∀ i, ((X - bandFamily.P N X) i : (Fin 3 → ℤ) → W3 ℂ Mat VM i) m =
      if m ∈ Fourier.Torus.bandN N then 0 else (X i : (Fin 3 → ℤ) → W3 ℂ Mat VM i) m := by
    intro i
    rw [PiLp.sub_apply, Measure.ae_count_iff.1 (Lp.coeFn_sub _ _) m, Pi.sub_apply,
      SpectralFamily.P, totalSub_starProjection_apply]
    erw [coe_starProjection_band]
    split_ifs <;> simp
  unfold fibreEnergy
  simp only [e]
  split_ifs <;> simp

/-- Off the band `|n|_∞ ≤ N`: `(2π (N + 1))^{2s} ≤ ⟨ξ_m⟩^{2s}` for `s ≥ 0`. -/
theorem pow_le_weight {N : ℕ} {m : Fin 3 → ℤ} (hm : m ∉ Fourier.Torus.bandN N) {s : ℝ}
    (hs : 0 ≤ s) : ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ s ≤ weight s m := by
  obtain ⟨j, hj⟩ : ∃ j, ¬ |m j| ≤ N := by
    by_contra h
    push Not at h
    exact hm h
  have hj' : ((N : ℝ) + 1) ≤ |(m j : ℝ)| := by
    have : (N : ℤ) + 1 ≤ |m j| := by omega
    exact_mod_cast this
  have h1 : 2 * Real.pi * ((N : ℝ) + 1) ≤ ‖Fourier.Torus.freq m‖ := by
    have hc : |Fourier.Torus.freq m j| ≤ ‖Fourier.Torus.freq m‖ := by
      have := PiLp.norm_apply_le (Fourier.Torus.freq m) j
      rwa [Real.norm_eq_abs] at this
    rw [Fourier.Torus.freq_apply, abs_mul, abs_of_pos (by positivity)] at hc
    nlinarith [Real.pi_pos]
  have h2 : (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 ≤ 1 + ‖Fourier.Torus.freq m‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    linarith
  exact Real.rpow_le_rpow (sq_nonneg _) h2 hs

/-- `(2π (N + 1))^{-2s} ≤ (N + 1)^{-2s}` for `s ≥ 0`. -/
theorem inv_rpow_le_one_div_rpow_sq (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ s)⁻¹ ≤ ((1 / ((N : ℝ) + 1)) ^ s) ^ 2 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : ((N : ℝ) + 1) ^ 2 ≤ (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 := by
    have : (N : ℝ) + 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) := by nlinarith [Real.two_le_pi]
    exact pow_le_pow_left₀ hN.le this 2
  have h2 : (((N : ℝ) + 1) ^ 2) ^ s ≤ ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ s :=
    Real.rpow_le_rpow (by positivity) h1 hs
  have h3 : (((N : ℝ) + 1) ^ 2) ^ s = (((N : ℝ) + 1) ^ s) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_natCast (((N : ℝ) + 1) ^ s),
      ← Real.rpow_mul hN.le, mul_comm]
  have h4 : (1 / ((N : ℝ) + 1)) ^ s = (((N : ℝ) + 1) ^ s)⁻¹ := by
    rw [Real.div_rpow zero_le_one hN.le, Real.one_rpow, one_div]
  rw [h4, inv_pow]
  exact inv_anti₀ (by positivity) (h3 ▸ h2)

/-- **The Sobolev norm of a torus state**: `‖X‖²_s = Σ_m ⟨ξ_m⟩^{2s} Σᵢ |X̂ᵢ(m)|²`. -/
def sobStateT (s : ℝ) (X : PiLp 2 Models.Torus.BGG.Space) : ℝ :=
  ∑' m, weight s m * fibreEnergy X m

/-- `X ∈ Hˢ(𝕋³)`. -/
def MemSobStateT (s : ℝ) (X : PiLp 2 Models.Torus.BGG.Space) : Prop :=
  Summable fun m => weight s m * fibreEnergy X m

theorem sobStateT_nonneg (s : ℝ) (X : PiLp 2 Models.Torus.BGG.Space) : 0 ≤ sobStateT s X :=
  tsum_nonneg fun m => mul_nonneg (weight_nonneg s m) (fibreEnergy_nonneg _ m)

/-- **Truncation error of `Hˢ` states on `𝕋³`**: `‖X - P_N X‖ ≤ (N + 1)^{-s} ‖X‖_s`. -/
theorem norm_sub_P_le_sobStateT {s : ℝ} (hs : 0 ≤ s) {X : PiLp 2 Models.Torus.BGG.Space}
    (hX : MemSobStateT s X) (N : ℕ) :
    ‖X - bandFamily.P N X‖ ≤ (1 / ((N : ℝ) + 1)) ^ s * √(sobStateT s X) := by
  set c : ℝ := ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ s with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by positivity) s
  have hsq : ‖X - bandFamily.P N X‖ ^ 2 ≤ c⁻¹ * sobStateT s X := by
    rw [norm_sq_eq_tsum_fibreEnergy, sobStateT]
    have hle : ∀ m, fibreEnergy (X - bandFamily.P N X) m ≤
        c⁻¹ * (weight s m * fibreEnergy X m) := fun m => by
      rw [fibreEnergy_sub_P]
      split_ifs with hm
      · exact mul_nonneg (inv_nonneg.2 hcpos.le)
          (mul_nonneg (weight_nonneg s m) (fibreEnergy_nonneg _ m))
      · have h1 : 1 ≤ c⁻¹ * weight s m := by
          rw [inv_mul_eq_div, one_le_div hcpos]; exact pow_le_weight hm hs
        rw [← mul_assoc]
        exact le_mul_of_one_le_left (fibreEnergy_nonneg _ m) h1
    have hsum : Summable fun m => c⁻¹ * (weight s m * fibreEnergy X m) := hX.mul_left c⁻¹
    have h := Summable.tsum_le_tsum hle
      (Summable.of_nonneg_of_le (fun m => fibreEnergy_nonneg _ m) hle hsum) hsum
    rwa [tsum_mul_left] at h
  have hS := sobStateT_nonneg s X
  have key : ‖X - bandFamily.P N X‖ ^ 2 ≤ ((1 / ((N : ℝ) + 1)) ^ s * √(sobStateT s X)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hS]
    exact hsq.trans (mul_le_mul_of_nonneg_right (inv_rpow_le_one_div_rpow_sq N hs) hS)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key

/-! ### TSD states of `H^{2+s}(𝕋³)` -/

/-- A TSD torus state with `Σ_m |ξ_m|² Σᵢ |X̂ᵢ(m)|² < ∞` lies in `D(L)`. -/
theorem mem_wave_domain_of_summable_torus {X : PiLp 2 Models.Torus.BGG.Space}
    (hX : X ∈ totalSub Models.Torus.BGG.constraint)
    (h : Summable fun m => ‖Fourier.Torus.freq m‖ ^ 2 * fibreEnergy X m) :
    X ∈ Models.Torus.BGG.complex.wave.domain := by
  have hE : ∀ n, tc1 X n ∈ tsd (Fourier.Torus.freq n) := fun n =>
    Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 (hX 1)) n
  have hB := fun n => Models.Torus.BGG.mem_constraint_two_iff.1 (hX 2) n
  refine Models.Torus.BGG.mem_wave_domain_of (Models.Torus.BGG.mem_constraint_zero_iff.1 (hX 0))
    (hX 1) ?_ ?_
  · refine (Operator.mem_mulDomain_count_iff
      (fun n => bggFamily.m 1 2 (Fourier.Torus.freq n))).2 (memℓp_gen ?_)
    have hb : ∀ n, ‖bgg (Fourier.Torus.freq n) (tc1 X n)‖ ^ 2 ≤
        ‖Fourier.Torus.freq n‖ ^ 2 * fibreEnergy X n := fun n => by
      have haxial : Fourier.BGG.axialL (tc1 X n) = 0 :=
        (mem_tsdB.1 (Fourier.BGG.bgg_mem_tsdB (hE n))).1
      rw [norm_sq_VM]
      change ‖Fourier.BGG.axialL (tc1 X n)‖ ^ 2 +
        ‖curl (Fourier.Torus.freq n) (tc1 X n)‖ ^ 2 ≤ _
      rw [haxial, norm_zero, norm_curl_of_mem_tsd (hE n), fibreEnergy_eq]
      nlinarith [sq_nonneg ‖tc0 X n‖, sq_nonneg ‖tc2 X n‖,
        sq_nonneg ‖Fourier.Torus.freq n‖, mul_nonneg (sq_nonneg ‖Fourier.Torus.freq n‖)
          (sq_nonneg ‖tc0 X n‖), mul_nonneg (sq_nonneg ‖Fourier.Torus.freq n‖)
          (sq_nonneg ‖tc2 X n‖)]
    have hs : Summable fun n => ‖bgg (Fourier.Torus.freq n) (tc1 X n)‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb h
    refine hs.congr fun n => ?_
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
    rfl
  · rw [show (Models.Torus.BGG.complex.d 1 2)† = Operator.mulOp Measure.count fun n =>
        ContinuousLinearMap.adjoint (bggFamily.m 1 2 (Fourier.Torus.freq n)) from
      (Fourier.Torus.symbolComplex bggFamily).adjoint_d 1 2]
    refine (Operator.mem_mulDomain_count_iff _).2 (memℓp_gen ?_)
    have hb : ∀ n, ‖ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq n))
        (tc2 X n)‖ ^ 2 ≤ ‖Fourier.Torus.freq n‖ ^ 2 * fibreEnergy X n :=
      fun n => by
        have hw : tc2 X n = WithLp.toLp 2 ((0 : Vec), (WithLp.ofLp (tc2 X n)).2) := by
          rw [← (hB n).1]; rfl
        have hadj : ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq n)) (tc2 X n) =
            curl (Fourier.Torus.freq n) (WithLp.ofLp (tc2 X n)).2 := by
          conv_lhs => rw [hw]
          exact adjoint_bgg_inr _ _
        have h3 : ‖tc2 X n‖ ^ 2 = ‖(WithLp.ofLp (tc2 X n)).2‖ ^ 2 := by
          rw [norm_sq_VM, (hB n).1, norm_zero]; ring
        rw [hadj, norm_curl_of_mem_tsd (hB n).2, fibreEnergy_eq, mul_pow, ← h3]
        nlinarith [sq_nonneg ‖tc0 X n‖, sq_nonneg ‖tc1 X n‖,
          mul_nonneg (sq_nonneg ‖Fourier.Torus.freq n‖) (sq_nonneg ‖tc0 X n‖),
          mul_nonneg (sq_nonneg ‖Fourier.Torus.freq n‖) (sq_nonneg ‖tc1 X n‖)]
    have hs : Summable fun n => ‖ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq n))
        (tc2 X n)‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb h
    refine hs.congr fun n => ?_
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
    rfl

/-- `|ξ_m|^{2j} e_X(m)` is summable for `X ∈ H^{2+s}`, `s ≥ 0`, `j ≤ 2`. -/
theorem summable_freq_pow_of_memSobStateT {s : ℝ} (hs : 0 ≤ s) {j : ℕ} (hj : j ≤ 2)
    {X : PiLp 2 Models.Torus.BGG.Space} (h : MemSobStateT (2 + s) X) :
    Summable fun m => (‖Fourier.Torus.freq m‖ ^ 2) ^ j * fibreEnergy X m := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (sq_nonneg _) _) (fibreEnergy_nonneg _ m)) (fun m => ?_) h
  have h1 := weight_mul_freq_pow_le s hj m (fibreEnergy_nonneg X m)
  have h2 : 1 ≤ weight s m := by simpa using weight_mono hs m
  have h3 : 0 ≤ (‖Fourier.Torus.freq m‖ ^ 2) ^ j * fibreEnergy X m :=
    mul_nonneg (pow_nonneg (sq_nonneg _) _) (fibreEnergy_nonneg _ m)
  nlinarith

/-- If `e_X(m) = |ξ_m|^{2j} e_Y(m)` with `j ≤ 2` and `Y ∈ H^{2+s}`, then `X ∈ Hˢ` and
`‖X‖²_s ≤ ‖Y‖²_{2+s}`. -/
theorem sobStateT_le_of_fibreEnergy_eq {s : ℝ} {j : ℕ} (hj : j ≤ 2)
    {X Y : PiLp 2 Models.Torus.BGG.Space}
    (hXY : ∀ m, fibreEnergy X m = (‖Fourier.Torus.freq m‖ ^ 2) ^ j * fibreEnergy Y m)
    (hY : MemSobStateT (2 + s) Y) : MemSobStateT s X ∧ sobStateT s X ≤ sobStateT (2 + s) Y := by
  have hle : ∀ m, weight s m * fibreEnergy X m ≤ weight (2 + s) m * fibreEnergy Y m := fun m => by
    rw [hXY]; exact weight_mul_freq_pow_le s hj m (fibreEnergy_nonneg _ m)
  have h0 : ∀ m, 0 ≤ weight s m * fibreEnergy X m := fun m =>
    mul_nonneg (weight_nonneg s m) (fibreEnergy_nonneg _ m)
  have hX : MemSobStateT s X := Summable.of_nonneg_of_le h0 hle hY
  exact ⟨hX, Summable.tsum_le_tsum hle hX hY⟩

/-- **TSD data in `H^{2+s}(𝕋³)` lie in the approximation class of order `s`** of the Fourier
spectral discretization, with class norm at most `3 ‖X‖_{2+s}` (in particular `X ∈ D(L²)`). -/
theorem mem_rateData_of_memSobStateT {X : PiLp 2 Models.Torus.BGG.Space}
    (hK : X ∈ totalSub Models.Torus.BGG.constraint) {s : ℝ} (hs : 0 ≤ s)
    (h : MemSobStateT (2 + s) X) :
    X ∈ bandFamily.rateData s ∧ bandFamily.rateNorm s X ≤ 3 * √(sobStateT (2 + s) X) := by
  have hD : X ∈ Models.Torus.BGG.complex.wave.domain :=
    mem_wave_domain_of_summable_torus hK
      ((summable_freq_pow_of_memSobStateT hs (j := 1) (by norm_num) h).congr fun m => by
        rw [pow_one])
  have hYK : Models.Torus.BGG.complex.wave ⟨X, hD⟩ ∈ totalSub Models.Torus.BGG.constraint :=
    Models.Torus.BGG.reducingSubcomplex.isReducing_wave.mapsTo ⟨X, hD⟩ hK
  have eY := fibreEnergy_wave_torus ⟨X, hD⟩ hK
  have hYD : Models.Torus.BGG.complex.wave ⟨X, hD⟩ ∈ Models.Torus.BGG.complex.wave.domain :=
    mem_wave_domain_of_summable_torus hYK
      ((summable_freq_pow_of_memSobStateT hs le_rfl h).congr fun m => by rw [eY]; ring)
  have eZ : ∀ m, fibreEnergy (Models.Torus.BGG.complex.wave ⟨_, hYD⟩) m =
      (‖Fourier.Torus.freq m‖ ^ 2) ^ 2 * fibreEnergy X m := fun m => by
    rw [fibreEnergy_wave_torus ⟨_, hYD⟩ hYK, eY]; ring
  obtain ⟨h0, b0⟩ := sobStateT_le_of_fibreEnergy_eq (j := 0) (X := X) (by norm_num)
    (fun m => by rw [pow_zero, one_mul]) h
  obtain ⟨h1, b1⟩ := sobStateT_le_of_fibreEnergy_eq (j := 1) (by norm_num)
    (fun m => by rw [pow_one]; exact eY m) h
  obtain ⟨h2, b2⟩ := sobStateT_le_of_fibreEnergy_eq (j := 2) le_rfl eZ h
  have e1 : Models.Torus.BGG.complex.waveExt X = Models.Torus.BGG.complex.wave ⟨X, hD⟩ :=
    waveExt_of_mem hD
  have e2 : Models.Torus.BGG.complex.waveExt (Models.Torus.BGG.complex.wave ⟨X, hD⟩) =
      Models.Torus.BGG.complex.wave ⟨_, hYD⟩ := waveExt_of_mem hYD
  refine bandFamily.mem_rateData_of_tail_le hD (e1 ▸ hYD) fun N => ?_
  rw [SpectralFamily.tail, e1, e2]
  have a0 := norm_sub_P_le_sobStateT hs h0 N
  have a1 := norm_sub_P_le_sobStateT hs h1 N
  have a2 := norm_sub_P_le_sobStateT hs h2 N
  have c0 := Real.sqrt_le_sqrt b0
  have c1 := Real.sqrt_le_sqrt b1
  have c2 := Real.sqrt_le_sqrt b2
  have hp : 0 ≤ (1 / ((N : ℝ) + 1)) ^ s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left c0 hp, mul_le_mul_of_nonneg_left c1 hp,
    mul_le_mul_of_nonneg_left c2 hp]

/-! ### A TSD state on `𝕋³` that is not band-limited -/

/-- The frequencies `(0, 0, k)`. -/
def lineFreq (k : ℤ) : Fin 3 → ℤ := ![0, 0, k]

theorem lineFreq_injective : Function.Injective lineFreq := fun a b h => by
  simpa [lineFreq] using congrFun h 2

theorem eq_lineFreq {n : Fin 3 → ℤ} (h : n 0 = 0 ∧ n 1 = 0) : n = lineFreq (n 2) := by
  funext j
  fin_cases j <;> simp [lineFreq, h.1, h.2]

theorem norm_freq_lineFreq_sq (k : ℤ) :
    ‖Fourier.Torus.freq (lineFreq k)‖ ^ 2 = (2 * Real.pi * k) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [lineFreq, Fourier.Torus.freq_apply, mul_pow, sq_abs]

/-- The amplitudes `(1 + k²)⁻²`. -/
def decayAmp (k : ℤ) : ℝ := ((1 + (k : ℝ) ^ 2) ^ 2)⁻¹

theorem decayAmp_pos (k : ℤ) : 0 < decayAmp k := by unfold decayAmp; positivity

theorem summable_inv_one_add_sq : Summable fun k : ℤ => (1 + (k : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (g := fun k : ℤ => 1 / (k : ℝ) ^ 2)
    (Real.summable_one_div_int_pow.2 (by norm_num)) ?_
  filter_upwards [eventually_cofinite_ne 0] with k hk
  have hk' : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
  exact inv_anti₀ hk' (by linarith)

open Classical in
/-- The coefficients `(0, 0, k) ↦ (1 + k²)⁻² diag(1, -1, 0)`, `0` off the line. -/
def decayCoeff (n : Fin 3 → ℤ) : Mat :=
  if n 0 = 0 ∧ n 1 = 0 then ((decayAmp (n 2) : ℝ) : ℂ) • Models.Cube.Mirror.M0 else 0

theorem decayCoeff_lineFreq (k : ℤ) :
    decayCoeff (lineFreq k) = ((decayAmp k : ℝ) : ℂ) • Models.Cube.Mirror.M0 := by
  simp [decayCoeff, lineFreq]

theorem decayCoeff_eq_zero {n : Fin 3 → ℤ} (hn : n ∉ range lineFreq) : decayCoeff n = 0 := by
  unfold decayCoeff
  split_ifs with h
  · exact absurd ⟨n 2, (eq_lineFreq h).symm⟩ hn
  · rfl

theorem norm_decayCoeff_lineFreq (k : ℤ) :
    ‖decayCoeff (lineFreq k)‖ = decayAmp k * ‖Models.Cube.Mirror.M0‖ := by
  rw [decayCoeff_lineFreq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (decayAmp_pos k)]

/-- Summability of a sequence supported on the line `(0, 0, k)` from its restriction. -/
theorem summable_of_line {f : (Fin 3 → ℤ) → ℝ} (hf : ∀ n ∉ range lineFreq, f n = 0)
    (h : Summable fun k => f (lineFreq k)) : Summable f :=
  (lineFreq_injective.summable_iff hf).1 h

theorem decayAmp_sq_le (k : ℤ) : decayAmp k ^ 2 ≤ (1 + (k : ℝ) ^ 2)⁻¹ := by
  have h1 : (1 : ℝ) ≤ 1 + (k : ℝ) ^ 2 := by nlinarith [sq_nonneg (k : ℝ)]
  unfold decayAmp
  rw [inv_pow, ← pow_mul]
  exact inv_anti₀ (by positivity) (le_self_pow₀ h1 (by norm_num))

theorem memLp_decayCoeff : MemLp decayCoeff 2 (Measure.count : Measure (Fin 3 → ℤ)) := by
  refine memLp_count_of_summable (summable_of_line (fun n hn => by
    rw [decayCoeff_eq_zero hn, norm_zero]; norm_num) ?_)
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_)
    (summable_inv_one_add_sq.mul_left (‖Models.Cube.Mirror.M0‖ ^ 2))
  rw [norm_decayCoeff_lineFreq, mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_left (decayAmp_sq_le k) (sq_nonneg _)

/-- **The electric field** `E = Σ_k (1 + k²)⁻² e^{2πi k x₃} diag(1, -1, 0)` (Fourier side). -/
def decayE : Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ)) := memLp_decayCoeff.toLp decayCoeff

theorem coe_decayE (n : Fin 3 → ℤ) : (decayE : (Fin 3 → ℤ) → Mat) n = decayCoeff n :=
  Measure.ae_count_iff.1 memLp_decayCoeff.coeFn_toLp n

/-- **The state** `(0, E, (0, 0))`. -/
def decayState : PiLp 2 Models.Torus.BGG.Space := WithLp.toLp 2 (Pi.single 1 decayE)

theorem decayState_zero : decayState 0 = 0 :=
  Pi.single_eq_of_ne (M := Models.Torus.BGG.Space) (by decide : (0 : Fin 3) ≠ 1) decayE

theorem decayState_one : decayState 1 = decayE :=
  Pi.single_eq_same (M := Models.Torus.BGG.Space) (1 : Fin 3) decayE

theorem decayState_two : decayState 2 = 0 :=
  Pi.single_eq_of_ne (M := Models.Torus.BGG.Space) (by decide : (2 : Fin 3) ≠ 1) decayE

theorem M0_mem_tsd_of {n : Fin 3 → ℤ} (h0 : n 0 = 0 ∧ n 1 = 0) :
    Models.Cube.Mirror.M0 ∈ tsd (Fourier.Torus.freq n) := by
  refine mem_tsd.2 ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, toMatrix_apply, Models.Cube.Mirror.M0_apply]
    split_ifs <;> simp_all
  · simp [Matrix.trace, toMatrix_apply, Models.Cube.Mirror.M0_apply, Fin.sum_univ_three]
  · ext a
    simp only [Matrix.mulVec, dotProduct, toMatrix_apply, Models.Cube.Mirror.M0_apply, cfreq,
      Fin.sum_univ_three, Pi.zero_apply]
    fin_cases a <;> simp [Fourier.Torus.freq_apply, h0.1, h0.2]

theorem decayE_mem_constraint : decayE ∈ Models.Torus.BGG.constraint 1 := by
  refine Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun n => ?_)
  change (decayE : (Fin 3 → ℤ) → Mat) n ∈ tsd (Fourier.Torus.freq n)
  rw [coe_decayE]
  unfold decayCoeff
  split_ifs with h
  · exact Submodule.smul_mem _ _ (M0_mem_tsd_of h)
  · exact Submodule.zero_mem _

/-- `decayState` is TSD. -/
theorem decayState_mem_constraint : decayState ∈ totalSub Models.Torus.BGG.constraint := by
  intro i
  fin_cases i
  · change decayState 0 ∈ _; rw [decayState_zero]; exact Submodule.zero_mem _
  · change decayState 1 ∈ _; rw [decayState_one]; exact decayE_mem_constraint
  · change decayState 2 ∈ _; rw [decayState_two]; exact Submodule.zero_mem _

theorem fibreEnergy_decayState (n : Fin 3 → ℤ) :
    fibreEnergy decayState n = ‖decayCoeff n‖ ^ 2 := by
  have c0 : tc0 decayState n = 0 := by
    change ((decayState 0 : Models.Torus.BGG.Space 0) : (Fin 3 → ℤ) → _) n = 0
    rw [decayState_zero]
    exact Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) n
  have c1 : tc1 decayState n = decayCoeff n := by
    change ((decayState 1 : Models.Torus.BGG.Space 1) : (Fin 3 → ℤ) → _) n = _
    rw [decayState_one]
    exact coe_decayE n
  have c2 : tc2 decayState n = 0 := by
    change ((decayState 2 : Models.Torus.BGG.Space 2) : (Fin 3 → ℤ) → _) n = 0
    rw [decayState_two]
    exact Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) n
  rw [fibreEnergy_eq, c0, c1, c2, norm_zero, norm_zero]
  ring

/-- **`decayState ∈ H³(𝕋³)`**: `⟨2πk⟩⁶ (1 + k²)⁻⁴ ≤ (4π²)³ (1 + k²)⁻¹`. -/
theorem decayState_memSobStateT : MemSobStateT (2 + 1) decayState := by
  refine summable_of_line (fun n hn => by
    rw [fibreEnergy_decayState, decayCoeff_eq_zero hn, norm_zero]; ring) ?_
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (weight_nonneg _ _) (fibreEnergy_nonneg _ _)) (fun k => ?_)
    (summable_inv_one_add_sq.mul_left ((4 * Real.pi ^ 2) ^ 3 * ‖Models.Cube.Mirror.M0‖ ^ 2))
  have hw : weight (2 + 1) (lineFreq k) = (1 + (2 * Real.pi * k) ^ 2) ^ 3 := by
    rw [show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, weight_natCast, norm_freq_lineFreq_sq]
  rw [hw, fibreEnergy_decayState, norm_decayCoeff_lineFreq]
  set a : ℝ := 1 + (k : ℝ) ^ 2 with ha
  have ha1 : 1 ≤ a := by nlinarith [sq_nonneg (k : ℝ)]
  have ha0 : 0 < a := by linarith
  have hpi : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hb : 1 + (2 * Real.pi * k) ^ 2 ≤ 4 * Real.pi ^ 2 * a := by
    rw [ha]; nlinarith [sq_nonneg (k : ℝ)]
  have hb3 : (1 + (2 * Real.pi * k) ^ 2) ^ 3 ≤ (4 * Real.pi ^ 2) ^ 3 * a ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hb 3
  have hd : (decayAmp k * ‖Models.Cube.Mirror.M0‖) ^ 2 =
      ‖Models.Cube.Mirror.M0‖ ^ 2 * (a ^ 4)⁻¹ := by
    change (((1 + (k : ℝ) ^ 2) ^ 2)⁻¹ * ‖Models.Cube.Mirror.M0‖) ^ 2 = _
    rw [← ha, mul_pow, inv_pow, ← pow_mul, mul_comm]
  have key : a ^ 3 * (a ^ 4)⁻¹ = a⁻¹ := by
    rw [show a ^ 4 = a ^ 3 * a by ring, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
  rw [hd]
  calc (1 + (2 * Real.pi * k) ^ 2) ^ 3 * (‖Models.Cube.Mirror.M0‖ ^ 2 * (a ^ 4)⁻¹)
      ≤ (4 * Real.pi ^ 2) ^ 3 * a ^ 3 * (‖Models.Cube.Mirror.M0‖ ^ 2 * (a ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_right hb3 (by positivity)
    _ = (4 * Real.pi ^ 2) ^ 3 * ‖Models.Cube.Mirror.M0‖ ^ 2 * (a ^ 3 * (a ^ 4)⁻¹) := by
        ring
    _ = _ := by rw [key]

theorem M0_ne_zero : Models.Cube.Mirror.M0 ≠ 0 := by
  intro h
  have := congrArg (fun M : Mat => M (0, 0)) h
  simp [Models.Cube.Mirror.M0_apply] at this

theorem decayCoeff_lineFreq_ne_zero (k : ℤ) : decayCoeff (lineFreq k) ≠ 0 := by
  rw [decayCoeff_lineFreq]
  exact smul_ne_zero (by exact_mod_cast (decayAmp_pos k).ne') M0_ne_zero

/-- **`decayState` is not band-limited**: it has the mode `(0, 0, N + 1)` off every band. -/
theorem decayState_not_mem_band (N : ℕ) : decayState ∉ totalSub (band N) := by
  intro h
  have h1 := h 1
  rw [Fourier.mem_band_iff, Measure.ae_count_iff] at h1
  have hn : lineFreq ((N : ℤ) + 1) ∉ Fourier.Torus.bandN N := fun hb => by
    have h2 : |(N : ℤ) + 1| ≤ N := by simpa [lineFreq] using hb 2
    rw [abs_of_nonneg (by positivity)] at h2
    omega
  apply decayCoeff_lineFreq_ne_zero ((N : ℤ) + 1)
  rw [← coe_decayE, ← decayState_one]
  exact h1 _ hn

/-- **Non-vacuity of the torus Sobolev rate**: `decayState` is TSD, lies in `H³` (so in the
approximation class of order `1`, `mem_rateData_of_memSobStateT`), is not band-limited for any
`N`, and is not stationary (`L X ≠ 0`). -/
theorem decayState_nonvacuous :
    decayState ∈ totalSub Models.Torus.BGG.constraint ∧ MemSobStateT (2 + 1) decayState ∧
      (∀ N, decayState ∉ totalSub (band N)) ∧
      ∃ hD : decayState ∈ Models.Torus.BGG.complex.wave.domain,
        Models.Torus.BGG.complex.wave ⟨decayState, hD⟩ ≠ 0 := by
  have hD := (mem_rateData_of_memSobStateT decayState_mem_constraint zero_le_one
    decayState_memSobStateT).1.1
  refine ⟨decayState_mem_constraint, decayState_memSobStateT, decayState_not_mem_band, hD,
    fun h0 => ?_⟩
  have e := fibreEnergy_wave_torus ⟨decayState, hD⟩ decayState_mem_constraint (lineFreq 1)
  have hle := (summable_fibreEnergy (Models.Torus.BGG.complex.wave ⟨decayState, hD⟩)).le_tsum
    (lineFreq 1) fun m _ => fibreEnergy_nonneg _ m
  have e' : fibreEnergy (Models.Torus.BGG.complex.wave ⟨decayState, hD⟩) (lineFreq 1) =
      (2 * Real.pi * ((1 : ℤ) : ℝ)) ^ 2 * ‖decayCoeff (lineFreq 1)‖ ^ 2 := by
    rw [e, ← norm_freq_lineFreq_sq]
    exact congrArg _ (fibreEnergy_decayState _)
  rw [← norm_sq_eq_tsum_fibreEnergy, e', h0, norm_zero] at hle
  have hc := norm_pos_iff.2 (decayCoeff_lineFreq_ne_zero 1)
  have : 0 < (2 * Real.pi * ((1 : ℤ) : ℝ)) ^ 2 * ‖decayCoeff (lineFreq 1)‖ ^ 2 := by
    have := Real.pi_pos
    positivity
  linarith

/-! ### The mirror cube -/

/-- **Truncation error of `Hˢ` states on `Q`**: `‖x - P_N x‖ ≤ (N + 1)^{-s} ‖x‖_s` (the torus
bound `norm_sub_P_le_sobStateT` for the mirror extension, `‖J y‖² = 8 ‖y‖²`). -/
theorem norm_sub_P_le_sobState {s : ℝ} (hs : 0 ≤ s) {x : PiLp 2 Models.Cube.MirrorBGG.SpaceQ}
    (hx : MemSobState s x) (N : ℕ) :
    ‖x - bandFamilyQ.P N x‖ ≤ (1 / ((N : ℝ) + 1)) ^ s * √(sobState s x) := by
  -- the extension of the truncation is the truncation of the extension
  have hJ : extState (x - bandFamilyQ.P N x) = extState x - bandFamily.P N (extState x) := by
    refine PiLp.ext fun i => ?_
    rw [totalJ_apply, PiLp.sub_apply, _root_.map_sub, PiLp.sub_apply, totalJ_apply,
      SpectralFamily.P, SpectralFamily.P, totalSub_starProjection_apply,
      totalSub_starProjection_apply]
    congr 1
    exact Models.Cube.MirrorBGG.embeddingQ.starProjection_comap _
      (exists_J_eq_starProjection_band N i) (x i)
  have hT := norm_sub_P_le_sobStateT hs (X := extState x) hx N
  have hS := sobStateT_nonneg s (extState x)
  have e : sobState s x = 8⁻¹ * sobStateT s (extState x) := rfl
  have h8 := norm_extState_sq (x - bandFamilyQ.P N x)
  rw [hJ] at h8
  have hT2 := pow_le_pow_left₀ (norm_nonneg _) hT 2
  rw [mul_pow, Real.sq_sqrt hS] at hT2
  have key : ‖x - bandFamilyQ.P N x‖ ^ 2 ≤ ((1 / ((N : ℝ) + 1)) ^ s * √(sobState s x)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (sobState_nonneg s x), e]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key

/-- **TSD data in `H^{2+s}` lie in the approximation class of order `s`** of the mirror spectral
discretization, with class norm at most `3 ‖ξ₀‖_{2+s}`. -/
theorem mem_rateData_of_memSobState (D : TSDDatum) {s : ℝ} (hs : 0 ≤ s)
    (h : MemSobState (2 + s) D.U₀) :
    D.U₀ ∈ bandFamilyQ.rateData s ∧
      bandFamilyQ.rateNorm s D.U₀ ≤ 3 * √(sobState (2 + s) D.U₀) := by
  obtain ⟨h0, h1, h2, hb⟩ := D.memSobState_of_add_two h
  have e1 : Models.Cube.MirrorBGG.complexQ.waveExt D.U₀ = D.LU₀ := waveExt_of_mem D.mem
  have e2 : Models.Cube.MirrorBGG.complexQ.waveExt D.LU₀ = D.LLU₀ := waveExt_of_mem D.mem₂
  refine (bandFamilyQ.mem_rateData_of_tail_le D.mem (e1 ▸ D.mem₂) fun N => ?_).imp_right
    fun h => h.trans hb
  rw [SpectralFamily.tail, e1, e2]
  have a0 := norm_sub_P_le_sobState hs h0 N
  have a1 := norm_sub_P_le_sobState hs h1 N
  have a2 := norm_sub_P_le_sobState hs h2 N
  unfold TSDDatum.sobSize
  linarith

/-- States with finitely many modes lie in every `Hʳ`. -/
theorem memSobState_of_finite {x : PiLp 2 Models.Cube.MirrorBGG.SpaceQ} (S : Finset (Fin 3 → ℤ))
    (hx : ∀ m ∉ S, fibreEnergy (extState x) m = 0) (r : ℝ) : MemSobState r x :=
  summable_of_ne_finset_zero fun m hm => by rw [hx m hm, mul_zero]

/-- **The cos datum lies in every `Hʳ`**: its mirror extension has the modes `±k₀` only. -/
theorem cosDatum_memSobState (r : ℝ) : MemSobState r cosDatum.U₀ := by
  refine memSobState_of_finite {Models.Cube.Mirror.k0, -Models.Cube.Mirror.k0} (fun m hm => ?_) r
  change fibreEnergy (totalJ Models.Cube.MirrorBGG.J Models.Cube.MirrorBGG.cosStateQ) m = 0
  rw [Models.Cube.MirrorBGG.totalJ_cosStateQ]
  unfold fibreEnergy
  exact Finset.sum_eq_zero fun i _ => by rw [cosState_finite i m hm, norm_zero]; norm_num

/-! ### Sobolev rates through the approximating FEEC theorem -/

section Approx

open Metric

open Models.Torus.BGG (complex constraint Space)
open Models.Cube.MirrorBGG (complexQ tsdQ SpaceQ)

/-- **`Hˢ` states on `𝕋³` as a rate class of the approximating FEEC discretization
`torusApprox`** (no TSD or domain condition): `h_N = 1/(N + 1)`, order `s`, `C = 1`, `C' = 0`,
class norm `‖X‖_s` (`norm_sub_P_le_sobStateT`). -/
def torusSobolevRate {s : ℝ} (hs : 0 ≤ s) (T : ℝ) : torusApprox.RateClass T :=
  torusBands.rateClass _ _ T {X | MemSobStateT s X} (fun X => √(sobStateT s X))
    (fun N => 1 / ((N : ℝ) + 1)) s 1 fun _ hX N => by
      rw [one_mul]; exact norm_sub_P_le_sobStateT hs hX N

/-- **The time-uniform Sobolev rate on `𝕋³`**: for every state `X ∈ Hˢ(𝕋³)`, `s ≥ 0`, the error of
the Fourier spectral solution from `π_N X` is `≤ (N + 1)^{-s} ‖X‖_s` for all `t ≥ 0`, and so is
its TSD residual when `X` is TSD. For `X ∈ D(L)` this orbit is the semi-discrete solution of
`torusFEEC` from `Rₙ X` (`SpectralFamily.graphFst_discrete_eq_sol`); `TorusSobolevDiscreteRate`
states the bound for those solutions. -/
abbrev TorusSobolevApproxRate : Prop :=
  ∀ {s : ℝ}, 0 ≤ s → ∀ X : PiLp 2 Space, MemSobStateT s X → ∀ (N : ℕ) {t : ℝ}, 0 ≤ t →
    ‖complex.waveGroup.S t X - torusApprox.sol N ((torusBands.B N).orthogonalProjectionOnto X) t‖ ≤
        (1 / ((N : ℝ) + 1)) ^ s * √(sobStateT s X) ∧
      (X ∈ totalSub constraint →
        infDist (torusApprox.sol N ((torusBands.B N).orthogonalProjectionOnto X) t)
            (totalSub constraint : Set (PiLp 2 Space)) ≤
          (1 / ((N : ℝ) + 1)) ^ s * √(sobStateT s X))

/-- `TorusSobolevApproxRate`, from the rate and the residual bound of `approxFEEC`
(`norm_sub_sol_le_of_truncation`, `infDist_sol_le_of_truncation`). -/
theorem einsteinBianchi_torus_approxFEEC_sobolev : TorusSobolevApproxRate := by
  intro s hs X hX N t ht
  have hrate : ∀ Y ∈ {Y | MemSobStateT s Y}, ∀ M : ℕ,
      ‖Y - (torusBands.B M).starProjection Y‖ ≤
        1 * (1 / ((M : ℝ) + 1)) ^ s * √(sobStateT s Y) := fun _ hY M => by
    rw [one_mul]; exact norm_sub_P_le_sobStateT hs hY M
  have h1 := norm_sub_sol_le_of_truncation torusBands (totalSub constraint) isClosed_totalSub
    hrate hX N ht
  rw [one_mul] at h1
  refine ⟨h1, fun hXK => ?_⟩
  have h2 := infDist_sol_le_of_truncation torusBands (totalSub constraint) isClosed_totalSub
    torusApprox_isReducing
    hrate hX hXK N ht
  rwa [one_mul] at h2

/-- **Non-vacuity of the time-uniform torus rate**: the TSD state `decayState ∈ H³` is not
reproduced by the spectral solution at `t = 0` for any `N` (it is not band-limited), so the error
bound of `einsteinBianchi_torus_approxFEEC_sobolev` at `s = 3` concerns a nonzero error. -/
theorem torusApprox_sol_decayState_ne (N : ℕ) :
    torusApprox.sol N ((torusBands.B N).orthogonalProjectionOnto decayState) 0 ≠ decayState := by
  intro h
  have e := ApproxFEEC.sol_zero torusApprox N
    ((torusBands.B N).orthogonalProjectionOnto decayState)
  exact decayState_not_mem_band N
    ((Submodule.starProjection_eq_self_iff (K := totalSub (band N))).1 (e.symm.trans h))

/-- **`Hˢ` states on the mirror cube as a rate class of `mirrorApprox`**: `h_N = 1/(N + 1)`, order
`s`, `C = 1`, `C' = 0`, class norm `‖x‖_s` (`norm_sub_P_le_sobState`). -/
def mirrorSobolevRate {s : ℝ} (hs : 0 ≤ s) (T : ℝ) : mirrorApprox.RateClass T :=
  mirrorBands.rateClass _ _ T {x | MemSobState s x} (fun x => √(sobState s x))
    (fun N => 1 / ((N : ℝ) + 1)) s 1 fun _ hx N => by
      rw [one_mul]; exact norm_sub_P_le_sobState hs hx N

/-- **The time-uniform Sobolev rate on the mirror cube**: for every state `x` with mirror
extension in `Hˢ`, `s ≥ 0`, the error of the cosine–sine spectral solution from `π_N x` is
`≤ (N + 1)^{-s} ‖x‖_s` for all `t ≥ 0`, and so is its TSD residual when `x` is TSD. -/
abbrev MirrorSobolevApproxRate : Prop :=
  ∀ {s : ℝ}, 0 ≤ s → ∀ x : PiLp 2 SpaceQ, MemSobState s x → ∀ (N : ℕ) {t : ℝ}, 0 ≤ t →
    ‖complexQ.waveGroup.S t x -
        mirrorApprox.sol N ((mirrorBands.B N).orthogonalProjectionOnto x) t‖ ≤
        (1 / ((N : ℝ) + 1)) ^ s * √(sobState s x) ∧
      (x ∈ totalSub tsdQ →
        infDist (mirrorApprox.sol N ((mirrorBands.B N).orthogonalProjectionOnto x) t)
            (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
          (1 / ((N : ℝ) + 1)) ^ s * √(sobState s x))

theorem einsteinBianchi_mirror_approxFEEC_sobolev : MirrorSobolevApproxRate := by
  intro s hs x hx N t ht
  have hrate : ∀ y ∈ {y | MemSobState s y}, ∀ M : ℕ,
      ‖y - (mirrorBands.B M).starProjection y‖ ≤
        1 * (1 / ((M : ℝ) + 1)) ^ s * √(sobState s y) := fun _ hy M => by
    rw [one_mul]; exact norm_sub_P_le_sobState hs hy M
  have h1 := norm_sub_sol_le_of_truncation mirrorBands (totalSub tsdQ) isClosed_totalSub
    hrate hx N ht
  rw [one_mul] at h1
  refine ⟨h1, fun hxK => ?_⟩
  have h2 := infDist_sol_le_of_truncation mirrorBands (totalSub tsdQ) isClosed_totalSub
    mirrorApprox_isReducing
    hrate hx hxK N ht
  rwa [one_mul] at h2

/-- **The conforming Sobolev rate on `𝕋³`**: for a TSD datum in `H^{2+s}`, `s ≥ 0`, the error and
the TSD residual of the semi-discrete solutions of `torusFEEC` are
`≤ (1 + C_P)(1 + 2t)(N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}` (`TorusSobolevVerdict` with `(1 + t)²` replaced
by `1 + 2t`). -/
abbrev TorusSobolevConformingRate : Prop :=
  ∀ (x : PiLp 2 Space), x ∈ totalSub constraint → ∀ {s : ℝ}, 0 ≤ s → MemSobStateT (2 + s) x →
    x ∈ complex.wave.domain ∧ ∀ (hx : x ∈ complex.wave.domain) (N : ℕ) {T t : ℝ}, t ∈ Icc 0 T →
      ‖complex.waveGroup.S t x - complex.totalD.graphFst
          ((bandFamily.toFEEC (totalSub constraint) isClosed_totalSub).discrete N
            (waveLift complex ⟨x, hx⟩) t)‖ ≤
        (1 + ellipticConst complex) * (1 + 2 * t) *
          ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x))) ∧
      infDist (complex.totalD.graphFst
          ((bandFamily.toFEEC (totalSub constraint) isClosed_totalSub).discrete N
            (waveLift complex ⟨x, hx⟩) t)) (totalSub constraint : Set (PiLp 2 Space)) ≤
        (1 + ellipticConst complex) * (1 + 2 * t) *
          ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)))

theorem einsteinBianchi_torus_conforming_sobolev : TorusSobolevConformingRate := by
  intro x hK s hs h
  obtain ⟨hD, hn⟩ := mem_rateData_of_memSobStateT hK hs h
  refine ⟨hD.1, fun hx N T t ht => ?_⟩
  have hrate := einsteinBianchi_torus_conforming_rate s T x hD N t ht
  have hC : 0 ≤ (1 + ellipticConst complex) * (1 + 2 * t) := by
    have := ellipticConst_nonneg complex
    have : 0 ≤ t := ht.1
    positivity
  have hle : 1 * (1 / ((N : ℝ) + 1)) ^ s * bandFamily.rateNorm s x ≤
      (1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobStateT (2 + s) x)) := by
    rw [one_mul]; exact mul_le_mul_of_nonneg_left hn (by positivity)
  exact ⟨hrate.1.trans (mul_le_mul_of_nonneg_left hle hC),
    (hrate.2 hK).trans (mul_le_mul_of_nonneg_left hle hC)⟩

/-- **The conforming Sobolev rate on the mirror cube**: for a TSD datum with mirror extension in
`H^{2+s}`, `s ≥ 0`, the error and the TSD residual of the semi-discrete solutions of `mirrorFEEC`
are `≤ (1 + C_P)(1 + 2t)(N + 1)^{-s} · 3 ‖ξ₀‖_{2+s}`. -/
abbrev MirrorSobolevConformingRate : Prop :=
  ∀ (D : TSDDatum) {s : ℝ}, 0 ≤ s → MemSobState (2 + s) D.U₀ → ∀ (N : ℕ) {T t : ℝ},
    t ∈ Icc 0 T →
    ‖complexQ.waveGroup.S t D.U₀ - complexQ.totalD.graphFst
        ((bandFamilyQ.toFEEC (totalSub tsdQ) isClosed_totalSub).discrete N
          (waveLift complexQ ⟨D.U₀, D.mem⟩) t)‖ ≤
      (1 + ellipticConst complexQ) * (1 + 2 * t) *
        ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobState (2 + s) D.U₀))) ∧
    infDist (complexQ.totalD.graphFst
        ((bandFamilyQ.toFEEC (totalSub tsdQ) isClosed_totalSub).discrete N
          (waveLift complexQ ⟨D.U₀, D.mem⟩) t)) (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
      (1 + ellipticConst complexQ) * (1 + 2 * t) *
        ((1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobState (2 + s) D.U₀)))

theorem einsteinBianchi_mirror_conforming_sobolev : MirrorSobolevConformingRate := by
  intro D s hs h N T t ht
  obtain ⟨hD, hn⟩ := mem_rateData_of_memSobState D hs h
  have hrate := einsteinBianchi_mirror_conforming_rate s T D.U₀ hD N t ht
  have hC : 0 ≤ (1 + ellipticConst complexQ) * (1 + 2 * t) := by
    have := ellipticConst_nonneg complexQ
    have : 0 ≤ t := ht.1
    positivity
  have hle : 1 * (1 / ((N : ℝ) + 1)) ^ s * bandFamilyQ.rateNorm s D.U₀ ≤
      (1 / ((N : ℝ) + 1)) ^ s * (3 * √(sobState (2 + s) D.U₀)) := by
    rw [one_mul]; exact mul_le_mul_of_nonneg_left hn (by positivity)
  exact ⟨hrate.1.trans (mul_le_mul_of_nonneg_left hle hC),
    (hrate.2 D.tsd).trans (mul_le_mul_of_nonneg_left hle hC)⟩

/-- **The time-uniform Sobolev rate of the spectral semi-discrete solutions on `𝕋³`**: for every
`X ∈ D(L) ∩ Hˢ(𝕋³)`, `s ≥ 0`, the semi-discrete solutions `ξ_N` of `torusFEEC` (spelled
`bandFamily.toFEEC (totalSub constraint) isClosed_totalSub`) from `Rₙ X` satisfy
`‖e^{tL} X - ξ_N(t)‖ ≤ (N + 1)^{-s} ‖X‖_s` for all `t ∈ ℝ`, and so does their TSD residual when
`X` is TSD. Compared with `TorusSobolevVerdict` (TSD data in `H^{2+s}`, factor
`(1 + C_P)(1 + t)² · 3`) these are the same solutions; the data need only `D(L) ∩ Hˢ` and the
bound is uniform in time. -/
abbrev TorusSobolevDiscreteRate : Prop :=
  ∀ {s : ℝ}, 0 ≤ s → ∀ X : PiLp 2 Space, ∀ hX : X ∈ complex.wave.domain, MemSobStateT s X →
    ∀ (N : ℕ) (t : ℝ),
    ‖complex.waveGroup.S t X - complex.totalD.graphFst
        ((bandFamily.toFEEC (totalSub constraint) isClosed_totalSub).discrete N
          (waveLift complex ⟨X, hX⟩) t)‖ ≤ (1 / ((N : ℝ) + 1)) ^ s * √(sobStateT s X) ∧
      (X ∈ totalSub constraint →
        infDist (complex.totalD.graphFst
          ((bandFamily.toFEEC (totalSub constraint) isClosed_totalSub).discrete N
            (waveLift complex ⟨X, hX⟩) t)) (totalSub constraint : Set (PiLp 2 Space)) ≤
          (1 / ((N : ℝ) + 1)) ^ s * √(sobStateT s X))

/-- `TorusSobolevDiscreteRate`: the semi-discrete solutions are the truncated exact solutions
(`SpectralFamily.graphFst_discrete`), so the error is the truncation error
(`SpectralFamily.discrete_le_of_truncation`, `norm_sub_P_le_sobStateT`). -/
theorem einsteinBianchi_torus_discrete_sobolev : TorusSobolevDiscreteRate := by
  intro s hs X hX hS N t
  have h := bandFamily.discrete_le_of_truncation (totalSub constraint) isClosed_totalSub N
    ⟨X, hX⟩ (norm_sub_P_le_sobStateT hs hS N) t
  exact ⟨h.1, h.2 torusApprox_isReducing⟩

/-- **Non-vacuity of the time-uniform discrete rate on `𝕋³`**: the TSD state `decayState` lies in
`D(L) ∩ H³` (`decayState_nonvacuous`) and is not band-limited, so the error of the semi-discrete
solutions of `torusFEEC` is positive at every time and every `N` (it equals the truncation
error). -/
theorem torus_discrete_decayState_error_pos :
    ∃ hD : decayState ∈ complex.wave.domain, ∀ (N : ℕ) (t : ℝ),
    0 < ‖complex.waveGroup.S t decayState - complex.totalD.graphFst
        ((bandFamily.toFEEC (totalSub constraint) isClosed_totalSub).discrete N
          (waveLift complex ⟨decayState, hD⟩) t)‖ := by
  obtain ⟨-, -, -, hD, -⟩ := decayState_nonvacuous
  refine ⟨hD, fun N t => ?_⟩
  refine lt_of_lt_of_eq ?_ (bandFamily.norm_sub_discrete_eq (totalSub constraint)
    isClosed_totalSub N ⟨decayState, hD⟩ t).symm
  rw [norm_pos_iff, sub_ne_zero]
  intro h
  exact decayState_not_mem_band N
    ((Submodule.starProjection_eq_self_iff (K := totalSub (band N))).1 h.symm)

/-- **The time-uniform Sobolev rate of the spectral semi-discrete solutions on the mirror
cube**: for `x ∈ D(L)` with mirror extension in `Hˢ`, `s ≥ 0`, the semi-discrete solutions of
`mirrorFEEC` (spelled `bandFamilyQ.toFEEC (totalSub tsdQ) isClosed_totalSub`) from `Rₙ x`
satisfy `‖e^{tL} x - ξ_N(t)‖ ≤ (N + 1)^{-s} ‖x‖_s` for all `t ∈ ℝ`, and so does their TSD
residual when `x` is TSD. -/
abbrev MirrorSobolevDiscreteRate : Prop :=
  ∀ {s : ℝ}, 0 ≤ s → ∀ x : PiLp 2 SpaceQ, ∀ hx : x ∈ complexQ.wave.domain, MemSobState s x →
    ∀ (N : ℕ) (t : ℝ),
    ‖complexQ.waveGroup.S t x - complexQ.totalD.graphFst
        ((bandFamilyQ.toFEEC (totalSub tsdQ) isClosed_totalSub).discrete N
          (waveLift complexQ ⟨x, hx⟩) t)‖ ≤ (1 / ((N : ℝ) + 1)) ^ s * √(sobState s x) ∧
      (x ∈ totalSub tsdQ →
        infDist (complexQ.totalD.graphFst
          ((bandFamilyQ.toFEEC (totalSub tsdQ) isClosed_totalSub).discrete N
            (waveLift complexQ ⟨x, hx⟩) t)) (totalSub tsdQ : Set (PiLp 2 SpaceQ)) ≤
          (1 / ((N : ℝ) + 1)) ^ s * √(sobState s x))

theorem einsteinBianchi_mirror_discrete_sobolev : MirrorSobolevDiscreteRate := by
  intro s hs x hx hS N t
  have h := bandFamilyQ.discrete_le_of_truncation (totalSub tsdQ) isClosed_totalSub N
    ⟨x, hx⟩ (norm_sub_P_le_sobState hs hS N) t
  exact ⟨h.1, h.2 mirrorApprox_isReducing⟩

end Approx

end Feec.Instances.EinsteinBianchi
