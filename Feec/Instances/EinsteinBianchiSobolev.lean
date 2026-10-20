module

public import Feec.Instances.EinsteinBianchiSpectral
public import Feec.Models.Cube.MirrorWaveRegularity

/-!
# Sobolev data lie in the approximation classes of the mirror spectral discretization

For the cosine–sine spectral family `Feec.Models.Cube.MirrorBGG.bandFamilyQ` of the mirror BGG
complex on `Q = (0, ½)³`, the truncation error of a state whose mirror extension lies in
`Hˢ(𝕋³)` (`Feec.Models.Cube.MirrorWeakSymmetry.MemSobState s`) is
`‖x - P_N x‖ ≤ (N + 1)^{-s} ‖x‖_s` (`norm_sub_P_le_sobState`): the modes off the band
`|n|_∞ ≤ N` have `|ξ| ≥ 2π (N + 1)`. Hence a TSD datum in `H^{2+s}`, `s ≥ 0`, lies in the
approximation class of order `s`, with norm at most `3 ‖ξ₀‖_{2+s}`
(`TSDDatum.mem_rateData_of_memSobState`, from `TSDDatum.memSobState_of_add_two`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.12–4.13, Ch. 6
-/

open scoped InnerProductSpace Topology
open Set Filter MeasureTheory

@[expose] public noncomputable section

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.BGG Feec.HilbertComplex
open Feec.Models.Torus.BGG (band bandFamily bandFamily_B)
open Feec.Models.Cube.MirrorBGG (bandFamilyQ)
open Feec.Models.Cube.Sobolev (weight weight_nonneg)
open Feec.ShortHilbertComplex (W3)

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

/-- **Truncation error of `Hˢ` states on `Q`**: `‖x - P_N x‖ ≤ (N + 1)^{-s} ‖x‖_s`. -/
theorem norm_sub_P_le_sobState {s : ℝ} (hs : 0 ≤ s) {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemSobState s x) (N : ℕ) :
    ‖x - bandFamilyQ.P N x‖ ≤ (1 / ((N : ℝ) + 1)) ^ s * √(sobState s x) := by
  set c : ℝ := ((2 * Real.pi * ((N : ℝ) + 1)) ^ 2) ^ s with hc
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by positivity) s
  -- the extension of the truncation is the truncation of the extension
  have hJ : extState (x - bandFamilyQ.P N x) = extState x - bandFamily.P N (extState x) := by
    refine PiLp.ext fun i => ?_
    rw [totalJ_apply, PiLp.sub_apply, _root_.map_sub, PiLp.sub_apply, totalJ_apply,
      SpectralFamily.P, SpectralFamily.P, totalSub_starProjection_apply,
      totalSub_starProjection_apply]
    congr 1
    exact MirrorBGG.embeddingQ.starProjection_comap _
      (MirrorBGG.exists_J_eq_starProjection_band N i) (x i)
  have hsq : ‖x - bandFamilyQ.P N x‖ ^ 2 ≤ c⁻¹ * sobState s x := by
    rw [norm_sq_eq_tsum_extState, hJ, sobState]
    have hle : ∀ m, fibreEnergy (extState x - bandFamily.P N (extState x)) m ≤
        c⁻¹ * (weight s m * fibreEnergy (extState x) m) := fun m => by
      rw [fibreEnergy_sub_P]
      split_ifs with hm
      · exact mul_nonneg (inv_nonneg.2 hcpos.le)
          (mul_nonneg (weight_nonneg s m) (fibreEnergy_nonneg _ m))
      · have h1 : 1 ≤ c⁻¹ * weight s m := by
          rw [inv_mul_eq_div, one_le_div hcpos]; exact pow_le_weight hm hs
        rw [← mul_assoc]
        exact le_mul_of_one_le_left (fibreEnergy_nonneg _ m) h1
    have hsum := hx.mul_left c⁻¹
    have h := Summable.tsum_le_tsum hle
      (Summable.of_nonneg_of_le (fun m => fibreEnergy_nonneg _ m) hle hsum) hsum
    rw [tsum_mul_left] at h
    nlinarith
  have hc' : c⁻¹ ≤ ((1 / ((N : ℝ) + 1)) ^ s) ^ 2 := by
    have h1 : ((N : ℝ) + 1) ^ 2 ≤ (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 := by
      have : (N : ℝ) + 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) := by nlinarith [Real.two_le_pi]
      exact pow_le_pow_left₀ hN.le this 2
    have h2 : (((N : ℝ) + 1) ^ 2) ^ s ≤ c := Real.rpow_le_rpow (by positivity) h1 hs
    have h3 : (((N : ℝ) + 1) ^ 2) ^ s = (((N : ℝ) + 1) ^ s) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_natCast (((N : ℝ) + 1) ^ s),
        ← Real.rpow_mul hN.le, mul_comm]
    have h4 : (1 / ((N : ℝ) + 1)) ^ s = (((N : ℝ) + 1) ^ s)⁻¹ := by
      rw [Real.div_rpow zero_le_one hN.le, Real.one_rpow, one_div]
    rw [h4, inv_pow]
    exact inv_anti₀ (by positivity) (h3 ▸ h2)
  have hS := sobState_nonneg s x
  have key : ‖x - bandFamilyQ.P N x‖ ^ 2 ≤ ((1 / ((N : ℝ) + 1)) ^ s * √(sobState s x)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hS]
    exact hsq.trans (mul_le_mul_of_nonneg_right hc' hS)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key

/-- **TSD data in `H^{2+s}` lie in the approximation class of order `s`** of the mirror spectral
discretization, with class norm at most `3 ‖ξ₀‖_{2+s}`. -/
theorem TSDDatum.mem_rateData_of_memSobState (D : TSDDatum) {s : ℝ} (hs : 0 ≤ s)
    (h : MemSobState (2 + s) D.U₀) :
    D.U₀ ∈ bandFamilyQ.rateData s ∧
      bandFamilyQ.rateNorm s D.U₀ ≤ 3 * √(sobState (2 + s) D.U₀) := by
  obtain ⟨h0, h1, h2, hb⟩ := D.memSobState_of_add_two h
  have e1 : MirrorBGG.complexQ.waveExt D.U₀ = D.LU₀ := waveExt_of_mem D.mem
  have e2 : MirrorBGG.complexQ.waveExt D.LU₀ = D.LLU₀ := waveExt_of_mem D.mem₂
  have htail : ∀ N : ℕ, ((N : ℝ) + 1) ^ s * bandFamilyQ.tail N D.U₀ ≤ D.sobSize s := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hp : ((N : ℝ) + 1) ^ s * (1 / ((N : ℝ) + 1)) ^ s = 1 := by
      rw [← Real.mul_rpow hN.le (by positivity), mul_one_div_cancel hN.ne', Real.one_rpow]
    have hP := Real.rpow_pos_of_pos hN s
    rw [SpectralFamily.tail, e1, e2]
    have a0 := norm_sub_P_le_sobState hs h0 N
    have a1 := norm_sub_P_le_sobState hs h1 N
    have a2 := norm_sub_P_le_sobState hs h2 N
    calc ((N : ℝ) + 1) ^ s * (‖D.U₀ - bandFamilyQ.P N D.U₀‖ + ‖D.LU₀ - bandFamilyQ.P N D.LU₀‖ +
          ‖D.LLU₀ - bandFamilyQ.P N D.LLU₀‖)
        ≤ ((N : ℝ) + 1) ^ s * ((1 / ((N : ℝ) + 1)) ^ s * D.sobSize s) := by
          gcongr
          unfold TSDDatum.sobSize
          linarith
      _ = D.sobSize s := by rw [← mul_assoc, hp, one_mul]
  have hbdd : BddAbove (range fun N : ℕ => ((N : ℝ) + 1) ^ s * bandFamilyQ.tail N D.U₀) :=
    ⟨D.sobSize s, by rintro _ ⟨N, rfl⟩; exact htail N⟩
  refine ⟨⟨D.mem, e1 ▸ D.mem₂, hbdd⟩, (ciSup_le htail).trans hb⟩

/-- States with finitely many modes lie in every `Hʳ`. -/
theorem memSobState_of_finite {x : PiLp 2 MirrorBGG.SpaceQ} (S : Finset (Fin 3 → ℤ))
    (hx : ∀ m ∉ S, fibreEnergy (extState x) m = 0) (r : ℝ) : MemSobState r x :=
  summable_of_ne_finset_zero fun m hm => by rw [hx m hm, mul_zero]

/-- **The cos datum lies in every `Hʳ`**: its mirror extension has the modes `±k₀` only. -/
theorem cosDatum_memSobState (r : ℝ) : MemSobState r cosDatum.U₀ := by
  refine memSobState_of_finite {Models.Cube.Mirror.k0, -Models.Cube.Mirror.k0} (fun m hm => ?_) r
  change fibreEnergy (totalJ MirrorBGG.J MirrorBGG.cosStateQ) m = 0
  rw [MirrorBGG.totalJ_cosStateQ]
  unfold fibreEnergy
  exact Finset.sum_eq_zero fun i _ => by rw [cosState_finite i m hm, norm_zero]; norm_num

end Feec.Models.Cube.MirrorWeakSymmetry
