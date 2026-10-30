import Feec.Models.Cube.SobolevRateHigh
import Feec.Instances.Corollaries

/-!
# Regression tests: Sobolev rates on the cube without `2 r_eff > n`

The optimal rates `h^{min(s, r_eff)}` for `Hˢ` data of `Feec.Models.Cube.SobolevRateHigh` were
proved under the condition `2 r_eff > n` (`hns : n < 2 * (p + 1)`; `n ≤ 3` for the `P₂` bottom
row), inherited from the Sobolev embedding of `H^{r_eff}` into `C⁰` behind the point values of
the canonical interpolant. The interpolation error is now bounded with lower-order terms in every
dimension (`Feec.Models.Cube.FEM.norm_formL2_sub_glue_globalInterp_le_sum`, from the Sobolev
embedding of `D^{r_eff} w`, `Feec.FiniteElement.enorm_le_L2`), and the rate theorems have lost
the condition, with a new constant `sobConstHigh`. The old constant is kept as
`sobConstHighEmb`, with its interpolation step `norm_formL2_truncField_sub_glue_le_emb` for
`2 r_eff > n`.

The theorems `rough_old_*` state the old results verbatim, with the now unused hypotheses named
`_hns`, `_hn3`, and are proved from the new API:
* the interpolation step `exists_mem_near_truncField_le` and the two best-approximation theorems
  `infDist_poly_le_sobolevQ_high`, `infDist_polyPartial_le_sobolevPar_high` keep their old
  meaning: the old constant `sobConstHigh` is renamed `sobConstHighEmb`, and they are derived
  through `infDist_poly_le_sobolevQ_of_near` and `infDist_polyPartial_le_sobolevPar_of_near`;
* the mixed rates (`∃ K`) keep their old meaning unchanged;
* the theorems with an explicit degreewise constant (`sobConstHighZ`, `sobConstHighParZ`, the
  windows, `sobolevHighJackson`) are stated with the new constant `sobConstHigh`: their old
  values, built from `sobConstHighEmb`, are not preserved. The Jackson estimate
  `sobolevHighJackson n S p` takes the order `p` in place of the proof of `2 (p + 1) > n`.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

open scoped InnerProductSpace Topology ContDiff ENNReal
open Set MeasureTheory Filter Finset

namespace FeecCheck.RoughRates

open Feec Feec.Domain Feec.Mesh Feec.HilbertComplex Feec.FiniteElement Feec.ExteriorFibre
open Feec.Models.Cube Feec.Models.Cube.FEM Feec.Models.Cube.Sobolev

variable {n : ℕ}

/-- The old `Feec.Models.Cube.FEM.exists_mem_near_truncField_le`, with the old `sobConstHigh`
renamed `sobConstHighEmb`. -/
theorem rough_old_exists_mem_near_truncField_le (S : PolySeq) {k p : ℕ} {q s : ℝ} (hq0 : 0 ≤ q)
    (hqp : q ≤ p + 1) (hqs : q ≤ s)
    {x : Seq n k} (hx : MemSob s x) (N : ℕ) :
    √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) (truncField k x (N + 1)) y‖ ^ 2) *
        meshSize N ^ (p + 1) * globalL2Const n S k p ≤
      (sobConstHighEmb n S k p - 1) * meshSize N ^ q * √(sobSum s x) := by
  have h := meshSize_pow_mul_sqrt_integral_truncField_le (r := p + 1) hq0
    (by exact_mod_cast hqp) hqs hx N
  have := mul_le_mul_of_nonneg_left h (globalL2Const_nonneg (n := n) S k p)
  rw [sobConstHighEmb, add_sub_cancel_left]
  linarith

/-- The old `Feec.Models.Cube.FEM.infDist_poly_le_sobolevQ_high`, with the old `sobConstHigh`
renamed `sobConstHighEmb`. -/
theorem rough_old_infDist_poly_le_sobolevQ_high [NeZero n] (S : PolySeq) (k p : ℕ)
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {s : ℝ} (hs0 : 0 ≤ s)
    (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k)) (hy : toQ k y ∈ sobolevQ n k s) :
    Metric.infDist y ((poly n S N).V k) ≤
      sobConstHighEmb n S k p * meshSize N ^ min s (p + 1) * qNorm k s (toQ k y) :=
  have hq0 : 0 ≤ min s (p + 1) := le_min hs0 (by positivity)
  infDist_poly_le_sobolevQ_of_near S (sobConstHighEmb_nonneg S k p) hq0 (min_le_left _ _)
    (fun _ hx => norm_formL2_truncField_sub_glue_le_emb S hs hns hq0 (min_le_right _ _)
      (min_le_left _ _) hx N) y hy

/-- The old `Feec.Models.Cube.FEM.infDist_polyPartial_le_sobolevPar_high`, with the old
`sobConstHigh` renamed `sobConstHighEmb`. -/
theorem rough_old_infDist_polyPartial_le_sobolevPar_high [NeZero n] (S : PolySeq)
    (J : Finset (Fin n)) (k p : ℕ) (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1))
    {s : ℝ} (hs0 : 0 ≤ s) (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : toQ k y ∈ sobolevPar J k s) :
    Metric.infDist y ((polyPartial n S N J).V k) ≤
      √(2 ^ n) * sobConstHighEmb n S k p * meshSize N ^ min s (p + 1) *
        parNorm J k s (toQ k y) :=
  have hq0 : 0 ≤ min s (p + 1) := le_min hs0 (by positivity)
  infDist_polyPartial_le_sobolevPar_of_near S J hq0 (min_le_left _ _)
    (fun _ hx => norm_formL2_truncField_sub_glue_le_emb S hs hns hq0 (min_le_right _ _)
      (min_le_left _ _) hx N) y hy

/-- The old `Feec.Models.Cube.FEM.infDist_poly_le_sobAt_high`, with the new constant
`sobConstHighZ` (the old value is not preserved). -/
theorem rough_old_infDist_poly_le_sobAt_high [NeZero n] (S : PolySeq) {p : ℕ}
    (_hns : n < 2 * (p + 1)) {s L : ℝ} (hs0 : 0 ≤ s) (N : ℕ) {j : ℤ}
    (hS : ∀ k : ℕ, (k : ℤ) = j → polySpace n p k ≤ S.space n k)
    {y : L2F ℝ (cubeDomain n) (formIdx n j)} (hy : SobAt n s L j y) :
    Metric.infDist y ((poly n S N).V j) ≤
      sobConstHighZ n S p j * meshSize N ^ min s (p + 1) * L :=
  infDist_poly_le_sobAt_high S hs0 N hS hy

/-- The old `Feec.Models.Cube.FEM.mixed_rate_sobolevQ_high`. -/
theorem rough_old_mixed_rate_sobolevQ_high [NeZero n] (S : PolySeq) {p : ℕ}
    (_hns : n < 2 * (p + 1)) {s : ℝ} (hs0 : 0 ≤ s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    (hS : ∀ d : ℕ, i ≤ d → (d : ℤ) ≤ i + 2 → polySpace n p d ≤ S.space n d) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    SobGraph n s L σ → SobGraph n s L u →
    SobGraph n s L ((complex n).boundaryPart j ((complex n).domainIncl j u)) →
    SobAt n s L j (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ min s (p + 1) :=
  mixed_rate_sobolevQ_high S hs0 hij hjk hS

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.exists_mem_window_le_sob_high`,
with the new constant `sobConstHighZ` (the old value is not preserved). -/
theorem rough_old_exists_mem_window_le_sob_high [NeZero n] {S : PolySeq}
    {p' : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p' C)
    {p : ℕ} (_hns : n < 2 * (p + 1)) {s L : ℝ} (hs0 : 0 ≤ s) (hL0 : 0 ≤ L) {a : ℤ} {m : ℕ}
    (hS : ∀ k : ℕ, a ≤ k → (k : ℤ) ≤ a + m → polySpace n p k ≤ S.space n k)
    (ζ : ((complex n).window a m).totalD.GraphSpace)
    (hζ : ∀ i : Fin m, SobComp n s L (((complex n).window a m).totalD.graphFst ζ i)) (N : ℕ) :
    ∃ w ∈ ((poly n S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * ((1 + 2 * C) * (∑ i : Fin m, (sobConstHighZ n S p (a + i) +
        sobConstHighZ n S p (a + i + 1))) * meshSize N ^ min s (p + 1) * L) :=
  hE.exists_mem_window_le_sob_high hs0 hL0 hS ζ hζ N

/-- The old `Feec.Models.Cube.FEM.PolySmoothingEstimates.norm_sub_le_window_sobolevQ_high`,
with the new constant `sobConstHighZ` (the old value is not preserved). -/
theorem rough_old_norm_sub_le_window_sobolevQ_high [NeZero n] {S : PolySeq}
    {p' : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p' C)
    {p : ℕ} (_hns : n < 2 * (p + 1)) {s : ℝ} (hs0 : 0 ≤ s) (a : ℤ) (m : ℕ)
    (hS : ∀ k : ℕ, a ≤ k → (k : ℤ) ≤ a + m → polySpace n p k ≤ S.space n k) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((poly n S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((poly n S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      SobComp n s L (((complex n).window a m).totalD.graphFst (ξ τ) i) ∧
        SobComp n s L (((complex n).window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 * (((m : ℝ) + m * m) * ((1 + 2 * C) * (∑ i : Fin m,
          (sobConstHighZ n S p (a + i) + sobConstHighZ n S p (a + i + 1))) *
            meshSize N ^ min s (p + 1) * L)) :=
  hE.norm_sub_le_window_sobolevQ_high hs0 a m hS hξ hξh h0 hL0 hreg N ht

section Parity

variable (J : Finset (Fin n))

/-- The old `Feec.Models.Cube.FEM.infDist_polyPartial_le_sobAtPar_high`, with the new constant
`sobConstHighParZ` (the old value is not preserved). -/
theorem rough_old_infDist_polyPartial_le_sobAtPar_high [NeZero n] (S : PolySeq) {p : ℕ}
    (_hns : n < 2 * (p + 1)) {s L : ℝ} (hs0 : 0 ≤ s) (N : ℕ) {j : ℤ}
    (hS : ∀ k : ℕ, (k : ℤ) = j → polySpace n p k ≤ S.space n k)
    {y : L2F ℝ (cubeDomain n) (formIdx n j)} (hy : SobAtPar n J s L j y) :
    Metric.infDist y ((polyPartial n S N J).V j) ≤
      sobConstHighParZ n S p j * meshSize N ^ min s (p + 1) * L :=
  infDist_polyPartial_le_sobAtPar_high J S hs0 N hS hy

/-- The old `Feec.Models.Cube.FEM.ParitySmoothingEstimates.infDist_domainSub_le_sobGraphPar_high`,
with the new constant `sobConstHighParZ` (the old value is not preserved). -/
theorem rough_old_infDist_domainSub_le_sobGraphPar_high [NeZero n] {S : PolySeq}
    {ρ : ℕ → ParitySmoother.ReflKernel n} {C : ℝ} (hE : ParitySmoothingEstimates n J S ρ C)
    {p : ℕ} (_hns : n < 2 * (p + 1)) {s L : ℝ} (hs0 : 0 ≤ s) (N : ℕ) {j : ℤ}
    (hS0 : ∀ k : ℕ, (k : ℤ) = j → polySpace n p k ≤ S.space n k)
    (hS1 : ∀ k : ℕ, (k : ℤ) = j + 1 → polySpace n p k ≤ S.space n k)
    {σ : (complexPart n J).domainSpace j} (hσ : SobGraphPar n J s L σ) :
    Metric.infDist σ ((polyPartial n S N J).domainSub j) ≤
      (1 + 2 * C) * (sobConstHighParZ n S p j + sobConstHighParZ n S p (j + 1)) *
        meshSize N ^ min s (p + 1) * L :=
  hE.infDist_domainSub_le_sobGraphPar_high hs0 N hS0 hS1 hσ

/-- The old `Feec.Models.Cube.FEM.mixed_rate_sobolevPar_high`. -/
theorem rough_old_mixed_rate_sobolevPar_high [NeZero n] (S : PolySeq) {p : ℕ}
    (_hns : n < 2 * (p + 1)) {s : ℝ} (hs0 : 0 ≤ s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    (hS : ∀ d : ℕ, i ≤ d → (d : ℤ) ≤ i + 2 → polySpace n p d ≤ S.space n d) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexPart n J).domainSpace i}
    {u : (complexPart n J).domainSpace j} {q : (complexPart n J).harmonic j},
    (complexPart n J).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    SobGraphPar n J s L σ → SobGraphPar n J s L u →
    SobGraphPar n J s L ((complexPart n J).boundaryPart j ((complexPart n J).domainIncl j u)) →
    SobAtPar n J s L j (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (polyPartial n S N J).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyPartial n S N J) hij hjk f).fst‖ +
        ‖u - (polyPartial n S N J).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyPartial n S N J) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyPartial n S N J) hij hjk
            f).snd.snd : (polyPartial n S N J).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ min s (p + 1) :=
  mixed_rate_sobolevPar_high J S hs0 hij hjk hS

end Parity

/-- The old `Feec.Models.Cube.FEM.mixed_rate_sobolevQ_high_of_polyOrderAt`. -/
theorem rough_old_mixed_rate_sobolevQ_high_of_polyOrderAt [NeZero n] (S : PolySeq) {p : ℕ}
    (_hns : n < 2 * (p + 1)) {s : ℝ} (hs0 : 0 ≤ s) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) (hj : 0 ≤ j)
    (hSi : PolyOrderAt n S p i) (hSj : PolyOrderAt n S p j) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    SobGraph n s L σ → SobGraph n s L u →
    SobGraph n s L ((complex n).boundaryPart j ((complex n).domainIncl j u)) →
    SobAt n s L j (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ min s (p + 1) :=
  mixed_rate_sobolevQ_high_of_polyOrderAt S hs0 hij hjk hj hSi hSj

/-- The old `Feec.Models.Cube.FEM.mixed_rate_lagrangeP2_sobolevQ`. -/
theorem rough_old_mixed_rate_lagrangeP2_sobolevQ [NeZero n] (_hn3 : n ≤ 3) {s : ℝ} (hs0 : 0 ≤ s) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n 1)} {σ : (complex n).domainSpace 0}
    {u : (complex n).domainSpace 1} {q : (complex n).harmonic 1},
    (complex n).IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    SobGraph n s L σ → SobGraph n s L u →
    SobGraph n s L ((complex n).boundaryPart 1 ((complex n).domainIncl 1 u)) →
    SobAt n s L 1 (q : L2F ℝ (cubeDomain n) (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - (poly n PolySeq.lagrangeP2 N).embD 0
          (Subcomplex.CochainProjection.discreteMixedSolution
            (poly n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
        ‖u - (poly n PolySeq.lagrangeP2 N).embD 1
          (Subcomplex.CochainProjection.discreteMixedSolution
            (poly n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n 1)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n PolySeq.lagrangeP2 N)
            (i := 0) (j := 1) (k := 2) rfl rfl f).snd.snd :
            (poly n PolySeq.lagrangeP2 N).V 1) : L2F ℝ (cubeDomain n) (formIdx n 1))‖ ≤
      K * L * meshSize N ^ min s 2 :=
  mixed_rate_lagrangeP2_sobolevQ hs0

/-- The old `Feec.Models.Cube.FEM.exists_norm_sub_le_window_sobolevQ_high`. -/
theorem rough_old_exists_norm_sub_le_window_sobolevQ_high [NeZero n] (S : PolySeq) {p : ℕ}
    (_hns : n < 2 * (p + 1)) {s : ℝ} (hs0 : 0 ≤ s) (a : ℤ) (m : ℕ)
    (hS : ∀ k : ℕ, a ≤ k → (k : ℤ) ≤ a + m → polySpace n p k ≤ S.space n k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t₀ t₁ : ℝ} {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace},
      HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ' →
      ∀ {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace},
      (∀ N, HodgeWave.IsSemidiscreteSolution (((poly n S N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) →
      (∀ N, ξh N t₀ =
        HodgeWave.ellipticProjection (((poly n S N).window a m).graphSub) (ξ t₀)) →
      ∀ {L : ℝ}, 0 ≤ L →
      (∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
        SobComp n s L (((complex n).window a m).totalD.graphFst (ξ τ) i) ∧
          SobComp n s L (((complex n).window a m).totalD.graphFst (ξ' τ) i)) →
      ∀ (N : ℕ) {t : ℝ}, t ∈ Set.Icc t₀ t₁ →
      ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
        (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
          (1 + (t - t₀)) ^ 2 * (K * meshSize N ^ min s (p + 1) * L) :=
  exists_norm_sub_le_window_sobolevQ_high S hs0 a m hS

/-- The old `Feec.Instances.Corollaries.Cube.FEM.feec_sobolev`, with `sobolevHighJackson n S p`
for the old `sobolevHighJackson n S hns` (whose constants are now built from the new
`sobConstHigh`). -/
theorem rough_old_feec_sobolev [NeZero n] (S : PolySeq) {p : ℕ} (_hns : n < 2 * (p + 1)) :
    ConformingFamily.Verdict.Rated (polyFamily n S) (sobolevHighJackson n S p) :=
  Feec.Instances.Corollaries.Cube.FEM.feec_sobolev n S p

end FeecCheck.RoughRates
