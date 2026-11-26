module

public import Feec.Physics.EinsteinBianchi.WaveFEM
public import Feec.Physics.EinsteinBianchi.StaticFEM
public import Feec.Models.Cube.WeakSymmetryTangentialRate

/-!
# The Einstein–Bianchi system on the cube: rates for solutions with vanishing tangential traces

The rates of `Feec.EinsteinBianchi.StaticFEM.staticFEM` and `Feec.EinsteinBianchi.WaveFEM.waveFEM`
([QuennevilleBelair2015], §5.3, §6.3) for solutions that are `C²` up to `∂Q` with vanishing
tangential traces (`staticFEM_rate_tr`, `waveFEM_rate_tr`, `waveFEM_rate_tr_nonvacuous`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.StaticFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

set_option maxHeartbeats 1000000 in
/-- Under `CurlPotential`, for some common smoother, the error of (5.6) is `O(h_N)` for solutions of
(5.3) that are `C²` up to `∂Q` with vanishing tangential traces. [QuennevilleBelair2015], Thm 5.5 -/
theorem staticFEM_rate_tr (hR : CurlPotential) :
    ∃ (p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      (∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
        {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
        (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
          ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
        (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
          ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
        bggSegment.d0 σ = bggSegment.S0 φ →
        IsCsFormTr 0 0 L (σ : W0) → (∀ a, IsCsFormTr 0 0 L (φ a : W0)) →
        (∀ a, IsCsFormTr 0 1 L (u a : W1)) → ‖lam‖ ≤ L →
        ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
        σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
        uh ∈ (cubeFEM hT hB N).Vt1h →
        (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
          ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
            ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
        (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
          ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
            ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
        (∀ μ ∈ (cubeFEM hT hB N).V1h,
          ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
        Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
          (cubeFEM hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2) ∧
      ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {f : Wv W1} {x : Feec.BGG.Xsp V0 Vt0 Vt1} {lam : W1} {L : ℝ},
        0 ≤ L → bggHilb.IsSaddle f x (bggHilb.jW lam) →
        IsCsFormTr 0 0 L ((graphDomₗ (Feec.BGG.pσ V0 Vt0 Vt1 x) : U0) : W0) →
        (∀ a, IsCsFormTr 0 0 L ((rp (Feec.BGG.pφ V0 Vt0 Vt1 x) a : U0) : W0)) →
        (∀ a, IsCsFormTr 0 1 L ((rp1 (Feec.BGG.pu V0 Vt0 Vt1 x) a : U1) : W1)) → ‖lam‖ ≤ L →
        ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
        σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
        uh ∈ (cubeFEM hT hB N).Vt1h →
        (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
          ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
            ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
        (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
          ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
            ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = ((innerSL ℝ f).toLinearMap ∘ₗ incl1) v) →
        (∀ μ ∈ (cubeFEM hT hB N).V1h,
          ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
        Feec.BGG.graphSq bggSegment.d0 (graphDomₗ (Feec.BGG.pσ V0 Vt0 Vt1 x) - σh) +
          Feec.BGG.graphSq bggSegment.dt0 (rp (Feec.BGG.pφ V0 Vt0 Vt1 x) - φh) +
          (cubeFEM hT hB N).gnSq (rp1 (Feec.BGG.pu V0 Vt0 Vt1 x) - uh) ≤
            (K * L * meshSize N) ^ 2 := by
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrows := tableRows_uniform_cochainProjection
  obtain ⟨p, C, hT, hB, -⟩ := hrows
  exact ⟨p, C, hT, hB, cubeFEM_rate_tr hT hB hCR.1 hCR.2,
    cubeFEM_rate_isSaddle_tr hT hB hCR.1 hCR.2⟩

end Feec.EinsteinBianchi.StaticFEM

namespace Feec.EinsteinBianchi.WaveFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

set_option maxHeartbeats 4000000 in
/-- Under `CurlPotential`, the conclusions of `waveFEM` with its rate for solutions of (6.2) in
`IsSmoothStateTr`, and the rate of the elliptic projection (6.4). [QuennevilleBelair2015], §6.3 -/
theorem waveFEM_rate_tr (hR : CurlPotential) :
    ∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      (∀ N, (cubeFEM hT hB N).Compatible ∧ (cubeFEM hT hB N).Bounded (2 * C)) ∧
      (∀ N, Function.Injective (cubeWave hT hB N).dt0 ∧
        Function.Surjective (cubeWave hT hB N).S0) ∧
      (∀ (N : ℕ) {T : ℝ} (_ : 0 < T) {f : ℝ → (cubeFEM hT hB N).Vt1h},
        ContinuousOn f (Icc 0 T) → ∀ σ₀ u₀ M₀ ρ₀,
        (∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T f, s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧
          s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
          ∀ ψ, (cubeWave hT hB N).S0 ψ = 0 → ⟪u₀, (cubeWave hT hB N).dt0 ψ⟫ = 0) ∧
      (∀ (N : ℕ) {T : ℝ} {f : ℝ → (cubeFEM hT hB N).Vt1h}
        (s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T f), ContinuousOn f (Icc 0 T) →
        ∀ t ∈ Icc 0 T, √(‖s.σ t‖ ^ 2 + ‖s.u t‖ ^ 2 + ‖s.M t‖ ^ 2 + ‖s.ρ t‖ ^ 2) ≤
          √(‖s.σ 0‖ ^ 2 + ‖s.u 0‖ ^ 2 + ‖s.M 0‖ ^ 2 + ‖s.ρ 0‖ ^ 2) +
            ∫ r in (0:ℝ)..t, ‖f r‖) ∧
      (∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_ : 0 < T) {f : ℝ → Wv W1}
        (_ : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
        0 ≤ L →
        (∀ t ∈ Icc 0 T, IsSmoothStateTr L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
          IsSmoothStateTr L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
        (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
        ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
          (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
            (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
              (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
              (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
                (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
          ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
            ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N) ∧
      ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
        (ℓ : U1 →ₗ[ℝ] ℝ) {L : ℝ}, 0 ≤ L → bggSegment.d0 σ = bggSegment.S0 φ →
        (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → IsSmoothStateTr L σ φ u M ρ →
        ∀ {x : (((cubeFEM hT hB N).V0h × (cubeFEM hT hB N).Vt1h × (cubeFEM hT hB N).W2h ×
            (cubeFEM hT hB N).Wt2h) × (cubeFEM hT hB N).Vt0h) × (cubeFEM hT hB N).V1h},
        Feec.BGG.IsEllipticProjection (cubeFEM hT hB N).toSegmentH
          ((cubeFEM hT hB N).ellipticDataH σ φ u M ρ ℓ) 0 x →
        √(‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 +
          ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤ K * L * meshSize N := by
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrows := tableRows_uniform_cochainProjection
  obtain ⟨p, C, hT, hB, -⟩ := hrows
  exact ⟨p, C, hT, hB, fun N => ⟨cubeFEM_compatible hT hB N, cubeFEM_bounded hT hB N⟩,
    fun N => ⟨cubeWave_dt0_injective hT hB N, cubeWave_S0_surjective hT hB N⟩,
    fun N _ hT0 _ hf σ₀ u₀ M₀ ρ₀ => cubeWave_exists_iff_compatible_u hT hB N hT0 hf σ₀ u₀ M₀ ρ₀,
    fun N _ _ s hf => s.sqrt_energy_le hf, cubeWave_rate_tr hT hB hCR.1 hCR.2,
    cubeFEM_ellipticProjection_rate_tr hT hB hCR.1 hCR.2⟩

set_option maxHeartbeats 4000000 in
/-- Under `CurlPotential`, the classical solution `waveTangential T` of (6.2), nonzero and outside
every flat class `IsCsFormMin`, is approximated by solutions of (6.5) at rate `h_N`. -/
theorem waveFEM_rate_tr_nonvacuous {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) (hR : CurlPotential) {T : ℝ}
    (hT0 : 0 < T) :
    (∀ t, (waveTangential T).u t ≠ 0) ∧
    (∀ t s L, ¬ IsCsFormMin s 1 L (((waveTangential T).u t 0 : U1) : W1)) ∧
    ∃ (K : ℝ) (sh : (N : ℕ) → Feec.BGG.DiscreteSolution (cubeWave hT hB N) T
        (cubeSource hT hB N fun t => t • waveTangentialSrc)),
      ∀ N, ∀ t ∈ Icc 0 T,
        √(‖(waveTangential T).σ t - (sh N).σ t‖ ^ 2 +
          ‖(waveTangential T).u t - (sh N).u t‖ ^ 2 +
          ‖(waveTangential T).M t - (sh N).M t‖ ^ 2 +
          ‖(waveTangential T).ρ t - (sh N).ρ t‖ ^ 2) ≤ K * (1 + t) * meshSize N := by
  obtain ⟨L, hL0, hsm, hmult, hne⟩ := waveTangential_hyps hT0
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  obtain ⟨K, -, hK⟩ := cubeWave_rate_tr hT hB hCR.1 hCR.2
  have hf : ContinuousOn (fun t : ℝ => t • waveTangentialSrc) (Icc 0 T) :=
    (continuous_id.smul continuous_const).continuousOn
  have hsol := fun N => hK N hT0 hf (waveTangential T) hL0 hsm hmult
  choose sh _ hsh using hsol
  refine ⟨hne, fun t => not_isCsFormMin_tangentialU0, K * L, sh, fun N t ht => ?_⟩
  refine (hsh N t ht).trans (le_of_eq ?_); ring

end Feec.EinsteinBianchi.WaveFEM
