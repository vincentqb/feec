module

public import Feec.Models.Cube.RegularDecomposition
public import Feec.Physics.EinsteinBianchi.WaveFEMTangential

/-!
# The tangential-trace rates on the cube, unconditionally

The rates of `Feec.Models.Cube.WeakSymmetryTangentialRate` (Thm 5.5, the elliptic projection (6.4)
and the scheme (6.5) for solutions that are `C²` up to `∂Q` with vanishing tangential traces) and
the headline theorems of `Feec.Physics.EinsteinBianchi.WaveFEMTangential` take the regularity
hypothesis `curl H̊(curl) = curl S⁰ H̊¹(Q; ℝ³)` (`CurlPotential`, or its constant `C_R`) as a
hypothesis. It is a theorem (`Feec.Models.Cube.WeakSymmetry.curlPotential`,
`exists_curlPotential_bound`, `Feec.Models.Cube.RegularDecomposition`), and this file states them
without it.

## Main results

* `Feec.Models.Cube.WeakSymmetry.cubeFEM_rate_tr'`, `cubeFEM_rate_tr_of_bounds'`,
  `cubeFEM_rate_isSaddle_tr'` (Thm 5.5), `cubeFEM_ellipticProjection_rate_tr'` (the `O(h)` rate of
  the elliptic projection (6.4)), `cubeWave_rate_tr'` (the `O(h)` rate of (6.5));
* `Feec.EinsteinBianchi.StaticFEM.staticFEM_rate_tr_cube`, `staticFEM_rate_tr_nonvacuous_cube`,
  `staticFEM_rate_tr_nonvacuous_combined_cube`;
* `Feec.EinsteinBianchi.WaveFEM.waveFEM_rate_tr_cube`, `waveFEM_rate_tr_nonvacuous_cube`.

## The failing datum is not in the rate class

The TSD datum `(σ, u, (M, B))(0) = (0, 0, (0, β))`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`, of
`Feec.Counterexamples.BoundedBGG.bggComplex_verdict` (transported to this model in
`Feec.Physics.EinsteinBianchi.MatrixModel`) is **not covered** by these rates: its magnetic rows
`ρₐ(0)` (the `2`-forms of the rows of `β`) have nonzero tangential components on `∂Q` (the first
row of `β` is `x₃ e₂`, whose `2`-form has the `{0, 2}` component `-y₂`, tangential to the faces
`{y₁ = 0}` and `{y₁ = ½}`), so `ρ(0)` is in no class `IsCsFormTr 0 2 L`. Moreover
`u'(0) = diag(1, -1, 0)` does not vanish on `∂Q` while `u(t) ∈ H̊Λ¹(Q)³` for all `t`, so the solution
is not `C²` in space up to `∂Q` uniformly in `t` (the incompatibility of the datum with the boundary
condition launches a front from `∂Q`). Its convergence without rate is the subject of
`Feec.Physics.EinsteinBianchi.BoundedFailure`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Thm 5.5; §6.2 (6.4), §6.3 ((6.5), Table 6.1)
-/

open scoped InnerProductSpace RealInnerProductSpace ContDiff
open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM

section CubeFEM

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

set_option maxHeartbeats 1000000 in
/-- **`cubeFEM_rate_tr_of_bounds`, unconditionally**: with the constant of `curlPotential`
(`exists_curlPotential_bound`). -/
theorem cubeFEM_rate_tr_of_bounds' :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
      {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
        ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
      (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
        ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
      bggSegment.d0 σ = bggSegment.S0 φ →
      IsCsFormTr 0 0 L (σ : W0) → (∀ a, IsCsFormTr 0 0 L (φ a : W0)) →
      (∀ a, IsCsFormTr 0 1 L (u a : W1)) → IsCsFormTr 0 2 L (bggSegment.S1 u) →
      ‖lam‖ ≤ L → ‖bggSegment.S1 u‖ ≤ L →
      (∀ w : U1, |⟪bggSegment.S1 u, bggSegment.d1 w⟫| ≤ L * ‖w‖) →
      ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
      σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
      uh ∈ (cubeFEM hT hB N).Vt1h →
      (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
        ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
          ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
      (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
        ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
        (cubeFEM hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2 :=
  exists_curlPotential_bound.elim fun _ h => cubeFEM_rate_tr_of_bounds hT hB h.1 h.2

set_option maxHeartbeats 1000000 in
/-- **[QuennevilleBelair2015], Thm 5.5 for solutions with vanishing tangential traces,
unconditionally**: `cubeFEM_rate_tr` with the constant of `curlPotential`. -/
theorem cubeFEM_rate_tr' :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
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
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
        (cubeFEM hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2 :=
  exists_curlPotential_bound.elim fun _ h => cubeFEM_rate_tr hT hB h.1 h.2

set_option maxHeartbeats 1000000 in
/-- **The rate for the solution of Prop 5.2 with vanishing tangential traces, unconditionally**:
`cubeFEM_rate_isSaddle_tr` with the constant of `curlPotential`. -/
theorem cubeFEM_rate_isSaddle_tr' :
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
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (graphDomₗ (Feec.BGG.pσ V0 Vt0 Vt1 x) - σh) +
        Feec.BGG.graphSq bggSegment.dt0 (rp (Feec.BGG.pφ V0 Vt0 Vt1 x) - φh) +
        (cubeFEM hT hB N).gnSq (rp1 (Feec.BGG.pu V0 Vt0 Vt1 x) - uh) ≤
          (K * L * meshSize N) ^ 2 :=
  exists_curlPotential_bound.elim fun _ h => cubeFEM_rate_isSaddle_tr hT hB h.1 h.2

set_option maxHeartbeats 4000000 in
/-- **The `O(h)` rate of the elliptic projection (6.4) on the cube, unconditionally**:
`cubeFEM_ellipticProjection_rate_tr` with the constant of `curlPotential`. -/
theorem cubeFEM_ellipticProjection_rate_tr' :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
      (ℓ : U1 →ₗ[ℝ] ℝ) {L : ℝ}, 0 ≤ L → bggSegment.d0 σ = bggSegment.S0 φ →
      (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → IsSmoothStateTr L σ φ u M ρ →
      ∀ {x : (((cubeFEM hT hB N).V0h × (cubeFEM hT hB N).Vt1h × (cubeFEM hT hB N).W2h ×
          (cubeFEM hT hB N).Wt2h) × (cubeFEM hT hB N).Vt0h) × (cubeFEM hT hB N).V1h},
      Feec.BGG.IsEllipticProjection (cubeFEM hT hB N).toSegmentH
        ((cubeFEM hT hB N).ellipticDataH σ φ u M ρ ℓ) 0 x →
      √(‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 +
        ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤ K * L * meshSize N :=
  exists_curlPotential_bound.elim fun _ h => cubeFEM_ellipticProjection_rate_tr hT hB h.1 h.2

set_option maxHeartbeats 4000000 in
/-- **The `O(h)` rate of the scheme (6.5) for states with vanishing tangential traces,
unconditionally**: `cubeWave_rate_tr` with the constant of `curlPotential`. -/
theorem cubeWave_rate_tr' :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
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
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N :=
  exists_curlPotential_bound.elim fun _ h => cubeWave_rate_tr hT hB h.1 h.2

end CubeFEM

end Feec.Models.Cube.WeakSymmetry

namespace Feec.EinsteinBianchi.StaticFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

set_option maxHeartbeats 1000000 in
/-- **`staticFEM_rate_tr`, unconditionally**: the static rates for solutions with vanishing
tangential traces, with the regularity hypothesis discharged by `curlPotential`. -/
theorem staticFEM_rate_tr_cube :
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
            (K * L * meshSize N) ^ 2 :=
  staticFEM_rate_tr curlPotential

set_option maxHeartbeats 1000000 in
/-- **Non-vacuity of `staticFEM_rate_tr_cube`**: `staticFEM_rate_tr_nonvacuous` with the regularity
hypothesis discharged. -/
theorem staticFEM_rate_tr_nonvacuous_cube {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) :
    tangentialU ≠ 0 ∧ (∀ s L, ¬ IsCsFormMin s 1 L ((tangentialU 0 : U1) : W1)) ∧
    (∃ (K : ℝ) (uh : ℕ → Wv U1), ∀ N, uh N ∈ (cubeFEM hT hB N).Vt1h ∧
      ∃ (σh : U0) (φh : Wv U0) (lh : U1), σh ∈ (cubeFEM hT hB N).V0h ∧
        φh ∈ (cubeFEM hT hB N).Vt0h ∧
        (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
          ⟪σh, τ⟫ - ⟪uh N, bggSegment.dt0 ψ⟫ -
            ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) ∧
        (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
          ⟪(cubeFEM hT hB N).S1h (uh N), (cubeFEM hT hB N).S1h v⟫ +
            ⟪bggSegment.dt1 (uh N), bggSegment.dt1 v⟫ = tangentialDatum v) ∧
        (∀ μ ∈ (cubeFEM hT hB N).V1h,
          ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) ∧
        (cubeFEM hT hB N).gnSq (tangentialU - uh N) ≤ (K * meshSize N) ^ 2) :=
  let h := staticFEM_rate_tr_nonvacuous hT hB
  ⟨h.1, h.2.1, h.2.2 curlPotential⟩

set_option maxHeartbeats 2000000 in
/-- **Non-vacuity of `staticFEM_rate_tr_cube` with every unknown nonzero and non-flat `u`**:
`staticFEM_rate_tr_nonvacuous_combined` with the regularity hypothesis discharged. -/
theorem staticFEM_rate_tr_nonvacuous_combined_cube
    {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)}
    {C : ℝ} (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) :
    coupledσ ≠ 0 ∧ coupledφ ≠ 0 ∧ coupledMult ≠ 0 ∧
    (∀ L, ¬ IsCsFormMin 0 1 L ((((coupledu + tangentialU : Wv U1)) 0 : U1) : W1)) ∧
    (∃ K : ℝ, ∀ N, ∃ (σh : U0) (φh : Wv U0) (uh : Wv U1) (lh : U1),
      σh ∈ (cubeFEM hT hB N).V0h ∧ φh ∈ (cubeFEM hT hB N).Vt0h ∧ uh ∈ (cubeFEM hT hB N).Vt1h ∧
        (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
          ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
            ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) ∧
        (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
          ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
            ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = (coupledDatum + tangentialDatum) v) ∧
        (∀ μ ∈ (cubeFEM hT hB N).V1h,
          ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) ∧
        Feec.BGG.graphSq bggSegment.d0 (coupledσ - σh) +
          Feec.BGG.graphSq bggSegment.dt0 (coupledφ - φh) +
          (cubeFEM hT hB N).gnSq ((coupledu + tangentialU) - uh) ≤ (K * meshSize N) ^ 2) :=
  let h := staticFEM_rate_tr_nonvacuous_combined hT hB
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2 curlPotential⟩

end Feec.EinsteinBianchi.StaticFEM

namespace Feec.EinsteinBianchi.WaveFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

set_option maxHeartbeats 4000000 in
/-- **`waveFEM_rate_tr`, unconditionally**: the rate of (6.5) for solutions with vanishing
tangential traces, with the regularity hypothesis discharged by `curlPotential`. -/
theorem waveFEM_rate_tr_cube :
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
          ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤ K * L * meshSize N :=
  waveFEM_rate_tr curlPotential

set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `waveFEM_rate_tr_cube`**: `waveFEM_rate_tr_nonvacuous` with the regularity
hypothesis discharged. -/
theorem waveFEM_rate_tr_nonvacuous_cube {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) {T : ℝ}
    (hT0 : 0 < T) :
    (∀ t, (waveTangential T).u t ≠ 0) ∧
    (∀ t s L, ¬ IsCsFormMin s 1 L (((waveTangential T).u t 0 : U1) : W1)) ∧
    ∃ (K : ℝ) (sh : (N : ℕ) → Feec.BGG.DiscreteSolution (cubeWave hT hB N) T
        (cubeSource hT hB N fun t => t • waveTangentialSrc)),
      ∀ N, ∀ t ∈ Icc 0 T,
        √(‖(waveTangential T).σ t - (sh N).σ t‖ ^ 2 +
          ‖(waveTangential T).u t - (sh N).u t‖ ^ 2 +
          ‖(waveTangential T).M t - (sh N).M t‖ ^ 2 +
          ‖(waveTangential T).ρ t - (sh N).ρ t‖ ^ 2) ≤ K * (1 + t) * meshSize N :=
  waveFEM_rate_tr_nonvacuous hT hB curlPotential hT0

end Feec.EinsteinBianchi.WaveFEM
