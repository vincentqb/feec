module

public import Feec.Models.Cube.RegularDecomposition
public import Feec.Physics.EinsteinBianchi.StaticFEM
public import Feec.Physics.EinsteinBianchi.WaveFEM

/-!
# The Einstein–Bianchi system with weak symmetries on the cube, unconditionally

The regularity hypothesis `curl H̊(curl, Q) = curl S⁰ H̊¹(Q; ℝ³)`
(`Feec.Models.Cube.WeakSymmetry.CurlPotential`) is a theorem
(`Feec.Models.Cube.WeakSymmetry.curlPotential`, `Feec.Models.Cube.RegularDecomposition`), so
the main theorems of `Feec.Physics.EinsteinBianchi.StaticFEM` and
`Feec.Physics.EinsteinBianchi.WaveFEM` hold without it. This file states them with the
hypothesis discharged.

## Main results

* `StaticFEM.staticFEM_cube`: [QuennevilleBelair2015], §5.3, Props 5.2, 5.4, Thm 5.5 on the cube
  with the elements of Table 5.1 (well-posedness, (5.4), discrete well-posedness, `O(h)` rates);
* `StaticFEM.staticFEM_nonvacuous_cube`, `StaticFEM.staticFEM_nonvacuous_coupled_cube`: the
  manufactured solutions and the convergence of their discrete solutions;
* `WaveFEM.bgg_wave_existsUnique_cube`: existence and uniqueness for the Hodge wave equation of
  (5.1) on the cube (Thm 4.6 for (4.16));
* `WaveFEM.waveFEM_cube`: the semi-discrete method (6.5) of Table 6.1 ((5.4), well-posedness,
  energy stability, `O(h)` convergence), and `WaveFEM.waveFEM_nonvacuous_cube`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3 (Props 5.2, 5.4, Thm 5.5), §6.3 ((6.5), Table 6.1), Thm 4.6
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [R. Hiptmair, J. Xu, *Nodal auxiliary space preconditioning in H(curl) and H(div) spaces*][HiptmairXu2007],
  §3 (regular decomposition)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.StaticFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

set_option maxHeartbeats 1000000 in
/-- **The time-independent Einstein–Bianchi system with weak symmetries on the cube: well-posedness
and convergence of the finite element method of Table 5.1, unconditionally**
([QuennevilleBelair2015], §5.3, Props 5.2, 5.4, Thm 5.5): `staticFEM` with the regularity
hypothesis discharged by `curlPotential`. -/
theorem staticFEM_cube :
    ((∀ f : Wv W1, ∃! xl : Feec.BGG.Xsp V0 Vt0 Vt1 × bggHilb.Wcheck,
        bggHilb.IsSaddle f xl.1 xl.2) ∧
      ∃ C', ∀ (f : Wv W1) (x : Feec.BGG.Xsp V0 Vt0 Vt1) (l : bggHilb.Wcheck),
        bggHilb.IsSaddle f x l → ‖x‖ + ‖l‖ ≤ C' * ‖f‖) ∧
    ∃ (p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      (∀ N, (cubeFEM hT hB N).Compatible) ∧ (∀ N, (cubeFEM hT hB N).Bounded (2 * C)) ∧
      (∀ (N : ℕ) (F : Wv U1 →ₗ[ℝ] ℝ),
        ∃! x : (cubeFEM hT hB N).V0h × (cubeFEM hT hB N).Vt0h × (cubeFEM hT hB N).Vt1h ×
            (cubeFEM hT hB N).V1h,
          (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
            ⟪(x.1 : U0), τ⟫ - ⟪(x.2.2.1 : Wv U1), bggSegment.dt0 ψ⟫
              - ⟪(x.2.2.2 : U1), bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) ∧
          (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 x.2.1, v⟫ +
            ⟪(cubeFEM hT hB N).S1h x.2.2.1, (cubeFEM hT hB N).S1h v⟫ +
              ⟪bggSegment.dt1 x.2.2.1, bggSegment.dt1 v⟫ = F v) ∧
          (∀ μ ∈ (cubeFEM hT hB N).V1h,
            ⟪bggSegment.d0 x.1 - (cubeFEM hT hB N).S0h x.2.1, μ⟫ = 0)) ∧
      (∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
        {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
        (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
          ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
        (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
          ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
        bggSegment.d0 σ = bggSegment.S0 φ →
        IsCsFormMin 0 0 L (σ : W0) → (∀ a, IsCsFormMin 0 0 L (φ a : W0)) →
        (∀ a, IsCsFormMin 0 1 L (u a : W1)) → ‖lam‖ ≤ L →
        IsCsFormMin 0 2 L (bggSegment.S1 u) →
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
        IsCsFormMin 0 0 L ((graphDomₗ (Feec.BGG.pσ V0 Vt0 Vt1 x) : U0) : W0) →
        (∀ a, IsCsFormMin 0 0 L ((rp (Feec.BGG.pφ V0 Vt0 Vt1 x) a : U0) : W0)) →
        (∀ a, IsCsFormMin 0 1 L ((rp1 (Feec.BGG.pu V0 Vt0 Vt1 x) a : U1) : W1)) → ‖lam‖ ≤ L →
        IsCsFormMin 0 2 L (bggSegment.S1 (rp1 (Feec.BGG.pu V0 Vt0 Vt1 x))) →
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
  staticFEM curlPotential

/-- **Non-vacuity of `staticFEM_cube`**: `staticFEM_nonvacuous` with the regularity hypothesis
discharged; the discrete solutions of the manufactured problem converge at rate `h_N` and are
nonzero for all large `N`. -/
theorem staticFEM_nonvacuous_cube {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) :
    (∀ᶠ N in atTop, (cubeFEM hT hB N).V0h ≠ ⊥ ∧ (cubeFEM hT hB N).V1h ≠ ⊥ ∧
      (cubeFEM hT hB N).Vt0h ≠ ⊥ ∧ (cubeFEM hT hB N).Vt1h ≠ ⊥) ∧
    manufacturedU ≠ 0 ∧
    (∀ τ ψ, ⟪(0 : U0), τ⟫ - ⟪manufacturedU, bggSegment.dt0 ψ⟫ -
      ⟪(0 : W1), ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) ∧
    (∀ v, ⟪bggSegment.dt0 (0 : Wv U0), v⟫ + ⟪bggSegment.S1 manufacturedU, bggSegment.S1 v⟫ +
      ⟪bggSegment.dt1 manufacturedU, bggSegment.dt1 v⟫ = manufacturedDatum v) ∧
    bggSegment.d0 (0 : U0) = bggSegment.S0 (0 : Wv U0) ∧
    (∃ L, 0 ≤ L ∧
      IsCsFormMin 0 0 L ((0 : U0) : W0) ∧ (∀ a, IsCsFormMin 0 0 L (((0 : Wv U0) a : U0) : W0)) ∧
      (∀ a, IsCsFormMin 0 1 L ((manufacturedU a : U1) : W1)) ∧ IsCsFormMin 0 1 L (0 : W1) ∧
      IsCsFormMin 0 2 L (bggSegment.S1 manufacturedU)) ∧
    (∃ (K : ℝ) (uh : ℕ → Wv U1), (∀ N, uh N ∈ (cubeFEM hT hB N).Vt1h ∧
      ∃ (σh : U0) (φh : Wv U0) (lh : U1), σh ∈ (cubeFEM hT hB N).V0h ∧
        φh ∈ (cubeFEM hT hB N).Vt0h ∧
        (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
          ⟪σh, τ⟫ - ⟪uh N, bggSegment.dt0 ψ⟫ -
            ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) ∧
        (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
          ⟪(cubeFEM hT hB N).S1h (uh N), (cubeFEM hT hB N).S1h v⟫ +
            ⟪bggSegment.dt1 (uh N), bggSegment.dt1 v⟫ = manufacturedDatum v) ∧
        (∀ μ ∈ (cubeFEM hT hB N).V1h,
          ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) ∧
        (cubeFEM hT hB N).gnSq (manufacturedU - uh N) ≤ (K * meshSize N) ^ 2) ∧
      ∀ᶠ N in atTop, uh N ≠ 0) :=
  let h := staticFEM_nonvacuous hT hB
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2 curlPotential⟩

set_option maxHeartbeats 1000000 in
/-- **Non-vacuity of `staticFEM_cube` with every unknown coupled**: `staticFEM_nonvacuous_coupled`
with the regularity hypothesis discharged. -/
theorem staticFEM_nonvacuous_coupled_cube {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) :
    coupledσ ≠ 0 ∧ coupledφ ≠ 0 ∧ coupledu ≠ 0 ∧ coupledMult ≠ 0 ∧
    (∀ τ ψ, ⟪coupledσ, τ⟫ - ⟪coupledu, bggSegment.dt0 ψ⟫ -
      ⟪coupledMult, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) ∧
    (∀ v, ⟪bggSegment.dt0 coupledφ, v⟫ + ⟪bggSegment.S1 coupledu, bggSegment.S1 v⟫ +
      ⟪bggSegment.dt1 coupledu, bggSegment.dt1 v⟫ = coupledDatum v) ∧
    bggSegment.d0 coupledσ = bggSegment.S0 coupledφ ∧
    (∃ L, 0 ≤ L ∧ IsCsFormMin 0 0 L (coupledσ : W0) ∧ (∀ a, IsCsFormMin 0 0 L (coupledφ a : W0)) ∧
      (∀ a, IsCsFormMin 0 1 L (coupledu a : W1)) ∧ ‖coupledMult‖ ≤ L ∧
      IsCsFormMin 0 2 L (bggSegment.S1 coupledu)) ∧
    (∃ (K : ℝ) (σh : ℕ → U0) (φh : ℕ → Wv U0) (uh : ℕ → Wv U1),
      (∀ N, σh N ∈ (cubeFEM hT hB N).V0h ∧ φh N ∈ (cubeFEM hT hB N).Vt0h ∧
        uh N ∈ (cubeFEM hT hB N).Vt1h ∧ ∃ lh : U1,
        (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
          ⟪σh N, τ⟫ - ⟪uh N, bggSegment.dt0 ψ⟫ -
            ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) ∧
        (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 (φh N), v⟫ +
          ⟪(cubeFEM hT hB N).S1h (uh N), (cubeFEM hT hB N).S1h v⟫ +
            ⟪bggSegment.dt1 (uh N), bggSegment.dt1 v⟫ = coupledDatum v) ∧
        (∀ μ ∈ (cubeFEM hT hB N).V1h,
          ⟪bggSegment.d0 (σh N) - (cubeFEM hT hB N).S0h (φh N), μ⟫ = 0) ∧
        Feec.BGG.graphSq bggSegment.d0 (coupledσ - σh N) +
          Feec.BGG.graphSq bggSegment.dt0 (coupledφ - φh N) +
          (cubeFEM hT hB N).gnSq (coupledu - uh N) ≤ (K * meshSize N) ^ 2) ∧
      ∀ᶠ N in atTop, σh N ≠ 0 ∧ φh N ≠ 0 ∧ uh N ≠ 0) :=
  let h := staticFEM_nonvacuous_coupled hT hB
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2 curlPotential⟩

end Feec.EinsteinBianchi.StaticFEM

namespace Feec.EinsteinBianchi.WaveFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

section Stone

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **Existence and uniqueness for the Hodge wave equation of (5.1) on the cube, unconditionally**
([QuennevilleBelair2015], Thm 4.6 for the complex (4.16); Stone's theorem):
`bgg_wave_existsUnique` with the regularity hypothesis discharged. -/
theorem bgg_wave_existsUnique_cube
    {U₀ : PiLp 2 (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2)))}
    (hU₀ : U₀ ∈ (bggHilb.toHilbertComplex bggHilb_hyps bggS0_injective).wave.domain) {a b : ℝ}
    {F : ℝ → PiLp 2 (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2)))}
    (hF : Evolution.ForcingClass.admissible
      (bggHilb.toHilbertComplex bggHilb_hyps bggS0_injective).wave a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution
        (bggHilb.toHilbertComplex bggHilb_hyps bggS0_injective).wave (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution
        (bggHilb.toHilbertComplex bggHilb_hyps bggS0_injective).wave (Icc a b) F V →
          EqOn V U (Icc a b) :=
  bgg_wave_existsUnique curlPotential hU₀ hF

end Stone

set_option maxHeartbeats 4000000 in
/-- **The Einstein–Bianchi wave system with weak symmetries on the cube: the semi-discrete method
(6.5) of Table 6.1, unconditionally** ([QuennevilleBelair2015], §6.3): `waveFEM` with the
regularity hypothesis discharged. -/
theorem waveFEM_cube :
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
      ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_ : 0 < T) {f : ℝ → Wv W1}
        (_ : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
        0 ≤ L →
        (∀ t ∈ Icc 0 T, IsSmoothState L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
          IsSmoothState L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
        (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
        ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
          (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
            (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
              (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
              (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
                (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
          ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
            ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N :=
  waveFEM curlPotential

set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `waveFEM_cube`**: `waveFEM_nonvacuous` with the regularity hypothesis
discharged. -/
theorem waveFEM_nonvacuous_cube {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) {T : ℝ}
    (hT0 : 0 < T) :
    (∀ t ∈ Ioc 0 T, (waveManufactured T).σ t ≠ 0 ∧ (waveManufactured T).φ t ≠ 0) ∧
    (∀ t, (waveManufactured T).u t ≠ 0) ∧ coupledMult ≠ 0 ∧
    ∃ (K : ℝ) (sh : (N : ℕ) → Feec.BGG.DiscreteSolution (cubeWave hT hB N) T
        (cubeSource hT hB N fun t => incl1 (t • (bggSegment.dt0 coupledφ + waveCurlCurlU)))),
      (∀ N, ∀ t ∈ Icc 0 T,
        √(‖(waveManufactured T).σ t - (sh N).σ t‖ ^ 2 +
          ‖(waveManufactured T).u t - (sh N).u t‖ ^ 2 +
          ‖(waveManufactured T).M t - (sh N).M t‖ ^ 2 +
          ‖(waveManufactured T).ρ t - (sh N).ρ t‖ ^ 2) ≤ K * (1 + t) * meshSize N) ∧
      ∀ t ∈ Ioc 0 T, ∀ᶠ N in atTop, ((sh N).σ t : U0) ≠ 0 :=
  waveFEM_nonvacuous hT hB curlPotential hT0

end Feec.EinsteinBianchi.WaveFEM
