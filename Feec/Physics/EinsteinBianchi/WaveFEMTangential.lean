module

public import Feec.Physics.EinsteinBianchi.WaveFEM
public import Feec.Physics.EinsteinBianchi.StaticFEM
public import Feec.Models.Cube.WeakSymmetryTangentialRate

/-!
# The Einstein–Bianchi system on the cube: rates for solutions with vanishing tangential traces

The headline theorems `Feec.EinsteinBianchi.StaticFEM.staticFEM` (items 4, 5: thesis Thm 5.5 with
the elements of Table 5.1) and `Feec.EinsteinBianchi.WaveFEM.waveFEM` (item 5: the `O(h)` rate of
(6.5)) assume solutions that are `C²` and vanish outside `Q` (flat at `∂Q`). This module restates
them, under the same regularity hypothesis `CurlPotential` (through its constant; it is proved, and
`Feec.Physics.EinsteinBianchi.WaveFEMTangentialCube` states the results without it), for solutions
that are `C²` **up to the boundary** with vanishing tangential traces on `∂Q`
(`Feec.Models.Cube.FEM.IsCsFormTr`, `Feec.Models.Cube.WeakSymmetry.IsSmoothStateTr`), the boundary
conditions of the discrete spaces:

* **`staticFEM_rate_tr`**: Thm 5.5 (`cubeFEM_rate_tr`) and its form for the solution of Prop 5.2
  (`cubeFEM_rate_isSaddle_tr`);
* **`waveFEM_rate_tr`**: items 1–4 of `waveFEM` unchanged, item 5 on `IsSmoothStateTr`
  (`cubeWave_rate_tr`), and the `O(h)` rate of the elliptic projection (6.4) on the cube
  (`cubeFEM_ellipticProjection_rate_tr`);
* non-vacuity beyond the flat class: `staticFEM_rate_tr_nonvacuous` (the solution
  `tangentialManufactured_solution`, whose `u` has a nonzero normal component on `∂Q`),
  `staticFEM_rate_tr_nonvacuous_combined` (the solution `combinedManufactured_solution`, with
  `σ, φ, λ ≠ 0` and non-flat `u`) and
  `waveFEM_rate_tr_nonvacuous` (the classical solution `waveTangential T` of (6.2)).

"`C²` up to `∂Q`" means the restriction to `Q` of a `C²` field on `ℝ³` (equivalent through an
extension theorem for the cube, which is not formalized). The class of `S¹u` is derived from that
of `u` (`exists_isCsFormTr_segS1`). The states `M`, `ρ` are required to have vanishing tangential
traces as well: the discrete `Mₕ, ρₕ` have vanishing boundary DOFs, so without that condition the
error is expected to be of order `h^{1/2}` at `t = 0` already (boundary-layer argument, not
formalized; see `Feec.Models.Cube.WeakSymmetryTangentialRate`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3 (Table 5.1, Thm 5.5), §6.2 ((6.4), Prop 6.2), §6.3 ((6.5), Table 6.1)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.StaticFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

set_option maxHeartbeats 1000000 in
/-- **Thesis Thm 5.5 on the cube with the elements of Table 5.1 for solutions with vanishing
tangential traces**, under the regularity hypothesis: there are smoothing parameters `p` (one
smoother for both rows) and `C` such that
1. there is `K`, independent of `N` and of the solution, such that for every exact solution
   `(σ, φ, u, λ)` of (5.3) with `λ ∈ L²`, `‖λ‖ ≤ L`, whose components `σ, φ, u` are `C²` up to
   `∂Q` with vanishing tangential traces (`IsCsFormTr 0`, bound `L` on the values and first
   derivatives) and every discrete solution of (5.6),
   `‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N)²`;
2. the same for the solution `x` of Prop 5.2 (`bggHilb.IsSaddle`) with multiplier in `L²Λ¹(Q)`. -/
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

set_option maxHeartbeats 1000000 in
/-- **Non-vacuity of `staticFEM_rate_tr` beyond flat data** (for any common smoother): the field
`tangentialU` (first row `(sin 2πy₁ sin 2πy₂) dx₀`) is nonzero and not flat (its first row is in
no class `IsCsFormMin`: its normal component does not vanish on `{y₀ = 0}`);
`(σ, φ, u, λ) = (0, 0, tangentialU, 0)` with datum `tangentialDatum` solves (5.3) with the
hypotheses of `cubeFEM_rate_tr`; under the regularity hypothesis the discrete solutions `uₕ` of
(5.6) converge to it at rate `h_N` in `‖·‖_{Γₕ}`. -/
theorem staticFEM_rate_tr_nonvacuous {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) :
    tangentialU ≠ 0 ∧ (∀ s L, ¬ IsCsFormMin s 1 L ((tangentialU 0 : U1) : W1)) ∧
    (CurlPotential → ∃ (K : ℝ) (uh : ℕ → Wv U1), ∀ N, uh N ∈ (cubeFEM hT hB N).Vt1h ∧
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
        (cubeFEM hT hB N).gnSq (tangentialU - uh N) ≤ (K * meshSize N) ^ 2) := by
  refine ⟨tangentialU_ne_zero, not_isCsFormMin_tangentialU0, fun hR => ?_⟩
  obtain ⟨c1, c2, c3, L, hL0, hσ, hφ, hu, hlam⟩ := tangentialManufactured_solution
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  obtain ⟨K, hK0, hK⟩ := cubeFEM_rate_tr hT hB hCR.1 hCR.2
  have hsol := fun N => (cubeFEM_existsUnique hT hB hCR.1 hCR.2 N tangentialDatum).exists
  choose x hx using hsol
  have hbound : ∀ N, Feec.BGG.graphSq bggSegment.d0 ((0 : U0) - (x N).1) +
      Feec.BGG.graphSq bggSegment.dt0 ((0 : Wv U0) - (x N).2.1) +
      (cubeFEM hT hB N).gnSq (tangentialU - (x N).2.2.1) ≤ (K * L * meshSize N) ^ 2 := fun N =>
    hK N hL0 c1 c2 c3 hσ hφ hu hlam (x N).1.2 (x N).2.1.2 (x N).2.2.1.2 (hx N).1
      (hx N).2.1 (hx N).2.2
  refine ⟨K * L, fun N => (x N).2.2.1, fun N => ⟨(x N).2.2.1.2, (x N).1, (x N).2.1, (x N).2.2.2,
    (x N).1.2, (x N).2.1.2, (hx N).1, (hx N).2.1, (hx N).2.2, ?_⟩⟩
  exact le_trans (le_add_of_nonneg_left (add_nonneg (Feec.BGG.graphSq_nonneg _ _)
    (Feec.BGG.graphSq_nonneg _ _))) (hbound N)

set_option maxHeartbeats 2000000 in
/-- **Non-vacuity of `staticFEM_rate_tr` with every unknown nonzero and non-flat `u`**: the
solution `combinedManufactured_solution` (`σ, φ, λ ≠ 0`, `u = coupledu + tangentialU`, not in
any `IsCsFormMin 0 1 L`) of (5.3) with datum `coupledDatum + tangentialDatum`; under the
regularity hypothesis the discrete solutions of (5.6) converge to it at rate `h_N` in
`‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ}`. -/
theorem staticFEM_rate_tr_nonvacuous_combined {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)}
    {C : ℝ} (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) :
    coupledσ ≠ 0 ∧ coupledφ ≠ 0 ∧ coupledMult ≠ 0 ∧
    (∀ L, ¬ IsCsFormMin 0 1 L ((((coupledu + tangentialU : Wv U1)) 0 : U1) : W1)) ∧
    (CurlPotential → ∃ K : ℝ, ∀ N, ∃ (σh : U0) (φh : Wv U0) (uh : Wv U1) (lh : U1),
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
          (cubeFEM hT hB N).gnSq ((coupledu + tangentialU) - uh) ≤ (K * meshSize N) ^ 2) := by
  have hsol0 := combinedManufactured_solution
  obtain ⟨hσ0, hφ0, hM0, hnf, c1, c2, c3, L, hL0, hσ, hφ, hu, hlam⟩ := hsol0
  refine ⟨hσ0, hφ0, hM0, hnf, fun hR => ?_⟩
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrate := cubeFEM_rate_tr hT hB hCR.1 hCR.2
  obtain ⟨K, hK⟩ := hrate
  have hsol := fun N =>
    (cubeFEM_existsUnique hT hB hCR.1 hCR.2 N (coupledDatum + tangentialDatum)).exists
  choose x hx using hsol
  refine ⟨K * L, fun N => ⟨(x N).1, (x N).2.1, (x N).2.2.1, (x N).2.2.2, (x N).1.2,
    (x N).2.1.2, (x N).2.2.1.2, (hx N).1, (hx N).2.1, (hx N).2.2, ?_⟩⟩
  have hb := hK.2 N hL0 c1 c2 c3 hσ hφ hu hlam (x N).1.2 (x N).2.1.2 (x N).2.2.1.2 (hx N).1
    (hx N).2.1 (hx N).2.2
  exact hb.trans_eq (by ring)

end Feec.EinsteinBianchi.StaticFEM

namespace Feec.EinsteinBianchi.WaveFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

set_option maxHeartbeats 4000000 in
/-- **`waveFEM` for solutions with vanishing tangential traces** ([QuennevilleBelair2015], §6.3),
under the regularity hypothesis `CurlPotential`: for one smoother `p` and constant `C`, items 1–4
of `waveFEM` ((5.4) and uniform bounds; `grad` injective and `S₀,ₕ` onto; corrected Prop 6.2;
energy stability) and
5. (`O(h)` convergence of (6.5)) there is `K` such that for every classical solution of (6.2)
   whose states and time derivatives are `C²` up to `∂Q` with vanishing tangential traces
   (`IsSmoothStateTr L`: no flatness, no condition on the normal components) and `L²`-bounded
   multiplier, the solution of (6.5) from the elliptic projection (6.4) of the exact initial state
   satisfies `‖(σ, u, M, ρ)(t) − (σₕ, uₕ, Mₕ, ρₕ)(t)‖ ≤ K L (1 + t) h_N` on `[0,T]`;
6. (the `O(h)` rate of (6.4)) there is `K'` such that every solution `x` of the elliptic projection
   (6.4) of a state `(σ, φ, u, M, ρ)` in `IsSmoothStateTr L` with `dσ = S₀φ` and
   `|ℓ μ| ≤ L ‖μ‖` has energy error `≤ K' L h_N`. -/
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
/-- **Non-vacuity of `waveFEM_rate_tr` beyond flat data** (for any common smoother): the classical
solution `waveTangential T` of (6.2) (`u(t) = tangentialU`, `ρ(t) = t curl u`, `M = 0`, source
`t (curl* curl u, 0, 0)`) has `u(t) ≠ 0` not flat (no class `IsCsFormMin`), meets every hypothesis
of item 5, and under `CurlPotential` the solutions of (6.5) from the elliptic projection of its
initial state converge at rate `h_N`. -/
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
