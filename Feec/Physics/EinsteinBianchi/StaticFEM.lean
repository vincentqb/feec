module

public import Feec.Models.Cube.WeakSymmetryFEM

/-!
# The time-independent Einstein–Bianchi system with weak symmetries: finite elements on the cube

The time-independent EB system with weakly imposed symmetry, [QuennevilleBelair2015], §5.3,
(5.3), on `Q = (0, ½)³` with the thesis' boundary conditions, discretized by the elements of
Table 5.1 on the level-`(N + 1)` Freudenthal meshes (`h_N = 1 / (2 (N + 1))`):

* top row `P₁Λ̊⁰ → P₁⁻Λ̊¹ → P₁⁻Λ̊²` (Lagrange, Nédélec, Raviart–Thomas), bottom row
  `P₂Λ̊⁰ ⊗ ℝ³ → P₂⁻Λ̊¹ ⊗ ℝ³ → P₁Λ̊² ⊗ ℝ³`, all with vanishing boundary DOFs;
* `S₀,ₕ = π¹S⁰`, `S₁,ₕ = π²S¹` with the **smoothed** cochain projections `π = J⁻¹ Π_h R` of one
  common smoother for both rows (`Feec.Models.Cube.WeakSymmetry.cubeFEM`); the canonical
  projections of the thesis are not bounded on `L²` (on the discrete spaces both are defined,
  and Props 5.7–5.9 for the canonical maps are in `Feec.Models.Cube.WeakSymmetryEstimates`).

**Main theorem** (`staticFEM`, under the regularity hypothesis `CurlPotential`, see below):
the continuous problem (5.3) is well posed for every `f` (thesis Prop 5.2); for every `N` the
discretization satisfies the surjectivity hypothesis (5.4) and uniform projection bounds; the
discrete problem (5.6), i.e. the thesis' (5.7) with `S_h = πS` in place of `Π_h S`, has a unique
solution for every datum (thesis Prop 5.4); and for exact solutions with `σ, φ, u, S¹u` of class
`C²`, vanishing outside `Q`, with first derivatives bounded by `L`, and `‖λ‖ ≤ L`,
`‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N)²` with `K` independent of `N`
(thesis Thm 5.5, corrected). The same rate holds for the solution of Prop 5.2 itself whenever its
multiplier lies in `L²Λ¹(Q)` (`l = jW λ`), through `isSaddle_jW_domain_eqs`.

**Status of the thesis statements used.**
* Prop 5.7 (5.4): proved, in the corrected (moment-DOF) form, for the canonical maps
  (`Feec.FiniteElement.PolySeq.bggS0h_tensorInterp`) and transferred to the smoothed projections
  of one smoother (`Feec.Models.Cube.WeakSymmetry.cubeFEM_compatible`).
* Prop 5.8: corrected (the `ℓ¹` DOF sums are replaced by local `ℓ²`/`L²` scaling,
  `Feec.Models.Cube.WeakSymmetry.norm_glue_bggS0h_le`, `norm_glue_bggS1h_le`); `S₁ = 2 vskw`
  (the normalization of the anticommutation `d S = −S d`).
* Prop 5.9(1): proved (`norm_sub_glue_bggS0h_le`), and transferred to `π¹`
  (`cubeFEM_happ0`).
* Prop 5.9(2): **refuted** (`exists_interpolationError_ge`, also for every projection onto
  the Raviart–Thomas spaces, `not_exists_bestApprox_bound`). Thm 5.5 therefore applies with the
  weak consistency `|⟪S¹u, (S₁ − S₁,ₕ)v⟫| ≤ C h ‖v‖_V` in place of the false hypothesis
  (`Feec.BGG.Discrete.error_estimate_of_weakConsistency`), which follows from regular `H̊¹`
  potentials and the `H̊¹` approximation of the smoothed projections
  (`Feec.Models.Cube.WeakSymmetry.cubeFEMReg`,
  `Feec.BGG.Discrete.weakConsistency_of_regularPotential_of_bound`).
* Thm 5.5: proved for Table 5.1 on the cube, with `λ ∈ L²` (the thesis' `λ ∈ H⁻¹(div)` does not
  give the bound) and the `h`-dependent norm `‖·‖_{Γₕ}`.

**The remaining hypothesis.** `CurlPotential` (`curl H̊(curl) = curl S⁰ H̊¹(Q; ℝ³)`, the regular
decomposition of [Hiptmair2002], Lemma 2.4, [HiptmairXu2007], §3) is the one explicit hypothesis;
it is not in Mathlib (`Feec.Models.Cube.WeakSymmetry.CurlPotential`: equivalent to the closedness
of `curl S⁰ H̊¹(Q; ℝ³)`, true on test fields). It is now proved
(`Feec.Models.Cube.WeakSymmetry.curlPotential` in `Feec.Models.Cube.RegularDecomposition`), and the
theorem of this file with it discharged is `staticFEM_cube` in
`Feec.Physics.EinsteinBianchi.Unconditional`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, (5.3), (5.6), (5.7), Table 5.1, Props 5.2, 5.4, 5.7–5.9, Thm 5.5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [R. Hiptmair, J. Xu, *Nodal auxiliary space preconditioning in H(curl) and H(div) spaces*][HiptmairXu2007],
  §3 (regular decomposition)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Filter

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.StaticFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

set_option maxHeartbeats 1000000 in
/-- **The time-independent Einstein–Bianchi system with weak symmetries on the cube: well-posedness
and convergence of the finite element method of Table 5.1** ([QuennevilleBelair2015], §5.3,
Props 5.2, 5.4, Thm 5.5), under the regularity hypothesis `CurlPotential`. There are smoothing
parameters `p` (one smoother for both rows) and a constant `C` such that:
1. (5.3) is well posed for every `f` (`bggHilb.IsSaddle`, with a stability bound);
2. for every `N` the discretization `cubeFEM hT hB N` satisfies (5.4) (`Compatible`) and the
   projection bounds `Bounded (2C)`, `C` independent of `N`;
3. for every `N` and every datum `F` the discrete problem (5.6) (thesis (5.7) with `S_h = πS`)
   has exactly one solution;
4. there is `K`, independent of `N` and of the solution, such that for every exact solution
   `(σ, φ, u, λ)` of (5.3) with `λ ∈ L²`, `‖λ‖ ≤ L`, whose components and `S¹u` are `C²` forms
   vanishing outside `Q` with first derivatives bounded by `L`, and every discrete solution,
   `‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N)²`;
5. the same for the solution `(x, l)` of item 1 (right-hand side `f`, discrete datum
   `F v = ⟪f, v⟫`) whenever its multiplier lies in `L²Λ¹(Q)`, `l = jW λ`: the graph-space
   components of `x`, read in the domains, are the exact solution of item 4. -/
theorem staticFEM (hR : CurlPotential) :
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
            (K * L * meshSize N) ^ 2 := by
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrows := tableRows_uniform_cochainProjection
  obtain ⟨p, C, hT, hB, -⟩ := hrows
  exact ⟨bgg_existsUnique_isSaddle hR, p, C, hT, hB, cubeFEM_compatible hT hB,
    cubeFEM_bounded hT hB, cubeFEM_existsUnique hT hB hCR.1 hCR.2,
    cubeFEM_rate_C2 hT hB hCR.1 hCR.2, cubeFEM_rate_isSaddle hT hB hCR.1 hCR.2⟩

end Feec.EinsteinBianchi.StaticFEM
