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

**Non-vacuity** (`staticFEM_nonvacuous`): the discrete spaces are nonzero for all large `N`
(unconditionally), and there is a nontrivial smooth exact solution (manufactured data:
`u` = `dᵗ(f dx₀ ∧ dx₁)` in the first row, `σ = φ = λ = 0`) satisfying every hypothesis of the
error estimate, whose discrete solutions are nonzero for large `N`; and
(`staticFEM_nonvacuous_coupled`) a smooth exact solution with all four unknowns nonzero
(`λ = dg`, `σ = dᵗλ`, `φₐ = ∂ₐσ`, `uₐ = −g dxₐ`, `g` a bump in `Q`), so that the multiplier and the
constraint `dσ = S⁰φ` are exercised, whose discrete `σₕ, φₕ, uₕ` converge at rate `h_N` and are
nonzero for large `N`.

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
theorems of this file with it discharged are `staticFEM_cube`, `staticFEM_nonvacuous_cube` and
`staticFEM_nonvacuous_coupled_cube` in `Feec.Physics.EinsteinBianchi.Unconditional`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, (5.3), (5.6), (5.7), Table 5.1, Props 5.2, 5.4, 5.7–5.9, Thm 5.5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothed projections)
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

/-- **Non-vacuity of `staticFEM`** (for any common smoother `p` of the two rows):
1. the discrete spaces `Vₕ⁰, Vₕ¹, Ṽₕ⁰, Ṽₕ¹` are nonzero for all large `N` (unconditionally);
2. the manufactured field `manufacturedU` (first row `dᵗ(f dx₀ ∧ dx₁)`, `f` a bump in `Q`) is
   nonzero, and `(σ, φ, u, λ) = (0, 0, manufacturedU, 0)` with the datum `manufacturedDatum`
   solves (5.3) with all the `C²` hypotheses of
   the error estimate;
3. under the regularity hypothesis, the discrete solutions `uₕ` of (5.6) with datum
   `manufacturedDatum` converge
   to `manufacturedU` at rate `h_N` in `‖·‖_{Γₕ}` and are nonzero for all large `N`. -/
theorem staticFEM_nonvacuous {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
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
    (CurlPotential → ∃ (K : ℝ) (uh : ℕ → Wv U1), (∀ N, uh N ∈ (cubeFEM hT hB N).Vt1h ∧
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
      ∀ᶠ N in atTop, uh N ≠ 0) := by
  have hman := exists_manufactured_solution
  refine ⟨cubeFEM_ne_bot hT hB, manufacturedU_ne_zero, manufactured_c1, manufactured_c2,
    manufactured_c3,
    hman, fun hR => ?_⟩
  obtain ⟨L, hLm⟩ := hman
  have hL0 := hLm.1
  have hm := hLm.2
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrate := cubeFEM_rate_C2 hT hB hCR.1 hCR.2
  obtain ⟨K, hK⟩ := hrate
  have hsol := fun N => (cubeFEM_existsUnique hT hB hCR.1 hCR.2 N manufacturedDatum).exists
  choose x hx using hsol
  have hbound : ∀ N, Feec.BGG.graphSq bggSegment.d0 ((0 : U0) - (x N).1) +
      Feec.BGG.graphSq bggSegment.dt0 ((0 : Wv U0) - (x N).2.1) +
      (cubeFEM hT hB N).gnSq (manufacturedU - (x N).2.2.1) ≤ (K * L * meshSize N) ^ 2 := fun N =>
    hK.2 N hL0 manufactured_c1 manufactured_c2 manufactured_c3 hm.1 hm.2.1 hm.2.2.1
      (by rw [norm_zero]; exact hL0) hm.2.2.2.2 (x N).1.2 (x N).2.1.2 (x N).2.2.1.2 (hx N).1
      (hx N).2.1 (hx N).2.2
  have hgn : ∀ N, (cubeFEM hT hB N).gnSq (manufacturedU - (x N).2.2.1) ≤ (K * L * meshSize N) ^ 2 :=
    fun N => le_trans (le_add_of_nonneg_left (add_nonneg (Feec.BGG.graphSq_nonneg _ _)
      (Feec.BGG.graphSq_nonneg _ _))) (hbound N)
  refine ⟨K * L, fun N => (x N).2.2.1, fun N => ⟨(x N).2.2.1.2, (x N).1, (x N).2.1, (x N).2.2.2,
    (x N).1.2, (x N).2.1.2, (hx N).1, (hx N).2.1, (hx N).2.2, hgn N⟩, ?_⟩
  refine eventually_ne_zero_of_le (A := K * L) (B := 1) manufacturedU_ne_zero fun N => ?_
  have h1 : ‖manufacturedU - (x N).2.2.1‖ ^ 2 ≤ (K * L * meshSize N) ^ 2 := by
    refine le_trans ?_ (hgn N)
    unfold Feec.BGG.Discrete.gnSq
    nlinarith [sq_nonneg ‖(cubeFEM hT hB N).S1h (manufacturedU - (x N).2.2.1)‖,
      sq_nonneg ‖bggSegment.dt1 (manufacturedU - (x N).2.2.1)‖]
  have hKL : 0 ≤ K * L * meshSize N := mul_nonneg (mul_nonneg hK.1 hL0) (meshSize_pos N).le
  rw [mul_one]
  exact le_of_pow_le_pow_left₀ two_ne_zero hKL h1

set_option maxHeartbeats 1000000 in
/-- **Non-vacuity of `staticFEM` with every unknown coupled** (for any common smoother `p`): the
manufactured solution `λ = dg`, `σ = dᵗλ`, `φₐ = ∂ₐσ`, `uₐ = −g dxₐ` (`g` a bump in `Q`) has all
four unknowns nonzero, solves (5.3) with the datum `coupledDatum` and meets every hypothesis of item 4
of `staticFEM`; under the regularity hypothesis its discrete solutions `(σₕ, φₕ, uₕ)` converge at
rate `h_N` and `σₕ, φₕ, uₕ` are nonzero for all large `N`. -/
theorem staticFEM_nonvacuous_coupled {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
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
    (CurlPotential → ∃ (K : ℝ) (σh : ℕ → U0) (φh : ℕ → Wv U0) (uh : ℕ → Wv U1),
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
      ∀ᶠ N in atTop, σh N ≠ 0 ∧ φh N ≠ 0 ∧ uh N ≠ 0) := by
  have hman := exists_coupled_manufactured_solution
  obtain ⟨L, hL0, hσ0, hφ0, hu0, hm0, c1, c2, c3, hσ, hφ, hu, hlam, hSu⟩ := hman
  refine ⟨hσ0, hφ0, hu0, hm0, c1, c2, c3, ⟨L, hL0, hσ, hφ, hu, hlam, hSu⟩, fun hR => ?_⟩
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrate := cubeFEM_rate_C2 hT hB hCR.1 hCR.2
  obtain ⟨K, hK⟩ := hrate
  have hsol := fun N => (cubeFEM_existsUnique hT hB hCR.1 hCR.2 N coupledDatum).exists
  choose x hx using hsol
  have hbound : ∀ N, Feec.BGG.graphSq bggSegment.d0 (coupledσ - (x N).1) +
      Feec.BGG.graphSq bggSegment.dt0 (coupledφ - (x N).2.1) +
      (cubeFEM hT hB N).gnSq (coupledu - (x N).2.2.1) ≤ (K * L * meshSize N) ^ 2 := fun N =>
    hK.2 N hL0 c1 c2 c3 hσ hφ hu hlam hSu (x N).1.2 (x N).2.1.2 (x N).2.2.1.2 (hx N).1
      (hx N).2.1 (hx N).2.2
  refine ⟨K * L, fun N => (x N).1, fun N => (x N).2.1, fun N => (x N).2.2.1, fun N =>
    ⟨(x N).1.2, (x N).2.1.2, (x N).2.2.1.2, (x N).2.2.2, (hx N).1, (hx N).2.1, (hx N).2.2,
      hbound N⟩, ?_⟩
  have hKL : ∀ N, 0 ≤ K * L * meshSize N := fun N =>
    mul_nonneg (mul_nonneg hK.1 hL0) (meshSize_pos N).le
  have g0 := fun N => Feec.BGG.graphSq_nonneg bggSegment.d0 (coupledσ - (x N).1)
  have g1 := fun N => Feec.BGG.graphSq_nonneg bggSegment.dt0 (coupledφ - (x N).2.1)
  have g2 : ∀ N, 0 ≤ (cubeFEM hT hB N).gnSq (coupledu - (x N).2.2.1) := fun N => by
    unfold Feec.BGG.Discrete.gnSq; positivity
  have e1 : ∀ᶠ N in atTop, ((x N).1 : U0) ≠ 0 := by
    refine eventually_ne_zero_of_le (y := fun N => ((x N).1 : U0)) (A := K * L) (B := 1) hσ0
      fun N => ?_
    have h1 : ‖coupledσ - (x N).1‖ ^ 2 ≤ (K * L * meshSize N) ^ 2 := by
      have := hbound N
      unfold Feec.BGG.graphSq at this
      nlinarith [sq_nonneg ‖bggSegment.d0 (coupledσ - (x N).1)‖, g1 N, g2 N]
    rw [mul_one]
    exact le_of_pow_le_pow_left₀ two_ne_zero (hKL N) h1
  have e2 : ∀ᶠ N in atTop, ((x N).2.1 : Wv U0) ≠ 0 := by
    refine eventually_ne_zero_of_le (y := fun N => ((x N).2.1 : Wv U0)) (A := K * L) (B := 1) hφ0
      fun N => ?_
    have h1 : ‖coupledφ - (x N).2.1‖ ^ 2 ≤ (K * L * meshSize N) ^ 2 := by
      have := hbound N
      unfold Feec.BGG.graphSq at this
      nlinarith [sq_nonneg ‖bggSegment.dt0 (coupledφ - (x N).2.1)‖, g0 N, g2 N]
    rw [mul_one]
    exact le_of_pow_le_pow_left₀ two_ne_zero (hKL N) h1
  have e3 : ∀ᶠ N in atTop, ((x N).2.2.1 : Wv U1) ≠ 0 := by
    refine eventually_ne_zero_of_le (y := fun N => ((x N).2.2.1 : Wv U1)) (A := K * L) (B := 1)
      hu0 fun N => ?_
    have h1 : ‖coupledu - (x N).2.2.1‖ ^ 2 ≤ (K * L * meshSize N) ^ 2 := by
      have := hbound N
      unfold Feec.BGG.Discrete.gnSq at this
      nlinarith [sq_nonneg ‖(cubeFEM hT hB N).S1h (coupledu - (x N).2.2.1)‖,
        sq_nonneg ‖bggSegment.dt1 (coupledu - (x N).2.2.1)‖, g0 N, g1 N]
    rw [mul_one]
    exact le_of_pow_le_pow_left₀ two_ne_zero (hKL N) h1
  filter_upwards [e1, e2, e3] with N h1 h2 h3
  exact ⟨h1, h2, h3⟩

end Feec.EinsteinBianchi.StaticFEM
