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
  common smoother for both rows (`Feec.Models.Cube.WeakSymmetry.table51`); the canonical
  projections of the thesis are not bounded on `L²` (on the discrete spaces both are defined,
  and Props 5.7–5.9 for the canonical maps are in `Feec.Models.Cube.WeakSymmetryEstimates`).

**Main theorem** (`staticFEM`, under the regularity hypothesis `CurlPotential`, see below):
the continuous problem (5.3) is well posed for every `f` (thesis Prop 5.2); for every `N` the
discretization satisfies the surjectivity hypothesis (5.4) and uniform projection bounds; the
discrete problem (5.7) has a unique solution for every datum (thesis Prop 5.4); and for exact
solutions with `σ, φ, u, λ, S¹u` of class `C²`, vanishing outside `Q`, with first derivatives
bounded by `L`, `‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N)²` with `K` independent of `N`
(thesis Thm 5.5, corrected).

**Non-vacuity** (`staticFEM_nonvacuous`): the discrete spaces are nonzero for all large `N`
(unconditionally), and there is a nontrivial smooth exact solution (manufactured data:
`u` = `dᵗ(f dx₀ ∧ dx₁)` in the first row, `σ = φ = λ = 0`) satisfying every hypothesis of the
error estimate, whose discrete solutions are nonzero for large `N`.

**Status of the thesis statements used.**
* Prop 5.7 (5.4): proved, in the corrected (moment-DOF) form, for the canonical maps
  (`Feec.FiniteElement.PolySeq.bggS0h_tensorInterp`) and transferred to the smoothed projections
  of one smoother (`Feec.Models.Cube.WeakSymmetry.table51_compatible`).
* Prop 5.8: corrected (the `ℓ¹` DOF sums are replaced by local `ℓ²`/`L²` scaling,
  `Feec.Models.Cube.WeakSymmetry.norm_glue_bggS0h_le`, `norm_glue_bggS1h_le`); `S₁ = 2 vskw`
  (the normalization of the anticommutation `d S = −S d`).
* Prop 5.9(1): proved (`norm_sub_glue_bggS0h_le`), and transferred to `π¹`
  (`table51_happ0`).
* Prop 5.9(2): **refuted** (`exists_counterexample_prop59_two`, also for every projection onto
  the Raviart–Thomas spaces, `not_exists_bestApprox_bound`). Thm 5.5 therefore applies with the
  weak consistency `|⟪S¹u, (S₁ − S₁,ₕ)v⟫| ≤ C h ‖v‖_V` in place of the false hypothesis
  (`Feec.BGG.Discrete.error_estimate_of_weakConsistency`), which follows from regular `H̊¹`
  potentials and the `H̊¹` approximation of the smoothed projections
  (`Feec.Models.Cube.WeakSymmetry.table51Reg`,
  `Feec.BGG.Discrete.weakConsistency_of_regularPotential_of_bound`).
* Thm 5.5: proved for Table 5.1 on the cube, with `λ ∈ L²` (the thesis' `λ ∈ H⁻¹(div)` does not
  give the bound) and the `h`-dependent norm `‖·‖_{Γₕ}`.

**The remaining hypothesis.** `CurlPotential` (`curl H̊(curl) = curl S⁰ H̊¹(Q; ℝ³)`, the regular
decomposition of [Hiptmair2002], Lemma 2.4, [HiptmairXu2007], §3) is the one explicit hypothesis;
it is not in Mathlib (`Feec.Models.Cube.WeakSymmetry.CurlPotential`: equivalent to the closedness
of `curl S⁰ H̊¹(Q; ℝ³)`, true on test fields).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, (5.3), (5.7), Table 5.1, Props 5.2, 5.4, 5.7–5.9, Thm 5.5
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [R. Hiptmair, J. Xu, *Nodal auxiliary space preconditioning in H(curl) and H(div) spaces*][HiptmairXu2007],
  §3 (regular decomposition)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Filter

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.StaticFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

/-- **The time-independent Einstein–Bianchi system with weak symmetries on the cube: well-posedness
and convergence of the finite element method of Table 5.1** ([QuennevilleBelair2015], §5.3,
Props 5.2, 5.4, Thm 5.5), under the regularity hypothesis `CurlPotential`. There are smoothing
parameters `p` (one smoother for both rows) and a constant `C` such that:
1. (5.3) is well posed for every `f` (`bggHilb.IsSaddle`, with a stability bound);
2. for every `N` the discretization `table51 hT hB N` satisfies (5.4) (`Compatible`) and the
   projection bounds `Bounded (2C)`, `C` independent of `N`;
3. for every `N` and every datum `F` the discrete problem (5.7) has exactly one solution;
4. there is `K`, independent of `N` and of the solution, such that for every exact solution
   `(σ, φ, u, λ)` of (5.3) (with `λ ∈ L²`) whose components, `λ` and `S¹u` are `C²` forms vanishing
   outside `Q` with first derivatives bounded by `L`, and every discrete solution,
   `‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N)²`. -/
theorem staticFEM (hR : CurlPotential) :
    ((∀ f : Wv W1, ∃! xl : Feec.BGG.Xsp V0 Vt0 Vt1 × bggHilb.Wcheck,
        bggHilb.IsSaddle f xl.1 xl.2) ∧
      ∃ C', ∀ (f : Wv W1) (x : Feec.BGG.Xsp V0 Vt0 Vt1) (l : bggHilb.Wcheck),
        bggHilb.IsSaddle f x l → ‖x‖ + ‖l‖ ≤ C' * ‖f‖) ∧
    ∃ (p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      (∀ N, (table51 hT hB N).Compatible) ∧ (∀ N, (table51 hT hB N).Bounded (2 * C)) ∧
      (∀ (N : ℕ) (F : Wv U1 →ₗ[ℝ] ℝ),
        ∃! x : (table51 hT hB N).V0h × (table51 hT hB N).Vt0h × (table51 hT hB N).Vt1h ×
            (table51 hT hB N).V1h,
          (∀ τ ∈ (table51 hT hB N).V0h, ∀ ψ ∈ (table51 hT hB N).Vt0h,
            ⟪(x.1 : U0), τ⟫ - ⟪(x.2.2.1 : Wv U1), bggSegment.dt0 ψ⟫
              - ⟪(x.2.2.2 : U1), bggSegment.d0 τ - (table51 hT hB N).S0h ψ⟫ = 0) ∧
          (∀ v ∈ (table51 hT hB N).Vt1h, ⟪bggSegment.dt0 x.2.1, v⟫ +
            ⟪(table51 hT hB N).S1h x.2.2.1, (table51 hT hB N).S1h v⟫ +
              ⟪bggSegment.dt1 x.2.2.1, bggSegment.dt1 v⟫ = F v) ∧
          (∀ μ ∈ (table51 hT hB N).V1h,
            ⟪bggSegment.d0 x.1 - (table51 hT hB N).S0h x.2.1, μ⟫ = 0)) ∧
      ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
        {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
        (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
          ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
        (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
          ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
        bggSegment.d0 σ = bggSegment.S0 φ →
        IsCsFormMin 0 0 L (σ : W0) → (∀ a, IsCsFormMin 0 0 L (φ a : W0)) →
        (∀ a, IsCsFormMin 0 1 L (u a : W1)) → IsCsFormMin 0 1 L lam →
        IsCsFormMin 0 2 L (bggSegment.S1 u) →
        ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
        σh ∈ (table51 hT hB N).V0h → φh ∈ (table51 hT hB N).Vt0h →
        uh ∈ (table51 hT hB N).Vt1h →
        (∀ τ ∈ (table51 hT hB N).V0h, ∀ ψ ∈ (table51 hT hB N).Vt0h,
          ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
            ⟪lh, bggSegment.d0 τ - (table51 hT hB N).S0h ψ⟫ = 0) →
        (∀ v ∈ (table51 hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
          ⟪(table51 hT hB N).S1h uh, (table51 hT hB N).S1h v⟫ +
            ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
        (∀ μ ∈ (table51 hT hB N).V1h,
          ⟪bggSegment.d0 σh - (table51 hT hB N).S0h φh, μ⟫ = 0) →
        Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
          (table51 hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2 := by
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrows := tableRows_uniform_cochainProjection
  obtain ⟨p, C, hT, hB, -⟩ := hrows
  exact ⟨bgg_existsUnique_isSaddle hR, p, C, hT, hB, table51_compatible hT hB,
    table51_bounded hT hB, table51_existsUnique hT hB hCR.1 hCR.2,
    table51_rate_C2 hT hB hCR.1 hCR.2⟩

/-- **Non-vacuity of `staticFEM`** (for any common smoother `p` of the two rows):
1. the discrete spaces `Vₕ⁰, Vₕ¹, Ṽₕ⁰, Ṽₕ¹` are nonzero for all large `N` (unconditionally);
2. the manufactured field `mU` (first row `dᵗ(f dx₀ ∧ dx₁)`, `f` a bump in `Q`) is nonzero, and
   `(σ, φ, u, λ) = (0, 0, mU, 0)` with the datum `mF` solves (5.3) with all the `C²` hypotheses of
   the error estimate;
3. under the regularity hypothesis, the discrete solutions `uₕ` of (5.7) with datum `mF` converge
   to `mU` at rate `h_N` in `‖·‖_{Γₕ}` and are nonzero for all large `N`. -/
theorem staticFEM_nonvacuous {p : ℕ → Feec.Domain.SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) :
    (∀ᶠ N in atTop, (table51 hT hB N).V0h ≠ ⊥ ∧ (table51 hT hB N).V1h ≠ ⊥ ∧
      (table51 hT hB N).Vt0h ≠ ⊥ ∧ (table51 hT hB N).Vt1h ≠ ⊥) ∧
    mU ≠ 0 ∧
    (∀ τ ψ, ⟪(0 : U0), τ⟫ - ⟪mU, bggSegment.dt0 ψ⟫ -
      ⟪(0 : W1), ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) ∧
    (∀ v, ⟪bggSegment.dt0 (0 : Wv U0), v⟫ + ⟪bggSegment.S1 mU, bggSegment.S1 v⟫ +
      ⟪bggSegment.dt1 mU, bggSegment.dt1 v⟫ = mF v) ∧
    bggSegment.d0 (0 : U0) = bggSegment.S0 (0 : Wv U0) ∧
    (∃ L, 0 ≤ L ∧
      IsCsFormMin 0 0 L ((0 : U0) : W0) ∧ (∀ a, IsCsFormMin 0 0 L (((0 : Wv U0) a : U0) : W0)) ∧
      (∀ a, IsCsFormMin 0 1 L ((mU a : U1) : W1)) ∧ IsCsFormMin 0 1 L (0 : W1) ∧
      IsCsFormMin 0 2 L (bggSegment.S1 mU)) ∧
    (CurlPotential → ∃ (K : ℝ) (uh : ℕ → Wv U1), (∀ N, uh N ∈ (table51 hT hB N).Vt1h ∧
      ∃ (σh : U0) (φh : Wv U0) (lh : U1), σh ∈ (table51 hT hB N).V0h ∧
        φh ∈ (table51 hT hB N).Vt0h ∧
        (∀ τ ∈ (table51 hT hB N).V0h, ∀ ψ ∈ (table51 hT hB N).Vt0h,
          ⟪σh, τ⟫ - ⟪uh N, bggSegment.dt0 ψ⟫ -
            ⟪lh, bggSegment.d0 τ - (table51 hT hB N).S0h ψ⟫ = 0) ∧
        (∀ v ∈ (table51 hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
          ⟪(table51 hT hB N).S1h (uh N), (table51 hT hB N).S1h v⟫ +
            ⟪bggSegment.dt1 (uh N), bggSegment.dt1 v⟫ = mF v) ∧
        (∀ μ ∈ (table51 hT hB N).V1h,
          ⟪bggSegment.d0 σh - (table51 hT hB N).S0h φh, μ⟫ = 0) ∧
        (table51 hT hB N).gnSq (mU - uh N) ≤ (K * meshSize N) ^ 2) ∧
      ∀ᶠ N in atTop, uh N ≠ 0) := by
  have hman := exists_manufactured_solution
  refine ⟨table51_ne_bot hT hB, mU_ne_zero, manufactured_c1, manufactured_c2, manufactured_c3,
    hman, fun hR => ?_⟩
  obtain ⟨L, hLm⟩ := hman
  have hL0 := hLm.1
  have hm := hLm.2
  have hCRex := hR.exists_bound
  obtain ⟨CR, hCR⟩ := hCRex
  have hrate := table51_rate_C2 hT hB hCR.1 hCR.2
  obtain ⟨K, hK⟩ := hrate
  have hsol := fun N => (table51_existsUnique hT hB hCR.1 hCR.2 N mF).exists
  choose x hx using hsol
  have hbound : ∀ N, Feec.BGG.graphSq bggSegment.d0 ((0 : U0) - (x N).1) +
      Feec.BGG.graphSq bggSegment.dt0 ((0 : Wv U0) - (x N).2.1) +
      (table51 hT hB N).gnSq (mU - (x N).2.2.1) ≤ (K * L * meshSize N) ^ 2 := fun N =>
    hK.2 N hL0 manufactured_c1 manufactured_c2 manufactured_c3 hm.1 hm.2.1 hm.2.2.1
      hm.2.2.2.1 hm.2.2.2.2 (x N).1.2 (x N).2.1.2 (x N).2.2.1.2 (hx N).1 (hx N).2.1 (hx N).2.2
  have hgn : ∀ N, (table51 hT hB N).gnSq (mU - (x N).2.2.1) ≤ (K * L * meshSize N) ^ 2 :=
    fun N => le_trans (le_add_of_nonneg_left (add_nonneg (Feec.BGG.graphSq_nonneg _ _)
      (Feec.BGG.graphSq_nonneg _ _))) (hbound N)
  refine ⟨K * L, fun N => (x N).2.2.1, fun N => ⟨(x N).2.2.1.2, (x N).1, (x N).2.1, (x N).2.2.2,
    (x N).1.2, (x N).2.1.2, (hx N).1, (hx N).2.1, (hx N).2.2, hgn N⟩, ?_⟩
  refine eventually_ne_zero_of_le (A := K * L) (B := 1) mU_ne_zero fun N => ?_
  have h1 : ‖mU - (x N).2.2.1‖ ^ 2 ≤ (K * L * meshSize N) ^ 2 := by
    refine le_trans ?_ (hgn N)
    unfold Feec.BGG.Discrete.gnSq
    nlinarith [sq_nonneg ‖(table51 hT hB N).S1h (mU - (x N).2.2.1)‖,
      sq_nonneg ‖bggSegment.dt1 (mU - (x N).2.2.1)‖]
  have hKL : 0 ≤ K * L * meshSize N := mul_nonneg (mul_nonneg hK.1 hL0) (meshSize_pos N).le
  rw [mul_one]
  exact le_of_pow_le_pow_left₀ two_ne_zero hKL h1

end Feec.EinsteinBianchi.StaticFEM
