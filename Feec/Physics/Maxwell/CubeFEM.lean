module

public import Feec.Models.Cube.FiniteElementConvergence
public import Feec.Physics.Maxwell.Forms

/-!
# Finite element approximation of Maxwell's equations on the cube

On `Q = (0, ½)³` (`Feec.Models.Cube.FEM.cubeDomain 3`) Maxwell's equations in form coordinates
are the Hodge wave equation of the window `0, 1, 2` of the `L²` de Rham complex:

* **perfect magnetic conductor**: `HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)`, the window of the maximal complex
  (`Feec.Maxwell.maximalComplex_d_eq_pmcForms_d₀`, `_d₁`);
* **perfect electric conductor**: `H̊Λ⁰(Q) → H̊Λ¹(Q) → L²Λ²(Q)`, the window of the minimal complex
  (`Feec.Maxwell.minimalComplex_d_eq_pecForms_d₀`, `_d₁`).

Discretized on the level-`(N + 1)` Freudenthal meshes by Lagrange `P₁`, Nédélec edge and
Raviart–Thomas face elements (the lowest-order Whitney forms; with vanishing boundary DOFs for
PEC), the semi-discrete solutions converge for `D(L)` data, and at rate `h` for solutions whose
components are `C²` forms (vanishing outside `Q` for PEC), with no further hypothesis
(`pmc_tendstoUniformlyOn`, `pmc_norm_sub_le_meshSize`, `pec_tendstoUniformlyOn`,
`pec_norm_sub_le_meshSize`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (rates for smooth
  solutions), Ch. 8 (evolution problems)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Maxwell.CubeFEM

open Feec.Domain Feec.HilbertComplex Feec.Models.Cube.FEM

/-- **Maxwell's equations with a perfect magnetic conductor on the cube meshes**: the semi-discrete
Lagrange–Nédélec–Raviart–Thomas solutions with `ξₕ(t₀) = Pₕ x` converge to the solution
`e^{(t - t₀) L} x` uniformly on `[t₀, t₁]`, for every `D(L)` datum ([QuennevilleBelair2015],
Thm 4.14). -/
theorem pmc_tendstoUniformlyOn (t₀ t₁ : ℝ) (x : ((complex 3).window 0 3).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complex 3).window 0 3).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitney 3 N).window 0 3).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney 3 N).window 0 3).graphSub)
        (((complex 3).window 0 3).totalD.toGraphSpace
          ⟨x, (((complex 3).window 0 3).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complex 3).window 0 3).totalD.graphFst (ξh N t))
        (fun t => ((complex 3).window 0 3).waveGroup.S (t - t₀) x) Filter.atTop
        (Set.Icc t₀ t₁) :=
  maxwell_exists_tendstoUniformlyOn_whitney t₀ t₁ x

/-- **`O(h)` convergence for Maxwell's equations with a perfect magnetic conductor**
([QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7): if the components `(σ, E, B)` of the
solution `ξ(s)` and of `ξ'(s)` are `C²` forms with bound `L` on `[t₀, t₁]`, the semi-discrete
solutions started at the elliptic projection satisfy
`‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² K L h_N` with `A`, `K` independent of `N`. -/
theorem pmc_norm_sub_le_meshSize {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex 3).window 0 3).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex 3).window 0 3).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitney 3 N).window 0 3).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney 3 N).window 0 3).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ s ∈ Set.Icc t₀ t₁, ∀ i : Fin 3,
      IsC2Form (0 + i) L (((complex 3).window 0 3).totalD.graphFst (ξ s) i) ∧
        IsC2Form (0 + i) L (((complex 3).window 0 3).totalD.graphFst (ξ' s) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex 3).window 0 3).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex 3).window 0 3).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          ((((3 : ℕ) : ℝ) + (3 : ℕ) * (3 : ℕ)) * (∑ i : Fin 3, interpBound 3 (0 + i)) * L *
            meshSize N) :=
  norm_sub_le_meshSize_window_smooth 0 3 hξ hξh h0 hL0 hreg N ht

/-- **Maxwell's equations with a perfect electric conductor on the cube meshes**: the
semi-discrete solutions in the Whitney spaces with vanishing boundary DOFs (vanishing tangential
traces) converge uniformly on `[t₀, t₁]` for every `D(L)` datum ([QuennevilleBelair2015],
Thm 4.14). -/
theorem pec_tendstoUniformlyOn (t₀ t₁ : ℝ) (x : ((complexMin 3).window 0 3).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complexMin 3).window 0 3).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitneyMin 3 N).window 0 3).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitneyMin 3 N).window 0 3).graphSub)
        (((complexMin 3).window 0 3).totalD.toGraphSpace
          ⟨x, (((complexMin 3).window 0 3).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complexMin 3).window 0 3).totalD.graphFst (ξh N t))
        (fun t => ((complexMin 3).window 0 3).waveGroup.S (t - t₀) x) Filter.atTop
        (Set.Icc t₀ t₁) :=
  exists_tendstoUniformlyOn_windowMin_whitney 0 3 t₀ t₁ x

/-- **`O(h)` convergence for Maxwell's equations with a perfect electric conductor**
([QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7): as `pmc_norm_sub_le_meshSize`, when
the components of `ξ(s)` and `ξ'(s)` are `C²` forms vanishing outside `Q` with bound `L`. -/
theorem pec_norm_sub_le_meshSize {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexMin 3).window 0 3).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin 3).window 0 3).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitneyMin 3 N).window 0 3).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((whitneyMin 3 N).window 0 3).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ s ∈ Set.Icc t₀ t₁, ∀ i : Fin 3,
      IsC2FormMin (0 + i) L (((complexMin 3).window 0 3).totalD.graphFst (ξ s) i) ∧
        IsC2FormMin (0 + i) L (((complexMin 3).window 0 3).totalD.graphFst (ξ' s) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin 3).window 0 3).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin 3).window 0 3).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          ((((3 : ℕ) : ℝ) + (3 : ℕ) * (3 : ℕ)) * (∑ i : Fin 3, interpBound 3 (0 + i)) * L *
            meshSize N) :=
  norm_sub_le_meshSize_windowMin_smooth 0 3 hξ hξh h0 hL0 hreg N ht

end Feec.Maxwell.CubeFEM
