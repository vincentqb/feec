module

public import Solution.Sobolev
public import Feec.Models.Cube.TangentialH1
public import Feec.Models.Cube.WeakSymmetryWave

/-!
# The `C²` states are `H¹` states

The `C²` rates of [QuennevilleBelair2015] on the cube are stated for states whose components are
`C²` up to `∂Q` with vanishing tangential traces (`Feec`'s class
`Feec.Models.Cube.WeakSymmetry.IsSmoothStateTr`, the class of
`Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr'`). Such states are of the class `IsH1State` of the
challenge with bound `c L`, `c` universal (`exists_isH1State_of_isSmoothStateTr`, from
`Feec.Models.Cube.FEM.IsCsFormTr.exists_h1Data`), so the `C²` rates are corollaries of the `H¹`
rates of `FEEC.weakSymmetry_cube`; the challenge states the `H¹` ones.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 5.5, §6.3
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

/-- `IsCsFormTr 0 k L` gives the `H¹(Q)` class with bound `16 c L`, also for `d̊`. -/
theorem exists_isSobolevForm_of_isCsFormTr : ∃ c : ℝ, 0 ≤ c ∧ ∀ {k : ℕ} {L : ℝ}
    {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)}, IsCsFormTr 0 k L x →
    IsSobolevForm (cube 3) 1 k (c * L) x ∧ x ∈ (dMin (cube 3) k).domain ∧
      ∀ h : x ∈ (dMin (cube 3) k).domain,
        IsSobolevForm (cube 3) 1 (k + 1) (c * L) (dMin (cube 3) k ⟨x, h⟩) := by
  obtain ⟨c, hc, H⟩ := IsCsFormTr.exists_h1Data 3
  refine ⟨16 * c, by positivity, fun {k L x} hx => ?_⟩
  obtain ⟨⟨h0⟩, h1⟩ := H hx
  have hm := hx.mem_domain
  rw [deRham_minimalComplex_d] at hm
  have e : (dMin (cube 3) k : L2Form (cube 3) k →ₗ.[ℝ] L2Form (cube 3) (k + 1)) =
      (Feec.Models.Cube.FEM.complexMin 3).d k (k + 1) := by
    rw [dMin_eq, deRham_minimalComplex_d]; rfl
  refine ⟨mul_assoc 16 c L ▸ isSobolevForm_of_h1Data h0, by rw [dMin_eq]; exact hm, fun h => ?_⟩
  have h' : x ∈ ((Feec.Models.Cube.FEM.complexMin 3).d k (k + 1)).domain := e ▸ h
  obtain ⟨hd⟩ := h1 h'
  have e2 : dMin (cube 3) k ⟨x, h⟩ = (Feec.Models.Cube.FEM.complexMin 3).d k (k + 1) ⟨x, h'⟩ :=
    LinearPMap.apply_of_eq' e ⟨x, h⟩
  rw [e2]
  exact mul_assoc 16 c L ▸ isSobolevForm_of_h1Data hd

/-- **The `C²` states are `H¹` states**: a state of `Feec`'s class `IsSmoothStateTr L` is of the
class `IsH1State (c L)` of the challenge. -/
theorem exists_isH1State_of_isSmoothStateTr : ∃ c : ℝ, 0 ≤ c ∧ ∀ {L : ℝ} {σ : U0} {φ : Wv U0}
    {u : Wv U1} {M : W2} {ρ : Wv W2}, IsSmoothStateTr L σ φ u M ρ →
      IsH1State (c * L) (σ : W0) (incl0 φ) (incl1 u) M ρ := by
  obtain ⟨c, hc, H⟩ := exists_isSobolevForm_of_isCsFormTr
  refine ⟨c, hc, fun {L σ φ u M ρ} h => ?_⟩
  obtain ⟨hσ, hφ, hu, hM, hρ⟩ := h
  exact ⟨(H (k := 0) hσ).1, fun a ha => (H (k := 0) (hφ a)).2.2 ha,
    fun a => (H (k := 1) (hu a)).1, fun a ha => (H (k := 1) (hu a)).2.2 ha,
    (H (k := 2) hM).1, fun a => (H (k := 2) (hρ a)).1, (H (k := 2) hM).2.1,
    fun a => (H (k := 2) (hρ a)).2.1⟩

end FEEC
