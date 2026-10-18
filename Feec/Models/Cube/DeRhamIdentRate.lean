module

public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Cube.WhitneyRate

/-!
# `O(h)` rates of the Whitney method on the cube with the Poincaré hypotheses discharged

The `O(h)` convergence theorems of `Feec.Models.Cube.WhitneyRate` for `C²` solutions of the mixed
Hodge–Laplace problem on `Q = (0, ½)ⁿ` take the Poincaré inequalities of `HΛ(Q)` (resp. `H̊Λ(Q)`)
as hypotheses `hPi`, `hPj`. These hold with `c_P = (2π)⁻¹` in every degree
(`FEM.norm_le_of_mem_orthogonal_cycles`, `FEM.norm_le_of_mem_orthogonal_cycles_min`, from the
identification with the parity classes of the torus de Rham complex), so the rates hold with only
the smoothing estimates and the `C²` regularity of the solution as hypotheses:

* `SmoothingEstimates.norm_sub_le_meshSize_smooth'` (the family `HΛ(Q)`, Whitney spaces);
* `SmoothingEstimatesMin.norm_sub_le_meshSize'` (generic quasi-optimal rate on `H̊Λ(Q)`);
* `SmoothingEstimatesMin.norm_sub_le_meshSize_smooth'` (`C²` forms vanishing outside `Q`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (Poincaré inequality), Thm 3.9 (quasi-optimality of the mixed method)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (rates for smooth
  solutions)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.HilbertComplex

variable {n : ℕ} [NeZero n]

namespace SmoothingEstimates

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : SmoothingEstimates n p C)
include hE

/-- **`O(h)` convergence of the mixed method for smooth solutions on `HΛ(Q)`** ([AFW2010],
Thm 3.9; [Arnold2018], Ch. 7): `SmoothingEstimates.norm_sub_le_meshSize_smooth` with the
Poincaré hypotheses discharged (`c_P = (2π)⁻¹`). -/
theorem norm_sub_le_meshSize_smooth' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsC2Form i L ((complex n).domainIncl i σ))
    (hu : IsC2Form j L ((complex n).domainIncl j u))
    (hB : IsC2Form j L ((complex n).domainIncl j
      ((complex n).boundaryPart j ((complex n).domainIncl j u))))
    (hq : IsC2Form j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        ((1 + 2 * C) * (interpBound n i + interpBound n j) * L) * meshSize N :=
  hE.norm_sub_le_meshSize_smooth hij hjk (norm_le_of_mem_orthogonal_cycles hij)
    (norm_le_of_mem_orthogonal_cycles hjk) hs hL0 hσ hu hB hq N

end SmoothingEstimates

namespace SmoothingEstimatesMin

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : SmoothingEstimatesMin n p C)
include hE

/-- **Quasi-optimal `O(h)` rate of the mixed method on `H̊Λ(Q)`** ([AFW2010], Thm 3.9):
`SmoothingEstimatesMin.norm_sub_le_meshSize` with the Poincaré hypotheses discharged
(`c_P = (2π)⁻¹`). -/
theorem norm_sub_le_meshSize' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {K : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((whitneyMin n N).domainSub i) ≤ K * meshSize N)
    (hu : Metric.infDist u ((whitneyMin n N).domainSub j) ≤ K * meshSize N)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitneyMin n N).harmonicW j) ≤
      K * meshSize N)
    (hB : Metric.infDist ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))
      ((whitneyMin n N).domainSub j) ≤ K * meshSize N) :
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
        meshSize N :=
  hE.norm_sub_le_meshSize hij hjk (norm_le_of_mem_orthogonal_cycles_min hij)
    (norm_le_of_mem_orthogonal_cycles_min hjk) hs N hσ hu hq hB

/-- **`O(h)` convergence of the mixed method with vanishing traces for smooth solutions**
([AFW2010], Thm 3.9; [Arnold2018], Ch. 7): `SmoothingEstimatesMin.norm_sub_le_meshSize_smooth`
with the Poincaré hypotheses discharged (`c_P = (2π)⁻¹`). -/
theorem norm_sub_le_meshSize_smooth' {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexMin n).domainSpace i}
    {u : (complexMin n).domainSpace j} {q : (complexMin n).harmonic j}
    (hs : (complexMin n).IsMixedSolution i j k f σ u q) {L : ℝ} (hL0 : 0 ≤ L)
    (hσ : IsC2FormMin i L ((complexMin n).domainIncl i σ))
    (hu : IsC2FormMin j L ((complexMin n).domainIncl j u))
    (hB : IsC2FormMin j L ((complexMin n).domainIncl j
      ((complexMin n).boundaryPart j ((complexMin n).domainIncl j u))))
    (hq : IsC2FormMin j L (q : L2F ℝ (cubeDomain n) (formIdx n j))) (N : ℕ) :
    ‖σ - (whitneyMin n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).fst‖ +
        ‖u - (whitneyMin n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin n N) hij hjk f).snd.snd :
            (whitneyMin n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) *
        (2 * ((1 + 2 * C) * (interpBound n i + interpBound n j) * L)) * meshSize N :=
  hE.norm_sub_le_meshSize_smooth hij hjk (norm_le_of_mem_orthogonal_cycles_min hij)
    (norm_le_of_mem_orthogonal_cycles_min hjk) hs hL0 hσ hu hB hq N

end SmoothingEstimatesMin

end Feec.Models.Cube.FEM
