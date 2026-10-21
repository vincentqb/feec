module

public import Feec.Instances.Maxwell
public import Feec.HilbertComplex.Approximation.ApproxComplexCrime

/-!
# Maxwell on the cube through the discrete complex: the `O(h)` rate

The Whitney discretizations `Feec.Instances.Maxwell.cubePMC`, `Feec.Instances.Maxwell.cubePEC` of
Maxwell's equations on the cube go through the complex-level front end
`Feec.HilbertComplex.ApproxFEEC.ofComplex` (`Feec.Instances.Maxwell.cubePMC_ofComplex`). Their
`O(h)` rate classes of `C²` solutions (`cubePMCRate`, `cubePECRate`: graph-norm best
approximation `O(h)` along the trajectory) give, through
`Feec.HilbertComplex.ConstrainedFEEC.RateClass.toCrimeRate` (zero inner-product defect, zero
cochain defect), rate classes of `ofComplex`, so that the discrete solutions of `ofComplex`
started from the modified elliptic projection `Rₕ (x, 𝐝 x)` satisfy
`‖e^{tL} x - iₕ e^{tLₕ} Rₕ x‖ ≤ (C + C_ι C' t) h_N Λ`, linear in `t`
(`cubePMC_ofComplex_rate`, `cubePEC_ofComplex_rate`); the constants do not depend on `T` or `Λ`
(`cubePMC_toCrimeRate_C`; they take no `N` or `x`). This is an `O(h)` rate, as for the conforming
routes (`Feec.Instances.Maxwell.cubePMC_approx_rate`, factor `(1 + C_P)(1 + 2t)`;
`Feec.Instances.Maxwell.cubePMC_rate`, factor `(1 + C_P)(1 + t)²`), now from complex-level
estimates, with larger constants.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  Thm 3.10 (elliptic analogue)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.Instances.Maxwell

open Feec.HilbertComplex Models.Cube Feec.Domain Feec.ExteriorFibre

variable {n : ℕ} [NeZero n] {a : ℤ}

/-- **The `O(h)` rate of `cubePMC` through the discrete complex**: for `C²` orbits with bound
`Λ` on `[0, T]` (`cubePMCRate`), the discrete solution of `ofComplex` from the modified elliptic
projection of the datum satisfies `‖e^{tL} x - iₙ e^{tLₙ} Rₙ x‖ ≤ (C + C_ι C' t) h_N Λ`, with
`C = (1 + 8 C_ι) Cₐ`, `C' = 2 (1 + 8 (1 + C_ι²) + C_ι (1 + 8 C_ι)) Cₐ`,
`Cₐ = 2 (1 + C_ι) · 12 Σᵢ B_{a+i}` (`ConstrainedFEEC.RateClass.toCrimeRate`). -/
theorem cubePMC_ofComplex_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePMCRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complex n).window a 3).waveGroup.S t x -
        (ApproxFEEC.ofComplex (cubePMC n a).toComplex).sol N
          (((ApproxFEEC.ofComplexCore (cubePMC n a).toComplex).cmp T).p x N 0) t‖ ≤
      ((cubePMCRate n a T Λ hΛ).toCrimeRate.C +
        (cubePMC n a).toComplex.toCrime.toFamily.boundConst *
          (cubePMCRate n a T Λ hΛ).toCrimeRate.C' * t) * (FEM.meshSize N * Λ) := by
  set R := (cubePMCRate n a T Λ hΛ).toCrimeRate
  have hx2 : x ∈ ((FEM.complex n).window a 3).wave.domainSq :=
    LinearPMap.mem_domainSq.2 ⟨(cubePMCRate n a T Λ hΛ).mem_domain x hx,
      (cubePMCRate n a T Λ hΛ).mem_domain_sq x _ hx⟩
  have h := (cubePMC n a).toComplex.toCrime.error_le_of_rateClass R hx N ht
  have hp : R.p x N 0 = ((ApproxFEEC.ofComplexCore (cubePMC n a).toComplex).cmp T).p x N 0 :=
    ApproxFEEC.ofComplexCrimeCore_toCrime_p (cubePMC n a).toComplex T hx2 N 0
  rw [hp] at h
  refine h.trans_eq ?_
  change _ * (FEM.meshSize N ^ (1 : ℝ) * Λ) = _
  rw [Real.rpow_one]

/-- **The `O(h)` rate of `cubePEC` through the discrete complex** (as `cubePMC_ofComplex_rate`,
perfect electric conductor). -/
theorem cubePEC_ofComplex_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePECRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        (ApproxFEEC.ofComplex (cubePEC n a).toComplex).sol N
          (((ApproxFEEC.ofComplexCore (cubePEC n a).toComplex).cmp T).p x N 0) t‖ ≤
      ((cubePECRate n a T Λ hΛ).toCrimeRate.C +
        (cubePEC n a).toComplex.toCrime.toFamily.boundConst *
          (cubePECRate n a T Λ hΛ).toCrimeRate.C' * t) * (FEM.meshSize N * Λ) := by
  set R := (cubePECRate n a T Λ hΛ).toCrimeRate
  have hx2 : x ∈ ((FEM.complexMin n).window a 3).wave.domainSq :=
    LinearPMap.mem_domainSq.2 ⟨(cubePECRate n a T Λ hΛ).mem_domain x hx,
      (cubePECRate n a T Λ hΛ).mem_domain_sq x _ hx⟩
  have h := (cubePEC n a).toComplex.toCrime.error_le_of_rateClass R hx N ht
  have hp : R.p x N 0 = ((ApproxFEEC.ofComplexCore (cubePEC n a).toComplex).cmp T).p x N 0 :=
    ApproxFEEC.ofComplexCrimeCore_toCrime_p (cubePEC n a).toComplex T hx2 N 0
  rw [hp] at h
  refine h.trans_eq ?_
  change _ * (FEM.meshSize N ^ (1 : ℝ) * Λ) = _
  rw [Real.rpow_one]

/-- The constants of `cubePMC_ofComplex_rate` do not depend on `T` or `Λ`. -/
theorem cubePMC_toCrimeRate_C {T T' Λ Λ' : ℝ} {hΛ : 0 ≤ Λ} {hΛ' : 0 ≤ Λ'} :
    (cubePMCRate n a T Λ hΛ).toCrimeRate.C = (cubePMCRate n a T' Λ' hΛ').toCrimeRate.C ∧
      (cubePMCRate n a T Λ hΛ).toCrimeRate.C' = (cubePMCRate n a T' Λ' hΛ').toCrimeRate.C' :=
  ⟨rfl, rfl⟩

end Feec.Instances.Maxwell
