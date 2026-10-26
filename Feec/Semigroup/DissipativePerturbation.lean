module

public import Feec.Semigroup.LumerPhillips
public import Feec.ForMathlib.LinearPMap.Bounded

/-!
# Dissipative bounded perturbations of m-dissipative operators

Lower-order terms (damping, absorption, zeroth-order coupling between the fields of a system)
enter an evolution `u' = A u` as a bounded perturbation `A + B`. This file records the
combination rule that lets the semidiscrete and fully discrete FEEC theorems
(`Feec.HilbertComplex.DissipFEEC`, `Feec.HilbertComplex.Approximation.FullyDiscrete`) apply to
`A + B`:

* **`LinearPMap.IsMDissipative.vadd`**: if `A` is m-dissipative, `B` is bounded and `A + B`
  (domain `D(A)`, `B +ᵥ A`) is dissipative, then `A + B` is m-dissipative:
  `μ - A - B = (1 - B (μ - A)⁻¹)(μ - A)` is onto for `μ > ‖B‖`. In particular
  `IsMDissipative.vadd_of_dissipative` (bounded dissipative `B`, e.g. damping `-σ`), and
  `IsMDissipative.vadd_sub_smul` (any bounded `B`, shifted by `ω ≥ ‖B‖`: the generator of
  `e^{-ωt} e^{t(A + B)}`, a quasi-contractive perturbation reduced to a contractive one).

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.1 (Thm 1.1, Cor 3.3: bounded perturbations of generators)
* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §III.1 (bounded perturbations)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Feec.Operator

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {A : E →ₗ.[𝕜] E}

/-- **Dissipative bounded perturbations of m-dissipative operators are m-dissipative**: if `A` is
m-dissipative, `B` bounded and `B +ᵥ A` dissipative, then `B +ᵥ A` is m-dissipative (for
`μ = ‖B‖ + 1`, `μ - A - B = (1 - B R(μ))(μ - A)` with `‖B R(μ)‖ < 1`). [Pazy1983], §3.1 -/
theorem IsMDissipative.vadd (hA : A.IsMDissipative) (B : E →L[𝕜] E)
    (hAB : ((B : E →ₗ[𝕜] E) +ᵥ A).IsDissipative) : ((B : E →ₗ[𝕜] E) +ᵥ A).IsMDissipative := by
  set μ : ℝ := ‖B‖ + 1
  have hμ : 0 < μ := by positivity
  have hR := hA.isResolvent hμ
  set R := resolvent A (μ : 𝕜)
  set T : E →L[𝕜] E := B * R
  have hT : ‖T‖ < 1 := by
    have h1 : ‖R‖ ≤ μ⁻¹ := hA.norm_resolvent_le hμ
    calc ‖T‖ ≤ ‖B‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ ‖B‖ * μ⁻¹ := by gcongr
      _ < μ * μ⁻¹ := by gcongr; simp [μ]
      _ = 1 := mul_inv_cancel₀ hμ.ne'
  set U := Units.oneSub T hT
  refine ⟨hAB, μ, hμ, fun y => ?_⟩
  set z := (↑U⁻¹ : E →L[𝕜] E) y
  have hz : z - T z = y := by
    have h := congrArg (fun C : E →L[𝕜] E => C y) U.mul_inv
    simpa [U, z, Units.val_oneSub] using h
  refine ⟨⟨R z, hR.mem_domain z⟩, ?_⟩
  change (μ : 𝕜) • R z - (B (R z) + A (hR.toDomain z)) = y
  rw [hR.apply_resolvent, ← hz]
  change _ = z - B (R z)
  abel

/-- **Bounded dissipative perturbations** (damping, absorption): `A` m-dissipative and `B` bounded
dissipative give `A + B` m-dissipative. [Pazy1983], §3.1 -/
theorem IsMDissipative.vadd_of_dissipative (hA : A.IsMDissipative) {B : E →L[𝕜] E}
    (hB : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) : ((B : E →ₗ[𝕜] E) +ᵥ A).IsMDissipative :=
  hA.vadd B (hA.dissipative.vadd hB)

/-- **Any bounded perturbation, shifted**: for `A` m-dissipative, `B` bounded and `ω ≥ ‖B‖`,
`A + B - ω` is m-dissipative (it generates `e^{-ωt} e^{t(A + B)}`). [Pazy1983], §3.1 -/
theorem IsMDissipative.vadd_sub_smul (hA : A.IsMDissipative) (B : E →L[𝕜] E) {ω : ℝ}
    (hω : ‖B‖ ≤ ω) :
    (((B - (ω : 𝕜) • ContinuousLinearMap.id 𝕜 E : E →L[𝕜] E) : E →ₗ[𝕜] E) +ᵥ A).IsMDissipative :=
  hA.vadd_of_dissipative fun x => by
    have h1 : RCLike.re ⟪B x, x⟫_𝕜 ≤ ω * ‖x‖ ^ 2 :=
      calc RCLike.re ⟪B x, x⟫_𝕜 ≤ ‖B x‖ * ‖x‖ :=
            (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
        _ ≤ ‖B‖ * ‖x‖ * ‖x‖ := by gcongr; exact B.le_opNorm x
        _ ≤ ω * ‖x‖ ^ 2 := by rw [pow_two, ← mul_assoc]; gcongr
    have h2 : RCLike.re ⟪(B - (ω : 𝕜) • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜 =
        RCLike.re ⟪B x, x⟫_𝕜 - ω * ‖x‖ ^ 2 := by
      simp only [_root_.sub_apply, _root_.smul_apply,
        ContinuousLinearMap.id_apply, inner_sub_left, inner_smul_left, RCLike.conj_ofReal,
        _root_.map_sub, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    linarith

end LinearPMap
