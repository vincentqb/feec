module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Elementary facts on inner product spaces

A real normed-space structure on a normed `𝕜`-space is the restriction of scalars,
`⟪x, x⟫ + ⟪y, y⟫ = 0` forces `x = y = 0`, and `(D - D†)² = -(D D† + D† D)` when `D² = 0`.
-/

open scoped InnerProductSpace

public section

variable {𝕜 : Type*} [RCLike 𝕜]

theorem RCLike.isScalarTower_of_normedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] : IsScalarTower ℝ 𝕜 E := by
  refine ⟨fun r k x => ?_⟩
  have := Continuous.ext_on Rat.denseRange_cast (continuous_id.smul continuous_const)
    ((RCLike.continuous_ofReal (K := 𝕜)).smul continuous_const) (by
      rintro _ ⟨q, rfl⟩
      change (q : ℝ) • (k • x) = ((q : ℝ) : 𝕜) • (k • x)
      rw [RCLike.ofReal_ratCast]
      exact ratCast_smul_eq ℝ 𝕜 q (k • x))
  rw [Algebra.smul_def, mul_smul]
  exact (congrFun this r).symm

theorem inner_self_add_inner_self_eq_zero {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {x : E} {y : F}
    (h : ⟪x, x⟫_𝕜 + ⟪y, y⟫_𝕜 = 0) : x = 0 ∧ y = 0 := by
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_add, RCLike.ofReal_eq_zero] at h
  have hx : ‖x‖ = 0 := by nlinarith [norm_nonneg x, norm_nonneg y]
  have hy : ‖y‖ = 0 := by nlinarith [norm_nonneg x, norm_nonneg y]
  exact ⟨norm_eq_zero.1 hx, norm_eq_zero.1 hy⟩

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem sub_adjoint_sq {D : E →L[𝕜] E} (hD : D ∘L D = 0) :
    (D - D.adjoint) ^ 2 = -(D ∘L D.adjoint + D.adjoint ∘L D) := by
  have h2 : D.adjoint ∘L D.adjoint = 0 := by rw [← adjoint_comp, hD, _root_.map_zero]
  rw [pow_two]
  change (D - D.adjoint) ∘L (D - D.adjoint) = _
  rw [sub_comp, comp_sub, comp_sub, hD, h2]
  abel

end ContinuousLinearMap
