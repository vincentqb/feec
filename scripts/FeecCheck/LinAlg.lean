import Feec.HilbertComplex.Approximation.FullyDiscrete
import Feec.HilbertComplex.Approximation.StaticFEEC

/-!
# Regression tests: the block systems and Fortin operators under the crown

`Feec.TimeStepping.BlockMatrix` and `Feec.Variational.Fortin` fed nothing that reaches the crown.
They now do: the crown's fully discrete Crank–Nicolson iterate is the solution of the signed
Hermitian system of `BlockMatrix` in every basis of the discrete space
(`Feec.HilbertComplex.DissipFEEC.crankNicolson_signed_mulVec_iff`,
`Feec.HilbertComplex.SkewFEEC.crankNicolson_signed`), and the static verdict carries the uniform
discrete inf-sup condition, proved by Fortin's criterion with the Fortin operators built from the
cochain projections (`Feec.HilbertComplex.ConformingFamily.StaticVerdict.infSup`,
`Feec.HilbertComplex.Subcomplex.CochainProjection.exists_isFortinOperator`).

On the way, the testing lemmas `Feec.TimeStepping.inner_eq_sum_repr` and
`Feec.TimeStepping.eq_of_inner_basis` were generalized from `ℝ` to every `RCLike` field, and the
continuous inf-sup hypothesis of Fortin's lemma
(`Feec.Variational.IsFortinOperator.discrete_infSup`,
`Feec.Variational.existsUnique_discrete_isSaddleSolution`) is now required on `Yₕ` only. The
theorems `linalg_old_*` state the old results verbatim and derive them from the new ones.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

namespace FeecCheck.LinAlg

open Feec Feec.Variational
open scoped RealInnerProductSpace

/-- The old `Feec.TimeStepping.inner_eq_sum_repr` (real inner products). -/
theorem linalg_old_inner_eq_sum_repr {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {m : Type*} [Fintype m] (b : Module.Basis m ℝ W) (w y : W) :
    ⟪w, y⟫ = ∑ j, b.repr y j * ⟪w, b j⟫ :=
  TimeStepping.inner_eq_sum_repr b w y

/-- The old `Feec.TimeStepping.eq_of_inner_basis` (real inner products). -/
theorem linalg_old_eq_of_inner_basis {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {m : Type*} [Fintype m] (b : Module.Basis m ℝ W) {y y' : W}
    (h : ∀ i, ⟪b i, y⟫ = ⟪b i, y'⟫) : y = y' :=
  TimeStepping.eq_of_inner_basis b h

section Normed

variable {𝕜 X Y : Type*} [RCLike 𝕜] {σ : 𝕜 →+* 𝕜} [RingHomIsometric σ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {b : X →L[𝕜] Y →SL[σ] 𝕜} {Xh : Submodule 𝕜 X} {Yh : Submodule 𝕜 Y} {P : X → X} {C β : ℝ}

/-- The old `Feec.Variational.IsFortinOperator.discrete_infSup` (inf-sup hypothesis for every
`q`). -/
theorem linalg_old_discrete_infSup (hP : IsFortinOperator b Xh Yh P C) (hC : 0 < C)
    (hb : ∀ q, β * ‖q‖ ≤ ‖b.flip q‖) :
    ∀ q ∈ Yh, β / C * ‖q‖ ≤ ‖(b.flip q).comp Xh.subtypeL‖ :=
  hP.discrete_infSup hC fun q _ => hb q

end Normed

section Hilbert

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
  {a : X →L[𝕜] X →L⋆[𝕜] 𝕜} {b : X →L[𝕜] Y →L⋆[𝕜] 𝕜} {Xh : Submodule 𝕜 X}
  {Yh : Submodule 𝕜 Y} {P : X → X} {C β γ : ℝ}

/-- The old `Feec.Variational.existsUnique_discrete_isSaddleSolution` (inf-sup hypothesis for
every `q`). -/
theorem linalg_old_existsUnique_discrete_isSaddleSolution [CompleteSpace Xh] [CompleteSpace Yh]
    (hP : IsFortinOperator b Xh Yh P C) (hC : 0 < C) (hβ : 0 < β)
    (hb : ∀ q, β * ‖q‖ ≤ ‖b.flip q‖)
    (hZ : InfSup (restrict (restrict a Xh Xh) (rieszOp (restrict b Xh Yh)).ker
      (rieszOp (restrict b Xh Yh)).ker) γ)
    (hZs : SeparatingRight (restrict (restrict a Xh Xh) (rieszOp (restrict b Xh Yh)).ker
      (rieszOp (restrict b Xh Yh)).ker))
    (F : Xh →L⋆[𝕜] 𝕜) (G : Yh →L⋆[𝕜] 𝕜) :
    ∃! up : Xh × Yh,
      IsSaddleSolution (restrict a Xh Xh) (rieszOp (restrict b Xh Yh)) F G up.1 up.2 :=
  existsUnique_discrete_isSaddleSolution hP hC hβ (fun q _ => hb q) hZ hZs F G

end Hilbert

end FeecCheck.LinAlg
