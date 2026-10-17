module

public import Feec.Variational.SaddlePoint

/-!
# Fortin operators and the discrete inf-sup condition

A Fortin operator for a constraint form `b : X →L[𝕜] Y →SL[σ] 𝕜` and discrete spaces
`Xₕ ⊆ X`, `Yₕ ⊆ Y` is a map `P : X → Xₕ` with `b (P v) q = b v q` for `q ∈ Yₕ` and
`‖P v‖ ≤ C ‖v‖`. It transfers the continuous inf-sup condition of `b` (inf over `q`) to the
discrete one with constant `β / C`.

## Main results

* `IsFortinOperator.discrete_infSup`: Fortin's lemma (any normed spaces, bilinear or
  sesquilinear `b`; `P` need not be linear).
* `existsUnique_discrete_isSaddleSolution`: discrete Brezzi: with a Fortin operator and the
  inf-sup property of `a` on the discrete kernel, the discrete saddle point problem on closed
  `Xₕ × Yₕ` is uniquely solvable.

## References

* [Fortin1977]; [BoffiBrezziFortin2013], §5.4; [Arnold2018], Ch. 4
-/

open ContinuousLinearMap (adjoint)

@[expose] public noncomputable section

namespace Feec.Variational

section Normed

variable {𝕜 X Y : Type*} [RCLike 𝕜] {σ : 𝕜 →+* 𝕜} [RingHomIsometric σ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- `P` is a **Fortin operator** for `b` onto `Xₕ` relative to `Yₕ`, with bound `C`. -/
structure IsFortinOperator (b : X →L[𝕜] Y →SL[σ] 𝕜) (Xh : Submodule 𝕜 X) (Yh : Submodule 𝕜 Y)
    (P : X → X) (C : ℝ) : Prop where
  mem : ∀ v, P v ∈ Xh
  comm : ∀ v, ∀ q ∈ Yh, b (P v) q = b v q
  norm_le : ∀ v, ‖P v‖ ≤ C * ‖v‖

variable {b : X →L[𝕜] Y →SL[σ] 𝕜} {Xh : Submodule 𝕜 X} {Yh : Submodule 𝕜 Y} {P : X → X}
  {C β : ℝ}

/-- **Fortin's lemma**: a Fortin operator with bound `C` transfers the inf-sup condition
`β ‖q‖ ≤ sup_v |b v q| / ‖v‖` to `Yₕ` with the sup over `Xₕ` and constant `β / C`. -/
theorem IsFortinOperator.discrete_infSup (hP : IsFortinOperator b Xh Yh P C) (hC : 0 < C)
    (hb : ∀ q, β * ‖q‖ ≤ ‖b.flip q‖) :
    ∀ q ∈ Yh, β / C * ‖q‖ ≤ ‖(b.flip q).comp Xh.subtypeL‖ := by
  intro q hq
  have key : ‖b.flip q‖ ≤ C * ‖(b.flip q).comp Xh.subtypeL‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    calc ‖b.flip q v‖ = ‖((b.flip q).comp Xh.subtypeL) ⟨P v, hP.mem v⟩‖ := by
          simp [ContinuousLinearMap.flip_apply, hP.comm v q hq]
      _ ≤ ‖(b.flip q).comp Xh.subtypeL‖ * ‖P v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(b.flip q).comp Xh.subtypeL‖ * (C * ‖v‖) := by gcongr; exact hP.norm_le v
      _ = _ := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  nlinarith [hb q]

end Normed

section Hilbert

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
  {a : X →L[𝕜] X →L⋆[𝕜] 𝕜} {b : X →L[𝕜] Y →L⋆[𝕜] 𝕜} {Xh : Submodule 𝕜 X}
  {Yh : Submodule 𝕜 Y} {P : X → X} {C β γ : ℝ}

/-- **Discrete Brezzi via Fortin.** On complete (e.g. closed or finite-dimensional) discrete spaces `Xₕ`, `Yₕ`, let `Bₕ` be the
discrete constraint operator of `b` (`b vₕ qₕ = ⟪qₕ, Bₕ vₕ⟫`). If `b` has the continuous inf-sup
property (inf over `q`), a Fortin operator with bound `C` exists, and `a` has the inf-sup property
and separates on the discrete kernel `ker Bₕ`, then the discrete saddle point problem is uniquely
solvable for all discrete data. Thesis: Thm 4.11 -/
theorem existsUnique_discrete_isSaddleSolution [CompleteSpace Xh] [CompleteSpace Yh]
    (hP : IsFortinOperator b Xh Yh P C) (hC : 0 < C) (hβ : 0 < β)
    (hb : ∀ q, β * ‖q‖ ≤ ‖b.flip q‖)
    (hZ : InfSup (restrict (restrict a Xh Xh) (rieszOp (restrict b Xh Yh)).ker
      (rieszOp (restrict b Xh Yh)).ker) γ)
    (hZs : SeparatingRight (restrict (restrict a Xh Xh) (rieszOp (restrict b Xh Yh)).ker
      (rieszOp (restrict b Xh Yh)).ker))
    (F : Xh →L⋆[𝕜] 𝕜) (G : Yh →L⋆[𝕜] 𝕜) :
    ∃! up : Xh × Yh,
      IsSaddleSolution (restrict a Xh Xh) (rieszOp (restrict b Xh Yh)) F G up.1 up.2 := by
  refine existsUnique_isSaddleSolution hZ hZs (div_pos hβ hC) (fun q => ?_) F G
  rw [norm_adjoint_rieszOp_apply]
  have heq : ((restrict b Xh Yh).flip q : Xh →L[𝕜] 𝕜) = (b.flip q).comp Xh.subtypeL :=
    ContinuousLinearMap.ext fun _ => rfl
  rw [heq]
  exact hP.discrete_infSup hC hb q q.2

end Hilbert

end Feec.Variational
