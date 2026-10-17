module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.Star
public import Feec.Variational.Galerkin

/-!
# Babuška–Nečas and Lax–Milgram over `ℝ` and `ℂ`

For Hilbert spaces `X`, `Y` over `𝕜 = ℝ` or `ℂ` and a bounded sesquilinear form
`B : X →L[𝕜] Y →L⋆[𝕜] 𝕜` (linear in `x`, antilinear in `y`), the problem
"find `x` with `B x = f`" is uniquely solvable for every antilinear functional `f` iff `B` has
the inf-sup property and separates the second slot. Mathlib's Lax–Milgram is real-only; here it
is a corollary of Babuška–Nečas over `RCLike`.

## Main definitions

* `Feec.Variational.rieszOp B : X →L[𝕜] Y`, with `B x y = ⟪y, rieszOp B x⟫`.

## Main results

* `Feec.Variational.innerSLFlip_surjective`, `norm_innerSLFlip`: Riesz representation of the
  antidual, `f y = ⟪y, g⟫` with `‖f‖ = ‖g‖`.
* `InfSup.surjective`, `existsUnique_apply_eq`, `existsUnique_inner`: Babuška–Nečas.
* `exists_infSup_of_bijective`: the converse, by the bounded inverse theorem.
* `babuskaNecas_iff`, `babuskaNecas_iff_inner`: the equivalence (with "exists unique"; the
  thesis' converse with "exists" is false).
* `infSup_of_coercive`, `existsUnique_of_coercive`: Lax–Milgram for `α ‖x‖² ≤ re B x x`.
* `existsUnique_galerkin_sesq`: discrete well-posedness for sesquilinear forms on
  finite-dimensional trial and test spaces of equal dimension.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.8 (Lax–Milgram), Thm 4.9 (Babuška–Nečas)
* [D. N. Arnold, *Lecture notes on Numerical Analysis of Partial Differential Equations*][ArnoldNotes2011]
  (source of Thm 4.9 of the thesis, including `‖L⁻¹‖⁻¹` as the best inf-sup constant)
* [I. Babuška, *Error-bounds for finite element method*][Babuska1971]
* [D. Boffi, F. Brezzi, M. Fortin, *Mixed Finite Element Methods and Applications*][BoffiBrezziFortin2013],
  Ch. 4
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 4
-/

open Module

@[expose] public noncomputable section

namespace Feec.Variational

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Riesz representation of antilinear functionals -/

/-- `‖y ↦ ⟪y, g⟫‖ = ‖g‖`. -/
theorem norm_innerSLFlip (g : Y) : ‖innerSLFlip 𝕜 g‖ = ‖g‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_) ?_
  · rw [innerSLFlip_apply_apply, mul_comm]; exact norm_inner_le_norm y g
  · rcases (norm_nonneg g).eq_or_lt with hg | hg
    · rw [← hg]; exact norm_nonneg _
    · refine le_of_mul_le_mul_right ?_ hg
      calc ‖g‖ * ‖g‖ = ‖⟪g, g⟫‖ := by
            rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq]
        _ = ‖innerSLFlip 𝕜 g g‖ := by rw [innerSLFlip_apply_apply]
        _ ≤ ‖innerSLFlip 𝕜 g‖ * ‖g‖ := (innerSLFlip 𝕜 g).le_opNorm g

variable [CompleteSpace Y]

/-- **Riesz representation of the antidual**: every bounded antilinear `f` is `y ↦ ⟪y, g⟫`. -/
theorem innerSLFlip_surjective : Function.Surjective (innerSLFlip 𝕜 : Y →L[𝕜] Y →L⋆[𝕜] 𝕜) := by
  intro f
  let φ : Y →L[𝕜] 𝕜 := ((starL 𝕜 : 𝕜 ≃L⋆[𝕜] 𝕜) : 𝕜 →L⋆[𝕜] 𝕜).comp f
  refine ⟨(InnerProductSpace.toDual 𝕜 Y).symm φ, ContinuousLinearMap.ext fun y => ?_⟩
  rw [innerSLFlip_apply_apply, ← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
  simp [φ]

/-! ### The Riesz operator of a form -/

variable [CompleteSpace X]

/-- The **Riesz operator** of a bounded sesquilinear form: `B x y = ⟪y, rieszOp B x⟫`. -/
def rieszOp (B : X →L[𝕜] Y →L⋆[𝕜] 𝕜) : X →L[𝕜] Y :=
  ContinuousLinearMap.adjoint
    ((((InnerProductSpace.toDual 𝕜 X).symm : StrongDual 𝕜 X ≃ₗᵢ⋆[𝕜] X) :
      StrongDual 𝕜 X →L⋆[𝕜] X).comp B.flip)

variable {B : X →L[𝕜] Y →L⋆[𝕜] 𝕜} {γ : ℝ}

@[simp] theorem inner_rieszOp (B : X →L[𝕜] Y →L⋆[𝕜] 𝕜) (x : X) (y : Y) :
    ⟪y, rieszOp B x⟫ = B x y := by
  rw [rieszOp, ContinuousLinearMap.adjoint_inner_right]
  simp [InnerProductSpace.toDual_symm_apply]

theorem innerSLFlip_rieszOp (B : X →L[𝕜] Y →L⋆[𝕜] 𝕜) (x : X) :
    innerSLFlip 𝕜 (rieszOp B x) = B x :=
  ContinuousLinearMap.ext fun y => by rw [innerSLFlip_apply_apply, inner_rieszOp]

/-- `‖rieszOp B x‖ = ‖B x‖`. -/
theorem norm_rieszOp_apply (B : X →L[𝕜] Y →L⋆[𝕜] 𝕜) (x : X) : ‖rieszOp B x‖ = ‖B x‖ := by
  rw [← innerSLFlip_rieszOp B x, norm_innerSLFlip]

/-! ### Babuška–Nečas -/

namespace InfSup

theorem isClosed_range_rieszOp (h : InfSup B γ) :
    IsClosed ((LinearMap.range (rieszOp B : X →ₗ[𝕜] Y) : Submodule 𝕜 Y) : Set Y) := by
  have : AntilipschitzWith (γ⁻¹).toNNReal (rieszOp B) := by
    refine ContinuousLinearMap.antilipschitz_of_bound _ fun x => ?_
    rw [Real.coe_toNNReal _ (inv_pos.2 h.pos).le, norm_rieszOp_apply]
    exact h.norm_le x
  exact this.isClosed_range (rieszOp B).uniformContinuous

/-- **Babuška–Nečas**, existence: inf-sup and separation make `B` onto the antidual.
[QuennevilleBelair2015], Thm 4.9 -/
theorem surjective (h : InfSup B γ) (hs : SeparatingRight B) : Function.Surjective B := by
  have hc := h.isClosed_range_rieszOp
  have : CompleteSpace (LinearMap.range (rieszOp B : X →ₗ[𝕜] Y)) := hc.completeSpace_coe
  have htop : LinearMap.range (rieszOp B : X →ₗ[𝕜] Y) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro y hy
    refine hs y fun x => ?_
    rw [← inner_rieszOp]
    exact Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self _ x) hy
  intro f
  obtain ⟨g, rfl⟩ := innerSLFlip_surjective f
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 htop g
  exact ⟨x, by rw [← innerSLFlip_rieszOp]; exact congrArg _ hx⟩

end InfSup

/-- **Babuška–Nečas** (Thm 4.9): under inf-sup and separation, `B x = f` has a unique solution
for every bounded antilinear `f`, and `‖x‖ ≤ γ⁻¹ ‖f‖`. [QuennevilleBelair2015], Thm 4.9 -/
theorem existsUnique_apply_eq (h : InfSup B γ) (hs : SeparatingRight B) (f : Y →L⋆[𝕜] 𝕜) :
    ∃! x, B x = f := by
  obtain ⟨x, hx⟩ := h.surjective hs f
  exact ⟨x, hx, fun x' hx' => h.injective (hx'.trans hx.symm)⟩

/-- **Babuška–Nečas**, Riesz-representative form: `B x y = ⟪y, g⟫` for all `y` has a unique
solution. [QuennevilleBelair2015], Thm 4.9 -/
theorem existsUnique_inner (h : InfSup B γ) (hs : SeparatingRight B) (g : Y) :
    ∃! x, ∀ y, B x y = ⟪y, g⟫ := by
  obtain ⟨x, hx, hu⟩ := existsUnique_apply_eq h hs (innerSLFlip 𝕜 g)
  refine ⟨x, fun y => by rw [hx, innerSLFlip_apply_apply], fun x' hx' => hu x' ?_⟩
  exact ContinuousLinearMap.ext fun y => by rw [hx', innerSLFlip_apply_apply]

/-- Under inf-sup and separation, `B` is an isomorphism of `X` onto the antidual of `Y`. -/
def equivOfInfSup (h : InfSup B γ) (hs : SeparatingRight B) : X ≃L[𝕜] (Y →L⋆[𝕜] 𝕜) :=
  ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.2 h.injective)
    (LinearMap.range_eq_top.2 (h.surjective hs))

@[simp] theorem equivOfInfSup_apply (h : InfSup B γ) (hs : SeparatingRight B) (x : X) :
    equivOfInfSup h hs x = B x := rfl

omit [CompleteSpace Y] in
/-- The converse of Babuška–Nečas: a bijective `B` satisfies the inf-sup condition (bounded
inverse theorem). [QuennevilleBelair2015], Thm 4.9 -/
theorem exists_infSup_of_bijective (hB : Function.Bijective B) : ∃ γ, InfSup B γ := by
  let e := ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.2 hB.1)
    (LinearMap.range_eq_top.2 hB.2)
  have hpos : 0 < ‖(e.symm : (Y →L⋆[𝕜] 𝕜) →L[𝕜] X)‖ + 1 := by positivity
  refine ⟨(‖(e.symm : (Y →L⋆[𝕜] 𝕜) →L[𝕜] X)‖ + 1)⁻¹, ⟨inv_pos.2 hpos, fun x => ?_⟩⟩
  rw [inv_mul_le_iff₀ hpos]
  calc ‖x‖ = ‖e.symm (B x)‖ := by
        rw [show B x = e x from rfl, ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ‖(e.symm : (Y →L⋆[𝕜] 𝕜) →L[𝕜] X)‖ * ‖B x‖ :=
        (e.symm : (Y →L⋆[𝕜] 𝕜) →L[𝕜] X).le_opNorm (B x)
    _ ≤ _ := by gcongr; linarith

/-- **Babuška–Nečas, equivalence** (Thm 4.9, corrected): `B` has the inf-sup property and
separates the second slot iff `B x = f` is uniquely solvable for every antilinear `f`.
The thesis' converse with "there exists" alone is false. [QuennevilleBelair2015], Thm 4.9 (corrected);
the thesis takes the statement from [ArnoldNotes2011]. -/
theorem babuskaNecas_iff :
    ((∃ γ, InfSup B γ) ∧ SeparatingRight B) ↔ ∀ f : Y →L⋆[𝕜] 𝕜, ∃! x, B x = f := by
  refine ⟨fun ⟨⟨γ, h⟩, hs⟩ => existsUnique_apply_eq h hs, fun H => ⟨?_, fun y hy => ?_⟩⟩
  · refine exists_infSup_of_bijective ⟨fun x x' hxx' => ?_, fun f => (H f).exists⟩
    obtain ⟨z, -, hz⟩ := H (B x)
    exact (hz x rfl).trans (hz x' hxx'.symm).symm
  · obtain ⟨x, hx, -⟩ := H (innerSLFlip 𝕜 y)
    have := hy x
    rw [hx, innerSLFlip_apply_apply] at this
    exact inner_self_eq_zero.1 this

/-- **Babuška–Nečas, equivalence**, Riesz-representative form. [QuennevilleBelair2015], Thm 4.9 (corrected) -/
theorem babuskaNecas_iff_inner :
    ((∃ γ, InfSup B γ) ∧ SeparatingRight B) ↔ ∀ g : Y, ∃! x, ∀ y, B x y = ⟪y, g⟫ := by
  rw [babuskaNecas_iff]
  have key : ∀ (g : Y) (x : X), (∀ y, B x y = ⟪y, g⟫) ↔ B x = innerSLFlip 𝕜 g := fun g x =>
    ⟨fun h => ContinuousLinearMap.ext fun y => by rw [h, innerSLFlip_apply_apply],
      fun h y => by rw [h, innerSLFlip_apply_apply]⟩
  constructor
  · intro H g; simpa only [key] using H (innerSLFlip 𝕜 g)
  · intro H f
    obtain ⟨g, rfl⟩ := innerSLFlip_surjective f
    simpa only [key] using H g

/-! ### Lax–Milgram -/

section Coercive

variable {B : X →L[𝕜] X →L⋆[𝕜] 𝕜} {α : ℝ}

omit [CompleteSpace X] in
/-- A coercive form, `α ‖x‖² ≤ re B x x`, satisfies the inf-sup condition with constant `α`.
[QuennevilleBelair2015], Thm 4.8 -/
theorem infSup_of_coercive (hα : 0 < α) (hB : ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re (B x x)) :
    InfSup B α := by
  simpa using InfSup.of_testMap (B := B) id hα one_pos (fun x => by simp) hB

omit [CompleteSpace X] in
/-- A coercive form separates the second slot. -/
theorem separatingRight_of_coercive (hα : 0 < α)
    (hB : ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re (B x x)) : SeparatingRight B := by
  intro y hy
  have := hB y
  rw [hy y, map_zero] at this
  have : ‖y‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖y‖]
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg y])

/-- **Lax–Milgram** over `ℝ` and `ℂ`: a bounded coercive sesquilinear form gives a unique
solution of `B x = f` for every antilinear `f`, with `‖x‖ ≤ α⁻¹ ‖f‖`. [QuennevilleBelair2015], Thm 4.8 -/
theorem existsUnique_of_coercive (hα : 0 < α) (hB : ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re (B x x))
    (f : X →L⋆[𝕜] 𝕜) : ∃! x, B x = f :=
  existsUnique_apply_eq (infSup_of_coercive hα hB) (separatingRight_of_coercive hα hB) f

end Coercive

/-! ### Discrete well-posedness for sesquilinear forms -/

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Discrete well-posedness** (sesquilinear forms): with the discrete inf-sup condition on
finite-dimensional `K`, `L` of equal dimension, the Galerkin problem `uₕ ∈ K`, `B uₕ v = F v`
(`v ∈ L`) has a unique solution for every bounded antilinear `F`. [QuennevilleBelair2015], Thm 4.10 -/
theorem existsUnique_galerkin_sesq {K : Submodule 𝕜 X} {L : Submodule 𝕜 Y}
    [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L] (hdim : finrank 𝕜 K = finrank 𝕜 L)
    (h : InfSup (restrict B K L) γ) (F : Y →L⋆[𝕜] 𝕜) :
    ∃! uh, uh ∈ K ∧ ∀ v ∈ L, B uh v = F v := by
  set A := rieszOp (restrict B K L)
  have hinj : Function.Injective A := fun x x' hxx' => h.injective (by
    rw [← innerSLFlip_rieszOp (restrict B K L) x, ← innerSLFlip_rieszOp (restrict B K L) x']
    exact congrArg _ hxx')
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  obtain ⟨g, hg⟩ := innerSLFlip_surjective (F.comp L.subtypeL)
  obtain ⟨w, hw⟩ := hsurj g
  have hBw : restrict B K L w = F.comp L.subtypeL := by
    rw [← innerSLFlip_rieszOp]; exact (congrArg _ hw).trans hg
  refine ⟨w, ⟨w.2, fun v hv => ?_⟩, ?_⟩
  · have := congrArg (fun f => f ⟨v, hv⟩) hBw
    simpa using this
  · rintro y ⟨hy, hyF⟩
    have : restrict B K L ⟨y, hy⟩ = restrict B K L w :=
      ContinuousLinearMap.ext fun v => by
        rw [hBw, restrict_apply, hyF v v.2]; rfl
    exact congrArg Subtype.val (h.injective this)

end Feec.Variational

/-! ### Real bilinear forms as sesquilinear forms -/

namespace Feec.Variational

section Real

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- A real bilinear form seen as a sesquilinear form (`starRingEnd ℝ` is the identity). -/
def toSesq (B : X →L[ℝ] Y →L[ℝ] ℝ) : X →L[ℝ] Y →L⋆[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id ℝ) (starRingEnd ℝ) (fun x y => B x y)
      (fun x x' y => by simp) (fun a x y => by simp) (fun x y y' => by simp)
      (fun a x y => by simp))
    ‖B‖ fun x y => B.le_opNorm₂ x y

@[simp] theorem toSesq_apply (B : X →L[ℝ] Y →L[ℝ] ℝ) (x : X) (y : Y) : toSesq B x y = B x y :=
  rfl

/-- A real linear functional seen as an antilinear one. -/
def toAnti (f : Y →L[ℝ] ℝ) : Y →L⋆[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := f, map_add' := f.map_add, map_smul' := fun a y => by simp } ‖f‖ f.le_opNorm

@[simp] theorem toAnti_apply (f : Y →L[ℝ] ℝ) (y : Y) : toAnti f y = f y := rfl

theorem norm_toAnti (f : Y →L[ℝ] ℝ) : ‖toAnti f‖ = ‖f‖ :=
  le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => f.le_opNorm y)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => (toAnti f).le_opNorm y)

theorem toSesq_apply_eq (B : X →L[ℝ] Y →L[ℝ] ℝ) (x : X) : toSesq B x = toAnti (B x) := rfl

theorem norm_toSesq_apply (B : X →L[ℝ] Y →L[ℝ] ℝ) (x : X) : ‖toSesq B x‖ = ‖B x‖ :=
  norm_toAnti (B x)

theorem toAnti_injective : Function.Injective (toAnti : (Y →L[ℝ] ℝ) → Y →L⋆[ℝ] ℝ) :=
  fun f g h => ContinuousLinearMap.ext fun y => by
    simpa using congrArg (fun F => F y) h

theorem toAnti_surjective : Function.Surjective (toAnti : (Y →L[ℝ] ℝ) → Y →L⋆[ℝ] ℝ) := by
  intro F
  refine ⟨LinearMap.mkContinuous
    { toFun := F, map_add' := F.map_add, map_smul' := fun a y => by simp } ‖F‖ F.le_opNorm,
    ContinuousLinearMap.ext fun y => rfl⟩

end Real

end Feec.Variational

namespace Feec.Variational

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
  {B : X →L[𝕜] Y →L⋆[𝕜] 𝕜} {γ : ℝ}

/-- **The best inf-sup constant** is `‖B⁻¹‖⁻¹`: under inf-sup and separation, `γ' ≥ 0` is an
admissible constant iff `γ' ‖B⁻¹‖ ≤ 1`. [QuennevilleBelair2015], Thm 4.9, after [ArnoldNotes2011]. -/
theorem infSup_iff_mul_norm_symm_le (h : InfSup B γ) (hs : SeparatingRight B) {γ' : ℝ}
    (hγ' : 0 ≤ γ') :
    (∀ x, γ' * ‖x‖ ≤ ‖B x‖) ↔
      γ' * ‖((equivOfInfSup h hs).symm : (Y →L⋆[𝕜] 𝕜) →L[𝕜] X)‖ ≤ 1 := by
  set e := equivOfInfSup h hs
  constructor
  · intro hb
    rcases hγ'.lt_or_eq with hγ' | rfl
    · rw [← le_div_iff₀' hγ']
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
      have := hb (e.symm f)
      rw [show B (e.symm f) = e (e.symm f) from rfl, ContinuousLinearEquiv.apply_symm_apply]
        at this
      rw [ContinuousLinearEquiv.coe_coe, div_mul_eq_mul_div, one_mul, le_div_iff₀' hγ']
      exact this
    · simp
  · intro hb x
    calc γ' * ‖x‖ = γ' * ‖(e.symm : (Y →L⋆[𝕜] 𝕜) →L[𝕜] X) (e x)‖ := by simp
      _ ≤ γ' * (‖(e.symm : (Y →L⋆[𝕜] 𝕜) →L[𝕜] X)‖ * ‖e x‖) := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = (γ' * ‖(e.symm : (Y →L⋆[𝕜] 𝕜) →L[𝕜] X)‖) * ‖e x‖ := by ring
      _ ≤ 1 * ‖e x‖ := by gcongr
      _ = ‖B x‖ := one_mul _

end Feec.Variational

namespace Feec.Variational

theorem norm_toSesq_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (B : X →L[ℝ] Y →L[ℝ] ℝ) : ‖toSesq B‖ ≤ ‖B‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [norm_toSesq_apply]; exact B.le_opNorm x

end Feec.Variational

namespace Feec.Variational

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
  {B : X →L[𝕜] Y →L⋆[𝕜] 𝕜} {γ : ℝ}

/-- In Hilbert spaces the supremum of the inf-sup condition is attained, with the same constant:
`InfSup B γ ↔ ∀ x, ∃ y, ‖y‖ ≤ 1 ∧ γ ‖x‖ ≤ |B x y|`. This is the "equivalent" form of the inf-sup
condition in [QuennevilleBelair2015], §4.5, which follows [ArnoldNotes2011]. -/
theorem infSup_iff_forall_exists_norm_le_one (hγ : 0 < γ) :
    InfSup B γ ↔ ∀ x, ∃ y, ‖y‖ ≤ 1 ∧ γ * ‖x‖ ≤ ‖B x y‖ := by
  refine ⟨fun h x => ?_, InfSup.of_forall_exists_norm_le_one hγ⟩
  set v := rieszOp B x
  have hv : ‖v‖ = ‖B x‖ := norm_rieszOp_apply B x
  rcases eq_or_ne v 0 with h0 | h0
  · refine ⟨0, by simp, ?_⟩
    have := h.le x
    rw [← hv, h0, norm_zero] at this
    simpa using this
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 h0
    refine ⟨((‖v‖⁻¹ : ℝ) : 𝕜) • v, ?_, ?_⟩
    · rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hpos.ne']
    · have e : ‖B x (((‖v‖⁻¹ : ℝ) : 𝕜) • v)‖ = ‖v‖ := by
        rw [← inner_rieszOp, inner_smul_real_left, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_norm, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq,
          ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      rw [e, hv]; exact h.le x

end Feec.Variational
