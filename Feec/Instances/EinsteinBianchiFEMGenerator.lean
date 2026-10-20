module

public import Feec.HilbertComplex.BGG.TimeDependent
public import Feec.HilbertComplex.Approximation.ApproxFEEC
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The source-free scheme (6.3) as a skew bounded generator

The semi-discrete BGG system (6.3) of [QuennevilleBelair2015], §6.2, without source, is a
differential-algebraic system on the finite element spaces `Vₕ⁰ × Ṽₕ⁰ × Ṽₕ¹ × Vₕ² × Ṽₕ²` with a
multiplier `λₕ ∈ Vₕ¹`. Its solutions are the orbits of a skew operator on the **hidden-constraint
space** of energy states `(σ, u, M, ρ)` with `u ⊥ d̃(ker S₀,ₕ)`: eliminating `φₕ = Φ(σₕ, 0)`
(`Feec.BGG.phiMap`) and `λₕ = (S₀,ₕ*)⁻¹ d̃* uₕ` gives

`σ' = d* λ(u)`, `u' = -d̃ Φ(σ, 0) - S₁* M - d̃* ρ`, `M' = S₁ u`, `ρ' = d̃ u`.

This file makes this precise, for any BGG segment `D` of finite-dimensional inner product spaces
with `d̃ : Ṽₕ⁰ → Ṽₕ¹` injective and `S₀,ₕ` onto (the hypotheses of the corrected Prop 6.2).

## Main definitions and results

* `EState`: the energy space `Vₕ⁰ × Ṽₕ¹ × Vₕ² × Ṽₕ²` (`L²`-sum inner product), `hiddenSpace`,
  and its type `HiddenState` with instances fixed once (synthesis on concrete finite element
  spaces is expensive).
* `waveOp` (on all energy states, mapping into the hidden space, `waveOp_mem_hiddenSpace`) and the
  generator `waveGen : HiddenState D →L[ℝ] HiddenState D`, **skew** in the energy inner product
  (`waveGen_skew`), so `e^{t Lₕ}` is unitary.
* `DiscreteSolution.eq_group`: every solution of (6.3) without source is, on `[0, T]`, the orbit of
  `e^{t Lₕ}` from its initial energy state; `exists_discreteSolution_group`: every orbit from the
  hidden space is a solution of (6.3).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.3), Prop 6.2)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.BGG

/-! ### The energy space -/

/-- The discrete energy space `Vₕ⁰ × Ṽₕ¹ × Vₕ² × Ṽₕ²` with the `L²`-sum inner product. -/
abbrev EState (P0 Pt1 P2 Pt2 : Type*) [NormedAddCommGroup P0] [NormedAddCommGroup Pt1]
    [NormedAddCommGroup P2] [NormedAddCommGroup Pt2] : Type _ :=
  WithLp 2 (P0 × WithLp 2 (Pt1 × WithLp 2 (P2 × Pt2)))

section EState

variable {P0 Pt1 P2 Pt2 : Type*}
  [NormedAddCommGroup P0] [NormedAddCommGroup Pt1] [NormedAddCommGroup P2] [NormedAddCommGroup Pt2]

/-- The energy state `(σ, u, M, ρ)`. -/
def EState.mk (σ : P0) (u : Pt1) (M : P2) (ρ : Pt2) : EState P0 Pt1 P2 Pt2 :=
  WithLp.toLp 2 (σ, WithLp.toLp 2 (u, WithLp.toLp 2 (M, ρ)))

/-- The `σ` component. -/
def EState.σ (x : EState P0 Pt1 P2 Pt2) : P0 := (WithLp.ofLp x).1
/-- The `u` component. -/
def EState.u (x : EState P0 Pt1 P2 Pt2) : Pt1 := (WithLp.ofLp (WithLp.ofLp x).2).1
/-- The `M` component. -/
def EState.M (x : EState P0 Pt1 P2 Pt2) : P2 :=
  (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp x).2).2).1
/-- The `ρ` component. -/
def EState.ρ (x : EState P0 Pt1 P2 Pt2) : Pt2 :=
  (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp x).2).2).2

@[simp] theorem EState.σ_mk (σ : P0) (u : Pt1) (M : P2) (ρ : Pt2) :
    (EState.mk σ u M ρ).σ = σ := rfl
@[simp] theorem EState.u_mk (σ : P0) (u : Pt1) (M : P2) (ρ : Pt2) :
    (EState.mk σ u M ρ).u = u := rfl
@[simp] theorem EState.M_mk (σ : P0) (u : Pt1) (M : P2) (ρ : Pt2) :
    (EState.mk σ u M ρ).M = M := rfl
@[simp] theorem EState.ρ_mk (σ : P0) (u : Pt1) (M : P2) (ρ : Pt2) :
    (EState.mk σ u M ρ).ρ = ρ := rfl

theorem EState.mk_eta (x : EState P0 Pt1 P2 Pt2) : EState.mk x.σ x.u x.M x.ρ = x := rfl

theorem EState.ext {x y : EState P0 Pt1 P2 Pt2} (h1 : x.σ = y.σ) (h2 : x.u = y.u)
    (h3 : x.M = y.M) (h4 : x.ρ = y.ρ) : x = y := by
  rw [← EState.mk_eta x, ← EState.mk_eta y, h1, h2, h3, h4]

@[simp] theorem EState.σ_add (x y : EState P0 Pt1 P2 Pt2) : (x + y).σ = x.σ + y.σ := rfl
@[simp] theorem EState.u_add (x y : EState P0 Pt1 P2 Pt2) : (x + y).u = x.u + y.u := rfl
@[simp] theorem EState.M_add (x y : EState P0 Pt1 P2 Pt2) : (x + y).M = x.M + y.M := rfl
@[simp] theorem EState.ρ_add (x y : EState P0 Pt1 P2 Pt2) : (x + y).ρ = x.ρ + y.ρ := rfl
@[simp] theorem EState.σ_sub (x y : EState P0 Pt1 P2 Pt2) : (x - y).σ = x.σ - y.σ := rfl
@[simp] theorem EState.u_sub (x y : EState P0 Pt1 P2 Pt2) : (x - y).u = x.u - y.u := rfl
@[simp] theorem EState.M_sub (x y : EState P0 Pt1 P2 Pt2) : (x - y).M = x.M - y.M := rfl
@[simp] theorem EState.ρ_sub (x y : EState P0 Pt1 P2 Pt2) : (x - y).ρ = x.ρ - y.ρ := rfl
@[simp] theorem EState.σ_zero : (0 : EState P0 Pt1 P2 Pt2).σ = 0 := rfl
@[simp] theorem EState.u_zero : (0 : EState P0 Pt1 P2 Pt2).u = 0 := rfl
@[simp] theorem EState.M_zero : (0 : EState P0 Pt1 P2 Pt2).M = 0 := rfl
@[simp] theorem EState.ρ_zero : (0 : EState P0 Pt1 P2 Pt2).ρ = 0 := rfl

theorem EState.mk_add (σ σ' : P0) (u u' : Pt1) (M M' : P2) (ρ ρ' : Pt2) :
    EState.mk (σ + σ') (u + u') (M + M') (ρ + ρ') = EState.mk σ u M ρ + EState.mk σ' u' M' ρ' :=
  rfl

end EState

section EStateSMul

variable {P0 Pt1 P2 Pt2 : Type*}
  [NormedAddCommGroup P0] [NormedSpace ℝ P0]
  [NormedAddCommGroup Pt1] [NormedSpace ℝ Pt1]
  [NormedAddCommGroup P2] [NormedSpace ℝ P2]
  [NormedAddCommGroup Pt2] [NormedSpace ℝ Pt2]

@[simp] theorem EState.σ_smul (c : ℝ) (x : EState P0 Pt1 P2 Pt2) : (c • x).σ = c • x.σ := rfl
@[simp] theorem EState.u_smul (c : ℝ) (x : EState P0 Pt1 P2 Pt2) : (c • x).u = c • x.u := rfl
@[simp] theorem EState.M_smul (c : ℝ) (x : EState P0 Pt1 P2 Pt2) : (c • x).M = c • x.M := rfl
@[simp] theorem EState.ρ_smul (c : ℝ) (x : EState P0 Pt1 P2 Pt2) : (c • x).ρ = c • x.ρ := rfl

theorem EState.mk_smul (c : ℝ) (σ : P0) (u : Pt1) (M : P2) (ρ : Pt2) :
    EState.mk (c • σ) (c • u) (c • M) (c • ρ) = c • EState.mk σ u M ρ := rfl

end EStateSMul

section EStateInner

variable {P0 Pt1 P2 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]

/-- **The energy inner product**: `⟪x, y⟫ = ⟪σ, σ'⟫ + ⟪u, u'⟫ + ⟪M, M'⟫ + ⟪ρ, ρ'⟫`. -/
theorem EState.inner_def (x y : EState P0 Pt1 P2 Pt2) :
    ⟪x, y⟫ = ⟪x.σ, y.σ⟫ + ⟪x.u, y.u⟫ + ⟪x.M, y.M⟫ + ⟪x.ρ, y.ρ⟫ := by
  simp only [WithLp.prod_inner_apply, EState.σ, EState.u, EState.M, EState.ρ]
  ring

theorem EState.norm_sq (x : EState P0 Pt1 P2 Pt2) :
    ‖x‖ ^ 2 = ‖x.σ‖ ^ 2 + ‖x.u‖ ^ 2 + ‖x.M‖ ^ 2 + ‖x.ρ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EState.inner_def, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

end EStateInner

section EStateCalculus

variable {P0 Pt1 P2 Pt2 : Type*}
  [NormedAddCommGroup P0] [NormedSpace ℝ P0]
  [NormedAddCommGroup Pt1] [NormedSpace ℝ Pt1]
  [NormedAddCommGroup P2] [NormedSpace ℝ P2]
  [NormedAddCommGroup Pt2] [NormedSpace ℝ Pt2]

/-- `EState.mk` as a continuous linear equivalence. -/
def EState.mkL : (P0 × Pt1 × P2 × Pt2) ≃L[ℝ] EState P0 Pt1 P2 Pt2 :=
  ((ContinuousLinearEquiv.refl ℝ P0).prodCongr
    ((ContinuousLinearEquiv.refl ℝ Pt1).prodCongr
      (WithLp.prodContinuousLinearEquiv 2 ℝ P2 Pt2).symm |>.trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ Pt1 _).symm)).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ P0 _).symm

@[simp] theorem EState.mkL_apply (a : P0 × Pt1 × P2 × Pt2) :
    EState.mkL a = EState.mk a.1 a.2.1 a.2.2.1 a.2.2.2 := rfl

/-- A trajectory of energy states has the right derivative of its components. -/
theorem EState.hasDerivWithinAt_mk {σ : ℝ → P0} {u : ℝ → Pt1} {M : ℝ → P2} {ρ : ℝ → Pt2}
    {σ' : P0} {u' : Pt1} {M' : P2} {ρ' : Pt2} {s : Set ℝ} {t : ℝ}
    (hσ : HasDerivWithinAt σ σ' s t) (hu : HasDerivWithinAt u u' s t)
    (hM : HasDerivWithinAt M M' s t) (hρ : HasDerivWithinAt ρ ρ' s t) :
    HasDerivWithinAt (fun r => EState.mk (σ r) (u r) (M r) (ρ r)) (EState.mk σ' u' M' ρ') s t :=
  (EState.mkL (P0 := P0) (Pt1 := Pt1) (P2 := P2) (Pt2 := Pt2)).hasFDerivAt.comp_hasDerivWithinAt
    t (HasDerivWithinAt.prodMk hσ (HasDerivWithinAt.prodMk hu (HasDerivWithinAt.prodMk hM hρ)))

theorem EState.continuousOn_mk {σ : ℝ → P0} {u : ℝ → Pt1} {M : ℝ → P2} {ρ : ℝ → Pt2}
    {s : Set ℝ} (hσ : ContinuousOn σ s) (hu : ContinuousOn u s) (hM : ContinuousOn M s)
    (hρ : ContinuousOn ρ s) : ContinuousOn (fun r => EState.mk (σ r) (u r) (M r) (ρ r)) s :=
  (EState.mkL (P0 := P0) (Pt1 := Pt1) (P2 := P2) (Pt2 := Pt2)).continuous.comp_continuousOn
    (hσ.prodMk (hu.prodMk (hM.prodMk hρ)))

end EStateCalculus

section EStateMap

variable {P0 Pt1 P2 Pt2 Q0 Qt1 Q2 Qt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  [NormedAddCommGroup Q0] [InnerProductSpace ℝ Q0]
  [NormedAddCommGroup Qt1] [InnerProductSpace ℝ Qt1]
  [NormedAddCommGroup Q2] [InnerProductSpace ℝ Q2]
  [NormedAddCommGroup Qt2] [InnerProductSpace ℝ Qt2]

/-- The componentwise map of energy states. -/
def EState.mapL (f0 : P0 →L[ℝ] Q0) (f1 : Pt1 →L[ℝ] Qt1) (f2 : P2 →L[ℝ] Q2) (f3 : Pt2 →L[ℝ] Qt2) :
    EState P0 Pt1 P2 Pt2 →L[ℝ] EState Q0 Qt1 Q2 Qt2 :=
  EState.mkL.toContinuousLinearMap ∘L (f0.prodMap (f1.prodMap (f2.prodMap f3))) ∘L
    EState.mkL.symm.toContinuousLinearMap

@[simp] theorem EState.mapL_apply (f0 : P0 →L[ℝ] Q0) (f1 : Pt1 →L[ℝ] Qt1) (f2 : P2 →L[ℝ] Q2)
    (f3 : Pt2 →L[ℝ] Qt2) (x : EState P0 Pt1 P2 Pt2) :
    EState.mapL f0 f1 f2 f3 x = EState.mk (f0 x.σ) (f1 x.u) (f2 x.M) (f3 x.ρ) := rfl

/-- Componentwise isometries give an isometry of energy states. -/
theorem EState.norm_mapL {f0 : P0 →L[ℝ] Q0} {f1 : Pt1 →L[ℝ] Qt1} {f2 : P2 →L[ℝ] Q2}
    {f3 : Pt2 →L[ℝ] Qt2} (h0 : ∀ x, ‖f0 x‖ = ‖x‖) (h1 : ∀ x, ‖f1 x‖ = ‖x‖)
    (h2 : ∀ x, ‖f2 x‖ = ‖x‖) (h3 : ∀ x, ‖f3 x‖ = ‖x‖) (x : EState P0 Pt1 P2 Pt2) :
    ‖EState.mapL f0 f1 f2 f3 x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EState.norm_sq, EState.norm_sq,
    EState.mapL_apply,
    EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk, h0, h1, h2, h3]

end EStateMap

/-! ### The hidden-constraint space -/

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  (D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2)

/-- The **hidden-constraint space** (C2) of (6.3): energy states with `u ⊥ d̃(ker S₀,ₕ)`. Every
solution of (6.3) lies in it (`Feec.BGG.DiscreteSolution.hidden_constraint`). -/
def hiddenSpace : Submodule ℝ (EState P0 Pt1 P2 Pt2) where
  carrier := {x | ∀ ψ, D.S0 ψ = 0 → ⟪x.u, D.dt0 ψ⟫ = 0}
  add_mem' {x y} hx hy ψ hψ := by
    rw [EState.u_add, inner_add_left, hx ψ hψ, hy ψ hψ, add_zero]
  zero_mem' ψ _ := by rw [EState.u_zero, inner_zero_left]
  smul_mem' c x hx ψ hψ := by
    rw [EState.u_smul, real_inner_smul_left, hx ψ hψ, mul_zero]

theorem mem_hiddenSpace {x : EState P0 Pt1 P2 Pt2} :
    x ∈ hiddenSpace D ↔ ∀ ψ, D.S0 ψ = 0 → ⟪x.u, D.dt0 ψ⟫ = 0 := Iff.rfl

/-- The hidden space as a type whose instances are fixed once, generically. -/
def HiddenState : Type _ := hiddenSpace D

instance HiddenState.instNormedAddCommGroup : NormedAddCommGroup (HiddenState D) :=
  Submodule.normedAddCommGroup _

instance HiddenState.instInnerProductSpace : InnerProductSpace ℝ (HiddenState D) :=
  Submodule.innerProductSpace _

variable {D} in
/-- The underlying energy state. -/
def HiddenState.toEState (x : HiddenState D) : EState P0 Pt1 P2 Pt2 :=
  ((show hiddenSpace D from x : hiddenSpace D) : EState P0 Pt1 P2 Pt2)

variable {D} in
theorem HiddenState.toEState_mem (x : HiddenState D) : x.toEState ∈ hiddenSpace D :=
  (show hiddenSpace D from x).2

variable {D} in
/-- A hidden energy state as a point of `HiddenState`. -/
def HiddenState.mk (x : EState P0 Pt1 P2 Pt2) (hx : x ∈ hiddenSpace D) : HiddenState D :=
  (⟨x, hx⟩ : hiddenSpace D)

@[simp] theorem HiddenState.toEState_mk (x : EState P0 Pt1 P2 Pt2) (hx : x ∈ hiddenSpace D) :
    (HiddenState.mk x hx).toEState = x := rfl

/-- The isometric inclusion into the energy space. -/
def HiddenState.subtypeL : HiddenState D →L[ℝ] EState P0 Pt1 P2 Pt2 :=
  (hiddenSpace D).subtypeL

@[simp] theorem HiddenState.subtypeL_apply (x : HiddenState D) :
    HiddenState.subtypeL D x = x.toEState := rfl

variable {D} in
theorem HiddenState.toEState_injective :
    Function.Injective (HiddenState.toEState (D := D)) :=
  Subtype.val_injective

variable {D} in
@[simp] theorem HiddenState.toEState_add (x y : HiddenState D) :
    (x + y).toEState = x.toEState + y.toEState := rfl

variable {D} in
@[simp] theorem HiddenState.toEState_sub (x y : HiddenState D) :
    (x - y).toEState = x.toEState - y.toEState := rfl

variable {D} in
@[simp] theorem HiddenState.toEState_zero : (0 : HiddenState D).toEState = 0 := rfl

variable {D} in
@[simp] theorem HiddenState.toEState_smul (c : ℝ) (x : HiddenState D) :
    (c • x).toEState = c • x.toEState := rfl

variable {D} in
theorem HiddenState.inner_toEState (x y : HiddenState D) :
    ⟪x.toEState, y.toEState⟫ = ⟪x, y⟫ := rfl

variable {D} in
theorem HiddenState.norm_toEState (x : HiddenState D) : ‖x.toEState‖ = ‖x‖ := rfl

theorem HiddenState.norm_subtypeL (x : HiddenState D) : ‖HiddenState.subtypeL D x‖ = ‖x‖ := rfl

/-! ### Energy states of solutions of (6.3) -/

/-- The energy state of a solution of (6.3) at time `t`. -/
def DiscreteSolution.state {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f) (t : ℝ) :
    EState P0 Pt1 P2 Pt2 :=
  EState.mk (s.σ t) (s.u t) (s.M t) (s.ρ t)

variable {D} in
theorem DiscreteSolution.state_mem {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f) {t : ℝ}
    (ht : t ∈ Icc 0 T) : DiscreteSolution.state D s t ∈ hiddenSpace D := fun _ hψ =>
  s.hidden_constraint ht hψ

variable {D} in
theorem DiscreteSolution.continuousOn_state {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f) :
    ContinuousOn (DiscreteSolution.state D s) (Icc 0 T) :=
  EState.continuousOn_mk s.cσ s.cu s.cM s.cρ

variable {D} in
/-- The initial hidden state of a solution of (6.3). -/
def DiscreteSolution.hiddenInit {T : ℝ} (hT : 0 ≤ T) {f : ℝ → Pt1} (s : DiscreteSolution D T f) :
    HiddenState D :=
  HiddenState.mk _ (DiscreteSolution.state_mem s ⟨le_rfl, hT⟩)

section FiniteDimensional

variable [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P1] [FiniteDimensional ℝ P2]
  [FiniteDimensional ℝ Pt0] [FiniteDimensional ℝ Pt1] [FiniteDimensional ℝ Pt2]

/-- Explicit instance: synthesis is expensive on concrete finite element spaces. -/
instance EState.finiteDimensional : FiniteDimensional ℝ (EState P0 Pt1 P2 Pt2) :=
  inferInstance

instance hiddenSpace.completeSpace : CompleteSpace (hiddenSpace D) :=
  FiniteDimensional.complete ℝ _

instance HiddenState.instCompleteSpace : CompleteSpace (HiddenState D) :=
  hiddenSpace.completeSpace D

instance HiddenState.instFiniteDimensional : FiniteDimensional ℝ (HiddenState D) :=
  FiniteDimensional.finiteDimensional_submodule (hiddenSpace D)

/-! ### The generator -/

variable (hdinj : Function.Injective D.dt0) (hS : Function.Surjective D.S0)

/-- A left inverse of `S₀,ₕ*` (injective since `S₀,ₕ` is onto). -/
def adjS0Inv : Pt0 →ₗ[ℝ] P1 :=
  (LinearMap.exists_leftInverse_of_injective (LinearMap.adjoint D.S0)
    (LinearMap.ker_eq_bot.mpr (adjoint_S0_injective hS))).choose

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt1]
  [FiniteDimensional ℝ Pt2] in
theorem adjS0Inv_adjoint (μ : P1) : adjS0Inv D hS (LinearMap.adjoint D.S0 μ) = μ :=
  LinearMap.congr_fun (LinearMap.exists_leftInverse_of_injective (LinearMap.adjoint D.S0)
    (LinearMap.ker_eq_bot.mpr (adjoint_S0_injective hS))).choose_spec μ

/-- The multiplier of an energy state, `λ(u) = (S₀,ₕ*)⁻¹ d̃* u`. -/
def lamMap : Pt1 →ₗ[ℝ] P1 := adjS0Inv D hS ∘ₗ LinearMap.adjoint D.dt0

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
/-- On hidden states, `S₀,ₕ* λ(u) = d̃* u`. -/
theorem adjoint_S0_lamMap {u : Pt1} (hu : ∀ ψ, D.S0 ψ = 0 → ⟪u, D.dt0 ψ⟫ = 0) :
    LinearMap.adjoint D.S0 (lamMap D hS u) = LinearMap.adjoint D.dt0 u := by
  obtain ⟨μ, hμ⟩ := exists_adjoint_S0 (D := D) (z := LinearMap.adjoint D.dt0 u) fun ψ hψ => by
    rw [LinearMap.adjoint_inner_left]; exact hu ψ hψ
  change LinearMap.adjoint D.S0 (adjS0Inv D hS (LinearMap.adjoint D.dt0 u)) = _
  rw [← hμ, adjS0Inv_adjoint]

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
/-- The multiplier is the one of (6.3a): `λ` with `S₀,ₕ* λ = d̃* u` is `λ(u)`. -/
theorem lamMap_eq {u : Pt1} {μ : P1} (h : LinearMap.adjoint D.S0 μ = LinearMap.adjoint D.dt0 u) :
    lamMap D hS u = μ := by
  change adjS0Inv D hS (LinearMap.adjoint D.dt0 u) = μ
  rw [← h, adjS0Inv_adjoint]

/-- `σ ↦ Φ(σ, 0)`. -/
def phi0 : P0 →ₗ[ℝ] Pt0 := phiMap D hdinj hS ∘ₗ LinearMap.inl ℝ P0 Pt1

omit [FiniteDimensional ℝ P0] [FiniteDimensional ℝ P2] [FiniteDimensional ℝ Pt2] in
theorem phi0_apply (σ : P0) : phi0 D hdinj hS σ = phiMap D hdinj hS (σ, 0) := rfl

/-- **The operator of (6.3) without source** on all energy states:
`(σ, u, M, ρ) ↦ (d* λ(u), -d̃ Φ(σ, 0) - S₁* M - d̃* ρ, S₁ u, d̃ u)`. -/
def waveOp : EState P0 Pt1 P2 Pt2 →ₗ[ℝ] EState P0 Pt1 P2 Pt2 where
  toFun x := EState.mk (LinearMap.adjoint D.d0 (lamMap D hS x.u))
    (-D.dt0 (phi0 D hdinj hS x.σ) - LinearMap.adjoint D.S1 x.M -
      LinearMap.adjoint D.dt1 x.ρ) (D.S1 x.u) (D.dt1 x.u)
  map_add' x y := by
    rw [← EState.mk_add]
    simp only [EState.u_add, EState.σ_add, EState.M_add, EState.ρ_add, map_add]
    congr 1
    abel
  map_smul' c x := by
    rw [RingHom.id_apply, ← EState.mk_smul]
    simp only [EState.u_smul, EState.σ_smul, EState.M_smul, EState.ρ_smul, map_smul,
      smul_sub, smul_neg]

@[simp] theorem waveOp_σ (x : EState P0 Pt1 P2 Pt2) :
    (waveOp D hdinj hS x).σ = LinearMap.adjoint D.d0 (lamMap D hS x.u) := rfl
@[simp] theorem waveOp_u (x : EState P0 Pt1 P2 Pt2) :
    (waveOp D hdinj hS x).u = -D.dt0 (phiMap D hdinj hS (x.σ, 0)) -
      LinearMap.adjoint D.S1 x.M - LinearMap.adjoint D.dt1 x.ρ := rfl
@[simp] theorem waveOp_M (x : EState P0 Pt1 P2 Pt2) : (waveOp D hdinj hS x).M = D.S1 x.u := rfl
@[simp] theorem waveOp_ρ (x : EState P0 Pt1 P2 Pt2) : (waveOp D hdinj hS x).ρ = D.dt1 x.u := rfl

/-- `waveOp` maps every energy state into the hidden space: `d̃Φ(σ, 0) ⊥ d̃(ker S₀,ₕ)`,
`S₁ d̃ = 0` on `ker S₀,ₕ` and `d̃ d̃ = 0`. -/
theorem waveOp_mem_hiddenSpace (x : EState P0 Pt1 P2 Pt2) :
    waveOp D hdinj hS x ∈ hiddenSpace D := fun ψ hψ => by
  rw [waveOp_u, inner_sub_left, inner_sub_left, inner_neg_left, inner_phiMap hdinj hS _ hψ,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, D.S1_dt0_eq_zero hψ,
    D.dt1_dt0, inner_zero_right, inner_zero_right, inner_zero_left]
  ring

/-- The pairing of `waveOp` on hidden states: `⟪L x, y⟫ = ⟪u, d̃Φ_y⟫ - ⟪d̃Φ_x, u'⟫ - ⟪M, S₁u'⟫
- ⟪ρ, d̃u'⟫ + ⟪S₁u, M'⟫ + ⟪d̃u, ρ'⟫` (antisymmetric in `x`, `y`). -/
theorem inner_waveOp {x y : EState P0 Pt1 P2 Pt2} (hx : x ∈ hiddenSpace D) :
    ⟪waveOp D hdinj hS x, y⟫ = ⟪x.u, D.dt0 (phiMap D hdinj hS (y.σ, 0))⟫ -
      ⟪D.dt0 (phiMap D hdinj hS (x.σ, 0)), y.u⟫ - ⟪x.M, D.S1 y.u⟫ - ⟪x.ρ, D.dt1 y.u⟫ +
        ⟪D.S1 x.u, y.M⟫ + ⟪D.dt1 x.u, y.ρ⟫ := by
  rw [EState.inner_def, waveOp_σ, waveOp_u, waveOp_M, waveOp_ρ, LinearMap.adjoint_inner_left,
    ← S0_phiMap hdinj hS (y.σ, (0 : Pt1)), ← LinearMap.adjoint_inner_left,
    adjoint_S0_lamMap D hS hx, LinearMap.adjoint_inner_left, inner_sub_left, inner_sub_left,
    inner_neg_left, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  ring

/-- `waveOp` is skew on the hidden space. -/
theorem waveOp_skew {x y : EState P0 Pt1 P2 Pt2} (hx : x ∈ hiddenSpace D)
    (hy : y ∈ hiddenSpace D) : ⟪waveOp D hdinj hS x, y⟫ = -⟪x, waveOp D hdinj hS y⟫ := by
  rw [inner_waveOp D hdinj hS hx, real_inner_comm (waveOp D hdinj hS y) x,
    inner_waveOp D hdinj hS hy]
  rw [real_inner_comm (D.dt0 _) x.u, real_inner_comm y.u (D.dt0 _), real_inner_comm x.M,
    real_inner_comm x.ρ, real_inner_comm (D.S1 x.u), real_inner_comm (D.dt1 x.u)]
  ring

theorem inner_waveOp_self {x : EState P0 Pt1 P2 Pt2} (hx : x ∈ hiddenSpace D) :
    ⟪waveOp D hdinj hS x, x⟫ = 0 := by
  have h := waveOp_skew D hdinj hS hx hx
  rw [real_inner_comm (waveOp D hdinj hS x) x] at h
  linarith

/-- **The discrete generator** of (6.3) without source, on the hidden space. -/
def waveGen : HiddenState D →L[ℝ] HiddenState D :=
  LinearMap.toContinuousLinearMap
    ((waveOp D hdinj hS).restrict (p := hiddenSpace D) (q := hiddenSpace D)
      fun x _ => waveOp_mem_hiddenSpace D hdinj hS x)

theorem waveGen_toEState (x : HiddenState D) :
    (waveGen D hdinj hS x).toEState = waveOp D hdinj hS x.toEState := rfl

/-- **The discrete generator is skew** in the energy inner product. -/
theorem waveGen_skew (x y : HiddenState D) :
    ⟪waveGen D hdinj hS x, y⟫ = -⟪x, waveGen D hdinj hS y⟫ := by
  rw [← HiddenState.inner_toEState, ← HiddenState.inner_toEState, waveGen_toEState,
    waveGen_toEState]
  exact waveOp_skew D hdinj hS x.toEState_mem y.toEState_mem

/-- The group `e^{t Lₕ}` of the discrete generator. -/
abbrev waveGroupH : C0Group ℝ (HiddenState D) := C0Group.ofBounded (waveGen D hdinj hS)

theorem hasDerivAt_waveGroupH (v : HiddenState D) (t : ℝ) :
    HasDerivAt (fun s => ((waveGroupH D hdinj hS).S s v).toEState)
      (waveOp D hdinj hS ((waveGroupH D hdinj hS).S t v).toEState) t :=
  (HiddenState.subtypeL D).hasFDerivAt.comp_hasDerivAt t
    (C0Group.hasDerivAt_exp_ofReal_smul_apply (waveGen D hdinj hS) v t)

/-! ### Solutions of (6.3) are the orbits of the generator -/

variable {D}

/-- **A solution of (6.3) without source solves `ξ' = Lₕ ξ`** (right derivatives on `[0, T)`):
`σ' = d* λ` with `λ = λ(u)` from (6.3a), `φ = Φ(σ, 0)` (`Feec.BGG.DiscreteSolution.phi_eq`),
and (6.3b)–(6.3d). -/
theorem DiscreteSolution.hasDerivWithinAt_state {T : ℝ} (s : DiscreteSolution D T 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (DiscreteSolution.state D s)
      (waveOp D hdinj hS (DiscreteSolution.state D s t)) (Ici t) t := by
  have ht' := Ico_subset_Icc_self ht
  have hlam : LinearMap.adjoint D.S0 (s.lam t) = LinearMap.adjoint D.dt0 (s.u t) := by
    refine ext_inner_right ℝ fun ψ => ?_
    have h := s.ea t ht' 0 ψ
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
    simp only [map_zero, inner_zero_right, zero_sub, inner_neg_right, sub_neg_eq_add] at h
    linarith
  have hσ' : s.σ' t = LinearMap.adjoint D.d0 (lamMap D hS (s.u t)) := by
    rw [lamMap_eq D hS hlam]
    refine ext_inner_right ℝ fun τ => ?_
    have h := s.ea t ht' τ 0
    rw [LinearMap.adjoint_inner_left]
    simp only [map_zero, inner_zero_right, sub_zero] at h
    linarith
  have hφ : s.φ t = phiMap D hdinj hS (s.σ t, 0) := DiscreteSolution.phi_eq hdinj hS s ht
  have hu' : s.u' t = -D.dt0 (phiMap D hdinj hS (s.σ t, 0)) -
      LinearMap.adjoint D.S1 (s.M t) - LinearMap.adjoint D.dt1 (s.ρ t) := by
    refine ext_inner_right ℝ fun v => ?_
    have h := s.eb t ht v
    rw [hφ] at h
    simp only [Pi.zero_apply, inner_zero_left] at h
    rw [inner_sub_left, inner_sub_left, inner_neg_left, LinearMap.adjoint_inner_left,
      LinearMap.adjoint_inner_left]
    linarith
  have hM' : s.M' t = D.S1 (s.u t) := by
    refine ext_inner_right ℝ fun N => ?_
    have h := s.ec t ht N
    linarith
  have hρ' : s.ρ' t = D.dt1 (s.u t) := by
    refine ext_inner_right ℝ fun μ => ?_
    have h := s.ed t ht μ
    linarith
  have h := EState.hasDerivWithinAt_mk (s.dσ t ht) (s.du t ht) (s.dM t ht) (s.dρ t ht)
  rw [hσ', hu', hM', hρ'] at h
  exact h

/-- **Every solution of (6.3) without source is the orbit of `e^{t Lₕ}`** from its initial energy
state, on `[0, T]` (energy argument: the difference has right derivative `Lₕ e`, and
`⟪Lₕ e, e⟫ = 0`). -/
theorem DiscreteSolution.eq_group {T : ℝ} (hT : 0 ≤ T) (s : DiscreteSolution D T 0) :
    ∀ t ∈ Icc 0 T, ((waveGroupH D hdinj hS).S t (DiscreteSolution.hiddenInit hT s)).toEState =
      DiscreteSolution.state D s t := by
  set v := DiscreteSolution.hiddenInit hT s
  set q : ℝ → EState P0 Pt1 P2 Pt2 := fun r => ((waveGroupH D hdinj hS).S r v).toEState
  set e : ℝ → EState P0 Pt1 P2 Pt2 := fun r => DiscreteSolution.state D s r - q r
  have hq : ∀ r, HasDerivAt q (waveOp D hdinj hS (q r)) r := hasDerivAt_waveGroupH D hdinj hS v
  have hec : ContinuousOn e (Icc 0 T) :=
    (DiscreteSolution.continuousOn_state s).sub fun r _ => (hq r).continuousAt.continuousWithinAt
  have hed : ∀ r ∈ Ico 0 T, HasDerivWithinAt e (waveOp D hdinj hS (e r)) (Ici r) r := fun r hr => by
    have h := (DiscreteSolution.hasDerivWithinAt_state hdinj hS s hr).sub (hq r).hasDerivWithinAt
    rw [← map_sub] at h
    exact h
  have hemem : ∀ r ∈ Icc 0 T, e r ∈ hiddenSpace D := fun r hr =>
    (hiddenSpace D).sub_mem (DiscreteSolution.state_mem s hr) ((waveGroupH D hdinj hS).S r v).2
  have hg : ∀ r ∈ Ico 0 T, HasDerivWithinAt (fun r => ‖e r‖ ^ 2) 0 (Ici r) r := fun r hr => by
    have h := (hed r hr).norm_sq
    rw [real_inner_comm, inner_waveOp_self D hdinj hS (hemem r (Ico_subset_Icc_self hr)),
      mul_zero] at h
    exact h
  have hconst := constant_of_has_deriv_right_zero (hec.norm.pow 2) hg
  intro t ht
  have h0 : e 0 = 0 := by
    simp only [e, q, v, C0Group.S_zero_apply, sub_eq_zero]
    rfl
  have := hconst t ht
  simp only [Pi.pow_apply, h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, pow_eq_zero_iff, norm_eq_zero] at this
  exact (sub_eq_zero.1 this).symm

/-- **Every orbit of `e^{t Lₕ}` from the hidden space is a solution of (6.3) without source**
(existence by the corrected Prop 6.2, `Feec.BGG.exists_discreteSolution_iff_compatible_u`, and
identification by `DiscreteSolution.eq_group`). -/
theorem exists_discreteSolution_group {T : ℝ} (hT : 0 < T) (v : HiddenState D) :
    ∃ s : DiscreteSolution D T 0, DiscreteSolution.hiddenInit hT.le s = v ∧
      ∀ t ∈ Icc 0 T, ((waveGroupH D hdinj hS).S t v).toEState = DiscreteSolution.state D s t := by
  obtain ⟨s, hσ, hu, hM, hρ⟩ := (exists_discreteSolution_iff_compatible_u hT hdinj hS
    (f := 0) continuousOn_const v.toEState.σ v.toEState.u v.toEState.M v.toEState.ρ).2
    v.toEState_mem
  have hv : DiscreteSolution.hiddenInit hT.le s = v := by
    apply HiddenState.toEState_injective
    change EState.mk (s.σ 0) (s.u 0) (s.M 0) (s.ρ 0) = v.toEState
    rw [hσ, hu, hM, hρ, EState.mk_eta]
  refine ⟨s, hv, fun t ht => ?_⟩
  rw [← hv]
  exact DiscreteSolution.eq_group hdinj hS hT.le s t ht

end FiniteDimensional

end Feec.Instances.EinsteinBianchi.FEM
