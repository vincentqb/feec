module

public import Feec.Models.Cube.RowWiseIdent
public import Feec.Models.BoundedDomain.Density

/-!
# Only static data propagate on the cube with the thesis' boundary conditions

For the parity model `Feec.Models.Cube.Parity.complex` and `K = {0} × S₁ × S₂`, with `S₁`, `S₂`
closed and made of parity fields symmetric and trace-free on the cube, forward invariance of `K`
forces stationarity, and the stationary data of `{0} × L²(TSD) × L²(TSD)` are infinite-dimensional.

## Main results

* `Parity.forward_torus_iff`, `Parity.forward_iff`: forward invariance of `K` forces stationarity.
* `Parity.forward_tsd_iff`: for `{0} × L²(TSD) × L²(TSD)`, only the curl-free `(0, 0, B₀)`.
* `Parity.totalJ_mem_invariantCore`: the parity extension maps `K*` on `Q` into `K*` of the model.
* `Parity.not_finiteDimensional_invariantCore`: this `K*` is infinite-dimensional.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate
open Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace Feec.Models.Cube.Parity

open Feec.Models.Torus.GradCurl (Space)
open Models.BoundedDomain (R3 Ix tsd)
open HilbertComplex (totalSub totalJ)
open ShortHilbertComplex (W3 family3 inj₂ mem_totalSub_family3)
open RowWise (WQ J cubeComplex ofRealF ofRealL)
open Geometry (Q)
open Fourier.GradCurl (curl)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-! ### Forward invariance -/

/-- [QuennevilleBelair2015], Prop 4.17 (adapted), torus side: for `S₁`, `S₂` as in
`mem_invariantCore_torus_iff`, `S t y ∈ K` for all `t ≥ 0` iff `y ∈ K` is stationary. -/
theorem forward_torus_iff {S1 : Submodule ℝ (Space 1)} {S2 : Submodule ℝ (Space 2)}
    [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]
    (hS1 : S1 ≤ rowAction.fixed 1 ⊓ boxSym ⊓ boxTr) (hS2 : S2 ≤ rowAction.fixed 2 ⊓ boxSym ⊓ boxTr)
    (y : PiLp 2 Space) :
    (∀ t, 0 ≤ t → RealTorus.gradCurl.waveGroup.S t y ∈ totalSub (constraint S1 S2)) ↔
      y ∈ totalSub (constraint S1 S2) ∧ y ∈ RealTorus.gradCurl.waveGroup.stationary := by
  refine ⟨fun h => (mem_invariantCore_torus_iff hS1 hS2 y).1
    (RealTorus.gradCurl.isIsometric_waveGroup.mem_invariantCore_of_forward_invariant
      isPurePoint_torus HilbertComplex.isClosed_totalSub h), fun ⟨hK, hs⟩ t _ => ?_⟩
  rw [C0Group.mem_stationary.1 hs t]; exact hK

/-- [QuennevilleBelair2015], Prop 4.17 (adapted), on the cube: for `S₁`, `S₂` as in
`mem_invariantCore_iff`, `S t y ∈ K` for all `t ≥ 0` iff `y ∈ K` is stationary. -/
theorem forward_iff {S1 : Submodule ℝ (Space 1)} {S2 : Submodule ℝ (Space 2)}
    [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]
    (hS1 : S1 ≤ rowAction.fixed 1 ⊓ boxSym ⊓ boxTr) (hS2 : S2 ≤ rowAction.fixed 2 ⊓ boxSym ⊓ boxTr)
    (y : PiLp 2 fun i => rowAction.fixed i) :
    (∀ t, 0 ≤ t → complex.waveGroup.S t y ∈ totalSub (compSub rowAction.fixed (constraint S1 S2))) ↔
      y ∈ totalSub (compSub rowAction.fixed (constraint S1 S2)) ∧
        y ∈ complex.waveGroup.stationary := by
  rw [forward_compSub_iff, forward_torus_iff hS1 hS2, mem_stationary_compSub_iff]
  rfl

/-- **Forward invariance of `K = {0} × L²(TSD) × L²(TSD)`** ([QuennevilleBelair2015], Prop 4.17
(adapted)): the forward orbit of `y` stays in `K` iff `y = (0, 0, B₀)`, `B₀ ∈ L²(TSD)` curl-free. -/
theorem forward_tsd_iff (y : PiLp 2 Space) :
    (∀ t, 0 ≤ t → RealTorus.gradCurl.waveGroup.S t y ∈ totalSub (constraint tsdE tsdB)) ↔
      (y 0 : Space 0) = 0 ∧ (y 1 : Space 1) = 0 ∧ (y 2 : Space 2) ∈ tsdB ∧
        ∀ n, curl (Fourier.Torus.freq n) ((y 2 : Space 2) n) = 0 := by
  rw [← mem_invariantCore_tsd_iff]
  exact ⟨RealTorus.gradCurl.isIsometric_waveGroup.mem_invariantCore_of_forward_invariant
    isPurePoint_torus HilbertComplex.isClosed_totalSub,
    fun h t _ => C0Group.mem_invariantCore.1 h t⟩

/-! ### `L²(TSD)` on `Q` in the parity model -/

theorem fderiv_re {f : R3 → ℂ} (hf : Differentiable ℝ f) (x v : R3) :
    fderiv ℝ (fun y => (f y).re) x v = (fderiv ℝ f x v).re := by
  have h := (Complex.reCLM.hasFDerivAt (x := f x)).comp x (hf x).hasFDerivAt
  rw [show (fun y => (f y).re) = Complex.reCLM ∘ f from rfl, h.fderiv]
  rfl

theorem fderiv_im {f : R3 → ℂ} (hf : Differentiable ℝ f) (x v : R3) :
    fderiv ℝ (fun y => (f y).im) x v = (fderiv ℝ f x v).im := by
  have h := (Complex.imCLM.hasFDerivAt (x := f x)).comp x (hf x).hasFDerivAt
  rw [show (fun y => (f y).im) = Complex.imCLM ∘ f from rfl, h.fderiv]
  rfl

theorem inner_ofRealF {P : Type*} [Fintype P] (f g : Domain.L2F ℝ (Q (Fin 3)) P) :
    ⟪ofRealF f, ofRealF g⟫_ℂ = (⟪f, g⟫_ℝ : ℂ) := by
  rw [Domain.L2F.inner_def, Domain.L2F.inner_def, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun p _ => RowWise.inner_ofRealL (f p) (g p)

theorem inner_testField_grad_ofRealF {u : Domain.L2F ℝ (Q (Fin 3)) Ix}
    (hu : ∀ ψ : Fin 3 → R3 → ℝ, ∀ hψ : Domain.IsTestField (Q (Fin 3)) ψ,
      ⟪u, Domain.testField
        ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ _ _).isTestField_apply hψ)⟫_ℝ = 0)
    {φ : Fin 3 → R3 → ℂ} (hφ : Domain.IsTestField (Q (Fin 3)) φ) :
    ⟪Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ),
      ofRealF u⟫_ℂ = 0 := by
  set φr : Fin 3 → R3 → ℝ := fun a x => (φ a x).re
  set φi : Fin 3 → R3 → ℝ := fun a x => (φ a x).im
  have hr : Domain.IsTestField (Q (Fin 3)) φr := fun a => (hφ a).comp_clm Complex.reCLM
  have hi : Domain.IsTestField (Q (Fin 3)) φi := fun a => (hφ a).comp_clm Complex.imCLM
  set gr := Domain.testField
    ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ _ _).isTestField_apply hr)
  set gi := Domain.testField
    ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ _ _).isTestField_apply hi)
  have key : Domain.testField
      ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ) =
      ofRealF gr + Complex.I • ofRealF gi := by
    refine (Domain.eq_testField _ fun p => ?_).symm
    filter_upwards [Lp.coeFn_add (ofRealF gr p) (Complex.I • ofRealF gi p),
      Lp.coeFn_smul Complex.I (ofRealF gi p), RowWise.coeFn_ofRealL (gr p),
      RowWise.coeFn_ofRealL (gi p), Domain.coeFn_testField
        ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ _ _).isTestField_apply hr) p,
      Domain.coeFn_testField
        ((Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ _ _).isTestField_apply hi) p] with
      x h1 h2 h3 h4 h5 h6
    change ((ofRealF gr + Complex.I • ofRealF gi) p : R3 → ℂ) x = _
    rw [PiLp.add_apply, PiLp.smul_apply, h1, Pi.add_apply, h2, Pi.smul_apply,
      RowWise.ofRealF_apply, RowWise.ofRealF_apply, h3, h4, h5, h6, Domain.gradOp_apply,
      Domain.gradOp_apply, Domain.gradOp_apply, fderiv_re (hφ p.1).differentiable,
      fderiv_im (hφ p.1).differentiable, smul_eq_mul,
      mul_comm, Complex.re_add_im]
  rw [key, inner_add_left, inner_smul_left, inner_ofRealF, inner_ofRealF, real_inner_comm u gr,
    real_inner_comm u gi, hu φr hr, hu φi hi]
  simp

theorem JR_mem_boxDiv {pc : Ix → Fin 3 → ℂ} {u : Domain.L2F ℝ (Q (Fin 3)) Ix}
    (hu : u ∈ tsd (Q (Fin 3))) : (RowWise.JR pc u : MatL) ∈ boxDiv :=
  mem_boxDiv.2 fun _ hφ => by rw [RowWise.resM_JR]; exact inner_testField_grad_ofRealF hu.2.2 hφ

theorem J_one_mem_tsdE {u : WQ 1} (hu : u ∈ tsd (Q (Fin 3))) : J 1 u ∈ tsdE :=
  ⟨RowWise.J_one_mem_of_tsd hu, JR_mem_boxDiv hu⟩

theorem J_two_mem_tsdB {u : WQ 2} (hu : u ∈ tsd (Q (Fin 3))) : J 2 u ∈ tsdB :=
  ⟨RowWise.J_two_mem_of_tsd hu, JR_mem_boxDiv hu⟩

/-- **`K*` on `Q` extends to `K*` of the parity model** under the parity extension. -/
theorem totalJ_mem_invariantCore {y : PiLp 2 WQ}
    (hy : y ∈ cubeComplex.waveGroup.invariantCore
      (totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)))
        (tsd (Q (Fin 3))) (tsd (Q (Fin 3)))))) :
    totalJ J y ∈ RealTorus.gradCurl.waveGroup.invariantCore
      (totalSub (constraint tsdE tsdB)) := by
  refine C0Group.mem_invariantCore.2 fun t => ?_
  rw [← RowWise.waveGroup_J]
  obtain ⟨e0, m1, m2⟩ := mem_totalSub_family3.1 (C0Group.mem_invariantCore.1 hy t)
  refine mem_totalSub_constraint.2 ⟨?_, J_one_mem_tsdE m1, J_two_mem_tsdB m2⟩
  have e0' : ((cubeComplex.waveGroup.S t y) 0 : Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) = 0 := e0
  show J 0 ((cubeComplex.waveGroup.S t y) 0) = 0
  rw [e0', _root_.map_zero]

/-! ### The stationary data -/

theorem nonempty_Q : (Q (Fin 3)).Nonempty :=
  ⟨fun _ => 1 / 4, Geometry.mem_Q.2 fun _ => ⟨by norm_num, by norm_num⟩⟩

/-- The datum `(0, 0, B₀)` of the torus. -/
def magState (B : Space 2) : PiLp 2 Space := WithLp.toLp 2 (Pi.single (M := Space) 2 B)

theorem totalJ_inj₂ (u : Domain.L2F ℝ (Q (Fin 3)) Ix) :
    totalJ J (inj₂ (𝕜 := ℝ) (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) (Domain.L2F ℝ (Q (Fin 3)) Ix)
      (Domain.L2F ℝ (Q (Fin 3)) Ix) u) = magState (J 2 u) := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · exact _root_.map_zero (J 0)
  · exact _root_.map_zero (J 1)
  · rfl

/-- The Hessian of the harmonic function `e^{-t x₁} cos(t x₂)` on `Q`. -/
abbrev hessQ (t : ℝ) : Domain.L2F ℝ (Q (Fin 3)) Ix :=
  Models.BoundedDomain.hessL2 Geometry.isOpen_Q RowWise.isBounded_Q
    (Models.BoundedDomain.contDiff_expCos t)

theorem inj₂_hessQ_mem_invariantCore (t : ℝ) :
    inj₂ (𝕜 := ℝ) (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) (Domain.L2F ℝ (Q (Fin 3)) Ix)
        (Domain.L2F ℝ (Q (Fin 3)) Ix) (hessQ t) ∈
      cubeComplex.waveGroup.invariantCore
        (totalSub (family3 (⊥ : Submodule ℝ (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)))
          (tsd (Q (Fin 3))) (tsd (Q (Fin 3))))) :=
  Models.BoundedDomain.hessL2_mem_invariantCore₂ Geometry.isOpen_Q RowWise.isBounded_Q _
    (Models.BoundedDomain.contDiff_expCos t) fun x _ => Models.BoundedDomain.laplacian_expCos t x

/-- The parity extension of the Hessian of `e^{-x₁} cos x₂`. -/
def staticB : Space 2 := J 2 (hessQ 1)

theorem staticB_mem_invariantCore :
    magState staticB ∈ RealTorus.gradCurl.waveGroup.invariantCore
      (totalSub (constraint tsdE tsdB)) := by
  rw [staticB, ← totalJ_inj₂]
  exact totalJ_mem_invariantCore (inj₂_hessQ_mem_invariantCore 1)

theorem linearIndependent_magState :
    LinearIndependent ℝ fun n : ℕ => magState (J 2 (hessQ ((n : ℝ) + 1))) := by
  have hli := Models.BoundedDomain.linearIndependent_hessL2_expCos Geometry.isOpen_Q
    RowWise.isBounded_Q nonempty_Q
  let f : Domain.L2F ℝ (Q (Fin 3)) Ix →ₗ[ℝ] PiLp 2 Space :=
    (totalJ J : PiLp 2 WQ →L[ℝ] PiLp 2 Space).toLinearMap ∘ₗ
      (inj₂ (𝕜 := ℝ) (Domain.L2F ℝ (Q (Fin 3)) (Fin 3)) (Domain.L2F ℝ (Q (Fin 3)) Ix)
        (Domain.L2F ℝ (Q (Fin 3)) Ix)).toLinearMap
  have hf : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun u v h => ?_
    have := RowWise.totalJ_injective h
    exact congrArg (fun z : PiLp 2 WQ => (z 2 : WQ 2)) this
  have e : (fun n : ℕ => magState (J 2 (hessQ ((n : ℝ) + 1)))) =
      f ∘ fun n : ℕ => hessQ ((n : ℝ) + 1) :=
    funext fun n => (totalJ_inj₂ _).symm
  rw [e]
  exact hli.map' f hf

/-- **`K*` of the constraint `{0} × L²(TSD) × L²(TSD)` on the cube is infinite-dimensional**
([QuennevilleBelair2015], Prop 4.17 (adapted)). -/
theorem not_finiteDimensional_invariantCore :
    ¬ FiniteDimensional ℝ (RealTorus.gradCurl.waveGroup.invariantCore
      (totalSub (constraint tsdE tsdB))) := by
  intro hfin
  let v : ℕ → RealTorus.gradCurl.waveGroup.invariantCore (totalSub (constraint tsdE tsdB)) :=
    fun n => ⟨magState (J 2 (hessQ ((n : ℝ) + 1))), by
      rw [← totalJ_inj₂]
      exact totalJ_mem_invariantCore (inj₂_hessQ_mem_invariantCore _)⟩
  have hli : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (Submodule.subtype _) linearIndependent_magState
  exact Module.Finite.not_linearIndependent_of_infinite v hli

theorem exists_linearIndependent_invariantCore (n : ℕ) :
    ∃ v : Fin n → PiLp 2 Space, LinearIndependent ℝ v ∧
      ∀ i, v i ∈ RealTorus.gradCurl.waveGroup.invariantCore (totalSub (constraint tsdE tsdB)) ∧
        v i ∈ RealTorus.gradCurl.waveGroup.stationary := by
  refine ⟨fun i => magState (J 2 (hessQ (((i : ℕ) : ℝ) + 1))),
    linearIndependent_magState.comp _ Fin.val_injective, fun i => ?_⟩
  have h : magState (J 2 (hessQ (((i : ℕ) : ℝ) + 1))) ∈
      RealTorus.gradCurl.waveGroup.invariantCore (totalSub (constraint tsdE tsdB)) := by
    rw [← totalJ_inj₂]
    exact totalJ_mem_invariantCore (inj₂_hessQ_mem_invariantCore _)
  exact ⟨h, ((mem_invariantCore_torus_iff (S1 := tsdE) (S2 := tsdB) inf_le_left inf_le_left
    _).1 h).2⟩

theorem invariantCore_ne_bot :
    complex.waveGroup.invariantCore
        (totalSub (compSub rowAction.fixed (constraint tsdE tsdB))) ≠ ⊥ := by
  have hfix : ∀ i, magState staticB i ∈ rowAction.fixed i := by
    intro i
    fin_cases i
    · exact Submodule.zero_mem _
    · exact Submodule.zero_mem _
    · exact (mem_realFixed_iff.1 (RowWise.J_mem 2 (hessQ 1))).2
  set y : PiLp 2 fun i => rowAction.fixed i := WithLp.toLp 2 fun i => ⟨_, hfix i⟩
  intro hbot
  have hy : y ∈ complex.waveGroup.invariantCore
      (totalSub (compSub rowAction.fixed (constraint tsdE tsdB))) :=
    (mem_invariantCore_compSub_iff _ _ y).2 staticB_mem_invariantCore
  rw [hbot, Submodule.mem_bot] at hy
  have h2 := congrArg (fun z : PiLp 2 fun i => rowAction.fixed i => ((z 2 : _) : Space 2)) hy
  change staticB = 0 at h2
  have := linearIndependent_magState.ne_zero 0
  simp only [Nat.cast_zero, zero_add] at this
  refine this ?_
  rw [show J 2 (hessQ 1) = staticB from rfl, h2]
  show WithLp.toLp 2 (Pi.single (M := Space) 2 0) = 0
  rw [Pi.single_zero]
  rfl

end Feec.Models.Cube.Parity
