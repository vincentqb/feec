module

public import Feec.HilbertComplex.Reweight
public import Feec.Physics.Maxwell.Constraints

/-!
# Maxwell's equations in a linear medium

Maxwell's equations in a linear medium with `ε = e† e`, `μ = m† m`, on a short complex: in the
variables `(σ, e E, m H)` they are the Hodge wave equation of a conjugated complex, hence well
posed (`Medium.existsUnique`), with conserved energy and propagating weighted Gauss laws.
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Maxwell

universe u

open ShortHilbertComplex HilbertComplex

/-- A linear medium: bounded isomorphisms `e`, `m` with `ε = e† e` and `μ = m† m`. -/
structure Medium (𝕜 : Type*) [RCLike 𝕜] (W₁ W₂ : Type*) [NormedAddCommGroup W₁]
    [InnerProductSpace 𝕜 W₁] [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] where
  /-- the factor of the permittivity, `ε = e† e` -/
  e : W₁ ≃L[𝕜] W₁
  /-- the factor of the permeability, `μ = m† m` -/
  m : W₂ ≃L[𝕜] W₂

section Components

variable {W₀ W₁ W₂ : Type u} [NormedAddCommGroup W₀] [NormedAddCommGroup W₁]
  [NormedAddCommGroup W₂]

/-- The gauge component `σ` of a state `(σ, E, H)`. -/
def gauge (U : PiLp 2 (W3 W₀ W₁ W₂)) : W₀ := U 0

/-- The electric component `E` of a state `(σ, E, H)`. -/
def electric (U : PiLp 2 (W3 W₀ W₁ W₂)) : W₁ := U 1

/-- The magnetic component `H` of a state `(σ, E, H)`. -/
def magnetic (U : PiLp 2 (W3 W₀ W₁ W₂)) : W₂ := U 2

end Components

namespace Medium

section Coefficients

variable {𝕜 : Type*} [RCLike 𝕜] {W₁ W₂ : Type*}
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [NormedAddCommGroup W₂]
  [InnerProductSpace 𝕜 W₂] (M : Medium 𝕜 W₁ W₂)

/-- The condition number `max (‖e‖ ‖e⁻¹‖) (‖m‖ ‖m⁻¹‖)` of a medium. -/
def cond : ℝ :=
  max (‖(M.e : W₁ →L[𝕜] W₁)‖ * ‖(M.e.symm : W₁ →L[𝕜] W₁)‖)
    (‖(M.m : W₂ →L[𝕜] W₂)‖ * ‖(M.m.symm : W₂ →L[𝕜] W₂)‖)

section Permittivity

variable [CompleteSpace W₁]

/-- The permittivity `ε = e† e`. -/
def ε : W₁ →L[𝕜] W₁ := ContinuousLinearMap.adjoint (M.e : W₁ →L[𝕜] W₁) ∘L (M.e : W₁ →L[𝕜] W₁)

theorem ε_apply (x : W₁) : M.ε x = M.e.adjoint (M.e x) := rfl

theorem re_inner_ε_apply (x : W₁) : RCLike.re ⟪M.ε x, x⟫_𝕜 = ‖M.e x‖ ^ 2 :=
  ContinuousLinearMap.re_inner_adjoint_comp_self_apply _ x

theorem ε_e_symm_apply (x : W₁) : M.ε (M.e.symm x) = M.e.adjoint x := by
  rw [ε_apply, ContinuousLinearEquiv.apply_symm_apply]

end Permittivity

section Permeability

variable [CompleteSpace W₂]

/-- The permeability `μ = m† m`. -/
def μ : W₂ →L[𝕜] W₂ := ContinuousLinearMap.adjoint (M.m : W₂ →L[𝕜] W₂) ∘L (M.m : W₂ →L[𝕜] W₂)

theorem μ_apply (x : W₂) : M.μ x = M.m.adjoint (M.m x) := rfl

theorem re_inner_μ_apply (x : W₂) : RCLike.re ⟪M.μ x, x⟫_𝕜 = ‖M.m x‖ ^ 2 :=
  ContinuousLinearMap.re_inner_adjoint_comp_self_apply _ x

theorem μ_m_symm_apply (x : W₂) : M.μ (M.m.symm x) = M.m.adjoint x := by
  rw [μ_apply, ContinuousLinearEquiv.apply_symm_apply]

end Permeability

end Coefficients

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  (M : Medium 𝕜 W₁ W₂)

/-! ### The conjugated complex and the change of variables -/

variable (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-- The conjugated complex `d₀' = e d₀`, `d₁' = (m⁻¹)† d₁ e⁻¹` of a medium. -/
def complex : ShortHilbertComplex 𝕜 W₀ W₁ W₂ :=
  S.conj (ContinuousLinearEquiv.refl 𝕜 W₀) M.e M.m.adjoint.symm

theorem adjoint_complex_d₀ : (M.complex S).d₀† =
    S.d₀†.conj M.e.adjoint.symm (ContinuousLinearEquiv.refl 𝕜 W₀).adjoint.symm :=
  adjoint_conj _ _ S.dense₀

theorem adjoint_complex_d₁ : (M.complex S).d₁† =
    S.d₁†.conj M.m.adjoint.symm.adjoint.symm M.e.adjoint.symm :=
  adjoint_conj _ _ S.dense₁

variable (W₀) in
/-- The weights `(1, e, m)` of the state variables, as a family on `Fin 3`. -/
def stateW : ∀ i : Fin 3, W3 W₀ W₁ W₂ i ≃L[𝕜] W3 W₀ W₁ W₂ i
  | 0 => ContinuousLinearEquiv.refl 𝕜 W₀
  | 1 => M.e
  | 2 => M.m

variable (W₀) in
/-- The change of variables `(σ, E, H) ↦ (σ, e E, m H)`. -/
def state : PiLp 2 (W3 W₀ W₁ W₂) ≃L[𝕜] PiLp 2 (W3 W₀ W₁ W₂) :=
  ContinuousLinearEquiv.equivOfInverse (totalMap (M.stateW W₀))
    (totalMap fun i => (M.stateW W₀ i).symm)
    (fun x => PiLp.ext fun i => (M.stateW W₀ i).symm_apply_apply (x i))
    (fun x => PiLp.ext fun i => (M.stateW W₀ i).apply_symm_apply (x i))

/-- The Maxwell operator `(σ, E, H) ↦ (−d₀† (ε E), d₀ σ − ε⁻¹ d₁† H, μ⁻¹ d₁ E)` of the medium. -/
def maxwell : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂) :=
  (M.complex S).wave.conj (M.state W₀).symm (M.state W₀).symm

theorem mem_maxwell_domain {U : PiLp 2 (W3 W₀ W₁ W₂)} : U ∈ (M.maxwell S).domain ↔
    gauge U ∈ S.d₀.domain ∧ electric U ∈ S.d₁.domain ∧ M.ε (electric U) ∈ S.d₀†.domain ∧
      magnetic U ∈ S.d₁†.domain := by
  change M.state W₀ U ∈ (M.complex S).wave.domain ↔ _
  rw [ShortHilbertComplex.mem_wave_domain, adjoint_complex_d₀, adjoint_complex_d₁]
  change gauge U ∈ S.d₀.domain ∧ M.e.symm (M.e (electric U)) ∈ S.d₁.domain ∧
      M.e.adjoint (M.e (electric U)) ∈ S.d₀†.domain ∧
      M.m.adjoint.symm.adjoint (M.m (magnetic U)) ∈ S.d₁†.domain ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.adjoint_symm_adjoint_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

variable {M S}

theorem state_mem_wave_domain (x : (M.maxwell S).domain) :
    M.state W₀ x ∈ (M.complex S).wave.domain := x.2

theorem ε_electric_maxwell_apply (x : (M.maxwell S).domain) :
    M.ε (electric (M.maxwell S x)) =
      M.ε (S.d₀ ⟨gauge x.1, (M.mem_maxwell_domain S |>.1 x.2).1⟩) -
        S.d₁† ⟨magnetic x.1, (M.mem_maxwell_domain S |>.1 x.2).2.2.2⟩ := by
  change M.ε (M.e.symm (electric ((M.complex S).wave ⟨M.state W₀ x, state_mem_wave_domain x⟩))) = _
  rw [ε_e_symm_apply]
  change M.e.adjoint (((M.complex S).wave ⟨M.state W₀ x, state_mem_wave_domain x⟩ :
    PiLp 2 _) 1) = _
  rw [ShortHilbertComplex.wave_apply_one]
  change M.e.adjoint ((M.complex S).d₀ ⟨gauge x.1, (state_mem_wave_domain x).1 0 1⟩ -
    (M.complex S).d₁† ⟨M.m (magnetic x.1), (state_mem_wave_domain x).2 2 1⟩) = _
  rw [_root_.map_sub, apply_eq_of_eq (adjoint_complex_d₁ M S) _ ⟨M.m (magnetic x.1), by
      rw [← adjoint_complex_d₁]; exact (state_mem_wave_domain x).2 2 1⟩ rfl, conj_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  congr 1
  refine apply_congr' _ _ _ ?_
  change M.m.adjoint.symm.adjoint (M.m (magnetic x.1)) = magnetic x.1
  rw [ContinuousLinearEquiv.adjoint_symm_adjoint_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem μ_magnetic_maxwell_apply (x : (M.maxwell S).domain) :
    M.μ (magnetic (M.maxwell S x)) =
      S.d₁ ⟨electric x.1, (M.mem_maxwell_domain S |>.1 x.2).2.1⟩ := by
  change M.μ (M.m.symm (magnetic ((M.complex S).wave ⟨M.state W₀ x, state_mem_wave_domain x⟩))) = _
  rw [μ_m_symm_apply]
  change M.m.adjoint (((M.complex S).wave ⟨M.state W₀ x, state_mem_wave_domain x⟩ :
    PiLp 2 _) 2) = _
  rw [ShortHilbertComplex.wave_apply_two]
  change M.m.adjoint (M.m.adjoint.symm (S.d₁ ⟨M.e.symm (M.e (electric x.1)), _⟩)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact apply_congr' _ _ _ (M.e.symm_apply_apply _)

variable (M S)

theorem isSkewAdjoint_wave_complex : (M.complex S).wave.IsSkewAdjoint :=
  (M.complex S).isSkewAdjoint_wave

/-! ### Well-posedness and energy -/

section Evolution

variable [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀] [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁]
  [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂]

/-- Strong solutions of Maxwell's equations in the medium are, in the variables
`(σ, e E, m H)`, the strong solutions of the Hodge wave equation of the conjugated complex. -/
theorem isStrongSolution_iff {I : Set ℝ} {F U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)} :
    Evolution.IsStrongSolution (M.maxwell S) I F U ↔
      Evolution.IsStrongSolution (M.complex S).wave I (fun t => M.state W₀ (F t))
        (fun t => M.state W₀ (U t)) :=
  Evolution.isStrongSolution_conj_symm_iff (M.state W₀)

/-- Well-posedness in a medium: data in the domain and admissible forcing give a classical
solution of `U' = M U + F`, unique among strong solutions. -/
theorem existsUnique {U₀ : PiLp 2 (W3 W₀ W₁ W₂)} (hU₀ : U₀ ∈ (M.maxwell S).domain)
    {F : ℝ → PiLp 2 (W3 W₀ W₁ W₂)} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible (M.maxwell S) a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (M.maxwell S) (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (M.maxwell S) (Icc a b) F V →
        EqOn V U (Icc a b) :=
  Evolution.existsUnique_conj_symm (M.state W₀)
    (fun _ hU₀ _ hF => (M.isSkewAdjoint_wave_complex S).existsUnique_classicalSolution hU₀ hF)
    hU₀ hF

omit [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀] [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁]
  [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂] in
/-- The **weighted energy** `½ (‖σ‖² + ⟪ε E, E⟫ + ⟪μ H, H⟫)`. -/
def energy (U : PiLp 2 (W3 W₀ W₁ W₂)) : ℝ :=
  (‖gauge U‖ ^ 2 + RCLike.re ⟪M.ε (electric U), electric U⟫_𝕜 +
    RCLike.re ⟪M.μ (magnetic U), magnetic U⟫_𝕜) / 2

omit [CompleteSpace W₀] [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀] [NormedSpace ℝ W₁]
  [IsScalarTower ℝ 𝕜 W₁] [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂] in
theorem energy_eq_norm_state (U : PiLp 2 (W3 W₀ W₁ W₂)) :
    M.energy U = ‖M.state W₀ U‖ ^ 2 / 2 := by
  rw [energy, re_inner_ε_apply, re_inner_μ_apply, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  rfl

/-- Conservation of the weighted energy: a strong solution of the free Maxwell equations in the
medium has `½ (‖σ‖² + ⟪ε E, E⟫ + ⟪μ H, H⟫)` constant in time. -/
theorem energy_eq {a b : ℝ} {U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)}
    (hU : Evolution.IsStrongSolution (M.maxwell S) (Icc a b) 0 U) :
    ∀ t ∈ Icc a b, M.energy (U t) = M.energy (U a) := by
  have h := (M.isStrongSolution_iff S).1 hU
  have h' : Evolution.IsStrongSolution (M.complex S).wave (Icc a b) 0
      (fun t => M.state W₀ (U t)) := by
    convert h using 1
    funext t; simp
  intro t ht
  rw [energy_eq_norm_state, energy_eq_norm_state,
    h'.norm_eq (M.isSkewAdjoint_wave_complex S).isSkewSymmetric t ht]

end Evolution

/-! ### The weighted Gauss laws -/

section Gauss

variable (Y : Submodule 𝕜 W₂)

/-- The weighted Gauss laws `σ = 0`, `d₀† (ε E) = 0` and `μ H ∈ Y`. -/
def gauss : Submodule 𝕜 (PiLp 2 (W3 W₀ W₁ W₂)) :=
  (totalSub ((M.complex S).divFreeSub (Y.map (M.m.adjoint.symm : W₂ →ₗ[𝕜] W₂)))).comap
    (M.state W₀ : PiLp 2 (W3 W₀ W₁ W₂) →ₗ[𝕜] PiLp 2 (W3 W₀ W₁ W₂))

variable {Y} in
theorem complex_d₁_mem (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y)
    (x : (M.complex S).d₁.domain) :
    (M.complex S).d₁ x ∈ Y.map (M.m.adjoint.symm : W₂ →ₗ[𝕜] W₂) := by
  exact Submodule.mem_map_of_mem (hY ⟨M.e.symm x, x.2⟩)

variable [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀] [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁]
  [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂]

variable {Y} [Y.HasOrthogonalProjection]

/-- The weighted Gauss laws `σ = 0`, `d₀† (ε E) = 0`, `μ H ∈ Y` propagate in any medium, on any
short complex, for any `Y ⊇ R(d₁)` with an orthogonal projection. -/
theorem gauss_propagates (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y) {t₀ t₁ : ℝ}
    {F U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)}
    (hU : Evolution.IsStrongSolution (M.maxwell S) (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ M.gauss S Y) (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ M.gauss S Y) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ M.gauss S Y :=
  (M.complex S).divFree_propagates _ (M.complex_d₁_mem S hY) ((M.isStrongSolution_iff S).1 hU)
    h0 hF

/-- Data in the domain and admissible forcing satisfying the weighted Gauss laws give a classical
solution, unique among strong ones, which satisfies them. -/
theorem gauss_existsUnique (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y) {U₀ : PiLp 2 (W3 W₀ W₁ W₂)}
    (hU₀ : U₀ ∈ (M.maxwell S).domain) (hU₀Y : U₀ ∈ M.gauss S Y) {F : ℝ → PiLp 2 (W3 W₀ W₁ W₂)}
    {a b : ℝ} (hF : Evolution.ForcingClass.admissible (M.maxwell S) a b F)
    (hFY : ∀ t ∈ Icc a b, F t ∈ M.gauss S Y) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (M.maxwell S) (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ M.gauss S Y) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (M.maxwell S) (Icc a b) F V →
        EqOn V U (Icc a b) := by
  obtain ⟨U, hU0, hU, huniq⟩ := M.existsUnique S hU₀ hF
  exact ⟨U, hU0, hU, M.gauss_propagates S hY hU.toIsStrongSolution (hU0 ▸ hU₀Y) hFY, huniq⟩

end Gauss

end Medium

/-! ### Every medium has weights (over `ℂ`) -/

/-- Over `ℂ`, for bounded self-adjoint uniformly positive `ε`, `μ` there is a `Maxwell.Medium`
with permittivity `ε` and permeability `μ`. -/
theorem Medium.exists_eq {W₁ W₂ : Type*} [NormedAddCommGroup W₁] [InnerProductSpace ℂ W₁]
    [CompleteSpace W₁] [NormedAddCommGroup W₂] [InnerProductSpace ℂ W₂] [CompleteSpace W₂]
    {ε : W₁ →L[ℂ] W₁} {μ : W₂ →L[ℂ] W₂} (hε : IsSelfAdjoint ε) (hμ : IsSelfAdjoint μ)
    {c : ℝ} (hc : 0 < c) (hcε : ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪ε x, x⟫_ℂ)
    (hcμ : ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪μ x, x⟫_ℂ) :
    ∃ M : Medium ℂ W₁ W₂, M.ε = ε ∧ M.μ = μ := by
  obtain ⟨e, -, he⟩ := ContinuousLinearMap.exists_selfAdjoint_equiv_adjoint_comp_eq hε hc hcε
  obtain ⟨m, -, hm⟩ := ContinuousLinearMap.exists_selfAdjoint_equiv_adjoint_comp_eq hμ hc hcμ
  exact ⟨⟨e, m⟩, he, hm⟩

end Feec.Maxwell
