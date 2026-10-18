module

public import Feec.HilbertComplex.Reweight
public import Feec.Physics.Maxwell.Constraints

/-!
# Maxwell's equations in a linear medium

A linear, possibly anisotropic and inhomogeneous medium has a permittivity `ε` and a permeability
`μ`: bounded, self-adjoint, uniformly positive operators on the electric and magnetic `L²`
spaces (e.g. multiplication by measurable scalar or Hermitian matrix fields with
`λ ≤ ε(x), μ(x) ≤ Λ`, `Feec.Physics.Maxwell.Coefficients`). Maxwell's
equations in the medium read

  `ε E' = ε dσ − d† H`,  `μ H' = d E`,  `σ' = −d† (ε E)`

on a short complex `W₀ --d₀--> W₁ --d₁--> W₂` (the window `V a → V (a+1) → V (a+2)` of any
Hilbert complex, `grad → curl` with a perfect electric or magnetic conductor on an open
`Ω ⊆ ℝ³`): `E` is the electric field, `H` the magnetic field (`B = μ H` the magnetic flux), `σ`
the gauge field of the Hodge wave formulation (the physical system is `σ = 0`). With
`H ↦ −H` this is `ε E' = curl H`, `μ H' = −curl E` (`σ = 0`). Here `d† H` uses the adjoint
`d₁†` (the curl with the complementary boundary condition), and `ε dσ` is the gauge coupling.

A medium is given by factors `ε = e† e`, `μ = m† m` with bounded isomorphisms `e`, `m`
(`Maxwell.Medium`); over `ℂ` every bounded self-adjoint uniformly positive `ε`, `μ` has such
factors (`e = ε^{1/2}`, `m = μ^{1/2}`, `Maxwell.Medium.exists_eq`). In the variables
`(σ, e E, m H)` the system is the Hodge wave equation of the conjugated complex
`d₀' = e d₀`, `d₁' = (m⁻¹)† d₁ e⁻¹` (`Maxwell.Medium.complex`), whose wave operator is
skew-adjoint. This gives:

## Main definitions

* `Maxwell.Medium`: the factors `e`, `m`; `Medium.ε`, `Medium.μ`; `Medium.state`: the change of
  variables `(σ, E, H) ↦ (σ, e E, m H)`.
* `Medium.maxwell S`: the Maxwell operator of the medium on `W₀ × W₁ × W₂`, with domain and
  action `mem_maxwell_domain`, `gauge_maxwell_apply`, `ε_electric_maxwell_apply`,
  `μ_magnetic_maxwell_apply`.
* `Medium.energy`: `½ (‖σ‖² + ⟪ε E, E⟫ + ⟪μ H, H⟫)`; `Medium.gauss S Y`: the weighted Gauss
  laws `σ = 0`, `d₀† (ε E) = 0` (`div (ε E) = 0`), `μ H ∈ Y` (`div (μ H) = 0` for `Y = N(d₂)`).

## Main results

* `Medium.isStrongSolution_iff`, `Medium.equations`: strong solutions of `U' = M U + F` are the
  solutions of the three equations above (with forcing).
* `Medium.existsUnique`: **well-posedness** for data in the domain and admissible forcing
  (Stone's theorem for the conjugated complex).
* `Medium.energy_eq`: **conservation of the weighted energy**.
* `Medium.gauss_propagates`, `Medium.gauss_existsUnique`: **the weighted Gauss laws
  propagate**; instances for the window of any complex (`window_gauss_propagates`) and for
  perfect electric and magnetic conductors on every open `Ω ⊆ ℝ³` (`pec_gauss_propagates_medium`,
  `pmc_gauss_propagates_medium`).

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 8 (evolution problems:
  the Hodge wave equation and Maxwell's equations)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (weighted inner products on a Hilbert complex)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.9 (Prop 4.16: the vector wave equation and its divergence constraint)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.Maxwell

universe u

open ShortHilbertComplex HilbertComplex

/-- A **linear medium** on the electric space `W₁` and the magnetic space `W₂`: bounded
isomorphisms `e`, `m` with permittivity `ε = e† e` and permeability `μ = m† m`. -/
structure Medium (𝕜 : Type*) [RCLike 𝕜] (W₁ W₂ : Type*) [NormedAddCommGroup W₁]
    [InnerProductSpace 𝕜 W₁] [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] where
  /-- the factor of the permittivity, `ε = e† e` (e.g. `e = ε^{1/2}`) -/
  e : W₁ ≃L[𝕜] W₁
  /-- the factor of the permeability, `μ = m† m` (e.g. `m = μ^{1/2}`) -/
  m : W₂ ≃L[𝕜] W₂

/-! ### Components of the state `(σ, E, H)` -/

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

section Permittivity

variable [CompleteSpace W₁]

/-- The permittivity `ε = e† e`. -/
def ε : W₁ →L[𝕜] W₁ := ContinuousLinearMap.adjoint (M.e : W₁ →L[𝕜] W₁) ∘L (M.e : W₁ →L[𝕜] W₁)

theorem ε_apply (x : W₁) : M.ε x = M.e.adjoint (M.e x) := rfl

/-- The permittivity is bounded and self-adjoint. -/
theorem isSelfAdjoint_ε : IsSelfAdjoint M.ε := ContinuousLinearMap.isSelfAdjoint_adjoint_comp_self _

/-- The permittivity is uniformly positive. -/
theorem coercive_ε : ∃ c > 0, ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪M.ε x, x⟫_𝕜 :=
  ContinuousLinearMap.coercive_adjoint_comp_self M.e

theorem re_inner_ε_apply (x : W₁) : RCLike.re ⟪M.ε x, x⟫_𝕜 = ‖M.e x‖ ^ 2 :=
  ContinuousLinearMap.re_inner_adjoint_comp_self_apply _ x

/-- `ε e⁻¹ = e†`. -/
theorem ε_e_symm_apply (x : W₁) : M.ε (M.e.symm x) = M.e.adjoint x := by
  rw [ε_apply, ContinuousLinearEquiv.apply_symm_apply]

end Permittivity

section Permeability

variable [CompleteSpace W₂]

/-- The permeability `μ = m† m`. -/
def μ : W₂ →L[𝕜] W₂ := ContinuousLinearMap.adjoint (M.m : W₂ →L[𝕜] W₂) ∘L (M.m : W₂ →L[𝕜] W₂)

theorem μ_apply (x : W₂) : M.μ x = M.m.adjoint (M.m x) := rfl

/-- The permeability is bounded and self-adjoint. -/
theorem isSelfAdjoint_μ : IsSelfAdjoint M.μ := ContinuousLinearMap.isSelfAdjoint_adjoint_comp_self _

/-- The permeability is uniformly positive. -/
theorem coercive_μ : ∃ c > 0, ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪M.μ x, x⟫_𝕜 :=
  ContinuousLinearMap.coercive_adjoint_comp_self M.m

theorem re_inner_μ_apply (x : W₂) : RCLike.re ⟪M.μ x, x⟫_𝕜 = ‖M.m x‖ ^ 2 :=
  ContinuousLinearMap.re_inner_adjoint_comp_self_apply _ x

/-- `μ m⁻¹ = m†`. -/
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

/-- The conjugated complex `d₀' = e d₀`, `d₁' = (m⁻¹)† d₁ e⁻¹` of a medium: its standard inner
products are the weighted ones `⟪ε E, E⟫`, `⟪μ⁻¹ B, B⟫`. -/
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

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem gauge_state (U : PiLp 2 (W3 W₀ W₁ W₂)) : gauge (M.state W₀ U) = gauge U := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem electric_state (U : PiLp 2 (W3 W₀ W₁ W₂)) :
    electric (M.state W₀ U) = M.e (electric U) := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem magnetic_state (U : PiLp 2 (W3 W₀ W₁ W₂)) :
    magnetic (M.state W₀ U) = M.m (magnetic U) := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem gauge_state_symm (U : PiLp 2 (W3 W₀ W₁ W₂)) :
    gauge ((M.state W₀).symm U) = gauge U := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem electric_state_symm (U : PiLp 2 (W3 W₀ W₁ W₂)) :
    electric ((M.state W₀).symm U) = M.e.symm (electric U) := rfl
omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
@[simp] theorem magnetic_state_symm (U : PiLp 2 (W3 W₀ W₁ W₂)) :
    magnetic ((M.state W₀).symm U) = M.m.symm (magnetic U) := rfl

/-- The **Maxwell operator of the medium** on `W₀ × W₁ × W₂`: `Φ⁻¹ L' Φ` for the wave operator
`L'` of the conjugated complex and the change of variables `Φ = M.state`. Explicitly
(`gauge_maxwell_apply`, `ε_electric_maxwell_apply`, `μ_magnetic_maxwell_apply`)
`(σ, E, H) ↦ (−d₀† (ε E), d₀ σ − ε⁻¹ d₁† H, μ⁻¹ d₁ E)`. -/
def maxwell : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂) :=
  (M.complex S).wave.conj (M.state W₀).symm (M.state W₀).symm

/-- `D(M) = {(σ, E, H) | σ ∈ D(d₀), E ∈ D(d₁), ε E ∈ D(d₀†), H ∈ D(d₁†)}`. -/
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

theorem maxwell_apply (x : (M.maxwell S).domain) :
    M.maxwell S x = (M.state W₀).symm ((M.complex S).wave ⟨_, state_mem_wave_domain x⟩) := rfl

/-- `(M U)_σ = −d₀† (ε E)`: the gauge equation `σ' = −d₀† (ε E)`. -/
theorem gauge_maxwell_apply (x : (M.maxwell S).domain) :
    gauge (M.maxwell S x) =
      -(S.d₀† ⟨M.ε (electric x.1), (M.mem_maxwell_domain S |>.1 x.2).2.2.1⟩) := by
  change ((M.complex S).wave ⟨M.state W₀ x, state_mem_wave_domain x⟩ : PiLp 2 _) 0 = _
  rw [ShortHilbertComplex.wave_apply_zero]
  change -((M.complex S).d₀† ⟨M.e (electric x.1), (state_mem_wave_domain x).2 1 0⟩) = _
  congr 1
  rw [apply_eq_of_eq (adjoint_complex_d₀ M S) _ ⟨M.e (electric x.1), by
      rw [← adjoint_complex_d₀]; exact (state_mem_wave_domain x).2 1 0⟩ rfl, conj_apply,
    ContinuousLinearEquiv.adjoint_refl_symm_apply]
  exact apply_congr' _ _ _ rfl

/-- `ε (M U)_E = ε d₀ σ − d₁† H`: Ampère's law `ε E' = ε d₀ σ − d₁† H`. -/
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
    ContinuousLinearEquiv.adjoint_apply_adjoint_symm_apply]
  congr 1
  refine apply_congr' _ _ _ ?_
  change M.m.adjoint.symm.adjoint (M.m (magnetic x.1)) = magnetic x.1
  rw [ContinuousLinearEquiv.adjoint_symm_adjoint_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- `μ (M U)_H = d₁ E`: Faraday's law `μ H' = d₁ E`. -/
theorem μ_magnetic_maxwell_apply (x : (M.maxwell S).domain) :
    M.μ (magnetic (M.maxwell S x)) =
      S.d₁ ⟨electric x.1, (M.mem_maxwell_domain S |>.1 x.2).2.1⟩ := by
  change M.μ (M.m.symm (magnetic ((M.complex S).wave ⟨M.state W₀ x, state_mem_wave_domain x⟩))) = _
  rw [μ_m_symm_apply]
  change M.m.adjoint (((M.complex S).wave ⟨M.state W₀ x, state_mem_wave_domain x⟩ :
    PiLp 2 _) 2) = _
  rw [ShortHilbertComplex.wave_apply_two]
  change M.m.adjoint (M.m.adjoint.symm (S.d₁ ⟨M.e.symm (M.e (electric x.1)), _⟩)) = _
  rw [ContinuousLinearEquiv.adjoint_apply_adjoint_symm_apply]
  exact apply_congr' _ _ _ (M.e.symm_apply_apply _)

variable (M S)

/-- The wave operator of the conjugated complex is skew-adjoint (no closed range needed). -/
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

/-- **Maxwell's equations in the medium**: a strong solution `U = (σ, E, H)` of `U' = M U + F`
satisfies, at every `t ∈ I` (derivatives within `I`),
`σ' = −d₀† (ε E) + F_σ`, `(ε E)' = ε d₀ σ − d₁† H + ε F_E`, `(μ H)' = d₁ E + μ F_H`. -/
theorem equations {I : Set ℝ} {F U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)}
    (hU : Evolution.IsStrongSolution (M.maxwell S) I F U) (t : ℝ) (ht : t ∈ I) :
    HasDerivWithinAt (fun s => gauge (U s))
        (-(S.d₀† ⟨M.ε (electric (U t)), (M.mem_maxwell_domain S |>.1 (hU.mem_domain ht)).2.2.1⟩) +
          gauge (F t)) I t ∧
      HasDerivWithinAt (fun s => M.ε (electric (U s)))
        (M.ε (S.d₀ ⟨gauge (U t), (M.mem_maxwell_domain S |>.1 (hU.mem_domain ht)).1⟩) -
          S.d₁† ⟨magnetic (U t), (M.mem_maxwell_domain S |>.1 (hU.mem_domain ht)).2.2.2⟩ +
            M.ε (electric (F t))) I t ∧
      HasDerivWithinAt (fun s => M.μ (magnetic (U s)))
        (S.d₁ ⟨electric (U t), (M.mem_maxwell_domain S |>.1 (hU.mem_domain ht)).2.1⟩ +
          M.μ (magnetic (F t))) I t := by
  have hd := hU.hasDerivWithinAt ht
  set x : (M.maxwell S).domain := ⟨U t, hU.mem_domain ht⟩
  let p₀ : PiLp 2 (W3 W₀ W₁ W₂) →L[𝕜] W₀ := PiLp.proj 2 (W3 W₀ W₁ W₂) 0
  let p₁ : PiLp 2 (W3 W₀ W₁ W₂) →L[𝕜] W₁ := M.ε ∘L PiLp.proj 2 (W3 W₀ W₁ W₂) 1
  let p₂ : PiLp 2 (W3 W₀ W₁ W₂) →L[𝕜] W₂ := M.μ ∘L PiLp.proj 2 (W3 W₀ W₁ W₂) 2
  have h₀ : HasDerivWithinAt (fun s => gauge (U s)) (p₀ (M.maxwell S x + F t)) I t :=
    (p₀.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  have h₁ : HasDerivWithinAt (fun s => M.ε (electric (U s))) (p₁ (M.maxwell S x + F t)) I t :=
    (p₁.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  have h₂ : HasDerivWithinAt (fun s => M.μ (magnetic (U s))) (p₂ (M.maxwell S x + F t)) I t :=
    (p₂.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  refine ⟨?_, ?_, ?_⟩
  · convert h₀ using 1
    change _ = gauge (M.maxwell S x) + gauge (F t)
    rw [gauge_maxwell_apply]
  · convert h₁ using 1
    change _ = M.ε (electric (M.maxwell S x) + electric (F t))
    rw [_root_.map_add, ε_electric_maxwell_apply]
  · convert h₂ using 1
    change _ = M.μ (magnetic (M.maxwell S x) + magnetic (F t))
    rw [_root_.map_add, μ_magnetic_maxwell_apply]

/-- **Well-posedness of Maxwell's equations in a medium**: for initial data in the domain and
admissible forcing `F ∈ C([a,b]) ∩ (W^{1,1} ∪ L¹(D(M)))` there is a classical solution of
`U' = M U + F`, `U a = U₀`, unique among strong solutions (Stone's theorem for the skew-adjoint
wave operator of the conjugated complex). -/
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
/-- The weighted energy is half the squared norm of the conjugated variables. -/
theorem energy_eq_norm_state (U : PiLp 2 (W3 W₀ W₁ W₂)) :
    M.energy U = ‖M.state W₀ U‖ ^ 2 / 2 := by
  rw [energy, re_inner_ε_apply, re_inner_μ_apply, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  rfl

/-- **Conservation of the weighted energy**: a strong solution of the free Maxwell equations
in the medium has `½ (‖σ‖² + ⟪ε E, E⟫ + ⟪μ H, H⟫)` constant in time. -/
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

/-- The **weighted Gauss laws** `σ = 0`, `d₀† (ε E) = 0` (`div (ε E) = 0`) and `μ H ∈ Y`
(`div (μ H) = 0` for `Y = N(d₂)`), in the physical variables `(σ, E, H)`: the pull-back of the
constraint family `{0} × N(d₀'†) × (m⁻¹)† Y` of the conjugated complex (`mem_gauss_iff`). -/
def gauss : Submodule 𝕜 (PiLp 2 (W3 W₀ W₁ W₂)) :=
  (totalSub ((M.complex S).divFreeSub (Y.map (M.m.adjoint.symm : W₂ →ₗ[𝕜] W₂)))).comap
    (M.state W₀ : PiLp 2 (W3 W₀ W₁ W₂) →ₗ[𝕜] PiLp 2 (W3 W₀ W₁ W₂))

theorem mem_gauss_iff {U : PiLp 2 (W3 W₀ W₁ W₂)} : U ∈ M.gauss S Y ↔
    gauge U = 0 ∧ M.ε (electric U) ∈ (S.d₀†).ker ∧ M.μ (magnetic U) ∈ Y := by
  set Y' := Y.map (M.m.adjoint.symm : W₂ →ₗ[𝕜] W₂)
  have e0 : (M.state W₀ U) 0 ∈ (M.complex S).divFreeSub Y' 0 ↔ gauge U = 0 := by
    change gauge U ∈ (⊥ : Submodule 𝕜 W₀) ↔ _
    exact Submodule.mem_bot 𝕜
  have e1 : (M.state W₀ U) 1 ∈ (M.complex S).divFreeSub Y' 1 ↔
      M.ε (electric U) ∈ (S.d₀†).ker := by
    change M.e (electric U) ∈ ((M.complex S).d₀†).ker ↔ _
    rw [adjoint_complex_d₀, ker_conj, Submodule.mem_map_continuousLinearEquiv]
    rfl
  have e2 : (M.state W₀ U) 2 ∈ (M.complex S).divFreeSub Y' 2 ↔ M.μ (magnetic U) ∈ Y := by
    change M.m (magnetic U) ∈ Y' ↔ _
    rw [Submodule.mem_map_continuousLinearEquiv]
    rfl
  change (∀ i, (M.state W₀ U) i ∈ (M.complex S).divFreeSub Y' i) ↔ _
  constructor
  · intro h
    exact ⟨e0.1 (h 0), e1.1 (h 1), e2.1 (h 2)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    exacts [e0.2 h0, e1.2 h1, e2.2 h2]

variable {Y} in
/-- If `R(d₁) ⊆ Y`, the conjugated `d₁'` maps into `(m⁻¹)† Y`. -/
theorem complex_d₁_mem (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y)
    (x : (M.complex S).d₁.domain) :
    (M.complex S).d₁ x ∈ Y.map (M.m.adjoint.symm : W₂ →ₗ[𝕜] W₂) := by
  exact Submodule.mem_map_of_mem (hY ⟨M.e.symm x, x.2⟩)

variable [NormedSpace ℝ W₀] [IsScalarTower ℝ 𝕜 W₀] [NormedSpace ℝ W₁] [IsScalarTower ℝ 𝕜 W₁]
  [NormedSpace ℝ W₂] [IsScalarTower ℝ 𝕜 W₂]

variable {Y} [Y.HasOrthogonalProjection]

/-- **The weighted Gauss laws propagate** for Maxwell's equations in any medium, on any short
complex, for any closed `Y ⊇ R(d₁)`: strong solutions with data and forcing satisfying `σ = 0`,
`d₀† (ε E) = 0`, `μ H ∈ Y` satisfy them for all times. No closed range or density hypothesis. -/
theorem gauss_propagates (hY : ∀ x : S.d₁.domain, S.d₁ x ∈ Y) {t₀ t₁ : ℝ}
    {F U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)}
    (hU : Evolution.IsStrongSolution (M.maxwell S) (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ M.gauss S Y) (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ M.gauss S Y) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ M.gauss S Y :=
  (M.complex S).divFree_propagates _ (M.complex_d₁_mem S hY) ((M.isStrongSolution_iff S).1 hU)
    h0 hF

/-- **Well-posedness in the weighted Gauss-law subspace**: for data in the domain satisfying the
weighted Gauss laws and admissible forcing satisfying them, there is a unique classical
solution, and it satisfies the weighted Gauss laws for all times. -/
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

/-- **Every linear medium is a `Maxwell.Medium`** (over `ℂ`): bounded, self-adjoint, uniformly
positive `ε`, `μ` (e.g. multiplication by measurable Hermitian matrix fields with
`λ ≤ ε(x), μ(x) ≤ Λ`, `Maxwell.Medium.exists_anisotropic`) have the factors `e = ε^{1/2}`, `m = μ^{1/2}`. -/
theorem Medium.exists_eq {W₁ W₂ : Type*} [NormedAddCommGroup W₁] [InnerProductSpace ℂ W₁]
    [CompleteSpace W₁] [NormedAddCommGroup W₂] [InnerProductSpace ℂ W₂] [CompleteSpace W₂]
    {ε : W₁ →L[ℂ] W₁} {μ : W₂ →L[ℂ] W₂} (hε : IsSelfAdjoint ε) (hμ : IsSelfAdjoint μ)
    {c : ℝ} (hc : 0 < c) (hcε : ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪ε x, x⟫_ℂ)
    (hcμ : ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪μ x, x⟫_ℂ) :
    ∃ M : Medium ℂ W₁ W₂, M.ε = ε ∧ M.μ = μ := by
  obtain ⟨e, -, he⟩ := ContinuousLinearMap.exists_selfAdjoint_equiv_adjoint_comp_eq hε hc hcε
  obtain ⟨m, -, hm⟩ := ContinuousLinearMap.exists_selfAdjoint_equiv_adjoint_comp_eq hμ hc hcμ
  exact ⟨⟨e, m⟩, he, hm⟩

/-! ### Instances: windows of complexes, perfect conductors on domains -/

section Window

variable {𝕜 : Type*} [RCLike 𝕜] {V : ℕ → Type u} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  (H : HilbertComplex 𝕜 (ComplexShape.up ℕ) V) (a : ℕ)
  (M : Medium 𝕜 (V (a + ((1 : Fin 3) : ℕ))) (V (a + ((2 : Fin 3) : ℕ))))

/-- **Maxwell in a medium on the window of any complex** (any degree): the weighted Gauss laws
`σ = 0`, `d† (ε E) = 0`, `d (μ H) = 0` propagate. -/
theorem window_gauss_propagates {t₀ t₁ : ℝ} {F U : ℝ → Space a (V := V)}
    (hU : Evolution.IsStrongSolution (M.maxwell (window H a)) (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ M.gauss (window H a) (closedSub H a))
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ M.gauss (window H a) (closedSub H a)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ M.gauss (window H a) (closedSub H a) :=
  M.gauss_propagates (window H a) (d_mem_closedSub H a) hU h0 hF

end Window

section Conductor

open Feec.Domain

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) [Fact (IsOpen Ω)]
  (M : Medium 𝕜 (L2F 𝕜 Ω (Fin 1 × Fin 3)) (L2F 𝕜 Ω (Fin 1 × Fin 3)))

/-- **Maxwell in a medium with a perfect electric conductor** on any open `Ω ⊆ ℝ³` (bounded or
not): the weighted Gauss laws `σ = 0`, `div (ε E) = 0`, `div (μ H) = 0` with `μ H · n = 0`
propagate. -/
theorem pec_gauss_propagates_medium {t₀ t₁ : ℝ}
    {F U : ℝ → PiLp 2 (W3 (L2F 𝕜 Ω (Fin 1)) (L2F 𝕜 Ω (Fin 1 × Fin 3)) (L2F 𝕜 Ω (Fin 1 × Fin 3)))}
    (hU : Evolution.IsStrongSolution (M.maxwell (pec 𝕜 hΩ)) (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ M.gauss (pec 𝕜 hΩ) (magneticPEC 𝕜 Ω))
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ M.gauss (pec 𝕜 hΩ) (magneticPEC 𝕜 Ω)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ M.gauss (pec 𝕜 hΩ) (magneticPEC 𝕜 Ω) :=
  M.gauss_propagates _ (curl_mem_magneticPEC hΩ) hU h0 hF

/-- **Maxwell in a medium with a perfect magnetic conductor** on any open `Ω ⊆ ℝ³`: the weighted
Gauss laws propagate. -/
theorem pmc_gauss_propagates_medium {t₀ t₁ : ℝ}
    {F U : ℝ → PiLp 2 (W3 (L2F 𝕜 Ω (Fin 1)) (L2F 𝕜 Ω (Fin 1 × Fin 3)) (L2F 𝕜 Ω (Fin 1 × Fin 3)))}
    (hU : Evolution.IsStrongSolution (M.maxwell (pmc 𝕜 hΩ)) (Icc t₀ t₁) F U)
    (h0 : U t₀ ∈ M.gauss (pmc 𝕜 hΩ) (magneticPMC 𝕜 Ω))
    (hF : ∀ t ∈ Icc t₀ t₁, F t ∈ M.gauss (pmc 𝕜 hΩ) (magneticPMC 𝕜 Ω)) :
    ∀ t ∈ Icc t₀ t₁, U t ∈ M.gauss (pmc 𝕜 hΩ) (magneticPMC 𝕜 Ω) :=
  M.gauss_propagates _ (curl_mem_magneticPMC hΩ) hU h0 hF

end Conductor

end Feec.Maxwell
