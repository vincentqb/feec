module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Degrees of freedom, unisolvence and commuting interpolants

A finite element is a space `P` of shape functions with degrees of freedom (DOFs)
`ℓ : ι → P →ₗ[R] R`. The DOFs are *unisolvent* when `p ↦ (ℓ i p)ᵢ` is a bijection
`P ≃ (ι → R)`. If the DOFs extend to a larger space `Y ⊇ P` (`m i ∘ incl = ℓ i`), the canonical
interpolant `Π : Y → P` is defined by `ℓ i (Π y) = m i y`. It commutes with a differential
`d : Y → Y'` as soon as each DOF of `d y` is a linear combination of DOFs of `y`.

Everything is algebraic: modules over a commutative ring `R`, any index types. The unisolvent
DOFs `ω ↦ ∫_f tr_f ω ∧ μ` of `P_rΛᵏ(T)` and `P_r⁻Λᵏ(T)` and their canonical cochain projections
([QuennevilleBelair2015], §4.7, after [Arnold2013]) are the motivating instances; the integrals,
simplices and triangulations themselves are not formalized here. The thesis then combines these
projections with smoothers as in [AFW2010] to get bounded cochain projections `π_hᵏ : L²Λᵏ → Λ_hᵏ`
([QuennevilleBelair2015], Thm 4.15); that smoothing construction is out of scope, and only its
abstract consequences are formalized (`Feec.HilbertComplex.Subcomplex.CochainProjection`).

## Main definitions

* `Feec.FiniteElement.IsUnisolvent ℓ`: `LinearMap.pi ℓ` is bijective.
* `Feec.FiniteElement.interp hℓ m`: the canonical interpolant `Y → P` defined by the DOFs `m`.

## Main results

* `isUnisolvent_iff_forall_eq_zero`: over a field with `dim P = #ι`, unisolvence is the
  vanishing criterion `(∀ i, ℓ i p = 0) → p = 0`.
* `dof_interp`, `interp_incl`, `incl_interp_idem`: `Π` reproduces the DOFs, is a projection onto
  `P`.
* `interp_comp_eq`: **commuting interpolant** `Π' (d y) = d_h (Π y)`.
* `comp_eq_of_dof`, `dof_vanish_of_mem_span`, `comp_eq_of_mem_span`: the DOF argument behind
  the commuting property (5.4) of thesis Prop 5.7, without the invalid density step.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.7, Prop 5.7 (§5.3)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (degrees of freedom, canonical projections)
* [D. N. Arnold, *Spaces of finite element differential forms*][Arnold2013] (degrees of freedom,
  canonical projections)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
  (bounded cochain projections from canonical projections and smoothers)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5 (degrees of freedom,
  canonical projections)
-/

@[expose] public noncomputable section

namespace Feec.FiniteElement

variable {R : Type*} [CommRing R]

section Unisolvence

variable {P ι : Type*} [AddCommGroup P] [Module R P]

/-- The DOFs `ℓ` are **unisolvent** on `P`: every vector of values `(cᵢ)` is taken by exactly one
shape function. Abstracts the unisolvent DOF sets of `P_rΛᵏ(T)` and `P_r⁻Λᵏ(T)` of
[QuennevilleBelair2015], §4.7; see [Arnold2013]. -/
def IsUnisolvent (ℓ : ι → P →ₗ[R] R) : Prop := Function.Bijective (LinearMap.pi ℓ)

/-- Over a field, with as many DOFs as the dimension, unisolvence is the vanishing criterion (the
usual way unisolvence of the DOFs of [QuennevilleBelair2015], §4.7 is checked; see
[Arnold2013]). -/
theorem isUnisolvent_iff_forall_eq_zero {K : Type*} [Field K] {P : Type*} [AddCommGroup P]
    [Module K P] [FiniteDimensional K P] [Fintype ι] (ℓ : ι → P →ₗ[K] K)
    (hdim : Module.finrank K P = Fintype.card ι) :
    IsUnisolvent ℓ ↔ ∀ p, (∀ i, ℓ i p = 0) → p = 0 := by
  have hinj : Function.Injective (LinearMap.pi ℓ) ↔ ∀ p, (∀ i, ℓ i p = 0) → p = 0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    refine forall_congr' fun p => ?_
    simp [funext_iff]
  rw [IsUnisolvent, ← hinj]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [hdim, Module.finrank_fintype_fun_eq_card])).1 h

variable {ℓ : ι → P →ₗ[R] R}

/-- Shape functions are determined by their DOFs. -/
theorem IsUnisolvent.ext (hℓ : IsUnisolvent ℓ) {p q : P} (h : ∀ i, ℓ i p = ℓ i q) : p = q :=
  hℓ.1 (funext h)

/-- The shape function with prescribed DOF values. -/
def IsUnisolvent.equiv (hℓ : IsUnisolvent ℓ) : P ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofBijective (LinearMap.pi ℓ) hℓ

theorem IsUnisolvent.dof_equiv_symm (hℓ : IsUnisolvent ℓ) (c : ι → R) (i : ι) :
    ℓ i (hℓ.equiv.symm c) = c i :=
  congrFun (hℓ.equiv.apply_symm_apply c) i

end Unisolvence

section Interpolant

variable {P Y ι : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Y] [Module R Y]
  {ℓ : ι → P →ₗ[R] R} (hℓ : IsUnisolvent ℓ) (m : ι → Y →ₗ[R] R)

/-- The **canonical interpolant** `Π : Y → P`, `ℓ i (Π y) = m i y`: the canonical projection
defined by the DOFs, [QuennevilleBelair2015], §4.7; see [Arnold2013]. -/
def interp : Y →ₗ[R] P := hℓ.equiv.symm.toLinearMap ∘ₗ LinearMap.pi m

/-- `Π` reproduces the DOFs. -/
theorem dof_interp (y : Y) (i : ι) : ℓ i (interp hℓ m y) = m i y :=
  hℓ.dof_equiv_symm _ i

/-- `Π` is the identity on `P` when the DOFs of `Y` extend those of `P`. -/
theorem interp_incl (incl : P →ₗ[R] Y) (hm : ∀ i, m i ∘ₗ incl = ℓ i) (p : P) :
    interp hℓ m (incl p) = p :=
  hℓ.ext fun i => by rw [dof_interp, ← hm i, LinearMap.comp_apply]

/-- `incl ∘ Π` is a projection of `Y` onto `P`. -/
theorem incl_interp_idem (incl : P →ₗ[R] Y) (hm : ∀ i, m i ∘ₗ incl = ℓ i) (y : Y) :
    incl (interp hℓ m (incl (interp hℓ m y))) = incl (interp hℓ m y) := by
  rw [interp_incl hℓ m incl hm]

/-- **Commuting interpolant.** Let `Π : Y → P`, `Π' : Y' → P'` be canonical interpolants
(`incl`, `incl'` embed the shape functions), `d : Y → Y'` and `d_h : P → P'` with
`d ∘ incl = incl' ∘ d_h`. If each DOF `m' k ∘ d` lies in the span of the DOFs `m i`, then
`Π' (d y) = d_h (Π y)`. [QuennevilleBelair2015], Prop 5.7 (abstract form)

See [QuennevilleBelair2015], Prop 5.7; cf. [AFW2006], [Arnold2013]. This is the commuting
property of the canonical cochain projections of [QuennevilleBelair2015], §4.7. The thesis
combines them with smoothers as in [AFW2010] to obtain bounded cochain projections; the
smoothing is not formalized, only the bounded-cochain-projection consequences
(`Feec.HilbertComplex.Subcomplex.CochainProjection`). -/
theorem interp_comp_eq {P' Y' κ : Type*} [AddCommGroup P'] [Module R P'] [AddCommGroup Y']
    [Module R Y'] {ℓ' : κ → P' →ₗ[R] R} (hℓ' : IsUnisolvent ℓ') (m' : κ → Y' →ₗ[R] R)
    (incl : P →ₗ[R] Y) (incl' : P' →ₗ[R] Y') (hm : ∀ i, m i ∘ₗ incl = ℓ i)
    (hm' : ∀ k, m' k ∘ₗ incl' = ℓ' k) (d : Y →ₗ[R] Y') (dh : P →ₗ[R] P')
    (hd : d ∘ₗ incl = incl' ∘ₗ dh) (hspan : ∀ k, m' k ∘ₗ d ∈ Submodule.span R (Set.range m))
    (y : Y) : interp hℓ' m' (d y) = dh (interp hℓ m y) := by
  refine hℓ'.ext fun k => ?_
  rw [dof_interp, ← hm' k, LinearMap.comp_apply, ← LinearMap.comp_apply incl' dh, ← hd,
    LinearMap.comp_apply, ← LinearMap.comp_apply (m' k) d, ← LinearMap.comp_apply (m' k) d]
  -- both sides are values of `f = m' k ∘ d ∈ span m`, which only sees DOFs
  have key : ∀ f ∈ Submodule.span R (Set.range m), f y = f (incl (interp hℓ m y)) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← LinearMap.comp_apply (m i) incl, hm i, dof_interp]
    | zero => simp
    | add x z _ _ hx hz => simp [hx, hz]
    | smul a x _ hx => simp [hx]
  exact key _ (hspan k)

end Interpolant

section DofArgument

variable {Y X ι κ : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup X] [Module R X]

/-- **Abstract core of thesis Prop 5.7** ((5.4) for canonical projections): `Π¹` depends only
on the DOFs `ℓ_k`, `Π̃⁰` preserves the DOFs `m_i`, and every `ℓ_k ∘ S₀` vanishes on the joint
kernel of the `m_i`. Then `Π¹S₀Π̃⁰ = Π¹S₀` (no density argument).
[QuennevilleBelair2015], Prop 5.7 (abstract form)

See [QuennevilleBelair2015], Prop 5.7 (§5.3), with the DOFs of §4.7; cf. [AFW2006],
[Arnold2013]. -/
theorem comp_eq_of_dof (m : ι → Y →ₗ[R] R) (ℓ : κ → X →ₗ[R] R) (S0 : Y →ₗ[R] X)
    (Pt0 : Y →ₗ[R] Y) (P1 : X →ₗ[R] X)
    (hP1 : ∀ x y, (∀ k, ℓ k x = ℓ k y) → P1 x = P1 y)
    (hPt0 : ∀ i ψ, m i (Pt0 ψ) = m i ψ)
    (hS : ∀ ω, (∀ i, m i ω = 0) → ∀ k, ℓ k (S0 ω) = 0) (ψ : Y) :
    P1 (S0 (Pt0 ψ)) = P1 (S0 ψ) := by
  refine hP1 _ _ fun k => ?_
  have := hS (Pt0 ψ - ψ) (fun i => by simp [hPt0]) k
  rwa [map_sub, map_sub, sub_eq_zero] at this

/-- The usual sufficient condition for `comp_eq_of_dof`: every `ℓ_k ∘ S₀` is a linear
combination of the `m_i`. See [QuennevilleBelair2015], Prop 5.7, (5.8). -/
theorem dof_vanish_of_mem_span (m : ι → Y →ₗ[R] R) (ℓ : κ → X →ₗ[R] R) (S0 : Y →ₗ[R] X)
    (hspan : ∀ k, ℓ k ∘ₗ S0 ∈ Submodule.span R (Set.range m)) :
    ∀ ω, (∀ i, m i ω = 0) → ∀ k, ℓ k (S0 ω) = 0 := by
  intro ω hω k
  have key : ∀ f ∈ Submodule.span R (Set.range m), f ω = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hω i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  exact key _ (hspan k)

/-- **Thesis Prop 5.7 (abstract form)**: (5.4) `Π¹S₀Π̃⁰ = Π¹S₀` from DOFs.
See [QuennevilleBelair2015], Prop 5.7. -/
theorem comp_eq_of_mem_span (m : ι → Y →ₗ[R] R) (ℓ : κ → X →ₗ[R] R) (S0 : Y →ₗ[R] X)
    (Pt0 : Y →ₗ[R] Y) (P1 : X →ₗ[R] X)
    (hP1 : ∀ x y, (∀ k, ℓ k x = ℓ k y) → P1 x = P1 y)
    (hPt0 : ∀ i ψ, m i (Pt0 ψ) = m i ψ)
    (hspan : ∀ k, ℓ k ∘ₗ S0 ∈ Submodule.span R (Set.range m)) (ψ : Y) :
    P1 (S0 (Pt0 ψ)) = P1 (S0 ψ) :=
  comp_eq_of_dof m ℓ S0 Pt0 P1 hP1 hPt0 (dof_vanish_of_mem_span m ℓ S0 hspan) ψ

end DofArgument

end Feec.FiniteElement
