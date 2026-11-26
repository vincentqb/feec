module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Degrees of freedom, unisolvence and commuting interpolants

Unisolvent degrees of freedom define canonical interpolants, which commute with a differential when
each degree of freedom of `d y` is a combination of those of `y` ([QuennevilleBelair2015], §4.7
(adapted), after [Arnold2013]).

## Main results

* `interp_comp_eq`: the commuting interpolant.
* `comp_eq_of_mem_span`: `Π¹S₀Π̃⁰ = Π¹S₀` from degrees of freedom.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [D. N. Arnold, *Spaces of finite element differential forms*][Arnold2013]

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.FiniteElement

variable {R : Type*} [CommRing R]

section Unisolvence

variable {P ι : Type*} [AddCommGroup P] [Module R P]

/-- The degrees of freedom `ℓ` are unisolvent on `P`: `p ↦ (ℓ i p)ᵢ` is bijective. -/
def IsUnisolvent (ℓ : ι → P →ₗ[R] R) : Prop := Function.Bijective (LinearMap.pi ℓ)

/-- Over a field with `dim P = #ι`, unisolvence is `(∀ i, ℓ i p = 0) → p = 0`. -/
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

theorem IsUnisolvent.ext (hℓ : IsUnisolvent ℓ) {p q : P} (h : ∀ i, ℓ i p = ℓ i q) : p = q :=
  hℓ.1 (funext h)

/-- The DOFs as a linear isomorphism `P ≃ (ι → R)`, `p ↦ (ℓ i p)ᵢ`. -/
def IsUnisolvent.equiv (hℓ : IsUnisolvent ℓ) : P ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofBijective (LinearMap.pi ℓ) hℓ

theorem IsUnisolvent.dof_equiv_symm (hℓ : IsUnisolvent ℓ) (c : ι → R) (i : ι) :
    ℓ i (hℓ.equiv.symm c) = c i :=
  congrFun (hℓ.equiv.apply_symm_apply c) i

end Unisolvence

section Interpolant

variable {P Y ι : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Y] [Module R Y]
  {ℓ : ι → P →ₗ[R] R} (hℓ : IsUnisolvent ℓ) (m : ι → Y →ₗ[R] R)

/-- The canonical interpolant `Π : Y → P`, `ℓ i (Π y) = m i y` ([QuennevilleBelair2015], §4.7). -/
def interp : Y →ₗ[R] P := hℓ.equiv.symm.toLinearMap ∘ₗ LinearMap.pi m

theorem dof_interp (y : Y) (i : ι) : ℓ i (interp hℓ m y) = m i y :=
  hℓ.dof_equiv_symm _ i

theorem interp_incl (incl : P →ₗ[R] Y) (hm : ∀ i, m i ∘ₗ incl = ℓ i) (p : P) :
    interp hℓ m (incl p) = p :=
  hℓ.ext fun i => by rw [dof_interp, ← hm i, LinearMap.comp_apply]

/-- The commuting interpolant: if `m ∘ incl = ℓ`, `m' ∘ incl' = ℓ'`, `d ∘ incl = incl' ∘ d_h` and
each `m' k ∘ d` lies in the span of the `m i`, then `Π' (d y) = d_h (Π y)`;
[QuennevilleBelair2015], Prop 5.7 (adapted). -/
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

theorem comp_eq_of_dof (m : ι → Y →ₗ[R] R) (ℓ : κ → X →ₗ[R] R) (S0 : Y →ₗ[R] X)
    (Pt0 : Y →ₗ[R] Y) (P1 : X →ₗ[R] X)
    (hP1 : ∀ x y, (∀ k, ℓ k x = ℓ k y) → P1 x = P1 y)
    (hPt0 : ∀ i ψ, m i (Pt0 ψ) = m i ψ)
    (hS : ∀ ω, (∀ i, m i ω = 0) → ∀ k, ℓ k (S0 ω) = 0) (ψ : Y) :
    P1 (S0 (Pt0 ψ)) = P1 (S0 ψ) := by
  refine hP1 _ _ fun k => ?_
  have := hS (Pt0 ψ - ψ) (fun i => by simp [hPt0]) k
  rwa [map_sub, map_sub, sub_eq_zero] at this

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

/-- `Π¹S₀Π̃⁰ = Π¹S₀` when every `ℓ_k ∘ S₀` is a combination of the `m_i`;
[QuennevilleBelair2015], Prop 5.7 (adapted). -/
theorem comp_eq_of_mem_span (m : ι → Y →ₗ[R] R) (ℓ : κ → X →ₗ[R] R) (S0 : Y →ₗ[R] X)
    (Pt0 : Y →ₗ[R] Y) (P1 : X →ₗ[R] X)
    (hP1 : ∀ x y, (∀ k, ℓ k x = ℓ k y) → P1 x = P1 y)
    (hPt0 : ∀ i ψ, m i (Pt0 ψ) = m i ψ)
    (hspan : ∀ k, ℓ k ∘ₗ S0 ∈ Submodule.span R (Set.range m)) (ψ : Y) :
    P1 (S0 (Pt0 ψ)) = P1 (S0 ψ) :=
  comp_eq_of_dof m ℓ S0 Pt0 P1 hP1 hPt0 (dof_vanish_of_mem_span m ℓ S0 hspan) ψ

end DofArgument

end Feec.FiniteElement
