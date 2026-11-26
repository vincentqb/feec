module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Extensions of partial linear maps

An extension `f ≤ g` of partial linear maps with `D(g) ⊆ D(f)` is an equality.
-/

@[expose] public section

namespace LinearPMap

variable {R S : Type*} [Ring R] [Ring S] {σ : R →+* S} {E F : Type*} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module S F]

theorem eq_of_le_of_domain_le {f g : E →ₛₗ.[σ] F} (hle : f ≤ g) (h : g.domain ≤ f.domain) :
    f = g :=
  eq_of_le_of_domain_eq hle (le_antisymm hle.1 h)

theorem apply_eq_of_eq' {f g : E →ₛₗ.[σ] F} (h : f = g) (x : f.domain) :
    f x = g ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

end LinearPMap
