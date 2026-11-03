module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Extensions of partial linear maps

`LinearPMap.eq_of_le_of_domain_le`: an extension `f ≤ g` with `D(g) ⊆ D(f)` is an equality, the
form in which an operator is identified with an extension (e.g. its adjoint).
`LinearPMap.apply_eq_of_eq'` evaluates equal partial maps at the same point.

## References

* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.2 (extensions)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public section

namespace LinearPMap

variable {R S : Type*} [Ring R] [Ring S] {σ : R →+* S} {E F : Type*} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module S F]

/-- An extension `f ≤ g` with `D(g) ⊆ D(f)` is an equality. -/
theorem eq_of_le_of_domain_le {f g : E →ₛₗ.[σ] F} (hle : f ≤ g) (h : g.domain ≤ f.domain) :
    f = g :=
  eq_of_le_of_domain_eq hle (le_antisymm hle.1 h)

/-- Evaluating equal partial maps. -/
theorem apply_eq_of_eq' {f g : E →ₛₗ.[σ] F} (h : f = g) (x : f.domain) :
    f x = g ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

end LinearPMap
