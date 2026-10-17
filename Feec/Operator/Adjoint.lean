module

public import Feec.ForMathlib.LinearPMap.Skew
public import Feec.ForMathlib.LinearPMap.GraphSpace
public import Feec.ForMathlib.LinearPMap.Reducing
public import Feec.ForMathlib.LinearPMap.Intertwines
public import Feec.ForMathlib.LinearPMap.ClosedRange
public import Feec.ForMathlib.LinearPMap.Bounded
public import Feec.ForMathlib.LinearPMap.CompPartial

/-!
# Adjoints of composable pairs `T : E → F`, `S : F → G` with `S T = 0`

The operator-level facts behind the dual of a Hilbert complex, stated for any pair of
operators with `R(T) ⊆ D(S)` and `S T = 0` (over `RCLike 𝕜`):

* `Feec.Operator.inner_adjoint_apply_eq_zero`: `⟪S† u, T v⟫ = 0`;
* `Feec.Operator.adjoint_mapsTo`: `R(S†) ⊆ D(T†)`; `Feec.Operator.adjoint_comp_eq_zero`:
  `T† S† = 0`;
* `Feec.Operator.range_le_ker`: `R(T) ⊆ N(S)`;
* `Feec.Operator.orthogonal_ker_le_ker_adjoint`: `N(S)ᗮ ⊆ N(T†)`, and
  `Feec.Operator.orthogonal_ker_adjoint_le_ker`: `N(T†)ᗮ ⊆ N(S)` for closed `S`
  (both without any closed-range hypothesis).

This module also re-exports the `LinearPMap` API of `Feec.ForMathlib.LinearPMap.*`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (dual complex)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.Operator

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] G}

omit [CompleteSpace E] in
/-- `⟪S† u, T v⟫ = 0` when `S T = 0`. -/
theorem inner_adjoint_apply_eq_zero (hS : Dense (S.domain : Set F))
    (hmaps : ∀ x : T.domain, T x ∈ S.domain) (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0)
    (u : S†.domain) (v : T.domain) : ⟪S† u, T v⟫_𝕜 = 0 := by
  have := adjoint_isFormalAdjoint hS u ⟨T v, hmaps v⟩
  rw [hcomp, inner_zero_right] at this
  exact this

/-- `R(S†) ⊆ D(T†)` when `S T = 0`. -/
theorem adjoint_mapsTo (hS : Dense (S.domain : Set F))
    (hmaps : ∀ x : T.domain, T x ∈ S.domain) (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0)
    (u : S†.domain) : S† u ∈ T†.domain :=
  mem_adjoint_domain_of_exists _ ⟨0, fun v => by
    rw [inner_zero_left, inner_adjoint_apply_eq_zero hS hmaps hcomp]⟩

/-- `T† S† = 0` when `S T = 0`. -/
theorem adjoint_comp_eq_zero (hT : Dense (T.domain : Set E)) (hS : Dense (S.domain : Set F))
    (hmaps : ∀ x : T.domain, T x ∈ S.domain) (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0)
    (u : S†.domain) : T† ⟨S† u, adjoint_mapsTo hS hmaps hcomp u⟩ = 0 :=
  adjoint_apply_eq hT _ fun v => by
    rw [inner_zero_left, inner_adjoint_apply_eq_zero hS hmaps hcomp]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `R(T) ⊆ N(S)` when `S T = 0`. -/
theorem range_le_ker (hmaps : ∀ x : T.domain, T x ∈ S.domain)
    (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0) : LinearMap.range T.toFun ≤ S.ker := by
  rintro _ ⟨x, rfl⟩
  exact (LinearPMap.mem_ker_iff).2 ⟨⟨_, hmaps x⟩, rfl, hcomp x⟩

omit [CompleteSpace F] in
/-- `N(S)ᗮ ⊆ N(T†)` when `S T = 0` and `T` is densely defined (no closed range needed). -/
theorem orthogonal_ker_le_ker_adjoint (hT : Dense (T.domain : Set E))
    (hmaps : ∀ x : T.domain, T x ∈ S.domain) (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0) :
    S.kerᗮ ≤ T†.ker := by
  rw [← orthogonal_range_eq_ker_adjoint T hT]
  exact Submodule.orthogonal_le (range_le_ker hmaps hcomp)

/-- `N(T†)ᗮ = cl R(T) ⊆ N(S)` when `S T = 0`, `T` is densely defined and `S` is closed. -/
theorem orthogonal_ker_adjoint_le_ker (hT : Dense (T.domain : Set E)) (hSc : S.IsClosed)
    (hmaps : ∀ x : T.domain, T x ∈ S.domain) (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0) :
    T†.kerᗮ ≤ S.ker := by
  rw [← orthogonal_range_eq_ker_adjoint T hT, Submodule.orthogonal_orthogonal_eq_closure]
  exact Submodule.topologicalClosure_minimal _ (range_le_ker hmaps hcomp) (isClosed_ker hSc)

end Feec.Operator
