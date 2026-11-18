module

public import Solution.Defs
public import Feec.FiniteElement.PolyOrder

/-!
# The polynomial spaces of the challenge are those of `Feec`

`P_rΛᵏ`, `H_rΛᵏ`, `κ`, `P_r⁻Λᵏ` and the evaluation of the challenge are `Feec.Koszul.polyForm`,
`Feec.Koszul.homForm`, `Feec.Koszul.koszulₗ`, `Feec.Koszul.polyFormMinus` and
`Feec.FiniteElement.evalForm` (`polyForm_eq`, …), and the exterior derivative of polynomial forms is
`Feec.Koszul.extDerivₗ` (`polyExtDeriv_eq`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MvPolynomial

@[expose] public noncomputable section

namespace FEEC

variable {n : ℕ} {K : Type*} [Field K]

theorem mem_polyForm {r k : ℕ} {p : PolyForm K n} :
    p ∈ polyForm K n r k ↔ ∀ s, (s.card = k → p s ∈ restrictTotalDegree (Fin n) K r) ∧
      (s.card ≠ k → p s = 0) := by
  simp only [polyForm, Submodule.mem_pi, Set.mem_univ, true_implies]
  refine forall_congr' fun s => ?_
  by_cases hs : s.card = k <;> simp [hs]

theorem mem_homForm {r k : ℕ} {p : PolyForm K n} :
    p ∈ homForm K n r k ↔ ∀ s, (s.card = k → p s ∈ homogeneousSubmodule (Fin n) K r) ∧
      (s.card ≠ k → p s = 0) := by
  simp only [homForm, Submodule.mem_pi, Set.mem_univ, true_implies]
  refine forall_congr' fun s => ?_
  by_cases hs : s.card = k <;> simp [hs]

theorem polyForm_eq (r k : ℕ) : polyForm K n r k = Feec.Koszul.polyForm K (Fin n) r k := by
  ext p
  rw [mem_polyForm]
  change _ ↔ Feec.ExteriorFibre.IsDeg k p ∧ ∀ s, (p s).totalDegree ≤ r
  constructor
  · intro h
    refine ⟨fun s hs => (h s).2 hs, fun s => ?_⟩
    by_cases hs : s.card = k
    · exact (mem_restrictTotalDegree _ _ _).1 ((h s).1 hs)
    · rw [(h s).2 hs, totalDegree_zero]; exact Nat.zero_le _
  · rintro ⟨h1, h2⟩ s
    exact ⟨fun _ => (mem_restrictTotalDegree _ _ _).2 (h2 s), h1 s⟩

theorem homForm_eq (r k : ℕ) : homForm K n r k = Feec.Koszul.homForm K (Fin n) r k := by
  ext p
  rw [mem_homForm]
  change _ ↔ Feec.ExteriorFibre.IsDeg k p ∧ Feec.Koszul.IsHomogeneousForm r p
  constructor
  · intro h
    refine ⟨fun s hs => (h s).2 hs, fun s => ?_⟩
    by_cases hs : s.card = k
    · exact (mem_homogeneousSubmodule _ _).1 ((h s).1 hs)
    · rw [(h s).2 hs]; exact isHomogeneous_zero _ _ _
  · rintro ⟨h1, h2⟩ s
    exact ⟨fun _ => (mem_homogeneousSubmodule _ _).2 (h2 s), h1 s⟩

theorem koszul_eq : koszul K n = Feec.Koszul.koszulₗ K (Fin n) := by
  refine LinearMap.ext fun p => funext fun s => ?_
  rw [koszul, LinearMap.pi_apply, LinearMap.sum_apply, Feec.Koszul.koszulₗ_apply, Feec.Koszul.koszul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply,
    sgn, Feec.ExteriorFibre.sgn, smul_eq_C_mul, map_pow, map_neg, map_one, mul_assoc]

theorem polyExtDeriv_eq : polyExtDeriv K n = Feec.Koszul.extDerivₗ K (Fin n) := by
  refine LinearMap.ext fun p => funext fun s => ?_
  rw [polyExtDeriv, LinearMap.pi_apply, LinearMap.sum_apply, Feec.Koszul.extDerivₗ_apply,
    Feec.Koszul.extDeriv_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, sgn,
    Feec.ExteriorFibre.sgn, smul_eq_C_mul, map_pow, map_neg, map_one]
  rfl

theorem polyFormMinus_eq (r k : ℕ) :
    polyFormMinus K n r k = Feec.Koszul.polyFormMinus K (Fin n) r k := by
  cases r with
  | zero => rfl
  | succ r =>
    change polyForm K n r k ⊔ (homForm K n r (k + 1)).map (koszul K n) = _
    rw [polyForm_eq, homForm_eq, koszul_eq]
    rfl

theorem evalForm_eq : evalForm (n := n) = Feec.FiniteElement.evalForm n := by
  refine LinearMap.ext fun p => funext fun x => funext fun s => ?_
  simp [evalForm, Feec.FiniteElement.evalForm_apply]


end FEEC
