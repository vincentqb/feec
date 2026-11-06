module

public import Solution.Defs
public import Feec.FiniteElement.PolyOrder

/-!
# The polynomial spaces of the challenge are those of `Feec`

`P_rΛᵏ`, `H_rΛᵏ`, `κ`, `P_r⁻Λᵏ` and the evaluation of the challenge are `Feec.Koszul.polyForm`,
`Feec.Koszul.homForm`, `Feec.Koszul.koszulₗ`, `Feec.Koszul.polyFormMinus` and
`Feec.FiniteElement.evalForm` (`polyForm_eq`, …); an admissible sequence of the challenge is a
`Feec.FiniteElement.PolySeq` (`PolySeq.toFeec`) with the same spaces (`PolySeq.space_eq`) and the
same orders (`PolySeq.polyOrderAt_iff`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3, §5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MvPolynomial

@[expose] public noncomputable section

namespace FEEC

variable {n : ℕ}

theorem mem_polyForm {r k : ℕ} {p : PolyForm n} :
    p ∈ polyForm r k ↔ ∀ s, (s.card = k → p s ∈ restrictTotalDegree (Fin n) ℝ r) ∧
      (s.card ≠ k → p s = 0) := by
  simp only [polyForm, Submodule.mem_pi, Set.mem_univ, true_implies]
  refine forall_congr' fun s => ?_
  by_cases hs : s.card = k <;> simp [hs]

theorem mem_homForm {r k : ℕ} {p : PolyForm n} :
    p ∈ homForm r k ↔ ∀ s, (s.card = k → p s ∈ homogeneousSubmodule (Fin n) ℝ r) ∧
      (s.card ≠ k → p s = 0) := by
  simp only [homForm, Submodule.mem_pi, Set.mem_univ, true_implies]
  refine forall_congr' fun s => ?_
  by_cases hs : s.card = k <;> simp [hs]

theorem polyForm_eq (r k : ℕ) : polyForm (n := n) r k = Feec.Koszul.polyForm ℝ (Fin n) r k := by
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

theorem homForm_eq (r k : ℕ) : homForm (n := n) r k = Feec.Koszul.homForm ℝ (Fin n) r k := by
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

theorem koszul_eq : koszul (n := n) = Feec.Koszul.koszulₗ ℝ (Fin n) := by
  refine LinearMap.ext fun p => funext fun s => ?_
  rw [koszul, LinearMap.pi_apply, LinearMap.sum_apply, Feec.Koszul.koszulₗ_apply, Feec.Koszul.koszul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply,
    sgn, Feec.ExteriorFibre.sgn, smul_eq_C_mul, map_pow, map_neg, map_one, mul_assoc]

theorem polyFormMinus_eq (r k : ℕ) :
    polyFormMinus (n := n) r k = Feec.Koszul.polyFormMinus ℝ (Fin n) r k := by
  cases r with
  | zero => rfl
  | succ r =>
    change polyForm r k ⊔ (homForm r (k + 1)).map koszul = _
    rw [polyForm_eq, homForm_eq, koszul_eq]
    rfl

theorem evalForm_eq : evalForm (n := n) = Feec.FiniteElement.evalForm n := by
  refine LinearMap.ext fun p => funext fun x => funext fun s => ?_
  simp [evalForm, Feec.FiniteElement.evalForm_apply]

namespace PolySeq

variable (S : PolySeq)

/-- The family of degree `k` of `S`. -/
def kind (k : ℕ) : Feec.FiniteElement.PolyKind :=
  if S.full k then .full else .trimmed

/-- An admissible sequence of the challenge as a `Feec.FiniteElement.PolySeq`. -/
def toFeec : Feec.FiniteElement.PolySeq where
  kind := S.kind
  deg := S.deg
  one_le_deg := S.one_le_deg
  transition k := by
    rcases S.transition k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [kind, h1], h2⟩
    · exact Or.inr ⟨by simp [kind, h1], h2⟩

theorem space_eq (k : ℕ) : S.space n k = S.toFeec.space n k := by
  change _ = (S.kind k).space n (S.deg k) k
  unfold space kind
  cases h : S.full k
  · simp only [Bool.false_eq_true, ↓reduceIte, Feec.FiniteElement.PolyKind.space_trimmed]
    rw [polyFormMinus_eq, evalForm_eq]; rfl
  · simp only [↓reduceIte, Feec.FiniteElement.PolyKind.space_full]
    rw [polyForm_eq, evalForm_eq]; rfl

theorem polyOrderAt_iff (s : ℕ) (j : ℤ) :
    S.PolyOrderAt n s j ↔ Feec.FiniteElement.PolyOrderAt n S.toFeec s j := by
  unfold PolyOrderAt Feec.FiniteElement.PolyOrderAt
  simp only [space_eq, polyForm_eq, evalForm_eq]
  rfl

end PolySeq

end FEEC
