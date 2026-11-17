module

public import Feec.FiniteElement.Assembly
public import Feec.FiniteElement.LocalSpace

/-!
# Glued finite element forms are their pieces, and the pieces of `P₁Λ` are affine

Two facts about the glued spaces `Vₕᵏ = E.V M k` of an element family on a mesh
(`Feec.FiniteElement.LocalElement`):

* **`LocalElement.exists_piece_of_mem_V`**: a form of `Vₕᵏ` is, almost everywhere on each element
  `Ω ∩ T`, a form field of the local space `P(T)ᵏ` (the frontier of a simplex is null);
* **`exists_affine_of_mem_polySpace_one`**: the form fields of `P₁Λᵏ` are affine,
  `ω(x)_s = a_s + Σᵢ A_{s,i} xᵢ` (from `MvPolynomial.eval_eq_of_totalDegree_le_one`: a polynomial
  of total degree at most `1` is `c₀ + Σᵢ cᵢ Xᵢ`); so are those of `P₁⁻Λᵏ ⊆ P₁Λᵏ`, the Whitney
  forms.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3, §5

Bibliography: [references.bib](../../docs/references.bib)
-/

open MeasureTheory Set

@[expose] public section

namespace MvPolynomial

/-- A monomial of degree at most `1` is `1` or a variable. -/
theorem eq_zero_or_eq_single_of_sum_le_one {σ : Type*} (m : σ →₀ ℕ)
    (hm : (m.sum fun _ e => e) ≤ 1) : m = 0 ∨ ∃ i, m = Finsupp.single i 1 := by
  by_cases h0 : m = 0
  · exact Or.inl h0
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc; exact h0 (Finsupp.ext fun j => not_not.1 fun h => hc ⟨j, h⟩)
  refine Or.inr ⟨i, Finsupp.ext fun j => ?_⟩
  have hsub : ∀ t ⊆ m.support, ∑ l ∈ t, m l ≤ 1 := fun t ht =>
    (Finset.sum_le_sum_of_subset_of_nonneg ht fun _ _ _ => Nat.zero_le _).trans hm
  classical
  by_cases hij : j = i
  · subst hij
    have := hsub {j} (by simpa using hi)
    rw [Finsupp.single_eq_same]; simp at this; omega
  · rw [Finsupp.single_eq_of_ne hij]
    by_contra hj
    have := hsub {i, j} (by
      intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl <;> simpa)
    rw [Finset.sum_pair (Ne.symm hij)] at this
    omega

/-- **A polynomial of total degree at most `1` is affine**:
`p(x) = p₀ + Σᵢ p_{eᵢ} xᵢ`. -/
theorem eval_eq_of_totalDegree_le_one {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ 1) (x : Fin n → ℝ) :
    eval x p = p.coeff 0 + ∑ i, p.coeff (Finsupp.single i 1) * x i := by
  have hc : ∀ m, (C (p.coeff 0) + ∑ i, C (p.coeff (Finsupp.single i 1)) * X i :
      MvPolynomial (Fin n) ℝ).coeff m = (if 0 = m then p.coeff 0 else 0) +
        ∑ i, if Finsupp.single i 1 = m then p.coeff (Finsupp.single i 1) else 0 := fun m => by
    simp [coeff_C_mul, coeff_X, coeff_C]
  have hq : p = C (p.coeff 0) + ∑ i, C (p.coeff (Finsupp.single i 1)) * X i := by
    ext m
    rw [hc]
    by_cases hm : m ∈ p.support
    · rcases eq_zero_or_eq_single_of_sum_le_one m ((le_totalDegree hm).trans hp) with
        rfl | ⟨i, rfl⟩
      · simp
      · simp only [Finsupp.single_left_inj one_ne_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]
        split_ifs with h
        · exact absurd h.symm (Finsupp.single_ne_zero.2 one_ne_zero)
        · rw [zero_add]
    · have h0 : ∀ m', m' = m → p.coeff m' = 0 := fun m' h => h ▸ notMem_support_iff.1 hm
      have e1 : (if (0 : Fin n →₀ ℕ) = m then p.coeff 0 else 0) = 0 := by
        split_ifs with h
        · exact h0 _ h
        · rfl
      have e2 : (∑ i, if Finsupp.single i 1 = m then p.coeff (Finsupp.single i 1) else 0) = 0 :=
        Finset.sum_eq_zero fun i _ => by split_ifs with h; exacts [h0 _ h, rfl]
      rw [e1, e2, add_zero, h0 m rfl]
  conv_lhs => rw [hq]
  simp

end MvPolynomial

namespace Feec.FiniteElement

open Feec.Mesh Feec.Domain

variable {n : ℕ}

/-- **The form fields of `P₁Λᵏ` are affine**: `ω(x)_s = a_s + Σᵢ A_{s,i} xᵢ`. -/
theorem exists_affine_of_mem_polySpace_one {k : ℕ} {ω : FormField n} (h : ω ∈ polySpace n 1 k) :
    ∃ (a : Finset (Fin n) → ℝ) (A : Finset (Fin n) → Fin n → ℝ),
      ∀ x s, ω x s = a s + ∑ i, A s i * x i := by
  obtain ⟨Ω, hΩ, rfl⟩ := h
  exact ⟨fun s => (Ω s).coeff 0, fun s i => (Ω s).coeff (Finsupp.single i 1), fun x s =>
    (evalForm_apply Ω x s).trans (MvPolynomial.eval_eq_of_totalDegree_le_one _ (hΩ.2 s) x)⟩

/-- Almost every point of a simplex lies in its interior. -/
theorem ae_mem_interior_closedInterior (Ω : Set (Fin n → ℝ))
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ∀ᵐ x ∂volume.restrict (Ω ∩ T.closedInterior), x ∈ interior T.closedInterior := by
  have h0 := Convex.addHaar_frontier volume (convex_closedInterior T)
  have h1 : ∀ᵐ x ∂volume, x ∉ frontier T.closedInterior := measure_eq_zero_iff_ae_notMem.1 h0
  have h2 : ∀ᵐ x ∂volume.restrict (Ω ∩ T.closedInterior), x ∈ T.closedInterior :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right
      (ae_restrict_mem T.isCompact_closedInterior.isClosed.measurableSet)
  filter_upwards [ae_restrict_of_ae h1, h2] with x hx hx'
  by_contra hi
  exact hx ⟨subset_closure hx', hi⟩

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n)

/-- **The glued field is the element field almost everywhere on each simplex.** -/
theorem glue_ae_eq {k : ℤ} (v : E.Piecewise M k.toNat) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) (s : formIdx n k) :
    ⇑((E.glue M k v) s) =ᵐ[volume.restrict (M.domain ∩ T.closedInterior)]
      fun x => (v ⟨T, hT⟩ : FormField n) x s.1 := by
  have h1 : ⇑((E.glue M k v) s) =ᵐ[volume.restrict M.domain]
      pieceFun M fun T => formComp (k := k) (E.extendPW M v T) s :=
    coeFn_pieceL2 M M.domain (fun T => formComp (k := k) (E.extendPW M v T))
      (fun T hT s => continuous_formComp (E.contDiff_extendPW M v hT).continuous s) s
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left h1,
    ae_mem_interior_closedInterior M.domain T] with x hx hx'
  rw [hx, pieceFun_of_mem_interior M _ hT hx', ← E.extendPW_of_mem M v hT]
  rfl

/-- **A form of `Vₕᵏ` is, on each element, a field of the local space**: almost everywhere on
`Ω ∩ T` it agrees with some `w ∈ P(T)ᵏ`. -/
theorem exists_piece_of_mem_V {k : ℤ} {u : L2F ℝ M.domain (formIdx n k)} (hu : u ∈ E.V M k)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    ∃ w ∈ E.space T k.toNat, ∀ s : formIdx n k,
      ⇑(u s) =ᵐ[volume.restrict (M.domain ∩ T.closedInterior)] fun x => w x s.1 := by
  obtain ⟨v, rfl⟩ := hu
  exact ⟨_, (v.1 ⟨T, hT⟩).2, fun s => E.glue_ae_eq M v.1 hT s⟩

end LocalElement

end Feec.FiniteElement
