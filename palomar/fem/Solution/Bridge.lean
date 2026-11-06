module

public import Solution.Defs
public import Feec.HilbertComplex.Approximation.StaticFEEC

/-!
# The bridge from the challenge to `Feec`

The converse of `Solution.Complex`, as in the Palomar entry `palomar/feec` (`Solution.Bridge`
there, restricted to what the evolutions need): a Hilbert complex of the challenge is a
`Feec.HilbertComplex` on `ComplexShape.up ℤ` (`HilbertComplex.toFeec`, the same fields), and so
are its subcomplexes; a cochain projection of the challenge, defined on the domain complex only,
extends linearly to `W` (`CochainProjection.extend`: continuously where it is bounded in `W`,
otherwise along an algebraic complement of `D(d)`), which is a `Feec` cochain projection
(`CochainProjection.toFeec`). A family of subcomplexes is a
`Feec.HilbertComplex.SubcomplexFamily` (`SubcomplexFamily.toFeec`), to which the graph-norm bounds
transfer degree by degree (`SubcomplexFamily.isGraphBoundedBy_toFeec`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-- The complex as a `Feec` Hilbert complex on `ComplexShape.up ℤ`. -/
def toFeec : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W where
  d := H.d
  shape := H.shape
  dense := H.dense
  closed := H.closed
  mapsTo := H.mapsTo
  d_comp_d := H.d_comp_d

theorem rel_add_one (i : ℤ) : (ComplexShape.up ℤ).Rel i (i + 1) := rfl

theorem rel_sub_one (i : ℤ) : (ComplexShape.up ℤ).Rel (i - 1) i := sub_add_cancel i 1

theorem boundaries_eq (i : ℤ) : H.toFeec.boundaries i = H.boundaries i :=
  H.toFeec.boundaries_eq (rel_sub_one i)

theorem closedRangeAt_iff (i : ℤ) :
    H.toFeec.ClosedRangeAt i ↔ IsClosed (H.boundaries i : Set (W i)) := by
  rw [Feec.HilbertComplex.ClosedRangeAt, boundaries_eq]

/-- A linear projection of `Wⁱ` onto `D(dⁱ)`, along an algebraic complement. -/
def domainProj (i : ℤ) : W i →ₗ[𝕜] (H.d i (i + 1)).domain :=
  Submodule.projectionOnto _ _ (Submodule.exists_isCompl (H.d i (i + 1)).domain).choose_spec

theorem domainProj_apply {i : ℤ} (x : (H.d i (i + 1)).domain) : H.domainProj i x = x :=
  Submodule.projectionOnto_apply_left _ x

namespace Subcomplex

variable {H} (S : H.Subcomplex)

/-- The subcomplex as a `Feec` subcomplex. -/
def toFeec : H.toFeec.Subcomplex := ⟨S.V, S.le_domain, S.mapsTo⟩

instance [∀ i, FiniteDimensional 𝕜 (S.V i)] (i : ℤ) : FiniteDimensional 𝕜 (S.toFeec.V i) :=
  ‹∀ i, FiniteDimensional 𝕜 (S.V i)› i

namespace CochainProjection

variable {S} (P : S.CochainProjection)

/-- **The cochain projection extended to `W`**: where `π` is bounded in the norm of `W` on `D(d)`
and `V` is closed, its continuous extension (`D(d)` is dense); otherwise `π` after a linear
projection onto `D(d)` along an algebraic complement (not continuous). Linear; it agrees with `π`
on `D(d)` and takes values in `V`. -/
def extend (i : ℤ) : W i →ₗ[𝕜] W i := by
  classical
  exact if hb : (∃ C, ∀ x : (H.d i (i + 1)).domain, ‖(P.π i x : W i)‖ ≤ C * ‖(x : W i)‖) ∧
      IsClosed (S.V i : Set (W i)) then
    haveI := hb.2.completeSpace_coe
    (S.V i).subtype ∘ₗ ((P.π i).extendOfNorm (H.d i (i + 1)).domain.subtype :
      W i →L[𝕜] S.V i).toLinearMap
  else (S.V i).subtype ∘ₗ P.π i ∘ₗ H.domainProj i

theorem extend_mem (i : ℤ) (x : W i) : P.extend i x ∈ S.V i := by
  unfold extend
  split_ifs with hb
  · exact Submodule.coe_mem _
  · exact Submodule.coe_mem _

theorem extend_apply {i : ℤ} (x : (H.d i (i + 1)).domain) : P.extend i x = P.π i x := by
  unfold extend
  split_ifs with hb
  · have := hb.2.completeSpace_coe
    obtain ⟨C, hC⟩ := hb.1
    change (((P.π i).extendOfNorm (H.d i (i + 1)).domain.subtype :
      W i →L[𝕜] S.V i) ((H.d i (i + 1)).domain.subtype x) : W i) = _
    rw [LinearMap.extendOfNorm_eq (H.dense i (i + 1)).denseRange_val ⟨C, fun y => hC y⟩]
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, domainProj_apply]

/-- **The continuous extension is bounded in `W`**: a bound `‖π x‖ ≤ C ‖x‖` on `D(d)` with `V`
closed gives `‖π x‖ ≤ max C 0 ‖x‖` for the extension on all of `W`. -/
theorem norm_extend_le {i : ℤ} {C : ℝ}
    (hC : ∀ x : (H.d i (i + 1)).domain, ‖(P.π i x : W i)‖ ≤ C * ‖(x : W i)‖)
    (hV : IsClosed (S.V i : Set (W i))) (x : W i) : ‖P.extend i x‖ ≤ max C 0 * ‖x‖ := by
  classical
  have hb : (∃ C, ∀ x : (H.d i (i + 1)).domain, ‖(P.π i x : W i)‖ ≤ C * ‖(x : W i)‖) ∧
      IsClosed (S.V i : Set (W i)) := ⟨⟨C, hC⟩, hV⟩
  have := hV.completeSpace_coe
  set g : W i →L[𝕜] S.V i := (P.π i).extendOfNorm (H.d i (i + 1)).domain.subtype
  have e : ∀ y, P.extend i y = g y := fun y => by
    unfold extend
    split_ifs
    rfl
  rw [e]
  have hd := (H.dense i (i + 1)).denseRange_val
  refine hd.induction_on (p := fun y => ‖(g y : W i)‖ ≤ max C 0 * ‖y‖) x
    (isClosed_le (continuous_norm.comp (continuous_subtype_val.comp g.continuous))
      (continuous_const.mul continuous_norm)) fun y => ?_
  change ‖(g ((H.d i (i + 1)).domain.subtype y) : W i)‖ ≤ _
  rw [LinearMap.extendOfNorm_eq hd ⟨C, fun z => hC z⟩]
  exact (hC y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- The extended cochain projection as a `Feec` cochain projection. -/
def toFeec : S.toFeec.CochainProjection where
  π := P.extend
  mem i x := P.extend_mem i x
  proj i x hx := (P.extend_apply ⟨x, S.le_domain i (i + 1) hx⟩).trans (P.proj i _ hx)
  comm i j x := by
    by_cases hij : i + 1 = j
    · subst hij
      have e1 : (⟨P.extend i x, S.le_domain i (i + 1) (P.extend_mem i x)⟩ :
          (H.d i (i + 1)).domain) = ⟨P.π i x, S.le_domain i (i + 1) (P.π i x).2⟩ :=
        Subtype.ext (P.extend_apply x)
      exact (congrArg (H.d i (i + 1)) e1).trans ((P.comm i x).trans
        (P.extend_apply ⟨_, H.mapsTo i (i + 1) (i + 1 + 1) x⟩).symm)
    · have h0 := H.shape i j hij
      refine (apply_eq_zero_of_eq_zero h0 _).trans ?_
      show (0 : W j) = P.extend j (H.d i j x)
      rw [apply_eq_zero_of_eq_zero h0 x, _root_.map_zero]

theorem toFeec_π_apply {i : ℤ} (x : (H.d i (i + 1)).domain) : P.toFeec.π i x = P.π i x :=
  P.extend_apply x

end CochainProjection

end Subcomplex

variable {H} {κ : Type*}

/-- The family as a `Feec` family of subcomplexes. -/
def SubcomplexFamily.toFeec (F : H.SubcomplexFamily κ) :
    Feec.HilbertComplex.SubcomplexFamily H.toFeec κ where
  l := F.l
  V h := (F.V h).toFeec
  finiteDimensional h i := F.finiteDimensional h i
  π h := (F.π h).toFeec

/-- **Graph-norm bounds transfer**: `‖π x‖_V ≤ C ‖x‖_V` is `Feec`'s bound, squared, at every
`k = i + 1`. -/
theorem SubcomplexFamily.isGraphBoundedBy_toFeec {F : H.SubcomplexFamily κ} {i k : ℤ}
    (hik : i + 1 = k) {C : ℝ} (hπ : F.IsGraphBoundedBy i C) (h : κ) :
    (F.toFeec.π h).IsGraphBounded i k C := by
  subst hik
  intro x
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hπ h x) 2
  unfold graphNorm at h2
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h2
  have e1 : ‖(F.toFeec.π h).π i x‖ = ‖((F.π h).π i x : W i)‖ :=
    congrArg norm ((F.π h).extend_apply x)
  have e2 : ‖H.toFeec.d i (i + 1) ⟨(F.toFeec.π h).π i x,
      (F.toFeec.V h).le_domain i (i + 1) ((F.toFeec.π h).mem i x)⟩‖ =
      ‖H.d i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).π i x).2⟩‖ :=
    congrArg (fun y => ‖H.d i (i + 1) y‖) (Subtype.ext ((F.π h).extend_apply x))
  exact (congrArg₂ (· + ·) (congrArg (· ^ 2) e1) (congrArg (· ^ 2) e2)).trans_le h2

end HilbertComplex

end FEEC
