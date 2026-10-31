module

public import Solution.Bridge
public import Feec.HilbertComplex.Approximation.CochainProjectionExistence

/-!
# The bridge for the converse

The discrete Poincaré inequality and the harmonic bound of the challenge are those of `Feec`
(`Subcomplex.PoincareBy.toFeec`, `Subcomplex.poincareBy_of_feec`,
`Subcomplex.harmonicBound_iff`), and a `Feec` cochain projection of the subcomplex restricts to the
domain complex as a cochain projection of the challenge with the same graph-norm bound
(`Subcomplex.CochainProjection.ofFeec`, `Subcomplex.CochainProjection.graphNorm_ofFeec_le`). The
compared theorems `FEEC.exists_cochainProjection` and `FEEC.exists_subcomplexFamily_iff` follow from
`Feec.HilbertComplex.Subcomplex.exists_cochainProjection` and
`Feec.HilbertComplex.Subcomplex.exists_isGraphBounded_iff`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3, Thms 3.6, 3.7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

namespace Subcomplex

variable {H : HilbertComplex 𝕜 W} {S : H.Subcomplex}

theorem cyclesW_eq (i : ℤ) : S.toFeec.cyclesW i = S.cycles i := by
  change S.V i ⊓ H.toFeec.cycles i = _
  rw [H.cycles_eq]
  rfl

/-- **The discrete Poincaré inequality transfers** to `Feec`. -/
theorem PoincareBy.toFeec {i : ℤ} {C : ℝ} (h : S.PoincareBy i C) :
    S.toFeec.DiscretePoincare i C := by
  refine (S.toFeec.discretePoincare_iff_of_rel (rel_add_one i)).2 fun x hx hxo => ?_
  have h1 := h x hx fun z hz => hxo z ((cyclesW_eq (S := S) i).symm ▸ hz)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (by positivity), mul_pow] at h2
  exact h2

/-- **The discrete Poincaré inequality of `Feec`** gives that of the challenge, with `|C|`. -/
theorem poincareBy_of_feec {i : ℤ} {C : ℝ} (h : S.toFeec.DiscretePoincare i C) :
    S.PoincareBy i |C| := by
  rw [S.toFeec.discretePoincare_iff_of_rel (rel_add_one i)] at h
  intro v hv hvo
  have h1 := h hv fun z hz => hvo z ((cyclesW_eq (S := S) i) ▸ hz)
  unfold graphNorm
  rw [← Real.sqrt_sq (mul_nonneg (abs_nonneg C) (norm_nonneg _)), mul_pow, sq_abs]
  exact Real.sqrt_le_sqrt h1

theorem harmonicBound_iff {i : ℤ} {C : ℝ} :
    S.toFeec.HarmonicBound i C ↔ S.HarmonicBoundBy i C := by
  unfold Feec.HilbertComplex.Subcomplex.HarmonicBound HarmonicBoundBy
  rw [harmonic_eq]
  refine forall₂_congr fun q _ => ?_
  rw [starProjection_congr (H.harmonic_eq i) q]

namespace CochainProjection

/-- **A `Feec` cochain projection restricted to the domain complex** is a cochain projection of
the challenge. -/
def ofFeec (P : S.toFeec.CochainProjection) : S.CochainProjection where
  π i := LinearMap.codRestrict (S.V i) (P.π i ∘ₗ (H.d i (i + 1)).domain.subtype)
    fun x => P.mem i x
  proj i x hx := P.proj i x hx
  comm i x := P.comm i (i + 1) x

/-- The graph-norm bound of `Feec` is that of the challenge. -/
theorem graphNorm_ofFeec_le (P : S.toFeec.CochainProjection) {i : ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hπ : P.IsGraphBounded i ((ComplexShape.up ℤ).next i) C) (x : (H.d i (i + 1)).domain) :
    H.graphNorm i (i + 1) ⟨(ofFeec P).π i x, S.le_domain i (i + 1) ((ofFeec P).π i x).2⟩ ≤
      C * H.graphNorm i (i + 1) x := by
  have h := hπ.of_next (rel_add_one i) x
  unfold graphNorm
  rw [← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg C)]
  exact Real.sqrt_le_sqrt h

end CochainProjection

end Subcomplex

end HilbertComplex

end FEEC
