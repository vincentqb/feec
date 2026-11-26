module

public import Feec.HilbertComplex.Approximation.DiscreteHodge
public import Feec.HilbertComplex.Mixed

/-!
# Uniform stability of the discrete mixed Hodge Laplacian

With a cochain projection bounded by `C` in `W`, the discrete mixed Hodge Laplacian is well-posed
with a stability constant `16 (C c_P)²` independent of the subcomplex.

## Main results

* `Subcomplex.CochainProjection.poincare_toHilbertComplex`: the discrete Poincaré inequality.
* `Subcomplex.CochainProjection.infSup_mixedForm`: the uniform inf-sup condition.
* `Subcomplex.CochainProjection.norm_le_of_mixed`: uniform stability.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Feec.Variational

@[expose] public noncomputable section

namespace Feec.HilbertComplex.Subcomplex.CochainProjection

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} {S : H.Subcomplex} [∀ i, FiniteDimensional 𝕜 (S.V i)]
  (P : S.CochainProjection)

/-- **The discrete Poincaré inequality**: with `‖π‖ ≤ C`, the discrete complex has the Poincaré
constant `C c_P`. [AFW2010], Thm 3.6 -/
theorem poincare_toHilbertComplex {i j : ι} (hij : c.Rel i j) {cP C : ℝ}
    (hP : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hC : 0 ≤ C) (hπ : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) :
    ∀ z : (S.toHilbertComplex.d i j).domain,
      (z : S.V i) ∈ (S.toHilbertComplex.cycles i)ᗮ →
        ‖(z : S.V i)‖ ≤ C * cP * ‖S.toHilbertComplex.d i j z‖ := by
  intro z hz
  have hxo : ∀ y ∈ S.cyclesW i, ⟪y, ((z : S.V i) : W i)⟫_𝕜 = 0 := by
    intro y hy
    have hy' : (⟨y, (S.mem_cyclesW_iff.1 hy).1⟩ : S.V i) ∈ S.toHilbertComplex.cycles i :=
      S.mem_cycles_iff.2 (S.mem_cyclesW_iff.1 hy).2
    have := Submodule.inner_right_of_mem_orthogonal hy' hz
    rwa [Submodule.coe_inner] at this
  exact P.norm_le_of_forall_inner_eq_zero hij hP hC hπ (z : S.V i).2 hxo

/-- **Uniform inf-sup condition for the discrete mixed Hodge Laplacian**: constant
`1 / (16 (C c_P)²)`, independent of the subcomplex. [AFW2010], Thm 3.8 -/
theorem infSup_mixedForm {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {cP C : ℝ}
    (hcP : 1 ≤ cP) (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (hπj : ∀ x, ‖P.π j x‖ ≤ C * ‖x‖) :
    InfSup (S.toHilbertComplex.mixedForm i j k) (1 / (16 * (C * cP) ^ 2)) :=
  S.toHilbertComplex.infSup_mixedForm hij hjk (one_le_mul_of_one_le_of_one_le hC hcP)
    (P.poincare_toHilbertComplex hij hPi (zero_le_one.trans hC) hπi)
    (P.poincare_toHilbertComplex hjk hPj (zero_le_one.trans hC) hπj)

/-- **Well-posedness of the discrete mixed Hodge Laplacian.** [AFW2010], Thm 3.8 -/
theorem existsUnique_mixed {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {cP C : ℝ}
    (hcP : 1 ≤ cP) (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (hπj : ∀ x, ‖P.π j x‖ ≤ C * ‖x‖) (f : S.V j) :
    ∃! x, S.toHilbertComplex.mixedForm i j k x = S.toHilbertComplex.mixedRHS i j f :=
  S.toHilbertComplex.existsUnique_mixed hij hjk (one_le_mul_of_one_le_of_one_le hC hcP)
    (P.poincare_toHilbertComplex hij hPi (zero_le_one.trans hC) hπi)
    (P.poincare_toHilbertComplex hjk hPj (zero_le_one.trans hC) hπj) f

/-- **Uniform stability of the discrete mixed Hodge Laplacian**: `‖xₕ‖ ≤ 16 (C c_P)² ‖fₕ‖`.
[AFW2010], Thm 3.8 -/
theorem norm_le_of_mixed {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {cP C : ℝ}
    (hcP : 1 ≤ cP) (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (hπj : ∀ x, ‖P.π j x‖ ≤ C * ‖x‖) {f : S.V j}
    {x : S.toHilbertComplex.MixedSpace i j}
    (hx : S.toHilbertComplex.mixedForm i j k x = S.toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (C * cP) ^ 2 * ‖f‖ :=
  S.toHilbertComplex.norm_le_of_mixed hij hjk (one_le_mul_of_one_le_of_one_le hC hcP)
    (P.poincare_toHilbertComplex hij hPi (zero_le_one.trans hC) hπi)
    (P.poincare_toHilbertComplex hjk hPj (zero_le_one.trans hC) hπj) hx

end Feec.HilbertComplex.Subcomplex.CochainProjection
