module

public import Feec.HilbertComplex.Approximation.DiscreteHodge
public import Feec.HilbertComplex.Mixed

/-!
# Uniform stability of the discrete mixed Hodge Laplacian

For a finite-dimensional subcomplex `Vₕ` of a Hilbert complex with a `W`-bounded cochain
projection `π` (`‖π‖ ≤ C`), the Poincaré inequality of the continuous complex (constant `c_P`)
passes to the discrete complex with constant `C c_P` (`CochainProjection.poincare_toHilbertComplex`).
The discrete complex is itself a Hilbert complex, so the well-posedness theorem of the mixed
Hodge Laplacian (`Feec.HilbertComplex.existsUnique_mixed`) applies to it, with a stability
constant `16 (C c_P)²` **independent of the subcomplex**: this is the uniform discrete inf-sup
stability on which the quasi-optimal error analysis of mixed finite element methods rests.

## Main results

* `CochainProjection.poincare_toHilbertComplex`: the discrete Poincaré inequality, in the form
  required by `Feec.HilbertComplex.infSup_mixedForm`.
* `CochainProjection.infSup_mixedForm`: the discrete mixed form has the inf-sup constant
  `1 / (16 (C c_P)²)`.
* `CochainProjection.existsUnique_mixed`, `CochainProjection.norm_le_of_mixed`: uniform
  well-posedness of the discrete mixed Hodge Laplacian.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.4 (Thm 3.8: discrete stability; the quasi-optimal estimate Thm 3.9 also needs the harmonic
  gap, `CochainProjection.norm_sub_starProjection_harmonicW_le`)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5
-/

open scoped InnerProductSpace
open LinearPMap Feec.Variational

@[expose] public noncomputable section

namespace Feec.HilbertComplex.Subcomplex.CochainProjection

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} {S : H.Subcomplex} [∀ i, FiniteDimensional 𝕜 (S.V i)]
  (P : S.CochainProjection)

/-- **The discrete Poincaré inequality for the discrete complex**: with a `W`-bounded cochain
projection (`‖π x‖ ≤ C ‖x‖`) and the Poincaré inequality `‖z‖ ≤ c_P ‖d z‖` on `(𝔷ⁱ)ᗮ`, the
discrete complex satisfies `‖z‖ ≤ C c_P ‖dₕ z‖` on `(𝔷ₕⁱ)ᗮ`. -/
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
`1 / (16 (C c_P)²)`, independent of the subcomplex. -/
theorem infSup_mixedForm {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {cP C : ℝ}
    (hcP : 1 ≤ cP) (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (hπj : ∀ x, ‖P.π j x‖ ≤ C * ‖x‖) :
    InfSup (S.toHilbertComplex.mixedForm i j k) (1 / (16 * (C * cP) ^ 2)) :=
  S.toHilbertComplex.infSup_mixedForm hij hjk (one_le_mul_of_one_le_of_one_le hC hcP)
    (P.poincare_toHilbertComplex hij hPi (zero_le_one.trans hC) hπi)
    (P.poincare_toHilbertComplex hjk hPj (zero_le_one.trans hC) hπj)

/-- **Uniform well-posedness of the discrete mixed Hodge Laplacian**. -/
theorem existsUnique_mixed {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {cP C : ℝ}
    (hcP : 1 ≤ cP) (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (hπj : ∀ x, ‖P.π j x‖ ≤ C * ‖x‖) (f : S.V j) :
    ∃! x, S.toHilbertComplex.mixedForm i j k x = S.toHilbertComplex.mixedRHS i j f :=
  S.toHilbertComplex.existsUnique_mixed hij hjk (one_le_mul_of_one_le_of_one_le hC hcP)
    (P.poincare_toHilbertComplex hij hPi (zero_le_one.trans hC) hπi)
    (P.poincare_toHilbertComplex hjk hPj (zero_le_one.trans hC) hπj) f

/-- **Uniform stability of the discrete mixed Hodge Laplacian**: `‖xₕ‖ ≤ 16 (C c_P)² ‖fₕ‖`. -/
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
