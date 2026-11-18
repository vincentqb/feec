module

public import Solution.Family
public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.ForMathlib.Analysis.QuasiOptimal

/-!
# From `Feec`'s Hilbert complexes to the challenge's

A `Feec.HilbertComplex` on `ComplexShape.up ℤ` is a Hilbert complex of the challenge with the same
fields (`HilbertComplex.ofFeec`), and so are its subcomplexes (`Subcomplex.ofFeec`, the
subcomplexes of `Solution.Family`); a `Feec` cochain projection, defined on `W`, restricts to the
domain complex (`CochainProjection.ofFeec`). Cochain projections extending to uniformly bounded
projections of `W` attain the rate of every Jackson estimate (`Jackson.projRate`), by the
quasi-optimality of a bounded projection (`ContinuousLinearMap.norm_sub_apply_le_of_apply_eq`)
and the commutation `d π = π d`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5, §5.5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

/-- A `Feec` Hilbert complex on `ComplexShape.up ℤ` as a Hilbert complex of the challenge. -/
def ofFeec (G : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W) : HilbertComplex 𝕜 W where
  d := G.d
  shape := G.shape
  dense := G.dense
  closed := G.closed
  mapsTo := G.mapsTo
  d_comp_d := G.d_comp_d

variable {G : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W}

@[simp] theorem ofFeec_d (i j : ℤ) : (ofFeec G).d i j = G.d i j := rfl

/-- A `Feec` subcomplex as a subcomplex of the challenge. -/
def Subcomplex.ofFeec (S : G.Subcomplex) : (HilbertComplex.ofFeec G).Subcomplex where
  V := S.V
  le_domain := S.le_domain
  mapsTo := S.mapsTo

@[simp] theorem Subcomplex.ofFeec_V (S : G.Subcomplex) (i : ℤ) :
    (Subcomplex.ofFeec S).V i = S.V i := rfl

/-- A `Feec` cochain projection restricted to the domain complex. -/
def CochainProjection.ofFeec {S : G.Subcomplex} (P : S.CochainProjection) :
    (Subcomplex.ofFeec S).CochainProjection where
  π i := (P.π i).codRestrict (S.V i) (P.mem i) ∘ₗ (G.d i (i + 1)).domain.subtype
  proj i x hx := P.proj i x hx
  comm i x := P.comm i (i + 1) x

@[simp] theorem CochainProjection.ofFeec_π {S : G.Subcomplex} (P : S.CochainProjection) (i : ℤ)
    (x : (G.d i (i + 1)).domain) : ((CochainProjection.ofFeec P).π i x : W i) = P.π i x := rfl

/-- **Uniformly bounded projections attain the Jackson rate**: if the cochain projections of `F`
extend to projections `P` of `W` onto `Vₕ` with `‖P‖ ≤ C`, then `‖x - π x‖ ≤ (1 + C) ‖x - v‖`
and `‖d x - d π x‖ = ‖(1 - P) (d x - d v)‖ ≤ (1 + C) ‖d (x - v)‖` for the `v` of the Jackson
estimate, which `J` bounds. -/
theorem SubcomplexFamily.Jackson.projRate {H : HilbertComplex 𝕜 W} {κ ρ : Type*}
    {F : H.SubcomplexFamily κ} (J : F.Jackson ρ) {C : ℝ}
    (hP : ∀ h i, ∃ P : W i →L[𝕜] W i, ‖P‖ ≤ C ∧ (∀ x, P x ∈ (F.V h).V i) ∧
      ∀ x : (H.d i (i + 1)).domain, P x = ((F.π h).π i x : W i)) :
    J.ProjRate := by
  refine ⟨fun s i => (1 + C) * J.B s i, fun s h i L x hL hx => ?_⟩
  choose P hPC _ hPπ using hP
  have hfix : ∀ i (u : W i), u ∈ (F.V h).V i → P h i u = u := fun i u hu => by
    rw [hPπ h i ⟨u, (F.V h).le_domain i (i + 1) hu⟩]
    exact (F.π h).proj i _ hu
  have hC : 0 ≤ 1 + C := by linarith [(norm_nonneg _).trans (hPC h i)]
  obtain ⟨v, hv, h1, h2⟩ := J.jackson s h i (x : W i) hL hx
  set dv := H.d i (i + 1) ⟨v, (F.V h).le_domain i (i + 1) hv⟩
  have hdv : dv ∈ (F.V h).V (i + 1) := (F.V h).mapsTo i (i + 1) v hv
  refine ⟨?_, ?_⟩
  · rw [← hPπ h i x]
    calc ‖(x : W i) - P h i x‖ ≤ (1 + C) * ‖(x : W i) - v‖ :=
          (P h i).norm_sub_apply_le_of_apply_eq (hPC h i) (hfix i v hv) _
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hC
  · have hcomm := (F.π h).comm i x
    have e : H.d i (i + 1) ⟨_, (F.V h).le_domain i (i + 1) ((F.π h).π i x).2⟩ =
        P h (i + 1) (H.d i (i + 1) x) := by
      rw [hcomm, hPπ h (i + 1) ⟨_, H.mapsTo i (i + 1) (i + 1 + 1) x⟩]
    have e2 : H.d i (i + 1) x - dv = H.d i (i + 1)
        ⟨(x : W i) - v, Submodule.sub_mem _ x.2 ((F.V h).le_domain i (i + 1) hv)⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e]
    calc ‖H.d i (i + 1) x - P h (i + 1) (H.d i (i + 1) x)‖
        ≤ (1 + C) * ‖H.d i (i + 1) x - dv‖ :=
          (P h (i + 1)).norm_sub_apply_le_of_apply_eq (hPC h (i + 1)) (hfix _ dv hdv) _
      _ ≤ _ := by rw [e2, mul_assoc]; exact mul_le_mul_of_nonneg_left (h2 (i + 1) x.2) hC

end HilbertComplex

end FEEC
