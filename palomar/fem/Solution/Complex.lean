module

public import Solution.Defs
public import Feec.HilbertComplex.Approximation.ConformingFamily

/-!
# From `Feec`'s Hilbert complexes to the challenge's

A `Feec.HilbertComplex` on `ComplexShape.up ℤ` is a Hilbert complex of the challenge with the same
fields (`HilbertComplex.ofFeec`), and so are its subcomplexes (`Subcomplex.ofFeec`); a `Feec`
cochain projection, defined on `W`, restricts to the domain complex (`CochainProjection.ofFeec`).
The graph-norm bounds and the graph-norm approximation of `Feec` give those of the challenge
(`isGraphBoundedBy_of_feec`, `approximates_of_eventually`).

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

variable (H : HilbertComplex 𝕜 W)

theorem graphNorm_nonneg' {i j : ℤ} (x : (H.d i j).domain) : 0 ≤ H.graphNorm i j x :=
  Real.sqrt_nonneg _

/-- A squared graph-norm bound gives the graph-norm bound. -/
theorem graphNorm_le_of_sq {i j : ℤ} {x y : (H.d i j).domain} {C : ℝ} (hC : 0 ≤ C)
    (h : ‖(y : W i)‖ ^ 2 + ‖H.d i j y‖ ^ 2 ≤ C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)) :
    H.graphNorm i j y ≤ C * H.graphNorm i j x := by
  unfold graphNorm
  rw [← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg C)]
  exact Real.sqrt_le_sqrt h

/-- The graph-norm distance to a subcomplex is at most `√2 ε` if some point of it is within `ε`
of `x` in `W` and for `d`. -/
theorem graphDist_le (S : H.Subcomplex) {i j : ℤ} (x : (H.d i j).domain) {ε : ℝ}
    {v : W i} (hv : v ∈ S.V i) (h1 : ‖(x : W i) - v‖ < ε)
    (h2 : ‖H.d i j ⟨(x : W i) - v, Submodule.sub_mem _ x.2 (S.le_domain i j hv)⟩‖ < ε) :
    S.graphDist i j x ≤ √2 * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans h1.le
  refine (ciInf_le ⟨0, ?_⟩ ⟨v, hv⟩).trans ?_
  · rintro _ ⟨w, rfl⟩; exact H.graphNorm_nonneg' _
  · unfold graphNorm
    rw [show √2 * ε = √(2 * ε ^ 2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hε]]
    refine Real.sqrt_le_sqrt ?_
    have e : ((x - ⟨v, S.le_domain i j hv⟩ : (H.d i j).domain) : W i) = (x : W i) - v := rfl
    have e' : H.d i j (x - ⟨v, S.le_domain i j hv⟩) =
        H.d i j ⟨(x : W i) - v, Submodule.sub_mem _ x.2 (S.le_domain i j hv)⟩ := rfl
    rw [e, e']
    nlinarith [norm_nonneg ((x : W i) - v), norm_nonneg (H.d i j
      ⟨(x : W i) - v, Submodule.sub_mem _ x.2 (S.le_domain i j hv)⟩)]

theorem graphDist_nonneg (S : H.Subcomplex) {i j : ℤ} (x : (H.d i j).domain) :
    0 ≤ S.graphDist i j x :=
  Real.iInf_nonneg fun _ => H.graphNorm_nonneg' _

/-- **Approximation from eventual `ε`-approximation** in `W` and for `d`. -/
theorem approximates_of_eventually {κ : Type*} (F : H.SubcomplexFamily κ) (i : ℤ)
    (h : ∀ x : (H.d i (i + 1)).domain, ∀ ε > 0, ∀ᶠ h in F.l, ∃ v, ∃ hv : v ∈ (F.V h).V i,
      ‖(x : W i) - v‖ < ε ∧ ‖H.d i (i + 1)
        ⟨(x : W i) - v, Submodule.sub_mem _ x.2 ((F.V h).le_domain i (i + 1) hv)⟩‖ < ε) :
    F.Approximates i := by
  intro x
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h x (ε / 2) (by positivity)] with h ⟨v, hv, h1, h2⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (graphDist_nonneg H _ x)]
  refine (graphDist_le H _ x hv h1 h2).trans_lt ?_
  have : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

end HilbertComplex

end FEEC
