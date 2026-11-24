module

public import Solution.Defs
public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.HilbertComplex.Compactness
public import Feec.ForMathlib.Analysis.QuasiOptimal

/-!
# From `Feec`'s Hilbert complexes to the challenge's

A `Feec.HilbertComplex` on `ComplexShape.up ℤ` is a Hilbert complex of the challenge with the same
fields (`HilbertComplex.ofFeec`), and so are its subcomplexes (`Subcomplex.ofFeec`); a `Feec`
cochain projection, defined on `W`, restricts to the domain complex (`CochainProjection.ofFeec`).
The harmonic forms of `Feec` are the challenge's `N(dᵏ) ∩ N((dᵏ⁻¹)†)` (`harmonic_eq_ofFeec`), and
its compactness property makes the graph-norm unit ball of `D(dᵏ) ∩ D((dᵏ⁻¹)†)` relatively
compact (`isCompact_closure_ofFeec`; with the closed range and the harmonic forms, `hodge_ofFeec`).
Eventual approximation in `W` and for `d` gives the graph-norm approximation of the challenge
(`approximates_of_eventually`), and graph-norm approximation gives approximation in `W`
(`tendsto_infDist`). Cochain projections extending to uniformly bounded
projections of `W` attain the rate of every Jackson estimate (`Jackson.projRate`), by the
quasi-optimality of a bounded projection
(`ContinuousLinearMap.norm_sub_apply_le_of_apply_eq`) and the commutation `d π = π d`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5, §4, §5

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

/-! ### Harmonic forms and the compactness property -/

/-- The harmonic forms `ℌᵏ` of `Feec` are `N(dᵏ) ∩ N((dᵏ⁻¹)†)`, the expression of the challenge. -/
theorem harmonic_eq_ofFeec (k : ℤ) :
    G.harmonic k = ((ofFeec G).d k (k + 1)).ker ⊓ ((ofFeec G).d (k - 1) k)†.ker := by
  change G.cycles k ⊓ ((G.d _ k)†).ker = _
  rw [G.cycles_eq (rfl : (ComplexShape.up ℤ).Rel k (k + 1)),
    (ComplexShape.up ℤ).prev_eq' (sub_add_cancel k 1)]
  rfl

/-- **The compactness property in the form of the challenge**: the unit ball of
`D(dᵏ) ∩ D((dᵏ⁻¹)†)` in its graph norm `(‖x‖² + ‖dx‖² + ‖d†x‖²)^½` lies in the box
`‖x‖, ‖dx‖, ‖d†x‖ ≤ 1` of `Feec.HilbertComplex.HasCompactPropertyAt`, hence in a compact set, so its
closure is compact. -/
theorem isCompact_closure_ofFeec {k : ℤ} (hG : G.HasCompactPropertyAt k) :
    IsCompact (closure {x : W k | ∃ (hx : x ∈ ((ofFeec G).d k (k + 1)).domain)
      (hx' : x ∈ ((ofFeec G).d (k - 1) k)†.domain),
        ‖x‖ ^ 2 + ‖(ofFeec G).d k (k + 1) ⟨x, hx⟩‖ ^ 2 +
          ‖((ofFeec G).d (k - 1) k)† ⟨x, hx'⟩‖ ^ 2 ≤ 1}) := by
  obtain ⟨K, hK, hsub⟩ := (Feec.HilbertComplex.hasCompactPropertyAt_iff_of_rel (H := G)
    (sub_add_cancel k 1) (rfl : (ComplexShape.up ℤ).Rel k (k + 1))).1 hG
  refine hK.closure_of_subset fun x ⟨hx, hx', h⟩ => ?_
  change ‖x‖ ^ 2 + ‖G.d k (k + 1) ⟨x, hx⟩‖ ^ 2 + ‖(G.d (k - 1) k)† ⟨x, hx'⟩‖ ^ 2 ≤ 1 at h
  have h1 := norm_nonneg x
  have h2 := norm_nonneg (G.d k (k + 1) ⟨x, hx⟩)
  have h3 := norm_nonneg ((G.d (k - 1) k)† ⟨x, hx'⟩)
  exact hsub x hx hx' (by nlinarith) (by nlinarith) (by nlinarith)

/-- **The Hodge data of a `Feec` complex with the compactness property**, in the form of the
challenge: in degree `k`, closed range, finite-dimensional harmonic forms (of dimension
`[k = m]` if those of `G` are) and the relatively compact graph-norm unit ball. -/
theorem hodge_ofFeec (hG : G.HasCompactProperty) {m : ℤ}
    (hm : ∀ k, Module.finrank 𝕜 (G.harmonic k) = if k = m then 1 else 0) (k : ℤ) :
    IsClosed (LinearMap.range ((ofFeec G).d k (k + 1)).toFun : Set (W (k + 1))) ∧
      FiniteDimensional 𝕜 ↥(((ofFeec G).d k (k + 1)).ker ⊓ ((ofFeec G).d (k - 1) k)†.ker) ∧
      Module.finrank 𝕜 ↥(((ofFeec G).d k (k + 1)).ker ⊓ ((ofFeec G).d (k - 1) k)†.ker) =
        (if k = m then 1 else 0) ∧
      IsCompact (closure {x : W k | ∃ (hx : x ∈ ((ofFeec G).d k (k + 1)).domain)
        (hx' : x ∈ ((ofFeec G).d (k - 1) k)†.domain),
          ‖x‖ ^ 2 + ‖(ofFeec G).d k (k + 1) ⟨x, hx⟩‖ ^ 2 +
            ‖((ofFeec G).d (k - 1) k)† ⟨x, hx'⟩‖ ^ 2 ≤ 1}) := by
  rw [← harmonic_eq_ofFeec]
  refine ⟨?_, (hG k).finiteDimensional_harmonic, hm k, isCompact_closure_ofFeec (hG k)⟩
  have h := (hG k).isClosed_range
  rwa [(ComplexShape.up ℤ).next_eq' (rfl : (ComplexShape.up ℤ).Rel k (k + 1))] at h

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

/-- **Approximation in `W` from approximation in the graph norm**: `D(d)` is dense, and the
distance in `W` is at most the graph-norm distance. -/
theorem tendsto_infDist {κ : Type*} (F : H.SubcomplexFamily κ) {i : ℤ} (hA : F.Approximates i)
    (x : W i) : Tendsto (fun h => Metric.infDist x ((F.V h).V i)) F.l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hyD, hy⟩ := (H.dense i (i + 1)).exists_dist_lt x (half_pos hε)
  filter_upwards [(tendsto_order.1 (hA ⟨y, hyD⟩)).2 (ε / 2) (half_pos hε)] with h hh
  obtain ⟨v, hv⟩ := exists_lt_of_ciInf_lt hh
  have hyv : dist y v ≤ H.graphNorm i (i + 1) (⟨y, hyD⟩ - ⟨v, (F.V h).le_domain i (i + 1) v.2⟩) :=
    (dist_eq_norm y v).trans_le (Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _)))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  calc Metric.infDist x ((F.V h).V i) ≤ dist x v := Metric.infDist_le_dist_of_mem v.2
    _ ≤ dist x y + dist y v := dist_triangle _ _ _
    _ < ε := by linarith

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
