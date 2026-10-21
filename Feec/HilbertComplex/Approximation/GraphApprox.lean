module

public import Feec.HilbertComplex.Approximation.Convergence
public import Feec.HilbertComplex.Approximation.QuasiOptimal

/-!
# Graph-norm approximation by subcomplexes, degree by degree

Interpolation estimates are proved one degree at a time: `‖x - v‖ ≤ ε` and `‖d (x - v)‖ ≤ ε`
for `x ∈ Wⁱ` and some `v ∈ Vₕⁱ`. This module turns them into the two forms used by the
approximation theory of subcomplexes.

* **The total graph space** `Γ(𝐝)` of a finite complex (the space of the semi-discrete Hodge
  wave equation, [QuennevilleBelair2015], §4.6): degreewise approximation within `ε` gives a
  point of `graphSub` within `(m + m²) ε`, `m` the number of degrees
  (`Subcomplex.exists_mem_graphSub_le`), and degreewise density gives density
  (`Subcomplex.eventually_exists_graphSub_lt`, the hypothesis of `Subcomplex.isApproximating`).
* **The discrete domain spaces** `Vₕⁱ ⊆ HΛⁱ`, measured in the graph norm (the quantities of the
  quasi-optimal estimate [AFW2010], Thm 3.9): `dist(σ, Vₕⁱ) ≤ ‖σ - v‖ + ‖d σ - d v‖`
  (`Subcomplex.infDist_domainSub_le`).

## Main results

* `Feec.HilbertComplex.Subcomplex.exists_mem_graphSub_le`
* `Feec.HilbertComplex.Subcomplex.eventually_exists_graphSub_lt`
* `Feec.HilbertComplex.Subcomplex.infDist_domainSub_le`

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9 (quasi-optimality in the graph norm)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 (approximating subcomplexes)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open Filter

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem toGraphSpace_sub (T : E →ₗ.[𝕜] F) (x y : T.domain) :
    T.toGraphSpace (x - y) = T.toGraphSpace x - T.toGraphSpace y := by
  refine Subtype.ext ?_
  change WithLp.toLp 2 (((x - y : T.domain) : E), T (x - y)) =
    WithLp.toLp 2 ((x : E), T x) - WithLp.toLp 2 ((y : E), T y)
  rw [LinearPMap.map_sub, ← WithLp.toLp_sub]
  rfl

/-- The graph norm is at most `‖x‖ + ‖T x‖`. -/
theorem norm_toGraphSpace_le (T : E →ₗ.[𝕜] F) (x : T.domain) :
    ‖T.toGraphSpace x‖ ≤ ‖(x : E)‖ + ‖T x‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((x : E), T x))
  have e : ‖T.toGraphSpace x‖ = ‖WithLp.toLp 2 ((x : E), T x)‖ := rfl
  rw [e]
  refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  rw [h]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  nlinarith [norm_nonneg (x : E), norm_nonneg (T x)]

end LinearPMap

namespace PiLp

/-- `‖x‖ ≤ Σᵢ ‖xᵢ‖` in `PiLp 2`. -/
theorem norm_le_sum_norm {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp 2 β) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  refine (abs_le_of_sq_le_sq' ?_ (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _

end PiLp

namespace Feec.HilbertComplex.Subcomplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

/-- **Degreewise approximation in the graph space of the total differential, with a rate**: if
every component `xᵢ` of `x ∈ D(𝐝)` has a `vᵢ ∈ Vₕⁱ` with `‖xᵢ - vᵢ‖ ≤ ε` and
`‖d (xᵢ - vᵢ)‖ ≤ ε` in every degree, then some point of `graphSub` is within `(m + m²) ε` of
`(x, 𝐝 x)`, with `m = #ι`. -/
theorem exists_mem_graphSub_le (S : H.Subcomplex) (x : H.totalD.domain) {ε : ℝ}
    (hdeg : ∀ i, ∃ v, ∃ hv : v ∈ S.V i, ‖(x : PiLp 2 W) i - v‖ ≤ ε ∧
      ∀ j (hx : (x : PiLp 2 W) i ∈ (H.d i j).domain),
        ‖H.d i j ⟨(x : PiLp 2 W) i - v, Submodule.sub_mem _ hx (S.le_domain i j hv)⟩‖ ≤ ε) :
    ∃ w ∈ S.graphSub, ‖H.totalD.toGraphSpace x - w‖ ≤
      ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) * ε := by
  classical
  set m : ℝ := (Fintype.card ι : ℝ)
  choose v hv hv1 hv2 using hdeg
  set y : PiLp 2 W := WithLp.toLp 2 fun i => v i
  have hy : y ∈ H.totalD.domain := fun i j => S.le_domain i j (hv i)
  refine ⟨H.totalD.toGraphSpace ⟨y, hy⟩, fun i => hv i, ?_⟩
  rw [← LinearPMap.toGraphSpace_sub]
  refine (LinearPMap.norm_toGraphSpace_le _ _).trans ?_
  have h1 : ‖((x - ⟨y, hy⟩ : H.totalD.domain) : PiLp 2 W)‖ ≤ m * ε := by
    refine (PiLp.norm_le_sum_norm _).trans ?_
    calc ∑ i, ‖((x - ⟨y, hy⟩ : H.totalD.domain) : PiLp 2 W) i‖ ≤ ∑ _i : ι, ε :=
          Finset.sum_le_sum fun i _ => hv1 i
      _ = m * ε := by simp [m]
  have h2 : ‖H.totalD (x - ⟨y, hy⟩)‖ ≤ m * (m * ε) := by
    refine (PiLp.norm_le_sum_norm _).trans ?_
    calc ∑ j, ‖H.totalD (x - ⟨y, hy⟩) j‖ ≤ ∑ _j : ι, m * ε := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [totalD_apply]
          refine (norm_sum_le _ _).trans ?_
          calc ∑ i, ‖H.d i j ⟨((x - ⟨y, hy⟩ : H.totalD.domain) : PiLp 2 W) i,
                (x - ⟨y, hy⟩ : H.totalD.domain).2 i j⟩‖ ≤ ∑ _i : ι, ε :=
                Finset.sum_le_sum fun i _ => hv2 i j (x.2 i j)
            _ = m * ε := by simp [m]
      _ = m * (m * ε) := by simp [m]
  linarith

/-- **Degreewise graph-norm approximation gives approximation in the graph space of the total
differential**: if every `x ∈ Wⁱ` is eventually within `ε` of `Vₕⁱ`, with `‖d (x - v)‖ < ε`
whenever `x ∈ D(d)`, then the total spaces `graphSub` of the subcomplexes approximate every point
of `Γ(𝐝)`. This is the hypothesis of `Feec.HilbertComplex.Subcomplex.isApproximating`. -/
theorem eventually_exists_graphSub_lt {κ : Type*} {l : Filter κ} (S : κ → H.Subcomplex)
    (hdeg : ∀ i (x : W i) (ε : ℝ), 0 < ε → ∀ᶠ h in l, ∃ v, ∃ hv : v ∈ (S h).V i,
      ‖x - v‖ < ε ∧ ∀ j (hx : x ∈ (H.d i j).domain),
        ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((S h).le_domain i j hv)⟩‖ < ε)
    (ζ : H.totalD.GraphSpace) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h in l, ∃ w ∈ (S h).graphSub, ‖ζ - w‖ < δ := by
  obtain ⟨x, rfl, -, -⟩ := H.totalD.exists_toGraphSpace_eq ζ
  set m : ℝ := (Fintype.card ι : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  set ε := δ / (m + m * m + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hev := Filter.eventually_all.2 fun i => hdeg i ((x : PiLp 2 W) i) ε hε
  filter_upwards [hev] with h hh
  obtain ⟨w, hw, hle⟩ := exists_mem_graphSub_le (S h) x (ε := ε) fun i => by
    obtain ⟨v, hv, h1, h2⟩ := hh i
    exact ⟨v, hv, h1.le, fun j hx => (h2 j hx).le⟩
  refine ⟨w, hw, hle.trans_lt ?_⟩
  have e : (m + m * m) * ε = (m + m * m) / (m + m * m + 1) * δ := by
    simp only [ε]; field_simp
  rw [e]
  have : (m + m * m) / (m + m * m + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  nlinarith

end Feec.HilbertComplex.Subcomplex

namespace Feec.HilbertComplex.Subcomplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- **Distance to the discrete domain space**: for `v ∈ Vₕⁱ`, the graph-norm distance of `σ` to
`Vₕⁱ` is at most `‖σ - v‖ + ‖d σ - d v‖` (the quantity bounded by interpolation estimates;
`domainSub` enters `CochainProjection.norm_sub_le_infDist`). -/
theorem infDist_domainSub_le {i j : ι} (hij : c.Rel i j) (σ : H.domainSpace i) {v : W i}
    (hv : v ∈ S.V i) :
    Metric.infDist σ (S.domainSub i) ≤ ‖H.domainIncl i σ - v‖ +
      ‖H.d i j (H.domainCoord i j σ) - H.d i j ⟨v, S.le_domain i j hv⟩‖ := by
  obtain rfl := c.next_eq' hij
  obtain ⟨x, rfl, -, -⟩ := (H.d i (c.next i)).exists_toGraphSpace_eq σ
  have hmem : (H.d i (c.next i)).toGraphSpace ⟨v, S.le_domain i _ hv⟩ ∈ S.domainSub i :=
    ⟨(S.toHilbertComplex.d i (c.next i)).toGraphSpace ⟨⟨v, hv⟩, Submodule.mem_top⟩, rfl⟩
  refine (Metric.infDist_le_dist_of_mem hmem).trans ?_
  rw [dist_eq_norm, ← LinearPMap.toGraphSpace_sub]
  refine (LinearPMap.norm_toGraphSpace_le _ _).trans (le_of_eq ?_)
  rw [LinearPMap.map_sub]
  rfl

end Feec.HilbertComplex.Subcomplex
