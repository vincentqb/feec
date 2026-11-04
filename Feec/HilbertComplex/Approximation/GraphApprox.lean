module

public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.HilbertComplex.Approximation.Convergence
public import Feec.HilbertComplex.Approximation.QuasiOptimal
public import Feec.ForMathlib.Analysis.Inequalities

/-!
# Graph-norm approximation by subcomplexes, degree by degree

Interpolation estimates are proved one degree at a time: `‖x - v‖ ≤ ε` and `‖d (x - v)‖ ≤ ε`
for `x ∈ Wⁱ` and some `v ∈ Vₕⁱ`. This module turns them into the two forms used by the
approximation theory of subcomplexes.

* **The total graph space** `Γ(𝐝)` of a finite complex (the space of the semi-discrete Hodge
  wave equation, [QuennevilleBelair2015], §4.6): degreewise approximation within `ε` gives a
  point of `graphSub` within `(m + m²) ε`, `m` the number of degrees
  (`Subcomplex.exists_mem_graphSub_le`; on a window `Wᵃ → ⋯ → W^{a+m-1}` with degreewise bounds
  `bᵢ ε`, within `(m + m²) (Σᵢ bᵢ) ε`, `Subcomplex.exists_mem_window_graphSub_le`), and
  degreewise density gives density (`Subcomplex.eventually_exists_graphSub_lt`, the hypothesis of
  `Subcomplex.isApproximating`).
* **The discrete domain spaces** `Vₕⁱ ⊆ HΛⁱ`, measured in the graph norm (the quantities of the
  quasi-optimal estimate [AFW2010], Thm 3.9): `dist(σ, Vₕⁱ) ≤ ‖σ - v‖ + ‖d σ - d v‖`
  (`Subcomplex.infDist_domainSub_le`), so `dist(σ, Vₕⁱ) ≤ 2 ε` from a degreewise approximation
  within `ε` (`Subcomplex.infDist_domainSub_le_two_mul`).
* **Families `(S_N)_{N ∈ ℕ}`** (complexes graded by `ℤ`): graph-norm approximation of every
  `x ∈ D(d)` from approximants `(y, z)` of `(x, d x)` with rates `b_N → 0`
  (`Subcomplex.eventually_exists_graph_of_near`);
  graph-norm density gives `L²` density (`Subcomplex.eventually_exists_lt_of_graph`, `D(d)` is
  dense), degreewise density in every graph norm (`Subcomplex.eventually_exists_near_of_graph`)
  and `dist(q, V_Nʲ) → 0` (`Subcomplex.tendsto_infDist_of_lt`); with degreewise density the
  semi-discrete Hodge wave equation converges on every window
  (`Subcomplex.exists_tendstoUniformlyOn_window_of`, [QuennevilleBelair2015], Thm 4.14).

## Main results

* `Feec.HilbertComplex.Subcomplex.exists_mem_graphSub_le`,
  `Feec.HilbertComplex.Subcomplex.exists_mem_window_graphSub_le`
* `Feec.HilbertComplex.Subcomplex.eventually_exists_graphSub_lt`
* `Feec.HilbertComplex.Subcomplex.infDist_domainSub_le`,
  `Feec.HilbertComplex.Subcomplex.infDist_domainSub_le_two_mul`
* `Feec.HilbertComplex.Subcomplex.eventually_exists_near_of_graph`,
  `Feec.HilbertComplex.Subcomplex.exists_tendstoUniformlyOn_window_of`

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9 (quasi-optimality in the graph norm)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 (approximating subcomplexes), Thm 4.14 (convergence of the semi-discrete Hodge wave
  equation)

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

section Window

variable {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α] {V : α → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V}

/-- **Degreewise approximation in the total space of a window, with degreewise rates**: if every
component `ζᵢ` of `ζ ∈ Γ(𝐝)` (the window `Wᵃ → ⋯ → W^{a+m-1}`) has a `vᵢ ∈ Vₕ^{a+i}` with
`‖ζᵢ - vᵢ‖ ≤ bᵢ ε` and `‖d (ζᵢ - vᵢ)‖ ≤ bᵢ ε` in every degree, then some point of the window of
`Vₕ` is within `(m + m²) (Σᵢ bᵢ) ε` of `ζ` (`exists_mem_graphSub_le` with `ε Σᵢ bᵢ`). -/
theorem exists_mem_window_graphSub_le (S : H.Subcomplex) {a : α} {m : ℕ}
    (ζ : (H.window a m).totalD.GraphSpace) (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hdeg : ∀ i : Fin m, ∃ v, ∃ hv : v ∈ S.V (a + i),
      ‖(H.window a m).totalD.graphFst ζ i - v‖ ≤ b i * ε ∧
        ∀ j (hx : (H.window a m).totalD.graphFst ζ i ∈ (H.d (a + i) j).domain),
          ‖H.d (a + i) j ⟨_ - v, Submodule.sub_mem _ hx (S.le_domain _ j hv)⟩‖ ≤ b i * ε) :
    ∃ w ∈ (S.window a m).graphSub, ‖ζ - w‖ ≤ ((m : ℝ) + m * m) * (∑ i, b i) * ε := by
  obtain ⟨x, rfl, -, -⟩ := (H.window a m).totalD.exists_toGraphSpace_eq ζ
  have hle : ∀ i, b i * ε ≤ (∑ i, b i) * ε := fun i =>
    mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)) hε
  obtain ⟨w, hw, hlt⟩ := (S.window a m).exists_mem_graphSub_le x (ε := (∑ i, b i) * ε) fun i => by
    obtain ⟨v, hv, h1, h2⟩ := hdeg i
    exact ⟨v, hv, h1.trans (hle i), fun j hx => (h2 (a + j) hx).trans (hle i)⟩
  refine ⟨w, hw, hlt.trans_eq ?_⟩
  rw [Fintype.card_fin]; ring

end Window

end Feec.HilbertComplex.Subcomplex

namespace Feec.HilbertComplex.Subcomplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- **Distance to the discrete domain space**: for `v ∈ Vₕⁱ`, the graph-norm distance of `σ` to
`Vₕⁱ` is at most `‖σ - v‖ + ‖d σ - d v‖` (the quantity bounded by interpolation estimates;
`domainSub` enters `CochainProjection.norm_sub_le_infDist`). -/
theorem infDist_domainSub_le_of_next {i : ι} (σ : H.domainSpace i) {v : W i} (hv : v ∈ S.V i) :
    Metric.infDist σ (S.domainSub i) ≤ ‖H.domainIncl i σ - v‖ +
      ‖H.d i (c.next i) (H.domainCoord i _ σ) - H.d i (c.next i) ⟨v, S.le_domain i _ hv⟩‖ := by
  obtain ⟨x, rfl, -, -⟩ := (H.d i (c.next i)).exists_toGraphSpace_eq σ
  have hmem : (H.d i (c.next i)).toGraphSpace ⟨v, S.le_domain i _ hv⟩ ∈ S.domainSub i :=
    ⟨(S.toHilbertComplex.d i (c.next i)).toGraphSpace ⟨⟨v, hv⟩, Submodule.mem_top⟩, rfl⟩
  refine (Metric.infDist_le_dist_of_mem hmem).trans ?_
  rw [dist_eq_norm, ← LinearPMap.toGraphSpace_sub]
  refine (LinearPMap.norm_toGraphSpace_le _ _).trans (le_of_eq ?_)
  rw [LinearPMap.map_sub]
  rfl

/-- **Distance to the discrete domain space** at a related pair `i → j`
(`infDist_domainSub_le_of_next`). -/
theorem infDist_domainSub_le {i j : ι} (hij : c.Rel i j) (σ : H.domainSpace i) {v : W i}
    (hv : v ∈ S.V i) :
    Metric.infDist σ (S.domainSub i) ≤ ‖H.domainIncl i σ - v‖ +
      ‖H.d i j (H.domainCoord i j σ) - H.d i j ⟨v, S.le_domain i j hv⟩‖ := by
  obtain rfl := c.next_eq' hij
  exact S.infDist_domainSub_le_of_next σ hv

/-- **Graph-norm distance from a degreewise approximation**: a `v ∈ Vₕⁱ` within `ε` of `σ`, with
`d (σ - v)` within `ε`, gives `dist_V(σ, Vₕⁱ) ≤ 2 ε`. -/
theorem infDist_domainSub_le_two_mul {i j : ι} (hij : c.Rel i j) (σ : H.domainSpace i) {v : W i}
    (hv : v ∈ S.V i) {ε : ℝ} (h1 : ‖H.domainIncl i σ - v‖ ≤ ε)
    (h2 : ∀ hx : H.domainIncl i σ ∈ (H.d i j).domain,
      ‖H.d i j ⟨H.domainIncl i σ - v, Submodule.sub_mem _ hx (S.le_domain i j hv)⟩‖ ≤ ε) :
    Metric.infDist σ (S.domainSub i) ≤ 2 * ε := by
  refine (S.infDist_domainSub_le hij σ hv).trans ?_
  rw [← LinearPMap.map_sub, two_mul]
  exact add_le_add h1 (h2 (H.domainCoord i j σ).2)

/-- **Degreewise graph-norm approximation gives graph-space approximation of the total
differential**: if every component `xᵢ` of `x ∈ D(𝐝)` is within `ε` of `Vₕⁱ` in the graph norm
of `d i (c.next i)`, then some point of `graphSub` is within `(m + m²) ε` of `(x, 𝐝 x)`,
`m = #ι` (`exists_mem_graphSub_le`). -/
theorem exists_mem_graphSub_le_of_infDist [Fintype ι] (x : H.totalD.domain) {ε : ℝ}
    (hx : ∀ i, Metric.infDist ((H.d i (c.next i)).toGraphSpace ⟨(x : PiLp 2 W) i, x.2 i _⟩)
      (S.domainSub i) < ε) :
    ∃ w ∈ S.graphSub, ‖H.totalD.toGraphSpace x - w‖ ≤
      ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) * ε := by
  refine S.exists_mem_graphSub_le x fun i => ?_
  set σ := (H.d i (c.next i)).toGraphSpace ⟨(x : PiLp 2 W) i, x.2 i _⟩
  obtain ⟨w, ⟨a, rfl⟩, hlt⟩ := (Metric.infDist_lt_iff ⟨0, (S.domainSub i).zero_mem⟩).1 (hx i)
  rw [dist_eq_norm] at hlt
  have e : H.domainIncl i (σ - S.embD i a) = (x : PiLp 2 W) i - S.toW i a := by
    rw [_root_.map_sub]; rfl
  refine ⟨S.toW i a, (S.toHilbertComplex.domainIncl i a).2, ?_, fun j hxj => ?_⟩
  · rw [← e]; exact ((H.norm_domainIncl_le i _).trans hlt.le)
  · have e' : H.d i j ⟨(x : PiLp 2 W) i - S.toW i a,
        Submodule.sub_mem _ hxj (S.le_domain i j (S.toHilbertComplex.domainIncl i a).2)⟩ =
        H.d i j (H.domainCoord i j (σ - S.embD i a)) :=
      congrArg (H.d i j) (Subtype.ext e.symm)
    rw [e']
    exact (H.norm_d_domainCoord_le i j _).trans hlt.le

end Feec.HilbertComplex.Subcomplex

/-! ### Degreewise approximation in a single degree -/

namespace Feec.HilbertComplex.Subcomplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} (S : H.Subcomplex)

/-- **Degreewise approximation in a trivial degree**: if `Wⁱ = 0`, then `v = 0 ∈ Vₕⁱ` is within
every `ε ≥ 0` of `x`, in every graph norm. -/
theorem exists_mem_le_of_subsingleton {i : ι} [Subsingleton (W i)] {x : W i} {ε : ℝ}
    (hε : 0 ≤ ε) :
    ∃ v, ∃ hv : v ∈ S.V i, ‖x - v‖ ≤ ε ∧ ∀ j (hx : x ∈ (H.d i j).domain),
      ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx (S.le_domain i j hv)⟩‖ ≤ ε := by
  refine ⟨0, Submodule.zero_mem _, ?_, fun j hx => ?_⟩
  · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
  · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε

/-- **Degreewise approximation on the cochain shape over `ℤ`**: the only differential out of
degree `j` is `d j (j + 1)` (`d j j' = 0` for `j' ≠ j + 1`), so a `v ∈ Vₕʲ` with `‖x - v‖ ≤ ε`
and `‖d x - d v‖ ≤ ε` approximates `x` within `ε` in every graph norm. -/
theorem exists_mem_le_of_succ {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    {H : HilbertComplex 𝕜 (ComplexShape.up ℤ) W} (S : H.Subcomplex) {j : ℤ} {x v : W j}
    (hv : v ∈ S.V j) {ε : ℝ} (hε : 0 ≤ ε) (h1 : ‖x - v‖ ≤ ε)
    (h2 : ∀ hx : x ∈ (H.d j (j + 1)).domain,
      ‖H.d j (j + 1) ⟨x, hx⟩ - H.d j (j + 1) ⟨v, S.le_domain j (j + 1) hv⟩‖ ≤ ε) :
    ∃ v, ∃ hv : v ∈ S.V j, ‖x - v‖ ≤ ε ∧ ∀ j' (hx : x ∈ (H.d j j').domain),
      ‖H.d j j' ⟨x - v, Submodule.sub_mem _ hx (S.le_domain j j' hv)⟩‖ ≤ ε := by
  refine ⟨v, hv, h1, fun j' hx => ?_⟩
  by_cases hj : j + 1 = j'
  · subst hj
    have e : H.d j (j + 1) ⟨x - v, Submodule.sub_mem _ hx (S.le_domain j (j + 1) hv)⟩ =
        H.d j (j + 1) ⟨x, hx⟩ - H.d j (j + 1) ⟨v, S.le_domain j (j + 1) hv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e]; exact h2 hx
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε

end Feec.HilbertComplex.Subcomplex

/-! ### Families of subcomplexes indexed by `ℕ`: from graph-norm to `L²` and degreewise density -/

namespace Feec.HilbertComplex.Subcomplex

open Filter Topology

section Family

variable {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, CompleteSpace (W i)] {H : HilbertComplex ℝ (ComplexShape.up ℤ) W}
  (S : ℕ → H.Subcomplex)

/-- **Graph-norm approximation from approximants with rates**: if every
`x ∈ D(d)` is within `ε` of some `y`, with `d x` within `ε` of some `z`, and `(y, z)` is
approximated by `(v, d v)`, `v ∈ Vₕ`, up to `b_N → 0`, then `x` is eventually within `ε` of `Vₕ`
in the graph norm. -/
theorem eventually_exists_graph_of_near {k : ℤ} {x : W k} (hx : x ∈ (H.d k (k + 1)).domain)
    (happ : ∀ ε > 0, ∃ (y : W k) (z : W (k + 1)) (b : ℕ → ℝ), ‖x - y‖ < ε ∧
      ‖H.d k (k + 1) ⟨x, hx⟩ - z‖ < ε ∧ Tendsto b atTop (𝓝 0) ∧
      ∀ N, ∃ v, ∃ hv : v ∈ (S N).V k, ‖y - v‖ ≤ b N ∧
        ‖z - H.d k (k + 1) ⟨v, (S N).le_domain k (k + 1) hv⟩‖ ≤ b N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (S N).V k, ‖x - v‖ < ε ∧
      ‖H.d k (k + 1) ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  obtain ⟨y, z, b, h1, h2, hb, hv⟩ := happ (ε / 2) (half_pos hε)
  filter_upwards [hb.eventually (gt_mem_nhds (half_pos hε))] with N hN
  obtain ⟨v, hv, hv1, hv2⟩ := hv N
  refine ⟨v, hv, ?_, ?_⟩
  · calc ‖x - v‖ ≤ ‖x - y‖ + ‖y - v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 (hv1.trans hN.le)
      _ = ε := add_halves ε
  · rw [show (⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain k (k + 1) hv)⟩ :
        (H.d k (k + 1)).domain) = ⟨x, hx⟩ - ⟨v, (S N).le_domain k (k + 1) hv⟩ from rfl,
      LinearPMap.map_sub]
    calc _ ≤ ‖H.d k (k + 1) ⟨x, hx⟩ - z‖ +
          ‖z - H.d k (k + 1) ⟨v, (S N).le_domain k (k + 1) hv⟩‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h2 (hv2.trans hN.le)
      _ = ε := add_halves ε

variable {S}

/-- **`L²` density from graph-norm approximation** (`D(d)` is dense). -/
theorem eventually_exists_lt_of_graph
    (hgraph : ∀ (k : ℤ) (x : W k) (hx : x ∈ (H.d k (k + 1)).domain) (ε : ℝ), 0 < ε →
      ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (S N).V k, ‖x - v‖ < ε ∧
        ‖H.d k (k + 1) ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain k (k + 1) hv)⟩‖ < ε)
    (k : ℤ) (x : W k) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (S N).V k, ‖x - v‖ < ε := by
  obtain ⟨y, hy, hxy⟩ := (H.dense k (k + 1)).exists_dist_lt x (half_pos hε)
  filter_upwards [hgraph k y hy _ (half_pos hε)] with N hN
  obtain ⟨v, hv, h1, -⟩ := hN
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm] at hxy
  calc ‖x - v‖ ≤ ‖x - y‖ + ‖y - v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy h1
    _ = ε := add_halves ε

/-- **Degreewise approximation in every graph norm from graph-norm approximation in the next
degree** (the hypothesis of `Feec.HilbertComplex.Subcomplex.eventually_exists_graphSub_lt`). -/
theorem eventually_exists_near_of_graph
    (hgraph : ∀ (k : ℤ) (x : W k) (hx : x ∈ (H.d k (k + 1)).domain) (ε : ℝ), 0 < ε →
      ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (S N).V k, ‖x - v‖ < ε ∧
        ‖H.d k (k + 1) ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain k (k + 1) hv)⟩‖ < ε)
    (i : ℤ) (x : W i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (S N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (H.d i j).domain),
        ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain i j hv)⟩‖ < ε := by
  by_cases hx : x ∈ (H.d i (i + 1)).domain
  · filter_upwards [hgraph i x hx ε hε] with N hN
    obtain ⟨v, hv, h1, h2⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact h2
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε
  · filter_upwards [eventually_exists_lt_of_graph hgraph i x hε] with N hN
    obtain ⟨v, hv, h1⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact absurd hxj hx
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε

/-- `dist(q, Vₕʲ) → 0` from `L²` density. -/
theorem tendsto_infDist_of_lt {j : ℤ} (q : W j)
    (hlt : ∀ ε > 0, ∀ᶠ N in atTop, ∃ v ∈ (S N).V j, ‖q - v‖ < ε) :
    Tendsto (fun N => Metric.infDist q ((S N).V j : Set (W j))) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N =>
    ha.trans_le Metric.infDist_nonneg, fun a ha => ?_⟩
  filter_upwards [hlt a ha] with N hN
  obtain ⟨v, hv, h⟩ := hN
  exact (Metric.infDist_le_dist_of_mem hv).trans_lt (by rwa [dist_eq_norm])

end Family

/-! ### The semi-discrete Hodge wave equation for families approximating the graph spaces -/

section Wave

variable {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, CompleteSpace (W i)] {H : HilbertComplex ℝ (ComplexShape.up ℤ) W}

variable {S : ℕ → H.Subcomplex} [∀ N k, FiniteDimensional ℝ ((S N).V k)]

/-- **Convergence of the semi-discrete Hodge wave equation** on every window, for a family of
subcomplexes approximating every point degreewise in the graph norm. -/
theorem exists_tendstoUniformlyOn_window_of (hdeg : ∀ i (x : W i) (ε : ℝ), 0 < ε →
      ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (S N).V i, ‖x - v‖ < ε ∧
        ∀ j (hx : x ∈ (H.d i j).domain),
          ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain i j hv)⟩‖ < ε)
    (a : ℤ) (m : ℕ) (t₀ t₁ : ℝ) (x : (H.window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → (H.window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((S N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((S N).window a m).graphSub)
        ((H.window a m).totalD.toGraphSpace ⟨x, ((H.window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => (H.window a m).totalD.graphFst (ξh N t))
        (fun t => (H.window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) := by
  have : ∀ N (i : Fin m), FiniteDimensional ℝ (((S N).window a m).V i) := fun N i =>
    inferInstanceAs (FiniteDimensional ℝ ((S N).V (a + i)))
  refine HilbertComplex.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection _
    (Subcomplex.isApproximating fun ζ _ hδ => ?_) t₀ t₁ x
  exact Subcomplex.eventually_exists_graphSub_lt (fun N => (S N).window a m)
    (fun i x _ hε => (hdeg (a + i) x _ hε).mono fun _ hN => by
      obtain ⟨v, hv, h1, h2⟩ := hN
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩) ζ hδ

end Wave

end Feec.HilbertComplex.Subcomplex
