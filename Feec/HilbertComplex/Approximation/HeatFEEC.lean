module

public import Feec.HilbertComplex.Total
public import Feec.HilbertComplex.Approximation.ApproxConforming
public import Feec.HilbertComplex.Approximation.StaticFEEC
public import Feec.HilbertComplex.Approximation.Ritz

/-!
# The heat FEEC theorem

The Hodge heat equation `u' = -Δ u` of a Hilbert complex `H` on a finite index type (any shape: a
window `H.window a m` of a complex on `ℤ` or `ℕ`, a short complex, …), discretized on a constrained
FEEC discretization `F` (a conforming family with a closed constraint `K`) by the discrete Hodge
Laplacian of the total spaces `Xₕ = ∏ Vₕⁱ`, is a dissipative FEEC discretization
(`ConstrainedFEEC.toHeat : DissipFEEC (-Δ) κ`), and the dissipative FEEC theorem holds for it with
the **heat Ritz projection**: the static FEEC theorem drives the dynamic one.

* **The total complex** (`Feec.HilbertComplex.Total`): `Δ` is the mixed Hodge Laplacian of the
  total complex `H.total` (`W = ⊕ Wⁱ` with `𝐝`), so its Green operator `G` is a solution operator
  and the static theory of [AFW2010], §3.4 applies to `Δ` in all degrees at once, the boundary
  degrees of a window included. The total spaces with the total cochain projections are a
  conforming family of `H.total` (`ConstrainedFEEC.totalFamily`).
* **The discrete side**: the discrete Hodge Laplacian `Δₕ = dₕ dₕ* + dₕ* dₕ`
  (`Subcomplex.laplacian`, bounded), the discrete Green operator `Gₕ` (the solution operator of
  the discrete total complex, `Δₕ Gₕ = 1 - P_ℌₕ`, `Subcomplex.laplacian_solutionOp`) and the
  discrete harmonic projection `P_ℌₕ`. The discrete Green operator *is* the mixed method
  (`discreteGreen_orthProj`: `Gₕ Qₕ f = uₕ`; `discreteHarmonicProj_orthProj`: `P_ℌₕ Qₕ f = pₕ`),
  so the static error `e(f) = ‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖` (`staticError`) bounds
  `‖G f - Gₕ Qₕ f‖` and `‖P_ℌ f - P_ℌₕ Qₕ f‖`.
* **The heat Ritz projection** (`heatRitz`), for the graph lift `ℓ y = (y, A y)` of `D(A²)`,
  `A = -Δ`, read by `ρ (y, z) = P_ℌ y - G z` (the Hodge decomposition `y = P_ℌ y + G Δ y`,
  `heatRead_lift`): `Rₕ ℓ y = Gₕ Qₕ (Δ y) + P_ℌₕ Qₕ y` (`ritzR_lift`). Its Galerkin property is
  `-Δₕ Rₕ ℓ y = (1 - P_ℌₕ) Qₕ (A y)` (`heatGen_ritzR`), so the consistency defect is
  `Rₕ ℓ(A y) - (1 - P_ℌₕ) Qₕ (A y)` (`heatRitz_defect_eq`; for `y ∈ D(Δ²)`,
  `(Qₕ - Rₕ ℓ)(Δ y) - P_ℌₕ Qₕ Δ y`), which on `ℓ (A y)` is the operator
  `Δₕ (y, z) = 2 P_ℌₕ Qₕ (1 - P_ℌ) y + Qₕ G z - Gₕ Qₕ z` (`ritzDefect_lift`, using
  `P_ℌ A y = 0` and `G A² y = -A y`), bounded by `2 e((1 - P_ℌ) y) + e(z)` (`norm_ritzDefect_le`).
* **Convergence**: the static errors tend to `0` (the static FEEC theorem, [AFW2010], Thm 3.9),
  so the heat Ritz projection gives a core (`heatCore`, data `D(Δ²)`, dense) and the full
  `DissipFEEC.Verdict` (`heatFEEC`).
* **Rates**: with a Jackson estimate, the static rate `e(f) ≤ K L hᵒʳᵈ` ([AFW2010], Thm 3.9,
  `ConformingFamily.StaticVerdict.rate`) along the orbit gives
  `‖S(t) x - ιₕ e^{-tΔₕ} Rₕ ℓ x‖ ≤ (2 + 3t) K L hᵒʳᵈ` (`rate_heat_of_static`, `rate_heat`): the
  static constant enters the dynamic bound.

## Main results

* `ConstrainedFEEC.toHeat`, `ConstrainedFEEC.heatRitz`, `ConstrainedFEEC.heatCore`;
* **`ConstrainedFEEC.heatFEEC`**, **`ConstrainedFEEC.rate_heat`**;
  `ConstrainedFEEC.totalJackson` (the Jackson estimate of the total family from one of the
  family), `ConstrainedFEEC.jacksonHeatRateClass`;
* `ConstrainedFEEC.ritzR_lift`, `ConstrainedFEEC.heatRitz_defect_eq`,
  `ConstrainedFEEC.heatGen_ritzR`, `ConstrainedFEEC.ritzDefect_lift`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.2 (the Hodge Laplacian), §3.4 (Thm 3.8, 3.9)
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]
  (the elliptic projection as comparison function)
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
  (the Hodge heat equation in FEEC)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### The discrete Hodge Laplacian -/

namespace Subcomplex

variable {H : HilbertComplex 𝕜 c W} (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- **The discrete Hodge Laplacian** `Δₕ = dₕ dₕ* + dₕ* dₕ` on `Vₕʲ` at `i → j → k`, a bounded
operator (`Vₕ` is finite-dimensional; `dₕ*` is the Hilbert adjoint of `dₕ` in the `W` inner
products). -/
def laplacian (i j k : ι) : S.V j →L[𝕜] S.V j :=
  S.dh i j ∘L (S.dh i j).adjoint + (S.dh j k).adjoint ∘L S.dh j k

theorem laplacian_apply (i j k : ι) (v : S.V j) :
    S.laplacian i j k v = S.dh i j ((S.dh i j).adjoint v) + (S.dh j k).adjoint (S.dh j k v) :=
  rfl

/-- `Δₕ ≥ 0`: `re ⟪Δₕ v, v⟫ = ‖dₕ* v‖² + ‖dₕ v‖²`. -/
theorem re_inner_laplacian_self (i j k : ι) (v : S.V j) :
    RCLike.re ⟪S.laplacian i j k v, v⟫ = ‖(S.dh i j).adjoint v‖ ^ 2 + ‖S.dh j k v‖ ^ 2 := by
  rw [laplacian_apply, inner_add_left,
    ← ContinuousLinearMap.adjoint_inner_right (S.dh i j) ((S.dh i j).adjoint v) v,
    ContinuousLinearMap.adjoint_inner_left (S.dh j k) v (S.dh j k v), _root_.map_add,
    inner_self_eq_norm_sq,
    inner_self_eq_norm_sq]

/-- The adjoint of a discrete differential is the Hilbert adjoint of `dₕ`. -/
theorem adjoint_d_toHilbertComplex_apply (i j : ι) (y : ((S.toHilbertComplex.d i j)†).domain) :
    (S.toHilbertComplex.d i j)† y = (S.dh i j).adjoint y :=
  LinearPMap.apply_eq_of_eq (ContinuousLinearMap.adjoint_toPMap_top (S.dh i j)) y
    ⟨y, Submodule.mem_top⟩ rfl

/-- **The discrete solution operator inverts `Δₕ`**: `Δₕ Gₕ f = f - P_ℌₕ f`. -/
theorem laplacian_solutionOp {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) (f : S.V j) :
    S.laplacian i j k
        (S.toHilbertComplex.solutionOp hij hjk (S.closedRangeAt j) (S.closedRangeAt k) f) =
      f - (S.toHilbertComplex.harmonic j).starProjection f := by
  obtain ⟨h₁, h₂, h₃, h₄, e⟩ :=
    S.toHilbertComplex.hodgeLaplacian_solutionOp hij hjk (S.closedRangeAt j) (S.closedRangeAt k) f
  have e' : S.dh i j ((S.toHilbertComplex.d i j)† ⟨_, h₂⟩) +
      (S.toHilbertComplex.d j k)† ⟨_, h₃⟩ = f - (S.toHilbertComplex.harmonic j).starProjection f :=
    e
  rwa [S.adjoint_d_toHilbertComplex_apply, S.adjoint_d_toHilbertComplex_apply] at e'

/-- **`Δₕ` vanishes on the discrete harmonic forms.** -/
theorem laplacian_of_mem_harmonic {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {q : S.V j}
    (hq : q ∈ S.toHilbertComplex.harmonic j) : S.laplacian i j k q = 0 := by
  obtain rfl := c.next_eq' hjk
  obtain rfl := c.prev_eq' hij
  obtain ⟨⟨y, rfl, hy⟩, hq'⟩ := (Submodule.mem_inf.1 hq).imp mem_ker_iff.1 mem_ker_iff.1
  obtain ⟨z, hz, hz0⟩ := hq'
  have h1 : S.dh j (c.next j) y = 0 := hy
  have h2 : (S.dh (c.prev j) j).adjoint y = 0 := by
    rw [hz, ← S.adjoint_d_toHilbertComplex_apply, hz0]
  rw [laplacian_apply, h1, h2, _root_.map_zero, _root_.map_zero, add_zero]

end Subcomplex

/-! ### The Hodge decomposition as a reading of the graph lift -/

section Read

variable [Fintype ι] (H : HilbertComplex 𝕜 c W)

/-- The reading `ρ (y, z) = P_ℌ y - G z` of the graph lift of the heat generator `A = -Δ`:
`ρ (y, A y) = P_ℌ y + G Δ y = y` on `D(Δ)` (the Hodge decomposition, `heatRead_lift`). -/
def heatRead (hcr : ∀ i, H.ClosedRangeAt i) : PiLp 2 W × PiLp 2 W →L[𝕜] PiLp 2 W :=
  (H.total.harmonic ()).starProjection ∘L ContinuousLinearMap.fst 𝕜 _ _ -
    H.greenOp hcr ∘L ContinuousLinearMap.snd 𝕜 _ _

theorem heatRead_apply (hcr : ∀ i, H.ClosedRangeAt i) (g : PiLp 2 W × PiLp 2 W) :
    H.heatRead hcr g = (H.total.harmonic ()).starProjection g.1 - H.greenOp hcr g.2 :=
  rfl

/-- `A y = -Δ y` for `y ∈ D(Δ)`, in terms of the extension `genExt`. -/
theorem genExt_neg_hodgeLaplacian {y : PiLp 2 W} (hy : y ∈ H.hodgeLaplacian.domain) :
    DissipFEEC.genExt (-H.hodgeLaplacian) y = -H.hodgeLaplacian ⟨y, hy⟩ :=
  (DissipFEEC.genExt_of_mem (A := -H.hodgeLaplacian) hy).trans (LinearPMap.neg_apply _ _)

theorem heatRead_lift (hcr : ∀ i, H.ClosedRangeAt i) {y : PiLp 2 W}
    (hy : y ∈ H.hodgeLaplacian.domain) :
    H.heatRead hcr (y, DissipFEEC.genExt (-H.hodgeLaplacian) y) = y := by
  rw [heatRead_apply, H.genExt_neg_hodgeLaplacian hy, _root_.map_neg, sub_neg_eq_add,
    H.greenOp_hodgeLaplacian hcr ⟨y, hy⟩]
  abel

end Read

/-! ### The total family of a constrained FEEC discretization -/

namespace ConstrainedFEEC

variable [Fintype ι] {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- The total spaces `Xₕ = ∏ Vₕⁱ`, a subcomplex of the total complex `H.total` (reducible, so
that its space is `Xₕ` for instances). -/
abbrev totalSubcomplex (h : κ) : H.total.Subcomplex where
  V _ := totalSub (F.V h).V
  le_domain _ _ x hx := F.Xh_mem_domain h ⟨x, hx⟩
  mapsTo _ _ x hx j := by
    change (H.totalD ⟨x, F.Xh_mem_domain h ⟨x, hx⟩⟩ : PiLp 2 W) j ∈ (F.V h).V j
    rw [totalD_apply]
    exact Submodule.sum_mem _ fun i _ => (F.V h).mapsTo i j _ (hx i)

instance (h : κ) (i : Unit) : FiniteDimensional 𝕜 ((F.totalSubcomplex h).V i) :=
  inferInstanceAs (FiniteDimensional 𝕜 (F.Xh h))

/-- The total cochain projection `Πₕ`, a cochain projection onto the total subcomplex. -/
def totalProjection (h : κ) : (F.totalSubcomplex h).CochainProjection where
  π _ := F.piProj h
  mem _ := F.piProj_mem h
  proj _ _ hx := F.piProj_of_mem h hx
  comm _ _ x := F.totalD_piProj h x

/-- **The total family**: the total spaces with the total cochain projections, a conforming
family of the total complex `H.total`. -/
def totalFamily : ConformingFamily H.total κ where
  l := F.l
  V := F.totalSubcomplex
  π := F.totalProjection
  bound_π := ⟨F.projConst, fun h _ x => F.norm_piProj_le h x⟩
  approx _ w := (tendsto_infDist_submodule_iff _ w).2 fun ε hε => F.dense w ε hε

/-- **The total Jackson estimate**: a Jackson estimate of the family is one of the total family
(`totalFamily`), for the forms of `D(𝐝)` whose components are `s`-regular with bound `L`, with the
constant `(m + m²) Σᵢ B_{s,i}`, `m` the number of degrees (`Subcomplex.exists_mem_graphSub_le`). -/
def totalJackson {ρ : Type*} (J : F.Jackson ρ) : F.totalFamily.Jackson ρ where
  meshSize := J.meshSize
  meshSize_nonneg := J.meshSize_nonneg
  tendsto_meshSize := J.tendsto_meshSize
  Reg s _ L x := x ∈ H.totalD.domain ∧ ∀ i, J.Reg s i L (x i)
  ord := J.ord
  B s _ := ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) * ∑ i, J.B s i
  B_nonneg s _ := mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => J.B_nonneg s i)
  jackson s h _ L x hL hx := by
    have hr : 0 ≤ L * J.meshSize h ^ J.ord s :=
      mul_nonneg hL (Real.rpow_nonneg (J.meshSize_nonneg h) _)
    obtain ⟨w, hw, hle⟩ := (F.V h).exists_mem_graphSub_le ⟨x, hx.1⟩
      (ε := (∑ i, J.B s i) * (L * J.meshSize h ^ J.ord s)) fun i => by
        obtain ⟨v, hv, h1, h2⟩ := J.jackson s h i (x i) hL (hx.2 i)
        have hB : J.B s i * (L * J.meshSize h ^ J.ord s) ≤
            (∑ i, J.B s i) * (L * J.meshSize h ^ J.ord s) :=
          mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (fun i _ => J.B_nonneg s i) (Finset.mem_univ i)) hr
        exact ⟨v, hv, h1.trans hB, fun j hxj => (h2 j hxj).trans hB⟩
    obtain ⟨y, rfl, -, -⟩ := H.totalD.exists_toGraphSpace_eq w
    rw [← LinearPMap.toGraphSpace_sub, ← mul_assoc] at hle
    have hsq := _root_.Feec.HodgeWave.norm_sq_graphSpace (H.totalD.toGraphSpace (⟨x, hx.1⟩ - y))
    rw [graphFst_toGraphSpace, graphSnd_toGraphSpace] at hsq
    have hN := norm_nonneg (H.totalD.toGraphSpace (⟨x, hx.1⟩ - y))
    refine ⟨y, hw, ?_, fun _ _ => ?_⟩
    · change ‖((⟨x, hx.1⟩ - y : H.totalD.domain) : PiLp 2 W)‖ ≤ _
      nlinarith [norm_nonneg ((⟨x, hx.1⟩ - y : H.totalD.domain) : PiLp 2 W),
        norm_nonneg (H.totalD (⟨x, hx.1⟩ - y))]
    · change ‖H.totalD (⟨x, hx.1⟩ - y)‖ ≤ _
      nlinarith [norm_nonneg ((⟨x, hx.1⟩ - y : H.totalD.domain) : PiLp 2 W),
        norm_nonneg (H.totalD (⟨x, hx.1⟩ - y))]

/-! ### The discrete heat equation -/

/-- **The discrete Green operator** `Gₕ` on `Xₕ`: the solution operator of the discrete total
complex (`Δₕ Gₕ = 1 - P_ℌₕ`, `Subcomplex.laplacian_solutionOp`). -/
def discreteGreen (h : κ) : F.Xh h →L[𝕜] F.Xh h :=
  (F.totalSubcomplex h).toHilbertComplex.solutionOp (loop_rel () ()) (loop_rel () ())
    ((F.totalSubcomplex h).closedRangeAt ()) ((F.totalSubcomplex h).closedRangeAt ())

/-- The orthogonal projection `P_ℌₕ` of `Xₕ` onto the discrete harmonic forms. -/
def discreteHarmonicProj (h : κ) : F.Xh h →L[𝕜] F.Xh h :=
  ((F.totalSubcomplex h).toHilbertComplex.harmonic ()).starProjection

/-- **The discrete heat generator** `-Δₕ` on `Xₕ`. -/
def heatGen (h : κ) : F.Xh h →L[𝕜] F.Xh h := -(F.totalSubcomplex h).laplacian () () ()

theorem heatGen_discreteGreen (h : κ) (v : F.Xh h) :
    F.heatGen h (F.discreteGreen h v) = F.discreteHarmonicProj h v - v := by
  rw [heatGen, _root_.neg_apply, discreteGreen, Subcomplex.laplacian_solutionOp,
    neg_sub]
  rfl

theorem heatGen_discreteHarmonicProj (h : κ) (v : F.Xh h) :
    F.heatGen h (F.discreteHarmonicProj h v) = 0 := by
  rw [heatGen, _root_.neg_apply, discreteHarmonicProj, Subcomplex.laplacian_of_mem_harmonic _
    (loop_rel () ()) (loop_rel () ()) (Submodule.starProjection_apply_mem _ _), neg_zero]

/-- `-Δₕ` is dissipative: `re ⟪-Δₕ v, v⟫ = -‖dₕ* v‖² - ‖dₕ v‖² ≤ 0`. -/
theorem re_inner_heatGen_self_le (h : κ) (v : F.Xh h) : RCLike.re ⟪F.heatGen h v, v⟫ ≤ 0 := by
  rw [heatGen, _root_.neg_apply, inner_neg_left, _root_.map_neg,
    Subcomplex.re_inner_laplacian_self]
  nlinarith [sq_nonneg ‖((F.totalSubcomplex h).dh () ()).adjoint v‖,
    sq_nonneg ‖(F.totalSubcomplex h).dh () () v‖]

/-! ### The static error -/

section Static

variable (hcr : ∀ i, H.ClosedRangeAt i)

/-- **The static FEEC theorem for the total family** ([AFW2010], Thm 3.4–3.9, for the mixed
Hodge Laplacian `Δ` of `W = ⊕ Wⁱ`). -/
theorem staticVerdict_total (hcr : ∀ i, H.ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 (H.harmonic i)] :
    F.totalFamily.StaticVerdict () :=
  F.totalFamily.staticFEEC (H.closedRangeAt_total hcr) ()

/-- **The static error** `‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖` of the mixed method for `Δ` with
data `f` on the total spaces `Xₕ`. -/
def staticError (h : κ) (f : PiLp 2 W) : ℝ :=
  (F.totalSubcomplex h).mixedError (loop_rel () ()) (loop_rel () ()) f
    (H.totalMixedSolution hcr f).fst (H.totalMixedSolution hcr f).snd.fst
    (H.totalMixedSolution hcr f).snd.snd

/-- **The discrete Green operator is the mixed method**: `Gₕ Qₕ f = uₕ`, the `u` component of the
discrete mixed solution with data `f` (`Subcomplex.CochainProjection.discreteMixedSolution`). -/
theorem discreteGreen_orthProj (h : κ) (f : PiLp 2 W) :
    (F.discreteGreen h (F.orthProj h f) : PiLp 2 W) = (F.totalSubcomplex h).toW ()
      (Subcomplex.CochainProjection.discreteMixedSolution (F.totalSubcomplex h) (loop_rel () ())
        (loop_rel () ()) f).snd.fst :=
  rfl

/-- `P_ℌₕ Qₕ f = pₕ`, the harmonic component of the discrete mixed solution with data `f`. -/
theorem discreteHarmonicProj_orthProj (h : κ) (f : PiLp 2 W) :
    (F.discreteHarmonicProj h (F.orthProj h f) : PiLp 2 W) =
      (((Subcomplex.CochainProjection.discreteMixedSolution (F.totalSubcomplex h) (loop_rel () ())
        (loop_rel () ()) f).snd.snd : F.Xh h) : PiLp 2 W) :=
  congrArg Subtype.val ((F.totalSubcomplex h).toHilbertComplex.harmonic_mixedSolution
    (loop_rel () ()) (loop_rel () ()) _ _ (F.orthProj h f)).symm

theorem norm_greenOp_sub_le (h : κ) (f : PiLp 2 W) :
    ‖H.greenOp hcr f - F.discreteGreen h (F.orthProj h f)‖ ≤ F.staticError hcr h f := by
  rw [greenOp_apply, discreteGreen_orthProj, ← Subcomplex.domainIncl_embD,
    ← (H.total.domainIncl ()).map_sub]
  refine (H.total.norm_domainIncl_le () _).trans ?_
  unfold staticError Subcomplex.mixedError
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg _)

theorem norm_harmonicProj_sub_le (h : κ) (f : PiLp 2 W) :
    ‖(H.total.harmonic ()).starProjection f - F.discreteHarmonicProj h (F.orthProj h f)‖ ≤
      F.staticError hcr h f := by
  rw [← harmonic_totalMixedSolution, discreteHarmonicProj_orthProj]
  unfold staticError Subcomplex.mixedError
  exact le_add_of_nonneg_left (add_nonneg (norm_nonneg _) (norm_nonneg _))

variable [∀ i, FiniteDimensional 𝕜 (H.harmonic i)]

/-- **The static error tends to `0`** ([AFW2010], Thm 3.9 with the approximation property). -/
theorem tendsto_staticError (f : PiLp 2 W) :
    Tendsto (fun h => F.staticError hcr h f) F.l (𝓝 0) :=
  (F.staticVerdict_total hcr).converges (loop_rel () ()) (loop_rel () ())
    (H.isMixedSolution_totalMixedSolution hcr f)

theorem tendsto_discreteGreen (f : PiLp 2 W) :
    Tendsto (fun h => (F.discreteGreen h (F.orthProj h f) : PiLp 2 W)) F.l (𝓝 (H.greenOp hcr f)) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun h => (norm_sub_rev _ _).trans_le (F.norm_greenOp_sub_le hcr h f))
    (F.tendsto_staticError hcr f))

theorem tendsto_discreteHarmonicProj (hcr : ∀ i, H.ClosedRangeAt i) (f : PiLp 2 W) :
    Tendsto (fun h => (F.discreteHarmonicProj h (F.orthProj h f) : PiLp 2 W)) F.l
      (𝓝 ((H.total.harmonic ()).starProjection f)) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun h => (norm_sub_rev _ _).trans_le (F.norm_harmonicProj_sub_le hcr h f))
    (F.tendsto_staticError hcr f))

/-- **Uniform stability of the discrete Green operators** ([AFW2010], Thm 3.8). -/
theorem exists_norm_discreteGreen_le (hcr : ∀ i, H.ClosedRangeAt i) :
    ∃ C, 0 ≤ C ∧ ∀ h, ‖F.discreteGreen h‖ ≤ C := by
  obtain ⟨C, hC⟩ := (F.staticVerdict_total hcr).wellPosed (loop_rel () ()) (loop_rel () ())
  refine ⟨max C 0, le_max_right _ _, fun h => ContinuousLinearMap.opNorm_le_bound _
    (le_max_right _ _) fun f => ?_⟩
  have hx := (hC h f).2 _ ((F.totalSubcomplex h).toHilbertComplex.mixedForm_mixedSolution
    (loop_rel () ()) (loop_rel () ()) ((F.totalSubcomplex h).closedRangeAt ())
    ((F.totalSubcomplex h).closedRangeAt ()) f)
  calc ‖F.discreteGreen h f‖ ≤ _ :=
        (F.totalSubcomplex h).toHilbertComplex.norm_solutionOp_le_norm_mixedSolution _ _ _ _ f
    _ ≤ C * ‖f‖ := hx
    _ ≤ max C 0 * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

end Static


/-! ### The heat Ritz projection -/

section Ritz

variable (hcr : ∀ i, H.ClosedRangeAt i)

/-- **The heat Ritz projection** `Rₕ (y, z) = P_ℌₕ Qₕ y - Gₕ Qₕ z`: on the graph lift,
`Rₕ ℓ y = Gₕ Qₕ (Δ y) + P_ℌₕ Qₕ y`, the discrete mixed solution with data `Δ y` plus the discrete
harmonic part of `y` (the elliptic projection of [Wheeler1973] for `Δ`). -/
def ritzR (h : κ) : PiLp 2 W × PiLp 2 W →L[𝕜] F.Xh h :=
  F.discreteHarmonicProj h ∘L F.orthProj h ∘L ContinuousLinearMap.fst 𝕜 _ _ -
    F.discreteGreen h ∘L F.orthProj h ∘L ContinuousLinearMap.snd 𝕜 _ _

theorem ritzR_apply (h : κ) (g : PiLp 2 W × PiLp 2 W) :
    F.ritzR h g = F.discreteHarmonicProj h (F.orthProj h g.1) -
      F.discreteGreen h (F.orthProj h g.2) :=
  rfl

/-- **The heat Ritz projection on the graph lift** is the discrete mixed solution with data `Δ y`
plus the discrete harmonic part of `y`: `Rₕ ℓ y = Gₕ Qₕ (Δ y) + P_ℌₕ Qₕ y` on `D(Δ)`. -/
theorem ritzR_lift (h : κ) {y : PiLp 2 W} (hy : y ∈ H.hodgeLaplacian.domain) :
    F.ritzR h (y, DissipFEEC.genExt (-H.hodgeLaplacian) y) =
      F.discreteGreen h (F.orthProj h (H.hodgeLaplacian ⟨y, hy⟩)) +
        F.discreteHarmonicProj h (F.orthProj h y) := by
  rw [ritzR_apply, H.genExt_neg_hodgeLaplacian hy, _root_.map_neg, _root_.map_neg,
    sub_neg_eq_add, add_comm]

/-- The defect operator `Δₕ (y, z) = 2 P_ℌₕ Qₕ (1 - P_ℌ) y + Qₕ G z - Gₕ Qₕ z` of the heat Ritz
projection; on `ℓ (A y)` it is the consistency defect (`ritzDefect_lift`), and it tends to `0`
strongly (`tendsto_ritzDefect`). -/
def ritzDefect (h : κ) : PiLp 2 W × PiLp 2 W →L[𝕜] F.Xh h :=
  (2 : 𝕜) • (F.discreteHarmonicProj h ∘L F.orthProj h ∘L
      (1 - (H.total.harmonic ()).starProjection) ∘L ContinuousLinearMap.fst 𝕜 _ _) +
    (F.orthProj h ∘L H.greenOp hcr - F.discreteGreen h ∘L F.orthProj h) ∘L
      ContinuousLinearMap.snd 𝕜 _ _

theorem ritzDefect_apply (h : κ) (g : PiLp 2 W × PiLp 2 W) :
    F.ritzDefect hcr h g = (2 : 𝕜) • F.discreteHarmonicProj h
        (F.orthProj h (g.1 - (H.total.harmonic ()).starProjection g.1)) +
      (F.orthProj h (H.greenOp hcr g.2) - F.discreteGreen h (F.orthProj h g.2)) :=
  rfl

/-- **The Galerkin property of the heat Ritz projection**: `-Δₕ Rₕ (y, z) = (1 - P_ℌₕ) Qₕ z`;
on the graph lift, `Δₕ Rₕ ℓ y = (1 - P_ℌₕ) Qₕ Δ y`. -/
theorem heatGen_ritzR (h : κ) (g : PiLp 2 W × PiLp 2 W) :
    F.heatGen h (F.ritzR h g) = F.orthProj h g.2 - F.discreteHarmonicProj h (F.orthProj h g.2) := by
  rw [ritzR_apply, _root_.map_sub, heatGen_discreteHarmonicProj, heatGen_discreteGreen]
  abel

/-- **The defect identity of the heat Ritz projection** (pointwise in `Xₕ`, for every `y`):
`Rₕ ℓ(A y) - Lₕ Rₕ ℓ y = Rₕ ℓ(A y) - (1 - P_ℌₕ) Qₕ (A y)`, `A = -Δ`, `Lₕ = -Δₕ`; for `y ∈ D(Δ²)`,
where `A y = -Δ y` and `ℓ (A y) = -ℓ (Δ y)`, the defect is `(Qₕ - Rₕ ℓ)(Δ y) - P_ℌₕ Qₕ Δ y`. -/
theorem heatRitz_defect_eq (h : κ) (y : PiLp 2 W) :
    F.ritzR h (DissipFEEC.genExt (-H.hodgeLaplacian) y,
        DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y)) -
        F.heatGen h (F.ritzR h (y, DissipFEEC.genExt (-H.hodgeLaplacian) y)) =
      F.ritzR h (DissipFEEC.genExt (-H.hodgeLaplacian) y,
          DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y)) -
        (F.orthProj h (DissipFEEC.genExt (-H.hodgeLaplacian) y) -
          F.discreteHarmonicProj h (F.orthProj h (DissipFEEC.genExt (-H.hodgeLaplacian) y))) := by
  rw [heatGen_ritzR]

/-- **The defect operator on the lifted velocities**: for `a ∈ D(Δ)` with `P_ℌ a = 0` (e.g.
`a = A y`), `Δₕ ℓ a = Rₕ ℓ a - (1 - P_ℌₕ) Qₕ a` (`G A a = -a`, the Hodge decomposition). -/
theorem ritzDefect_lift (h : κ) {a : PiLp 2 W} (ha : a ∈ H.hodgeLaplacian.domain)
    (hPa : (H.total.harmonic ()).starProjection a = 0) :
    F.ritzDefect hcr h (a, DissipFEEC.genExt (-H.hodgeLaplacian) a) =
      F.ritzR h (a, DissipFEEC.genExt (-H.hodgeLaplacian) a) -
        (F.orthProj h a - F.discreteHarmonicProj h (F.orthProj h a)) := by
  have hG : H.greenOp hcr (DissipFEEC.genExt (-H.hodgeLaplacian) a) = -a := by
    rw [H.genExt_neg_hodgeLaplacian ha, _root_.map_neg, H.greenOp_hodgeLaplacian hcr ⟨a, ha⟩]
    change -(a - (H.total.harmonic ()).starProjection a) = -a
    rw [hPa, sub_zero]
  rw [ritzDefect_apply, ritzR_apply, hPa, sub_zero, hG, _root_.map_neg, two_smul]
  change _ = F.discreteHarmonicProj h (F.orthProj h a) - _ - _
  abel

theorem norm_orthProj_apply_le (h : κ) (x : PiLp 2 W) : ‖F.orthProj h x‖ ≤ ‖x‖ :=
  Submodule.norm_orthogonalProjectionOnto_apply_le _ x

theorem norm_discreteHarmonicProj_apply_le (h : κ) (v : F.Xh h) :
    ‖F.discreteHarmonicProj h v‖ ≤ ‖v‖ :=
  Submodule.norm_starProjection_apply_le _ v

/-- **The defect operator is small**: `‖Δₕ (y, z)‖ ≤ 2 e((1 - P_ℌ) y) + e(z)`, `e` the static
error. -/
theorem norm_ritzDefect_le (h : κ) (g : PiLp 2 W × PiLp 2 W) :
    ‖F.ritzDefect hcr h g‖ ≤
      2 * F.staticError hcr h (g.1 - (H.total.harmonic ()).starProjection g.1) +
        F.staticError hcr h g.2 := by
  set P := (H.total.harmonic ()).starProjection
  have h1 : ‖F.discreteHarmonicProj h (F.orthProj h (g.1 - P g.1))‖ ≤
      F.staticError hcr h (g.1 - P g.1) := by
    have e : P (g.1 - P g.1) = 0 := by
      rw [_root_.map_sub, Submodule.starProjection_eq_self_iff.2
        (Submodule.starProjection_apply_mem _ _), sub_self]
    have := F.norm_harmonicProj_sub_le hcr h (g.1 - P g.1)
    rwa [e, zero_sub, norm_neg] at this
  have h2 : ‖F.orthProj h (H.greenOp hcr g.2) - F.discreteGreen h (F.orthProj h g.2)‖ ≤
      F.staticError hcr h g.2 := by
    have e : F.orthProj h (H.greenOp hcr g.2) - F.discreteGreen h (F.orthProj h g.2) =
        F.orthProj h (H.greenOp hcr g.2 - F.discreteGreen h (F.orthProj h g.2)) := by
      rw [_root_.map_sub, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rw [e]
    exact (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans
      (F.norm_greenOp_sub_le hcr h g.2)
  rw [ritzDefect_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, RCLike.norm_ofNat]
  linarith

/-! ### Rates: the static error along the orbit -/

section Rate

variable {ρ : Type*} (J : F.totalFamily.Jackson ρ) (s : ρ)

/-- `f` has an `s`-regular mixed solution with bound `L`: the solution `(σ, u, p)` of the mixed
problem of `Δ` with data `f`, the boundary part of `u`, and `p` are in the class `s` of the Jackson
estimate `J` of the total family. -/
def RegMixed (L : ℝ) (f : PiLp 2 W) : Prop :=
  J.Reg s () L (H.total.domainIncl () (H.totalMixedSolution hcr f).fst) ∧
    J.Reg s () L (H.total.domainIncl () (H.totalMixedSolution hcr f).snd.fst) ∧
    J.Reg s () L (H.total.domainIncl () (H.total.boundaryPart ()
      (H.total.domainIncl () (H.totalMixedSolution hcr f).snd.fst))) ∧
    J.Reg s () L ((H.totalMixedSolution hcr f).snd.snd : PiLp 2 W)

/-- **The static rate for the total family** ([AFW2010], Thm 3.9 with a Jackson estimate,
`ConformingFamily.StaticVerdict.rate`): `e(f) ≤ K L hᵒʳᵈ` for data with `s`-regular mixed
solutions. -/
theorem exists_staticError_le [∀ i, FiniteDimensional 𝕜 (H.harmonic i)] :
    ∃ K, 0 ≤ K ∧ ∀ {L : ℝ} {f : PiLp 2 W}, 0 ≤ L →
    F.RegMixed hcr J s L f → ∀ h, F.staticError hcr h f ≤ K * L * J.meshSize h ^ J.ord s := by
  obtain ⟨K, hK⟩ := (F.staticVerdict_total hcr).rate J s (loop_rel () ()) (loop_rel () ())
  refine ⟨max K 0, le_max_right _ _, fun {L f} hL hf h => (hK (H.isMixedSolution_totalMixedSolution
    hcr f) hL hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 h).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hL)
    (Real.rpow_nonneg (J.meshSize_nonneg h) _)

/-- **The regular states of the heat rate**: `y ∈ D(Δ²)` such that `y`, `A y` and `A² y` (`A = -Δ`)
have `s`-regular mixed solutions with bound `L`. -/
def heatReg (L : ℝ) : Set (PiLp 2 W) :=
  {y | y ∈ (-H.hodgeLaplacian).sqDomain ∧ F.RegMixed hcr J s L y ∧
    F.RegMixed hcr J s L (DissipFEEC.genExt (-H.hodgeLaplacian) y) ∧
    F.RegMixed hcr J s L (DissipFEEC.genExt (-H.hodgeLaplacian)
      (DissipFEEC.genExt (-H.hodgeLaplacian) y))}

variable {J s} {K : ℝ} (hK : ∀ {L : ℝ} {f : PiLp 2 W}, 0 ≤ L →
    F.RegMixed hcr J s L f → ∀ h, F.staticError hcr h f ≤ K * L * J.meshSize h ^ J.ord s)
  {L : ℝ} (hL : 0 ≤ L)
include hK hL

/-- **Static approximation of the heat Ritz projection**: `‖y - ιₕ Rₕ ℓ y‖ ≤ e(y) + e(A y)
≤ 2 K L hᵒʳᵈ` on the regular states (`y = P_ℌ y - G A y`). -/
theorem norm_sub_ritzR_le {y : PiLp 2 W} (hy : y ∈ F.heatReg hcr J s L) (h : κ) :
    ‖y - (F.ritzR h (y, DissipFEEC.genExt (-H.hodgeLaplacian) y) : PiLp 2 W)‖ ≤
      2 * K * L * J.meshSize h ^ J.ord s := by
  set a := DissipFEEC.genExt (-H.hodgeLaplacian) y
  have hy' : (H.total.harmonic ()).starProjection y - H.greenOp hcr a = y :=
    H.heatRead_lift hcr hy.1.1
  have e : y - (F.ritzR h (y, a) : PiLp 2 W) =
      ((H.total.harmonic ()).starProjection y - F.discreteHarmonicProj h (F.orthProj h y)) -
        (H.greenOp hcr a - F.discreteGreen h (F.orthProj h a)) := by
    calc y - (F.ritzR h (y, a) : PiLp 2 W) =
        ((H.total.harmonic ()).starProjection y - H.greenOp hcr a) -
          (F.ritzR h (y, a) : PiLp 2 W) :=
          by rw [hy']
      _ = _ := by rw [ritzR_apply]; push_cast; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := (F.norm_harmonicProj_sub_le hcr h y).trans (hK hL hy.2.1 h)
  have h2 := (F.norm_greenOp_sub_le hcr h a).trans (hK hL hy.2.2.1 h)
  linarith

/-- **Static consistency of the heat Ritz projection**: `‖Δₕ ℓ(A y)‖ ≤ 2 e(A y) + e(A² y)
≤ 3 K L hᵒʳᵈ` on the regular states (`P_ℌ A y = 0`). -/
theorem norm_ritzDefect_lift_le {y : PiLp 2 W} (hy : y ∈ F.heatReg hcr J s L) (h : κ) :
    ‖F.ritzDefect hcr h (DissipFEEC.genExt (-H.hodgeLaplacian) y,
      DissipFEEC.genExt (-H.hodgeLaplacian) (DissipFEEC.genExt (-H.hodgeLaplacian) y))‖ ≤
      3 * K * L * J.meshSize h ^ J.ord s := by
  have hPa :
      (H.total.harmonic ()).starProjection (DissipFEEC.genExt (-H.hodgeLaplacian) y) = 0 := by
    rw [H.genExt_neg_hodgeLaplacian hy.1.1, _root_.map_neg,
      H.starProjection_harmonic_total_hodgeLaplacian, neg_zero]
  refine (F.norm_ritzDefect_le hcr h _).trans ?_
  dsimp only
  rw [hPa, sub_zero]
  linarith [hK hL hy.2.2.1 h, hK hL hy.2.2.2 h]

end Rate

/-! ### The heat FEEC theorem -/

section Heat

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The heat FEEC discretization** of the Hodge heat equation `u' = -Δ u` on `W = ⊕ Wⁱ`:
`Xₕ = ∏ Vₕⁱ` with the `W` inner product, `Lₕ = -Δₕ` the discrete Hodge Laplacian of the total
spaces (`heatGen`), `ιₕ` the inclusion, `πₕ = Qₕ` the orthogonal projection. -/
def toHeat : DissipFEEC (-H.hodgeLaplacian) κ where
  isMDissipative := H.isMDissipative_neg_hodgeLaplacian
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X := F.Xh
  L := F.heatGen
  dissipative := F.re_inner_heatGen_self_le
  incl h := (totalSub (F.V h).V).subtypeL
  proj := F.orthProj
  proj_incl _ x := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
  bound := ⟨1, fun h => ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact le_rfl, Submodule.orthogonalProjectionOnto_norm_le _⟩⟩

theorem toHeat_L (h : κ) : F.toHeat.L h = F.heatGen h := rfl

theorem toHeat_incl_apply (h : κ) (v : F.Xh h) : F.toHeat.incl h v = (v : PiLp 2 W) := rfl

theorem norm_toHeat_incl_le (h : κ) : ‖F.toHeat.incl h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact le_rfl


/-- **The graph lift** `ℓ y = (y, -Δ y)` of `D(Δ²)` for the heat equation, read by
`ρ (y, z) = P_ℌ y - G z`. -/
def heatLift : F.toHeat.Lift (PiLp 2 W × PiLp 2 W) :=
  DissipFEEC.Lift.graph F.toHeat (H.heatRead hcr) fun _ hy => H.heatRead_lift hcr hy.1

variable [∀ i, FiniteDimensional 𝕜 (H.harmonic i)]

/-- **The heat Ritz projection** of the heat FEEC discretization, for the graph lift of `D(Δ²)`:
`Rₕ = ritzR`, defects `Δₕ = ritzDefect`, `Δₕ' = 0`, uniformly bounded by the uniform stability of
the discrete mixed problem ([AFW2010], Thm 3.8). -/
def heatRitz : F.toHeat.Ritz (F.heatLift hcr) where
  R := F.ritzR
  Δ := F.ritzDefect hcr
  Δ' _ := 0
  defect_eq h y hy := by
    obtain ⟨hy1, hy2⟩ := DissipFEEC.mem_sqDomain_iff.1 hy
    have hPa :
        (H.total.harmonic ()).starProjection (DissipFEEC.genExt (-H.hodgeLaplacian) y) = 0 := by
      rw [H.genExt_neg_hodgeLaplacian hy1, _root_.map_neg,
        H.starProjection_harmonic_total_hodgeLaplacian, neg_zero]
    exact (F.heatRitz_defect_eq h y).trans
      ((F.ritzDefect_lift hcr h hy2 hPa).symm.trans (add_zero _).symm)
  bound := by
    obtain ⟨C, hC0, hC⟩ := F.exists_norm_discreteGreen_le hcr
    set B := ‖H.greenOp hcr‖
    refine ⟨4 + B + C, fun h => ⟨?_, ?_, by rw [norm_zero]; positivity⟩⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
      rw [ritzR_apply]
      have h1 := (F.norm_discreteHarmonicProj_apply_le h _).trans
        ((F.norm_orthProj_apply_le h g.1).trans (norm_fst_le g))
      have h2 := ((F.discreteGreen h).le_opNorm _).trans (mul_le_mul (hC h)
        ((F.norm_orthProj_apply_le h g.2).trans (norm_snd_le g))
        (norm_nonneg _) hC0)
      have := norm_sub_le (F.discreteHarmonicProj h (F.orthProj h g.1))
        (F.discreteGreen h (F.orthProj h g.2))
      have hB := norm_nonneg (H.greenOp hcr)
      nlinarith [norm_nonneg g]
    · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
      rw [ritzDefect_apply]
      set P := (H.total.harmonic ()).starProjection
      have hP : ‖g.1 - P g.1‖ ≤ 2 * ‖g‖ := (norm_sub_le _ _).trans (by
        have := Submodule.norm_starProjection_apply_le (H.total.harmonic ()) g.1
        linarith [norm_fst_le g])
      have h1 := (F.norm_discreteHarmonicProj_apply_le h _).trans
        ((F.norm_orthProj_apply_le h (g.1 - P g.1)).trans hP)
      have h2 := (F.norm_orthProj_apply_le h (H.greenOp hcr g.2)).trans
        (((H.greenOp hcr).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_snd_le g)
          (norm_nonneg _)))
      have h3 := ((F.discreteGreen h).le_opNorm _).trans (mul_le_mul (hC h)
        ((F.norm_orthProj_apply_le h g.2).trans (norm_snd_le g))
        (norm_nonneg _) hC0)
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofNat]
      have := norm_sub_le (F.orthProj h (H.greenOp hcr g.2)) (F.discreteGreen h (F.orthProj h g.2))
      nlinarith [norm_nonneg g]

/-- **The heat core**: the core of the heat Ritz projection, data `D(Δ²)` (dense,
`dense_heatCore_data`), from the convergence of the static mixed method (the static error tends
to `0`, [AFW2010], Thm 3.9). -/
def heatCore : F.toHeat.Core :=
  (F.heatRitz hcr).toCore
    (fun g => ((F.tendsto_discreteHarmonicProj hcr g.1).sub (F.tendsto_discreteGreen hcr g.2)))
    (fun g => squeeze_zero (fun _ => norm_nonneg _) (fun h => F.norm_ritzDefect_le hcr h g) (by
      show Tendsto _ F.l _
      simpa using ((F.tendsto_staticError hcr _).const_mul 2).add (F.tendsto_staticError hcr g.2)))
    (fun _ => tendsto_const_nhds.congr fun _ => norm_zero.symm)

theorem heatCore_data : (F.heatCore hcr).Data = (-H.hodgeLaplacian).sqDomain := rfl

/-- The data `D(Δ²)` of the heat core are dense: the heat FEEC theorem applies to every datum. -/
theorem dense_heatCore_data : (F.heatCore hcr).Data.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.1 H.isMDissipative_neg_hodgeLaplacian.dense_sqDomain

/-- **The heat core has nonzero data** as soon as the window is nonzero (`dense_heatCore_data`). -/
theorem exists_mem_heatCore_data_ne_zero [Nontrivial (PiLp 2 W)] :
    ∃ x ∈ (F.heatCore hcr).Data, x ≠ 0 :=
  H.isMDissipative_neg_hodgeLaplacian.dense_sqDomain.exists_mem_open isOpen_ne (exists_ne 0)

/-- **The heat FEEC theorem** (`DissipFEEC.Verdict` of the heat FEEC discretization with the heat
core): well-posedness and the energy identity, propagation of `K`, convergence of the discrete
heat flows from every convergent family of discrete data (every datum: `dense_heatCore_data`),
rates for every rate class (`rate_heat`), the constraint residual. -/
theorem heatFEEC : F.toHeat.Verdict (F.heatCore hcr) :=
  dissipFEEC F.toHeat (F.heatCore hcr)

section Rate

variable {ρ : Type*} {J : F.totalFamily.Jackson ρ} {s : ρ} {K : ℝ} (hK0 : 0 ≤ K)
  (hK : ∀ {L : ℝ} {f : PiLp 2 W}, 0 ≤ L →
    F.RegMixed hcr J s L f → ∀ h, F.staticError hcr h f ≤ K * L * J.meshSize h ^ J.ord s)
  {L : ℝ} (hL : 0 ≤ L)
include hK0 hK hL

/-- **The heat rate class** on `[0, T]` of the heat Ritz projection: data `x ∈ D(Δ²)` whose orbit
stays in the regular states with bound `L`, approximation constant `2K` and consistency constant
`3K`, `K` the constant of the static rate. -/
def heatRateClass (T : ℝ) : F.toHeat.RateClass T :=
  (F.heatRitz hcr).toRateClass (DissipFEEC.RegScale.trajectory F.toHeat T
      (-H.hodgeLaplacian).sqDomain (F.heatReg hcr J s L) (fun _ => L) (fun _ => L))
    (fun _ hx => hx.1) J.meshSize J.meshSize_nonneg (J.ord s) (2 * K) (3 * K) (by positivity)
    (by positivity)
    (fun y hy h => by
      show _ ≤ 2 * K * J.meshSize h ^ J.ord s * L
      exact (F.norm_sub_ritzR_le hcr hK hL hy h).trans_eq (by ring))
    (fun y hy h => by
      show _ + ‖(0 : PiLp 2 W × PiLp 2 W →L[𝕜] F.Xh h) _‖ ≤ 3 * K * J.meshSize h ^ J.ord s * L
      rw [_root_.zero_apply, norm_zero, add_zero]
      exact (F.norm_ritzDefect_lift_le hcr hK hL hy h).trans_eq (by ring))

/-- **The heat rate, from the static rate**: for `x ∈ D(Δ²)` whose orbit on `[0, T]` stays in the
regular states with bound `L`, `‖S(t) x - ιₕ e^{-tΔₕ} Rₕ ℓ x‖ ≤ (2 + 3t) K L hᵒʳᵈ`, for every
constant `K` of the static rate `e(f) ≤ K L hᵒʳᵈ` ([AFW2010], Thm 3.9): the static estimate enters
the dynamic one directly. -/
theorem rate_heat_of_static {T : ℝ} {x : PiLp 2 W} (hx : x ∈ (-H.hodgeLaplacian).sqDomain)
    (hreg : ∀ t ∈ Icc 0 T, F.toHeat.S t x ∈ F.heatReg hcr J s L) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖F.toHeat.S t x - F.toHeat.sol h (F.ritzR h (x, DissipFEEC.genExt (-H.hodgeLaplacian) x)) t‖ ≤
      (2 + 3 * t) * K * L * J.meshSize h ^ J.ord s := by
  set R := F.heatRateClass hcr hK0 hK hL T
  have hxR : x ∈ R.Data := ⟨hx, fun t ht => ⟨hreg t ht, le_rfl⟩⟩
  have hp : R.p x h 0 = F.ritzR h (x, DissipFEEC.genExt (-H.hodgeLaplacian) x) := by
    change F.ritzR h ((F.heatLift hcr).lift (F.toHeat.S 0 x)) = _
    rw [DissipFEEC.S_def, C0Semigroup.S_zero_apply]
    rfl
  have hr := dissipFEEC_rate F.toHeat R hxR h (R.p x h 0) ht
  rw [sub_self, norm_zero, mul_zero, add_zero] at hr
  rw [← hp]
  refine hr.trans ?_
  change (2 * K * 1 + ‖F.toHeat.incl h‖ * (3 * K * 1) * t) *
    (J.meshSize h ^ J.ord s * L) ≤ _
  have hι := F.norm_toHeat_incl_le h
  have hm := Real.rpow_nonneg (J.meshSize_nonneg h) (J.ord s)
  have h0 : ‖F.toHeat.incl h‖ * (3 * K * 1) * t ≤ 3 * K * t := by
    have := mul_le_mul_of_nonneg_right hι (mul_nonneg (by positivity) ht.1 : 0 ≤ 3 * K * 1 * t)
    nlinarith [norm_nonneg (F.toHeat.incl h)]
  have := mul_le_mul_of_nonneg_right (add_le_add_left h0 (2 * K * 1)) (mul_nonneg hm hL)
  nlinarith

end Rate

/-- **The heat rate** ([AFW2010], Thm 3.9 along the heat flow): there is a constant `K`, the
constant of the static rate of the total family (`exists_staticError_le`), such that for
`x ∈ D(Δ²)` whose orbit on `[0, T]` stays in the regular states with bound `L`,
`‖S(t) x - ιₕ e^{-tΔₕ} Rₕ ℓ x‖ ≤ (2 + 3t) K L hᵒʳᵈ`. -/
theorem rate_heat {ρ : Type*} (J : F.totalFamily.Jackson ρ) (s : ρ) :
    ∃ K, 0 ≤ K ∧ ∀ {L : ℝ}, 0 ≤ L →
    ∀ {T : ℝ} {x : PiLp 2 W}, x ∈ (-H.hodgeLaplacian).sqDomain →
    (∀ t ∈ Icc 0 T, F.toHeat.S t x ∈ F.heatReg hcr J s L) → ∀ (h : κ), ∀ t ∈ Icc 0 T,
    ‖F.toHeat.S t x - F.toHeat.sol h (F.ritzR h (x, DissipFEEC.genExt (-H.hodgeLaplacian) x)) t‖ ≤
      (2 + 3 * t) * K * L * J.meshSize h ^ J.ord s := by
  obtain ⟨K, hK0, hK⟩ := F.exists_staticError_le hcr J s
  exact ⟨K, hK0, fun {_} hL {_ _} hx hreg h _ ht =>
    F.rate_heat_of_static hcr hK0 hK hL hx hreg h ht⟩

/-- **The heat rate class of a Jackson estimate** `J` of the total family: `heatRateClass` with
the constant `K` of the static rate (`exists_staticError_le`), approximation constant `2K` and
consistency constant `3K`. -/
def jacksonHeatRateClass {ρ : Type*} (J : F.totalFamily.Jackson ρ) (s : ρ) {L : ℝ} (hL : 0 ≤ L)
    (T : ℝ) : F.toHeat.RateClass T :=
  F.heatRateClass hcr (F.exists_staticError_le hcr J s).choose_spec.1
    (F.exists_staticError_le hcr J s).choose_spec.2 hL T

end Heat

end Ritz

end ConstrainedFEEC

end Feec.HilbertComplex
