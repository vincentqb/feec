module

public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.HilbertComplex.Approximation.QuasiOptimal

/-!
# Discrete cohomology: a cochain projection is an isomorphism on cohomology

Let `Vₕ` be a finite-dimensional subcomplex of a Hilbert complex `H` and `π` a cochain projection
onto `Vₕ`. Since `π` maps cycles to discrete cycles and boundaries to discrete boundaries, it
induces a map `Hⁱ(H) → Hⁱ(Vₕ)` on cohomology (`CochainProjection.cohomologyMap`), and since `π`
fixes `Vₕ` this map is **onto** (`cohomologyMap_surjective`): every discrete cycle is a cycle.
If `H` has closed range at `i` and `π` moves no harmonic form by its own length,

`‖q - π q‖ < ‖q‖`  for `0 ≠ q ∈ ℌⁱ`,

the map is also **one-to-one** (`cohomologyMap_injective`): write a cycle `z = b + q` with
`b ∈ 𝔅ⁱ`, `q ∈ ℌⁱ`; if `π z ∈ 𝔅ₕⁱ` then `π q ∈ 𝔅ₕⁱ ⊆ 𝔅ⁱ ⊥ q`, and the strict gap forces `q = 0`.
Hence `Hⁱ(Vₕ) ≅ Hⁱ(H)` (`CochainProjection.cohomologyEquiv`) and
`dim ℌₕⁱ = dim ℌⁱ` (`finrank_harmonicW_eq`); in particular `ℌⁱ` is finite-dimensional. No bound
on `π` is needed for the isomorphism itself.

The strict gap holds as soon as the harmonic gap `μ = sup_{q ∈ ℌ, ‖q‖ ≤ 1} ‖q - π q‖` is below
`1` (`norm_sub_π_lt_of_harmonicGap_lt_one`), so for a family of subcomplexes whose harmonic gap
tends to zero the discrete cohomology is **eventually the continuous cohomology**
(`eventually_finrank_cohomology_eq`, `eventually_finrank_harmonicW_eq`). The harmonic gap tends to
zero for uniformly `W`-bounded projections approximating a finite-dimensional `ℌ`
(`CochainProjection.tendsto_harmonicGap`: `‖q - π q‖ ≤ (1 + C) dist(q, Vₕ)`, and a basis of `ℌ`
makes the convergence uniform on the unit ball). So **every conforming family**
(`Feec.HilbertComplex.ConformingFamily`: bounded commuting projections and the approximation
property in `W`, a strengthening of the `V`-bounds of [AFW2010], §3.3) has, wherever `H` has
closed range and finite-dimensional harmonic forms, eventually the cohomology of `H`, through the
isomorphisms induced by its projections (`ConformingFamily.eventually_bijective_cohomologyMap`).
The isomorphism criterion itself (`CochainProjection.cohomologyMap_injective`) needs no bound.

## Main definitions

* `Subcomplex.CochainProjection.cyclesMap`: `π : 𝔷ⁱ → 𝔷ₕⁱ`.
* `Subcomplex.CochainProjection.cohomologyMap`: the induced map `Hⁱ(H) → Hⁱ(Vₕ)`.
* `Subcomplex.CochainProjection.cohomologyEquiv`: `Hⁱ(H) ≃ Hⁱ(Vₕ)` under the strict gap.

## Main results

* `CochainProjection.cohomologyMap_surjective`, **`CochainProjection.cohomologyMap_injective`**.
* **`CochainProjection.finrank_cohomology_eq`**, **`CochainProjection.finrank_harmonicW_eq`**,
  `CochainProjection.finiteDimensional_harmonic`.
* `CochainProjection.norm_sub_π_lt_of_harmonicGap_lt_one`.
* `CochainProjection.norm_sub_π_le_infDist`, `CochainProjection.tendsto_harmonicGap_of_tendsto`,
  **`CochainProjection.tendsto_harmonicGap`**.
* `CochainProjection.norm_sub_π_le_add` (`x ↦ ‖x − π x‖` is `(1 + C)`-Lipschitz),
  `CochainProjection.eventually_forall_norm_sub_π_le` (uniform convergence on compact sets).
* **`CochainProjection.eventually_finrank_cohomology_eq`**,
  `CochainProjection.eventually_finrank_harmonicW_eq`: along any filter on which the harmonic gap
  tends to zero.
* `ConformingFamily.tendsto_harmonicGap`, **`ConformingFamily.eventually_bijective_cohomologyMap`**,
  `ConformingFamily.eventually_finrank_cohomology_eq`,
  `ConformingFamily.eventually_finrank_harmonicW_eq`: every conforming family.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.4 (a cochain projection with `‖q - π q‖ < ‖q‖` on `ℌ \ 0` induces an isomorphism on
  cohomology), Thm 3.5 (the gap between `ℌ` and `ℌₕ`), §5.6 (finite element de Rham complexes)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5.2, §5.4 (canonical and smoothed cochain projections onto the finite element de Rham complexes)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Filter Topology

@[expose] public noncomputable section

/-- **Uniform convergence on compact sets**: a family `F h` of functions, Lipschitz in `x` with a
common constant and tending to `0` pointwise along `l`, tends to `0` uniformly on every compact
set. -/
theorem IsCompact.eventually_forall_le_of_lipschitz {E κ : Type*} [PseudoMetricSpace E]
    {K : Set E} (hK : IsCompact K) {l : Filter κ} {F : κ → E → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hlip : ∀ h x y, F h x ≤ F h y + B * dist x y)
    (hF : ∀ x, Tendsto (fun h => F h x) l (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in l, ∀ x ∈ K, F h x ≤ ε := by
  have hδ : 0 < ε / (2 * (B + 1)) := by positivity
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hK hδ
  have hev : ∀ᶠ h in l, ∀ y ∈ t, F h y < ε / 2 :=
    (Filter.eventually_all_finite htf).2 fun y _ =>
      (hF y).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with h hh x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  have h3 : B * dist x y ≤ B * (ε / (2 * (B + 1))) :=
    mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hxy).le hB
  have h4 : B * (ε / (2 * (B + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith [hlip h x y, hh y hy]

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Subcomplex

namespace CochainProjection

section Single

variable {S : H.Subcomplex} [∀ i, FiniteDimensional 𝕜 (S.V i)] (P : S.CochainProjection)

/-- `π` on the cycles, valued in the discrete cycles `𝔷ₕⁱ` (the cycles of `S.toHilbertComplex`). -/
def cyclesMap (i : ι) : H.cycles i →ₗ[𝕜] S.toHilbertComplex.cycles i where
  toFun z := ⟨⟨P.π i z, P.mem i z⟩, S.mem_cycles_iff.2 (S.cyclesW_le_cycles i (P.mem_cyclesW z.2))⟩
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

@[simp] theorem coe_cyclesMap_apply (i : ι) (z : H.cycles i) :
    ((P.cyclesMap i z : S.V i) : W i) = P.π i z := rfl

/-- **The map induced on cohomology** `Hⁱ(H) → Hⁱ(Vₕ)`, `[z] ↦ [π z]`. [AFW2010], §3.3 -/
def cohomologyMap (i : ι) : H.cohomology i →ₗ[𝕜] S.toHilbertComplex.cohomology i :=
  Submodule.mapQ _ _ (P.cyclesMap i) fun _ hz => S.mem_boundaries_iff.2 (P.mem_boundariesW hz)

/-- **The induced map on cohomology is onto**: a discrete cycle `z` is a cycle with `π z = z`.
[AFW2010], §3.3 -/
theorem cohomologyMap_surjective (i : ι) : Function.Surjective (P.cohomologyMap i) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨Submodule.Quotient.mk ⟨((x : S.V i) : W i), S.mem_cycles_iff.1 x.2⟩, ?_⟩
  rw [cohomologyMap, Submodule.mapQ_apply]
  congr 1
  ext
  exact P.proj i _ (x : S.V i).2

/-- **The induced map on cohomology is one-to-one** under closed range and the strict gap
`‖q - π q‖ < ‖q‖` on `ℌⁱ \ 0`. [AFW2010], Thm 3.4 -/
theorem cohomologyMap_injective {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    Function.Injective (P.cohomologyMap i) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [cohomologyMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  have hz : P.π i z ∈ S.boundariesW i := S.mem_boundaries_iff.1 hy
  have hz' : (z : W i) ∈ H.boundaries i ⊔ H.harmonic i := by
    rw [H.boundaries_sup_harmonic hi]; exact z.2
  obtain ⟨b, hb, q, hq, hbq⟩ := Submodule.mem_sup.1 hz'
  have hπq : P.π i q ∈ H.boundaries i := by
    have := (S.boundariesW i).sub_mem hz (P.mem_boundariesW hb)
    rw [← hbq, _root_.map_add, add_sub_cancel_left] at this
    exact S.boundariesW_le i this
  have hq0 : q = 0 := by
    by_contra hq0
    have h0 : ⟪P.π i q, q⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hπq (H.mem_harmonic_iff.1 hq).2
    have hle : ‖q‖ ^ 2 ≤ ‖q - P.π i q‖ * ‖q‖ := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), show ⟪q, q⟫ = ⟪q - P.π i q, q⟫ by
        rw [inner_sub_left, h0, sub_zero]]
      exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
    nlinarith [hgap q hq hq0]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, ← hbq, hq0,
    add_zero]
  exact hb

/-- **A cochain projection is an isomorphism on cohomology** `Hⁱ(H) ≃ Hⁱ(Vₕ)` under closed range
and the strict gap `‖q - π q‖ < ‖q‖` on `ℌⁱ \ 0`. [AFW2010], Thm 3.4 -/
def cohomologyEquiv {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    H.cohomology i ≃ₗ[𝕜] S.toHilbertComplex.cohomology i :=
  LinearEquiv.ofBijective _ ⟨P.cohomologyMap_injective hi hgap, P.cohomologyMap_surjective i⟩

@[simp] theorem cohomologyEquiv_apply {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) (x : H.cohomology i) :
    P.cohomologyEquiv hi hgap x = P.cohomologyMap i x := rfl

/-- **`dim Hⁱ(Vₕ) = dim Hⁱ(H)`**. [AFW2010], Thm 3.4 -/
theorem finrank_cohomology_eq {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    Module.finrank 𝕜 (S.toHilbertComplex.cohomology i) = Module.finrank 𝕜 (H.cohomology i) :=
  (P.cohomologyEquiv hi hgap).finrank_eq.symm

/-- **`dim ℌₕⁱ = dim ℌⁱ`**: the discrete harmonic forms have the dimension of the harmonic
forms. [AFW2010], Thm 3.4, Thm 3.5 -/
theorem finrank_harmonicW_eq {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    Module.finrank 𝕜 (S.harmonicW i) = Module.finrank 𝕜 (H.harmonic i) := by
  rw [← S.map_harmonic, ← (Submodule.equivMapOfInjective _ (S.V i).injective_subtype _).finrank_eq,
    ← (S.cohomologyEquivHarmonic i).finrank_eq, P.finrank_cohomology_eq hi hgap,
    (H.cohomologyEquivHarmonic hi).finrank_eq]

/-- A cochain projection onto a finite-dimensional subcomplex with the strict gap forces `ℌⁱ` to be
finite-dimensional. -/
theorem finiteDimensional_harmonic {i : ι} (hi : H.ClosedRangeAt i)
    (hgap : ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - P.π i q‖ < ‖q‖) :
    FiniteDimensional 𝕜 (H.harmonic i) :=
  have := (P.cohomologyEquiv hi hgap).symm.finiteDimensional
  (H.cohomologyEquivHarmonic hi).finiteDimensional

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- A harmonic gap below `1` is the strict gap. -/
theorem norm_sub_π_lt_of_harmonicGap_lt_one {i : ι} {μ : ℝ}
    (hμ : ∀ q ∈ H.harmonic i, ‖q - P.π i q‖ ≤ μ * ‖q‖) (h : P.harmonicGap i < 1) {q : W i}
    (hq : q ∈ H.harmonic i) (hq0 : q ≠ 0) : ‖q - P.π i q‖ < ‖q‖ :=
  (P.norm_sub_le_harmonicGap_mul hμ hq).trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.2 hq0) h)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- A cochain projection bounded by `C` in `W` moves harmonic forms by at most `(1 + C) ‖q‖`. -/
theorem norm_sub_π_le_of_norm_le {i : ι} {C : ℝ} (hπ : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (q : W i) :
    ‖q - P.π i q‖ ≤ (1 + C) * ‖q‖ :=
  (norm_sub_le _ _).trans (by linarith [hπ q])

end Single

/-! ### The harmonic gap of uniformly bounded cochain projections -/

section HarmonicGap

variable {S : H.Subcomplex}

/-- `‖x - π x‖ ≤ (1 + C) dist(x, Vₕ)` for a cochain projection bounded by `C` (in `W`). -/
theorem norm_sub_π_le_infDist (P : S.CochainProjection) {i : ι} {C : ℝ} (hC : 0 ≤ C)
    (hπ : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (x : W i) :
    ‖x - P.π i x‖ ≤ (1 + C) * Metric.infDist x (S.V i : Set (W i)) := by
  have key : ∀ v ∈ S.V i, ‖x - P.π i x‖ ≤ (1 + C) * dist x v := by
    intro v hv
    have e : x - P.π i x = (x - v) - P.π i (x - v) := by
      rw [_root_.map_sub, P.proj i v hv]; abel
    rw [e, dist_eq_norm]
    calc ‖(x - v) - P.π i (x - v)‖ ≤ ‖x - v‖ + ‖P.π i (x - v)‖ := norm_sub_le _ _
      _ ≤ ‖x - v‖ + C * ‖x - v‖ := by gcongr; exact hπ _
      _ = (1 + C) * ‖x - v‖ := by ring
  have hne : (S.V i : Set (W i)).Nonempty := ⟨0, (S.V i).zero_mem⟩
  have h1 : 0 < 1 + C := by linarith
  have h2 : ‖x - P.π i x‖ / (1 + C) ≤ Metric.infDist x (S.V i : Set (W i)) := by
    refine (Metric.le_infDist hne).2 fun v hv => ?_
    rw [div_le_iff₀' h1]
    exact key v hv
  rwa [div_le_iff₀' h1] at h2

/-- `x ↦ ‖x - π x‖` is `(1 + C)`-Lipschitz for a cochain projection bounded by `C` (in `W`). -/
theorem norm_sub_π_le_add (P : S.CochainProjection) {i : ι} {C : ℝ}
    (hπ : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (x y : W i) :
    ‖x - P.π i x‖ ≤ ‖y - P.π i y‖ + (1 + C) * dist x y := by
  have e : x - P.π i x = (y - P.π i y) + ((x - y) - P.π i (x - y)) := by
    rw [_root_.map_sub]; abel
  rw [e, dist_eq_norm]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  refine (norm_sub_le _ _).trans ?_
  have := hπ (x - y)
  linarith

/-- **The harmonic gap tends to zero as soon as `πₕ q → q` on `ℌʲ`**, for a finite-dimensional
harmonic space `ℌʲ`: in a basis `(bₖ)` of `ℌʲ`, `μₕ ≤ Σₖ ‖cₖ‖ ‖bₖ - πₕ bₖ‖`, `cₖ` the
coordinate functionals. -/
theorem tendsto_harmonicGap_of_tendsto {κ : Type*} {l : Filter κ} {S : κ → H.Subcomplex}
    (P : ∀ h, (S h).CochainProjection) {j : ι} [FiniteDimensional 𝕜 (H.harmonic j)]
    (hconv : ∀ q ∈ H.harmonic j, Tendsto (fun h => ‖q - (P h).π j q‖) l (𝓝 0)) :
    Tendsto (fun h => (P h).harmonicGap j) l (𝓝 0) := by
  classical
  -- a basis of `ℌʲ` and the (continuous) coordinate functionals
  set b := Module.finBasis 𝕜 (H.harmonic j)
  set m := Module.finrank 𝕜 (H.harmonic j)
  set coord : Fin m → H.harmonic j →L[𝕜] 𝕜 := fun k =>
    LinearMap.toContinuousLinearMap (b.coord k)
  set e : κ → Fin m → ℝ := fun h k =>
    ‖((b k : H.harmonic j) : W j) - (P h).π j ((b k : H.harmonic j) : W j)‖
  set g : κ → ℝ := fun h => ∑ k, ‖coord k‖ * e h k
  have hg : Tendsto g l (𝓝 0) := by
    have : Tendsto g l (𝓝 (∑ k : Fin m, ‖coord k‖ * 0)) :=
      tendsto_finsetSum _ fun k _ => (hconv _ (b k).2).const_mul ‖coord k‖
    simpa using this
  have hle : ∀ h, (P h).harmonicGap j ≤ g h := by
    intro h
    have hg0 : 0 ≤ g h := Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    refine (P h).harmonicGap_le hg0 fun q hq => ?_
    set q' : H.harmonic j := ⟨q, hq⟩
    have hrepr : q = ∑ k, (b.repr q' k) • ((b k : H.harmonic j) : W j) := by
      have := congrArg Subtype.val (b.sum_repr q')
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hcoord : ∀ k, ‖b.repr q' k‖ ≤ ‖coord k‖ * ‖q‖ := fun k =>
      (coord k).le_opNorm q'
    calc ‖q - (P h).π j q‖
        = ‖∑ k, (b.repr q' k) • (((b k : H.harmonic j) : W j) -
            (P h).π j ((b k : H.harmonic j) : W j))‖ := by
          conv_lhs => rw [hrepr]
          rw [map_sum]
          simp only [_root_.map_smul, smul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ k, ‖b.repr q' k‖ * e h k := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_smul]
      _ ≤ ∑ k, (‖coord k‖ * ‖q‖) * e h k :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hcoord k) (norm_nonneg _)
      _ = g h * ‖q‖ := by
          simp only [g, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  exact squeeze_zero (fun h => (P h).harmonicGap_nonneg j) hle hg

/-- **The harmonic gap tends to zero** (cf. [AFW2010], Thm 3.5 and §3.4): for a family of
subcomplexes `Vₕ` with cochain projections uniformly bounded in `W` by `C`, approximating every
harmonic form (`dist(q, Vₕ) → 0`), and a finite-dimensional harmonic space `ℌʲ`,
`μₕ = sup_{q ∈ ℌ, ‖q‖ ≤ 1} ‖q - πₕ q‖ → 0` (`tendsto_harmonicGap_of_tendsto`, with
`‖q - πₕ q‖ ≤ (1 + C) dist(q, Vₕ)`). -/
theorem tendsto_harmonicGap {κ : Type*} {l : Filter κ} {S : κ → H.Subcomplex}
    (P : ∀ h, (S h).CochainProjection) {j : ι} [FiniteDimensional 𝕜 (H.harmonic j)] {C : ℝ}
    (hC : 0 ≤ C) (hπ : ∀ h x, ‖(P h).π j x‖ ≤ C * ‖x‖)
    (happrox : ∀ q ∈ H.harmonic j,
      Tendsto (fun h => Metric.infDist q ((S h).V j : Set (W j))) l (𝓝 0)) :
    Tendsto (fun h => (P h).harmonicGap j) l (𝓝 0) :=
  tendsto_harmonicGap_of_tendsto P fun q hq => by
    have h0 := (happrox q hq).const_mul (1 + C)
    rw [mul_zero] at h0
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun h => (P h).norm_sub_π_le_infDist hC (hπ h) q) h0

end HarmonicGap

/-! ### Families of subcomplexes with vanishing harmonic gap -/

section Family

variable {κ : Type*} {l : Filter κ} {S : κ → H.Subcomplex} [∀ h i, FiniteDimensional 𝕜 ((S h).V i)]
  (P : ∀ h, (S h).CochainProjection) {i : ι} {C : ℝ} (hπ : ∀ h x, ‖(P h).π i x‖ ≤ C * ‖x‖)
  (hgap : Tendsto (fun h => (P h).harmonicGap i) l (𝓝 0))
include hπ hgap

omit [∀ h i, FiniteDimensional 𝕜 ((S h).V i)] in
/-- Eventually along `l`, the strict gap holds. -/
theorem eventually_norm_sub_π_lt :
    ∀ᶠ h in l, ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - (P h).π i q‖ < ‖q‖ :=
  (hgap.eventually (gt_mem_nhds one_pos)).mono fun h h1 _ hq hq0 =>
    (P h).norm_sub_π_lt_of_harmonicGap_lt_one (fun q _ => (P h).norm_sub_π_le_of_norm_le (hπ h) q)
      h1 hq hq0

/-- **The discrete cohomology is eventually the cohomology**: for `W`-bounded cochain projections
whose harmonic gap tends to zero along `l` (`tendsto_harmonicGap`), and `H` with closed range at
`i`, `dim Hⁱ(Vₕ) = dim Hⁱ(H)` eventually. [AFW2010], Thm 3.4 and the remark after it -/
theorem eventually_finrank_cohomology_eq (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in l, Module.finrank 𝕜 ((S h).toHilbertComplex.cohomology i) =
      Module.finrank 𝕜 (H.cohomology i) :=
  (eventually_norm_sub_π_lt P hπ hgap).mono fun h hh => (P h).finrank_cohomology_eq hi hh

/-- **`dim ℌₕⁱ = dim ℌⁱ` eventually.** [AFW2010], Thm 3.4, Thm 3.5 -/
theorem eventually_finrank_harmonicW_eq (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in l, Module.finrank 𝕜 ((S h).harmonicW i) = Module.finrank 𝕜 (H.harmonic i) :=
  (eventually_norm_sub_π_lt P hπ hgap).mono fun h hh => (P h).finrank_harmonicW_eq hi hh

end Family

/-! ### Uniform convergence on compact sets -/

/-- **Uniform convergence of bounded cochain projections on compact sets**: if `‖πₕ‖ ≤ C` and
`πₕ x → x` along `l` for every `x ∈ Wⁱ`, then `‖x − πₕ x‖ ≤ ε` for all `x ∈ K`, `K` compact,
eventually along `l` (`x ↦ ‖x − πₕ x‖` is `(1 + C)`-Lipschitz, `norm_sub_π_le_add`). -/
theorem eventually_forall_norm_sub_π_le {κ : Type*} {l : Filter κ} {S : κ → H.Subcomplex}
    (P : ∀ h, (S h).CochainProjection) {i : ι} {C : ℝ} (hC : 0 ≤ C)
    (hπ : ∀ h x, ‖(P h).π i x‖ ≤ C * ‖x‖)
    (hP : ∀ x, Tendsto (fun h => ‖x - (P h).π i x‖) l (𝓝 0)) {K : Set (W i)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ h in l, ∀ x ∈ K, ‖x - (P h).π i x‖ ≤ ε :=
  hK.eventually_forall_le_of_lipschitz (F := fun h x => ‖x - (P h).π i x‖)
    (by linarith : 0 ≤ 1 + C) (fun h x y => (P h).norm_sub_π_le_add (hπ h) x y) hP hε

end CochainProjection

end Subcomplex

/-! ### Conforming families -/

namespace ConformingFamily

variable {κ : Type*} (F : ConformingFamily H κ) {i : ι} [FiniteDimensional 𝕜 (H.harmonic i)]

/-- **The harmonic gap of a conforming family tends to zero** where `ℌⁱ` is finite-dimensional
(`CochainProjection.tendsto_harmonicGap`). [AFW2010], Thm 3.5 -/
theorem tendsto_harmonicGap : Tendsto (fun h => (F.π h).harmonicGap i) F.l (𝓝 0) :=
  Subcomplex.CochainProjection.tendsto_harmonicGap F.π (zero_le_one.trans F.one_le_projBound)
    (fun h => F.norm_π_le h i) fun q _ => F.approx i q

/-- For a conforming family and a finite-dimensional `ℌⁱ`, the strict gap
`‖q - πₕ q‖ < ‖q‖` on `ℌⁱ \ 0` holds eventually: the harmonic gap tends to zero
(`tendsto_harmonicGap`). [AFW2010], Thm 3.5 -/
theorem eventually_norm_sub_π_lt :
    ∀ᶠ h in F.l, ∀ q ∈ H.harmonic i, q ≠ 0 → ‖q - (F.π h).π i q‖ < ‖q‖ :=
  Subcomplex.CochainProjection.eventually_norm_sub_π_lt F.π (fun h => F.norm_π_le h i)
    F.tendsto_harmonicGap

/-- **A conforming family eventually has the cohomology of the complex**: if `H` has closed range
at `i` and `ℌⁱ` is finite-dimensional, the projections `πₕ` eventually induce isomorphisms
`Hⁱ(H) ≅ Hⁱ(Vₕ)`, `[z] ↦ [πₕ z]`. [AFW2010], Thm 3.4, Thm 3.5 -/
theorem eventually_bijective_cohomologyMap (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in F.l, Function.Bijective ((F.π h).cohomologyMap i) :=
  F.eventually_norm_sub_π_lt.mono fun h hh =>
    ⟨(F.π h).cohomologyMap_injective hi hh, (F.π h).cohomologyMap_surjective i⟩

/-- **`dim Hⁱ(Vₕ) = dim Hⁱ(H)` eventually**, for every conforming family. [AFW2010], Thm 3.4 -/
theorem eventually_finrank_cohomology_eq (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in F.l, Module.finrank 𝕜 ((F.V h).toHilbertComplex.cohomology i) =
      Module.finrank 𝕜 (H.cohomology i) :=
  F.eventually_norm_sub_π_lt.mono fun h hh => (F.π h).finrank_cohomology_eq hi hh

/-- **`dim ℌₕⁱ = dim ℌⁱ` eventually**, for every conforming family. [AFW2010], Thm 3.4, Thm 3.5 -/
theorem eventually_finrank_harmonicW_eq (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in F.l, Module.finrank 𝕜 ((F.V h).harmonicW i) = Module.finrank 𝕜 (H.harmonic i) :=
  F.eventually_norm_sub_π_lt.mono fun h hh => (F.π h).finrank_harmonicW_eq hi hh

end ConformingFamily

end Feec.HilbertComplex
