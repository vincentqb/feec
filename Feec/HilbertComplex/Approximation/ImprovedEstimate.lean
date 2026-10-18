module

public import Feec.HilbertComplex.Approximation.QuasiOptimal

/-!
# Improved error estimates for the mixed Hodge Laplacian

With a cochain projection `π` onto a finite-dimensional subcomplex `Vₕ` that is bounded in `W`
(`‖π x‖ ≤ C_W ‖x‖`), the error of the mixed method is estimated in terms of the `W`-best
approximation errors `E(w) = dist(w, Vₕ)` of the components of the solution and of the three
quantities ([AFW2010], §3.5)

* `η = max (‖(I - π) d K‖, ‖(I - π) d† K‖)` over the two neighbouring degrees (`improvedEta`),
* `δ = ‖(I - π) K‖` (`improvedDelta`),
* `μ = ‖(I - π) P_ℌ‖` (`harmonicGap`),

where `K` is the solution operator of the Hodge Laplacian (`Feec.HilbertComplex.solutionOp`).
The result is [AFW2010], Thm 3.11 ([Arnold2018], Thm 5.6), with explicit constants
(`A = 1 + C_W`):

* `‖d(σ - σₕ)‖ ≤ A E(dσ)`,
* `‖σ - σₕ‖ ≤ A² (E(σ) + η E(dσ))`,
* `‖p - pₕ‖ ≤ A (E(p) + μ E(dσ))`,
* `‖d(u - uₕ)‖ ≤ 2A (E(du) + η [E(dσ) + E(p)])`,
* `‖u - uₕ‖ ≤ 4A² (E(u) + η [E(du) + E(σ)] + (η² + δ) [E(dσ) + E(p)] + μ E(P_𝔅 u))`.

These are unconditional abstract theorems. They are proved first for any numbers `η`, `δ`, `μ`
dominating the corresponding operators (hypotheses `hη₁ … hη₄`, `hδ`, `hμ`), then for the defined
quantities, which are finite (`improvedEta_le`: `η ≤ (1 + C_W) c_P`; `improvedDelta_le`:
`δ ≤ (1 + C_W) c_P²`) as soon as `π` is `W`-bounded and Poincaré constants exist. Regularity
enters only when `η`, `δ`, `μ` are shown to be small for concrete spaces (e.g. `η = O(h)`,
`δ = O(h²)` on convex domains, by elliptic regularity); the compactness property assumed in
[AFW2010] serves only to make `η, δ, μ → 0` and is not needed here.

The norm of `(I - π) d K` on `W^{j-1}` is taken in the form `(I - π) K d` on `D(d)` relative to
the `W` norm (`etaDK`; `K d = d K`, `Feec.HilbertComplex.d_solutionOp`), and that of
`(I - π) d† K` on `W^{j+1}` in the form `(I - π) P_{𝔷ᗮ}` on `D(d)` relative to `‖d ·‖`
(`etaCycles`; `d† K d = P_{𝔷ᗮ}`). These agree with the operator norms of [AFW2010] (by density
of `D(d)` and boundedness of `K d`, resp. because `d† K g` depends only on `P_𝔅 g`; this
identification is not formalized here), and they avoid solution operators at other indices.

## Main definitions

* `ContinuousSolution`, `Subcomplex.DiscreteSolution`: the solutions of the continuous and
  discrete mixed problems, in terms of their components in `W`.
* `Subcomplex.bestApprox`: `E(w) = dist(w, Vₕ)`.
* `relNorm T L = sup_{‖L x‖ ≤ 1} ‖T x‖`, the norm of `T` relative to `L`.
* `CochainProjection.etaDK`, `etaSigma`, `etaD`, `etaCycles`, `improvedEta` (`η`) and
  `improvedDelta` (`δ`).

## Main results

* `IsMixedSolution.toContinuousSolution`, `Subcomplex.toDiscreteSolution`: the solutions of
  `Feec.HilbertComplex.existsUnique_mixed` and of the discrete complex
  (e.g. `CochainProjection.discreteMixedSolution`) as such.
* `CochainProjection.norm_d_sub_le`, `norm_sub_sigma_le`, `norm_sub_harmonic_le`,
  `norm_d_sub_u_le`, `norm_sub_u_le`: the five estimates (35)–(39) of [AFW2010], Thm 3.11;
  `norm_starProjection_boundariesW_le'`: (40).
* `CochainProjection.norm_sub_sigma_le_improvedEta`, `norm_sub_harmonic_le_harmonicGap`,
  `norm_d_sub_u_le_improvedEta`, **`norm_sub_u_le_improved`**: (36)–(39) with the defined `η`,
  `δ`, `μ`; `improvedEta_le`, `improvedDelta_le`: their finiteness.
* The intermediate lemmas of [AFW2010], Lemmas 3.12–3.16: `norm_sub_starProjection_cycles_le`
  (3.12), `norm_starProjection_boundariesW_le` (3.13), `norm_starProjection_harmonicW_le` (3.14,
  (34)), `norm_d_vh_le` (3.15), `norm_vh_le` (3.16), and the decomposition
  `norm_sub_u_le_decomp`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.5, Thm 3.11 and Lemmas 3.12–3.16
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Thm 5.6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (improved estimates by duality)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- `‖x - P_K x‖ ≤ ‖x - y‖` for `y ∈ K`. -/
theorem _root_.Submodule.norm_sub_starProjection_le_of_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] {x y : E}
    (hy : y ∈ K) : ‖x - K.starProjection x‖ ≤ ‖x - y‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm, Submodule.dist_starProjection_eq_infDist]
  exact Metric.infDist_le_dist_of_mem hy

/-! ### Relative operator norms -/

section RelNorm

variable {E F G : Type*} [AddCommGroup E] [Module 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] (T : E →ₗ[𝕜] F) (L : E →ₗ[𝕜] G)

/-- **The norm of `T` relative to `L`**, `sup_{‖L x‖ ≤ 1} ‖T x‖`: the smallest `η` with
`‖T x‖ ≤ η ‖L x‖` for all `x`, when some such `η` exists (`norm_le_relNorm_mul`, `relNorm_le`).
For `L = id` it is the operator norm of `T`. -/
def relNorm : ℝ := ⨆ x : {x : E // ‖L x‖ ≤ 1}, ‖T x‖

theorem relNorm_nonneg : 0 ≤ relNorm T L := Real.iSup_nonneg fun _ => norm_nonneg _

variable {T L}

private theorem bddAbove_relNorm {η : ℝ} (h : ∀ x, ‖T x‖ ≤ η * ‖L x‖) :
    BddAbove (Set.range fun x : {x : E // ‖L x‖ ≤ 1} => ‖T x‖) := by
  refine ⟨max η 0, ?_⟩
  rintro _ ⟨x, rfl⟩
  refine (h _).trans ?_
  rcases le_total 0 η with hη | hη
  · exact (mul_le_of_le_one_right hη x.2).trans (le_max_left _ _)
  · exact (mul_nonpos_of_nonpos_of_nonneg hη (norm_nonneg _)).trans (le_max_right _ _)

/-- `‖T x‖ ≤ relNorm T L * ‖L x‖`, provided some bound of this form holds. -/
theorem norm_le_relNorm_mul {η : ℝ} (h : ∀ x, ‖T x‖ ≤ η * ‖L x‖) (x : E) :
    ‖T x‖ ≤ relNorm T L * ‖L x‖ := by
  rcases (norm_nonneg (L x)).eq_or_lt with h0 | h0
  · have hx := h x
    rw [← h0, mul_zero] at hx ⊢
    exact hx
  · set a : 𝕜 := ((‖L x‖⁻¹ : ℝ) : 𝕜)
    have hna : ‖L (a • x)‖ = 1 := by
      rw [_root_.map_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
        inv_mul_cancel₀ h0.ne']
    have hle := le_ciSup (bddAbove_relNorm h) (⟨a • x, hna.le⟩ : {x : E // ‖L x‖ ≤ 1})
    simp only at hle
    rw [_root_.map_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm] at hle
    rw [← div_le_iff₀ h0, div_eq_inv_mul]
    exact hle

theorem relNorm_le {η : ℝ} (hη0 : 0 ≤ η) (h : ∀ x, ‖T x‖ ≤ η * ‖L x‖) : relNorm T L ≤ η :=
  Real.iSup_le (fun x => (h x).trans (mul_le_of_le_one_right hη0 x.2)) hη0

end RelNorm

variable (H : HilbertComplex 𝕜 c W)

/-- **A solution of the continuous mixed problem** at `i → j → k`, by its components in `W`:
`σ ∈ D(d)`, `u ∈ D(d)`, `p ∈ ℌʲ`, `⟪τ, σ⟫ = ⟪d τ, u⟫`,
`⟪v, d σ⟫ + ⟪d v, d u⟫ + ⟪v, p⟫ = ⟪v, f⟫` and `u ⊥ ℌʲ`. -/
structure ContinuousSolution (i j k : ι) (f : W j) where
  /-- `σ` -/
  σ : (H.d i j).domain
  /-- `u` -/
  u : (H.d j k).domain
  /-- `p` -/
  p : W j
  mem_p : p ∈ H.harmonic j
  fst : ∀ τ : (H.d i j).domain, ⟪(τ : W i), (σ : W i)⟫ = ⟪H.d i j τ, (u : W j)⟫
  snd : ∀ v : (H.d j k).domain,
    ⟪(v : W j), H.d i j σ⟫ + ⟪H.d j k v, H.d j k u⟫ + ⟪(v : W j), p⟫ = ⟪(v : W j), f⟫
  harm : ∀ q ∈ H.harmonic j, ⟪q, (u : W j)⟫ = 0

variable {H}

/-- A solution of the mixed problem gives a `ContinuousSolution`. -/
def IsMixedSolution.toContinuousSolution {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u p) : H.ContinuousSolution i j k f where
  σ := H.domainCoord i j σ
  u := H.domainCoord j k u
  p := p
  mem_p := p.2
  fst τ := by
    have e := hs.fst (H.toDomainSpace hij τ)
    rw [domainIncl_toDomainSpace, d_domainCoord_toDomainSpace, sub_eq_zero] at e
    exact e
  snd v := by
    have e := hs.snd (H.toDomainSpace hjk v)
    rw [domainIncl_toDomainSpace, d_domainCoord_toDomainSpace] at e
    exact e
  harm := hs.harm

namespace Subcomplex

variable (S : H.Subcomplex)

/-- **A solution of the discrete mixed problem** at `i → j → k` with data `f` (tested against
`Vₕʲ`, i.e. with data `P_{Vₕ} f`), by its components in `W`. -/
structure DiscreteSolution (i j k : ι) (f : W j) where
  /-- `σₕ` -/
  σ : W i
  /-- `uₕ` -/
  u : W j
  /-- `pₕ` -/
  p : W j
  mem_σ : σ ∈ S.V i
  mem_u : u ∈ S.V j
  mem_p : p ∈ S.harmonicW j
  fst : ∀ τ (hτ : τ ∈ S.V i), ⟪τ, σ⟫ = ⟪H.d i j ⟨τ, S.le_domain i j hτ⟩, u⟫
  snd : ∀ v (hv : v ∈ S.V j), ⟪v, H.d i j ⟨σ, S.le_domain i j mem_σ⟩⟫ +
    ⟪H.d j k ⟨v, S.le_domain j k hv⟩, H.d j k ⟨u, S.le_domain j k mem_u⟩⟫ + ⟪v, p⟫ = ⟪v, f⟫
  harm : ∀ q ∈ S.harmonicW j, ⟪q, u⟫ = 0

variable {S} [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- A solution of the mixed problem of the discrete complex gives a `DiscreteSolution`. -/
def toDiscreteSolution {i j k : ι} {f : W j} {fh : S.V j}
    (hfh : ∀ v : S.V j, ⟪(v : W j), (fh : W j)⟫ = ⟪(v : W j), f⟫)
    {σh : S.toHilbertComplex.domainSpace i} {uh : S.toHilbertComplex.domainSpace j}
    {ph : S.toHilbertComplex.harmonic j}
    (hsh : S.toHilbertComplex.IsMixedSolution i j k fh σh uh ph) :
    S.DiscreteSolution i j k f where
  σ := S.toW i σh
  u := S.toW j uh
  p := ((ph : S.V j) : W j)
  mem_σ := (S.toHilbertComplex.domainIncl i σh).2
  mem_u := (S.toHilbertComplex.domainIncl j uh).2
  mem_p := S.mem_harmonic_iff.1 ph.2
  fst τ hτ := by
    have e := hsh.fst ((S.toHilbertComplex.d i (c.next i)).toGraphSpace ⟨⟨τ, hτ⟩, Submodule.mem_top⟩)
    rw [sub_eq_zero] at e
    exact e
  snd v hv := by
    have e := hsh.snd ((S.toHilbertComplex.d j (c.next j)).toGraphSpace ⟨⟨v, hv⟩, Submodule.mem_top⟩)
    exact e.trans (hfh ⟨v, hv⟩)
  harm q hq := hsh.harm ⟨q, S.harmonicW_le_V j hq⟩ (S.mem_harmonic_iff.2 hq)

/-- **The `W`-best approximation error** `E(w) = dist(w, Vₕⁱ)`. -/
def bestApprox (S : H.Subcomplex) {i : ι} (w : W i) : ℝ := Metric.infDist w (S.V i)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
theorem bestApprox_nonneg {i : ι} (w : W i) : 0 ≤ S.bestApprox w := Metric.infDist_nonneg

namespace CochainProjection

variable (P : S.CochainProjection)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- **`‖(I - π) w‖ ≤ (1 + C_W) E(w)`** for a `W`-bounded cochain projection. -/
theorem norm_sub_π_le_bestApprox {i : ι} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hπ : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖) (w : W i) :
    ‖w - P.π i w‖ ≤ (1 + Cw) * S.bestApprox w := by
  by_contra hlt
  push Not at hlt
  have hne : ((S.V i : Set (W i))).Nonempty := ⟨0, zero_mem _⟩
  have hpos : 0 < 1 + Cw := by linarith
  obtain ⟨v, hv, hd⟩ := (Metric.infDist_lt_iff hne).1
    (show Metric.infDist w (S.V i) < ‖w - P.π i w‖ / (1 + Cw) by
      rw [lt_div_iff₀ hpos]; unfold bestApprox at hlt; linarith)
  have e : w - P.π i w = (w - v) - P.π i (w - v) := by
    rw [_root_.map_sub, P.proj i v hv]; abel
  have : ‖w - P.π i w‖ ≤ (1 + Cw) * dist w v := by
    rw [e, dist_eq_norm]
    calc _ ≤ ‖w - v‖ + ‖P.π i (w - v)‖ := norm_sub_le _ _
      _ ≤ ‖w - v‖ + Cw * ‖w - v‖ := by gcongr; exact hπ _
      _ = _ := by ring
  rw [lt_div_iff₀ hpos] at hd
  linarith

end CochainProjection

end Subcomplex


/-! ### Elementary facts -/

/-- If `⟪a, b⟫ = 0` then `‖a‖ ≤ ‖a + b‖`. -/
theorem norm_le_norm_add_of_inner_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {a b : E} (h : ⟪a, b⟫ = 0) : ‖a‖ ≤ ‖a + b‖ := by
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) a b h
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b)]

/-- `⟪x, P x⟫ = ‖P x‖²`. -/
theorem inner_starProjection_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E) :
    ⟪x, K.starProjection x⟫ = ((‖K.starProjection x‖ : ℝ) : 𝕜) ^ 2 := by
  have h := Submodule.starProjection_inner_eq_zero x (K.starProjection x)
    (Submodule.starProjection_apply_mem K x)
  rw [inner_sub_left, sub_eq_zero] at h
  rw [h, inner_self_eq_norm_sq_to_K]

theorem norm_sq_le_of_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {x : E} {a : 𝕜} {M : ℝ} (h : ⟪x, x⟫ = a) (ha : ‖a‖ ≤ M * ‖x‖) (hM : 0 ≤ M) : ‖x‖ ≤ M := by
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖x‖ ^ 2 ≤ M * ‖x‖ := by
    rw [← h, norm_pow, RCLike.norm_ofReal, abs_norm] at ha; exact ha
  nlinarith [norm_nonneg x]

theorem d_sub {i j : ι} {a b : W i} (h : a - b ∈ (H.d i j).domain) (ha : a ∈ (H.d i j).domain)
    (hb : b ∈ (H.d i j).domain) :
    H.d i j ⟨a - b, h⟩ = H.d i j ⟨a, ha⟩ - H.d i j ⟨b, hb⟩ := by
  rw [← LinearPMap.map_sub]; rfl

namespace Subcomplex

variable {S : H.Subcomplex}

theorem mem_boundariesW_iff {i j : ι} (hij : c.Rel i j) {b : W j} :
    b ∈ S.boundariesW j ↔ ∃ τ, ∃ hτ : τ ∈ S.V i, b = H.d i j ⟨τ, S.le_domain i j hτ⟩ := by
  obtain rfl := c.prev_eq' hij
  constructor
  · rintro ⟨τ, rfl⟩; exact ⟨τ, τ.2, rfl⟩
  · rintro ⟨τ, hτ, rfl⟩; exact ⟨⟨τ, hτ⟩, rfl⟩

theorem d_mem_boundariesW {i j : ι} (hij : c.Rel i j) {τ : W i} (hτ : τ ∈ S.V i) :
    H.d i j ⟨τ, S.le_domain i j hτ⟩ ∈ S.boundariesW j :=
  (mem_boundariesW_iff hij).2 ⟨τ, hτ, rfl⟩

end Subcomplex

/-! ### The continuous solution -/

namespace ContinuousSolution

variable {i j k : ι} {f : W j} (X : H.ContinuousSolution i j k f)

/-- `d σ`. -/
abbrev dσ : W j := H.d i j X.σ

/-- `d u`. -/
abbrev du : W k := H.d j k X.u

theorem dσ_mem_boundaries (hij : c.Rel i j) : X.dσ ∈ H.boundaries j := by
  rw [H.boundaries_eq hij]; exact ⟨_, rfl⟩

/-- **`d σ = P_𝔅 f`.** -/
theorem dσ_eq (hij : c.Rel i j) (hj : H.ClosedRangeAt j) :
    X.dσ = (H.boundaries j).topologicalClosure.starProjection f := by
  have hBc : (H.boundaries j).topologicalClosure = H.boundaries j :=
    IsClosed.submodule_topologicalClosure_eq hj
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (by rw [hBc]; exact X.dσ_mem_boundaries hij) fun w hw => ?_
  rw [hBc, H.boundaries_eq hij] at hw
  obtain ⟨τ, rfl⟩ := hw
  have e := X.snd ⟨_, H.mapsTo i j k τ⟩
  rw [show H.d j k ⟨_, H.mapsTo i j k τ⟩ = 0 from H.d_comp_d i j k τ, inner_zero_left, add_zero,
    show ⟪(H.d i j τ : W j), X.p⟫ = 0 from Submodule.inner_right_of_mem_orthogonal
      (by rw [H.boundaries_eq hij]; exact ⟨_, rfl⟩) (H.mem_harmonic_iff.1 X.mem_p).2,
    add_zero] at e
  rw [← inner_conj_symm]
  change starRingEnd 𝕜 ⟪H.d i j τ, f - X.dσ⟫ = 0
  rw [inner_sub_right, ← e, sub_self, _root_.map_zero]

/-- **`p = P_ℌ f`.** -/
theorem p_eq (hij : c.Rel i j) : X.p = (H.harmonic j).starProjection f := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero X.mem_p fun q hq => ?_
  have hqz := H.harmonic_le_cycles j hq
  have e := X.snd ⟨q, H.domain_next_le j k (H.cycles_le_domain j hqz)⟩
  rw [H.d_eq_zero_of_mem_cycles hqz, inner_zero_left, add_zero,
    show ⟪q, X.dσ⟫ = 0 from Submodule.inner_left_of_mem_orthogonal (X.dσ_mem_boundaries hij)
      (H.mem_harmonic_iff.1 hq).2, zero_add] at e
  rw [← inner_conj_symm, inner_sub_right]
  change starRingEnd 𝕜 (⟪q, f⟫ - ⟪q, X.p⟫) = 0
  rw [← e, sub_self, _root_.map_zero]

/-- `σ ⊥ 𝔷ⁱ`. -/
theorem σ_mem_orthogonal : (X.σ : W i) ∈ (H.cycles i)ᗮ :=
  (Submodule.mem_orthogonal _ _).2 fun z hz => by
    have hzd : z ∈ (H.d i j).domain := H.domain_next_le i j (H.cycles_le_domain i hz)
    rw [X.fst ⟨z, hzd⟩, H.d_eq_zero_of_mem_cycles hz, inner_zero_left]

theorem u_mem_orthogonal : (X.u : W j) ∈ (H.harmonic j)ᗮ :=
  (Submodule.mem_orthogonal _ _).2 X.harm

end ContinuousSolution

/-! ### The discrete solution -/

namespace Subcomplex.DiscreteSolution

variable {S : H.Subcomplex} {i j k : ι} {f : W j} (Y : S.DiscreteSolution i j k f)

/-- `d σₕ`. -/
abbrev dσ : W j := H.d i j ⟨Y.σ, S.le_domain i j Y.mem_σ⟩

/-- `d uₕ`. -/
abbrev du : W k := H.d j k ⟨Y.u, S.le_domain j k Y.mem_u⟩

/-- `σₕ ⊥ 𝔷ₕⁱ`. -/
theorem σ_inner_cyclesW {z : W i} (hz : z ∈ S.cyclesW i) : ⟪z, Y.σ⟫ = 0 := by
  rw [Y.fst z (S.cyclesW_le i hz), H.d_eq_zero_of_mem_cycles (S.cyclesW_le_cycles i hz),
    inner_zero_left]

variable [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- **`d σₕ = P_{𝔅ₕ} f`.** -/
theorem dσ_eq (hij : c.Rel i j) : Y.dσ = (S.boundariesW j).starProjection f := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (S.d_mem_boundariesW hij Y.mem_σ) fun w hw => ?_
  obtain ⟨τ, hτ, rfl⟩ := (Subcomplex.mem_boundariesW_iff hij).1 hw
  have e := Y.snd _ (S.mapsTo i j τ hτ)
  rw [show H.d j k ⟨_, S.le_domain j k (S.mapsTo i j τ hτ)⟩ = 0 from
      H.d_comp_d i j k ⟨τ, S.le_domain i j hτ⟩, inner_zero_left, add_zero,
    (S.mem_harmonicW_iff.1 Y.mem_p).2.2 _ (S.d_mem_boundariesW hij hτ), add_zero] at e
  rw [← inner_conj_symm, inner_sub_right, ← e, sub_self, _root_.map_zero]

/-- **`pₕ = P_{ℌₕ} f`.** -/
theorem p_eq (hij : c.Rel i j) : Y.p = (S.harmonicW j).starProjection f := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero Y.mem_p fun q hq => ?_
  have hqV := S.harmonicW_le_V j hq
  have hqz := S.cyclesW_le_cycles j (S.harmonicW_le_cyclesW j hq)
  have e := Y.snd q hqV
  rw [H.d_eq_zero_of_mem_cycles hqz, inner_zero_left, add_zero,
    show ⟪q, Y.dσ⟫ = 0 by
      rw [← inner_conj_symm, (S.mem_harmonicW_iff.1 hq).2.2 _ (S.d_mem_boundariesW hij Y.mem_σ),
        _root_.map_zero], zero_add] at e
  rw [← inner_conj_symm, inner_sub_right, ← e, sub_self, _root_.map_zero]

end Subcomplex.DiscreteSolution

/-! ### The error equations -/

namespace Subcomplex

variable {S : H.Subcomplex} {i j k : ι} {f : W j}

/-- First error equation: `⟪τ, σ - σₕ⟫ = ⟪d τ, u - uₕ⟫` on `Vₕⁱ`. -/
theorem error_fst (X : H.ContinuousSolution i j k f) (Y : S.DiscreteSolution i j k f) {τ : W i}
    (hτ : τ ∈ S.V i) :
    ⟪τ, (X.σ : W i) - Y.σ⟫ = ⟪H.d i j ⟨τ, S.le_domain i j hτ⟩, (X.u : W j) - Y.u⟫ := by
  rw [inner_sub_right, inner_sub_right, X.fst ⟨τ, S.le_domain i j hτ⟩, Y.fst τ hτ]

/-- Second error equation: `⟪v, d(σ - σₕ)⟫ + ⟪d v, d(u - uₕ)⟫ + ⟪v, p - pₕ⟫ = 0` on `Vₕʲ`. -/
theorem error_snd (X : H.ContinuousSolution i j k f) (Y : S.DiscreteSolution i j k f) {v : W j}
    (hv : v ∈ S.V j) :
    ⟪v, X.dσ - Y.dσ⟫ + ⟪H.d j k ⟨v, S.le_domain j k hv⟩, X.du - Y.du⟫ + ⟪v, X.p - Y.p⟫ = 0 := by
  have e1 := X.snd ⟨v, S.le_domain j k hv⟩
  have e2 := Y.snd v hv
  simp only [inner_sub_right]
  linear_combination e1 - e2

/-! ### The estimates for `d σ`, `p` and `P_{ℌₕ} u` -/

namespace CochainProjection

variable [∀ i, FiniteDimensional 𝕜 (S.V i)] (P : S.CochainProjection)
  (X : H.ContinuousSolution i j k f) (Y : S.DiscreteSolution i j k f)

/-- `d σₕ = P_{𝔅ₕ} d σ`. -/
theorem dσ_eq_starProjection (hij : c.Rel i j) (hj : H.ClosedRangeAt j) :
    Y.dσ = (S.boundariesW j).starProjection X.dσ := by
  have ho : f - X.dσ ∈ (S.boundariesW j)ᗮ := by
    rw [X.dσ_eq hij hj]
    exact Submodule.orthogonal_le ((S.boundariesW_le j).trans (H.boundaries j).le_topologicalClosure)
      (Submodule.sub_starProjection_mem_orthogonal f)
  have h0 := (Submodule.starProjection_apply_eq_zero_iff _).2 ho
  rw [_root_.map_sub, sub_eq_zero] at h0
  rw [Y.dσ_eq hij, h0]

/-- **[AFW2010], (35)**: `‖d(σ - σₕ)‖ ≤ (1 + C_W) E(d σ)`. -/
theorem norm_d_sub_le (hij : c.Rel i j) (hj : H.ClosedRangeAt j) {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) :
    ‖X.dσ - Y.dσ‖ ≤ (1 + Cw) * S.bestApprox X.dσ := by
  rw [dσ_eq_starProjection X Y hij hj]
  exact (Submodule.norm_sub_starProjection_le_of_mem _
    (P.mem_boundariesW (X.dσ_mem_boundaries hij))).trans (P.norm_sub_π_le_bestApprox hCw hπj _)

/-- **The discrete harmonic part of `x ⊥ ℌ`**: `‖P_{ℌₕ} x‖ ≤ μ (1 + C_W) E(P_𝔅 x)`
([AFW2010], (34)). -/
theorem norm_starProjection_harmonicW_le (hj : H.ClosedRangeAt j) {Cw μ : ℝ} (hCw : 0 ≤ Cw)
    (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hμ0 : 0 ≤ μ)
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖) {x : W j} (hx : x ∈ (H.harmonic j)ᗮ) :
    ‖(S.harmonicW j).starProjection x‖ ≤
      μ * ((1 + Cw) * S.bestApprox ((H.boundaries j).topologicalClosure.starProjection x)) := by
  set q := (S.harmonicW j).starProjection x
  have hq : q ∈ S.harmonicW j := Submodule.starProjection_apply_mem _ _
  have h1 := P.norm_inner_le_of_orthogonal_harmonic hj hq hx
  have h2 := P.norm_sub_starProjection_harmonic_le_mul hj hμ0 hμ hq
  have h3 := P.norm_sub_π_le_bestApprox hCw hπj
    ((H.boundaries j).topologicalClosure.starProjection x)
  have e : ‖⟪q, x⟫‖ = ‖q‖ ^ 2 := by
    rw [← inner_conj_symm, inner_starProjection_self, RCLike.norm_conj, norm_pow,
      RCLike.norm_ofReal, abs_norm]
  have hE := S.bestApprox_nonneg ((H.boundaries j).topologicalClosure.starProjection x)
  have hq0 := norm_nonneg q
  have : ‖q‖ ^ 2 ≤ ‖q‖ * (μ * ((1 + Cw) * S.bestApprox
      ((H.boundaries j).topologicalClosure.starProjection x))) := by
    rw [← e]
    refine h1.trans ?_
    calc _ ≤ (μ * ‖q‖) * ((1 + Cw) * S.bestApprox
          ((H.boundaries j).topologicalClosure.starProjection x)) :=
        mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  nlinarith [mul_nonneg hμ0 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + Cw) hE)]

/-- **[AFW2010], (37)**: `‖p - pₕ‖ ≤ (1 + C_W) (E(p) + μ E(d σ))`. -/
theorem norm_sub_harmonic_le (hij : c.Rel i j) (hj : H.ClosedRangeAt j) {Cw μ : ℝ}
    (hCw : 0 ≤ Cw) (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hμ0 : 0 ≤ μ)
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖) :
    ‖X.p - Y.p‖ ≤ (1 + Cw) * (S.bestApprox X.p + μ * S.bestApprox X.dσ) := by
  have hBc : (H.boundaries j).topologicalClosure = H.boundaries j :=
    IsClosed.submodule_topologicalClosure_eq hj
  have hdB := X.dσ_mem_boundaries hij
  -- `f - dσ - p ⊥ 𝔷`
  have hr : f - X.dσ - X.p ∈ (H.cycles j)ᗮ := by
    refine H.mem_orthogonal_cycles_of hj ((Submodule.mem_orthogonal _ _).2 fun b hb => ?_)
      ((Submodule.mem_orthogonal _ _).2 fun q hq => ?_)
    · have h1 : ⟪b, f - X.dσ⟫ = 0 := by
        rw [X.dσ_eq hij hj]
        exact Submodule.inner_right_of_mem_orthogonal ((H.boundaries j).le_topologicalClosure hb)
          (Submodule.sub_starProjection_mem_orthogonal f)
      rw [inner_sub_right, h1, Submodule.inner_right_of_mem_orthogonal hb
        (H.mem_harmonic_iff.1 X.mem_p).2, sub_zero]
    · have h1 : ⟪q, f - X.p⟫ = 0 := by
        rw [X.p_eq hij]
        exact Submodule.inner_right_of_mem_orthogonal hq
          (Submodule.sub_starProjection_mem_orthogonal f)
      rw [sub_sub, add_comm, ← sub_sub, inner_sub_right, h1,
        Submodule.inner_left_of_mem_orthogonal hdB (H.mem_harmonic_iff.1 hq).2, sub_zero]
  have hr0 : (S.harmonicW j).starProjection (f - X.dσ - X.p) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2 (Submodule.orthogonal_le
      ((S.harmonicW_le_cyclesW j).trans (S.cyclesW_le_cycles j)) hr)
  have hYp : Y.p = (S.harmonicW j).starProjection X.dσ + (S.harmonicW j).starProjection X.p := by
    have hf : (S.harmonicW j).starProjection f =
        (S.harmonicW j).starProjection ((f - X.dσ - X.p) + X.dσ + X.p) := by
      congr 1; abel
    rw [Y.p_eq hij, hf, _root_.map_add, _root_.map_add, hr0, zero_add]
  have e : X.p - Y.p = (X.p - (S.harmonicW j).starProjection X.p) -
      (S.harmonicW j).starProjection X.dσ := by rw [hYp]; abel
  rw [e]
  have h1 := (P.norm_sub_starProjection_harmonicW_le X.mem_p).trans
    (P.norm_sub_π_le_bestApprox hCw hπj X.p)
  have h2 := P.norm_starProjection_harmonicW_le hj hCw hπj hμ0 hμ
    (H.mem_orthogonal_harmonic_of_mem_boundaries hdB)
  have hPd : (H.boundaries j).topologicalClosure.starProjection X.dσ = X.dσ :=
    Submodule.starProjection_eq_self_iff.2 (by rw [hBc]; exact hdB)
  rw [hPd] at h2
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-! ### The estimates for `σ` and `P_{𝔅ₕ} u` -/

/-- `d(σ - σₕ) ⊥ 𝔅ₕ`. -/
theorem inner_boundariesW_d_sub (hij : c.Rel i j) (hj : H.ClosedRangeAt j) {b : W j}
    (hb : b ∈ S.boundariesW j) : ⟪b, X.dσ - Y.dσ⟫ = 0 := by
  rw [dσ_eq_starProjection X Y hij hj, ← inner_conj_symm,
    Submodule.starProjection_inner_eq_zero _ _ hb, _root_.map_zero]

/-- For `y ∈ 𝔅ʲ`: `|⟪y, d(σ - σₕ)⟫| ≤ ‖(I - π) y‖ ‖d(σ - σₕ)‖`. -/
theorem norm_inner_d_sub_le (hij : c.Rel i j) (hj : H.ClosedRangeAt j) {y : W j}
    (hy : y ∈ H.boundaries j) :
    ‖⟪y, X.dσ - Y.dσ⟫‖ ≤ ‖y - P.π j y‖ * ‖X.dσ - Y.dσ‖ := by
  have e : ⟪y, X.dσ - Y.dσ⟫ = ⟪y - (S.boundariesW j).starProjection y, X.dσ - Y.dσ⟫ := by
    rw [inner_sub_left, inner_boundariesW_d_sub X Y hij hj (Submodule.starProjection_apply_mem _ _),
      sub_zero]
  rw [e]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (Submodule.norm_sub_starProjection_le_of_mem _ (P.mem_boundariesW hy)) (norm_nonneg _))

/-- **[AFW2010], (36)**: `‖σ - σₕ‖ ≤ (1 + C_W)² (E(σ) + η E(d σ))`, with `η` bounding
`(I - π) d K = (I - π) K d` on `Wⁱ`. -/
theorem norm_sub_sigma_le (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j)
    (hk : H.ClosedRangeAt k) {Cw η : ℝ} (hCw : 0 ≤ Cw) (hπi : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖)
    (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hη0 : 0 ≤ η)
    (hη₁ : ∀ τ : (H.d i j).domain, ‖H.solutionOp hij hjk hj hk (H.d i j τ) -
      P.π j (H.solutionOp hij hjk hj hk (H.d i j τ))‖ ≤ η * ‖(τ : W i)‖) :
    ‖(X.σ : W i) - Y.σ‖ ≤ (1 + Cw) ^ 2 * (S.bestApprox (X.σ : W i) + η * S.bestApprox X.dσ) := by
  set Z := H.cycles i
  have hPZ : Z.starProjection Y.σ ∈ (H.d i j).domain :=
    H.domain_next_le i j (H.cycles_le_domain i (Submodule.starProjection_apply_mem _ _))
  have hYD : Y.σ ∈ (H.d i j).domain := S.le_domain i j Y.mem_σ
  set σ₂ := Y.σ - Z.starProjection Y.σ
  have h2D : σ₂ ∈ (H.d i j).domain := sub_mem hYD hPZ
  have hd2 : H.d i j ⟨σ₂, h2D⟩ = Y.dσ := by
    rw [d_sub h2D hYD hPZ, H.d_eq_zero_of_mem_cycles (Submodule.starProjection_apply_mem _ _),
      sub_zero]
  have h1D : (X.σ : W i) - σ₂ ∈ (H.d i j).domain := sub_mem X.σ.2 h2D
  have h1o : (X.σ : W i) - σ₂ ∈ Zᗮ :=
    sub_mem X.σ_mem_orthogonal (Submodule.sub_starProjection_mem_orthogonal _)
  have hd1 : H.d i j ⟨(X.σ : W i) - σ₂, h1D⟩ = X.dσ - Y.dσ := by
    rw [d_sub h1D X.σ.2 h2D, hd2]
  -- the test function `τ = π σ₂ - σₕ` has `d τ = 0`
  have hτ : P.π i σ₂ - Y.σ ∈ S.V i := sub_mem (P.mem i _) Y.mem_σ
  have hdτ : H.d i j ⟨P.π i σ₂ - Y.σ, S.le_domain i j hτ⟩ = 0 := by
    rw [d_sub (S.le_domain i j hτ) (S.le_domain i j (P.mem i _)) hYD]
    have := P.comm i j ⟨σ₂, h2D⟩
    simp only at this
    rw [this, hd2, P.proj j _ (S.mapsTo i j _ Y.mem_σ), sub_self]
  have horth : ⟪(X.σ : W i) - Y.σ, -(P.π i σ₂ - Y.σ)⟫ = 0 := by
    rw [inner_neg_right, ← inner_conj_symm, error_fst X Y hτ, hdτ, inner_zero_left,
      _root_.map_zero, neg_zero]
  have hle := norm_le_norm_add_of_inner_eq_zero horth
  rw [show (X.σ : W i) - Y.σ + -(P.π i σ₂ - Y.σ) =
      ((X.σ : W i) - P.π i X.σ) + P.π i ((X.σ : W i) - σ₂) by
        rw [map_sub (P.π i) (X.σ : W i) σ₂]; abel] at hle
  -- the bound on `σ₁ = σ - σ₂`
  set r := X.dσ - Y.dσ
  have hrB : r ∈ H.boundaries j := sub_mem (X.dσ_mem_boundaries hij)
    (S.boundariesW_le j (S.d_mem_boundariesW hij Y.mem_σ))
  have hr := P.norm_d_sub_le X Y hij hj hCw hπj
  have hσ₁ : ‖(X.σ : W i) - σ₂‖ ≤ η * ((1 + Cw) * S.bestApprox X.dσ) := by
    have e := H.norm_sq_eq_re_inner_solutionOp_d hij hjk hj hk (φ := ⟨_, h1D⟩) h1o
    simp only at e
    rw [hd1] at e
    have hK := P.norm_inner_d_sub_le X Y hij hj (H.solutionOp_mem_boundaries hij hjk hj hk hrB)
    have hK2 := hη₁ ⟨_, h1D⟩
    simp only [hd1] at hK2
    have h3 : ‖(X.σ : W i) - σ₂‖ ^ 2 ≤ ‖(X.σ : W i) - σ₂‖ *
        (η * ((1 + Cw) * S.bestApprox X.dσ)) := by
      rw [e]
      refine (RCLike.re_le_norm _).trans (hK.trans ?_)
      calc _ ≤ (η * ‖(X.σ : W i) - σ₂‖) * ((1 + Cw) * S.bestApprox X.dσ) :=
            mul_le_mul hK2 hr (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have := S.bestApprox_nonneg X.dσ
    nlinarith [norm_nonneg ((X.σ : W i) - σ₂), mul_nonneg hη0 (mul_nonneg
      (by linarith : (0:ℝ) ≤ 1 + Cw) this)]
  have hE1 := P.norm_sub_π_le_bestApprox hCw hπi (X.σ : W i)
  have hE0 := S.bestApprox_nonneg (X.σ : W i)
  have hE0' := S.bestApprox_nonneg X.dσ
  calc ‖(X.σ : W i) - Y.σ‖ ≤ ‖(X.σ : W i) - P.π i X.σ‖ + ‖P.π i ((X.σ : W i) - σ₂)‖ :=
        hle.trans (norm_add_le _ _)
    _ ≤ (1 + Cw) * S.bestApprox (X.σ : W i) + Cw * (η * ((1 + Cw) * S.bestApprox X.dσ)) :=
        add_le_add hE1 ((hπi _).trans (mul_le_mul_of_nonneg_left hσ₁ hCw))
    _ ≤ _ := by nlinarith [mul_nonneg hη0 hE0', mul_nonneg hCw hE0, mul_nonneg hCw (mul_nonneg hη0 hE0'),
        mul_nonneg (mul_nonneg hCw hCw) hE0]

/-- **[AFW2010], (40)** (first form): `‖P_{𝔅ₕ}(u - uₕ)‖ ≤ η ‖σ - σₕ‖ + (1 + C_W) δ E(d σ)`,
with `η` bounding `(I - π) d† K` and `δ` bounding `(I - π) K` on `Wʲ`. -/
theorem norm_starProjection_boundariesW_le (hij : c.Rel i j) (hjk : c.Rel j k)
    (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) {Cw η δ : ℝ} (hCw : 0 ≤ Cw)
    (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hη₂ : ∀ g : W j, ‖H.solutionSigma hij hjk hj hk g -
      P.π i (H.solutionSigma hij hjk hj hk g)‖ ≤ η * ‖g‖)
    (hδ : ∀ g : W j, ‖H.solutionOp hij hjk hj hk g - P.π j (H.solutionOp hij hjk hj hk g)‖ ≤
      δ * ‖g‖) :
    ‖(S.boundariesW j).starProjection ((X.u : W j) - Y.u)‖ ≤
      η * ‖(X.σ : W i) - Y.σ‖ + (1 + Cw) * δ * S.bestApprox X.dσ := by
  have hBc : (H.boundaries j).topologicalClosure = H.boundaries j :=
    IsClosed.submodule_topologicalClosure_eq hj
  set e := (S.boundariesW j).starProjection ((X.u : W j) - Y.u)
  have heBh : e ∈ S.boundariesW j := Submodule.starProjection_apply_mem _ _
  have heB : e ∈ H.boundaries j := S.boundariesW_le j heBh
  have heV : e ∈ S.V j := S.boundariesW_le_V j heBh
  obtain ⟨ρ, hρ, hρe⟩ := (Subcomplex.mem_boundariesW_iff hij).1 heBh
  -- the discrete preimage `φₕ ⊥ 𝔷ₕ`
  set φh := ρ - (S.cyclesW i).starProjection ρ
  have hPρ : (S.cyclesW i).starProjection ρ ∈ S.cyclesW i := Submodule.starProjection_apply_mem _ _
  have hφhV : φh ∈ S.V i := sub_mem hρ (S.cyclesW_le i hPρ)
  have hdφh : H.d i j ⟨φh, S.le_domain i j hφhV⟩ = e := by
    rw [d_sub (S.le_domain i j hφhV) (S.le_domain i j hρ) (S.le_domain i j (S.cyclesW_le i hPρ)),
      H.d_eq_zero_of_mem_cycles (S.cyclesW_le_cycles i hPρ), sub_zero, hρe]
  -- the continuous preimage `φ = d† K e ⊥ 𝔷`
  set φ := H.solutionSigma hij hjk hj hk e
  have hφD : φ ∈ (H.d i j).domain := H.solutionSigma_mem_domain hij hjk hj hk e
  have hφo : φ ∈ (H.cycles i)ᗮ := H.solutionSigma_mem_orthogonal_cycles hij hjk hj hk e
  have hdφ : H.d i j ⟨φ, hφD⟩ = e := by
    have := H.d_solutionSigma hij hjk hj hk e
    rw [Submodule.starProjection_eq_self_iff.2 (by rw [hBc]; exact heB)] at this
    exact this
  -- `‖φ - φₕ‖ ≤ ‖(I - π) φ‖`
  have hz : φh - P.π i φ ∈ S.cyclesW i := by
    refine S.mem_cyclesW_iff.2 ⟨sub_mem hφhV (P.mem i _), ?_⟩
    rw [H.cycles_eq hij]
    refine mem_ker_iff.2 ⟨⟨_, S.le_domain i j (sub_mem hφhV (P.mem i _))⟩, rfl, ?_⟩
    rw [d_sub (S.le_domain i j (sub_mem hφhV (P.mem i _))) (S.le_domain i j hφhV)
      (S.le_domain i j (P.mem i _)), hdφh]
    have := P.comm i j ⟨φ, hφD⟩
    simp only at this
    rw [this, hdφ, P.proj j e heV, sub_self]
  have hperp : ⟪φ - φh, φh - P.π i φ⟫ = 0 := by
    rw [inner_sub_left, Submodule.inner_left_of_mem_orthogonal (S.cyclesW_le_cycles i hz) hφo,
      Submodule.starProjection_inner_eq_zero ρ _ hz, sub_zero]
  have hφφh : ‖φ - φh‖ ≤ η * ‖e‖ := by
    refine (norm_le_norm_add_of_inner_eq_zero hperp).trans ?_
    rw [show φ - φh + (φh - P.π i φ) = φ - P.π i φ by abel]
    exact hη₂ e
  -- `‖e‖² = ⟪φₕ, σ - σₕ⟫`
  have he2 : ⟪e, e⟫ = ⟪φh - φ, (X.σ : W i) - Y.σ⟫ + ⟪φ, (X.σ : W i) - Y.σ⟫ := by
    rw [← inner_add_left, sub_add_cancel, error_fst X Y hφhV, hdφh]
    have hx : ⟪(X.u : W j) - Y.u, e⟫ = ((‖e‖ : ℝ) : 𝕜) ^ 2 := inner_starProjection_self _ _
    rw [← inner_conj_symm e ((X.u : W j) - Y.u), hx, map_pow, RCLike.conj_ofReal,
      inner_self_eq_norm_sq_to_K]
  -- `⟪φ, σ - σₕ⟫ = ⟪K e, d(σ - σₕ)⟫`
  have hK := H.solutionOp_mem_adjoint_domain hij hjk hj hk e
  have hσD : (X.σ : W i) - Y.σ ∈ (H.d i j).domain := sub_mem X.σ.2 (S.le_domain i j Y.mem_σ)
  have hadj := adjoint_isFormalAdjoint (H.dense i j) ⟨_, hK⟩ ⟨_, hσD⟩
  rw [H.adjoint_solutionOp hij hjk hj hk e hK] at hadj
  simp only at hadj
  rw [d_sub hσD X.σ.2 (S.le_domain i j Y.mem_σ)] at hadj
  have hKe := P.norm_inner_d_sub_le X Y hij hj (H.solutionOp_mem_boundaries hij hjk hj hk heB)
  have hr := P.norm_d_sub_le X Y hij hj hCw hπj
  have hE := S.bestApprox_nonneg X.dσ
  have hsq : ‖e‖ ^ 2 ≤ ‖e‖ * (η * ‖(X.σ : W i) - Y.σ‖ + (1 + Cw) * δ * S.bestApprox X.dσ) := by
    have h1 : ‖e‖ ^ 2 = ‖⟪e, e⟫‖ := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
    rw [h1, he2, hadj]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖⟪φh - φ, (X.σ : W i) - Y.σ⟫‖ ≤ η * ‖e‖ * ‖(X.σ : W i) - Y.σ‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (by rw [← norm_neg, neg_sub]; exact hφφh) (norm_nonneg _))
    have t2 : ‖⟪H.solutionOp hij hjk hj hk e, X.dσ - Y.dσ⟫‖ ≤
        δ * ‖e‖ * ((1 + Cw) * S.bestApprox X.dσ) :=
      hKe.trans (mul_le_mul (hδ e) hr (norm_nonneg _) (by positivity))
    have := add_le_add t1 t2
    linarith
  nlinarith [norm_nonneg e, norm_nonneg ((X.σ : W i) - Y.σ), mul_nonneg hη0 (norm_nonneg
    ((X.σ : W i) - Y.σ)), mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + Cw) hδ0) hE]

/-! ### The estimates for `d u` and `u` -/

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- `‖x - P_K x‖ ≤ ‖x‖`. -/
private theorem norm_sub_starProjection_le_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E) :
    ‖x - K.starProjection x‖ ≤ ‖x‖ := by
  simpa using Submodule.norm_sub_starProjection_le_of_mem (x := x) K (zero_mem K)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- **[AFW2010], Lemma 3.12**: for `vₕ ∈ Vₕʲ ⊥ 𝔷ₕʲ` and `v = P_{𝔷ᗮ} vₕ`,
`‖vₕ - v‖ ≤ ‖(I - π) v‖`. -/
theorem norm_sub_starProjection_cycles_le {j k : ι} (hjk : c.Rel j k) {vh : W j}
    (hvh : vh ∈ S.V j) (hvo : ∀ z ∈ S.cyclesW j, ⟪z, vh⟫ = 0) :
    ‖vh - (vh - (H.cycles j).starProjection vh)‖ ≤
      ‖(vh - (H.cycles j).starProjection vh) - P.π j (vh - (H.cycles j).starProjection vh)‖ := by
  set Z := H.cycles j
  set v := vh - Z.starProjection vh
  have hPD : Z.starProjection vh ∈ (H.d j k).domain :=
    H.domain_next_le j k (H.cycles_le_domain j (Submodule.starProjection_apply_mem _ _))
  have hvhD := S.le_domain j k hvh
  have hvD : v ∈ (H.d j k).domain := sub_mem hvhD hPD
  have hdv : H.d j k ⟨v, hvD⟩ = H.d j k ⟨vh, hvhD⟩ := by
    rw [d_sub hvD hvhD hPD, H.d_eq_zero_of_mem_cycles (Submodule.starProjection_apply_mem _ _),
      sub_zero]
  have hz : P.π j v - vh ∈ S.cyclesW j := by
    refine S.mem_cyclesW_iff.2 ⟨sub_mem (P.mem j _) hvh, ?_⟩
    rw [H.cycles_eq hjk]
    refine mem_ker_iff.2 ⟨⟨_, S.le_domain j k (sub_mem (P.mem j _) hvh)⟩, rfl, ?_⟩
    rw [d_sub (S.le_domain j k (sub_mem (P.mem j _) hvh)) (S.le_domain j k (P.mem j _)) hvhD]
    have := P.comm j k ⟨v, hvD⟩
    simp only at this
    rw [this, hdv, P.proj k _ (S.mapsTo j k vh hvh), sub_self]
  have hperp : ⟪vh - v, P.π j v - vh⟫ = 0 := by
    rw [inner_sub_left, ← inner_conj_symm, hvo _ hz, _root_.map_zero, zero_sub, neg_eq_zero]
    exact Submodule.inner_left_of_mem_orthogonal (S.cyclesW_le_cycles j hz)
      (Submodule.sub_starProjection_mem_orthogonal vh)
  refine (norm_le_norm_add_of_inner_eq_zero hperp).trans ?_
  rw [show vh - v + (P.π j v - vh) = -(v - P.π j v) by abel, norm_neg]

/-- **The tested second error equation**: for `y ∈ Vₕʲ ⊥ 𝔷ₕʲ` and `w ⊥ 𝔷ʲ`,
`|⟪d y, d(u - uₕ)⟫| ≤ ‖y - w‖ (‖d(σ - σₕ)‖ + ‖p - P_{ℌₕ} p‖)`. -/
theorem norm_inner_d_sub_u_le (hij : c.Rel i j) {y w : W j} (hy : y ∈ S.V j)
    (hyo : ∀ z ∈ S.cyclesW j, ⟪z, y⟫ = 0) (hw : w ∈ (H.cycles j)ᗮ) :
    ‖⟪H.d j k ⟨y, S.le_domain j k hy⟩, X.du - Y.du⟫‖ ≤
      ‖y - w‖ * (‖X.dσ - Y.dσ‖ + ‖X.p - (S.harmonicW j).starProjection X.p‖) := by
  have e := error_snd X Y hy
  have hq : (S.harmonicW j).starProjection X.p - Y.p ∈ S.cyclesW j :=
    S.harmonicW_le_cyclesW j (sub_mem (Submodule.starProjection_apply_mem _ _) Y.mem_p)
  have hy1 : ⟪y, (S.harmonicW j).starProjection X.p - Y.p⟫ = 0 := by
    rw [← inner_conj_symm, hyo _ hq, _root_.map_zero]
  have hdz : X.dσ - Y.dσ ∈ H.cycles j := H.boundaries_le_cycles j (sub_mem
    (X.dσ_mem_boundaries hij) (S.boundariesW_le j (S.d_mem_boundariesW hij Y.mem_σ)))
  have hpz : X.p - (S.harmonicW j).starProjection X.p ∈ H.cycles j :=
    sub_mem (H.harmonic_le_cycles j X.mem_p) (S.cyclesW_le_cycles j
      (S.harmonicW_le_cyclesW j (Submodule.starProjection_apply_mem _ _)))
  have hw1 := Submodule.inner_left_of_mem_orthogonal hdz hw
  have hw2 := Submodule.inner_left_of_mem_orthogonal hpz hw
  have key : ⟪H.d j k ⟨y, S.le_domain j k hy⟩, X.du - Y.du⟫ =
      -⟪y - w, (X.dσ - Y.dσ) + (X.p - (S.harmonicW j).starProjection X.p)⟫ := by
    have hsplit : X.p - Y.p = (X.p - (S.harmonicW j).starProjection X.p) +
        ((S.harmonicW j).starProjection X.p - Y.p) := by abel
    rw [hsplit, inner_add_right, hy1, add_zero] at e
    rw [inner_sub_left, inner_add_right, inner_add_right, hw1, hw2]
    linear_combination e
  rw [key, norm_neg]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _)
    (norm_nonneg _))

/-- `vₕ = P_{𝔅*ₕ}(π u - uₕ)`: the part of `π u - uₕ` orthogonal to the discrete cycles. -/
def vh : W j := (P.π j X.u - Y.u) - (S.cyclesW j).starProjection (P.π j X.u - Y.u)

theorem vh_mem : P.vh X Y ∈ S.V j :=
  sub_mem (sub_mem (P.mem j _) Y.mem_u)
    (S.cyclesW_le j (Submodule.starProjection_apply_mem _ _))

theorem vh_orthogonal : ∀ z ∈ S.cyclesW j, ⟪z, P.vh X Y⟫ = 0 := fun z hz => by
  rw [← inner_conj_symm, vh, Submodule.starProjection_inner_eq_zero _ _ hz, _root_.map_zero]

theorem d_vh : H.d j k ⟨P.vh X Y, S.le_domain j k (P.vh_mem X Y)⟩ = P.π k X.du - Y.du := by
  have h1 : P.π j X.u - Y.u ∈ S.V j := sub_mem (P.mem j _) Y.mem_u
  have h2 := S.cyclesW_le j (Submodule.starProjection_apply_mem (S.cyclesW j)
    (P.π j X.u - Y.u))
  rw [show H.d j k ⟨P.vh X Y, S.le_domain j k (P.vh_mem X Y)⟩ =
      H.d j k ⟨P.π j X.u - Y.u, S.le_domain j k h1⟩ -
        H.d j k ⟨_, S.le_domain j k h2⟩ from d_sub _ _ _,
    H.d_eq_zero_of_mem_cycles (S.cyclesW_le_cycles j (Submodule.starProjection_apply_mem _ _)),
    sub_zero, d_sub (S.le_domain j k h1) (S.le_domain j k (P.mem j _)) (S.le_domain j k Y.mem_u)]
  congr 1
  exact P.comm j k X.u

/-- `‖d(π u - uₕ)‖ ≤ (1 + C_W) (E(d u) + η [E(d σ) + E(p)])` (proof of [AFW2010], Lemma 3.15). -/
theorem norm_d_vh_le (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j) {Cw η : ℝ}
    (hCw : 0 ≤ Cw) (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hπk : ∀ x, ‖P.π k x‖ ≤ Cw * ‖x‖)
    (hη0 : 0 ≤ η)
    (hη₄ : ∀ x : (H.d j k).domain, ‖((x : W j) - (H.cycles j).starProjection x) -
      P.π j ((x : W j) - (H.cycles j).starProjection x)‖ ≤ η * ‖H.d j k x‖) :
    ‖P.π k X.du - Y.du‖ ≤
      (1 + Cw) * (S.bestApprox X.du + η * (S.bestApprox X.dσ + S.bestApprox X.p)) := by
  have hA : ‖X.p - (S.harmonicW j).starProjection X.p‖ ≤ (1 + Cw) * S.bestApprox X.p :=
    (P.norm_sub_starProjection_harmonicW_le X.mem_p).trans (P.norm_sub_π_le_bestApprox hCw hπj _)
  have hdσ := P.norm_d_sub_le X Y hij hj hCw hπj
  have h312 := (P.norm_sub_starProjection_cycles_le hjk (P.vh_mem X Y) (P.vh_orthogonal X Y)).trans
    (hη₄ ⟨_, S.le_domain j k (P.vh_mem X Y)⟩)
  rw [P.d_vh X Y] at h312
  have hB := norm_inner_d_sub_u_le X Y hij (P.vh_mem X Y) (P.vh_orthogonal X Y)
    (Submodule.sub_starProjection_mem_orthogonal (P.vh X Y))
  rw [P.d_vh X Y] at hB
  have hdu : ‖X.du - P.π k X.du‖ ≤ (1 + Cw) * S.bestApprox X.du :=
    P.norm_sub_π_le_bestApprox hCw hπk _
  have hE1 := S.bestApprox_nonneg X.du
  have hE2 := S.bestApprox_nonneg X.dσ
  have hE3 := S.bestApprox_nonneg X.p
  refine norm_sq_le_of_inner_le (𝕜 := 𝕜) (x := P.π k X.du - Y.du)
    (a := ⟪P.π k X.du - Y.du, P.π k X.du - X.du⟫ + ⟪P.π k X.du - Y.du, X.du - Y.du⟫)
    (by rw [← inner_add_right]; congr 1; abel) ?_ (by positivity)
  refine (norm_add_le _ _).trans ?_
  have t1 : ‖⟪P.π k X.du - Y.du, P.π k X.du - X.du⟫‖ ≤
      ‖P.π k X.du - Y.du‖ * ((1 + Cw) * S.bestApprox X.du) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (by rw [norm_sub_rev]; exact hdu) (norm_nonneg _))
  have t2 : ‖⟪P.π k X.du - Y.du, X.du - Y.du⟫‖ ≤
      ‖P.π k X.du - Y.du‖ * ((1 + Cw) * (η * (S.bestApprox X.dσ + S.bestApprox X.p))) := by
    refine hB.trans ?_
    calc _ ≤ (η * ‖P.π k X.du - Y.du‖) * ((1 + Cw) * S.bestApprox X.dσ +
          (1 + Cw) * S.bestApprox X.p) :=
        mul_le_mul h312 (add_le_add hdσ hA) (by positivity) (by positivity)
      _ = _ := by ring
  nlinarith [t1, t2]

/-- **[AFW2010], (38)**: `‖d(u - uₕ)‖ ≤ 2 (1 + C_W) (E(d u) + η [E(d σ) + E(p)])`. -/
theorem norm_d_sub_u_le (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j) {Cw η : ℝ}
    (hCw : 0 ≤ Cw) (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hπk : ∀ x, ‖P.π k x‖ ≤ Cw * ‖x‖)
    (hη0 : 0 ≤ η)
    (hη₄ : ∀ x : (H.d j k).domain, ‖((x : W j) - (H.cycles j).starProjection x) -
      P.π j ((x : W j) - (H.cycles j).starProjection x)‖ ≤ η * ‖H.d j k x‖) :
    ‖X.du - Y.du‖ ≤
      2 * (1 + Cw) * (S.bestApprox X.du + η * (S.bestApprox X.dσ + S.bestApprox X.p)) := by
  have h1 := P.norm_d_vh_le X Y hij hjk hj hCw hπj hπk hη0 hη₄
  have h2 : ‖X.du - P.π k X.du‖ ≤ (1 + Cw) * S.bestApprox X.du :=
    P.norm_sub_π_le_bestApprox hCw hπk _
  have h3 : ‖X.du - Y.du‖ ≤ ‖X.du - P.π k X.du‖ + ‖P.π k X.du - Y.du‖ := by
    rw [show X.du - Y.du = (X.du - P.π k X.du) + (P.π k X.du - Y.du) by abel]
    exact norm_add_le _ _
  have := mul_nonneg hη0 (add_nonneg (S.bestApprox_nonneg X.dσ) (S.bestApprox_nonneg X.p))
  nlinarith

/-- **[AFW2010], Lemma 3.16** (the bound on `vₕ`):
`‖vₕ‖ ≤ η ‖d(π u - uₕ)‖ + (1 + C_W) E(u) + η ‖d(u - uₕ)‖ + δ (1 + C_W) [E(d σ) + E(p)]`, with `η`
bounding `(I - π) d K` on `Wʲ` and `(I - π) d† K` on `Wᵏ`, and `δ` bounding `(I - π) K`. -/
theorem norm_vh_le (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j)
    (hk : H.ClosedRangeAt k) {Cw η δ : ℝ} (hCw : 0 ≤ Cw) (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖)
    (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hη₃ : ∀ g : W j, ‖H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk g)) -
      P.π k (H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk g)))‖ ≤ η * ‖g‖)
    (hη₄ : ∀ x : (H.d j k).domain, ‖((x : W j) - (H.cycles j).starProjection x) -
      P.π j ((x : W j) - (H.cycles j).starProjection x)‖ ≤ η * ‖H.d j k x‖)
    (hδ : ∀ g : W j, ‖H.solutionOp hij hjk hj hk g - P.π j (H.solutionOp hij hjk hj hk g)‖ ≤
      δ * ‖g‖) :
    ‖P.vh X Y‖ ≤ η * ‖P.π k X.du - Y.du‖ + (1 + Cw) * S.bestApprox (X.u : W j) +
      η * ‖X.du - Y.du‖ + δ * ((1 + Cw) * (S.bestApprox X.dσ + S.bestApprox X.p)) := by
  set Z := H.cycles j
  set vh := P.vh X Y
  set v := vh - Z.starProjection vh
  have hvo : v ∈ Zᗮ := Submodule.sub_starProjection_mem_orthogonal vh
  have hvn : ‖v‖ ≤ ‖vh‖ := norm_sub_starProjection_le_self Z vh
  have h312 := (P.norm_sub_starProjection_cycles_le hjk (P.vh_mem X Y) (P.vh_orthogonal X Y)).trans
    (hη₄ ⟨_, S.le_domain j k (P.vh_mem X Y)⟩)
  rw [P.d_vh X Y] at h312
  have hA : ‖X.p - (S.harmonicW j).starProjection X.p‖ ≤ (1 + Cw) * S.bestApprox X.p :=
    (P.norm_sub_starProjection_harmonicW_le X.mem_p).trans (P.norm_sub_π_le_bestApprox hCw hπj _)
  have hdσ := P.norm_d_sub_le X Y hij hj hCw hπj
  have hX : ‖X.dσ - Y.dσ‖ + ‖X.p - (S.harmonicW j).starProjection X.p‖ ≤
      (1 + Cw) * (S.bestApprox X.dσ + S.bestApprox X.p) := by linarith
  -- `⟪vₕ, vₕ⟫ = ⟪vₕ - v, vₕ⟫ + ⟪v, π u - u⟫ + ⟪v, u - uₕ⟫`
  have hz : (P.π j X.u - Y.u) - vh ∈ Z := by
    rw [show (P.π j X.u - Y.u) - vh = (S.cyclesW j).starProjection (P.π j X.u - Y.u) by
      simp only [vh, CochainProjection.vh]; abel]
    exact S.cyclesW_le_cycles j (Submodule.starProjection_apply_mem _ _)
  have e0 : ⟪vh, vh⟫ = ⟪vh - v, vh⟫ + ⟪v, P.π j X.u - X.u⟫ + ⟪v, (X.u : W j) - Y.u⟫ := by
    have h1 := Submodule.inner_left_of_mem_orthogonal hz hvo
    rw [inner_sub_right] at h1
    rw [add_assoc, ← inner_add_right, show P.π j X.u - X.u + ((X.u : W j) - Y.u) =
      P.π j X.u - Y.u by abel, sub_eq_zero.1 h1, ← inner_add_left, sub_add_cancel]
  -- `⟪v, u - uₕ⟫ = ⟪d K v, d(u - uₕ)⟫`
  have huD : (X.u : W j) - Y.u ∈ (H.d j k).domain := sub_mem X.u.2 (S.le_domain j k Y.mem_u)
  have e1 := H.inner_eq_inner_d_solutionOp hij hjk hj hk hvo ⟨_, huD⟩
  simp only at e1
  rw [d_sub huD X.u.2 (S.le_domain j k Y.mem_u)] at e1
  set g := H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk v))
  set Kv := H.solutionOp hij hjk hj hk v
  have hKvD : Kv ∈ (H.d j k).domain := H.solutionOp_mem_domain hij hjk hj hk v
  have hKvo : Kv ∈ Z ᗮ := H.solutionOp_mem_orthogonal_cycles hij hjk hj hk hvo
  -- `π g = d (π K v) = d yt` with `yt ⊥ 𝔷ₕ`
  set t := P.π j Kv
  set yt := t - (S.cyclesW j).starProjection t
  have hPt := Submodule.starProjection_apply_mem (S.cyclesW j) t
  have hytV : yt ∈ S.V j := sub_mem (P.mem j _) (S.cyclesW_le j hPt)
  have hyto : ∀ z ∈ S.cyclesW j, ⟪z, yt⟫ = 0 := fun z hz => by
    rw [← inner_conj_symm, Submodule.starProjection_inner_eq_zero _ _ hz, _root_.map_zero]
  have hπg : P.π k g = H.d j k ⟨yt, S.le_domain j k hytV⟩ := by
    rw [d_sub (S.le_domain j k hytV) (S.le_domain j k (P.mem j _))
      (S.le_domain j k (S.cyclesW_le j hPt)),
      H.d_eq_zero_of_mem_cycles (S.cyclesW_le_cycles j hPt), sub_zero]
    exact (P.comm j k ⟨Kv, hKvD⟩).symm
  have hyt : ‖yt - Kv‖ ≤ δ * ‖v‖ := by
    have hperp : ⟪yt - Kv, t - yt⟫ = 0 := by
      rw [show t - yt = (S.cyclesW j).starProjection t by simp only [yt]; abel, inner_sub_left,
        ← inner_conj_symm, hyto _ hPt, _root_.map_zero, zero_sub, neg_eq_zero]
      exact Submodule.inner_left_of_mem_orthogonal (S.cyclesW_le_cycles j hPt) hKvo
    refine (norm_le_norm_add_of_inner_eq_zero hperp).trans ?_
    rw [show yt - Kv + (t - yt) = -(Kv - t) by abel, norm_neg]
    exact hδ v
  have hB := norm_inner_d_sub_u_le X Y hij hytV hyto hKvo
  rw [← hπg] at hB
  -- the three terms
  have t1 : ‖⟪vh - v, vh⟫‖ ≤ (η * ‖P.π k X.du - Y.du‖) * ‖vh‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h312 (norm_nonneg _))
  have hu' : ‖P.π j X.u - X.u‖ ≤ (1 + Cw) * S.bestApprox (X.u : W j) := by
    rw [norm_sub_rev]; exact P.norm_sub_π_le_bestApprox hCw hπj _
  have t2 : ‖⟪v, P.π j X.u - X.u⟫‖ ≤ ‖vh‖ * ((1 + Cw) * S.bestApprox (X.u : W j)) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hvn hu' (norm_nonneg _) (norm_nonneg _))
  have t3 : ‖⟪v, (X.u : W j) - Y.u⟫‖ ≤
      ‖vh‖ * (η * ‖X.du - Y.du‖ + δ * ((1 + Cw) * (S.bestApprox X.dσ + S.bestApprox X.p))) := by
    rw [e1, show ⟪g, X.du - Y.du⟫ = ⟪g - P.π k g, X.du - Y.du⟫ + ⟪P.π k g, X.du - Y.du⟫ by
      rw [← inner_add_left, sub_add_cancel]]
    refine (norm_add_le _ _).trans ?_
    have u1 : ‖⟪g - P.π k g, X.du - Y.du⟫‖ ≤ (η * ‖vh‖) * ‖X.du - Y.du‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ((hη₃ v).trans
        (mul_le_mul_of_nonneg_left hvn hη0)) (norm_nonneg _))
    have u2 : ‖⟪P.π k g, X.du - Y.du⟫‖ ≤ (δ * ‖vh‖) * ((1 + Cw) *
        (S.bestApprox X.dσ + S.bestApprox X.p)) :=
      hB.trans (mul_le_mul (hyt.trans (mul_le_mul_of_nonneg_left hvn hδ0)) hX (by positivity)
        (by positivity))
    nlinarith [u1, u2]
  refine norm_sq_le_of_inner_le (𝕜 := 𝕜) e0 ?_ (by
    have := S.bestApprox_nonneg (X.u : W j)
    have := S.bestApprox_nonneg X.dσ
    have := S.bestApprox_nonneg X.p
    positivity)
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  nlinarith [t1, t2, t3]

/-- `P_{𝔷ₕ} = P_{𝔅ₕ} + P_{ℌₕ}`. -/
theorem starProjection_cyclesW_eq (x : W j) :
    (S.cyclesW j).starProjection x =
      (S.boundariesW j).starProjection x + (S.harmonicW j).starProjection x := by
  have hBH : ∀ b ∈ S.boundariesW j, ∀ q ∈ S.harmonicW j, ⟪q, b⟫ = 0 := fun b hb q hq => by
    rw [← inner_conj_symm, (S.mem_harmonicW_iff.1 hq).2.2 b hb, _root_.map_zero]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rw [S.cyclesW_eq j]
    exact Submodule.add_mem_sup (Submodule.starProjection_apply_mem _ _)
      (Submodule.starProjection_apply_mem _ _)
  · rw [S.cyclesW_eq j] at hw
    obtain ⟨b, hb, q, hq, rfl⟩ := Submodule.mem_sup.1 hw
    have h1 : ⟪x - ((S.boundariesW j).starProjection x + (S.harmonicW j).starProjection x), b⟫ =
        0 := by
      rw [show x - ((S.boundariesW j).starProjection x + (S.harmonicW j).starProjection x) =
          (x - (S.boundariesW j).starProjection x) - (S.harmonicW j).starProjection x by abel,
        inner_sub_left, Submodule.starProjection_inner_eq_zero _ _ hb,
        hBH b hb _ (Submodule.starProjection_apply_mem _ _), sub_zero]
    have h2 : ⟪x - ((S.boundariesW j).starProjection x + (S.harmonicW j).starProjection x), q⟫ =
        0 := by
      rw [show x - ((S.boundariesW j).starProjection x + (S.harmonicW j).starProjection x) =
          (x - (S.harmonicW j).starProjection x) - (S.boundariesW j).starProjection x by abel,
        inner_sub_left, Submodule.starProjection_inner_eq_zero _ _ hq, ← inner_conj_symm,
        hBH _ (Submodule.starProjection_apply_mem _ _) q hq, _root_.map_zero, sub_zero]
    rw [inner_add_right, h1, h2, add_zero]

/-- The decomposition `u - uₕ = (u - π u) + P_{𝔅ₕ}(π u - uₕ) + P_{ℌₕ}(π u - uₕ) + vₕ`. -/
theorem norm_sub_u_le_decomp :
    ‖(X.u : W j) - Y.u‖ ≤ 3 * ‖(X.u : W j) - P.π j X.u‖ +
      ‖(S.boundariesW j).starProjection ((X.u : W j) - Y.u)‖ +
      ‖(S.harmonicW j).starProjection (X.u : W j)‖ + ‖P.vh X Y‖ := by
  set a := (X.u : W j) - P.π j X.u
  have hHu : (S.harmonicW j).starProjection Y.u = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2 ((Submodule.mem_orthogonal _ _).2 Y.harm)
  have hy0 : P.π j X.u - Y.u = ((X.u : W j) - Y.u) - a := by simp only [a]; abel
  have hB : (S.boundariesW j).starProjection (P.π j X.u - Y.u) =
      (S.boundariesW j).starProjection ((X.u : W j) - Y.u) - (S.boundariesW j).starProjection a := by
    rw [hy0, _root_.map_sub]
  have hH : (S.harmonicW j).starProjection (P.π j X.u - Y.u) =
      (S.harmonicW j).starProjection (X.u : W j) - (S.harmonicW j).starProjection a := by
    rw [show P.π j X.u - Y.u = ((X.u : W j) - a) - Y.u by simp only [a]; abel, _root_.map_sub,
      _root_.map_sub, hHu, sub_zero]
  have hv : P.vh X Y = (P.π j X.u - Y.u) - ((S.boundariesW j).starProjection (P.π j X.u - Y.u) +
      (S.harmonicW j).starProjection (P.π j X.u - Y.u)) := by
    rw [← starProjection_cyclesW_eq]; rfl
  have e : (X.u : W j) - Y.u = a + ((S.boundariesW j).starProjection ((X.u : W j) - Y.u) -
      (S.boundariesW j).starProjection a) + ((S.harmonicW j).starProjection (X.u : W j) -
      (S.harmonicW j).starProjection a) + P.vh X Y := by
    rw [hv, hB, hH]; simp only [a]; abel
  rw [congrArg norm e]
  have n1 := Submodule.norm_starProjection_apply_le (S.boundariesW j) a
  have n2 := Submodule.norm_starProjection_apply_le (S.harmonicW j) a
  have := norm_add_le (a + ((S.boundariesW j).starProjection ((X.u : W j) - Y.u) -
      (S.boundariesW j).starProjection a) + ((S.harmonicW j).starProjection (X.u : W j) -
      (S.harmonicW j).starProjection a)) (P.vh X Y)
  have := norm_add_le (a + ((S.boundariesW j).starProjection ((X.u : W j) - Y.u) -
      (S.boundariesW j).starProjection a)) ((S.harmonicW j).starProjection (X.u : W j) -
      (S.harmonicW j).starProjection a)
  have := norm_add_le a ((S.boundariesW j).starProjection ((X.u : W j) - Y.u) -
      (S.boundariesW j).starProjection a)
  have := norm_sub_le ((S.boundariesW j).starProjection ((X.u : W j) - Y.u))
    ((S.boundariesW j).starProjection a)
  have := norm_sub_le ((S.harmonicW j).starProjection (X.u : W j))
    ((S.harmonicW j).starProjection a)
  linarith

/-- **[AFW2010], (40)**: `‖P_{𝔅ₕ}(u - uₕ)‖ ≤ (1 + C_W)² (η E(σ) + (η² + δ) E(d σ))`. -/
theorem norm_starProjection_boundariesW_le' (hij : c.Rel i j) (hjk : c.Rel j k)
    (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) {Cw η δ : ℝ} (hCw : 0 ≤ Cw)
    (hπi : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖) (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hη0 : 0 ≤ η)
    (hδ0 : 0 ≤ δ)
    (hη₁ : ∀ τ : (H.d i j).domain, ‖H.solutionOp hij hjk hj hk (H.d i j τ) -
      P.π j (H.solutionOp hij hjk hj hk (H.d i j τ))‖ ≤ η * ‖(τ : W i)‖)
    (hη₂ : ∀ g : W j, ‖H.solutionSigma hij hjk hj hk g -
      P.π i (H.solutionSigma hij hjk hj hk g)‖ ≤ η * ‖g‖)
    (hδ : ∀ g : W j, ‖H.solutionOp hij hjk hj hk g - P.π j (H.solutionOp hij hjk hj hk g)‖ ≤
      δ * ‖g‖) :
    ‖(S.boundariesW j).starProjection ((X.u : W j) - Y.u)‖ ≤
      (1 + Cw) ^ 2 * (η * S.bestApprox (X.σ : W i) + (η ^ 2 + δ) * S.bestApprox X.dσ) := by
  have he := P.norm_starProjection_boundariesW_le X Y hij hjk hj hk hCw hπj hη0 hδ0 hη₂ hδ
  have hσ := P.norm_sub_sigma_le X Y hij hjk hj hk hCw hπi hπj hη0 hη₁
  have h1 := mul_le_mul_of_nonneg_left hσ hη0
  have hE1 := S.bestApprox_nonneg (X.σ : W i)
  have hE2 := S.bestApprox_nonneg X.dσ
  have hA : 1 ≤ 1 + Cw := by linarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + Cw) (by linarith : (0:ℝ) ≤ Cw))
    (mul_nonneg hδ0 hE2), mul_nonneg hδ0 hE2]

private theorem improved_arith {A η δ μ Eu Edu Eσ Edσ Ep Eb Err e Pu vh D1 D2 σe U : ℝ}
    (hA : 1 ≤ A) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hμ : 0 ≤ μ) (hEu : 0 ≤ Eu) (hEdu : 0 ≤ Edu)
    (hEσ : 0 ≤ Eσ) (hEdσ : 0 ≤ Edσ) (hEp : 0 ≤ Ep) (hEb : 0 ≤ Eb)
    (h0 : Err ≤ 3 * U + e + Pu + vh) (hU : U ≤ A * Eu)
    (he : e ≤ η * σe + A * δ * Edσ) (hσ : σe ≤ A ^ 2 * (Eσ + η * Edσ))
    (hP : Pu ≤ μ * (A * Eb))
    (hv : vh ≤ η * D1 + A * Eu + η * D2 + δ * (A * (Edσ + Ep)))
    (hD1 : D1 ≤ A * (Edu + η * (Edσ + Ep))) (hD2 : D2 ≤ 2 * A * (Edu + η * (Edσ + Ep))) :
    Err ≤ 4 * A ^ 2 * (Eu + η * (Edu + Eσ) + (η ^ 2 + δ) * (Edσ + Ep) + μ * Eb) := by
  have s1 := mul_le_mul_of_nonneg_left hσ hη
  have s2 := mul_le_mul_of_nonneg_left hD1 hη
  have s3 := mul_le_mul_of_nonneg_left hD2 hη
  have hA0 : 0 ≤ A := by linarith
  have hA1 : 0 ≤ A - 1 := by linarith
  have q := mul_nonneg hA0 hA1
  have m1 := mul_nonneg hη hEdu
  have m2 := mul_nonneg hη hEσ
  have m3 := mul_nonneg (mul_nonneg hη hη) hEdσ
  have m4 := mul_nonneg (mul_nonneg hη hη) hEp
  have m5 := mul_nonneg hδ hEdσ
  have m6 := mul_nonneg hδ hEp
  have m7 := mul_nonneg hμ hEb
  nlinarith [mul_nonneg q hEu, mul_nonneg q m1, mul_nonneg hA0 m1, mul_nonneg q m2,
    mul_nonneg hA0 m2, mul_nonneg q m3, mul_nonneg q m4, mul_nonneg hA0 m4, mul_nonneg q m5,
    mul_nonneg hA0 m5, mul_nonneg q m6, mul_nonneg hA0 m6, mul_nonneg q m7, mul_nonneg hA0 m7]

/-- **[AFW2010], (39)**: the improved estimate for `u`,
`‖u - uₕ‖ ≤ 4 (1 + C_W)² (E(u) + η [E(d u) + E(σ)] + (η² + δ) [E(d σ) + E(p)] + μ E(P_𝔅 u))`.
Here `η` bounds `(I - π) d K` on `Wⁱ` (as `(I - π) K d`, `hη₁`) and on `Wʲ` (`hη₃`), and
`(I - π) d† K` on `Wʲ` (`hη₂`) and on `Wᵏ` (as `(I - π) P_{𝔅*}` relative to `‖d ·‖`, `hη₄`);
`δ` bounds `(I - π) K` and `μ` bounds `(I - π)` on `ℌʲ`. -/
theorem norm_sub_u_le (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j)
    (hk : H.ClosedRangeAt k) {Cw η δ μ : ℝ} (hCw : 0 ≤ Cw) (hπi : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖)
    (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hπk : ∀ x, ‖P.π k x‖ ≤ Cw * ‖x‖) (hη0 : 0 ≤ η)
    (hδ0 : 0 ≤ δ) (hμ0 : 0 ≤ μ)
    (hη₁ : ∀ τ : (H.d i j).domain, ‖H.solutionOp hij hjk hj hk (H.d i j τ) -
      P.π j (H.solutionOp hij hjk hj hk (H.d i j τ))‖ ≤ η * ‖(τ : W i)‖)
    (hη₂ : ∀ g : W j, ‖H.solutionSigma hij hjk hj hk g -
      P.π i (H.solutionSigma hij hjk hj hk g)‖ ≤ η * ‖g‖)
    (hη₃ : ∀ g : W j, ‖H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk g)) -
      P.π k (H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk g)))‖ ≤ η * ‖g‖)
    (hη₄ : ∀ x : (H.d j k).domain, ‖((x : W j) - (H.cycles j).starProjection x) -
      P.π j ((x : W j) - (H.cycles j).starProjection x)‖ ≤ η * ‖H.d j k x‖)
    (hδ : ∀ g : W j, ‖H.solutionOp hij hjk hj hk g - P.π j (H.solutionOp hij hjk hj hk g)‖ ≤
      δ * ‖g‖)
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖) :
    ‖(X.u : W j) - Y.u‖ ≤ 4 * (1 + Cw) ^ 2 * (S.bestApprox (X.u : W j) +
      η * (S.bestApprox X.du + S.bestApprox (X.σ : W i)) +
      (η ^ 2 + δ) * (S.bestApprox X.dσ + S.bestApprox X.p) +
      μ * S.bestApprox ((H.boundaries j).topologicalClosure.starProjection (X.u : W j))) := by
  have h0 := P.norm_sub_u_le_decomp X Y
  have hU := P.norm_sub_π_le_bestApprox hCw hπj (X.u : W j)
  have he := P.norm_starProjection_boundariesW_le X Y hij hjk hj hk hCw hπj hη0 hδ0 hη₂ hδ
  have hσ := P.norm_sub_sigma_le X Y hij hjk hj hk hCw hπi hπj hη0 hη₁
  have hP := P.norm_starProjection_harmonicW_le hj hCw hπj hμ0 hμ X.u_mem_orthogonal
  have hv := P.norm_vh_le X Y hij hjk hj hk hCw hπj hη0 hδ0 hη₃ hη₄ hδ
  have hD1 := P.norm_d_vh_le X Y hij hjk hj hCw hπj hπk hη0 hη₄
  have hD2 := P.norm_d_sub_u_le X Y hij hjk hj hCw hπj hπk hη0 hη₄
  rw [mul_assoc] at hD2
  exact improved_arith (by linarith) hη0 hδ0 hμ0 (S.bestApprox_nonneg _) (S.bestApprox_nonneg _)
    (S.bestApprox_nonneg _) (S.bestApprox_nonneg _) (S.bestApprox_nonneg _)
    (S.bestApprox_nonneg _) h0 hU (by linarith) hσ hP hv hD1 (by linarith)

/-! ### The quantities `η` and `δ` as relative operator norms -/

section Quantities

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- `‖(I - π) y‖ ≤ (1 + C_W) ‖y‖`. -/
theorem norm_sub_π_le {l : ι} {Cw : ℝ} (hπ : ∀ x, ‖P.π l x‖ ≤ Cw * ‖x‖) (y : W l) :
    ‖y - P.π l y‖ ≤ (1 + Cw) * ‖y‖ := by
  have := hπ y
  calc _ ≤ ‖y‖ + ‖P.π l y‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- With `π` bounded in `W`, `‖q - π q‖ ≤ μ ‖q‖` on `ℌʲ` for `μ = harmonicGap`. -/
theorem norm_sub_π_harmonic_le_harmonicGap {Cw : ℝ} (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) {q : W j}
    (hq : q ∈ H.harmonic j) : ‖q - P.π j q‖ ≤ P.harmonicGap j * ‖q‖ :=
  P.norm_sub_le_harmonicGap_mul (fun q _ => P.norm_sub_π_le hπj q) hq

/-- `(I - π) P_{𝔷ᗮ}` on `D(d j k)`. -/
def etaCyclesOp (j k : ι) : (H.d j k).domain →ₗ[𝕜] W j :=
  (LinearMap.id - P.π j) ∘ₗ
    ((LinearMap.id - (((H.cycles j).starProjection : W j →L[𝕜] W j) : W j →ₗ[𝕜] W j)) ∘ₗ
      (H.d j k).domain.subtype)

/-- `(I - π) P_{𝔷ᗮ}` on `D(d j k)` relative to `‖d ·‖`, i.e. the norm of `(I - π) d† K` on `Wᵏ`
(`d† K d = P_{𝔷ᗮ}`). -/
def etaCycles (j k : ι) : ℝ := relNorm (P.etaCyclesOp j k) (H.d j k).toFun

variable (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k)

/-- `(I - π) K d` on `D(d i j)`. -/
def etaDKOp : (H.d i j).domain →ₗ[𝕜] W j :=
  (LinearMap.id - P.π j) ∘ₗ
    ((H.solutionOp hij hjk hj hk : W j →L[𝕜] W j) : W j →ₗ[𝕜] W j) ∘ₗ (H.d i j).toFun

/-- `(I - π) K d` on `D(d i j)` relative to `‖·‖_W`, i.e. the norm of `(I - π) d K` on `Wⁱ`
(`K d = d K`). -/
def etaDK : ℝ := relNorm (P.etaDKOp hij hjk hj hk) (H.d i j).domain.subtype

/-- `(I - π) d† K` on `Wʲ`. -/
def etaSigmaOp : W j →ₗ[𝕜] W i :=
  (LinearMap.id - P.π i) ∘ₗ ((H.solutionSigma hij hjk hj hk : W j →L[𝕜] W i) : W j →ₗ[𝕜] W i)

/-- `‖(I - π) d† K‖` on `Wʲ`. -/
def etaSigma : ℝ := relNorm (P.etaSigmaOp hij hjk hj hk) LinearMap.id

/-- `(I - π) d K` on `Wʲ`. -/
def etaDOp : W j →ₗ[𝕜] W k :=
  (LinearMap.id - P.π k) ∘ₗ
    (((H.domainIncl k).comp ((H.domainD j k).comp (H.solutionOpV hij hjk hj hk)) :
      W j →L[𝕜] W k) : W j →ₗ[𝕜] W k)

/-- `‖(I - π) d K‖` on `Wʲ`. -/
def etaD : ℝ := relNorm (P.etaDOp hij hjk hj hk) LinearMap.id

/-- **`η`** of [AFW2010], §3.5: the maximum of the four norms `etaDK`, `etaSigma`, `etaD`,
`etaCycles` of `(I - π) d K` and `(I - π) d† K` at the two neighbouring degrees. -/
def improvedEta : ℝ :=
  max (max (P.etaDK hij hjk hj hk) (P.etaSigma hij hjk hj hk))
    (max (P.etaD hij hjk hj hk) (P.etaCycles j k))

/-- `(I - π) K` on `Wʲ`. -/
def deltaOp : W j →ₗ[𝕜] W j :=
  (LinearMap.id - P.π j) ∘ₗ ((H.solutionOp hij hjk hj hk : W j →L[𝕜] W j) : W j →ₗ[𝕜] W j)

/-- **`δ = ‖(I - π) K‖`** on `Wʲ` ([AFW2010], §3.5). -/
def improvedDelta : ℝ := relNorm (P.deltaOp hij hjk hj hk) LinearMap.id

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
theorem improvedEta_nonneg : 0 ≤ P.improvedEta hij hjk hj hk :=
  (relNorm_nonneg _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
theorem improvedDelta_nonneg : 0 ≤ P.improvedDelta hij hjk hj hk := relNorm_nonneg _ _

variable {Cw cP : ℝ} (hCw : 0 ≤ Cw) (hcP : 0 ≤ cP)
  (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
  (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
private theorem bound_etaDK (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (τ : (H.d i j).domain) :
    ‖P.etaDKOp hij hjk hj hk τ‖ ≤ ((1 + Cw) * cP) * ‖(H.d i j).domain.subtype τ‖ := by
  rw [mul_assoc]
  exact (P.norm_sub_π_le hπj _).trans (mul_le_mul_of_nonneg_left
    (H.norm_solutionOp_d_le hij hjk hj hk hcP hPi hPj τ) (by linarith))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
private theorem bound_etaSigma (hπi : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖) (g : W j) :
    ‖P.etaSigmaOp hij hjk hj hk g‖ ≤ ((1 + Cw) * cP) * ‖(LinearMap.id : W j →ₗ[𝕜] W j) g‖ := by
  rw [mul_assoc]
  exact (P.norm_sub_π_le hπi _).trans (mul_le_mul_of_nonneg_left
    (H.norm_solutionSigma_le hij hjk hj hk hcP hPi hPj g) (by linarith))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
private theorem bound_etaD (hπk : ∀ x, ‖P.π k x‖ ≤ Cw * ‖x‖) (g : W j) :
    ‖P.etaDOp hij hjk hj hk g‖ ≤ ((1 + Cw) * cP) * ‖(LinearMap.id : W j →ₗ[𝕜] W j) g‖ := by
  rw [mul_assoc]
  exact (P.norm_sub_π_le hπk _).trans (mul_le_mul_of_nonneg_left
    (H.norm_d_solutionOp_le hij hjk hj hk hcP hPi hPj g) (by linarith))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hPj in
private theorem bound_etaCycles (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (x : (H.d j k).domain) :
    ‖P.etaCyclesOp j k x‖ ≤ ((1 + Cw) * cP) * ‖(H.d j k).toFun x‖ := by
  have hPz : (H.cycles j).starProjection (x : W j) ∈ (H.d j k).domain :=
    H.domain_next_le j k (H.cycles_le_domain j (Submodule.starProjection_apply_mem _ _))
  have hD : (x : W j) - (H.cycles j).starProjection x ∈ (H.d j k).domain := sub_mem x.2 hPz
  have hd : H.d j k ⟨_, hD⟩ = H.d j k x := by
    rw [d_sub hD x.2 hPz, H.d_eq_zero_of_mem_cycles (Submodule.starProjection_apply_mem _ _),
      sub_zero]
  have hP := hPj ⟨_, hD⟩ (Submodule.sub_starProjection_mem_orthogonal _)
  rw [hd] at hP
  rw [mul_assoc]
  exact (P.norm_sub_π_le hπj _).trans (mul_le_mul_of_nonneg_left hP (by linarith))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
private theorem bound_delta (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (g : W j) :
    ‖P.deltaOp hij hjk hj hk g‖ ≤ ((1 + Cw) * cP ^ 2) * ‖(LinearMap.id : W j →ₗ[𝕜] W j) g‖ := by
  rw [mul_assoc]
  exact (P.norm_sub_π_le hπj _).trans (mul_le_mul_of_nonneg_left
    (H.norm_solutionOp_le hij hjk hj hk hcP hPi hPj g) (by linarith))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
/-- **`η` is finite**: `η ≤ (1 + C_W) c_P` ([AFW2010], §3.5). -/
theorem improvedEta_le (hπi : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖) (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖)
    (hπk : ∀ x, ‖P.π k x‖ ≤ Cw * ‖x‖) : P.improvedEta hij hjk hj hk ≤ (1 + Cw) * cP := by
  have h0 : 0 ≤ (1 + Cw) * cP := by positivity
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · exact relNorm_le h0 (P.bound_etaDK hij hjk hj hk hCw hcP hPi hPj hπj)
  · exact relNorm_le h0 (P.bound_etaSigma hij hjk hj hk hCw hcP hPi hPj hπi)
  · exact relNorm_le h0 (P.bound_etaD hij hjk hj hk hCw hcP hPi hPj hπk)
  · exact relNorm_le h0 (P.bound_etaCycles hCw hPj hπj)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
/-- **`δ` is finite**: `δ ≤ (1 + C_W) c_P²`. -/
theorem improvedDelta_le (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) :
    P.improvedDelta hij hjk hj hk ≤ (1 + Cw) * cP ^ 2 :=
  relNorm_le (by positivity) (P.bound_delta hij hjk hj hk hCw hcP hPi hPj hπj)

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
theorem norm_sub_π_solutionOp_d_le (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (τ : (H.d i j).domain) :
    ‖H.solutionOp hij hjk hj hk (H.d i j τ) - P.π j (H.solutionOp hij hjk hj hk (H.d i j τ))‖ ≤
      P.improvedEta hij hjk hj hk * ‖(τ : W i)‖ :=
  (norm_le_relNorm_mul (P.bound_etaDK hij hjk hj hk hCw hcP hPi hPj hπj) τ).trans
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (norm_nonneg _))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
theorem norm_sub_π_solutionSigma_le (hπi : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖) (g : W j) :
    ‖H.solutionSigma hij hjk hj hk g - P.π i (H.solutionSigma hij hjk hj hk g)‖ ≤
      P.improvedEta hij hjk hj hk * ‖g‖ :=
  (norm_le_relNorm_mul (P.bound_etaSigma hij hjk hj hk hCw hcP hPi hPj hπi) g).trans
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (norm_nonneg _))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
theorem norm_sub_π_d_solutionOp_le (hπk : ∀ x, ‖P.π k x‖ ≤ Cw * ‖x‖) (g : W j) :
    ‖H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk g)) -
      P.π k (H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk g)))‖ ≤
      P.improvedEta hij hjk hj hk * ‖g‖ :=
  (norm_le_relNorm_mul (P.bound_etaD hij hjk hj hk hCw hcP hPi hPj hπk) g).trans
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg _))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hPj in
theorem norm_sub_π_sub_starProjection_cycles_le (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖)
    (x : (H.d j k).domain) :
    ‖((x : W j) - (H.cycles j).starProjection x) -
      P.π j ((x : W j) - (H.cycles j).starProjection x)‖ ≤
      P.improvedEta hij hjk hj hk * ‖H.d j k x‖ :=
  (norm_le_relNorm_mul (P.bound_etaCycles hCw hPj hπj) x).trans
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg _))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
include hCw hcP hPi hPj in
theorem norm_sub_π_solutionOp_le (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (g : W j) :
    ‖H.solutionOp hij hjk hj hk g - P.π j (H.solutionOp hij hjk hj hk g)‖ ≤
      P.improvedDelta hij hjk hj hk * ‖g‖ :=
  norm_le_relNorm_mul (P.bound_delta hij hjk hj hk hCw hcP hPi hPj hπj) g

/-! #### The improved estimates with `η`, `δ`, `μ` the defined quantities -/

include hCw hcP hPi hPj in
/-- **[AFW2010], Thm 3.11, (36)** with `η = improvedEta`. -/
theorem norm_sub_sigma_le_improvedEta (hπi : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖)
    (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (X : H.ContinuousSolution i j k f)
    (Y : S.DiscreteSolution i j k f) :
    ‖(X.σ : W i) - Y.σ‖ ≤ (1 + Cw) ^ 2 * (S.bestApprox (X.σ : W i) +
      P.improvedEta hij hjk hj hk * S.bestApprox X.dσ) :=
  P.norm_sub_sigma_le X Y hij hjk hj hk hCw hπi hπj (P.improvedEta_nonneg hij hjk hj hk)
    (P.norm_sub_π_solutionOp_d_le hij hjk hj hk hCw hcP hPi hPj hπj)

include hij hj in
/-- **[AFW2010], Thm 3.11, (37)** with `μ = harmonicGap`. -/
theorem norm_sub_harmonic_le_harmonicGap (hCw : 0 ≤ Cw) (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖)
    (X : H.ContinuousSolution i j k f) (Y : S.DiscreteSolution i j k f) :
    ‖X.p - Y.p‖ ≤ (1 + Cw) * (S.bestApprox X.p + P.harmonicGap j * S.bestApprox X.dσ) :=
  P.norm_sub_harmonic_le X Y hij hj hCw hπj (P.harmonicGap_nonneg j)
    (fun _ hq => P.norm_sub_π_harmonic_le_harmonicGap hπj hq)

include hCw hPj in
/-- **[AFW2010], Thm 3.11, (38)** with `η = improvedEta`. -/
theorem norm_d_sub_u_le_improvedEta (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖)
    (hπk : ∀ x, ‖P.π k x‖ ≤ Cw * ‖x‖) (X : H.ContinuousSolution i j k f)
    (Y : S.DiscreteSolution i j k f) :
    ‖X.du - Y.du‖ ≤ 2 * (1 + Cw) * (S.bestApprox X.du +
      P.improvedEta hij hjk hj hk * (S.bestApprox X.dσ + S.bestApprox X.p)) :=
  P.norm_d_sub_u_le X Y hij hjk hj hCw hπj hπk (P.improvedEta_nonneg hij hjk hj hk)
    (P.norm_sub_π_sub_starProjection_cycles_le hij hjk hj hk hCw hPj hπj)

include hCw hcP hPi hPj in
/-- **[AFW2010], Thm 3.11, (39)** with `η = improvedEta`, `δ = improvedDelta` and
`μ = harmonicGap`: all three quantities are defined (and finite, `improvedEta_le`,
`improvedDelta_le`), and the estimate needs only the `W`-bound of `π` and Poincaré constants. -/
theorem norm_sub_u_le_improved (hπi : ∀ x, ‖P.π i x‖ ≤ Cw * ‖x‖)
    (hπj : ∀ x, ‖P.π j x‖ ≤ Cw * ‖x‖) (hπk : ∀ x, ‖P.π k x‖ ≤ Cw * ‖x‖)
    (X : H.ContinuousSolution i j k f) (Y : S.DiscreteSolution i j k f) :
    ‖(X.u : W j) - Y.u‖ ≤ 4 * (1 + Cw) ^ 2 * (S.bestApprox (X.u : W j) +
      P.improvedEta hij hjk hj hk * (S.bestApprox X.du + S.bestApprox (X.σ : W i)) +
      (P.improvedEta hij hjk hj hk ^ 2 + P.improvedDelta hij hjk hj hk) *
        (S.bestApprox X.dσ + S.bestApprox X.p) +
      P.harmonicGap j *
        S.bestApprox ((H.boundaries j).topologicalClosure.starProjection (X.u : W j))) :=
  P.norm_sub_u_le X Y hij hjk hj hk hCw hπi hπj hπk (P.improvedEta_nonneg hij hjk hj hk)
    (P.improvedDelta_nonneg hij hjk hj hk) (P.harmonicGap_nonneg j)
    (P.norm_sub_π_solutionOp_d_le hij hjk hj hk hCw hcP hPi hPj hπj)
    (P.norm_sub_π_solutionSigma_le hij hjk hj hk hCw hcP hPi hPj hπi)
    (P.norm_sub_π_d_solutionOp_le hij hjk hj hk hCw hcP hPi hPj hπk)
    (P.norm_sub_π_sub_starProjection_cycles_le hij hjk hj hk hCw hPj hπj)
    (P.norm_sub_π_solutionOp_le hij hjk hj hk hCw hcP hPi hPj hπj)
    (fun _ hq => P.norm_sub_π_harmonic_le_harmonicGap hπj hq)

end Quantities

end CochainProjection

end Subcomplex

end Feec.HilbertComplex
