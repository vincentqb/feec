module

public import Feec.HilbertComplex.Hodge
public import Feec.HilbertComplex.Dirac
public import Feec.Semigroup.Spectral
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# The compactness property of a Hilbert complex

A Hilbert complex has the **compactness property at `i`** if `Vⁱ ∩ V*ᵢ = D(d i (c.next i)) ∩
D((d (c.prev i) i)†)`, with the norm `max (‖x‖, ‖d x‖, ‖d† x‖)`, embeds compactly in `Wⁱ`; that
is, its unit ball lies in a compact subset of `Wⁱ` (`HasCompactPropertyAt`).

At an index with the compactness property:

* both `𝔅ⁱ` and the next boundaries `R(d i (c.next i))` are closed, and so is `𝔅*ᵢ`
  (`HasCompactPropertyAt.closedRangeAt`, `.isClosed_range`, `.dual_closedRangeAt`);
* `ℌⁱ` and the cohomology `𝔷ⁱ / 𝔅ⁱ` are finite-dimensional, and the Hodge decomposition holds
  without closures (`HasCompactPropertyAt.closed_and_fredholm`);
* the property is symmetric under duality (`hasCompactPropertyAt_dual_iff`).

For a finite complex with the compactness property at every index, the wave operator
`d − d†` has compact resolvent (`HasCompactProperty.isCompactOperator_resolvent_wave`), so the
eigenvectors of its square are dense (`HasCompactProperty.eigenDense_wave`).

The thesis' wording "`Vᵏ ∩ V*ₖ` is a dense and compact subspace of `Wᵏ`" is read as a compact
inclusion (a compact subspace is `0`); density is never needed.

## References

* [QuennevilleBelair2015], §4.2 (compactness property; "compactness ⇒ Fredholm ⇒ closed")
* [AFW2010], §3.1.3 (compactness property); [BruningLesch1992], §2
* [Arnold2018], §4.2
-/

open scoped InnerProductSpace Topology
open LinearPMap Set Filter

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A partial map equal to `S` takes the same values on `S.domain`. -/
theorem exists_mem_apply_eq_of_eq {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] {T S : E →ₗ.[R] F} (h : T = S) (x : T.domain) :
    ∃ hx : (x : E) ∈ S.domain, S ⟨x, hx⟩ = T x := by
  subst h; exact ⟨x.2, rfl⟩

/-- **Compactness ⇒ closed range.** If the unit ball of `D(T) ∩ N(T)ᗮ` in the graph box norm
lies in a compact subset of `E`, then `R(T)` is closed. -/
theorem isClosed_range_of_subset_isCompact {T : E →ₗ.[𝕜] F} (hc : T.IsClosed)
    {K : Set E} (hK : IsCompact K)
    (hsub : ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ 1 → ‖T x‖ ≤ 1 → (x : E) ∈ K) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) := by
  by_contra hR
  rw [isClosed_range_iff_exists_norm_le hc] at hR
  push Not at hR
  have hseq : ∀ n : ℕ, ∃ v : T.domain, (v : E) ∈ T.kerᗮ ∧ ‖(v : E)‖ = 1 ∧
      ‖T v‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨u, hu, h⟩ := hR ((n : ℝ) + 1)
    have hu0 : 0 < ‖(u : E)‖ := lt_of_le_of_lt (by positivity) h
    refine ⟨((‖(u : E)‖⁻¹ : ℝ) : 𝕜) • u, Submodule.smul_mem _ _ hu, ?_, ?_⟩
    · change ‖((‖(u : E)‖⁻¹ : ℝ) : 𝕜) • (u : E)‖ = 1
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hu0)]
      exact inv_mul_cancel₀ hu0.ne'
    · rw [LinearPMap.map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hu0),
        inv_mul_le_iff₀ hu0, mul_one_div, le_div_iff₀ (by positivity)]
      linarith
  choose v hvk hv1 hvd using hseq
  have hvd' : ∀ n, ‖T (v n)‖ ≤ 1 := fun n =>
    (hvd n).trans (div_le_one_of_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      (by positivity))
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun n => (v n : E))
    (fun n => hsub (v n) (hvk n) (hv1 n).le (hvd' n))
  have hd : Tendsto (fun n => T (v (φ n))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => (hvd (φ n)).trans ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    gcongr
    exact_mod_cast hφ.id_le n
  have hgr : ((a, 0) : E × F) ∈ (T.graph : Set (E × F)) :=
    hc.mem_of_tendsto (hlim.prodMk_nhds hd)
      (Eventually.of_forall fun n => T.mem_graph (v (φ n)))
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hgr
  have hker : a ∈ T.ker := (LinearPMap.mem_ker_iff).2 ⟨y, by simpa using hy1.symm, by simpa using hy2⟩
  have hperp : a ∈ T.kerᗮ :=
    (Submodule.isClosed_orthogonal _).mem_of_tendsto hlim
      (Eventually.of_forall fun n => hvk (φ n))
  have ha : a = 0 := by
    have hmem : a ∈ T.ker ⊓ T.kerᗮ := ⟨hker, hperp⟩
    rwa [Submodule.inf_orthogonal_eq_bot] at hmem
  have hn : Tendsto (fun n => ‖(v (φ n) : E)‖) atTop (𝓝 ‖a‖) := hlim.norm
  simp only [hv1, ha, norm_zero] at hn
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hn)

end LinearPMap

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Riesz:** a closed subspace whose unit ball lies in a compact set is finite-dimensional. -/
theorem finiteDimensional_of_closedBall_subset_isCompact {S : Submodule 𝕜 E}
    (hS : _root_.IsClosed (S : Set E)) {K : Set E} (hK : IsCompact K)
    (hsub : ∀ x ∈ S, ‖x‖ ≤ 1 → x ∈ K) : FiniteDimensional 𝕜 S := by
  have hiso : Isometry (S.subtype : S → E) := isometry_subtype_coe
  have himg : (S.subtype : S → E) '' Metric.closedBall 0 1 =
      (S : Set E) ∩ Metric.closedBall 0 1 := by
    ext x
    simp only [mem_image, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using hy⟩
    · rintro ⟨hx, hx1⟩
      exact ⟨⟨x, hx⟩, by simpa using hx1, rfl⟩
  have hc : IsCompact ((S : Set E) ∩ Metric.closedBall 0 1) :=
    hK.of_isClosed_subset (hS.inter Metric.isClosed_closedBall)
      (fun x hx => hsub x hx.1 (by simpa using hx.2))
  exact FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one
    (hiso.isEmbedding.isCompact_iff.2 (himg ▸ hc))

end Submodule

namespace Feec.Operator

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] G}

/-- **Compactness of the middle space** of a pair `E --T--> F --S--> G`: the unit ball of
`D(S) ∩ D(T†)` in the norm `max (‖x‖, ‖S x‖, ‖T† x‖)` lies in a compact subset of `F`. -/
def HasCompactPair (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] G) : Prop :=
  ∃ K : Set F, IsCompact K ∧ ∀ (x : F) (hx : x ∈ S.domain) (hx' : x ∈ T†.domain),
    ‖x‖ ≤ 1 → ‖S ⟨x, hx⟩‖ ≤ 1 → ‖T† ⟨x, hx'⟩‖ ≤ 1 → x ∈ K

variable [CompleteSpace G] in
/-- Compactness of the middle space passes to the adjoint pair `G --S†--> F --T†--> E`. -/
theorem HasCompactPair.adjoint (h : HasCompactPair T S) (hS : Dense (S.domain : Set F))
    (hSc : S.IsClosed) : HasCompactPair S† T† := by
  obtain ⟨K, hK, hsub⟩ := h
  refine ⟨K, hK, fun x hx hx' h1 h2 h3 => ?_⟩
  obtain ⟨hy, ey⟩ := exists_mem_apply_eq_of_eq (adjoint_adjoint S hS hSc) ⟨x, hx'⟩
  exact hsub x hy hx h1 (by rw [ey]; exact h3) h2

variable [CompleteSpace G] in
/-- **Compactness ⇒ `R(S)` closed** for a pair with `S T = 0`. -/
theorem HasCompactPair.isClosed_range_right (h : HasCompactPair T S)
    (hT : Dense (T.domain : Set E)) (hSc : S.IsClosed)
    (hmaps : ∀ x : T.domain, T x ∈ S.domain) (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0) :
    IsClosed (LinearMap.range S.toFun : Set G) := by
  obtain ⟨K, hK, hsub⟩ := h
  refine isClosed_range_of_subset_isCompact hSc hK fun x hx h1 h2 => ?_
  obtain ⟨⟨y, hy⟩, rfl, hy0⟩ :=
    (LinearPMap.mem_ker_iff).1 (orthogonal_ker_le_ker_adjoint hT hmaps hcomp hx)
  exact hsub _ x.2 hy h1 h2 (by rw [hy0, norm_zero]; exact zero_le_one)

/-- **Compactness ⇒ `R(T)` closed** for a pair with `S T = 0` (closed range theorem). -/
theorem HasCompactPair.isClosed_range_left (h : HasCompactPair T S)
    (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) (hSc : S.IsClosed)
    (hmaps : ∀ x : T.domain, T x ∈ S.domain) (hcomp : ∀ x : T.domain, S ⟨T x, hmaps x⟩ = 0) :
    IsClosed (LinearMap.range T.toFun : Set F) := by
  obtain ⟨K, hK, hsub⟩ := h
  refine (isClosed_range_adjoint_iff _ hT hTc).1 ?_
  refine isClosed_range_of_subset_isCompact (adjoint_isClosed hT) hK fun x hx h1 h2 => ?_
  obtain ⟨⟨y, hy⟩, hyx, hy0⟩ :=
    (LinearPMap.mem_ker_iff).1 (orthogonal_ker_adjoint_le_ker hT hSc hmaps hcomp hx)
  subst hyx
  exact hsub _ hy x.2 h1 (by rw [hy0, norm_zero]; exact zero_le_one) h2

omit [CompleteSpace F] in
/-- **Compactness ⇒ `N(S) ∩ N(T†)` finite-dimensional.** -/
theorem HasCompactPair.finiteDimensional (h : HasCompactPair T S)
    (hT : Dense (T.domain : Set E)) (hSc : S.IsClosed) :
    FiniteDimensional 𝕜 (S.ker ⊓ T†.ker : Submodule 𝕜 F) := by
  obtain ⟨K, hK, hsub⟩ := h
  refine Submodule.finiteDimensional_of_closedBall_subset_isCompact
    ((isClosed_ker hSc).inter (isClosed_ker (adjoint_isClosed hT))) hK fun x hx h1 => ?_
  obtain ⟨⟨y, hy⟩, rfl, hy0⟩ := (LinearPMap.mem_ker_iff).1 hx.1
  obtain ⟨⟨z, hz⟩, hzy, hz0⟩ := (LinearPMap.mem_ker_iff).1 hx.2
  subst hzy
  exact hsub _ hy hz h1 (by rw [hy0, norm_zero]; exact zero_le_one)
    (by rw [hz0, norm_zero]; exact zero_le_one)

end Feec.Operator

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-- **The compactness property at `i`**: the unit ball of `Vⁱ ∩ V*ᵢ`, in the norm
`max (‖x‖, ‖d x‖, ‖d† x‖)`, lies in a compact subset of `Wⁱ`. Thesis: §4.2 (corrected) -/
def HasCompactPropertyAt (i : ι) : Prop :=
  ∃ K : Set (W i), IsCompact K ∧ ∀ (x : W i) (hx : x ∈ (H.d i (c.next i)).domain)
    (hx' : x ∈ ((H.d (c.prev i) i)†).domain), ‖x‖ ≤ 1 → ‖H.d i (c.next i) ⟨x, hx⟩‖ ≤ 1 →
      ‖(H.d (c.prev i) i)† ⟨x, hx'⟩‖ ≤ 1 → x ∈ K

/-- The compactness property at every index. Thesis: §4.2 (corrected) -/
def HasCompactProperty : Prop := ∀ i, H.HasCompactPropertyAt i

variable {H}

/-- Scaling by `a ≠ 0` maps the box of radius `ρ` to the box of radius `|a| ρ`. -/
private theorem smul_mem_box {i : ι} {a : ℝ} (ha : 0 < a) {x : W i}
    (hx : x ∈ (H.d i (c.next i)).domain) (hx' : x ∈ ((H.d (c.prev i) i)†).domain) :
    ‖(a : 𝕜) • x‖ = a * ‖x‖ ∧
      ‖H.d i (c.next i) ⟨(a : 𝕜) • x, Submodule.smul_mem _ _ hx⟩‖ =
        a * ‖H.d i (c.next i) ⟨x, hx⟩‖ ∧
      ‖(H.d (c.prev i) i)† ⟨(a : 𝕜) • x, Submodule.smul_mem _ _ hx'⟩‖ =
        a * ‖(H.d (c.prev i) i)† ⟨x, hx'⟩‖ := by
  have hn : ∀ {V : Type _} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (v : V),
      ‖(a : 𝕜) • v‖ = a * ‖v‖ := fun v => by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos ha]
  refine ⟨hn x, ?_, ?_⟩
  · rw [show H.d i (c.next i) ⟨(a : 𝕜) • x, Submodule.smul_mem _ _ hx⟩ =
      (a : 𝕜) • H.d i (c.next i) ⟨x, hx⟩ from LinearPMap.map_smul _ _ ⟨x, hx⟩, hn]
  · rw [show (H.d (c.prev i) i)† ⟨(a : 𝕜) • x, Submodule.smul_mem _ _ hx'⟩ =
      (a : 𝕜) • (H.d (c.prev i) i)† ⟨x, hx'⟩ from LinearPMap.map_smul _ _ ⟨x, hx'⟩, hn]

/-- The compactness property, with any radius `r` in place of `1`. -/
theorem HasCompactPropertyAt.exists_isCompact {i : ι} (h : H.HasCompactPropertyAt i) (r : ℝ) :
    ∃ K : Set (W i), IsCompact K ∧ ∀ (x : W i) (hx : x ∈ (H.d i (c.next i)).domain)
      (hx' : x ∈ ((H.d (c.prev i) i)†).domain), ‖x‖ ≤ r → ‖H.d i (c.next i) ⟨x, hx⟩‖ ≤ r →
        ‖(H.d (c.prev i) i)† ⟨x, hx'⟩‖ ≤ r → x ∈ K := by
  obtain ⟨K, hK, hsub⟩ := h
  set s : ℝ := max r 1
  have hs : 0 < s := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(fun y => (s : 𝕜) • y) '' K, hK.image (continuous_const_smul _), ?_⟩
  intro x hx hx' h1 h2 h3
  have hsx : ∀ a : ℝ, a ≤ r → s⁻¹ * a ≤ 1 := fun a ha => by
    rw [inv_mul_le_iff₀ hs, mul_one]; exact ha.trans (le_max_left _ _)
  obtain ⟨e1, e2, e3⟩ := smul_mem_box (inv_pos.2 hs) hx hx'
  refine ⟨_, hsub (((s⁻¹ : ℝ) : 𝕜) • x) _ _ (by rw [e1]; exact hsx _ h1)
    (by rw [e2]; exact hsx _ h2) (by rw [e3]; exact hsx _ h3), ?_⟩
  simp only [smul_smul]
  rw [← RCLike.ofReal_mul, mul_inv_cancel₀ hs.ne', RCLike.ofReal_one, one_smul]

/-- The compactness property from a bound with any positive radius. -/
theorem hasCompactPropertyAt_of_bound {i : ι} {r : ℝ} (hr : 0 < r) {K : Set (W i)}
    (hK : IsCompact K) (hsub : ∀ (x : W i) (hx : x ∈ (H.d i (c.next i)).domain)
      (hx' : x ∈ ((H.d (c.prev i) i)†).domain), ‖x‖ ≤ r → ‖H.d i (c.next i) ⟨x, hx⟩‖ ≤ r →
        ‖(H.d (c.prev i) i)† ⟨x, hx'⟩‖ ≤ r → x ∈ K) : H.HasCompactPropertyAt i := by
  refine ⟨(fun y => ((r⁻¹ : ℝ) : 𝕜) • y) '' K, hK.image (continuous_const_smul _), ?_⟩
  intro x hx hx' h1 h2 h3
  obtain ⟨e1, e2, e3⟩ := smul_mem_box hr hx hx'
  refine ⟨(r : 𝕜) • x, hsub _ _ _ (by rw [e1]; nlinarith [norm_nonneg x])
    (by rw [e2]; nlinarith [norm_nonneg (H.d i (c.next i) ⟨x, hx⟩)])
    (by rw [e3]; nlinarith [norm_nonneg ((H.d (c.prev i) i)† ⟨x, hx'⟩)]), ?_⟩
  simp only [smul_smul]
  rw [← RCLike.ofReal_mul, inv_mul_cancel₀ hr.ne', RCLike.ofReal_one, one_smul]

/-- The compactness property at `i`, at a related pair `h → i → j`. -/
theorem hasCompactPropertyAt_iff_of_rel {h i j : ι} (hhi : c.Rel h i) (hij : c.Rel i j) :
    H.HasCompactPropertyAt i ↔ ∃ K : Set (W i), IsCompact K ∧ ∀ (x : W i)
      (hx : x ∈ (H.d i j).domain) (hx' : x ∈ ((H.d h i)†).domain), ‖x‖ ≤ 1 →
        ‖H.d i j ⟨x, hx⟩‖ ≤ 1 → ‖(H.d h i)† ⟨x, hx'⟩‖ ≤ 1 → x ∈ K := by
  obtain rfl := c.next_eq' hij
  obtain rfl := c.prev_eq' hhi
  rfl

/-- The compactness property at an index with no outgoing arrow, `h → i`: only `D((d h i)†)`
enters. -/
theorem hasCompactPropertyAt_iff_of_rel_of_not_rel {h i : ι} (hhi : c.Rel h i)
    (hi : ∀ j, ¬ c.Rel i j) :
    H.HasCompactPropertyAt i ↔ ∃ K : Set (W i), IsCompact K ∧ ∀ (x : W i)
      (hx' : x ∈ ((H.d h i)†).domain), ‖x‖ ≤ 1 → ‖(H.d h i)† ⟨x, hx'⟩‖ ≤ 1 → x ∈ K := by
  obtain rfl := c.prev_eq' hhi
  have h0 := H.shape i (c.next i) (hi _)
  constructor
  · rintro ⟨K, hK, hsub⟩
    refine ⟨K, hK, fun x hx' h1 h3 => hsub x (H.domain_eq_top_of_not_rel (hi _) ▸ trivial) hx'
      h1 ?_ h3⟩
    rw [apply_eq_zero_of_eq_zero h0, norm_zero]; exact zero_le_one
  · rintro ⟨K, hK, hsub⟩
    exact ⟨K, hK, fun x _ hx' h1 _ h3 => hsub x hx' h1 h3⟩

/-- The compactness property at an index with no incoming arrow, `i → j`: only `D(d i j)`
enters. -/
theorem hasCompactPropertyAt_iff_of_not_rel_of_rel {i j : ι} (hi : ∀ h, ¬ c.Rel h i)
    (hij : c.Rel i j) :
    H.HasCompactPropertyAt i ↔ ∃ K : Set (W i), IsCompact K ∧ ∀ (x : W i)
      (hx : x ∈ (H.d i j).domain), ‖x‖ ≤ 1 → ‖H.d i j ⟨x, hx⟩‖ ≤ 1 → x ∈ K := by
  obtain rfl := c.next_eq' hij
  have h0 : (H.d (c.prev i) i)† = 0 := by rw [H.shape _ i (hi _), adjoint_zero]
  constructor
  · rintro ⟨K, hK, hsub⟩
    refine ⟨K, hK, fun x hx h1 h2 => hsub x hx (by rw [h0]; trivial) h1 h2 ?_⟩
    rw [apply_eq_zero_of_eq_zero h0, norm_zero]; exact zero_le_one
  · rintro ⟨K, hK, hsub⟩
    exact ⟨K, hK, fun x hx _ h1 h2 _ => hsub x hx h1 h2⟩

/-- Every index of a complex with finite-dimensional spaces has the compactness property. -/
theorem hasCompactPropertyAt_of_finiteDimensional (i : ι) [FiniteDimensional 𝕜 (W i)] :
    H.HasCompactPropertyAt i :=
  haveI := FiniteDimensional.proper_rclike 𝕜 (W i)
  ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, fun _ _ _ h1 _ _ => mem_closedBall_zero_iff.2 h1⟩

/-- The compactness property at `i` is compactness of the middle space of the pair
`d (c.prev i) i`, `d i (c.next i)`. -/
theorem hasCompactPropertyAt_iff_hasCompactPair {i : ι} :
    H.HasCompactPropertyAt i ↔ Operator.HasCompactPair (H.d (c.prev i) i) (H.d i (c.next i)) :=
  Iff.rfl

/-! ### Duality -/

/-- The compactness property passes to the dual complex. -/
theorem HasCompactPropertyAt.dual {i : ι} (h : H.HasCompactPropertyAt i) :
    H.dual.HasCompactPropertyAt i :=
  Operator.HasCompactPair.adjoint h (H.dense _ _) (H.closed _ _)

theorem hasCompactPropertyAt_dual_iff {i : ι} :
    H.dual.HasCompactPropertyAt i ↔ H.HasCompactPropertyAt i :=
  ⟨fun h => by simpa only [dual_dual] using h.dual, HasCompactPropertyAt.dual⟩

theorem HasCompactProperty.dual (h : H.HasCompactProperty) : H.dual.HasCompactProperty :=
  fun i => (h i).dual

/-! ### Compactness ⇒ closed range and finite-dimensional harmonic forms -/

/-- **Compactness ⇒ closed range** of the outgoing differential `d i (c.next i)`.
Thesis: §4.2 (corrected) -/
theorem HasCompactPropertyAt.isClosed_range {i : ι} (h : H.HasCompactPropertyAt i) :
    IsClosed (LinearMap.range (H.d i (c.next i)).toFun : Set (W (c.next i))) :=
  Operator.HasCompactPair.isClosed_range_right h (H.dense _ _) (H.closed _ _) (H.mapsTo _ _ _)
    (H.d_comp_d _ _ _)

/-- **Compactness ⇒ closed range** at the next index: `𝔅ʲ` is closed for `i → j`.
Thesis: §4.2 (corrected) -/
theorem HasCompactPropertyAt.closedRangeAt_of_rel {i j : ι} (h : H.HasCompactPropertyAt i)
    (hij : c.Rel i j) : H.ClosedRangeAt j := by
  obtain rfl := c.next_eq' hij
  rw [ClosedRangeAt, H.boundaries_eq hij]
  exact h.isClosed_range

/-- **Compactness ⇒ closed range** at `i`: `𝔅ⁱ` is closed. Thesis: §4.2 (corrected) -/
theorem HasCompactPropertyAt.closedRangeAt {i : ι} (h : H.HasCompactPropertyAt i) :
    H.ClosedRangeAt i :=
  Operator.HasCompactPair.isClosed_range_left h (H.dense _ _) (H.closed _ _) (H.closed _ _)
    (H.mapsTo _ _ _) (H.d_comp_d _ _ _)

/-- **Compactness ⇒ closed dual range** at `i`: `𝔅*ᵢ` is closed. -/
theorem HasCompactPropertyAt.dual_closedRangeAt {i : ι} (h : H.HasCompactPropertyAt i) :
    H.dual.ClosedRangeAt i :=
  h.dual.closedRangeAt

/-- **Compactness ⇒ finite-dimensional harmonic forms.** Thesis: §4.2 (corrected) -/
theorem HasCompactPropertyAt.finiteDimensional_harmonic {i : ι} (h : H.HasCompactPropertyAt i) :
    FiniteDimensional 𝕜 (H.harmonic i) :=
  Operator.HasCompactPair.finiteDimensional h (H.dense _ _) (H.closed _ _)

/-- **Compactness ⇒ closed and Fredholm** at `i`: `𝔅ⁱ` and `𝔅*ᵢ` are closed, the harmonic
forms and the cohomology are finite-dimensional, and the Hodge decomposition
`Wⁱ = 𝔅ⁱ ⊕ ℌⁱ ⊕ 𝔅*ᵢ` holds without closures. This corrects the thesis' chain
"compactness ⇒ Fredholm ⇒ closed". Thesis: §4.2 (corrected), Thm 4.1 -/
theorem HasCompactPropertyAt.closed_and_fredholm {i : ι} (h : H.HasCompactPropertyAt i) :
    H.ClosedRangeAt i ∧ H.dual.ClosedRangeAt i ∧ FiniteDimensional 𝕜 (H.harmonic i) ∧
      FiniteDimensional 𝕜 (H.cohomology i) ∧
      H.boundaries i ⊔ H.harmonic i ⊔ H.dual.boundaries i = ⊤ :=
  have hfd := h.finiteDimensional_harmonic
  ⟨h.closedRangeAt, h.dual_closedRangeAt, hfd,
    (H.finiteDimensional_harmonic_iff h.closedRangeAt).1 hfd,
    (H.hodge_of_closedRangeAt h.closedRangeAt h.dual_closedRangeAt).1⟩

/-! ### Compact resolvent of the wave operator -/

section Resolvent

variable [Fintype ι]

/-- At a related pair `i → j`, the `j`-th component of `𝐝 x` is `d i j (x i)`. -/
theorem totalD_apply_of_rel (x : H.totalD.domain) {i j : ι} (hij : c.Rel i j) :
    (H.totalD x) j = H.d i j ⟨(x : PiLp 2 W) i, x.2 i j⟩ := by
  rw [totalD_apply]
  refine Finset.sum_eq_single i (fun i' _ hi' => ?_) (fun h => absurd (Finset.mem_univ i) h)
  exact apply_eq_zero_of_eq_zero (H.shape i' j fun h' => hi' (c.prev_eq h' hij)) _

/-- Each differential of a component is bounded by the total differential. -/
theorem norm_d_le_norm_totalD (x : H.totalD.domain) (i j : ι) :
    ‖H.d i j ⟨(x : PiLp 2 W) i, x.2 i j⟩‖ ≤ ‖H.totalD x‖ := by
  by_cases hij : c.Rel i j
  · rw [← H.totalD_apply_of_rel x hij]; exact PiLp.norm_apply_le _ _
  · rw [apply_eq_zero_of_not_rel _ hij, norm_zero]; exact norm_nonneg _

/-- `‖(𝐝 − 𝐝†) x‖² = ‖𝐝 x‖² + ‖𝐝† x‖²` on `D(𝐝) ∩ D(𝐝†)` (the cross term vanishes by
`𝐝 𝐝 = 0`). -/
theorem norm_wave_sq (x : H.wave.domain) :
    ‖H.wave x‖ ^ 2 = ‖H.totalD ⟨x, x.2.1⟩‖ ^ 2 + ‖H.dual.totalD ⟨x, x.2.2⟩‖ ^ 2 := by
  have hw : H.wave x = H.totalD ⟨x, x.2.1⟩ - H.dual.totalD ⟨x, x.2.2⟩ := rfl
  have h0 : ⟪H.totalD ⟨x, x.2.1⟩, H.dual.totalD ⟨x, x.2.2⟩⟫_𝕜 = 0 := by
    rw [← H.inner_totalD_dual ⟨_, H.totalD_mapsTo ⟨x, x.2.1⟩⟩ ⟨x, x.2.2⟩,
      H.totalD_comp_totalD, inner_zero_left]
  rw [hw, @norm_sub_sq 𝕜, h0, _root_.map_zero, mul_zero, sub_zero]

/-- **Compact resolvent**: a finite complex with the compactness property at every index has
`(1 − (d − d†))⁻¹` compact. Thesis: §4.2 (corrected) -/
theorem HasCompactProperty.isCompactOperator_resolvent_wave (h : H.HasCompactProperty) :
    IsCompactOperator (Operator.resolvent H.wave 1) := by
  choose K hK hsub using fun i => (h i).exists_isCompact 2
  refine ⟨(PiLp.homeomorph 2 W) ⁻¹' Set.pi univ K,
    (PiLp.homeomorph 2 W).isCompact_preimage.2 (isCompact_univ_pi hK),
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun y hy => ?_⟩
  rw [mem_ball_zero_iff] at hy
  have hA := H.isSkewAdjoint_wave
  have hre : RCLike.re (1 : 𝕜) ≠ 0 := by simp
  have hR := Operator.isResolvent_resolvent hA hre
  set x : H.wave.domain := ⟨_, hR.mem_domain y⟩
  have hx1 : ‖(x : PiLp 2 W)‖ ≤ 1 := by
    have hn1 : ‖Operator.resolvent H.wave 1‖ ≤ 1 :=
      (Operator.norm_resolvent_le hA hre).trans (by simp)
    have := (Operator.resolvent H.wave 1).le_of_opNorm_le hn1 y
    exact this.trans (by nlinarith [norm_nonneg y])
  have hxw : H.wave x = (x : PiLp 2 W) - y := by
    have := hR.sub_apply y
    rw [one_smul] at this
    rw [← this, sub_sub_cancel]
  have hw2 : ‖H.wave x‖ ≤ 2 := by
    rw [hxw]; exact (norm_sub_le _ _).trans (by linarith)
  have hsq := H.norm_wave_sq x
  have hT : ‖H.totalD ⟨x, x.2.1⟩‖ ≤ 2 := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_two two_ne_zero).1 ?_
    nlinarith [norm_nonneg (H.dual.totalD ⟨x, x.2.2⟩), norm_nonneg (H.wave x)]
  have hT' : ‖H.dual.totalD ⟨x, x.2.2⟩‖ ≤ 2 := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_two two_ne_zero).1 ?_
    nlinarith [norm_nonneg (H.totalD ⟨x, x.2.1⟩), norm_nonneg (H.wave x)]
  intro i _
  refine hsub i _ (x.2.1 i (c.next i)) (x.2.2 i (c.prev i))
    ((PiLp.norm_apply_le _ i).trans (hx1.trans one_le_two)) ?_ ?_
  · exact (H.norm_d_le_norm_totalD ⟨x, x.2.1⟩ i (c.next i)).trans hT
  · exact (H.dual.norm_d_le_norm_totalD ⟨x, x.2.2⟩ i (c.prev i)).trans hT'

/-- **Compact resolvent ⇒ `EigenDense`**: for a finite complex with the compactness property,
the eigenvectors of the square of the wave operator are dense, so its Stone group has pure
point spectrum. -/
theorem HasCompactProperty.eigenDense_wave [NormedSpace ℝ (PiLp 2 W)]
    [IsScalarTower ℝ 𝕜 (PiLp 2 W)] (h : H.HasCompactProperty) :
    H.isSkewAdjoint_wave.group.EigenDense :=
  C0Group.eigenDense_of_compactResolvent _ h.isCompactOperator_resolvent_wave

end Resolvent

end Feec.HilbertComplex
