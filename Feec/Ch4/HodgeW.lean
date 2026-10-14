import Feec.Ch4.Adjoint
import Feec.Ch4.Hodge

/-!
# `W`-level Hodge theory: compactness, Fredholm, and the bounded-model bridge (Thesis §4.2)

Complements `Feec.Ch4.Adjoint` (which proves the `W`-level Hodge decomposition, Thm 4.1:
`HilbertComplex2.hodge_W`, `hodge_W_of_closedRange`, `harmonic_eq`, `range_adjoint_d1_eq`
(`B* = Zᗮ`)) and `Feec.Ch4.Hodge` (bounded model). Critic items 7–10. Coverage:

* **Compactness property, precisely stated** (thesis: "`Vᵏ ∩ Vₖ*` is a dense and compact
  subspace of `Wᵏ`", corrected to a compact *inclusion*): `HilbertComplex2.HasCompactEmbedding`
  (`V¹ ∩ V₁* ↪ W1`, norm `‖u‖² + ‖d1 u‖² + ‖d0* u‖²`), `HasCompactEmbedding0` (`V⁰ ↪ W0`),
  `HasCompactEmbedding2` (`V₂* ↪ W2`); non-vacuity `hasCompactEmbedding_of_finiteDimensional`.
* **Compactness ⇒ closed** (the thesis' actual claim, unproved there):
  `isClosed_range_d0_of_compact`, `isClosed_range_d1_of_compact`, `closedRange_of_compact`, and
  the end-position forms `isClosed_range_d0_of_compact0`, `isClosed_range_d1_of_compact2`.
* **Compactness ⇒ Fredholm** (finite-dimensional `ℌ⁰ = N(d0)`, `ℌ¹`, `ℌ² = N(d1*)`):
  `finiteDimensional_harmonic_of_compact`, `finiteDimensional_ker_d0_of_compact0`,
  `finiteDimensional_ker_adjoint_d1_of_compact2`; all together with the closure-free Hodge
  decomposition in `closed_and_fredholm_of_compact`.
* **"Fredholm ⇒ closed" refuted with the project's `W`-level definitions** (critic item 10):
  `fredholm_not_closed_W` for `0 → ℓ² --diag(1/(n+1))--> ℓ² → ℝ⁰ → 0` (built with
  `HilbertComplex2.ofBounded`); the Brüning–Lesch version (finite-dimensional algebraic
  cohomology ⇒ closed) at the `W` level: `UHilbertComplex.isClosed_range_of_finiteDimensional_cohomology`,
  `HilbertComplex2.isClosed_range_d0_of_finiteDimensional_cohomology`.
* **Bridge to the bounded model** (critic item 8): for `UHilbertComplex`,
  `map_H_eq_harmonic` (bounded `ℌ` ↦ `W`-level `N(d) ∩ N(d*)`), `cohomologyEquiv`, and the
  derivation of M5's compact-operator hypotheses from the thesis' compactness property
  (`isCompactOperator_orthogonal_Z`, `isCompactOperator_H`, `isCompactOperator_orthogonal_Z_zero`,
  combined in `UHilbertComplex.closed_and_fredholm_of_compact`). For `HilbertComplex2`: the
  zero extension `HilbertComplex2.toU` (with `toU_segment_zero : H.toU.segment 0 = H`), the
  bounded model `HilbertComplex2.toHilbertComplex`, `closedRange_iff_isClosedAt`,
  `map_H_zero_eq_harmonic`, `closed_and_fredholm_V`.

Density of `V ∩ V*` (also in the thesis' definition) is never needed and is not assumed.
-/

open scoped RealInnerProductSpace Topology
open Set Filter LinearPMap

noncomputable section

namespace Feec

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Unpacking `x ∈ N(T)`. -/
theorem exists_apply_eq_zero_of_mem_ker {T : E →ₗ.[ℝ] F} {x : E} (hx : x ∈ T.ker) :
    ∃ h : x ∈ T.domain, T ⟨x, h⟩ = 0 := by
  obtain ⟨⟨y, hy⟩, rfl, h⟩ := (LinearPMap.mem_ker_iff).1 hx
  exact ⟨hy, h⟩

omit [CompleteSpace E] in
/-- A closed subspace whose unit ball lies in a compact set is finite-dimensional (Riesz). -/
theorem finiteDimensional_of_ball_subset_compact {S : Submodule ℝ E}
    (hS : IsClosed (S : Set E)) {K : Set E} (hK : IsCompact K)
    (hsub : ∀ x ∈ S, ‖x‖ ≤ 1 → x ∈ K) : FiniteDimensional ℝ S := by
  have hiso : Isometry (S.subtype : S → E) := isometry_subtype_coe
  have himg : (S.subtype : S → E) '' Metric.closedBall 0 1 = (S : Set E) ∩ Metric.closedBall 0 1 := by
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
  exact FiniteDimensional.of_isCompact_closedBall₀ ℝ zero_lt_one
    (hiso.isEmbedding.isCompact_iff.2 (himg ▸ hc))

/-- Compactness ⇒ closed range, for a closed operator: if the unit ball of `D(T) ∩ N(T)ᗮ` in
the box graph norm lies in a compact subset of `E`, then `R(T)` is closed. -/
theorem isClosed_range_of_ball_subset_compact {T : E →ₗ.[ℝ] F} (hc : T.IsClosed)
    {K : Set E} (hK : IsCompact K)
    (hsub : ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ 1 → ‖T x‖ ≤ 1 → (x : E) ∈ K) :
    IsClosed (LinearMap.range T.toFun : Set F) := by
  by_contra hR
  rw [isClosed_range_iff_poincare hc] at hR
  push Not at hR
  have hseq : ∀ n : ℕ, ∃ v : T.domain, (v : E) ∈ T.kerᗮ ∧ ‖(v : E)‖ = 1 ∧
      ‖T v‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨u, hu, h⟩ := hR ((n : ℝ) + 1)
    have hu0 : 0 < ‖(u : E)‖ := lt_of_le_of_lt (by positivity) h
    refine ⟨‖(u : E)‖⁻¹ • u, ?_, ?_, ?_⟩
    · exact Submodule.smul_mem _ _ hu
    · change ‖‖(u : E)‖⁻¹ • (u : E)‖ = 1
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ hu0.ne'
    · rw [LinearPMap.map_smul, norm_smul, norm_inv, norm_norm]
      rw [inv_mul_le_iff₀ hu0, mul_one_div, le_div_iff₀ (by positivity)]
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
    have := Submodule.inf_orthogonal_eq_bot T.ker
    have hmem : a ∈ T.ker ⊓ T.kerᗮ := ⟨hker, hperp⟩
    rw [this] at hmem
    exact hmem
  have hn : Tendsto (fun n => ‖(v (φ n) : E)‖) atTop (𝓝 ‖a‖) := hlim.norm
  simp only [hv1, ha, norm_zero] at hn
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hn)

end Generic

/-! ### The compactness property at the `W` level -/

namespace HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

/-- **Compactness property at the middle space** (Thesis §4.2, corrected): the inclusion
`V¹ ∩ V₁* ↪ W¹` is compact, where `V¹ ∩ V₁* = D(d1) ∩ D(d0*)` carries the norm
`‖u‖² + ‖d1 u‖² + ‖d0* u‖²`; i.e. its unit ball lies in a compact subset of `W1`.

Correction: the thesis says "`Vᵏ ∩ Vₖ*` is a dense and compact subspace of `Wᵏ`"; a compact
subspace is `{0}`, so the intended meaning is a compact inclusion. Density is not needed for
any conclusion below and is omitted. -/
def HasCompactEmbedding : Prop :=
  ∃ K : Set W1, IsCompact K ∧ ∀ (u : W1) (h1 : u ∈ H.d1.domain) (h0 : u ∈ H.d0†.domain),
    ‖u‖ ^ 2 + ‖H.d1 ⟨u, h1⟩‖ ^ 2 + ‖H.d0† ⟨u, h0⟩‖ ^ 2 ≤ 1 → u ∈ K

/-- Compactness property at the first space: `V⁰ ∩ V₀* = V⁰ = D(d0)` (since `d_{-1} = 0`, so
`V₀* = W0`) embeds compactly in `W0`. -/
def HasCompactEmbedding0 : Prop :=
  ∃ K : Set W0, IsCompact K ∧ ∀ (u : W0) (h : u ∈ H.d0.domain),
    ‖u‖ ^ 2 + ‖H.d0 ⟨u, h⟩‖ ^ 2 ≤ 1 → u ∈ K

/-- Compactness property at the last space: `V² ∩ V₂* = D(d1*)` (since `d2 = 0`, so `V² = W2`)
embeds compactly in `W2`. -/
def HasCompactEmbedding2 : Prop :=
  ∃ K : Set W2, IsCompact K ∧ ∀ (u : W2) (h : u ∈ H.d1†.domain),
    ‖u‖ ^ 2 + ‖H.d1† ⟨u, h⟩‖ ^ 2 ≤ 1 → u ∈ K

/-- Halving puts box-norm unit vectors into the squared-norm unit ball. -/
private theorem sq_half_le {a b c : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) : (1 / 2 * a) ^ 2 + (1 / 2 * b) ^ 2 + (1 / 2 * c) ^ 2 ≤ 1 := by
  nlinarith [pow_le_one₀ (n := 2) ha0 ha, pow_le_one₀ (n := 2) hb0 hb, pow_le_one₀ (n := 2) hc0 hc]

/-- `2 • K` is compact. -/
private theorem isCompact_two_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) : IsCompact ((fun x => (2 : ℝ) • x) '' K) :=
  hK.image (continuous_const_smul _)

/-- `x = 2 • (½ x)`. -/
private theorem mem_two_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {x : E} (h : (1 / 2 : ℝ) • x ∈ K) : x ∈ (fun x => (2 : ℝ) • x) '' K :=
  ⟨_, h, show (2 : ℝ) • ((1 / 2 : ℝ) • x) = x by rw [smul_smul]; norm_num⟩

/-- `N(d1)ᗮ ⊆ N(d0*)`: since `B⁰ ⊆ Z¹`, `(Z¹)ᗮ ⊆ (B⁰)ᗮ = Z*₀`. -/
theorem orthogonal_ker_d1_le : H.d1.kerᗮ ≤ H.d0†.ker := by
  rw [← H.orthogonal_range_d0]
  exact Submodule.orthogonal_le H.range_d0_le_ker_d1

/-- `N(d0*)ᗮ ⊆ N(d1)`: `N(d0*)ᗮ = cl B⁰ ⊆ Z¹`. -/
theorem orthogonal_ker_adjoint_d0_le : H.d0†.kerᗮ ≤ H.d1.ker := by
  rw [← H.orthogonal_range_d0, Submodule.orthogonal_orthogonal_eq_closure]
  exact Submodule.topologicalClosure_minimal _ H.range_d0_le_ker_d1 (isClosed_ker H.closed1)

/-- **Thesis §4.2, "compactness ⇒ closed", for `d1`.** If `V¹ ∩ V₁* ↪ W¹` is compact then
`B² = R(d1)` is closed.

Thesis gap: asserted without proof. Proof: on `D(d1) ∩ N(d1)ᗮ ⊆ N(d0*)` the `V ∩ V*`-norm is
the graph norm of `d1`, so a failing Poincaré sequence has a convergent subsequence whose limit
lies in `N(d1) ∩ N(d1)ᗮ = 0` but has norm `1` (`isClosed_range_of_ball_subset_compact`). -/
theorem isClosed_range_d1_of_compact (hC : H.HasCompactEmbedding) :
    IsClosed (LinearMap.range H.d1.toFun : Set W2) := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine isClosed_range_of_ball_subset_compact H.closed1 (isCompact_two_smul hK) ?_
  intro x hx hx1 hdx1
  obtain ⟨y, hy, hy0⟩ := (LinearPMap.mem_ker_iff).1 (H.orthogonal_ker_d1_le hx)
  refine mem_two_smul (hsub _ (Submodule.smul_mem _ _ x.2)
    (by rw [hy]; exact Submodule.smul_mem _ _ y.2) ?_)
  have e1 : H.d1 ⟨(1 / 2 : ℝ) • (x : W1), Submodule.smul_mem _ _ x.2⟩ = (1 / 2 : ℝ) • H.d1 x :=
    LinearPMap.map_smul _ _ _
  have e0 : ∀ h, H.d0† ⟨(1 / 2 : ℝ) • (x : W1), h⟩ = 0 := fun h => by
    have : (⟨(1 / 2 : ℝ) • (x : W1), h⟩ : H.d0†.domain) = (1 / 2 : ℝ) • y :=
      Subtype.ext (by simp [hy])
    rw [this, LinearPMap.map_smul, hy0, smul_zero]
  rw [e1, e0, norm_smul, norm_smul, norm_zero]
  simpa using sq_half_le hx1 hdx1 zero_le_one (norm_nonneg _) (norm_nonneg _) le_rfl

/-- **Thesis §4.2, "compactness ⇒ closed", for `d0`.** If `V¹ ∩ V₁* ↪ W¹` is compact then
`B¹ = R(d0)` is closed.

Thesis gap: asserted without proof. Proof: the same argument applied to the closed operator
`d0*` on `D(d0*) ∩ N(d0*)ᗮ ⊆ N(d1)`, followed by the closed range theorem
(`isClosed_range_adjoint_iff`). -/
theorem isClosed_range_d0_of_compact (hC : H.HasCompactEmbedding) :
    IsClosed (LinearMap.range H.d0.toFun : Set W1) := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine (isClosed_range_adjoint_iff _ H.dense0 H.closed0).1 ?_
  refine isClosed_range_of_ball_subset_compact (adjoint_isClosed H.dense0)
    (isCompact_two_smul hK) ?_
  intro x hx hx1 hdx1
  obtain ⟨y, hy, hy0⟩ := (LinearPMap.mem_ker_iff).1 (H.orthogonal_ker_adjoint_d0_le hx)
  refine mem_two_smul (hsub _ (by rw [hy]; exact Submodule.smul_mem _ _ y.2)
    (Submodule.smul_mem _ _ x.2) ?_)
  have e0 : H.d0† ⟨(1 / 2 : ℝ) • (x : W1), Submodule.smul_mem _ _ x.2⟩ =
      (1 / 2 : ℝ) • H.d0† x :=
    LinearPMap.map_smul _ _ _
  have e1 : ∀ h, H.d1 ⟨(1 / 2 : ℝ) • (x : W1), h⟩ = 0 := fun h => by
    have : (⟨(1 / 2 : ℝ) • (x : W1), h⟩ : H.d1.domain) = (1 / 2 : ℝ) • y :=
      Subtype.ext (by simp [hy])
    rw [this, LinearPMap.map_smul, hy0, smul_zero]
  rw [e0, e1, norm_smul, norm_smul, norm_zero]
  simpa using sq_half_le hx1 zero_le_one hdx1 (norm_nonneg _) le_rfl (norm_nonneg _)

/-- **Thesis §4.2: the compactness property implies the complex is closed.** Compactness of
`V¹ ∩ V₁* ↪ W¹` alone gives closed range of both `d0` and `d1`. -/
theorem closedRange_of_compact (hC : H.HasCompactEmbedding) : H.ClosedRange :=
  ⟨H.isClosed_range_d0_of_compact hC, H.isClosed_range_d1_of_compact hC⟩

/-- `ℌ¹ = N(d1) ∩ N(d0*)` is closed in `W1`. -/
theorem isClosed_harmonic : IsClosed (H.harmonic : Set W1) :=
  (isClosed_ker H.closed1).inter (isClosed_ker (adjoint_isClosed H.dense0))

/-- **Thesis §4.2: the compactness property implies `ℌ¹` is finite-dimensional.**

Thesis gap: asserted without proof. Proof: on `ℌ¹ ⊆ V¹ ∩ V₁*` we have `d1 = 0`, `d0* = 0`, so
its `W`-unit ball is in the `V ∩ V*`-unit ball, hence in a compact set; `ℌ¹` is closed, so Riesz's
theorem applies. -/
theorem finiteDimensional_harmonic_of_compact (hC : H.HasCompactEmbedding) :
    FiniteDimensional ℝ H.harmonic := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine finiteDimensional_of_ball_subset_compact H.isClosed_harmonic hK fun x hx hx1 => ?_
  obtain ⟨h1, e1⟩ := exists_apply_eq_zero_of_mem_ker hx.1
  obtain ⟨h0, e0⟩ := exists_apply_eq_zero_of_mem_ker hx.2
  refine hsub x h1 h0 ?_
  rw [e1, e0, norm_zero, norm_zero]
  nlinarith [norm_nonneg x]

/-- **Thesis §4.2, compactness at the first space ⇒ `B¹` closed.** If `V⁰ ↪ W0` is compact
(graph norm of `d0`) then `R(d0)` is closed. (Here `N(d0)ᗮ` needs no adjoint.) -/
theorem isClosed_range_d0_of_compact0 (hC : H.HasCompactEmbedding0) :
    IsClosed (LinearMap.range H.d0.toFun : Set W1) := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine isClosed_range_of_ball_subset_compact H.closed0 (isCompact_two_smul hK) ?_
  intro x _ hx1 hdx1
  refine mem_two_smul (hsub _ (Submodule.smul_mem _ _ x.2) ?_)
  have e : H.d0 ⟨(1 / 2 : ℝ) • (x : W0), Submodule.smul_mem _ _ x.2⟩ = (1 / 2 : ℝ) • H.d0 x :=
    LinearPMap.map_smul _ _ _
  rw [e, norm_smul, norm_smul]
  have := sq_half_le hx1 hdx1 zero_le_one (norm_nonneg _) (norm_nonneg _) le_rfl
  simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this ⊢
  linarith

/-- **Thesis §4.2, compactness at the first space ⇒ `ℌ⁰ = Z⁰ = N(d0)` finite-dimensional.** -/
theorem finiteDimensional_ker_d0_of_compact0 (hC : H.HasCompactEmbedding0) :
    FiniteDimensional ℝ H.d0.ker := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine finiteDimensional_of_ball_subset_compact (isClosed_ker H.closed0) hK fun x hx hx1 => ?_
  obtain ⟨h, e⟩ := exists_apply_eq_zero_of_mem_ker hx
  refine hsub x h ?_
  rw [e, norm_zero]
  nlinarith [norm_nonneg x]

/-- **Thesis §4.2, compactness at the last space ⇒ `B²` closed.** If `V₂* = D(d1*) ↪ W2` is
compact then `R(d1)` is closed (via the closed range theorem). -/
theorem isClosed_range_d1_of_compact2 (hC : H.HasCompactEmbedding2) :
    IsClosed (LinearMap.range H.d1.toFun : Set W2) := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine (isClosed_range_adjoint_iff _ H.dense1 H.closed1).1 ?_
  refine isClosed_range_of_ball_subset_compact (adjoint_isClosed H.dense1)
    (isCompact_two_smul hK) ?_
  intro x _ hx1 hdx1
  refine mem_two_smul (hsub _ (Submodule.smul_mem _ _ x.2) ?_)
  have e : H.d1† ⟨(1 / 2 : ℝ) • (x : W2), Submodule.smul_mem _ _ x.2⟩ =
      (1 / 2 : ℝ) • H.d1† x :=
    LinearPMap.map_smul _ _ _
  rw [e, norm_smul, norm_smul]
  have := sq_half_le hx1 hdx1 zero_le_one (norm_nonneg _) (norm_nonneg _) le_rfl
  simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this ⊢
  linarith

/-- **Thesis §4.2, compactness at the last space ⇒ `ℌ² = Z*₂ = N(d1*)` finite-dimensional.**
(`ℌ² = Z² ∩ (B²)ᗮ = (B²)ᗮ = N(d1*)` by (4.1a).) -/
theorem finiteDimensional_ker_adjoint_d1_of_compact2 (hC : H.HasCompactEmbedding2) :
    FiniteDimensional ℝ H.d1†.ker := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine finiteDimensional_of_ball_subset_compact (isClosed_ker (adjoint_isClosed H.dense1)) hK
    fun x hx hx1 => ?_
  obtain ⟨h, e⟩ := exists_apply_eq_zero_of_mem_ker hx
  refine hsub x h ?_
  rw [e, norm_zero]
  nlinarith [norm_nonneg x]

/-- **Thesis §4.2 + Thm 4.1 under the compactness property (corrected).** If the inclusions
`V⁰ ↪ W0`, `V¹ ∩ V₁* ↪ W1`, `V₂* ↪ W2` are compact, then the complex is closed, it is
Fredholm in the thesis' sense (`ℌ⁰ = N(d0)`, `ℌ¹`, `ℌ² = N(d1*)` finite-dimensional), and the
Hodge decomposition `W1 = B¹ ⊕ ℌ¹ ⊕ B*₁` holds without closures.

Correction: the thesis' chain "compactness ⇒ Fredholm ⇒ closed" is replaced by
"compactness ⇒ closed and Fredholm"; the middle step "Fredholm ⇒ closed" is false
(`fredholm_not_closed_W`). Only the middle compactness is needed for closedness. -/
theorem closed_and_fredholm_of_compact (h0 : H.HasCompactEmbedding0)
    (h1 : H.HasCompactEmbedding) (h2 : H.HasCompactEmbedding2) :
    H.ClosedRange ∧ FiniteDimensional ℝ H.d0.ker ∧ FiniteDimensional ℝ H.harmonic ∧
      FiniteDimensional ℝ H.d1†.ker ∧
      (LinearMap.range H.d0.toFun ⊔ H.harmonic ⊔ LinearMap.range H.d1†.toFun = ⊤ ∧
        LinearMap.range H.d0.toFun ⟂ H.harmonic ∧
        H.harmonic ⟂ LinearMap.range H.d1†.toFun ∧
        LinearMap.range H.d0.toFun ⟂ LinearMap.range H.d1†.toFun) :=
  have hC := H.closedRange_of_compact h1
  ⟨hC, H.finiteDimensional_ker_d0_of_compact0 h0, H.finiteDimensional_harmonic_of_compact h1,
    H.finiteDimensional_ker_adjoint_d1_of_compact2 h2, H.hodge_W_of_closedRange hC⟩

/-- Non-vacuity: every complex with finite-dimensional `W1` has the middle compactness
property (`K` = closed unit ball). -/
theorem hasCompactEmbedding_of_finiteDimensional [FiniteDimensional ℝ W1] :
    H.HasCompactEmbedding := by
  refine ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, fun u _ _ hu => ?_⟩
  rw [mem_closedBall_zero_iff]
  nlinarith [norm_nonneg u, sq_nonneg ‖H.d1 ⟨u, ‹_›⟩‖, sq_nonneg ‖H.d0† ⟨u, ‹_›⟩‖]

/-! ### Bounded complexes as `HilbertComplex2` -/

section Bounded

omit [CompleteSpace W0] [CompleteSpace W1] in
/-- An everywhere-defined continuous operator is closed. -/
theorem isClosed_toPMap_top (A : W0 →L[ℝ] W1) : ((A : W0 →ₗ[ℝ] W1).toPMap ⊤).IsClosed := by
  have : (((A : W0 →ₗ[ℝ] W1).toPMap ⊤).graph : Set (W0 × W1)) = {p | p.2 = A p.1} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hz]; rfl
    · intro h
      exact ⟨⟨x, Submodule.mem_top⟩, rfl, h.symm⟩
  rw [LinearPMap.IsClosed, this]
  exact isClosed_eq continuous_snd (A.continuous.comp continuous_fst)

omit [CompleteSpace W0] [CompleteSpace W1] in
/-- `N(f|_⊤) = N(f)`. -/
theorem ker_toPMap_top (f : W0 →ₗ[ℝ] W1) : (f.toPMap ⊤).ker = LinearMap.ker f := by
  rw [LinearMap.toPMap_ker, top_inf_eq]

omit [CompleteSpace W0] [CompleteSpace W1] in
/-- `R(f|_⊤) = R(f)`. -/
theorem range_toPMap_top (f : W0 →ₗ[ℝ] W1) :
    LinearMap.range (f.toPMap ⊤).toFun = LinearMap.range f := by
  change LinearMap.range (f.comp (⊤ : Submodule ℝ W0).subtype) = _
  rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_top]

/-- A bounded complex `W0 --A--> W1 --B--> W2` (`B A = 0`) as a Hilbert complex of
everywhere-defined operators. -/
def ofBounded (A : W0 →L[ℝ] W1) (B : W1 →L[ℝ] W2) (hBA : ∀ x, B (A x) = 0) :
    HilbertComplex2 W0 W1 W2 where
  d0 := (A : W0 →ₗ[ℝ] W1).toPMap ⊤
  d1 := (B : W1 →ₗ[ℝ] W2).toPMap ⊤
  dense0 := by simp
  dense1 := by simp
  closed0 := isClosed_toPMap_top A
  closed1 := isClosed_toPMap_top B
  map_mem _ := Submodule.mem_top
  comp_zero x := hBA x

/-- For a bounded complex, `d0* = A*` (everywhere defined). -/
theorem ofBounded_adjoint_d0 (A : W0 →L[ℝ] W1) (B : W1 →L[ℝ] W2) (hBA : ∀ x, B (A x) = 0) :
    (ofBounded A B hBA).d0† = ((ContinuousLinearMap.adjoint A : W1 →L[ℝ] W0) :
      W1 →ₗ[ℝ] W0).toPMap ⊤ :=
  A.toPMap_adjoint_eq_adjoint_toPMap_of_dense (by simp)

/-- For a bounded complex, `d1* = B*` (everywhere defined). -/
theorem ofBounded_adjoint_d1 (A : W0 →L[ℝ] W1) (B : W1 →L[ℝ] W2) (hBA : ∀ x, B (A x) = 0) :
    (ofBounded A B hBA).d1† = ((ContinuousLinearMap.adjoint B : W2 →L[ℝ] W1) :
      W2 →ₗ[ℝ] W1).toPMap ⊤ :=
  B.toPMap_adjoint_eq_adjoint_toPMap_of_dense (by simp)

end Bounded

end HilbertComplex2

/-! ### Counterexample to "Fredholm ⇒ closed" with the `W`-level definitions -/

namespace FredholmCE

/-- The trivial Hilbert space `ℝ⁰`. -/
abbrev R0 := EuclideanSpace ℝ (Fin 0)

/-- The `W`-level complex `0 → ℓ² --A--> ℓ² --0--> ℝ⁰ → 0`, `A = diag(1/(n+1))`, as a
`HilbertComplex2` (the thesis' setting of §4.2 with `n = 2`). -/
def cxW : HilbertComplex2 L2 L2 R0 :=
  HilbertComplex2.ofBounded A 0 fun _ => rfl

/-- `ℌ⁰ = N(d0) = N(A) = 0` in `cxW` (Thesis §4.2 counterexample). -/
theorem cxW_ker_d0 : cxW.d0.ker = ⊥ := by
  change ((A : L2 →ₗ[ℝ] L2).toPMap ⊤).ker = ⊥
  rw [HilbertComplex2.ker_toPMap_top, LinearMap.ker_eq_bot]
  exact A_injective

/-- `ℌ¹ = N(d1) ∩ N(d0*) = 0` in `cxW`, since `R(A)` is dense (Thesis §4.2 counterexample). -/
theorem cxW_harmonic : cxW.harmonic = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have h2 : y ∈ (LinearMap.range cxW.d0.toFun)ᗮ := cxW.orthogonal_range_d0 ▸ hy.2
  refine (Submodule.mem_bot ℝ).2 (eq_zero_of_inner_A_single fun n => ?_)
  exact (Submodule.mem_orthogonal _ _).1 h2 _ ⟨⟨_, Submodule.mem_top⟩, rfl⟩

/-- `R(d0) = R(A)` is not closed: `‖e_n‖ = 1`, `‖A e_n‖ = 1/(n+1)` violates the Poincaré
inequality (Thesis Thm 4.2, W-level form `isClosed_range_iff_poincare`). -/
theorem cxW_not_isClosed_range_d0 : ¬ IsClosed (LinearMap.range cxW.d0.toFun : Set L2) := by
  intro h
  obtain ⟨c, hc⟩ := (isClosed_range_iff_poincare cxW.closed0).1 h
  obtain ⟨n, hn⟩ := exists_nat_gt c
  have hk : (lp.single 2 n 1 : L2) ∈ cxW.d0.kerᗮ := by
    rw [cxW_ker_d0, Submodule.bot_orthogonal_eq_top]; trivial
  have := hc ⟨lp.single 2 n 1, Submodule.mem_top⟩ hk
  change ‖(lp.single 2 n 1 : L2)‖ ≤ c * ‖A (lp.single 2 n 1)‖ at this
  rw [norm_single, norm_A_single] at this
  have hc0 : c * (1 / ((n : ℝ) + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  linarith

end FredholmCE

open FredholmCE in
/-- **Refutation of Thesis §4.2 "A Fredholm Hilbert complex is always closed", with the
thesis' (`W`-level) definitions** (critic item 10). The Hilbert complex
`0 → ℓ² --A--> ℓ² --0--> ℝ⁰ → 0`, `A = diag(1/(n+1))`, of closed densely defined (indeed bounded)
operators has all harmonic spaces finite-dimensional — `ℌ⁰ = N(d0) = 0`,
`ℌ¹ = N(d1) ∩ N(d0*) = 0`, `ℌ² = N(d1*) ⊆ ℝ⁰` — so it is Fredholm in the thesis' sense, but it is
not closed (`R(d0)` is not closed). Consequently it also fails the compactness property
(`closedRange_of_compact`), which is therefore a genuine restriction.

Correction: the claim holds with Brüning–Lesch's definition of Fredholm (finite-dimensional
algebraic cohomology `Zᵏ/Bᵏ`), which is `HilbertComplex.isClosedAt_of_finiteDimensional_cohomology`
(at the `W` level: `HilbertComplex2.isClosed_range_d0_of_finiteDimensional_cohomology`,
`UHilbertComplex.isClosed_range_of_finiteDimensional_cohomology`); and
"compactness ⇒ closed and Fredholm" is `HilbertComplex2.closed_and_fredholm_of_compact`. -/
theorem fredholm_not_closed_W :
    cxW.d0.ker = ⊥ ∧ cxW.harmonic = ⊥ ∧
      (FiniteDimensional ℝ cxW.d0.ker ∧ FiniteDimensional ℝ cxW.harmonic ∧
        FiniteDimensional ℝ cxW.d1†.ker) ∧
      ¬ cxW.ClosedRange ∧ ¬ cxW.HasCompactEmbedding := by
  have hnc : ¬ cxW.ClosedRange := fun h => cxW_not_isClosed_range_d0 h.1
  refine ⟨cxW_ker_d0, cxW_harmonic, ⟨?_, ?_, inferInstance⟩, hnc,
    fun h => hnc (cxW.closedRange_of_compact h)⟩
  · rw [cxW_ker_d0]; infer_instance
  · rw [cxW_harmonic]; infer_instance

/-! ### Bridge: `W`-level harmonic forms and compactness versus the bounded model -/

namespace UHilbertComplex

variable {W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : UHilbertComplex W)

/-- In the bridged complex, `u ∈ 𝔷^k` iff the graph component `u.snd = d (u.fst)` vanishes. -/
theorem mem_toHilbertComplex_Z {k : ℕ} (u : C.domainSpace k) :
    u ∈ C.toHilbertComplex.Z k ↔ (u : WithLp 2 (W k × W (k + 1))).snd = 0 := by
  change C.dV k u = 0 ↔ _
  constructor
  · intro h
    exact congrArg (fun w : C.domainSpace (k + 1) =>
      (w : WithLp 2 (W (k + 1) × W (k + 1 + 1))).fst) h
  · intro h
    exact Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext h rfl))

/-- `ι` of a graph-space element is a domain element whose image is the second component. -/
theorem exists_domain (k : ℕ) (u : C.domainSpace k) :
    ∃ y : (C.d k).domain, C.toHilbertComplex.ι k u = y ∧
      (u : WithLp 2 (W k × W (k + 1))).snd = C.d k y := by
  obtain ⟨y, hy1, hy2⟩ := C.mem_domainSpace.1 u.2
  exact ⟨y, hy1.symm, hy2.symm⟩

/-- **Bridge of harmonic forms (Thesis §4.2, `ℌ = Z ∩ (B)ᗮ = Z ∩ Z*`).** The inclusion `ι` maps
the bounded-model harmonic space `ℌ^{k+1} = 𝔅ᗮ ∩ 𝔷 ⊆ V^{k+1}` (graph inner product) onto the
`W`-level harmonic space `N(d_{k+1}) ∩ N(d_k*)` of the segment `W^k → W^{k+1} → W^{k+2}`.

Thesis gap: the thesis identifies the two descriptions in one line via (4.1); here the
identification of `V`- and `W`-orthogonality on cycles (`HilbertComplex.mem_H_iff`) and (4.1a)
are made explicit. -/
theorem map_H_eq_harmonic (k : ℕ) :
    (C.toHilbertComplex.H k).map (C.toHilbertComplex.ι (k + 1)).toLinearMap =
      (C.segment k).harmonic := by
  ext x
  simp only [Submodule.mem_map, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hdu, horth⟩ := C.toHilbertComplex.mem_H_iff.1 hu
    obtain ⟨y, hy, hys⟩ := C.exists_domain (k + 1) u
    have hsnd : (u : WithLp 2 (W (k + 1) × W (k + 1 + 1))).snd = 0 :=
      (C.mem_toHilbertComplex_Z u).1 hdu
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [hy]
      exact (LinearPMap.mem_ker_iff).2 ⟨y, rfl, hys.symm.trans hsnd⟩
    · rw [← (C.segment k).orthogonal_range_d0, Submodule.mem_orthogonal]
      rintro _ ⟨z, rfl⟩
      exact horth (C.graphPt k z)
  · rintro ⟨h1, h0⟩
    obtain ⟨hy, hy0⟩ := exists_apply_eq_zero_of_mem_ker h1
    refine ⟨C.graphPt (k + 1) ⟨x, hy⟩, C.toHilbertComplex.mem_H_iff.2 ⟨?_, fun v => ?_⟩, rfl⟩
    · exact (C.mem_toHilbertComplex_Z _).2 hy0
    · have h0' : x ∈ (LinearMap.range (C.d k).toFun)ᗮ := (C.segment k).orthogonal_range_d0 ▸ h0
      obtain ⟨z, -, hz⟩ := C.exists_domain k v
      have : C.toHilbertComplex.ι (k + 1) (C.toHilbertComplex.d k v) = C.d k z := hz
      rw [this]
      exact (Submodule.mem_orthogonal _ _).1 h0' _ ⟨z, rfl⟩

/-- The bounded-model `ℌ^{k+1}` is finite-dimensional iff the `W`-level `ℌ` of the segment is. -/
theorem finiteDimensional_H_iff_harmonic (k : ℕ) :
    FiniteDimensional ℝ (C.toHilbertComplex.H k) ↔ FiniteDimensional ℝ (C.segment k).harmonic := by
  set f := (C.toHilbertComplex.ι (k + 1)).toLinearMap
  have hinj : Function.Injective f := C.toHilbertComplex.ι_injective (k + 1)
  have e : C.toHilbertComplex.H k ≃ₗ[ℝ] (C.segment k).harmonic :=
    (Submodule.equivMapOfInjective f hinj _).trans (LinearEquiv.ofEq _ _ (C.map_H_eq_harmonic k))
  exact ⟨fun _ => e.finiteDimensional, fun _ => e.symm.finiteDimensional⟩

/-- **The thesis' compactness property implies M5's compactness hypothesis on `(𝔷^{k+1})ᗮ`.**
If `V^{k+1} ∩ V*_{k+1} ↪ W^{k+1}` is compact, then `ι` restricted to `(𝔷^{k+1})^{⊥V}` is a
compact operator.

Thesis gap (filled, also missing from M5): `(𝔷^{k+1})^{⊥V} ⊆ V ∩ V*` with `d* = 0` there, so the
`V`-norm and the `V ∩ V*`-norm agree on it. -/
theorem isCompactOperator_orthogonal_Z (k : ℕ) (hC : (C.segment k).HasCompactEmbedding) :
    IsCompactOperator ((C.toHilbertComplex.ι (k + 1)).comp
      (C.toHilbertComplex.Z (k + 1))ᗮ.subtypeL) := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine ⟨K, hK, Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun w hw => ?_⟩
  rw [mem_ball_zero_iff] at hw
  set u : C.domainSpace (k + 1) := w.1
  obtain ⟨y, hy, hys⟩ := C.exists_domain (k + 1) u
  have hperp : (y : W (k + 1)) ∈ (C.d (k + 1)).kerᗮ := by
    rw [← hy, Submodule.mem_orthogonal']
    intro z hz
    obtain ⟨hz', hz0⟩ := exists_apply_eq_zero_of_mem_ker hz
    have := (C.toHilbertComplex.mem_orthogonal_Z_iff.1 w.2) (C.graphPt (k + 1) ⟨z, hz'⟩)
      ((C.mem_toHilbertComplex_Z _).2 hz0)
    exact this
  obtain ⟨h0, e0⟩ := exists_apply_eq_zero_of_mem_ker ((C.segment k).orthogonal_ker_d1_le hperp)
  change C.toHilbertComplex.ι (k + 1) u ∈ K
  rw [hy]
  refine hsub _ y.2 h0 ?_
  have hn := C.toHilbertComplex.norm_sq_eq (k + 1) u
  have hι : C.toHilbertComplex.ι (k + 1 + 1) (C.toHilbertComplex.d (k + 1) u) =
      C.d (k + 1) y := hys
  rw [hy, hι] at hn
  have e1 : (C.segment k).d1 ⟨(y : W (k + 1)), y.2⟩ = C.d (k + 1) y := rfl
  rw [e0, e1, norm_zero]
  have : ‖u‖ < 1 := hw
  nlinarith [norm_nonneg u]

/-- **The thesis' compactness property implies M5's compactness hypothesis on `ℌ^{k+1}`.** -/
theorem isCompactOperator_H (k : ℕ) (hC : (C.segment k).HasCompactEmbedding) :
    IsCompactOperator ((C.toHilbertComplex.ι (k + 1)).comp (C.toHilbertComplex.H k).subtypeL) := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine ⟨K, hK, Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun w hw => ?_⟩
  rw [mem_ball_zero_iff] at hw
  have hx : C.toHilbertComplex.ι (k + 1) w ∈ (C.segment k).harmonic :=
    C.map_H_eq_harmonic k ▸ Submodule.mem_map_of_mem w.2
  have hnorm : ‖C.toHilbertComplex.ι (k + 1) w‖ = ‖w‖ :=
    (C.toHilbertComplex.norm_of_mem_Z w.2.2).symm
  obtain ⟨h1, e1⟩ := exists_apply_eq_zero_of_mem_ker hx.1
  obtain ⟨h0, e0⟩ := exists_apply_eq_zero_of_mem_ker hx.2
  show C.toHilbertComplex.ι (k + 1) (w : C.domainSpace (k + 1)) ∈ K
  refine hsub _ h1 h0 ?_
  rw [e1, e0, norm_zero, norm_zero, hnorm]
  have : ‖w‖ < 1 := hw
  nlinarith [norm_nonneg w]

/-- **Compactness of `V⁰ ↪ W⁰` gives M5's hypothesis at degree 0.** -/
theorem isCompactOperator_orthogonal_Z_zero (hC : (C.segment 0).HasCompactEmbedding0) :
    IsCompactOperator ((C.toHilbertComplex.ι 0).comp (C.toHilbertComplex.Z 0)ᗮ.subtypeL) := by
  obtain ⟨K, hK, hsub⟩ := hC
  refine ⟨K, hK, Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun w hw => ?_⟩
  rw [mem_ball_zero_iff] at hw
  set u : C.domainSpace 0 := w.1
  obtain ⟨y, hy, hys⟩ := C.exists_domain 0 u
  change C.toHilbertComplex.ι 0 u ∈ K
  rw [hy]
  refine hsub _ y.2 ?_
  have hn := C.toHilbertComplex.norm_sq_eq 0 u
  have hι : C.toHilbertComplex.ι (0 + 1) (C.toHilbertComplex.d 0 u) = C.d 0 y := hys
  rw [hy, hι] at hn
  change ‖(y : W 0)‖ ^ 2 + ‖C.d 0 y‖ ^ 2 ≤ 1
  have : ‖u‖ < 1 := hw
  nlinarith [norm_nonneg u]

/-- **Thesis §4.2, compactness ⇒ closed and Fredholm, for the thesis' unbounded complex**
(critic item 9; the derivation dropped from M5). If `V⁰ ↪ W⁰` and every
`V^{k+1} ∩ V*_{k+1} ↪ W^{k+1}` are compact, then the bounded model is closed at every degree,
all harmonic spaces `ℌ^{k+1}` are finite-dimensional and so is every cohomology space; in `W`,
every `R(d k)` is closed. -/
theorem closed_and_fredholm_of_compact (h0 : (C.segment 0).HasCompactEmbedding0)
    (h : ∀ k, (C.segment k).HasCompactEmbedding) (k : ℕ) :
    C.toHilbertComplex.IsClosedAt k ∧ FiniteDimensional ℝ (C.toHilbertComplex.H k) ∧
      FiniteDimensional ℝ (C.toHilbertComplex.Cohomology k) ∧
      IsClosed (LinearMap.range (C.d k).toFun : Set (W (k + 1))) := by
  have hZ : IsCompactOperator ((C.toHilbertComplex.ι k).comp
      (C.toHilbertComplex.Z k)ᗮ.subtypeL) := by
    cases k with
    | zero => exact C.isCompactOperator_orthogonal_Z_zero h0
    | succ j => exact C.isCompactOperator_orthogonal_Z j (h j)
  obtain ⟨hB, hH, hc⟩ :=
    C.toHilbertComplex.closed_and_fredholm_of_isCompactOperator k hZ (C.isCompactOperator_H k (h k))
  exact ⟨hB, hH, hc, (C.toHilbertComplex_isClosedAt_iff k).1 hB⟩

/-! #### Algebraic cohomology: bounded model versus `W` level -/

/-- `ι : 𝔷^{k+1} ≃ N(d_{k+1})`: cycles of the bounded model are the `W`-level cycles. -/
def cyclesEquiv (k : ℕ) : C.toHilbertComplex.Z (k + 1) ≃ₗ[ℝ] (C.d (k + 1)).ker :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ ((C.toHilbertComplex.ι (k + 1)).toLinearMap.comp
      (C.toHilbertComplex.Z (k + 1)).subtype) fun z => by
        obtain ⟨y, hy, hys⟩ := C.exists_domain (k + 1) z
        refine (LinearPMap.mem_ker_iff).2 ⟨y, hy, ?_⟩
        rw [← hys]
        exact (C.mem_toHilbertComplex_Z _).1 z.2)
    ⟨fun a b hab => Subtype.ext (C.toHilbertComplex.ι_injective (k + 1)
        (congrArg Subtype.val hab)),
      fun x => by
        obtain ⟨hx, hx0⟩ := exists_apply_eq_zero_of_mem_ker x.2
        exact ⟨⟨C.graphPt (k + 1) ⟨x, hx⟩, (C.mem_toHilbertComplex_Z _).2 hx0⟩, rfl⟩⟩

/-- `cyclesEquiv` is `ι`. -/
theorem coe_cyclesEquiv (k : ℕ) (z : C.toHilbertComplex.Z (k + 1)) :
    (C.cyclesEquiv k z : W (k + 1)) = C.toHilbertComplex.ι (k + 1) z := rfl

/-- `cyclesEquiv` maps `𝔅^{k+1}` onto `R(d_k)`. -/
theorem map_cyclesEquiv (k : ℕ) :
    ((C.toHilbertComplex.B k).comap (C.toHilbertComplex.Z (k + 1)).subtype).map
        (C.cyclesEquiv k : _ →ₗ[ℝ] (C.d (k + 1)).ker) =
      (LinearMap.range (C.d k).toFun).comap (C.d (k + 1)).ker.subtype := by
  ext x
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  set w := (C.cyclesEquiv k).symm x
  have hw : C.toHilbertComplex.ι (k + 1) (w : C.domainSpace (k + 1)) = x := by
    rw [← coe_cyclesEquiv, LinearEquiv.apply_symm_apply]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨y, -, hy⟩ := C.exists_domain k v
    refine ⟨y, ?_⟩
    change C.d k y = (x : W (k + 1))
    rw [← hw]
    have hv' : C.toHilbertComplex.d k v = (w : C.domainSpace (k + 1)) := hv
    rw [← hv']
    exact hy.symm
  · rintro ⟨y, hy⟩
    refine ⟨C.graphPt k y, C.toHilbertComplex.ι_injective (k + 1) ?_⟩
    change _ = C.toHilbertComplex.ι (k + 1) (w : C.domainSpace (k + 1))
    rw [hw]
    exact hy

/-- Cohomology in the bounded model ≅ the `W`-level algebraic cohomology
`N(d_{k+1}) / R(d_k)`. -/
def cohomologyEquiv (k : ℕ) :
    C.toHilbertComplex.Cohomology k ≃ₗ[ℝ]
      (C.d (k + 1)).ker ⧸ (LinearMap.range (C.d k).toFun).comap (C.d (k + 1)).ker.subtype :=
  Submodule.Quotient.equiv _ _ (C.cyclesEquiv k) (C.map_cyclesEquiv k)

/-- **Correction of Thesis §4.2 ("Fredholm ⇒ closed"), Brüning–Lesch form at the `W` level:**
if the algebraic cohomology `N(d_{k+1}) / R(d_k)` is finite-dimensional, then `R(d_k)` is closed
in `W^{k+1}`. Transported from the bounded model
(`HilbertComplex.isClosedAt_of_finiteDimensional_cohomology`) via `cohomologyEquiv`. -/
theorem isClosed_range_of_finiteDimensional_cohomology (k : ℕ)
    [FiniteDimensional ℝ ((C.d (k + 1)).ker ⧸
      (LinearMap.range (C.d k).toFun).comap (C.d (k + 1)).ker.subtype)] :
    IsClosed (LinearMap.range (C.d k).toFun : Set (W (k + 1))) := by
  have : FiniteDimensional ℝ (C.toHilbertComplex.Cohomology k) :=
    (C.cohomologyEquiv k).symm.finiteDimensional
  exact (C.toHilbertComplex_isClosedAt_iff k).1
    (C.toHilbertComplex.isClosedAt_of_finiteDimensional_cohomology k)

end UHilbertComplex

/-! ### Bridge: `HilbertComplex2` as an ℕ-indexed complex and as a bounded model -/

namespace HilbertComplex2

universe u

/-- Spaces of the zero-extended complex `0 → W0 → W1 → W2 → 0 → 0 → ⋯` (the zero space is
`⊥ ⊆ W2`, to stay in one universe). -/
def extW (W0 W1 W2 : Type u) [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] : ℕ → Type u
  | 0 => W0
  | 1 => W1
  | 2 => W2
  | _ + 3 => (⊥ : Submodule ℝ W2)

variable {W0 W1 W2 : Type u}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- Norms on the extended spaces. -/
instance instNAGExtW : ∀ k, NormedAddCommGroup (extW W0 W1 W2 k)
  | 0 => inferInstanceAs (NormedAddCommGroup W0)
  | 1 => inferInstanceAs (NormedAddCommGroup W1)
  | 2 => inferInstanceAs (NormedAddCommGroup W2)
  | _ + 3 => inferInstanceAs (NormedAddCommGroup (⊥ : Submodule ℝ W2))

/-- Inner products on the extended spaces. -/
instance instIPSExtW : ∀ k, InnerProductSpace ℝ (extW W0 W1 W2 k)
  | 0 => inferInstanceAs (InnerProductSpace ℝ W0)
  | 1 => inferInstanceAs (InnerProductSpace ℝ W1)
  | 2 => inferInstanceAs (InnerProductSpace ℝ W2)
  | _ + 3 => inferInstanceAs (InnerProductSpace ℝ (⊥ : Submodule ℝ W2))

/-- Completeness of the extended spaces. -/
instance instCSExtW : ∀ k, CompleteSpace (extW W0 W1 W2 k)
  | 0 => inferInstanceAs (CompleteSpace W0)
  | 1 => inferInstanceAs (CompleteSpace W1)
  | 2 => inferInstanceAs (CompleteSpace W2)
  | _ + 3 => inferInstanceAs (CompleteSpace (⊥ : Submodule ℝ W2))

variable (H : HilbertComplex2 W0 W1 W2)

/-- Operators of the zero-extended complex: `d0, d1`, then `0`. -/
def extD : ∀ k, extW W0 W1 W2 k →ₗ.[ℝ] extW W0 W1 W2 (k + 1)
  | 0 => H.d0
  | 1 => H.d1
  | 2 => ((0 : W2 →L[ℝ] (⊥ : Submodule ℝ W2)) : W2 →ₗ[ℝ] (⊥ : Submodule ℝ W2)).toPMap ⊤
  | _ + 3 => ((0 : (⊥ : Submodule ℝ W2) →L[ℝ] (⊥ : Submodule ℝ W2)) :
      (⊥ : Submodule ℝ W2) →ₗ[ℝ] (⊥ : Submodule ℝ W2)).toPMap ⊤

/-- **Bridge (critic item 8).** A length-2 Hilbert complex `W0 → W1 → W2` (the setting of
Thm 4.6/4.7) extended by zero to an ℕ-indexed `UHilbertComplex`; its segment `0` is `H` itself
(`toU_segment_zero`). -/
def toU : UHilbertComplex (extW W0 W1 W2) where
  d := H.extD
  dense
    | 0 => H.dense0
    | 1 => H.dense1
    | 2 => dense_univ
    | _ + 3 => dense_univ
  closed
    | 0 => H.closed0
    | 1 => H.closed1
    | 2 => isClosed_toPMap_top (W0 := W2) (W1 := (⊥ : Submodule ℝ W2)) 0
    | _ + 3 => isClosed_toPMap_top (W0 := (⊥ : Submodule ℝ W2)) (W1 := (⊥ : Submodule ℝ W2)) 0
  map_mem
    | 0 => H.map_mem
    | 1 => fun _ => trivial
    | 2 => fun _ => trivial
    | _ + 3 => fun _ => trivial
  comp_zero
    | 0 => H.comp_zero
    | 1 => fun _ => rfl
    | 2 => fun _ => rfl
    | _ + 3 => fun _ => rfl

/-- The first segment of the extension is the original complex (definitionally). -/
theorem toU_segment_zero : H.toU.segment 0 = H := rfl

/-- **Bridge (critic item 8): the bounded domain complex of a `HilbertComplex2`**, `V k = D(d k)`
with the graph inner product (via the complete graph `UHilbertComplex.domainSpace`). All
bounded-model results (`HilbertComplex.poincare_iff`, `hodge_V`, `harmonicEquivCohomology`, …)
apply to it. -/
abbrev toHilbertComplex := H.toU.toHilbertComplex

/-- Closed at degree 0 in the bounded model ⇔ `R(d0)` closed in `W1`. -/
theorem toHilbertComplex_isClosedAt_zero_iff :
    H.toHilbertComplex.IsClosedAt 0 ↔ IsClosed (LinearMap.range H.d0.toFun : Set W1) :=
  H.toU.toHilbertComplex_isClosedAt_iff 0

/-- Closed at degree 1 in the bounded model ⇔ `R(d1)` closed in `W2`. -/
theorem toHilbertComplex_isClosedAt_one_iff :
    H.toHilbertComplex.IsClosedAt 1 ↔ IsClosed (LinearMap.range H.d1.toFun : Set W2) :=
  H.toU.toHilbertComplex_isClosedAt_iff 1

/-- The zero tail is closed. -/
theorem toHilbertComplex_isClosedAt_add_two (k : ℕ) : H.toHilbertComplex.IsClosedAt (k + 2) := by
  rw [UHilbertComplex.toHilbertComplex_isClosedAt_iff]
  cases k with
  | zero =>
    change IsClosed (LinearMap.range (((0 : W2 →L[ℝ] (⊥ : Submodule ℝ W2)) :
      W2 →ₗ[ℝ] (⊥ : Submodule ℝ W2)).toPMap ⊤).toFun : Set (⊥ : Submodule ℝ W2))
    rw [range_toPMap_top]
    simp
  | succ j =>
    change IsClosed (LinearMap.range (((0 : (⊥ : Submodule ℝ W2) →L[ℝ] (⊥ : Submodule ℝ W2)) :
      (⊥ : Submodule ℝ W2) →ₗ[ℝ] (⊥ : Submodule ℝ W2)).toPMap ⊤).toFun :
        Set (⊥ : Submodule ℝ W2))
    rw [range_toPMap_top]
    simp

/-- `H.ClosedRange` (thesis: closed Hilbert complex) ⇔ the bounded model is closed at every
degree. -/
theorem closedRange_iff_isClosedAt :
    H.ClosedRange ↔ ∀ k, H.toHilbertComplex.IsClosedAt k := by
  constructor
  · rintro ⟨h0, h1⟩ k
    match k with
    | 0 => exact H.toHilbertComplex_isClosedAt_zero_iff.2 h0
    | 1 => exact H.toHilbertComplex_isClosedAt_one_iff.2 h1
    | k + 2 => exact H.toHilbertComplex_isClosedAt_add_two k
  · intro h
    exact ⟨H.toHilbertComplex_isClosedAt_zero_iff.1 (h 0),
      H.toHilbertComplex_isClosedAt_one_iff.1 (h 1)⟩

/-- The bounded-model `ℌ¹` is mapped by `ι` onto `ℌ¹ = N(d1) ∩ N(d0*)` (Thesis §4.2). -/
theorem map_H_zero_eq_harmonic :
    (H.toHilbertComplex.H 0).map (H.toHilbertComplex.ι 1).toLinearMap = H.harmonic :=
  H.toU.map_H_eq_harmonic 0

/-- Compactness at `W2` for `H` is compactness of the middle space of the segment `W1 → W2 → 0`. -/
theorem hasCompactEmbedding_segment_one (h2 : H.HasCompactEmbedding2) :
    (H.toU.segment 1).HasCompactEmbedding := by
  obtain ⟨K, hK, hsub⟩ := h2
  refine ⟨K, hK, fun u h1 h0 hu => hsub u h0 ?_⟩
  have e : (H.toU.segment 1).d1 ⟨u, h1⟩ = 0 := rfl
  rw [e, norm_zero] at hu
  exact (Eq.le (by rw [zero_pow two_ne_zero, add_zero]; rfl)).trans hu

/-- The zero tail trivially has the compactness property. -/
theorem hasCompactEmbedding_segment_add_two (k : ℕ) :
    (H.toU.segment (k + 2)).HasCompactEmbedding := by
  have : FiniteDimensional ℝ (extW W0 W1 W2 (k + 2 + 1)) :=
    inferInstanceAs (FiniteDimensional ℝ (⊥ : Submodule ℝ W2))
  exact HilbertComplex2.hasCompactEmbedding_of_finiteDimensional _

/-- **Thesis §4.2, compactness ⇒ closed and Fredholm, in the bounded model of a
`HilbertComplex2`.** Under the three compact embeddings, the bounded model is closed at every
degree and has finite-dimensional harmonic and cohomology spaces. -/
theorem closed_and_fredholm_V (h0 : H.HasCompactEmbedding0) (h1 : H.HasCompactEmbedding)
    (h2 : H.HasCompactEmbedding2) (k : ℕ) :
    H.toHilbertComplex.IsClosedAt k ∧ FiniteDimensional ℝ (H.toHilbertComplex.H k) ∧
      FiniteDimensional ℝ (H.toHilbertComplex.Cohomology k) := by
  have hall : ∀ j, (H.toU.segment j).HasCompactEmbedding := fun j =>
    match j with
    | 0 => h1
    | 1 => H.hasCompactEmbedding_segment_one h2
    | j + 2 => H.hasCompactEmbedding_segment_add_two j
  obtain ⟨hB, hH, hc, -⟩ := H.toU.closed_and_fredholm_of_compact h0 hall k
  exact ⟨hB, hH, hc⟩

/-- **Correction of Thesis §4.2 ("Fredholm ⇒ closed"), Brüning–Lesch form for a
`HilbertComplex2`:** if `N(d1) / R(d0)` is finite-dimensional then `R(d0)` is closed. -/
theorem isClosed_range_d0_of_finiteDimensional_cohomology
    [hfd : FiniteDimensional ℝ (H.d1.ker ⧸ (LinearMap.range H.d0.toFun).comap H.d1.ker.subtype)] :
    IsClosed (LinearMap.range H.d0.toFun : Set W1) :=
  haveI : FiniteDimensional ℝ ((H.toU.d 1).ker ⧸
      (LinearMap.range (H.toU.d 0).toFun).comap (H.toU.d 1).ker.subtype) := hfd
  H.toU.isClosed_range_of_finiteDimensional_cohomology 0

end HilbertComplex2

end Feec
