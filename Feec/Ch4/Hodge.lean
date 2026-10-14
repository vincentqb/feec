import Feec.Foundation

/-!
# Bounded-model Hodge theory (Thesis §4.2: Thm 4.1, Thm 4.2)

Works in the bounded domain-complex model `Feec.HilbertComplex V W` (`V k` carries the graph
inner product, `ι k : V k → W k` the inclusion). Coverage:

* graph-norm bookkeeping, `(𝔷^k)^{⊥V} = V^k ∩ (𝔷^k)^{⊥W}` (`mem_orthogonal_Z_iff`) and the
  `W`-description of harmonic forms (`mem_H_iff`);
* **Thm 4.2** (Poincaré) with its missing hypothesis (closed range) and missing converse:
  `poincare`, `isClosedAt_of_poincare`, `poincare_iff`, and the `W`-norm forms
  `poincare_W`, `isClosedAt_iff_poincare_W`;
* closed in `V` ⇔ closed in `W` (`isClosedAt_iff_isClosed_image`);
* **Thm 4.1** (Hodge decomposition of `V`), orthogonal in both inner products, with uniqueness:
  `B_sup_H`, `hodge_V`, `hodge_V_orthogonal_W`, `hodge_V_unique`;
* harmonic forms represent cohomology (`harmonicEquivCohomology`), exactness ⇔ `ℌ = 0` under
  closed range;
* **correction of "Fredholm ⇒ closed"**: finite-dimensional algebraic cohomology ⇒ closed
  (`isClosedAt_of_finiteDimensional_cohomology`), and an explicit complex with all harmonic spaces
  zero but non-closed range (`fredholm_not_closed`);
* **bridge** from the thesis' unbounded complex `UHilbertComplex` to the bounded model
  (`UHilbertComplex.toHilbertComplex`), with closed range in `W` ⇔ `IsClosedAt`, and the
  W-level Poincaré equivalence `UHilbertComplex.isClosed_range_iff_poincare`.

Not here: the `W`-level decomposition `W = cl 𝔅 ⊕ ℌ ⊕ cl 𝔅*` (needs adjoints; HodgeW/M4) and the
compactness results (W-level, M16).

Indexing: `C.H k ⊆ V (k+1)` is `ℌ^{k+1}`; `ℌ^0` is `C.H0 = C.Z 0`.
-/

open scoped RealInnerProductSpace
open Set

noncomputable section

namespace Feec
namespace HilbertComplex

variable {V W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : HilbertComplex V W)

/-! ### Graph-norm bookkeeping -/

/-- The graph norm: `‖u‖_V² = ‖u‖_W² + ‖d u‖_W²` (Thesis §4.1, with `‖dv‖` read as `‖Tv‖`). -/
theorem norm_sq_eq (k : ℕ) (u : V k) :
    ‖u‖ ^ 2 = ‖C.ι k u‖ ^ 2 + ‖C.ι (k + 1) (C.d k u)‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using C.inner_graph k u u

/-- The inclusion `V k → W k` has norm at most one. -/
theorem norm_ι_le (k : ℕ) (u : V k) : ‖C.ι k u‖ ≤ ‖u‖ := by
  have h := C.norm_sq_eq k u
  have : ‖C.ι k u‖ ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [sq_nonneg ‖C.ι (k + 1) (C.d k u)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- On cycles the `V`-norm is the `W`-norm. -/
theorem norm_of_mem_Z {k : ℕ} {u : V k} (hu : u ∈ C.Z k) : ‖u‖ = ‖C.ι k u‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, C.inner_of_mem_Z hu]

/-- Boundaries are cycles: `d u ∈ 𝔷^{k+1}` (Thesis §4.2, `d ∘ d = 0`). -/
theorem d_mem_Z (k : ℕ) (u : V k) : C.d k u ∈ C.Z (k + 1) := C.d_d k u

/-- `‖d u‖_V = ‖d u‖_W`, since `d u` is a cycle. -/
theorem norm_d (k : ℕ) (u : V k) : ‖C.d k u‖ = ‖C.ι (k + 1) (C.d k u)‖ :=
  C.norm_of_mem_Z (C.d_mem_Z k u)

/-- `𝔅^{k+1} = d V^k` as a set. -/
theorem coe_B (k : ℕ) : (C.B k : Set (V (k + 1))) = range (C.d k) := rfl

/-! ### `𝔷ᗮ` in `V` versus `W` -/

/-- `(𝔷^k)^{⊥V} = V^k ∩ (𝔷^k)^{⊥W}`: a `v ∈ V` is `V`-orthogonal to the cycles iff it is
`W`-orthogonal to them.

Thesis gap (Thm 4.1): this identity is used but not stated; it holds because
`⟪v, z⟫_V = ⟪v, z⟫_W + ⟪dv, dz⟫_W` and `dz = 0`. -/
theorem mem_orthogonal_Z_iff {k : ℕ} {v : V k} :
    v ∈ (C.Z k)ᗮ ↔ ∀ z ∈ C.Z k, ⟪C.ι k v, C.ι k z⟫ = 0 := by
  rw [Submodule.mem_orthogonal']
  refine forall₂_congr fun z hz => ?_
  rw [real_inner_comm, C.inner_of_mem_Z hz, real_inner_comm]

/-- Harmonic forms, `W`-description: `ℌ^{k+1} = 𝔷^{k+1} ∩ (𝔅^{k+1})^{⊥W}`.
(Thesis §4.2; the `V`- and `W`-orthogonal complements of `𝔅` agree on cycles.) -/
theorem mem_H_iff {k : ℕ} {u : V (k + 1)} :
    u ∈ C.H k ↔ C.d (k + 1) u = 0 ∧ ∀ v : V k, ⟪C.ι (k + 1) (C.d k v), C.ι (k + 1) u⟫ = 0 := by
  rw [H, Submodule.mem_inf, and_comm]
  refine and_congr Iff.rfl ?_
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h v
    rw [← C.inner_of_mem_Z (C.d_mem_Z k v)]
    exact h _ ⟨v, rfl⟩
  · rintro h _ ⟨v, rfl⟩
    exact (C.inner_of_mem_Z (C.d_mem_Z k v)).trans (h v)

/-! ### Thm 4.2: Poincaré inequality ⇔ closed range -/

/-- `d^k` restricted to `(𝔷^k)ᗮ` (in `V`): injective with the same range as `d^k`. -/
def dPerp (k : ℕ) : (C.Z k)ᗮ →L[ℝ] V (k + 1) := (C.d k).comp (C.Z k)ᗮ.subtypeL

/-- `d^k` is injective on `(𝔷^k)ᗮ` (Thesis Thm 4.2, missing step). -/
theorem dPerp_injective (k : ℕ) : Function.Injective (C.dPerp k) := by
  intro x y hxy
  have hmem : (x : V k) - y ∈ C.Z k := by
    change C.d k (x - y) = 0
    simpa [dPerp, sub_eq_zero] using hxy
  have hperp : (x : V k) - y ∈ (C.Z k)ᗮ := sub_mem x.2 y.2
  have := (Submodule.inf_orthogonal_eq_bot (C.Z k)).le ⟨hmem, hperp⟩
  exact Subtype.ext (sub_eq_zero.mp this)

/-- Every boundary is `d` of an element of `(𝔷^k)ᗮ`: `d (u - P_𝔷 u) = d u`. -/
theorem range_dPerp (k : ℕ) : range (C.dPerp k) = range (C.d k) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩
  · rintro _ ⟨u, rfl⟩
    refine ⟨⟨u - (C.Z k).starProjection u, Submodule.sub_starProjection_mem_orthogonal u⟩, ?_⟩
    have h0 : C.d k ((C.Z k).starProjection u) = 0 := (C.Z k).starProjection_apply_mem u
    simp [dPerp, h0]

/-- **Thesis Thm 4.2 (Poincaré inequality).** For a complex closed at `k → k+1` there is `c`
with `‖u‖_V ≤ c ‖d u‖` for all `u ∈ (𝔷^k)^{⊥V}`.

Thesis gap: the hypothesis "closed complex" (`𝔅^{k+1}` closed) is not in the statement, and the
"bounded inverse" step is the Banach open-mapping theorem, which needs `𝔅^{k+1}` complete.
Here: `d^k : (𝔷^k)ᗮ → 𝔅^{k+1}` is injective (`dPerp_injective`), onto (`range_dPerp`), and
antilipschitz by `antilipschitz_of_injective_of_isClosed_range`. -/
theorem poincare (k : ℕ) (hB : C.IsClosedAt k) :
    ∃ c : ℝ, ∀ u ∈ (C.Z k)ᗮ, ‖u‖ ≤ c * ‖C.d k u‖ := by
  have hcl : IsClosed (range (C.dPerp k)) := by rw [range_dPerp]; exact hB
  obtain ⟨K, hK⟩ := (C.dPerp k).antilipschitz_of_injective_of_isClosed_range
    (C.dPerp_injective k) hcl
  refine ⟨K, fun u hu => ?_⟩
  simpa [dPerp] using hK.le_mul_dist ⟨u, hu⟩ 0

/-- **Converse of Thesis Thm 4.2:** a Poincaré inequality on `(𝔷^k)ᗮ` forces `𝔅^{k+1}` to be
closed.

Thesis gap: the converse is not stated, although "compactness ⇒ closed" relies on it. Proof:
`d^k` is antilipschitz on the complete space `(𝔷^k)ᗮ`, so its range is closed. -/
theorem isClosedAt_of_poincare (k : ℕ) {c : ℝ} (hc : ∀ u ∈ (C.Z k)ᗮ, ‖u‖ ≤ c * ‖C.d k u‖) :
    C.IsClosedAt k := by
  have hbd : ∀ x : (C.Z k)ᗮ, ‖x‖ ≤ (c.toNNReal : ℝ) * ‖C.dPerp k x‖ := fun x =>
    (hc x x.2).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal c) (norm_nonneg _))
  have hA := (C.dPerp k).antilipschitz_of_bound hbd
  have := hA.isClosed_range (C.dPerp k).uniformContinuous
  rwa [range_dPerp] at this

/-- **Thesis Thm 4.2, corrected form:** `𝔅^{k+1}` is closed iff a Poincaré inequality holds. -/
theorem poincare_iff (k : ℕ) :
    C.IsClosedAt k ↔ ∃ c : ℝ, ∀ u ∈ (C.Z k)ᗮ, ‖u‖ ≤ c * ‖C.d k u‖ :=
  ⟨C.poincare k, fun ⟨_, hc⟩ => C.isClosedAt_of_poincare k hc⟩

/-- Thesis Thm 4.2, `W`-norm form ("equivalently `‖z‖ ≤ C ‖dz‖`"): for `u ∈ (𝔷^k)ᗮ`,
`‖u‖_W ≤ ‖u‖_V ≤ c ‖d u‖_W`. -/
theorem poincare_W (k : ℕ) (hB : C.IsClosedAt k) :
    ∃ c : ℝ, ∀ u ∈ (C.Z k)ᗮ,
      ‖C.ι k u‖ ≤ ‖u‖ ∧ ‖u‖ ≤ c * ‖C.ι (k + 1) (C.d k u)‖ := by
  obtain ⟨c, hc⟩ := C.poincare k hB
  exact ⟨c, fun u hu => ⟨C.norm_ι_le k u, C.norm_d k u ▸ hc u hu⟩⟩

/-- Thesis Thm 4.2, corrected, entirely in `W`-norms: `𝔅^{k+1}` is closed iff
`‖u‖_W ≤ c ‖d u‖_W` on `(𝔷^k)ᗮ`. (`‖u‖_V ≤ ‖u‖_W + ‖du‖_W` gives the `V`-form.) -/
theorem isClosedAt_iff_poincare_W (k : ℕ) :
    C.IsClosedAt k ↔
      ∃ c : ℝ, ∀ u ∈ (C.Z k)ᗮ, ‖C.ι k u‖ ≤ c * ‖C.ι (k + 1) (C.d k u)‖ := by
  constructor
  · intro hB
    obtain ⟨c, hc⟩ := C.poincare_W k hB
    exact ⟨c, fun u hu => (hc u hu).1.trans (hc u hu).2⟩
  · rintro ⟨c, hc⟩
    refine C.isClosedAt_of_poincare k (c := c + 1) fun u hu => ?_
    have h := C.norm_sq_eq k u
    have hle : ‖u‖ ≤ ‖C.ι k u‖ + ‖C.ι (k + 1) (C.d k u)‖ := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [h]; nlinarith [norm_nonneg (C.ι k u), norm_nonneg (C.ι (k + 1) (C.d k u))]
    rw [C.norm_d k u]
    linarith [hc u hu]

/-! ### Closedness in `V` versus `W` -/

/-- `ι` restricted to the cycles is an isometry into `W`. -/
theorem isometry_ι_Z (k : ℕ) : Isometry (fun z : C.Z k => C.ι k z) := by
  refine AddMonoidHomClass.isometry_of_norm ((C.ι k).comp (C.Z k).subtypeL) fun z => ?_
  exact (C.norm_of_mem_Z z.2).symm

/-- The image of the cycles in `W` is closed (`ker d` is closed in `W`). -/
theorem isClosed_image_Z (k : ℕ) : IsClosed (C.ι k '' C.Z k) := by
  have : CompleteSpace (C.Z k) := (C.isClosed_Z k).completeSpace_coe
  have h := (C.isometry_ι_Z k).isClosedEmbedding.isClosed_range
  convert h using 1
  ext x; simp

/-- Thesis §4.2: "`𝔅^k` is closed in `W^k` (or, equivalently, in `V^k` since the norms for
`W^k` and `V^k` are equivalent on `𝔷^k`, which contains `𝔅^k`)". -/
theorem isClosedAt_iff_isClosed_image (k : ℕ) :
    C.IsClosedAt k ↔ IsClosed (C.ι (k + 1) '' C.B k) := by
  have : CompleteSpace (C.Z (k + 1)) := (C.isClosed_Z (k + 1)).completeSpace_coe
  have hBS : (C.B k : Set (V (k + 1))) =
      Subtype.val '' (Subtype.val ⁻¹' (C.B k : Set (V (k + 1))) : Set (C.Z (k + 1))) := by
    ext x; constructor
    · intro hx; exact ⟨⟨x, C.B_le_Z k hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  unfold IsClosedAt
  rw [hBS, Set.image_image]
  exact ((C.isClosed_Z (k + 1)).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed).symm.trans
    ((C.isometry_ι_Z (k + 1)).isClosedEmbedding.isClosed_iff_image_isClosed)

/-! ### Thm 4.1: Hodge decomposition of `V` -/

/-- **Thesis §4.2 (`𝔷 = 𝔅 ⊕ ℌ`).** Under closed range, cycles split into boundaries and
harmonic forms. -/
theorem B_sup_H (k : ℕ) (hB : C.IsClosedAt k) : C.B k ⊔ C.H k = C.Z (k + 1) := by
  have : CompleteSpace (C.B k) := hB.completeSpace_coe
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (C.B_le_Z k)

/-- `𝔅 ∩ ℌ = 0` (Thesis §4.2). -/
theorem B_inf_H (k : ℕ) : C.B k ⊓ C.H k = ⊥ :=
  eq_bot_iff.2 fun _ hx => (Submodule.inf_orthogonal_eq_bot (C.B k)).le ⟨hx.1, hx.2.1⟩

/-- **Thesis Thm 4.1 (Hodge decomposition, `V`-part).** For a complex closed at `k → k+1`,
`V^{k+1} = 𝔅^{k+1} ⊕ ℌ^{k+1} ⊕ (𝔷^{k+1})^{⊥V}`, orthogonally in the `V` inner product.

Thesis gap: the proof is one sentence; the facts used are `𝔅 ⊆ 𝔷` closed, `𝔷` closed in `V`
(continuity of `d`), and `𝔷 = 𝔅 ⊕ ℌ`. Only closedness of `𝔅^{k+1}` (not of the whole
complex) is needed. -/
theorem hodge_V (k : ℕ) (hB : C.IsClosedAt k) :
    C.B k ⊔ C.H k ⊔ (C.Z (k + 1))ᗮ = ⊤ ∧ C.B k ⟂ C.H k ∧ C.B k ⟂ (C.Z (k + 1))ᗮ ∧
      C.H k ⟂ (C.Z (k + 1))ᗮ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [C.B_sup_H k hB]; exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
  · exact (Submodule.IsOrtho.symm (inf_le_left : C.H k ≤ (C.B k)ᗮ))
  · exact (Submodule.isOrtho_orthogonal_right _).mono_left (C.B_le_Z k)
  · exact (Submodule.isOrtho_orthogonal_right _).mono_left inf_le_right

/-- Thesis Thm 4.1, orthogonality in the `W` inner product as well (the three summands are
pairwise `W`-orthogonal; this uses `dz = 0` on `𝔷`). -/
theorem hodge_V_orthogonal_W (k : ℕ) :
    (∀ b ∈ C.B k, ∀ h ∈ C.H k, ⟪C.ι (k + 1) b, C.ι (k + 1) h⟫ = 0) ∧
    (∀ z ∈ C.Z (k + 1), ∀ w ∈ (C.Z (k + 1))ᗮ, ⟪C.ι (k + 1) z, C.ι (k + 1) w⟫ = 0) := by
  refine ⟨fun b hb h hh => ?_, fun z hz w hw => ?_⟩
  · rw [← C.inner_of_mem_Z (C.B_le_Z k hb)]
    exact (Submodule.mem_orthogonal _ _).1 hh.1 b hb
  · rw [real_inner_comm]; exact C.mem_orthogonal_Z_iff.1 hw z hz

/-- Uniqueness in the Hodge decomposition. -/
theorem hodge_V_unique (k : ℕ) {b b' h h' z z' : V (k + 1)} (hb : b ∈ C.B k) (hb' : b' ∈ C.B k)
    (hh : h ∈ C.H k) (hh' : h' ∈ C.H k) (hz : z ∈ (C.Z (k + 1))ᗮ) (hz' : z' ∈ (C.Z (k + 1))ᗮ)
    (heq : b + h + z = b' + h' + z') : b = b' ∧ h = h' ∧ z = z' := by
  have e1 : (b - b') + (h - h') = z' - z := by
    rw [← sub_eq_zero, ← sub_eq_zero.2 heq]; abel
  have hzz : z' - z ∈ C.Z (k + 1) ⊓ (C.Z (k + 1))ᗮ := by
    refine ⟨?_, sub_mem hz' hz⟩
    rw [← e1]
    exact add_mem (sub_mem (C.B_le_Z k hb) (C.B_le_Z k hb')) (sub_mem hh.2 hh'.2)
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hzz
  rw [hzz] at e1
  have e2 : b - b' = h' - h := by rw [← sub_eq_zero, ← e1]; abel
  have hbb : b - b' ∈ C.B k ⊓ C.H k := ⟨sub_mem hb hb', e2 ▸ sub_mem hh' hh⟩
  rw [B_inf_H, Submodule.mem_bot] at hbb
  rw [hbb] at e2
  exact ⟨sub_eq_zero.1 hbb, (sub_eq_zero.1 e2.symm).symm, (sub_eq_zero.1 hzz).symm⟩

/-! ### Cohomology and harmonic forms -/

/-- Cohomology `H^{k+1} = 𝔷^{k+1} / 𝔅^{k+1}`. -/
abbrev Cohomology (k : ℕ) := C.Z (k + 1) ⧸ (C.B k).comap (C.Z (k + 1)).subtype

/-- The map `ℌ^{k+1} → H^{k+1}`, `h ↦ [h]`. -/
def harmonicToCohomology (k : ℕ) : C.H k →ₗ[ℝ] C.Cohomology k :=
  ((C.B k).comap (C.Z (k + 1)).subtype).mkQ ∘ₗ Submodule.inclusion inf_le_right

/-- Under closed range, `h ↦ [h]` is bijective (Thesis §4.2). -/
theorem harmonicToCohomology_bijective (k : ℕ) (hB : C.IsClosedAt k) :
    Function.Bijective (C.harmonicToCohomology k) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, harmonicToCohomology, LinearMap.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
    have : (x : V (k + 1)) ∈ C.B k ⊓ C.H k := ⟨hx, x.2⟩
    rw [B_inf_H, Submodule.mem_bot] at this
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext this)
  · intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hz : (z : V (k + 1)) ∈ C.B k ⊔ C.H k := (C.B_sup_H k hB).symm ▸ z.2
    obtain ⟨b, hb, h, hh, hbh⟩ := Submodule.mem_sup.1 hz
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [harmonicToCohomology, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq, Submodule.mem_comap]
    change h - (z : V (k + 1)) ∈ C.B k
    rw [← hbh, sub_add_cancel_right]
    exact neg_mem hb

/-- **Thesis §4.2:** under closed range, harmonic forms represent cohomology,
`ℌ^{k+1} ≅ 𝔷^{k+1}/𝔅^{k+1}`. -/
def harmonicEquivCohomology (k : ℕ) (hB : C.IsClosedAt k) : C.H k ≃ₗ[ℝ] C.Cohomology k :=
  LinearEquiv.ofBijective _ (C.harmonicToCohomology_bijective k hB)

/-- **Correction of Thesis §4.2 ("a Fredholm Hilbert complex is always closed"),
Brüning–Lesch version:** if the *algebraic* cohomology `𝔷^{k+1}/𝔅^{k+1}` is
finite-dimensional, then `𝔅^{k+1}` is closed.

Correction: with the thesis' definition of Fredholm (finite-dimensional *harmonic* forms) the
claim is false, see `fredholmCounterexample`. Proof: pick an algebraic complement `G` of `𝔅` in
`𝔷` (finite-dimensional); `(x, g) ↦ d x + g : (𝔷^k)ᗮ × G → 𝔷^{k+1}` is a continuous linear
bijection of Banach spaces, hence a homeomorphism, and `𝔅` is the image of the closed set
`(𝔷^k)ᗮ × {0}`. -/
theorem isClosedAt_of_finiteDimensional_cohomology (k : ℕ)
    [FiniteDimensional ℝ (C.Cohomology k)] : C.IsClosedAt k := by
  have : CompleteSpace (C.Z (k + 1)) := (C.isClosed_Z (k + 1)).completeSpace_coe
  set Z := C.Z (k + 1)
  set B' : Submodule ℝ Z := (C.B k).comap Z.subtype
  obtain ⟨G, hG⟩ := Submodule.exists_isCompl B'
  have : FiniteDimensional ℝ G :=
    LinearEquiv.finiteDimensional (Submodule.quotientEquivOfIsCompl B' G hG)
  have : CompleteSpace G := FiniteDimensional.complete ℝ G
  let δ : (C.Z k)ᗮ →L[ℝ] Z := (C.dPerp k).codRestrict Z fun x => C.d_mem_Z k x
  let Φ : ((C.Z k)ᗮ × G) →L[ℝ] Z :=
    δ.comp (ContinuousLinearMap.fst ℝ _ _) + G.subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)
  have hΦ : ∀ p, (Φ p : V (k + 1)) = C.d k p.1 + (p.2 : Z) := fun p => rfl
  have hδB : ∀ x, δ x ∈ B' := fun x => ⟨x, rfl⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, g⟩ hp
    have hp' : δ x + (g : Z) = 0 := hp
    have hg : (g : Z) ∈ B' ⊓ G := by
      refine ⟨?_, g.2⟩
      rw [eq_neg_of_add_eq_zero_right hp']; exact neg_mem (hδB x)
    rw [hG.inf_eq_bot, Submodule.mem_bot] at hg
    have hg0 : g = 0 := Subtype.ext hg
    rw [hg, add_zero] at hp'
    have hx : x = 0 := C.dPerp_injective k ((congrArg Subtype.val hp').trans (map_zero _).symm)
    simp [hx, hg0]
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨b, hb, g, hg, rfl⟩ := Submodule.mem_sup.1 (hG.sup_eq_top ▸ Submodule.mem_top (x := z))
    obtain ⟨x, hx⟩ : (b : V (k + 1)) ∈ range (C.dPerp k) := by
      rw [range_dPerp]; exact hb
    refine ⟨(x, ⟨g, hg⟩), Subtype.ext ?_⟩
    rw [hΦ]; simp only [Submodule.coe_add]; rw [← hx]; rfl
  let e : ((C.Z k)ᗮ × G) ≃L[ℝ] Z := ContinuousLinearEquiv.ofBijective Φ
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj)
  have hS : (B' : Set Z) = e '' {p | p.2 = 0} := by
    ext z; constructor
    · rintro ⟨u, hu⟩
      obtain ⟨x, hx⟩ : C.d k u ∈ range (C.dPerp k) := by rw [range_dPerp]; exact ⟨u, rfl⟩
      refine ⟨(x, 0), rfl, Subtype.ext ?_⟩
      change (Φ (x, 0) : V (k + 1)) = z
      rw [hΦ]; simp only [ZeroMemClass.coe_zero, add_zero]; exact hx.trans hu
    · rintro ⟨⟨x, g⟩, (hg : g = 0), rfl⟩
      subst hg
      change (Φ (x, 0) : V (k + 1)) ∈ C.B k
      rw [hΦ]; simp only [ZeroMemClass.coe_zero, add_zero]; exact ⟨x, rfl⟩
  have hB' : IsClosed (B' : Set Z) := by
    rw [hS]
    exact e.toHomeomorph.isClosedMap _ (isClosed_eq continuous_snd continuous_const)
  have hBS : (C.B k : Set (V (k + 1))) = Subtype.val '' (B' : Set Z) := by
    ext x; constructor
    · intro hx; exact ⟨⟨x, C.B_le_Z k hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  rw [IsClosedAt, hBS]
  exact (C.isClosed_Z (k + 1)).isClosedEmbedding_subtypeVal.isClosedMap _ hB'

/-- Under closed range the harmonic forms are finite-dimensional iff the cohomology is. -/
theorem finiteDimensional_H_iff (k : ℕ) (hB : C.IsClosedAt k) :
    FiniteDimensional ℝ (C.H k) ↔ FiniteDimensional ℝ (C.Cohomology k) :=
  ⟨fun _ => (C.harmonicEquivCohomology k hB).finiteDimensional,
    fun _ => (C.harmonicEquivCohomology k hB).symm.finiteDimensional⟩

/-- Harmonic `0`-forms `ℌ^0 = 𝔷^0` (there is no `𝔅^0`); `C.H k` only covers `ℌ^{k+1}`. -/
def H0 : Submodule ℝ (V 0) := C.Z 0

/-- Thesis §4.2: an exact complex (`𝔅 = 𝔷`) has no harmonic forms (no closedness needed). -/
theorem H_eq_bot_of_exact (k : ℕ) (h : C.B k = C.Z (k + 1)) : C.H k = ⊥ := by
  rw [H, ← h, inf_comm, Submodule.inf_orthogonal_eq_bot]

/-- Under closed range, `ℌ^{k+1} = 0` iff the complex is exact at `k+1`.
Without closed range the converse fails (`fredholm_not_closed`). -/
theorem exact_iff_H_eq_bot (k : ℕ) (hB : C.IsClosedAt k) :
    C.B k = C.Z (k + 1) ↔ C.H k = ⊥ := by
  refine ⟨C.H_eq_bot_of_exact k, fun h => ?_⟩
  rw [← C.B_sup_H k hB, h, sup_bot_eq]

end HilbertComplex

/-! ### Counterexample to "a Fredholm Hilbert complex is always closed" -/

namespace FredholmCE

/-- `ℓ²(ℕ, ℝ)`. -/
abbrev L2 := lp (fun _ : ℕ => ℝ) 2

/-- `|a/(n+1)| ≤ |a|`. -/
theorem norm_div_succ_le (a : ℝ) (n : ℕ) : ‖a / ((n : ℝ) + 1)‖ ≤ ‖a‖ := by
  rw [norm_div]
  exact div_le_self (norm_nonneg _) (by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; simp)

/-- `diag(1/(n+1))` on `ℓ²`, as a linear map. -/
def diagₗ : L2 →ₗ[ℝ] L2 where
  toFun x := ⟨fun n => x n / ((n : ℝ) + 1), (lp.memℓp x).mono' fun n => norm_div_succ_le _ n⟩
  map_add' x y := lp.ext <| funext fun n => by simp only [lp.coeFn_add, Pi.add_apply, add_div]
  map_smul' c x := lp.ext <| funext fun n => by simp [mul_div_assoc]

/-- `A = diag(1/(n+1)) : ℓ² → ℓ²`: bounded, injective, dense non-closed range. -/
def A : L2 →L[ℝ] L2 :=
  diagₗ.mkContinuous 1 fun x => by
    rw [one_mul]; exact lp.norm_mono two_ne_zero fun n => norm_div_succ_le _ n

/-- `(A x)_n = x_n / (n+1)`. -/
theorem A_apply (x : L2) (n : ℕ) : A x n = x n / ((n : ℝ) + 1) := rfl

/-- `A` is injective. -/
theorem A_injective : Function.Injective A := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine lp.ext <| funext fun n => ?_
  have := congrArg (fun y : L2 => y n) hx
  simp only [A_apply] at this
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simpa [div_eq_zero_iff, hn] using this

/-- `A e_n = e_n / (n+1)`. -/
theorem A_single (n : ℕ) : A (lp.single 2 n 1) = lp.single 2 n (1 / ((n : ℝ) + 1)) := by
  refine lp.ext <| funext fun m => ?_
  rw [A_apply]
  by_cases h : m = n
  · subst h; simp
  · simp [lp.single_apply, Pi.single_eq_of_ne h]

/-- The operators of the complex: `D k = A` for even `k`, `0` for odd `k`. -/
def D (k : ℕ) : L2 →L[ℝ] L2 := if Even k then A else 0

/-- `D k = A` for even `k`. -/
theorem D_of_even {k : ℕ} (hk : Even k) : D k = A := by simp [D, hk]

/-- `D k = 0` for odd `k`. -/
theorem D_of_odd {k : ℕ} (hk : Odd k) : D k = 0 := by
  simp [D, Nat.not_even_iff_odd.2 hk]

/-- `D (k+1) ∘ D k = 0`. -/
theorem D_comp_D (k : ℕ) (x : L2) : D (k + 1) (D k x) = 0 := by
  rcases Nat.even_or_odd k with hk | hk
  · have : ¬ Even (k + 1) := Nat.not_even_iff_odd.2 hk.add_one
    simp [D, this]
  · have : ¬ Even k := Nat.not_even_iff_odd.2 hk
    simp [D, this]

/-- Graph of `D k` in `ℓ² ×₂ ℓ²` (this is the domain space `V k` with its graph norm). -/
def G (k : ℕ) : Submodule ℝ (WithLp 2 (L2 × L2)) :=
  (WithLp.sndL 2 ℝ L2 L2 - (D k).comp (WithLp.fstL 2 ℝ L2 L2)).ker

/-- Membership in the graph of `D k`. -/
theorem mem_G {k : ℕ} {x : WithLp 2 (L2 × L2)} : x ∈ G k ↔ x.snd = D k x.fst := by
  simp [G, sub_eq_zero]

/-- Graphs of bounded maps are closed, hence complete. -/
instance (k : ℕ) : CompleteSpace (G k) :=
  (ContinuousLinearMap.isClosed_ker _).completeSpace_coe

/-- The graph point `(x, D k x)`. -/
def mk (k : ℕ) (x : L2) : G k := ⟨WithLp.toLp 2 (x, D k x), mem_G.2 rfl⟩

/-- Inclusion `V k → W k = ℓ²`, `(x, D x) ↦ x`. -/
def ι (k : ℕ) : G k →L[ℝ] L2 := (WithLp.fstL 2 ℝ L2 L2).comp (G k).subtypeL

/-- The differential `V k → V (k+1)`, `(x, D_k x) ↦ (D_k x, D_{k+1} D_k x)`. -/
def dd (k : ℕ) : G k →L[ℝ] G (k + 1) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ L2 L2).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ L2).prod (D (k + 1)))).comp
    ((WithLp.sndL 2 ℝ L2 L2).comp (G k).subtypeL) |>.codRestrict (G (k + 1)) fun _ => mem_G.2 rfl

/-- First component of `dd k u` is the second component of `u`. -/
theorem dd_fst (k : ℕ) (u : G k) :
    ((dd k u : WithLp 2 (L2 × L2))).fst = (u : WithLp 2 (L2 × L2)).snd :=
  rfl

end FredholmCE

open FredholmCE in
/-- The ℓ² Hilbert complex `ℓ² --A--> ℓ² --0--> ℓ² --A--> ℓ² --0--> ⋯` with
`A = diag(1/(n+1))`, as a bounded domain complex (`V k` = graph of `D k`). -/
def fredholmCounterexample : HilbertComplex (fun k => G k) (fun _ => L2) where
  ι := ι
  ι_injective k u v huv := by
    have h1 : (u : WithLp 2 (L2 × L2)).fst = (v : WithLp 2 (L2 × L2)).fst := huv
    have h2 : (u : WithLp 2 (L2 × L2)).snd = (v : WithLp 2 (L2 × L2)).snd := by
      rw [mem_G.1 u.2, mem_G.1 v.2, h1]
    exact Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext h1 h2))
  d := dd
  d_comp_d k := by
    refine ContinuousLinearMap.ext fun u => Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext ?_ ?_))
    · change D (k + 1) (u : WithLp 2 (L2 × L2)).snd = 0
      rw [mem_G.1 u.2, D_comp_D]
    · change D (k + 2) (D (k + 1) (u : WithLp 2 (L2 × L2)).snd) = 0
      rw [mem_G.1 u.2, D_comp_D]
  inner_graph k u v := by
    change ⟪(u : WithLp 2 (L2 × L2)), (v : WithLp 2 (L2 × L2))⟫ = _
    rw [WithLp.prod_inner_apply]
    rfl


namespace FredholmCE

/-- `𝔷^j = ker A = 0` for even `j`. -/
theorem Z_eq_bot_of_even {j : ℕ} (hj : Even j) : fredholmCounterexample.Z j = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  have hu' : dd j u = 0 := hu
  have h0 : (u : WithLp 2 (L2 × L2)).snd = 0 :=
    congrArg (fun w : G (j + 1) => (w : WithLp 2 (L2 × L2)).fst) hu'
  have h1 : A (u : WithLp 2 (L2 × L2)).fst = 0 := by
    rw [← h0, mem_G.1 u.2, D_of_even hj]
  have h2 := A_injective (h1.trans (map_zero A).symm)
  rw [Submodule.mem_bot]
  exact Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext h2 h0))

/-- All harmonic spaces vanish: for even `k`, `𝔅^{k+1} = range A` is dense; for odd `k`,
`𝔷^{k+1} = ker A = 0`. -/
theorem H_eq_bot (k : ℕ) : fredholmCounterexample.H k = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨-, horth⟩ := fredholmCounterexample.mem_H_iff.1 hu
    have hs : (u : WithLp 2 (L2 × L2)).snd = 0 := by
      rw [mem_G.1 u.2, D_of_odd hk.add_one]; rfl
    have hf : (u : WithLp 2 (L2 × L2)).fst = 0 := by
      refine lp.ext (funext fun n => ?_)
      have := horth (mk k (lp.single 2 n 1))
      change ⟪D k (lp.single 2 n 1), (u : WithLp 2 (L2 × L2)).fst⟫ = 0 at this
      rw [D_of_even hk, A_single, lp.inner_single_left] at this
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      simpa [hn] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext hf hs))
  · have := hu.2
    rwa [Z_eq_bot_of_even hk.add_one] at this

/-- `𝔅^1 = range A` is not closed: `‖e_n‖ = 1` but `‖A e_n‖ = 1/(n+1)` violates Poincaré
(Thm 4.2). -/
theorem not_isClosedAt_zero : ¬ fredholmCounterexample.IsClosedAt 0 := by
  intro hB
  obtain ⟨c, hc⟩ := fredholmCounterexample.poincare 0 hB
  obtain ⟨n, hn⟩ := exists_nat_gt c
  set u := mk 0 (lp.single 2 n 1)
  have h := hc u (by
    rw [Z_eq_bot_of_even (⟨0, rfl⟩ : Even 0), Submodule.bot_orthogonal_eq_top]; trivial)
  have h1 : 1 ≤ ‖u‖ := by
    have := fredholmCounterexample.norm_ι_le 0 u
    have hι : fredholmCounterexample.ι 0 u = lp.single 2 n 1 := rfl
    rwa [hι, lp.norm_single (by norm_num), norm_one] at this
  have h2 : ‖fredholmCounterexample.d 0 u‖ = 1 / ((n : ℝ) + 1) := by
    rw [fredholmCounterexample.norm_d]
    change ‖D 0 (lp.single 2 n 1)‖ = _
    rw [D_of_even (⟨0, rfl⟩ : Even 0), A_single, lp.norm_single (by norm_num), Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [h2, mul_one_div, le_div_iff₀ (by positivity)] at h
  nlinarith

end FredholmCE

open FredholmCE in
/-- **Refutation of Thesis §4.2, "A Fredholm Hilbert complex is always closed".**
With the thesis' definition (Fredholm = all harmonic spaces `ℌ^k` finite-dimensional) the
claim is false: the complex `ℓ² --A--> ℓ² --0--> ℓ² --A--> ⋯`, `A = diag(1/(n+1))`, has
`ℌ^0 = 𝔷^0 = 0` and `ℌ^{k+1} = 0` for all `k` (so it is Fredholm in the thesis' sense), but
`𝔅^1 = range A` is not closed.

Correction: the true statements are "finite-dimensional *algebraic* cohomology ⇒ closed"
(Brüning–Lesch's definition of Fredholm), `isClosedAt_of_finiteDimensional_cohomology`, and
"compactness property ⇒ closed" (W-level model, not stated in this file). -/
theorem fredholm_not_closed :
    fredholmCounterexample.H0 = ⊥ ∧ (∀ k, fredholmCounterexample.H k = ⊥) ∧
      (FiniteDimensional ℝ fredholmCounterexample.H0 ∧
        ∀ k, FiniteDimensional ℝ (fredholmCounterexample.H k)) ∧
      ¬ fredholmCounterexample.IsClosedAt 0 := by
  refine ⟨Z_eq_bot_of_even (⟨0, rfl⟩ : Even 0), H_eq_bot, ⟨?_, fun k => ?_⟩, not_isClosedAt_zero⟩
  · rw [HilbertComplex.H0, Z_eq_bot_of_even (⟨0, rfl⟩ : Even 0)]; infer_instance
  · rw [H_eq_bot]; infer_instance


/-! ### Bridge: the unbounded (W-level) complex as a bounded domain complex -/

namespace UHilbertComplex

variable {W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : UHilbertComplex W)

/-- The domain `V k = D(d k)` with the graph inner product, realised as the graph of `d k`
inside `W k ×₂ W (k+1)`. -/
def domainSpace (k : ℕ) : Submodule ℝ (WithLp 2 (W k × W (k + 1))) :=
  (C.d k).graph.comap (WithLp.linearEquiv 2 ℝ (W k × W (k + 1))).toLinearMap

/-- Membership in the graph space. -/
theorem mem_domainSpace {k : ℕ} {x : WithLp 2 (W k × W (k + 1))} :
    x ∈ C.domainSpace k ↔ ∃ y : (C.d k).domain, (y : W k) = x.fst ∧ C.d k y = x.snd := by
  simp only [domainSpace, Submodule.mem_comap, LinearEquiv.coe_coe, LinearPMap.mem_graph_iff]
  rfl

/-- The graph of the closed operator `d k` is closed. -/
theorem isClosed_domainSpace (k : ℕ) :
    IsClosed (C.domainSpace k : Set (WithLp 2 (W k × W (k + 1)))) :=
  (C.closed k).preimage (WithLp.prod_continuous_ofLp 2 _ _)

/-- The graph space is complete. -/
instance (k : ℕ) : CompleteSpace (C.domainSpace k) := (C.isClosed_domainSpace k).completeSpace_coe

/-- The graph point `(x, d x)` of `x ∈ D(d k)`. -/
def graphPt (k : ℕ) (x : (C.d k).domain) : C.domainSpace k :=
  ⟨WithLp.toLp 2 ((x : W k), C.d k x), C.mem_domainSpace.2 ⟨x, rfl, rfl⟩⟩

/-- `d k` as a bounded map of graph spaces, `(x, d x) ↦ (d x, 0)`. -/
def dV (k : ℕ) : C.domainSpace k →L[ℝ] C.domainSpace (k + 1) :=
  ((((WithLp.prodContinuousLinearEquiv 2 ℝ (W (k + 1)) (W (k + 1 + 1))).symm.toContinuousLinearMap
    |>.comp
    ((ContinuousLinearMap.id ℝ (W (k + 1))).prod 0)).comp
    ((WithLp.sndL 2 ℝ (W k) (W (k + 1))).comp (C.domainSpace k).subtypeL))).codRestrict _
    fun u => by
      obtain ⟨y, -, hy2⟩ := C.mem_domainSpace.1 u.2
      refine C.mem_domainSpace.2 ⟨⟨C.d k y, C.map_mem k y⟩, hy2, ?_⟩
      exact C.comp_zero k y

/-- First component of `dV k u` is `d (ι u)`. -/
theorem dV_fst (k : ℕ) (u : C.domainSpace k) :
    ((C.dV k u : WithLp 2 (W (k + 1) × W (k + 1 + 1)))).fst =
      (u : WithLp 2 (W k × W (k + 1))).snd :=
  rfl

/-- **Thesis §4.2, domain complex.** The thesis' Hilbert complex `(W, d)` (closed, densely
defined `d k`) gives the bounded domain complex `(V, d)`: `V k = D(d k)` with the graph inner
product, `ι k` the inclusion. All bounded-model results (`poincare_iff`, `hodge_V`,
`isClosedAt_of_finiteDimensional_cohomology`, …) apply to it.

Thesis gap: the thesis passes between `(W, d)` and `(V, d)` implicitly; completeness of `V k`
is exactly closedness of `d k`, and `d (V k) ⊆ V (k+1)` is the `map_mem` field. -/
def toHilbertComplex : HilbertComplex (fun k => C.domainSpace k) W where
  ι k := (WithLp.fstL 2 ℝ (W k) (W (k + 1))).comp (C.domainSpace k).subtypeL
  ι_injective k u v huv := by
    have h1 : (u : WithLp 2 (W k × W (k + 1))).fst = (v : WithLp 2 (W k × W (k + 1))).fst := huv
    have h2 : (u : WithLp 2 (W k × W (k + 1))).snd = (v : WithLp 2 (W k × W (k + 1))).snd :=
      (C.d k).mem_graph_snd_inj (x := (u : WithLp 2 (W k × W (k + 1))).fst)
        (x' := (u : WithLp 2 (W k × W (k + 1))).snd) u.2 v.2 h1
    exact Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext h1 h2))
  d := C.dV
  d_comp_d k := by
    refine ContinuousLinearMap.ext fun u => Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext ?_ ?_))
    · rfl
    · rfl
  inner_graph k u v := by
    change ⟪(u : WithLp 2 (W k × W (k + 1))), (v : WithLp 2 (W k × W (k + 1)))⟫ = _
    rw [WithLp.prod_inner_apply]
    rfl

/-- `ι (x, d x) = x`. -/
theorem toHilbertComplex_ι_graphPt (k : ℕ) (x : (C.d k).domain) :
    C.toHilbertComplex.ι k (C.graphPt k x) = x := rfl

/-- In the bridged complex, `ι (d u) = d (ι u)` (the bounded `d` is the thesis' `d`). -/
theorem toHilbertComplex_ι_d (k : ℕ) (u : C.domainSpace k) :
    ∃ y : (C.d k).domain, C.toHilbertComplex.ι k u = y ∧
      C.toHilbertComplex.ι (k + 1) (C.toHilbertComplex.d k u) = C.d k y := by
  obtain ⟨y, hy1, hy2⟩ := C.mem_domainSpace.1 u.2
  exact ⟨y, hy1.symm, hy2.symm⟩

/-- **Bridge (critic item 8):** the bounded model is closed at `k` iff `range (d k)` is closed in
`W (k+1)` (the thesis' definition of a closed complex). -/
theorem toHilbertComplex_isClosedAt_iff (k : ℕ) :
    C.toHilbertComplex.IsClosedAt k ↔
      IsClosed (LinearMap.range (C.d k).toFun : Set (W (k + 1))) := by
  rw [HilbertComplex.isClosedAt_iff_isClosed_image]
  congr! 1
  ext y; constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨x, -, hx⟩ := C.toHilbertComplex_ι_d k u
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨C.graphPt k x, rfl⟩, rfl⟩

/-- **Thesis Thm 4.2 at the W level (corrected):** `range (d k)` is closed in `W (k+1)` iff
`‖x‖ ≤ c ‖d x‖` for all `x ∈ D(d k)` that are `W`-orthogonal to `ker (d k)`. -/
theorem isClosed_range_iff_poincare (k : ℕ) :
    IsClosed (LinearMap.range (C.d k).toFun : Set (W (k + 1))) ↔
      ∃ c : ℝ, ∀ x : (C.d k).domain,
        (∀ z : (C.d k).domain, C.d k z = 0 → ⟪(x : W k), (z : W k)⟫ = 0) →
          ‖(x : W k)‖ ≤ c * ‖C.d k x‖ := by
  rw [← toHilbertComplex_isClosedAt_iff, HilbertComplex.isClosedAt_iff_poincare_W]
  -- `u ∈ 𝔷ᗮ` in the graph space ↔ `ι u ⊥_W ker d`
  have hZ : ∀ u : C.domainSpace k, u ∈ C.toHilbertComplex.Z k ↔
      (u : WithLp 2 (W k × W (k + 1))).snd = 0 := fun u => by
    change C.dV k u = 0 ↔ _
    constructor
    · intro h; exact congrArg (fun w : C.domainSpace (k + 1) =>
        (w : WithLp 2 (W (k + 1) × W (k + 1 + 1))).fst) h
    · intro h
      refine Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext h rfl))
  have hperp : ∀ x : (C.d k).domain, C.graphPt k x ∈ (C.toHilbertComplex.Z k)ᗮ ↔
      ∀ z : (C.d k).domain, C.d k z = 0 → ⟪(x : W k), (z : W k)⟫ = 0 := fun x => by
    rw [HilbertComplex.mem_orthogonal_Z_iff]
    constructor
    · intro h z hz
      exact h (C.graphPt k z) ((hZ _).2 hz)
    · intro h w hw
      obtain ⟨z, hz1, hz2⟩ := C.mem_domainSpace.1 w.2
      have : C.toHilbertComplex.ι k w = z := hz1.symm
      rw [this]
      exact h z (hz2.trans ((hZ w).1 hw))
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x hx => hc (C.graphPt k x) ((hperp x).2 hx)⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, fun u hu => ?_⟩
    obtain ⟨x, hx1, hx2⟩ := C.mem_domainSpace.1 u.2
    have hu' : u = C.graphPt k x :=
      Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext hx1.symm hx2.symm))
    subst hu'
    exact hc x ((hperp x).1 hu)

end UHilbertComplex

end Feec
