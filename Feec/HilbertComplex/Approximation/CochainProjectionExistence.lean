module

public import Feec.HilbertComplex.Approximation.StaticFEEC
public import Feec.HilbertComplex.Homology

/-!
# Bounded cochain projections from discrete stability

The converse of the discrete Poincaré inequality ([AFW2010], Thm 3.7). A finite-dimensional
subcomplex `Vₕ` of a Hilbert complex admits a cochain projection bounded in the graph norm as soon
as, in every degree `j`,

* the **discrete Poincaré inequality** `‖v‖_V ≤ c₁ ‖d v‖` holds on `Vₕʲ ⊥ 𝔷ₕʲ`
  (`Subcomplex.DiscretePoincare`), and
* the **harmonic bound** `‖q‖ ≤ c₂ ‖P_ℌ q‖` holds on the discrete harmonic forms `ℌₕʲ`
  (`Subcomplex.HarmonicBound`).

The projection (`Subcomplex.stableProjection`) is that of the proof of [AFW2010], Thm 3.7,
`πₕ = P_{𝔅ₕ} + Rₕ P_ℌ (I - Qₕ) + Qₕ`, where `Qₕ v ∈ Vₕʲ ⊥ 𝔷ₕʲ` is the discrete lift with
`d Qₕ v = P_{𝔅ₕ} d v` (`Subcomplex.poincareLift`) and `Rₕ` inverts `P_ℌ : ℌₕʲ → ℌʲ` on its range
(`Subcomplex.harmonicLift`); it is bounded by `(1 + c₁)(1 + c₂)` in the graph norm. In the
source `Rₕ` inverts `P_ℌ` on all of `ℌʲ`, which needs `P_ℌ (ℌₕʲ) = ℌʲ`; composing with the
projection onto the range removes that hypothesis. No closed range is needed.

Conversely (`Subcomplex.CochainProjection.discretePoincare`, [AFW2010], Thm 3.6, and
`Subcomplex.CochainProjection.harmonicBound`, [AFW2010], (30)), a projection bounded by `C` in
the graph norm gives both conditions with constants depending only on `C` and the Poincaré
constants of the complex; the harmonic bound needs no closed range, since `π` maps `cl 𝔅ʲ` into
`𝔅ₕʲ` (`Subcomplex.CochainProjection.mem_boundariesW_of_mem_closure`). For a family of
subcomplexes of a complex with closed range (needed for the Poincaré inequality),
**uniformly bounded cochain projections exist iff the two conditions hold uniformly**
(`Subcomplex.exists_isGraphBounded_iff`): the hypothesis `SubcomplexFamily.IsGraphBounded` of
the static FEEC theorem (`SubcomplexFamily.staticFEEC`) is equivalent to discrete stability
(`SubcomplexFamily.exists_isGraphBounded_iff`).

The cochain projections of `Feec` are maps of `Wⁱ`; one defined on the domain complex extends
linearly, not continuously, along an algebraic complement of the domain
(`Subcomplex.CochainProjection.ofDomain`). Graph-norm bounds only involve the domain.

## Main definitions

* `Subcomplex.DiscretePoincare`, `Subcomplex.HarmonicBound`.
* `HilbertComplex.domainProj`, `Subcomplex.CochainProjection.ofDomain`.
* `Subcomplex.poincareLift`, `Subcomplex.harmonicLift`, `Subcomplex.stableProjection`.

## Main results

* **`Subcomplex.exists_cochainProjection`** ([AFW2010], Thm 3.7),
  `Subcomplex.isGraphBounded_stableProjection`.
* `Subcomplex.CochainProjection.discretePoincare`, `Subcomplex.CochainProjection.harmonicBound`.
* **`Subcomplex.exists_isGraphBounded_iff`**, **`SubcomplexFamily.exists_isGraphBounded_iff`**.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3, Thm 3.6, (30), Thm 3.7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

variable (H) in
/-- A linear projection of `Wⁱ` onto the domain `Vⁱ = D(d i (c.next i))`, along an algebraic
complement (not continuous). -/
def domainProj (i : ι) : W i →ₗ[𝕜] (H.d i (c.next i)).domain :=
  Submodule.projectionOnto _ _ (Submodule.exists_isCompl (H.d i (c.next i)).domain).choose_spec

theorem domainProj_apply {i : ι} (x : (H.d i (c.next i)).domain) : H.domainProj i x = x :=
  Submodule.projectionOnto_apply_left _ x

private theorem starProjection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K K' : Submodule 𝕜 E} (h : K = K') [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection]
    (x : E) : K.starProjection x = K'.starProjection x := by
  subst h; rfl

namespace Subcomplex

variable (S : H.Subcomplex)

/-! ### The discrete stability conditions -/

/-- **The discrete Poincaré inequality** in degree `j` with constant `C`, in the graph norm:
`‖v‖_V ≤ C ‖d v‖` for every `v ∈ Vₕʲ` orthogonal to the discrete cycles `𝔷ₕʲ`, stated as
`‖v‖² + ‖d v‖² ≤ C² ‖d v‖²`. [AFW2010], Thm 3.7 -/
def DiscretePoincare (j : ι) (C : ℝ) : Prop :=
  ∀ ⦃x : W j⦄ (hx : x ∈ S.V j), (∀ y ∈ S.cyclesW j, ⟪y, x⟫_𝕜 = 0) →
    ‖x‖ ^ 2 + ‖H.d j (c.next j) ⟨x, S.le_domain j _ hx⟩‖ ^ 2 ≤
      C ^ 2 * ‖H.d j (c.next j) ⟨x, S.le_domain j _ hx⟩‖ ^ 2

/-- `DiscretePoincare` at a related pair `j → k`, with `d j k`. -/
theorem discretePoincare_iff_of_rel {j k : ι} (hjk : c.Rel j k) {C : ℝ} :
    S.DiscretePoincare j C ↔ ∀ ⦃x : W j⦄ (hx : x ∈ S.V j), (∀ y ∈ S.cyclesW j, ⟪y, x⟫_𝕜 = 0) →
      ‖x‖ ^ 2 + ‖H.d j k ⟨x, S.le_domain j k hx⟩‖ ^ 2 ≤
        C ^ 2 * ‖H.d j k ⟨x, S.le_domain j k hx⟩‖ ^ 2 := by
  obtain rfl := c.next_eq' hjk
  rfl

/-- **The harmonic bound** in degree `j` with constant `C`: `‖q‖ ≤ C ‖P_ℌ q‖` for every discrete
harmonic form `q ∈ ℌₕʲ`. [AFW2010], (30), Thm 3.7 -/
def HarmonicBound (j : ι) (C : ℝ) : Prop :=
  ∀ q ∈ S.harmonicW j, ‖q‖ ≤ C * ‖(H.harmonic j).starProjection q‖

/-! ### Cochain projections given on the domain complex -/

/-- **A cochain projection given on the domain complex** `Vⁱ = D(d i (c.next i))`: linear maps
`πⁱ : Vⁱ → Vₕⁱ`, the identity on `Vₕⁱ`, with `d πⁱ = π^{c.next i} d`, extended to `Wⁱ` along an
algebraic complement of `Vⁱ` (`domainProj`). -/
def CochainProjection.ofDomain (π : ∀ i, (H.d i (c.next i)).domain →ₗ[𝕜] W i)
    (mem : ∀ i x, π i x ∈ S.V i)
    (proj : ∀ i (x : (H.d i (c.next i)).domain), (x : W i) ∈ S.V i → π i x = x)
    (comm : ∀ i (x : (H.d i (c.next i)).domain),
      H.d i (c.next i) ⟨π i x, S.le_domain i _ (mem i x)⟩ =
        π (c.next i) ⟨H.d i (c.next i) x, H.mapsTo _ _ _ x⟩) : S.CochainProjection where
  π i := π i ∘ₗ H.domainProj i
  mem i x := mem i _
  proj i x hx := by
    have e : H.domainProj i x = ⟨x, S.le_domain i _ hx⟩ := domainProj_apply ⟨x, _⟩
    rw [LinearMap.comp_apply, e]
    exact proj i _ hx
  comm i j x := by
    by_cases hij : c.Rel i j
    · obtain rfl := c.next_eq' hij
      have e : (⟨(π i ∘ₗ H.domainProj i) x, S.le_domain i _ (mem i _)⟩ :
          (H.d i (c.next i)).domain) = ⟨π i x, S.le_domain i _ (mem i x)⟩ :=
        Subtype.ext (by
          change (π i ∘ₗ H.domainProj i) x = π i x
          rw [LinearMap.comp_apply, domainProj_apply])
      rw [e, comm, LinearMap.comp_apply]
      exact congrArg (π _) (domainProj_apply ⟨_, H.mapsTo _ _ _ x⟩).symm
    · simp only [H.apply_eq_zero_of_not_rel hij, _root_.map_zero]

theorem CochainProjection.ofDomain_apply {π : ∀ i, (H.d i (c.next i)).domain →ₗ[𝕜] W i}
    {mem proj comm} {i : ι} (x : (H.d i (c.next i)).domain) :
    (CochainProjection.ofDomain S π mem proj comm).π i x = π i x := by
  change π i (H.domainProj i x) = π i x
  rw [domainProj_apply]

/-! ### Discrete stability from bounded projections -/

variable {S}

/-- `DiscretePoincare` depends on the constant through its square only. -/
theorem DiscretePoincare.abs {j : ι} {C : ℝ} (h : S.DiscretePoincare j C) :
    S.DiscretePoincare j |C| := fun _ hx hxo => (h hx hxo).trans_eq (by rw [sq_abs])

theorem HarmonicBound.mono {j : ι} {C C' : ℝ} (h : S.HarmonicBound j C) (hC : C ≤ C') :
    S.HarmonicBound j C' := fun q hq =>
  (h q hq).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

variable (S) in
/-- Without a successor degree (`d = 0`), the discrete Poincaré inequality holds with every
constant: the only `v ∈ Vₕʲ` orthogonal to `𝔷ₕʲ = Vₕʲ` is `0`. -/
theorem discretePoincare_of_not_rel {j : ι} (hj : ¬ c.Rel j (c.next j)) (C : ℝ) :
    S.DiscretePoincare j C := fun x hx hxo => by
  have h0 := H.apply_eq_zero_of_not_rel hj ⟨x, S.le_domain j _ hx⟩
  have hx0 : x = 0 :=
    inner_self_eq_zero.1 (hxo x ⟨hx, H.mem_cycles_iff.2 ⟨S.le_domain j _ hx, h0⟩⟩)
  rw [h0, hx0]
  simp

/-- **The discrete Poincaré inequality from a bounded cochain projection** ([AFW2010], Thm 3.6):
if `π` is bounded by `C` in the graph norm and `‖z‖ ≤ c_P ‖d z‖` on `(𝔷ʲ)ᗮ`, then
`‖v‖_V ≤ √(1 + (C √(1 + c_P²))²) ‖d v‖` on `Vₕʲ ⊥ 𝔷ₕʲ`. -/
theorem CochainProjection.discretePoincare (P : S.CochainProjection) {j : ι}
    (hj : c.Rel j (c.next j)) {cP C : ℝ}
    (hP : ∀ z : (H.d j (c.next j)).domain, (z : W j) ∈ (H.cycles j)ᗮ →
      ‖(z : W j)‖ ≤ cP * ‖H.d j (c.next j) z‖)
    (hC : 0 ≤ C) (hπ : P.IsGraphBounded j (c.next j) C) :
    S.DiscretePoincare j √(1 + (C * √(1 + cP ^ 2)) ^ 2) := fun x hx hxo => by
  have h := P.norm_le_of_forall_inner_eq_zero_of_graph hj hP hC hπ hx hxo
  have h2 : ‖x‖ ^ 2 ≤ (C * √(1 + cP ^ 2) * ‖H.d j (c.next j) ⟨x, S.le_domain j _ hx⟩‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Real.sq_sqrt (by positivity)]
  nlinarith

/-- A projection bounded in the graph norm maps `cl 𝔅ʲ` into the finite-dimensional `𝔅ₕʲ`: on
cycles the graph norm is the norm of `W`, so `π` is continuous there. -/
theorem CochainProjection.mem_boundariesW_of_mem_closure {j : ι} [FiniteDimensional 𝕜 (S.V j)]
    (P : S.CochainProjection) {C : ℝ} (hC : 0 ≤ C) (hπ : P.IsGraphBounded j (c.next j) C)
    {b : W j} (hb : b ∈ (H.boundaries j).topologicalClosure) : P.π j b ∈ S.boundariesW j := by
  have : FiniteDimensional 𝕜 (S.boundariesW j) :=
    Submodule.finiteDimensional_of_le (S.boundariesW_le_V j)
  rw [← SetLike.mem_coe, ← (S.boundariesW j).closed_of_finiteDimensional.closure_eq,
    Metric.mem_closure_iff]
  intro ε hε
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hb
  obtain ⟨y, hy, hby⟩ := Metric.mem_closure_iff.1 hb (ε / (C + 1)) (by positivity)
  refine ⟨P.π j y, P.mem_boundariesW hy, ?_⟩
  have hz : b - y ∈ H.cycles j := sub_mem (H.closure_boundaries_le_cycles j (by
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe])) (H.boundaries_le_cycles j hy)
  rw [dist_eq_norm] at hby ⊢
  rw [← _root_.map_sub]
  calc ‖P.π j (b - y)‖ ≤ C * ‖b - y‖ := P.norm_π_le_of_mem_cycles_of_next hC hπ hz
    _ ≤ (C + 1) * ‖b - y‖ := by nlinarith [norm_nonneg (b - y)]
    _ < (C + 1) * (ε / (C + 1)) := by gcongr
    _ = ε := by field_simp

/-- **The harmonic bound from a bounded cochain projection** ([AFW2010], (30)): if `π` is bounded
by `C` in the graph norm, then `‖q‖ ≤ (2 + C) ‖P_ℌ q‖` on `ℌₕʲ` (from
`‖q - P_ℌ q‖ ≤ ‖(I - π) P_ℌ q‖`, [AFW2010], (28)). No closed range is needed:
`q - P_ℌ q ∈ cl 𝔅ʲ` and `π (cl 𝔅ʲ) ⊆ 𝔅ₕʲ`. -/
theorem CochainProjection.harmonicBound {j : ι} [FiniteDimensional 𝕜 (S.V j)]
    (P : S.CochainProjection)
    {C : ℝ} (hC : 0 ≤ C) (hπ : P.IsGraphBounded j (c.next j) C) :
    S.HarmonicBound j (2 + C) := fun q hq => by
  have hqz : q ∈ H.cycles j := S.cyclesW_le_cycles j (S.harmonicW_le_cyclesW j hq)
  have h1 := P.norm_sub_starProjection_harmonic_le_of_mem hq
    (P.mem_boundariesW_of_mem_closure hC hπ (H.mem_closure_boundaries_of_mem_cycles
      (sub_mem hqz (H.harmonic_le_cycles j (Submodule.starProjection_apply_mem _ q)))
      (Submodule.sub_starProjection_mem_orthogonal q)))
  have h2 := P.norm_sub_π_harmonic_le_of_next hC hπ
    (Submodule.starProjection_apply_mem (H.harmonic j) q)
  have h3 := norm_le_norm_sub_add q ((H.harmonic j).starProjection q)
  linarith

variable (S)

/-! ### `P_ℌ` on the discrete harmonic forms -/

/-- `P_ℌ` on the discrete harmonic forms. -/
def harmonicProj (j : ι) : S.harmonicW j →ₗ[𝕜] W j :=
  ((H.harmonic j).starProjection : W j →ₗ[𝕜] W j) ∘ₗ (S.harmonicW j).subtype

theorem harmonicProj_injective {j : ι} {C : ℝ} (h : S.HarmonicBound j C) :
    Function.Injective (S.harmonicProj j) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => Subtype.ext ?_
  have := h q q.2
  change (H.harmonic j).starProjection q = 0 at hq
  rw [hq, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-! ### The Poincaré lift `Qₕ` -/

/-- `Vₕʲ ⊥ 𝔷ₕʲ`: the part of `Vₕʲ` orthogonal to the discrete cycles. -/
def cyclesPerp (j : ι) : Submodule 𝕜 (W j) := S.V j ⊓ (S.cyclesW j)ᗮ

theorem cyclesPerp_le_V (j : ι) : S.cyclesPerp j ≤ S.V j := inf_le_left

/-- `d` on `Vₕʲ ⊥ 𝔷ₕʲ`. -/
def dPerp (j : ι) : S.cyclesPerp j →ₗ[𝕜] W (c.next j) :=
  (S.V (c.next j)).subtype ∘ₗ S.dLin j (c.next j) ∘ₗ Submodule.inclusion (S.cyclesPerp_le_V j)

theorem dPerp_apply (j : ι) (x : S.cyclesPerp j) :
    S.dPerp j x = H.d j (c.next j) ⟨x, S.le_domain j _ (S.cyclesPerp_le_V j x.2)⟩ := rfl

/-- `d` is injective on `Vₕʲ ⊥ 𝔷ₕʲ`. -/
theorem dPerp_injective (j : ι) : Function.Injective (S.dPerp j) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext ?_
  have hz : (x : W j) ∈ S.cyclesW j :=
    ⟨S.cyclesPerp_le_V j x.2, H.mem_cycles_iff.2 ⟨_, (S.dPerp_apply j x).symm.trans hx⟩⟩
  exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hz x.2.2)

/-- `d (Vₕʲ ⊥ 𝔷ₕʲ) = d Vₕʲ`, the discrete boundaries of the next degree. -/
abbrev dRange (j : ι) : Submodule 𝕜 (W (c.next j)) := LinearMap.range (S.dPerp j)

variable [∀ i, FiniteDimensional 𝕜 (S.V i)]

instance (j : ι) : FiniteDimensional 𝕜 (S.cyclesPerp j) :=
  Submodule.finiteDimensional_of_le (S.cyclesPerp_le_V j)

/-- `v - P_{𝔷ₕ} v ∈ Vₕʲ ⊥ 𝔷ₕʲ` for `v ∈ Vₕʲ`. -/
theorem sub_starProjection_mem_cyclesPerp {j : ι} {x : W j} (hx : x ∈ S.V j) :
    x - (S.cyclesW j).starProjection x ∈ S.cyclesPerp j :=
  ⟨sub_mem hx (S.cyclesW_le j (Submodule.starProjection_apply_mem _ x)),
    Submodule.sub_starProjection_mem_orthogonal x⟩

/-- `d v = d (v - P_{𝔷ₕ} v)` for `v ∈ Vₕʲ`. -/
theorem d_sub_starProjection {j : ι} {x : W j} (hx : x ∈ S.V j) :
    S.dPerp j ⟨_, S.sub_starProjection_mem_cyclesPerp hx⟩ =
      H.d j (c.next j) ⟨x, S.le_domain j _ hx⟩ := by
  set p := (S.cyclesW j).starProjection x
  have hp : p ∈ S.cyclesW j := Submodule.starProjection_apply_mem _ x
  have hpd : p ∈ (H.d j (c.next j)).domain := S.le_domain j _ (S.cyclesW_le j hp)
  have e : (⟨x - p, S.le_domain j _ (S.cyclesPerp_le_V j
      (S.sub_starProjection_mem_cyclesPerp hx))⟩ : (H.d j (c.next j)).domain) =
      ⟨x, S.le_domain j _ hx⟩ - ⟨p, hpd⟩ := rfl
  rw [dPerp_apply, e, LinearPMap.map_sub, H.d_eq_zero_of_mem_cycles (S.cyclesW_le_cycles j hp),
    sub_zero]

theorem d_mem_dRange {j : ι} {x : W j} (hx : x ∈ S.V j) :
    H.d j (c.next j) ⟨x, S.le_domain j _ hx⟩ ∈ S.dRange j :=
  ⟨_, S.d_sub_starProjection hx⟩

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- At a related pair `i → k`, the discrete boundaries `𝔅ₕᵏ` are `d Vₕⁱ`. -/
theorem mem_boundariesW_iff_of_rel {i k : ι} (hik : c.Rel i k) {y : W k} :
    y ∈ S.boundariesW k ↔ ∃ x : S.V i, H.d i k ⟨x, S.le_domain i k x.2⟩ = y := by
  obtain rfl := c.prev_eq' hik
  exact Iff.rfl

/-- `d Vₕʲ` is the space `𝔅ₕ` of discrete boundaries of the next degree. -/
theorem dRange_eq {j : ι} (hj : c.Rel j (c.next j)) : S.dRange j = S.boundariesW (c.next j) := by
  ext y
  rw [S.mem_boundariesW_iff_of_rel hj]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, S.cyclesPerp_le_V j x.2⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact S.d_mem_dRange x.2

/-- **The Poincaré lift** `Qₕ : Vʲ → Vₕʲ ⊥ 𝔷ₕʲ`, `d Qₕ v = P_{d Vₕʲ} d v`
([AFW2010], proof of Thm 3.7). -/
def poincareLift (j : ι) : (H.d j (c.next j)).domain →ₗ[𝕜] W j :=
  (S.cyclesPerp j).subtype ∘ₗ (LinearEquiv.ofInjective _ (S.dPerp_injective j)).symm.toLinearMap ∘ₗ
    (S.dRange j).orthogonalProjectionOnto.toLinearMap ∘ₗ (H.d j (c.next j)).toFun

theorem poincareLift_mem (j : ι) (x : (H.d j (c.next j)).domain) :
    S.poincareLift j x ∈ S.cyclesPerp j := Submodule.coe_mem _

theorem poincareLift_mem_V (j : ι) (x : (H.d j (c.next j)).domain) :
    S.poincareLift j x ∈ S.V j := S.cyclesPerp_le_V j (S.poincareLift_mem j x)

theorem d_poincareLift (j : ι) (x : (H.d j (c.next j)).domain) :
    H.d j (c.next j) ⟨S.poincareLift j x, S.le_domain j _ (S.poincareLift_mem_V j x)⟩ =
      (S.dRange j).starProjection (H.d j (c.next j) x) := by
  set e := LinearEquiv.ofInjective _ (S.dPerp_injective j)
  set y := e.symm ((S.dRange j).orthogonalProjectionOnto (H.d j (c.next j) x))
  have h := LinearEquiv.ofInjective_apply (S.dPerp j) (h := S.dPerp_injective j) y
  rw [show e y = _ from e.apply_symm_apply _, Submodule.coe_orthogonalProjectionOnto_apply] at h
  exact (S.dPerp_apply j y).symm.trans h.symm

/-- `v - Qₕ v` is a discrete cycle for `v ∈ Vₕʲ`. -/
theorem sub_poincareLift_mem_cyclesW {j : ι} {x : W j} (hx : x ∈ S.V j) :
    x - S.poincareLift j ⟨x, S.le_domain j _ hx⟩ ∈ S.cyclesW j := by
  refine ⟨sub_mem hx (S.poincareLift_mem_V j _), H.mem_cycles_iff.2
    ⟨S.le_domain j _ (sub_mem hx (S.poincareLift_mem_V j _)), ?_⟩⟩
  have e : (⟨x - S.poincareLift j ⟨x, S.le_domain j _ hx⟩,
      S.le_domain j _ (sub_mem hx (S.poincareLift_mem_V j _))⟩ : (H.d j (c.next j)).domain) =
      ⟨x, S.le_domain j _ hx⟩ - ⟨_, S.le_domain j _ (S.poincareLift_mem_V j _)⟩ := rfl
  rw [e, LinearPMap.map_sub, d_poincareLift, Submodule.starProjection_eq_self_iff.2
    (S.d_mem_dRange hx), sub_self]

/-- `Qₕ` vanishes on cycles. -/
theorem poincareLift_eq_zero {j : ι} (x : (H.d j (c.next j)).domain)
    (hx : (x : W j) ∈ H.cycles j) : S.poincareLift j x = 0 := by
  have h : H.d j (c.next j) x = 0 := H.d_eq_zero_of_mem_cycles hx _
  simp only [poincareLift, LinearMap.comp_apply]
  rw [show (H.d j (c.next j)).toFun x = 0 from h]
  simp

/-! ### The harmonic lift `Rₕ` -/

/-- **The harmonic lift** `Rₕ : Wʲ → ℌₕʲ`: the inverse of the injective `P_ℌ : ℌₕʲ → Wʲ` on its
range, after the orthogonal projection onto the range ([AFW2010], proof of Thm 3.7). -/
def harmonicLift (j : ι) (hinj : Function.Injective (S.harmonicProj j)) : W j →ₗ[𝕜] W j :=
  (S.harmonicW j).subtype ∘ₗ (LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ
    (LinearMap.range (S.harmonicProj j)).orthogonalProjectionOnto.toLinearMap

variable {S}

theorem harmonicLift_mem {j : ι} (hinj : Function.Injective (S.harmonicProj j)) (w : W j) :
    S.harmonicLift j hinj w ∈ S.harmonicW j := Submodule.coe_mem _

/-- `Rₕ P_ℌ q = q` on `ℌₕʲ`. -/
theorem harmonicLift_starProjection {j : ι} (hinj : Function.Injective (S.harmonicProj j))
    {q : W j} (hq : q ∈ S.harmonicW j) :
    S.harmonicLift j hinj ((H.harmonic j).starProjection q) = q := by
  set e := LinearEquiv.ofInjective _ hinj
  have hm : (H.harmonic j).starProjection q ∈ LinearMap.range (S.harmonicProj j) :=
    ⟨⟨q, hq⟩, rfl⟩
  have h1 : (LinearMap.range (S.harmonicProj j)).orthogonalProjectionOnto
      ((H.harmonic j).starProjection q) = e ⟨q, hq⟩ :=
    Subtype.ext (by
      rw [Submodule.coe_orthogonalProjectionOnto_apply, LinearEquiv.ofInjective_apply,
        Submodule.starProjection_eq_self_iff.2 hm]; rfl)
  simp only [harmonicLift, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, h1,
    LinearEquiv.coe_coe, Submodule.subtype_apply]
  rw [show (LinearEquiv.ofInjective _ hinj).symm (e ⟨q, hq⟩) = ⟨q, hq⟩ from e.symm_apply_apply _]

/-- `Rₕ P_ℌ z = z - P_{𝔅ₕ} z` for a discrete cycle `z`: the discrete Hodge decomposition
`z = P_{𝔅ₕ} z + P_{ℌₕ} z`, and `P_ℌ` kills `𝔅ₕ ⊆ 𝔅`. -/
theorem harmonicLift_starProjection_of_mem_cyclesW {j : ι}
    (hinj : Function.Injective (S.harmonicProj j)) {z : W j} (hz : z ∈ S.cyclesW j) :
    S.harmonicLift j hinj ((H.harmonic j).starProjection z) =
      z - (S.boundariesW j).starProjection z := by
  set b := (S.boundariesW j).starProjection z
  have hb : b ∈ S.boundariesW j := Submodule.starProjection_apply_mem _ z
  have hq : z - b ∈ S.harmonicW j :=
    ⟨sub_mem hz (S.boundariesW_le_cyclesW j hb), Submodule.sub_starProjection_mem_orthogonal z⟩
  have h0 : (H.harmonic j).starProjection b = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2
      (H.mem_orthogonal_harmonic_of_mem_boundaries (S.boundariesW_le j hb))
  have e : (H.harmonic j).starProjection z = (H.harmonic j).starProjection (z - b) := by
    rw [_root_.map_sub, h0, sub_zero]
  rw [e, harmonicLift_starProjection hinj hq]

/-- `‖Rₕ w‖ ≤ C ‖w‖` under the harmonic bound with constant `C ≥ 0`. -/
theorem norm_harmonicLift_le {j : ι} (hinj : Function.Injective (S.harmonicProj j)) {C : ℝ}
    (hC : 0 ≤ C) (h : S.HarmonicBound j C) (w : W j) : ‖S.harmonicLift j hinj w‖ ≤ C * ‖w‖ := by
  set M := LinearMap.range (S.harmonicProj j)
  set e := LinearEquiv.ofInjective _ hinj
  set q := e.symm (M.orthogonalProjectionOnto w)
  have hq : (H.harmonic j).starProjection (q : W j) = M.starProjection w := by
    have := LinearEquiv.ofInjective_apply (S.harmonicProj j) (h := hinj) q
    rw [show e q = _ from e.apply_symm_apply _, Submodule.coe_orthogonalProjectionOnto_apply]
      at this
    exact this.symm
  calc ‖S.harmonicLift j hinj w‖ = ‖(q : W j)‖ := rfl
    _ ≤ C * ‖(H.harmonic j).starProjection (q : W j)‖ := h _ q.2
    _ ≤ C * ‖w‖ := by rw [hq]; exact mul_le_mul_of_nonneg_left (M.norm_starProjection_apply_le w) hC

variable (S)

/-! ### The cochain projection -/

/-- The projection `πₕ = P_{𝔅ₕ} + Rₕ P_ℌ (I - Qₕ) + Qₕ` on `Vʲ` ([AFW2010], proof of
Thm 3.7). -/
def stableProj (j : ι) (hinj : Function.Injective (S.harmonicProj j)) :
    (H.d j (c.next j)).domain →ₗ[𝕜] W j :=
  ((S.boundariesW j).starProjection : W j →ₗ[𝕜] W j) ∘ₗ (H.d j (c.next j)).domain.subtype +
    S.harmonicLift j hinj ∘ₗ ((H.harmonic j).starProjection : W j →ₗ[𝕜] W j) ∘ₗ
      ((H.d j (c.next j)).domain.subtype - S.poincareLift j) + S.poincareLift j

theorem stableProj_apply (j : ι) (hinj : Function.Injective (S.harmonicProj j))
    (x : (H.d j (c.next j)).domain) :
    S.stableProj j hinj x = (S.boundariesW j).starProjection x +
      S.harmonicLift j hinj ((H.harmonic j).starProjection (x - S.poincareLift j x)) +
        S.poincareLift j x := rfl

theorem stableProj_mem (j : ι) (hinj : Function.Injective (S.harmonicProj j))
    (x : (H.d j (c.next j)).domain) : S.stableProj j hinj x ∈ S.V j :=
  add_mem (add_mem (S.boundariesW_le_V j (Submodule.starProjection_apply_mem _ _))
    (S.harmonicW_le_V j (harmonicLift_mem hinj _))) (S.poincareLift_mem_V j x)

theorem stableProj_sub_poincareLift_mem_cycles (j : ι)
    (hinj : Function.Injective (S.harmonicProj j)) (x : (H.d j (c.next j)).domain) :
    S.stableProj j hinj x - S.poincareLift j x ∈ H.cycles j := by
  rw [stableProj_apply, add_sub_cancel_right]
  exact add_mem (S.cyclesW_le_cycles j (S.boundariesW_le_cyclesW j
      (Submodule.starProjection_apply_mem _ _)))
    (S.cyclesW_le_cycles j (S.harmonicW_le_cyclesW j (harmonicLift_mem hinj _)))

/-- `d πₕ = P_{𝔅ₕ} d`. -/
theorem d_stableProj (j : ι) (hinj : Function.Injective (S.harmonicProj j))
    (x : (H.d j (c.next j)).domain) :
    H.d j (c.next j) ⟨S.stableProj j hinj x, S.le_domain j _ (S.stableProj_mem j hinj x)⟩ =
      (S.dRange j).starProjection (H.d j (c.next j) x) := by
  have e : (⟨S.stableProj j hinj x, S.le_domain j _ (S.stableProj_mem j hinj x)⟩ :
      (H.d j (c.next j)).domain) =
      ⟨S.stableProj j hinj x - S.poincareLift j x,
        S.le_domain j _ (sub_mem (S.stableProj_mem j hinj x) (S.poincareLift_mem_V j x))⟩ +
      ⟨S.poincareLift j x, S.le_domain j _ (S.poincareLift_mem_V j x)⟩ :=
    Subtype.ext (sub_add_cancel _ _).symm
  rw [e, LinearPMap.map_add, H.d_eq_zero_of_mem_cycles
    (S.stableProj_sub_poincareLift_mem_cycles j hinj x), zero_add, d_poincareLift]

theorem stableProj_of_mem (j : ι) (hinj : Function.Injective (S.harmonicProj j))
    (x : (H.d j (c.next j)).domain) (hx : (x : W j) ∈ S.V j) : S.stableProj j hinj x = x := by
  have hz := S.sub_poincareLift_mem_cyclesW hx
  have hQ : (S.boundariesW j).starProjection (S.poincareLift j x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2
      (Submodule.orthogonal_le (S.boundariesW_le_cyclesW j) (S.poincareLift_mem j x).2)
  have hB : (S.boundariesW j).starProjection (x : W j) =
      (S.boundariesW j).starProjection ((x : W j) - S.poincareLift j x) := by
    rw [_root_.map_sub, hQ, sub_zero]
  rw [stableProj_apply, harmonicLift_starProjection_of_mem_cyclesW hinj hz, hB]
  abel

/-- **The cochain projection of discrete stability** `πₕ = P_{𝔅ₕ} + Rₕ P_ℌ (I - Qₕ) + Qₕ`
([AFW2010], proof of Thm 3.7), defined when `P_ℌ` is injective on every `ℌₕʲ`. -/
def stableProjection (hinj : ∀ j, Function.Injective (S.harmonicProj j)) : S.CochainProjection :=
  CochainProjection.ofDomain S (fun j => S.stableProj j (hinj j))
    (fun j => S.stableProj_mem j (hinj j)) (fun j => S.stableProj_of_mem j (hinj j)) fun j x => by
    rw [d_stableProj, stableProj_apply,
      S.poincareLift_eq_zero _ (H.mem_cycles_iff.2 ⟨_, H.d_comp_d _ _ _ x⟩), sub_zero,
      add_zero]
    by_cases hj : c.Rel j (c.next j)
    · have hB : H.d j (c.next j) x ∈ H.boundaries (c.next j) := by
        rw [H.boundaries_eq hj]; exact ⟨x, rfl⟩
      rw [(Submodule.starProjection_apply_eq_zero_iff _).2
          (H.mem_orthogonal_harmonic_of_mem_boundaries hB),
        _root_.map_zero, add_zero]
      exact starProjection_congr (S.dRange_eq hj) _
    · have h0 : H.d j (c.next j) x = 0 := H.apply_eq_zero_of_not_rel hj x
      simp only [h0, _root_.map_zero, add_zero]

theorem stableProjection_apply (hinj : ∀ j, Function.Injective (S.harmonicProj j)) {j : ι}
    (x : (H.d j (c.next j)).domain) : (S.stableProjection hinj).π j x = S.stableProj j (hinj j) x :=
  CochainProjection.ofDomain_apply S x

private theorem graph_bound_aux {a e q p b r n c₁ c₂ : ℝ} (hp0 : 0 ≤ p) (hb0 : 0 ≤ b)
    (hr0 : 0 ≤ r) (hn0 : 0 ≤ n) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hpe : p ≤ e) (hQ : q ^ 2 + p ^ 2 ≤ c₁ ^ 2 * p ^ 2) (hb : b ≤ a) (hr : r ≤ c₂ * (a + q))
    (hn : n ≤ b + r + q) : n ^ 2 + p ^ 2 ≤ ((1 + c₁) * (1 + c₂)) ^ 2 * (a ^ 2 + e ^ 2) := by
  have hqp : q ≤ c₁ * p := (abs_le_of_sq_le_sq' (by nlinarith) (by positivity)).2
  have h1 : n ^ 2 + p ^ 2 ≤ (b + r + c₁ * p) ^ 2 := by
    have : n ^ 2 ≤ (b + r + q) ^ 2 := pow_le_pow_left₀ hn0 hn 2
    nlinarith
  have h2 : b + r + c₁ * p ≤ (1 + c₂) * (a + c₁ * e) := by
    nlinarith [mul_le_mul_of_nonneg_left hqp hc₂,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + c₂) hc₁) (sub_nonneg.2 hpe)]
  have h3 : (a + c₁ * e) ^ 2 ≤ (1 + c₁) ^ 2 * (a ^ 2 + e ^ 2) := by
    nlinarith [sq_nonneg (c₁ * a - e), mul_nonneg hc₁ (add_nonneg (sq_nonneg a) (sq_nonneg e))]
  calc n ^ 2 + p ^ 2 ≤ (b + r + c₁ * p) ^ 2 := h1
    _ ≤ ((1 + c₂) * (a + c₁ * e)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    _ = (1 + c₂) ^ 2 * (a + c₁ * e) ^ 2 := by ring
    _ ≤ (1 + c₂) ^ 2 * ((1 + c₁) ^ 2 * (a ^ 2 + e ^ 2)) := by gcongr
    _ = _ := by ring

/-- **The cochain projection of discrete stability is bounded in the graph norm** by
`(1 + c₁)(1 + c₂)` in degree `j`, under the discrete Poincaré inequality with constant `c₁` and
the harmonic bound with constant `c₂` in that degree. [AFW2010], Thm 3.7 -/
theorem isGraphBounded_stableProjection (hinj : ∀ j, Function.Injective (S.harmonicProj j))
    {j : ι} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hP : S.DiscretePoincare j c₁)
    (hH : S.HarmonicBound j c₂) :
    (S.stableProjection hinj).IsGraphBounded j (c.next j) ((1 + c₁) * (1 + c₂)) := fun x => by
  have e : (⟨(S.stableProjection hinj).π j x, S.le_domain j _ ((S.stableProjection hinj).mem j x)⟩ :
      (H.d j (c.next j)).domain) =
      ⟨S.stableProj j (hinj j) x, S.le_domain j _ (S.stableProj_mem j (hinj j) x)⟩ :=
    Subtype.ext (S.stableProjection_apply hinj x)
  rw [e, d_stableProj, S.stableProjection_apply hinj x]
  set Q := S.poincareLift j x
  have hQ := hP (S.poincareLift_mem_V j x) fun y hy =>
    Submodule.inner_right_of_mem_orthogonal hy (S.poincareLift_mem j x).2
  rw [d_poincareLift] at hQ
  have hr := norm_harmonicLift_le (hinj j) hc₂ hH ((H.harmonic j).starProjection ((x : W j) - Q))
  have hr' : ‖(H.harmonic j).starProjection ((x : W j) - Q)‖ ≤ ‖(x : W j)‖ + ‖Q‖ :=
    ((H.harmonic j).norm_starProjection_apply_le _).trans (norm_sub_le _ _)
  rw [stableProj_apply]
  exact graph_bound_aux (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hc₁ hc₂
    ((S.dRange j).norm_starProjection_apply_le _) hQ
    ((S.boundariesW j).norm_starProjection_apply_le _)
    (hr.trans (mul_le_mul_of_nonneg_left hr' hc₂)) (norm_add₃_le)

/-- **Bounded cochain projections from discrete stability** ([AFW2010], Thm 3.7). If, in every
degree `j`, the discrete Poincaré inequality `‖v‖_V ≤ c₁ʲ ‖d v‖` holds on `Vₕʲ ⊥ 𝔷ₕʲ` and
`‖q‖ ≤ c₂ʲ ‖P_ℌ q‖` holds on `ℌₕʲ`, then `Vₕ` has a cochain projection bounded in the graph norm
by `(1 + c₁ʲ)(1 + c₂ʲ)` in every degree `j`. No closed range is assumed. -/
theorem exists_cochainProjection {c₁ c₂ : ι → ℝ} (hc₁ : ∀ j, 0 ≤ c₁ j) (hc₂ : ∀ j, 0 ≤ c₂ j)
    (hP : ∀ j, S.DiscretePoincare j (c₁ j)) (hH : ∀ j, S.HarmonicBound j (c₂ j)) :
    ∃ P : S.CochainProjection, ∀ j, P.IsGraphBounded j (c.next j) ((1 + c₁ j) * (1 + c₂ j)) :=
  ⟨S.stableProjection fun j => S.harmonicProj_injective (hH j), fun j =>
    S.isGraphBounded_stableProjection _ (hc₁ j) (hc₂ j) (hP j) (hH j)⟩

/-- **Bounded cochain projections exist iff the discrete stability conditions hold**
([AFW2010], Thms 3.6, 3.7 and (30)): for a family `Vₕ` of finite-dimensional subcomplexes of a
Hilbert complex with closed range, there are cochain projections `πₕ` bounded in the graph norm
uniformly in `h` in every degree iff, in every degree, the discrete Poincaré inequality on
`Vₕʲ ⊥ 𝔷ₕʲ` and the harmonic bound `‖q‖ ≤ c ‖P_ℌ q‖` on `ℌₕʲ` hold uniformly in `h`. -/
theorem exists_isGraphBounded_iff {κ : Type*} (V : κ → H.Subcomplex)
    [∀ h i, FiniteDimensional 𝕜 ((V h).V i)] (hcr : ∀ i, H.ClosedRangeAt i) :
    (∃ π : ∀ h, (V h).CochainProjection, ∀ i, ∃ C, ∀ h, (π h).IsGraphBounded i (c.next i) C) ↔
      ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).DiscretePoincare i c₁ ∧ (V h).HarmonicBound i c₂ := by
  refine ⟨fun ⟨π, hπ⟩ i => ?_, fun hV => ?_⟩
  · obtain ⟨C, hC⟩ := hπ i
    have hC' : ∀ h, (π h).IsGraphBounded i (c.next i) |C| := fun h x =>
      (hC h x).trans_eq (by rw [sq_abs])
    have hH := fun h => (π h).harmonicBound (abs_nonneg C) (hC' h)
    by_cases hi : c.Rel i (c.next i)
    · obtain ⟨cP, -, hP⟩ := H.exists_poincare_of_closedRangeAt hi (hcr _)
      exact ⟨_, _, fun h => ⟨(π h).discretePoincare hi hP (abs_nonneg C) (hC' h), hH h⟩⟩
    · exact ⟨0, _, fun h => ⟨(V h).discretePoincare_of_not_rel hi 0, hH h⟩⟩
  · choose c₁ c₂ hc using hV
    refine ⟨fun h => (V h).stableProjection fun i => (V h).harmonicProj_injective (hc i h).2,
      fun i => ⟨(1 + |c₁ i|) * (1 + max (c₂ i) 0), fun h =>
        (V h).isGraphBounded_stableProjection _ (abs_nonneg _) (le_max_right _ _)
          (hc i h).1.abs ((hc i h).2.mono (le_max_left _ _))⟩⟩

end Subcomplex

/-- **The hypothesis of the static FEEC theorem is discrete stability** ([AFW2010], Thms 3.6, 3.7
and (30)): for finite-dimensional subcomplexes `Vₕ` of a Hilbert complex with closed range, refined
along `l`, there is a family of subcomplexes `G` on `Vₕ` with projections bounded in the graph norm
uniformly in `h` (`SubcomplexFamily.IsGraphBounded`, the hypothesis of
`SubcomplexFamily.staticFEEC`) in every degree iff, in every degree, the discrete Poincaré
inequality on `Vₕʲ ⊥ 𝔷ₕʲ` and the harmonic bound on `ℌₕʲ` hold uniformly in `h`. -/
theorem SubcomplexFamily.exists_isGraphBounded_iff {κ : Type*} (l : Filter κ)
    (V : κ → H.Subcomplex) [∀ h i, FiniteDimensional 𝕜 ((V h).V i)] (hcr : ∀ i, H.ClosedRangeAt i) :
    (∃ G : SubcomplexFamily H κ, G.l = l ∧ G.V = V ∧ ∀ i, G.IsGraphBounded i) ↔
      ∀ i, ∃ c₁ c₂ : ℝ, ∀ h, (V h).DiscretePoincare i c₁ ∧ (V h).HarmonicBound i c₂ := by
  rw [← Subcomplex.exists_isGraphBounded_iff V hcr]
  refine ⟨?_, fun ⟨π, hπ⟩ => ⟨⟨l, V, π⟩, rfl, rfl, hπ⟩⟩
  rintro ⟨G, -, rfl, hG⟩
  exact ⟨G.π, hG⟩

end Feec.HilbertComplex
