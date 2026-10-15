module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Feec.Ch4.Existence

/-!
# Stone's theorem for skew-adjoint operators on a real Hilbert space

The thesis takes existence of time evolutions (Thm 4.3) from a corollary of the Hille–Yosida
theorem ([CazenaveHaraux1998, Prop 4.1.6, Cor 2.4.9]); Mathlib has neither Hille–Yosida nor
Stone. The project therefore carried existence as the hypothesis structure
`Feec.UnitaryGroupGenerator` (`Feec.Ch4.Existence`). This module proves it: every skew-adjoint
operator on a real Hilbert space generates a strongly continuous orthogonal group, whose
generator is exactly the operator, domain included. Conversely every such generator is
skew-adjoint, and the group is unique.

## Main results

* `Feec.IsSkewAdjoint.dense_domain`: `A† = -A` forces `D(A)` dense (Mathlib's adjoint is junk
  `0` off dense domains), so density is never a separate hypothesis.
* The resolvent: for real `z ≠ 0`, `z - A : D(A) → E` is bijective
  (`IsSkewSymm.shiftOp_injective`, `IsSkewAdjoint.shiftOp_surjective`: closed range from
  `|z| ‖x‖ ≤ ‖(z - A) x‖`, dense range from `ker (z + A) = 0`), and
  `resolvent hA z = (z - A)⁻¹` has `‖R(z)‖ ≤ 1/|z|` (`norm_resolvent_apply_le`), adjoint
  `-R(-z)` (`inner_resolvent_left`), and satisfies the resolvent identity (`resolvent_sub`);
  resolvents commute (`resolvent_commute`).
* Bounded skew approximants (`approxB`): `B_n = (c²/2)(R(c) + R(-c)) = c² A (c² - A²)⁻¹`,
  `c = n + 1`. They are skew (`approxB_skew`), commute (`approxB_commute`), and
  `B_n x = J_n (A x) → A x` on `D(A)` (`tendsto_approxB`), where
  `J_n = c² (c² - A²)⁻¹ → 1` strongly (`tendsto_approxJ`).
* The group: `exp(t B_n)` (`approxU`, `NormedSpace.exp`) is orthogonal, and
  `‖e^{tB_n} x - e^{tB_m} x‖ ≤ |t| ‖B_n x - B_m x‖` (`norm_approxU_sub_le`), so it converges
  strongly; the limit `stoneS hA t` (`tendsto_approxU`) is a group of isometries
  (`stoneS_zero`, `stoneS_add`, `norm_stoneS_apply`), strongly continuous
  (`continuous_stoneS_apply`), with `S(t) x - x = ∫₀ᵗ S(s) A x ds` on `D(A)`
  (`stoneS_sub_eq_integral`).
* **`Feec.stoneGroup hA : UnitaryGroupGenerator A`** for every skew-adjoint `A`. The generator
  domain is exactly `D(A)` (`mem_domain_iff_differentiableAt_stoneS`): differentiability of
  `t ↦ S(t) x` at `0` puts `x` in `D(A†) = D(A)`.
* Converse and uniqueness: `UnitaryGroupGenerator.dense_domain`,
  `UnitaryGroupGenerator.isSkewAdjoint` (the generator of an orthogonal group is skew-adjoint),
  `UnitaryGroupGenerator.S_eq` (the group is determined by its generator, by an energy
  argument), `UnitaryGroupGenerator.S_eq_stoneS`, and Stone's theorem in the form
  `isSkewAdjoint_iff_nonempty_unitaryGroupGenerator`.

The consequences for Ch. 4 (Thm 4.3, Cor 4.5, Thm 4.6, Props 4.17/4.19 without existence
hypotheses) are in `Feec.Ch4.StoneApplications`.

Remark (choice of approximant): the Yosida approximant `c A (c - A)⁻¹` of a
skew-adjoint `A` is dissipative, not skew (for `A = iω` it is `(icω - ω²) c/(c² + ω²)`), so its
exponential is only a contraction semigroup. The symmetrized approximant `B_n` above is skew,
so all approximating groups are orthogonal and the group law passes to the limit directly.

Thesis gap: Thm 4.3 is cited, not proved, in the thesis; here its existence input (the
homogeneous group) is proved for every skew-adjoint operator.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3), §4.4 (Thm 4.6)
* [Pazy1983], §1.10 (Stone's theorem) and Ch. 1 (Hille–Yosida, Yosida approximation)
* [Brezis2011], Ch. 7 (Hille–Yosida; the self-adjoint and skew-adjoint cases)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (the results cited by the thesis for Thm 4.3)
* [Kato1995] (resolvents and the resolvent identity for closed operators)
-/

open scoped RealInnerProductSpace Topology
open Set Filter NormedSpace LinearPMap

@[expose] public noncomputable section

namespace Feec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

/-! ### Skew-adjoint operators are densely defined -/

/-- A skew-adjoint operator (`A† = -A`) is densely defined. As for Mathlib's
`IsSelfAdjoint.dense_domain`, this is not part of the definition: the adjoint of a non-densely
defined operator is `0` on its domain, which forces `A = 0` on `D(A)`, hence `D(A) = E`. -/
theorem IsSkewAdjoint.dense_domain (hA : IsSkewAdjoint A) : Dense (A.domain : Set E) := by
  by_contra h
  have hle : A† ≤ -A := hA ▸ le_rfl
  have hzero : ∀ x : A.domain, A x = 0 := by
    intro x
    have hx : (x : E) ∈ A†.domain := by rw [hA]; exact x.2
    have h2 : A† ⟨x, hx⟩ = (-A) x := hle.2 rfl
    rw [adjoint_apply_of_not_dense h, LinearPMap.neg_apply] at h2
    exact neg_eq_zero.1 h2.symm
  have htop : A.domain = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have hy : y ∈ A†.domain := by
      rw [mem_adjoint_domain_iff]
      have : (innerₛₗ ℝ y).comp A.toFun = 0 := by
        ext x; simp [hzero x]
      rw [this]; exact continuous_zero
    rw [hA] at hy; exact hy
  exact h (by rw [htop]; simp [dense_univ])

/-- Membership in `D(A†)` with `A† y = w` transfers to `D(A)` with `A y = -w` for skew-adjoint
`A`. -/
theorem IsSkewAdjoint.mem_domain_of_adjoint (hA : IsSkewAdjoint A) {y w : E}
    (h : ∀ x : A.domain, ⟪w, (x : E)⟫ = ⟪y, A x⟫) :
    ∃ hy : y ∈ A.domain, A ⟨y, hy⟩ = -w := by
  have hya : y ∈ A†.domain := mem_adjoint_domain_of_exists y ⟨w, h⟩
  have hval : A† ⟨y, hya⟩ = w := adjoint_apply_eq hA.dense_domain ⟨y, hya⟩ h
  have hle : A† ≤ -A := hA ▸ le_rfl
  have hy : y ∈ A.domain := hle.1 hya
  refine ⟨hy, ?_⟩
  have h2 : A† ⟨y, hya⟩ = (-A) ⟨y, hy⟩ := hle.2 rfl
  rw [hval, LinearPMap.neg_apply] at h2
  rw [h2, neg_neg]

/-! ### The shifted operator `z - A` and the resolvent -/

/-- `z - A : D(A) → E`. -/
def shiftOp (A : E →ₗ.[ℝ] E) (z : ℝ) : A.domain →ₗ[ℝ] E := z • A.domain.subtype - A.toFun

omit [CompleteSpace E] in
/-- `(z - A) x = z x - A x`. -/
@[simp] theorem shiftOp_apply (z : ℝ) (x : A.domain) : shiftOp A z x = z • (x : E) - A x := rfl

omit [CompleteSpace E] in
/-- `⟪A x, x⟫ = 0` for skew-symmetric `A`. -/
theorem IsSkewSymm.inner_self_eq_zero (hS : IsSkewSymm A) (x : A.domain) : ⟪A x, (x : E)⟫ = 0 := by
  have := hS x x
  rw [real_inner_comm (A x) (x : E)] at this
  linarith

omit [CompleteSpace E] in
/-- `‖(z - A) x‖² = z² ‖x‖² + ‖A x‖²` for skew-symmetric `A`. -/
theorem IsSkewSymm.norm_sq_shiftOp (hS : IsSkewSymm A) (z : ℝ) (x : A.domain) :
    ‖shiftOp A z x‖ ^ 2 = z ^ 2 * ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 := by
  rw [shiftOp_apply, norm_sub_sq_real, real_inner_smul_left, real_inner_comm,
    hS.inner_self_eq_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

omit [CompleteSpace E] in
/-- `|z| ‖x‖ ≤ ‖(z - A) x‖` for skew-symmetric `A`. -/
theorem IsSkewSymm.abs_mul_norm_le (hS : IsSkewSymm A) (z : ℝ) (x : A.domain) :
    |z| * ‖(x : E)‖ ≤ ‖shiftOp A z x‖ := by
  rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, hS.norm_sq_shiftOp,
    mul_pow, sq_abs]
  nlinarith [sq_nonneg ‖A x‖]

omit [CompleteSpace E] in
/-- `z - A` is injective for skew-symmetric `A` and `z ≠ 0`. -/
theorem IsSkewSymm.shiftOp_injective (hS : IsSkewSymm A) {z : ℝ} (hz : z ≠ 0) :
    Function.Injective (shiftOp A z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := hS.abs_mul_norm_le z x
  rw [hx, norm_zero] at h
  have : ‖(x : E)‖ = 0 :=
    le_antisymm (by nlinarith [abs_pos.2 hz, norm_nonneg (x : E)]) (norm_nonneg _)
  exact Subtype.ext (norm_eq_zero.1 this)

/-- The range of `z - A` is orthogonal to nothing: `(range (z - A))ᗮ = ⊥` (for `z ≠ 0`). -/
theorem IsSkewAdjoint.orthogonal_range_shiftOp (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) :
    (LinearMap.range (shiftOp A z))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have h : ∀ x : A.domain, ⟪z • y, (x : E)⟫ = ⟪y, A x⟫ := by
    intro x
    have := hy _ ⟨x, rfl⟩
    rw [shiftOp_apply, inner_sub_left, real_inner_smul_left, real_inner_comm y,
      real_inner_comm y] at this
    rw [real_inner_smul_left]; linarith
  obtain ⟨hyD, hAy⟩ := hA.mem_domain_of_adjoint h
  have h0 : shiftOp A (-z) ⟨y, hyD⟩ = 0 := by
    rw [shiftOp_apply, hAy]; simp
  have := (hA.isSkewSymm hA.dense_domain).shiftOp_injective (neg_ne_zero.2 hz)
    (h0.trans (_root_.map_zero _).symm)
  exact congrArg Subtype.val this

/-- The range of `z - A` is closed (for `z ≠ 0`). -/
theorem IsSkewAdjoint.isClosed_range_shiftOp (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) :
    IsClosed (LinearMap.range (shiftOp A z) : Set E) := by
  have hS := hA.isSkewSymm hA.dense_domain
  refine IsSeqClosed.isClosed fun {u y} hu huy => ?_
  choose x hx using hu
  have hz' : 0 < |z| := abs_pos.2 hz
  -- `x n` is Cauchy
  have hc : CauchySeq fun n => (x n : E) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 huy.cauchySeq (|z| * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hS.abs_mul_norm_le z (x m - x n)
    rw [_root_.map_sub, hx, hx, ← dist_eq_norm] at h1
    have h2 := hN m hm n hn
    rw [dist_eq_norm, ← Submodule.coe_sub]
    nlinarith
  obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hc
  have h : ∀ w : A.domain, ⟪y - z • x₀, (w : E)⟫ = ⟪x₀, A w⟫ := by
    intro w
    have l1 : Tendsto (fun n => ⟪(x n : E), A w⟫) atTop (𝓝 ⟪x₀, A w⟫) :=
      hx₀.inner tendsto_const_nhds
    have l2 : Tendsto (fun n => ⟪u n - z • (x n : E), (w : E)⟫) atTop (𝓝 ⟪y - z • x₀, (w : E)⟫) :=
      (huy.sub (hx₀.const_smul z)).inner tendsto_const_nhds
    refine tendsto_nhds_unique l2 (l1.congr fun n => ?_)
    rw [← hx n, shiftOp_apply, sub_sub_cancel_left, inner_neg_left, hS (x n) w]
    ring
  obtain ⟨hD, hAx⟩ := hA.mem_domain_of_adjoint h
  exact ⟨⟨x₀, hD⟩, by rw [shiftOp_apply, hAx]; abel⟩

/-- `z - A : D(A) → E` is surjective for skew-adjoint `A` and `z ≠ 0`. -/
theorem IsSkewAdjoint.shiftOp_surjective (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) :
    Function.Surjective (shiftOp A z) := by
  rw [← LinearMap.range_eq_top, ← (hA.isClosed_range_shiftOp hz).submodule_topologicalClosure_eq,
    Submodule.topologicalClosure_eq_top_iff]
  exact hA.orthogonal_range_shiftOp hz

/-- `z - A` as a linear equivalence `D(A) ≃ E` (skew-adjoint `A`, `z ≠ 0`). -/
def shiftEquiv (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) : A.domain ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (shiftOp A z)
    ⟨(hA.isSkewSymm hA.dense_domain).shiftOp_injective hz, hA.shiftOp_surjective hz⟩

/-- `(z - A)⁻¹ y ∈ D(A)`, as an element of the domain. -/
def resD (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) : A.domain := (shiftEquiv hA hz).symm y

/-- `(z - A) R(z) y = y`. -/
theorem shiftOp_resD (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    z • (resD hA hz y : E) - A (resD hA hz y) = y :=
  (shiftEquiv hA hz).apply_symm_apply y

/-- `R(z) (z - A) x = x` on `D(A)`. -/
theorem resD_shiftOp (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (x : A.domain) :
    resD hA hz (z • (x : E) - A x) = x :=
  (shiftEquiv hA hz).symm_apply_apply x

/-- `‖R(z) y‖ ≤ |z|⁻¹ ‖y‖`. -/
theorem norm_resD_le (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    ‖(resD hA hz y : E)‖ ≤ |z|⁻¹ * ‖y‖ := by
  have h := (hA.isSkewSymm hA.dense_domain).abs_mul_norm_le z (resD hA hz y)
  rw [shiftOp_apply, shiftOp_resD] at h
  rw [le_inv_mul_iff₀ (abs_pos.2 hz)]
  exact h

/-- The resolvent `R(z) = (z - A)⁻¹ : E →L[ℝ] E` of a skew-adjoint operator, for real `z ≠ 0`
(junk value `0` at `z = 0`), with `‖R(z)‖ ≤ 1/|z|`. -/
def resolvent (hA : IsSkewAdjoint A) (z : ℝ) : E →L[ℝ] E :=
  if hz : z = 0 then 0 else
    LinearMap.mkContinuous (A.domain.subtype ∘ₗ (shiftEquiv hA hz).symm.toLinearMap) (|z|⁻¹)
      (norm_resD_le hA hz)

/-- `R(z) y` is the domain element `resD hA hz y`. -/
theorem resolvent_apply (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    resolvent hA z y = (resD hA hz y : E) := by
  simp only [resolvent, hz, dite_false]
  rfl

/-- `‖R(z)‖ ≤ 1/|z|` (Hille–Yosida resolvent bound for skew-adjoint `A`). -/
theorem norm_resolvent_apply_le (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    ‖resolvent hA z y‖ ≤ |z|⁻¹ * ‖y‖ := by
  rw [resolvent_apply hA hz]; exact norm_resD_le hA hz y

/-- `A R(z) y = z R(z) y - y`. -/
theorem apply_resD (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    A (resD hA hz y) = z • resolvent hA z y - y := by
  rw [resolvent_apply hA hz]
  have h := shiftOp_resD hA hz y
  set u := resD hA hz y
  rw [← h, sub_sub_cancel]

/-- `R(z) (A x) = z R(z) x - x` on `D(A)`; i.e. `R(z)` commutes with `A`. -/
theorem resolvent_apply_domain (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (x : A.domain) :
    resolvent hA z (A x) = z • resolvent hA z x - x := by
  have h : A x = z • (x : E) - (z • (x : E) - A x) := by abel
  rw [h, _root_.map_sub, _root_.map_smul, resolvent_apply hA hz (z • (x : E) - A x),
    resD_shiftOp]

/-- `⟪R(z) x, y⟫ = -⟪x, R(-z) y⟫`: the adjoint of `R(z)` is `-R(-z) = (z + A)⁻¹`. -/
theorem inner_resolvent_left (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (x y : E) :
    ⟪resolvent hA z x, y⟫ = -⟪x, resolvent hA (-z) y⟫ := by
  have hS := hA.isSkewSymm hA.dense_domain
  have hz' : -z ≠ 0 := neg_ne_zero.2 hz
  set u := resD hA hz x
  set v := resD hA hz' y
  have hx : x = z • (u : E) - A u := (shiftOp_resD hA hz x).symm
  have hy : y = (-z) • (v : E) - A v := (shiftOp_resD hA hz' y).symm
  rw [resolvent_apply hA hz, resolvent_apply hA hz']
  conv_lhs => rw [hy]
  conv_rhs => rw [hx]
  have := hS u v
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  linarith

/-- The resolvent identity `R(z) - R(w) = (w - z) R(z) R(w)`. -/
theorem resolvent_sub (hA : IsSkewAdjoint A) {z w : ℝ} (hz : z ≠ 0) (hw : w ≠ 0) (y : E) :
    resolvent hA z y - resolvent hA w y = (w - z) • resolvent hA z (resolvent hA w y) := by
  set u := resD hA hw y
  have hu : (z • (u : E) - A u) = (z - w) • (u : E) + y := by
    rw [← shiftOp_resD hA hw y]; simp only [u, sub_smul]; abel
  have h := congrArg (fun v => (resolvent hA z v)) hu
  rw [resolvent_apply hA hz (z • (u : E) - A u), resD_shiftOp, _root_.map_add, _root_.map_smul]
    at h
  rw [resolvent_apply hA hw y]
  change resolvent hA z y - (u : E) = (w - z) • resolvent hA z u
  calc resolvent hA z y - (u : E)
      = resolvent hA z y - ((z - w) • resolvent hA z u + resolvent hA z y) := by rw [← h]
    _ = (w - z) • resolvent hA z u := by module

/-- Resolvents commute. -/
theorem resolvent_commute (hA : IsSkewAdjoint A) {z w : ℝ} (hz : z ≠ 0) (hw : w ≠ 0) :
    Commute (resolvent hA z) (resolvent hA w) := by
  rcases eq_or_ne z w with rfl | hzw
  · exact Commute.refl _
  ext y
  have h1 := resolvent_sub hA hz hw y
  have h2 := resolvent_sub hA hw hz y
  have h3 : (w - z) • resolvent hA z (resolvent hA w y) =
      (w - z) • resolvent hA w (resolvent hA z y) := by
    rw [← h1, show w - z = -(z - w) by ring, neg_smul, ← h2]; abel
  exact smul_right_injective E (sub_ne_zero.2 hzw.symm) h3

/-! ### Bounded skew approximants

For `c = n + 1`, `J_n = (c/2) (R(c) - R(-c)) = c² (c² - A²)⁻¹` and
`B_n = (c²/2) (R(c) + R(-c)) = A J_n = c² A (c² - A²)⁻¹`. Unlike the Yosida approximant
`c A (c - A)⁻¹` (which is only dissipative), `B_n` is bounded and skew, so `exp(t B_n)` is an
orthogonal group. -/

/-- The scale `c_n = n + 1`. -/
def scale (n : ℕ) : ℝ := (n : ℝ) + 1

/-- `c_n > 0`. -/
theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

/-- `c_n ≠ 0`. -/
theorem scale_ne_zero (n : ℕ) : scale n ≠ 0 := (scale_pos n).ne'

/-- `-c_n ≠ 0`. -/
theorem neg_scale_ne_zero (n : ℕ) : -scale n ≠ 0 := neg_ne_zero.2 (scale_ne_zero n)

/-- `J_n = (c/2) (R(c) - R(-c))`, a contraction converging strongly to the identity. -/
def approxJ (hA : IsSkewAdjoint A) (n : ℕ) : E →L[ℝ] E :=
  (scale n / 2) • (resolvent hA (scale n) - resolvent hA (-scale n))

/-- `B_n = (c²/2) (R(c) + R(-c))`, a bounded skew operator with `B_n x = J_n (A x)` on `D(A)`. -/
def approxB (hA : IsSkewAdjoint A) (n : ℕ) : E →L[ℝ] E :=
  (scale n ^ 2 / 2) • (resolvent hA (scale n) + resolvent hA (-scale n))

/-- `B_n` is skew: `⟪B_n x, y⟫ = -⟪x, B_n y⟫` (from `R(c)† = -R(-c)`). -/
theorem approxB_skew (hA : IsSkewAdjoint A) (n : ℕ) (x y : E) :
    ⟪approxB hA n x, y⟫ = -⟪x, approxB hA n y⟫ := by
  simp only [approxB, _root_.smul_apply, _root_.add_apply,
    real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    inner_resolvent_left hA (scale_ne_zero n), inner_resolvent_left hA (neg_scale_ne_zero n),
    neg_neg]
  ring

/-- `B_n x = J_n (A x)` on `D(A)`. -/
theorem approxB_apply_domain (hA : IsSkewAdjoint A) (n : ℕ) (x : A.domain) :
    approxB hA n x = approxJ hA n (A x) := by
  simp only [approxB, approxJ, _root_.smul_apply, _root_.add_apply,
    _root_.sub_apply, resolvent_apply_domain hA (scale_ne_zero n),
    resolvent_apply_domain hA (neg_scale_ne_zero n)]
  module

/-- `‖J_n‖ ≤ 1`. -/
theorem norm_approxJ_apply_le (hA : IsSkewAdjoint A) (n : ℕ) (y : E) :
    ‖approxJ hA n y‖ ≤ ‖y‖ := by
  have h1 := norm_resolvent_apply_le hA (scale_ne_zero n) y
  have h2 := norm_resolvent_apply_le hA (neg_scale_ne_zero n) y
  have hc := scale_pos n
  rw [abs_neg, abs_of_pos hc] at h2
  rw [abs_of_pos hc] at h1
  simp only [approxJ, _root_.smul_apply, _root_.sub_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (half_pos hc)]
  calc scale n / 2 * ‖resolvent hA (scale n) y - resolvent hA (-scale n) y‖
      ≤ scale n / 2 * (‖resolvent hA (scale n) y‖ + ‖resolvent hA (-scale n) y‖) := by
        gcongr; exact norm_sub_le _ _
    _ ≤ scale n / 2 * ((scale n)⁻¹ * ‖y‖ + (scale n)⁻¹ * ‖y‖) := by gcongr
    _ = ‖y‖ := by field_simp; ring

/-- `‖B_n x‖ ≤ ‖A x‖` on `D(A)`. -/
theorem norm_approxB_apply_domain_le (hA : IsSkewAdjoint A) (n : ℕ) (x : A.domain) :
    ‖approxB hA n x‖ ≤ ‖A x‖ := by
  rw [approxB_apply_domain]; exact norm_approxJ_apply_le hA n _

/-- `‖J_n y - y‖ ≤ ‖A y‖ / c_n` on `D(A)`. -/
theorem norm_approxJ_sub_le (hA : IsSkewAdjoint A) (n : ℕ) (y : A.domain) :
    ‖approxJ hA n y - y‖ ≤ ‖A y‖ / scale n := by
  have hc := scale_pos n
  have e1 := resolvent_apply_domain hA (scale_ne_zero n) y
  have e2 := resolvent_apply_domain hA (neg_scale_ne_zero n) y
  have h : approxJ hA n y - y =
      (1 / 2 : ℝ) • (resolvent hA (scale n) (A y) + resolvent hA (-scale n) (A y)) := by
    rw [e1, e2]
    simp only [approxJ, _root_.smul_apply, _root_.sub_apply]
    module
  have h1 := norm_resolvent_apply_le hA (scale_ne_zero n) (A y)
  have h2 := norm_resolvent_apply_le hA (neg_scale_ne_zero n) (A y)
  rw [abs_neg, abs_of_pos hc] at h2
  rw [abs_of_pos hc] at h1
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc 1 / 2 * ‖resolvent hA (scale n) (A y) + resolvent hA (-scale n) (A y)‖
      ≤ 1 / 2 * (‖resolvent hA (scale n) (A y)‖ + ‖resolvent hA (-scale n) (A y)‖) := by
        gcongr; exact norm_add_le _ _
    _ ≤ 1 / 2 * ((scale n)⁻¹ * ‖A y‖ + (scale n)⁻¹ * ‖A y‖) := by gcongr
    _ = ‖A y‖ / scale n := by field_simp; ring

/-- `c_n → ∞`. -/
theorem tendsto_scale_atTop : Tendsto scale atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

omit [CompleteSpace E] in
/-- Strong convergence on a dense set plus a uniform bound `‖T n x‖ ≤ ‖x‖` gives strong
convergence everywhere. -/
theorem tendsto_apply_of_dense {T : ℕ → E →L[ℝ] E} (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) {D : Set E}
    (hD : Dense D) (h : ∀ x ∈ D, Tendsto (fun n => T n x) atTop (𝓝 x)) (x : E) :
    Tendsto (fun n => T n x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.1 hD x (ε / 3) (by positivity)
  rw [Metric.mem_ball] at hd
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h d hdD) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : dist (T n x) (T n d) ≤ dist x d := by
    rw [dist_eq_norm, dist_eq_norm, ← _root_.map_sub]; exact hT n _
  have := hN n hn
  calc dist (T n x) x ≤ dist (T n x) (T n d) + dist (T n d) d + dist d x :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have hd' : dist x d < ε / 3 := by rwa [dist_comm]
        linarith
    _ = ε := by ring

/-- `J_n y → y` for every `y`. -/
theorem tendsto_approxJ (hA : IsSkewAdjoint A) (y : E) :
    Tendsto (fun n => approxJ hA n y) atTop (𝓝 y) := by
  refine tendsto_apply_of_dense (norm_approxJ_apply_le hA) hA.dense_domain ?_ y
  rintro x hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_approxJ_sub_le hA n ⟨x, hx⟩) ?_
  exact tendsto_const_nhds.div_atTop tendsto_scale_atTop

/-- `B_n x → A x` on `D(A)`. -/
theorem tendsto_approxB (hA : IsSkewAdjoint A) (x : A.domain) :
    Tendsto (fun n => approxB hA n x) atTop (𝓝 (A x)) := by
  simp_rw [approxB_apply_domain]; exact tendsto_approxJ hA _

/-- The approximants commute (resolvents commute). -/
theorem approxB_commute (hA : IsSkewAdjoint A) (n m : ℕ) :
    Commute (approxB hA n) (approxB hA m) := by
  have h : ∀ z w : ℝ, z ≠ 0 → w ≠ 0 → Commute (resolvent hA z) (resolvent hA w) :=
    fun z w hz hw => resolvent_commute hA hz hw
  have hn := scale_ne_zero n; have hm := scale_ne_zero m
  have hn' := neg_scale_ne_zero n; have hm' := neg_scale_ne_zero m
  unfold approxB
  refine ((Commute.add_left ?_ ?_).smul_left _).smul_right _ <;> refine Commute.add_right ?_ ?_
  all_goals apply h <;> assumption

omit [CompleteSpace E] in
/-- Strong Cauchy-ness on a dense set plus a uniform bound `‖T n x‖ ≤ ‖x‖` gives strong
Cauchy-ness everywhere. -/
theorem cauchySeq_apply_of_dense {T : ℕ → E →L[ℝ] E} (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) {D : Set E}
    (hD : Dense D) (h : ∀ x ∈ D, CauchySeq fun n => T n x) (x : E) :
    CauchySeq fun n => T n x := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.1 hD x (ε / 3) (by positivity)
  rw [Metric.mem_ball, dist_comm] at hd
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (h d hdD) (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 : ∀ k, dist (T k x) (T k d) ≤ dist x d := fun k => by
    rw [dist_eq_norm, dist_eq_norm, ← _root_.map_sub]; exact hT k _
  have := hN m hm n hn
  have h2 := h1 n
  rw [dist_comm] at h2
  calc dist (T m x) (T n x) ≤ dist (T m x) (T m d) + dist (T m d) (T n d) + dist (T n d) (T n x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h1 m]
    _ = ε := by ring

/-! ### The approximating groups `exp(t B_n)` and their strong limit -/

/-- `ℚ`-algebra structure on operators, needed by `NormedSpace.exp_add_of_commute`. -/
local instance instNormedAlgebraRatOpStone : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- For skew `B`, `‖exp(tB) x - x‖ ≤ |t| ‖B x‖` (mean value theorem; `exp(sB)` is an isometry
commuting with `B`). Same statement as `Feec.Torus.norm_exp_smul_sub_le`, reproved here to
keep this module independent of the periodic model. -/
theorem norm_exp_smul_sub_le_of_skew {B : E →L[ℝ] E} (hB : ∀ x y, ⟪B x, y⟫ = -⟪x, B y⟫)
    (t : ℝ) (x : E) : ‖exp (t • B) x - x‖ ≤ |t| * ‖B x‖ := by
  have hd : ∀ s ∈ (univ : Set ℝ), HasDerivWithinAt (fun s : ℝ => exp (s • B) x)
      (exp (s • B) (B x)) univ s := by
    intro s _
    have h := hasDerivAt_exp_smul_apply B x s
    have hc : B (exp (s • B) x) = exp (s • B) (B x) := by
      have : Commute B (exp (s • B)) := ((Commute.refl B).smul_right s).exp_right
      exact congrArg (fun C : E →L[ℝ] E => C x) this.eq
    rw [hc] at h
    exact h.hasDerivWithinAt
  have := (convex_univ).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun s _ => (norm_exp_smul_apply hB s (B x)).le) (mem_univ 0) (mem_univ t)
  simpa [zero_smul, exp_zero, Real.norm_eq_abs, mul_comm] using this

/-- The approximating orthogonal groups `U_n(t) = exp(t B_n)`. -/
def approxU (hA : IsSkewAdjoint A) (n : ℕ) (t : ℝ) : E →L[ℝ] E := exp (t • approxB hA n)

/-- `exp(t B_n)` is an isometry. -/
theorem norm_approxU_apply (hA : IsSkewAdjoint A) (n : ℕ) (t : ℝ) (x : E) :
    ‖approxU hA n t x‖ = ‖x‖ :=
  norm_exp_smul_apply (approxB_skew hA n) t x

/-- Group law for `exp(t B_n)`. -/
theorem approxU_add (hA : IsSkewAdjoint A) (n : ℕ) (s t : ℝ) :
    approxU hA n (s + t) = approxU hA n s * approxU hA n t :=
  exp_smul_add _ s t

/-- `‖e^{tB_n} x - e^{tB_m} x‖ ≤ |t| ‖B_n x - B_m x‖` (the approximants commute). -/
theorem norm_approxU_sub_le (hA : IsSkewAdjoint A) (n m : ℕ) (t : ℝ) (x : E) :
    ‖approxU hA n t x - approxU hA m t x‖ ≤ |t| * ‖approxB hA n x - approxB hA m x‖ := by
  set D := approxB hA n - approxB hA m
  have hD : ∀ x y, ⟪D x, y⟫ = -⟪x, D y⟫ := fun x y => by
    simp only [D, _root_.sub_apply, inner_sub_left, inner_sub_right, approxB_skew]; ring
  have hcomm : Commute (t • approxB hA m) (t • D) :=
    (((approxB_commute hA m n).sub_right (Commute.refl _)).smul_left t).smul_right t
  have he : approxU hA n t = approxU hA m t * exp (t • D) := by
    unfold approxU
    rw [← exp_add_of_commute hcomm, ← smul_add]
    congr 2
    simp only [D]; abel
  rw [he, mul_apply_eq_comp, ← _root_.map_sub, norm_approxU_apply]
  exact norm_exp_smul_sub_le_of_skew hD t x

/-- `(exp(t B_n) x)_n` is Cauchy: on `D(A)` by `norm_approxU_sub_le`, then by density. -/
theorem cauchySeq_approxU (hA : IsSkewAdjoint A) (t : ℝ) (x : E) :
    CauchySeq fun n => approxU hA n t x := by
  refine cauchySeq_apply_of_dense (fun n x => (norm_approxU_apply hA n t x).le)
    hA.dense_domain ?_ x
  intro y hy
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (tendsto_approxB hA ⟨y, hy⟩).cauchySeq
    (ε / (|t| + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := norm_approxU_sub_le hA m n t y
  have h2 := hN m hm n hn
  rw [dist_eq_norm] at h2 ⊢
  have h3 : |t| * ‖approxB hA m y - approxB hA n y‖ ≤ |t| * (ε / (|t| + 1)) :=
    mul_le_mul_of_nonneg_left h2.le (abs_nonneg t)
  have h4 : |t| * (ε / (|t| + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg t]
  linarith

/-- **The Stone group** `S(t) x = lim_n exp(t B_n) x` (strong limit; a continuous linear map by
Banach–Steinhaus, `continuousLinearMapOfTendsto`). -/
def stoneS (hA : IsSkewAdjoint A) (t : ℝ) : E →L[ℝ] E :=
  continuousLinearMapOfTendsto (fun n => approxU hA n t)
    (tendsto_pi_nhds.2 fun x => (cauchySeq_approxU hA t x).tendsto_limUnder)

/-- `exp(t B_n) x → S(t) x`. -/
theorem tendsto_approxU (hA : IsSkewAdjoint A) (t : ℝ) (x : E) :
    Tendsto (fun n => approxU hA n t x) atTop (𝓝 (stoneS hA t x)) :=
  (cauchySeq_approxU hA t x).tendsto_limUnder

/-- `exp(t B_n) y_n → S(t) y` whenever `y_n → y` (the `exp(t B_n)` are isometries). -/
theorem tendsto_approxU_of_tendsto (hA : IsSkewAdjoint A) (t : ℝ) {y : ℕ → E} {y₀ : E}
    (hy : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n => approxU hA n t (y n)) atTop (𝓝 (stoneS hA t y₀)) := by
  have h0 : Tendsto (fun n => approxU hA n t (y n - y₀)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_approxU_apply]
    exact tendsto_zero_iff_norm_tendsto_zero.1 (by simpa using hy.sub_const y₀)
  have := h0.add (tendsto_approxU hA t y₀)
  rw [zero_add] at this
  exact this.congr fun n => by rw [← _root_.map_add, sub_add_cancel]

/-- `S(t)` is an isometry. -/
theorem norm_stoneS_apply (hA : IsSkewAdjoint A) (t : ℝ) (x : E) : ‖stoneS hA t x‖ = ‖x‖ :=
  tendsto_nhds_unique (tendsto_approxU hA t x).norm
    (by simp_rw [norm_approxU_apply]; exact tendsto_const_nhds)

/-- `S(0) = 1`. -/
theorem stoneS_zero (hA : IsSkewAdjoint A) : stoneS hA 0 = 1 := by
  ext x
  refine tendsto_nhds_unique (tendsto_approxU hA 0 x) ?_
  simp [approxU]

/-- `S(s + t) = S(s) S(t)`. -/
theorem stoneS_add (hA : IsSkewAdjoint A) (s t : ℝ) :
    stoneS hA (s + t) = stoneS hA s * stoneS hA t := by
  ext x
  refine tendsto_nhds_unique (tendsto_approxU hA (s + t) x) ?_
  simp_rw [approxU_add, mul_apply_eq_comp]
  exact tendsto_approxU_of_tendsto hA s (tendsto_approxU hA t x)

/-- `‖S(t) x - S(s) x‖ ≤ |t - s| ‖A x‖` on `D(A)`. -/
theorem norm_stoneS_sub_le (hA : IsSkewAdjoint A) (x : A.domain) (t s : ℝ) :
    ‖stoneS hA t x - stoneS hA s x‖ ≤ |t - s| * ‖A x‖ := by
  refine le_of_tendsto' ((tendsto_approxU hA t x).sub (tendsto_approxU hA s x)).norm fun n => ?_
  have e : approxU hA n t = approxU hA n s * approxU hA n (t - s) := by
    rw [← approxU_add, add_sub_cancel]
  rw [e, mul_apply_eq_comp, ← _root_.map_sub, norm_approxU_apply]
  calc ‖approxU hA n (t - s) x - x‖ ≤ |t - s| * ‖approxB hA n x‖ :=
        norm_exp_smul_sub_le_of_skew (approxB_skew hA n) _ _
    _ ≤ |t - s| * ‖A x‖ := by gcongr; exact norm_approxB_apply_domain_le hA n x

/-- Strong continuity: `t ↦ S(t) x` is continuous (Lipschitz on `D(A)`, then uniform
approximation). -/
theorem continuous_stoneS_apply (hA : IsSkewAdjoint A) (x : E) :
    Continuous fun t => stoneS hA t x := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.1 hA.dense_domain x ε hε
  rw [Metric.mem_ball] at hd
  refine ⟨fun t => stoneS hA t d, ?_, fun t => hεu ?_⟩
  · refine (LipschitzWith.of_dist_le_mul (K := ‖A ⟨d, hdD⟩‖₊) fun t s => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, coe_nnnorm, mul_comm]
    exact norm_stoneS_sub_le hA ⟨d, hdD⟩ t s
  · rw [dist_eq_norm, ← _root_.map_sub, norm_stoneS_apply, ← dist_eq_norm, dist_comm]
    exact hd

/-- `S(t) x - x = ∫₀ᵗ S(s) (A x) ds` on `D(A)`. -/
theorem stoneS_sub_eq_integral (hA : IsSkewAdjoint A) (x : A.domain) (t : ℝ) :
    stoneS hA t x - x = ∫ s in (0 : ℝ)..t, stoneS hA s (A x) := by
  have hcont : ∀ n, Continuous fun s => approxU hA n s (approxB hA n x) := fun n =>
    (continuous_exp_smul _).clm_apply continuous_const
  have hftc : ∀ n, approxU hA n t x - x = ∫ s in (0 : ℝ)..t, approxU hA n s (approxB hA n x) := by
    intro n
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => approxU hA n s x) (a := 0) (b := t)
      (f' := fun s => approxU hA n s (approxB hA n x)) (fun s _ => ?_)
      ((hcont n).intervalIntegrable _ _)
    · rw [h]; simp [approxU]
    · have h := hasDerivAt_exp_smul_apply (approxB hA n) (x : E) s
      have hc : approxB hA n (exp (s • approxB hA n) x) = exp (s • approxB hA n) (approxB hA n x) := by
        have : Commute (approxB hA n) (exp (s • approxB hA n)) :=
          ((Commute.refl _).smul_right s).exp_right
        exact congrArg (fun C : E →L[ℝ] E => C x) this.eq
      rw [hc] at h
      exact h
  have hlim : Tendsto (fun n => ∫ s in (0 : ℝ)..t, approxU hA n s (approxB hA n x)) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, stoneS hA s (A x))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => ‖A x‖)
      (Eventually.of_forall fun n => (hcont n).aestronglyMeasurable) ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun n => Eventually.of_forall fun s _ => ?_
      rw [norm_approxU_apply]; exact norm_approxB_apply_domain_le hA n x
    · exact Eventually.of_forall fun s _ => tendsto_approxU_of_tendsto hA s (tendsto_approxB hA x)
  refine tendsto_nhds_unique ((tendsto_approxU hA t x).sub_const (x : E)) ?_
  simp_rw [hftc]; exact hlim

/-- The generator of `S` extends `A`: `(d/dt) S(t) x |_{t=0} = A x` on `D(A)`. -/
theorem hasDerivAt_stoneS_zero (hA : IsSkewAdjoint A) (x : A.domain) :
    HasDerivAt (fun t => stoneS hA t x) (A x) 0 := by
  have hc : Continuous fun s => stoneS hA s (A x) := continuous_stoneS_apply hA _
  have h := (hc.integral_hasStrictDerivAt 0 0).hasDerivAt.const_add (x : E)
  rw [stoneS_zero, one_apply_eq_self] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  rw [← stoneS_sub_eq_integral]; abel

/-- `⟪S(h) x, z⟫ = ⟪x, S(-h) z⟫`: `S(h)` is orthogonal with inverse `S(-h)`. -/
theorem inner_stoneS_left (hA : IsSkewAdjoint A) (h : ℝ) (x z : E) :
    ⟪stoneS hA h x, z⟫ = ⟪x, stoneS hA (-h) z⟫ := by
  have hpres := (LinearMap.norm_map_iff_inner_map_map (stoneS hA h)).mp (norm_stoneS_apply hA h)
  conv_lhs => rw [show z = stoneS hA h (stoneS hA (-h) z) by
    rw [← mul_apply_eq_comp, ← stoneS_add, add_neg_cancel, stoneS_zero,
      one_apply_eq_self]]
  exact hpres x _

/-- The generator of `S` is exactly `A`, domain included: if `t ↦ S(t) x` is differentiable at
`0`, then `x ∈ D(A†) = D(A)`. -/
theorem mem_domain_iff_differentiableAt_stoneS (hA : IsSkewAdjoint A) (x : E) :
    x ∈ A.domain ↔ DifferentiableAt ℝ (fun t => stoneS hA t x) 0 := by
  refine ⟨fun hx => (hasDerivAt_stoneS_zero hA ⟨x, hx⟩).differentiableAt, fun hd => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, HasDerivAt (fun t => stoneS hA t x) y 0 := ⟨_, hd.hasDerivAt⟩
  have key : ∀ z : A.domain, ⟪-y, (z : E)⟫ = ⟪x, A z⟫ := by
    intro z
    have d1 := hy.inner ℝ (hasDerivAt_const (0 : ℝ) (z : E))
    have hz' : HasDerivAt (fun h : ℝ => stoneS hA (-h) z) (-(A z)) 0 := by
      have h0 : HasDerivAt (fun t => stoneS hA t z) (A z) (-0) := by
        rw [neg_zero]; exact hasDerivAt_stoneS_zero hA z
      have := h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      simpa [Function.comp_def] using this
    have d2 := (hasDerivAt_const (0 : ℝ) x).inner ℝ hz'
    have e : (fun t => ⟪stoneS hA t x, (z : E)⟫) = fun t => ⟪x, stoneS hA (-t) z⟫ :=
      funext fun t => inner_stoneS_left hA t x z
    rw [e] at d1
    have := d1.unique d2
    simp only [inner_zero_right, inner_zero_left, zero_add, add_zero, inner_neg_right] at this
    rw [inner_neg_left, this, neg_neg]
  exact (hA.mem_domain_of_adjoint key).1

/-! ### Stone's theorem -/

/-- **Stone's theorem (existence half), real Hilbert space.** Every skew-adjoint operator
`A` (`A† = -A`; dense domain is automatic, `IsSkewAdjoint.dense_domain`) generates a strongly
continuous orthogonal group `S(t) = lim_n exp(t B_n)`, with generator domain exactly `D(A)`.
This discharges the hypothesis `Feec.UnitaryGroupGenerator` wherever the operator is
skew-adjoint.

Thesis gap: the existence input of [QuennevilleBelair2015, Thm 4.3], cited there from
[CazenaveHaraux1998]; proved here. Cf. [Pazy1983, §1.10], [Brezis2011, Ch. 7]. -/
def stoneGroup (hA : IsSkewAdjoint A) : UnitaryGroupGenerator A where
  S := stoneS hA
  map_zero := stoneS_zero hA
  map_add := stoneS_add hA
  norm_map := norm_stoneS_apply hA
  continuous_apply := continuous_stoneS_apply hA
  mem_domain_iff := mem_domain_iff_differentiableAt_stoneS hA
  hasDerivAt_zero := hasDerivAt_stoneS_zero hA

/-! ### The converse half of Stone's theorem, and uniqueness of the group -/

namespace UnitaryGroupGenerator

variable {L : E →ₗ.[ℝ] E}

omit [CompleteSpace E] in
/-- `⟪S(t) a, b⟫ = ⟪a, S(-t) b⟫`. -/
theorem inner_S_left (G : UnitaryGroupGenerator L) (t : ℝ) (a b : E) : ⟪G.S t a, b⟫ = ⟪a, G.S (-t) b⟫ := by
  have hpres := (LinearMap.norm_map_iff_inner_map_map (G.S t)).mp (G.norm_map t)
  conv_lhs => rw [show b = G.S t (G.S (-t) b) by
    rw [← mul_apply_eq_comp, ← G.map_add, add_neg_cancel, G.map_zero, one_apply_eq_self]]
  exact hpres a _

/-- The generator of a strongly continuous orthogonal group is densely defined:
`h⁻¹ ∫₀ʰ S(s) x ds ∈ D(L)` converges to `x` as `h → 0`. -/
theorem dense_domain (G : UnitaryGroupGenerator L) : Dense (L.domain : Set E) := by
  intro x
  set f : ℝ → E := fun s => G.S s x
  have hf : Continuous f := G.continuous_apply x
  -- `∫₀ʰ S(s) x ds ∈ D(L)`
  have hmem : ∀ h : ℝ, (∫ s in (0 : ℝ)..h, f s) ∈ L.domain := by
    intro h
    rw [G.mem_domain_iff]
    have e : (fun τ => G.S τ (∫ s in (0 : ℝ)..h, f s)) =
        fun τ => (∫ s in (0 : ℝ)..(τ + h), f s) - ∫ s in (0 : ℝ)..τ, f s := by
      funext τ
      rw [← (G.S τ).intervalIntegral_comp_comm (hf.intervalIntegrable _ _)]
      have : ∀ s, G.S τ (f s) = f (τ + s) := fun s => by
        simp only [f, G.map_add, mul_apply_eq_comp]
      simp_rw [this]
      rw [intervalIntegral.integral_comp_add_left (fun u => f u) τ, add_zero,
        intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
          (hf.intervalIntegrable _ _)]
    rw [e]
    have h1 : HasDerivAt (fun τ => ∫ s in (0 : ℝ)..(τ + h), f s) (f (0 + h)) 0 := by
      have := (hf.integral_hasStrictDerivAt 0 (0 + h)).hasDerivAt
      exact this.comp_add_const 0 h
    have h2 := (hf.integral_hasStrictDerivAt 0 0).hasDerivAt
    exact (h1.sub h2).differentiableAt
  -- `h⁻¹ ∫₀ʰ S(s) x ds → x`
  have hd := (hf.integral_hasStrictDerivAt 0 0).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hx : f 0 = x := by simp [f, G.map_zero]
  rw [hx] at hd
  refine mem_closure_of_tendsto hd (Eventually.of_forall fun h => ?_)
  rw [slope_def_module, intervalIntegral.integral_same, sub_zero, sub_zero]
  exact L.domain.smul_mem _ (hmem h)

/-- **Stone's theorem, converse half**: the generator of a strongly continuous orthogonal
group is skew-adjoint. -/
theorem isSkewAdjoint (G : UnitaryGroupGenerator L) : IsSkewAdjoint L := by
  have hD := G.dense_domain
  have hS := G.isSkewSymm
  have hle : -L ≤ L† := by
    refine IsFormalAdjoint.le_adjoint hD fun x y => ?_
    rw [LinearPMap.neg_apply, inner_neg_right]
    exact hS x y
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  -- `y ∈ D(L†)` with `L† y = w`: show `S(τ) y = y - ∫₀^τ S(u) w du`
  set w := L† ⟨y, hy⟩
  have hw : ∀ x : L.domain, ⟪w, (x : E)⟫ = ⟪y, L x⟫ := fun x =>
    adjoint_isFormalAdjoint hD ⟨y, hy⟩ x
  have hcw : Continuous fun u => G.S u w := G.continuous_apply w
  have key : ∀ τ, G.S τ y = y - ∫ u in (0 : ℝ)..τ, G.S u w := by
    intro τ
    rw [← sub_eq_zero]
    set v := G.S τ y - (y - ∫ u in (0 : ℝ)..τ, G.S u w)
    have horth : ∀ z ∈ (L.domain : Set E), ⟪v, z⟫ = 0 := by
      intro z hz
      -- derivative of `τ ↦ ⟪S(τ) y, z⟫`
      have hder : ∀ t, HasDerivAt (fun τ => ⟪G.S τ y, z⟫) (-⟪G.S t w, z⟫) t := by
        intro t
        have h0 : HasDerivAt (fun τ => G.S τ z) (G.S (-t) (L ⟨z, hz⟩)) (-t) :=
          G.hasDerivAt_apply ⟨z, hz⟩ (-t)
        have h1 := h0.scomp t (hasDerivAt_neg t)
        have h2 := (hasDerivAt_const t y).inner ℝ h1
        have e : (fun τ => ⟪G.S τ y, z⟫) = fun τ => ⟪y, G.S (-τ) z⟫ :=
          funext fun τ => G.inner_S_left τ y z
        rw [e]
        refine h2.congr_deriv ?_
        rw [inner_zero_left, add_zero, neg_one_smul, inner_neg_right, ← G.apply_comm ⟨z, hz⟩ (-t),
          ← hw, G.inner_S_left]
      have hcont : Continuous fun t => -⟪G.S t w, z⟫ :=
        (hcw.inner continuous_const).neg
      have hftc : (∫ t in (0 : ℝ)..τ, -⟪G.S t w, z⟫) = ⟪G.S τ y, z⟫ - ⟪y, z⟫ := by
        have := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun τ => ⟪G.S τ y, z⟫) (a := 0) (b := τ)
          (fun t _ => hder t) (hcont.intervalIntegrable _ _)
        rw [this, G.map_zero, one_apply_eq_self]
      have hcomm : (∫ u in (0 : ℝ)..τ, ⟪z, G.S u w⟫) = ⟪z, ∫ u in (0 : ℝ)..τ, G.S u w⟫ :=
        (innerSL ℝ z).intervalIntegral_comp_comm (hcw.intervalIntegrable _ _)
      rw [intervalIntegral.integral_neg] at hftc
      simp only [v, inner_sub_left]
      simp_rw [real_inner_comm z] at hftc ⊢
      rw [← hcomm]
      linarith
    have hall : ∀ z, ⟪v, z⟫ = 0 := by
      have hcl : IsClosed {z : E | ⟪v, z⟫ = 0} :=
        isClosed_eq (continuous_const.inner continuous_id) continuous_const
      intro z
      have := closure_minimal
        (show (L.domain : Set E) ⊆ {z : E | ⟪v, z⟫ = 0} from fun z hz => horth z hz) hcl
      rw [hD.closure_eq] at this
      exact this (mem_univ z)
    exact inner_self_eq_zero.1 (hall v)
  show y ∈ L.domain
  rw [G.mem_domain_iff]
  have hd := ((hcw.integral_hasStrictDerivAt 0 0).hasDerivAt.const_sub y)
  exact (hd.congr_of_eventuallyEq (Eventually.of_forall key)).differentiableAt

/-- **Uniqueness**: a strongly continuous orthogonal group is determined by its generator. -/
theorem S_eq (G G' : UnitaryGroupGenerator L) : G.S = G'.S := by
  have hS := G.isSkewSymm
  funext t
  have hD : ∀ x : L.domain, G.S t x = G'.S t x := by
    intro x
    set e : ℝ → E := fun s => G.S s x - G'.S s x
    have hmem : ∀ s, e s ∈ L.domain := fun s =>
      L.domain.sub_mem (G.mem_domain_apply x s) (G'.mem_domain_apply x s)
    have hde : ∀ s, HasDerivAt e (L ⟨e s, hmem s⟩) s := by
      intro s
      have := (G.hasDerivAt_apply x s).sub (G'.hasDerivAt_apply x s)
      convert this using 1
      have e1 : (⟨e s, hmem s⟩ : L.domain) =
          ⟨G.S s x, G.mem_domain_apply x s⟩ - ⟨G'.S s x, G'.mem_domain_apply x s⟩ := rfl
      rw [e1, LinearPMap.map_sub, G.apply_comm, G'.apply_comm]
    have hn : ∀ s, HasDerivAt (fun s => ‖e s‖ ^ 2) 0 s := by
      intro s
      have := (hde s).norm_sq
      rwa [real_inner_comm, IsSkewSymm.inner_self_eq_zero hS, mul_zero] at this
    have hc := is_const_of_deriv_eq_zero (fun s => (hn s).differentiableAt) (fun s => (hn s).deriv)
      t 0
    simp only [e, G.map_zero, G'.map_zero, sub_self, norm_zero] at hc
    have : ‖e t‖ = 0 := by simpa using hc
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  exact DFunLike.coe_injective
    (Continuous.ext_on G.dense_domain (G.S t).continuous (G'.S t).continuous fun x hx => hD ⟨x, hx⟩)

end UnitaryGroupGenerator

/-- **Stone's theorem** (real Hilbert space form): `A` is skew-adjoint iff it generates a
strongly continuous orthogonal group (with generator domain exactly `D(A)`). -/
theorem isSkewAdjoint_iff_nonempty_unitaryGroupGenerator :
    IsSkewAdjoint A ↔ Nonempty (UnitaryGroupGenerator A) :=
  ⟨fun hA => ⟨stoneGroup hA⟩, fun ⟨G⟩ => G.isSkewAdjoint⟩

/-- Every orthogonal group generated by a skew-adjoint `A` is the Stone group `stoneS`, the
strong limit of `exp(t B_n)`. -/
theorem UnitaryGroupGenerator.S_eq_stoneS (hA : IsSkewAdjoint A) (G : UnitaryGroupGenerator A) :
    G.S = stoneS hA :=
  G.S_eq (stoneGroup hA)

end Feec
