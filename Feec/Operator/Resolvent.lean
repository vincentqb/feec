module

public import Feec.ForMathlib.LinearPMap.Skew
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Resolvents of unbounded operators

For a linear operator `A : E →ₗ.[𝕜] E` on a Hilbert space over `𝕜 = ℝ` or `ℂ` and `z : 𝕜`:

* `IsResolvent A z R`: the bounded operator `R` is a two-sided inverse of `z - A : D(A) → E`.
  It is unique (`IsResolvent.unique`), and `resolvent A z` is it when it exists
  (`IsResolvent.resolvent_eq`; junk value `0` otherwise).
* General identities: `IsResolvent.apply_mem_domain`, `IsResolvent.apply_resolvent`
  (`A R y = z R y - y`), `IsResolvent.apply_domain` (`R A x = z R x - x`), the **resolvent
  identity** `IsResolvent.sub_eq` (`R(z) - R(w) = (w - z) R(z) R(w)`) and
  `IsResolvent.commute`.
* Lower bounds: `IsDissipative.re_mul_norm_le_norm_shiftOp` (`re z ‖x‖ ≤ ‖(z - A) x‖`),
  `re_mul_norm_le_norm_smul_sub` (`re z ‖x‖ ≤ ‖z x - A x‖` when
  `re ⟪A x, x⟫ ≤ 0`), `abs_re_mul_norm_le_norm_smul_sub` (`|re z| ‖x‖ ≤ ‖z x - A x‖` when
  `re ⟪A x, x⟫ = 0`), and `IsResolvent.norm_apply_le` (`‖R‖ ≤ 1/c` from
  `c ‖x‖ ≤ ‖z x - A x‖`).
* **Skew-adjoint operators** (`A.IsSkewAdjoint`, i.e. `A† = -A`): for `re z ≠ 0`, `z - A` is
  bijective (`IsSkewSymmetric.injective_shiftOp`, needing only skew-symmetry, and
  `surjective_shiftOp`), so `resolvent A z` is a resolvent (`isResolvent_resolvent`) with
  `‖R(z)‖ ≤ 1/|re z|` (`norm_resolvent_apply_le`) and adjoint `R(z)† = -R(-z̄)` (`adjoint_resolvent`, `inner_resolvent_left`).

Over `𝕜 = ℝ` this is the real-`z ≠ 0` resolvent used for Stone's theorem; over `ℂ` it is the
resolvent off the imaginary axis.

## References

* [Kato1995] (resolvents and the resolvent identity for closed operators)
* [Pazy1983], §1.10 (resolvents of skew-adjoint generators)
-/

open LinearPMap Filter Topology

@[expose] public noncomputable section

namespace Feec.Operator

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### `z - A` and the resolvent predicate -/

/-- `z - A : D(A) → E`. -/
def shiftOp (A : E →ₗ.[𝕜] E) (z : 𝕜) : A.domain →ₗ[𝕜] E := z • A.domain.subtype - A.toFun

@[simp] theorem shiftOp_apply (A : E →ₗ.[𝕜] E) (z : 𝕜) (x : A.domain) :
    shiftOp A z x = z • (x : E) - A x := rfl

/-- `R` is a resolvent of `A` at `z`: a bounded two-sided inverse of `z - A : D(A) → E`. -/
structure IsResolvent (A : E →ₗ.[𝕜] E) (z : 𝕜) (R : E →L[𝕜] E) : Prop where
  mem_domain : ∀ y, R y ∈ A.domain
  sub_apply : ∀ y, z • R y - A ⟨R y, mem_domain y⟩ = y
  apply_sub : ∀ x : A.domain, R (z • (x : E) - A x) = x

open scoped Classical in
/-- The resolvent `(z - A)⁻¹` of `A` at `z`, when `z - A` has a bounded inverse
(junk value `0` otherwise). -/
def resolvent (A : E →ₗ.[𝕜] E) (z : 𝕜) : E →L[𝕜] E :=
  if h : ∃ R, IsResolvent A z R then h.choose else 0

variable {A : E →ₗ.[𝕜] E} {z w : 𝕜} {R S : E →L[𝕜] E}

namespace IsResolvent

/-- `R y` as an element of `D(A)`. -/
def toDomain (hR : IsResolvent A z R) (y : E) : A.domain := ⟨R y, hR.mem_domain y⟩

@[simp] theorem coe_toDomain (hR : IsResolvent A z R) (y : E) : (hR.toDomain y : E) = R y := rfl

/-- `(z - A) R y = y`, with `R y` as a domain element. -/
theorem sub_apply_toDomain (hR : IsResolvent A z R) (y : E) :
    z • R y - A (hR.toDomain y) = y :=
  hR.sub_apply y

/-- A resolvent is unique. -/
theorem unique (hR : IsResolvent A z R) (hS : IsResolvent A z S) : R = S := by
  ext y
  have h := hR.apply_sub (hS.toDomain y)
  rw [coe_toDomain, hS.sub_apply_toDomain] at h
  exact h

/-- `resolvent A z` is the resolvent, when one exists. -/
theorem resolvent_eq (hR : IsResolvent A z R) : resolvent A z = R := by
  have h : ∃ R, IsResolvent A z R := ⟨R, hR⟩
  rw [resolvent, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.unique hR

theorem isResolvent_resolvent (hR : IsResolvent A z R) : IsResolvent A z (resolvent A z) :=
  hR.resolvent_eq ▸ hR

/-- `A R y = z R y - y`. -/
theorem apply_resolvent (hR : IsResolvent A z R) (y : E) :
    A (hR.toDomain y) = z • R y - y := by
  rw [eq_sub_iff_add_eq, add_comm]
  exact (sub_eq_iff_eq_add.1 (hR.sub_apply_toDomain y)).symm

/-- `R (A x) = z R x - x` on `D(A)`: `R` commutes with `A`. -/
theorem apply_domain (hR : IsResolvent A z R) (x : A.domain) :
    R (A x) = z • R x - x := by
  have h : A x = z • (x : E) - (z • (x : E) - A x) := by abel
  rw [h, _root_.map_sub, _root_.map_smul, hR.apply_sub]

/-- **Resolvent identity** `R(z) - R(w) = (w - z) R(z) R(w)`. -/
theorem sub_eq (hR : IsResolvent A z R) (hS : IsResolvent A w S) :
    R - S = (w - z) • (R * S) := by
  ext y
  have hu : z • S y - A (hS.toDomain y) = (z - w) • S y + (w • S y - A (hS.toDomain y)) := by
    rw [sub_smul]; abel
  rw [hS.sub_apply_toDomain] at hu
  have h := hR.apply_sub (hS.toDomain y)
  simp only [coe_toDomain] at h
  rw [hu, _root_.map_add, _root_.map_smul] at h
  change R y - S y = (w - z) • R (S y)
  generalize R (S y) = a at h ⊢
  rw [← h]
  module

/-- Resolvents at different points commute. -/
theorem commute (hR : IsResolvent A z R) (hS : IsResolvent A w S) : Commute R S := by
  rcases eq_or_ne z w with rfl | hzw
  · rw [hR.unique hS]
  have h1 := hR.sub_eq hS
  have h2 := hS.sub_eq hR
  have h3 : (w - z) • (R * S) = (w - z) • (S * R) := by
    rw [← h1, show w - z = -(z - w) by ring, neg_smul, ← h2]; abel
  exact smul_right_injective _ (sub_ne_zero.2 hzw.symm) h3

/-- `‖R y‖ ≤ c⁻¹ ‖y‖` from the lower bound `c ‖x‖ ≤ ‖z x - A x‖` (`c > 0`). -/
theorem norm_apply_le (hR : IsResolvent A z R) {c : ℝ} (hc : 0 < c)
    (hb : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖z • (x : E) - A x‖) (y : E) :
    ‖R y‖ ≤ c⁻¹ * ‖y‖ := by
  have h := hb (hR.toDomain y)
  rw [coe_toDomain, hR.sub_apply_toDomain] at h
  rw [le_inv_mul_iff₀ hc]
  exact h

/-- `‖R‖ ≤ c⁻¹` from the lower bound `c ‖x‖ ≤ ‖z x - A x‖` (`c > 0`). -/
theorem norm_le (hR : IsResolvent A z R) {c : ℝ} (hc : 0 < c)
    (hb : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖z • (x : E) - A x‖) : ‖R‖ ≤ c⁻¹ :=
  R.opNorm_le_bound (inv_nonneg.2 hc.le) (hR.norm_apply_le hc hb)

end IsResolvent

/-! ### Lower bounds -/

/-- `re z ‖x‖ ≤ ‖z x - y‖` when `re ⟪y, x⟫ ≤ 0`; with `y = A x` this is the lower bound
`re z ‖x‖ ≤ ‖(z - A) x‖` for a dissipative operator `A`. -/
theorem re_mul_norm_le_norm_smul_sub {x y : E} (hA : RCLike.re ⟪y, x⟫ ≤ 0) :
    RCLike.re z * ‖x‖ ≤ ‖z • x - y‖ := by
  have h1 : RCLike.re ⟪z • x - y, x⟫ = RCLike.re z * ‖x‖ ^ 2 - RCLike.re ⟪y, x⟫ := by
    rw [inner_sub_left, inner_smul_left, _root_.map_sub, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow, RCLike.re_mul_ofReal, RCLike.conj_re]
  have h2 : RCLike.re ⟪z • x - y, x⟫ ≤ ‖z • x - y‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · refine le_of_mul_le_mul_right ?_ h
    nlinarith

/-- `|re z| ‖x‖ ≤ ‖z x - y‖` when `re ⟪y, x⟫ = 0`; with `y = A x` this is the lower bound
`|re z| ‖x‖ ≤ ‖(z - A) x‖` for a skew-symmetric operator `A`. -/
theorem abs_re_mul_norm_le_norm_smul_sub {x y : E} (hA : RCLike.re ⟪y, x⟫ = 0) :
    |RCLike.re z| * ‖x‖ ≤ ‖z • x - y‖ := by
  rcases le_total 0 (RCLike.re z) with hz | hz
  · rw [abs_of_nonneg hz]; exact re_mul_norm_le_norm_smul_sub hA.le
  · have h := re_mul_norm_le_norm_smul_sub (z := -z) (x := x) (y := -y)
      (by rw [inner_neg_left, _root_.map_neg, hA, neg_zero])
    rw [abs_of_nonpos hz, ← _root_.map_neg]
    calc RCLike.re (-z) * ‖x‖ ≤ ‖-z • x - -y‖ := h
      _ = ‖z • x - y‖ := by rw [← norm_neg]; congr 1; rw [neg_smul]; abel

/-- `re z ‖x‖ ≤ ‖(z - A) x‖` for a dissipative operator `A`. -/
theorem _root_.LinearPMap.IsDissipative.re_mul_norm_le_norm_shiftOp (hA : A.IsDissipative)
    (z : 𝕜) (x : A.domain) : RCLike.re z * ‖(x : E)‖ ≤ ‖shiftOp A z x‖ :=
  re_mul_norm_le_norm_smul_sub (hA x)

/-- For dissipative `A` and `re z > 0`, a resolvent is bounded by `1 / re z`. -/
theorem IsResolvent.norm_le_of_isDissipative (hR : IsResolvent A z R) (hA : A.IsDissipative)
    (hz : 0 < RCLike.re z) : ‖R‖ ≤ (RCLike.re z)⁻¹ :=
  hR.norm_le hz (hA.re_mul_norm_le_norm_shiftOp z)

/-- `|re z| ‖x‖ ≤ ‖(z - A) x‖` for skew-symmetric `A`. -/
theorem _root_.LinearPMap.IsSkewSymmetric.abs_re_mul_norm_le_norm_shiftOp
    (hA : A.IsSkewSymmetric) (z : 𝕜) (x : A.domain) :
    |RCLike.re z| * ‖(x : E)‖ ≤ ‖shiftOp A z x‖ :=
  abs_re_mul_norm_le_norm_smul_sub (hA.re_inner_self x)

/-- `z - A` is injective for skew-symmetric `A` and `re z ≠ 0`. -/
theorem _root_.LinearPMap.IsSkewSymmetric.injective_shiftOp (hA : A.IsSkewSymmetric)
    (hz : RCLike.re z ≠ 0) : Function.Injective (shiftOp A z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := hA.abs_re_mul_norm_le_norm_shiftOp z x
  rw [hx, norm_zero] at h
  have : ‖(x : E)‖ = 0 :=
    le_antisymm (by nlinarith [abs_pos.2 hz, norm_nonneg (x : E)]) (norm_nonneg _)
  exact Subtype.ext (norm_eq_zero.1 this)

/-! ### Skew-adjoint operators -/

section SkewAdjoint

variable [CompleteSpace E]

/-- Membership in `D(A†)` with `A† y = w` transfers to `D(A)` with `A y = -w`. -/
private theorem mem_domain_of_inner_eq (hA : A.IsSkewAdjoint) {y w : E}
    (h : ∀ x : A.domain, ⟪w, (x : E)⟫ = ⟪y, A x⟫) : ∃ hy : y ∈ A.domain, A ⟨y, hy⟩ = -w := by
  have hya : y ∈ A†.domain := mem_adjoint_domain_of_exists y ⟨w, h⟩
  have hval : A† ⟨y, hya⟩ = w := adjoint_apply_eq hA.dense_domain ⟨y, hya⟩ h
  have hle : A† ≤ -A := hA ▸ le_rfl
  have hy : y ∈ A.domain := hle.1 hya
  refine ⟨hy, ?_⟩
  have h2 : A† ⟨y, hya⟩ = (-A) ⟨y, hy⟩ := hle.2 rfl
  rw [hval, LinearPMap.neg_apply] at h2
  rw [h2, neg_neg]

/-- `(range (z - A))ᗮ = ⊥` for skew-adjoint `A` and `re z ≠ 0`. -/
theorem orthogonal_range_shiftOp (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) :
    (LinearMap.range (shiftOp A z))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have h : ∀ x : A.domain, ⟪(starRingEnd 𝕜) z • y, (x : E)⟫ = ⟪y, A x⟫ := by
    intro x
    have h0 := hy _ ⟨x, rfl⟩
    rw [shiftOp_apply, inner_sub_left, inner_smul_left, sub_eq_zero] at h0
    have h1 := congrArg (starRingEnd 𝕜) h0
    rw [map_mul, RCLike.conj_conj, inner_conj_symm, inner_conj_symm] at h1
    rw [inner_smul_left, RCLike.conj_conj]
    exact h1
  obtain ⟨hyD, hAy⟩ := mem_domain_of_inner_eq hA h
  have h0 : shiftOp A (-(starRingEnd 𝕜) z) ⟨y, hyD⟩ = 0 := by
    rw [shiftOp_apply, hAy]; simp
  have hz' : RCLike.re (-(starRingEnd 𝕜) z) ≠ 0 := by
    rw [_root_.map_neg, RCLike.conj_re]; exact neg_ne_zero.2 hz
  have := hA.isSkewSymmetric.injective_shiftOp hz' (h0.trans (_root_.map_zero _).symm)
  exact congrArg Subtype.val this

/-- The range of `z - A` is closed for skew-adjoint `A` and `re z ≠ 0`. -/
theorem isClosed_range_shiftOp (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) :
    IsClosed (LinearMap.range (shiftOp A z) : Set E) := by
  refine IsSeqClosed.isClosed fun {u y} hu huy => ?_
  choose x hx using hu
  have hz' : 0 < |RCLike.re z| := abs_pos.2 hz
  have hc : CauchySeq fun n => (x n : E) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 huy.cauchySeq (|RCLike.re z| * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hA.isSkewSymmetric.abs_re_mul_norm_le_norm_shiftOp z (x m - x n)
    rw [_root_.map_sub, hx, hx, ← dist_eq_norm] at h1
    have h2 := hN m hm n hn
    rw [dist_eq_norm, ← Submodule.coe_sub]
    nlinarith
  obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hc
  have h : ∀ w : A.domain, ⟪y - z • x₀, (w : E)⟫ = ⟪x₀, A w⟫ := by
    intro w
    have l1 : Tendsto (fun n => ⟪(x n : E), A w⟫) atTop (𝓝 ⟪x₀, A w⟫) :=
      hx₀.inner tendsto_const_nhds
    have l2 : Tendsto (fun n => ⟪u n - z • (x n : E), (w : E)⟫) atTop
        (𝓝 ⟪y - z • x₀, (w : E)⟫) :=
      (huy.sub (hx₀.const_smul z)).inner tendsto_const_nhds
    refine tendsto_nhds_unique l2 (l1.congr fun n => ?_)
    rw [← hx n, shiftOp_apply, sub_sub_cancel_left, inner_neg_left, hA.isSkewSymmetric,
      neg_neg]
  obtain ⟨hD, hAx⟩ := mem_domain_of_inner_eq hA h
  refine ⟨⟨x₀, hD⟩, ?_⟩
  rw [shiftOp_apply]
  change z • x₀ - A ⟨x₀, hD⟩ = y
  rw [hAx]
  abel

/-- `z - A : D(A) → E` is surjective for skew-adjoint `A` and `re z ≠ 0`. -/
theorem surjective_shiftOp (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) :
    Function.Surjective (shiftOp A z) := by
  rw [← LinearMap.range_eq_top, ← (isClosed_range_shiftOp hA hz).submodule_topologicalClosure_eq,
    Submodule.topologicalClosure_eq_top_iff]
  exact orthogonal_range_shiftOp hA hz

/-- `z - A` as a linear equivalence `D(A) ≃ E` (skew-adjoint `A`, `re z ≠ 0`). -/
def shiftEquiv (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) : A.domain ≃ₗ[𝕜] E :=
  LinearEquiv.ofBijective (shiftOp A z)
    ⟨hA.isSkewSymmetric.injective_shiftOp hz, surjective_shiftOp hA hz⟩

private theorem norm_shiftEquiv_symm_le (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) (y : E) :
    ‖((shiftEquiv hA hz).symm y : E)‖ ≤ |RCLike.re z|⁻¹ * ‖y‖ := by
  have h := hA.isSkewSymmetric.abs_re_mul_norm_le_norm_shiftOp z ((shiftEquiv hA hz).symm y)
  have he : shiftOp A z ((shiftEquiv hA hz).symm y) = y := (shiftEquiv hA hz).apply_symm_apply y
  rw [he] at h
  rw [le_inv_mul_iff₀ (abs_pos.2 hz)]
  exact h

/-- **The resolvent of a skew-adjoint operator** exists off the imaginary axis. -/
theorem isResolvent_resolvent (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) :
    IsResolvent A z (resolvent A z) := by
  let R : E →L[𝕜] E := LinearMap.mkContinuous
    (A.domain.subtype ∘ₗ (shiftEquiv hA hz).symm.toLinearMap) (|RCLike.re z|⁻¹)
    (norm_shiftEquiv_symm_le hA hz)
  have hR : IsResolvent A z R :=
    { mem_domain := fun y => ((shiftEquiv hA hz).symm y).2
      sub_apply := fun y => (shiftEquiv hA hz).apply_symm_apply y
      apply_sub := fun x => congrArg Subtype.val ((shiftEquiv hA hz).symm_apply_apply x) }
  exact hR.isResolvent_resolvent

/-- `‖R(z) y‖ ≤ |re z|⁻¹ ‖y‖` for skew-adjoint `A` (Hille–Yosida bound). -/
theorem norm_resolvent_apply_le (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) (y : E) :
    ‖resolvent A z y‖ ≤ |RCLike.re z|⁻¹ * ‖y‖ :=
  (isResolvent_resolvent hA hz).norm_apply_le (abs_pos.2 hz)
    (hA.isSkewSymmetric.abs_re_mul_norm_le_norm_shiftOp z) y

/-- `‖R(z)‖ ≤ |re z|⁻¹` for skew-adjoint `A`. -/
theorem norm_resolvent_le (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) :
    ‖resolvent A z‖ ≤ |RCLike.re z|⁻¹ :=
  (isResolvent_resolvent hA hz).norm_le (abs_pos.2 hz)
    (hA.isSkewSymmetric.abs_re_mul_norm_le_norm_shiftOp z)

/-- `⟪R(z) x, y⟫ = -⟪x, R(-z̄) y⟫` for skew-adjoint `A`. -/
theorem inner_resolvent_left (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) (x y : E) :
    ⟪resolvent A z x, y⟫ = -⟪x, resolvent A (-(starRingEnd 𝕜) z) y⟫ := by
  have hz' : RCLike.re (-(starRingEnd 𝕜) z) ≠ 0 := by
    rw [_root_.map_neg, RCLike.conj_re]; exact neg_ne_zero.2 hz
  have hR := isResolvent_resolvent hA hz
  have hR' := isResolvent_resolvent hA hz'
  set u := hR.toDomain x
  set v := hR'.toDomain y
  have hx : x = z • (u : E) - A u := (hR.sub_apply_toDomain x).symm
  have hy : y = -(starRingEnd 𝕜) z • (v : E) - A v := (hR'.sub_apply_toDomain y).symm
  change ⟪(u : E), y⟫ = -⟪x, (v : E)⟫
  have hs := hA.isSkewSymmetric u v
  conv_lhs => rw [hy]
  conv_rhs => rw [hx]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hs]
  ring

/-- **The adjoint of the resolvent**: `R(z)† = -R(-z̄)` for skew-adjoint `A`. -/
theorem adjoint_resolvent (hA : A.IsSkewAdjoint) (hz : RCLike.re z ≠ 0) :
    ContinuousLinearMap.adjoint (resolvent A z) = -resolvent A (-(starRingEnd 𝕜) z) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun y x => ?_).symm
  have h := congrArg (starRingEnd 𝕜) (inner_resolvent_left hA hz x y)
  rw [inner_conj_symm, _root_.map_neg, inner_conj_symm] at h
  rw [_root_.neg_apply, inner_neg_left, h]

end SkewAdjoint

end Feec.Operator
