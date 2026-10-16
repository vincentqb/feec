module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Feec.Ch4.Existence
public import Feec.Semigroup.Stone

/-!
# Stone's theorem for skew-adjoint operators on a real Hilbert space (old interface)

Stone's theorem is proved over `𝕜 = ℝ` or `ℂ` in `Feec.Semigroup.Stone`
(`LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup`, `LinearPMap.IsSkewAdjoint.group`).
This module keeps the real-Hilbert-space interface of the thesis formalization, every
declaration re-proved from the general one:

* the resolvent `resolvent hA z = (z - A)⁻¹`, `z ≠ 0` real (`Feec.Operator.resolvent`), with
  `‖R(z)‖ ≤ 1/|z|`, `R(z)† = -R(-z)`, the resolvent identity;
* the bounded skew approximants `approxB` (`Feec.Stone.approxB`), the approximating groups
  `approxU`, and their strong limit `stoneS` (`Feec.Stone.stoneS`);
* **`Feec.stoneGroup hA : UnitaryGroupGenerator A`** (the Stone group
  `(LinearPMap.IsSkewAdjoint.group hA)` with its generator identified with `A`);
* `UnitaryGroupGenerator.dense_domain`, `.isSkewAdjoint`, `.S_eq` (uniqueness), and
  `isSkewAdjoint_iff_nonempty_unitaryGroupGenerator`.

Thesis gap: Thm 4.3 is cited, not proved, in the thesis; its existence input (the homogeneous
group) is proved for every skew-adjoint operator.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3), §4.4 (Thm 4.6)
* [Pazy1983], §1.10 (Stone's theorem)
* [Kato1995] (resolvents and the resolvent identity for closed operators)
-/

open scoped RealInnerProductSpace Topology
open Set Filter NormedSpace LinearPMap

@[expose] public noncomputable section

namespace Feec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

/-- Membership in `D(A†)` with `A† y = w` transfers to `D(A)` with `A y = -w` for skew-adjoint
`A` (`LinearPMap.IsSkewAdjoint.exists_mem_domain_of_inner_eq`). -/
theorem IsSkewAdjoint.mem_domain_of_adjoint (hA : IsSkewAdjoint A) {y w : E}
    (h : ∀ x : A.domain, ⟪w, (x : E)⟫ = ⟪y, A x⟫) :
    ∃ hy : y ∈ A.domain, A ⟨y, hy⟩ = -w :=
  LinearPMap.IsSkewAdjoint.exists_mem_domain_of_inner_eq hA h

/-! ### The shifted operator `z - A` and the resolvent -/

/-- `z - A : D(A) → E` (`Feec.Operator.shiftOp`). -/
def shiftOp (A : E →ₗ.[ℝ] E) (z : ℝ) : A.domain →ₗ[ℝ] E := Operator.shiftOp A z

omit [CompleteSpace E] in
/-- `(z - A) x = z x - A x`. -/
@[simp] theorem shiftOp_apply (z : ℝ) (x : A.domain) : shiftOp A z x = z • (x : E) - A x := rfl

@[deprecated IsSkewSymm.inner_self (since := "2026-10-16")]
alias IsSkewSymm.inner_self_eq_zero := IsSkewSymm.inner_self

omit [CompleteSpace E] in
/-- `‖(z - A) x‖² = z² ‖x‖² + ‖A x‖²` for skew-symmetric `A`. -/
theorem IsSkewSymm.norm_sq_shiftOp (hS : IsSkewSymm A) (z : ℝ) (x : A.domain) :
    ‖shiftOp A z x‖ ^ 2 = z ^ 2 * ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 := by
  rw [shiftOp_apply, norm_sub_sq_real, real_inner_smul_left, real_inner_comm,
    hS.inner_self, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

omit [CompleteSpace E] in
/-- `|z| ‖x‖ ≤ ‖(z - A) x‖` for skew-symmetric `A`
(`LinearPMap.IsSkewSymmetric.abs_re_mul_norm_le_norm_shiftOp`). -/
theorem IsSkewSymm.abs_mul_norm_le (hS : IsSkewSymm A) (z : ℝ) (x : A.domain) :
    |z| * ‖(x : E)‖ ≤ ‖shiftOp A z x‖ :=
  LinearPMap.IsSkewSymmetric.abs_re_mul_norm_le_norm_shiftOp hS z x

omit [CompleteSpace E] in
/-- `z - A` is injective for skew-symmetric `A` and `z ≠ 0`. -/
theorem IsSkewSymm.shiftOp_injective (hS : IsSkewSymm A) {z : ℝ} (hz : z ≠ 0) :
    Function.Injective (shiftOp A z) :=
  LinearPMap.IsSkewSymmetric.injective_shiftOp hS (z := z) hz

/-- The range of `z - A` is orthogonal to nothing: `(range (z - A))ᗮ = ⊥` (for `z ≠ 0`). -/
theorem IsSkewAdjoint.orthogonal_range_shiftOp (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) :
    (LinearMap.range (shiftOp A z))ᗮ = ⊥ :=
  Operator.orthogonal_range_shiftOp (𝕜 := ℝ) hA hz

/-- The range of `z - A` is closed (for `z ≠ 0`). -/
theorem IsSkewAdjoint.isClosed_range_shiftOp (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) :
    IsClosed (LinearMap.range (shiftOp A z) : Set E) :=
  Operator.isClosed_range_shiftOp (𝕜 := ℝ) hA hz

/-- `z - A : D(A) → E` is surjective for skew-adjoint `A` and `z ≠ 0`. -/
theorem IsSkewAdjoint.shiftOp_surjective (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) :
    Function.Surjective (shiftOp A z) :=
  Operator.surjective_shiftOp (𝕜 := ℝ) hA hz

/-- `z - A` as a linear equivalence `D(A) ≃ E` (skew-adjoint `A`, `z ≠ 0`). -/
def shiftEquiv (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) : A.domain ≃ₗ[ℝ] E :=
  Operator.shiftEquiv (𝕜 := ℝ) hA hz

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
  have h := (hA.isSkewSymmetric).abs_mul_norm_le z (resD hA hz y)
  rw [shiftOp_apply, shiftOp_resD] at h
  rw [le_inv_mul_iff₀ (abs_pos.2 hz)]
  exact h

/-- The resolvent `R(z) = (z - A)⁻¹ : E →L[ℝ] E` of a skew-adjoint operator, for real `z ≠ 0`
(`Feec.Operator.resolvent`), with `‖R(z)‖ ≤ 1/|z|`. -/
def resolvent (_hA : IsSkewAdjoint A) (z : ℝ) : E →L[ℝ] E := Operator.resolvent A z

theorem isResolvent_resolvent (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) :
    Operator.IsResolvent A z (resolvent hA z) :=
  Operator.isResolvent_resolvent (𝕜 := ℝ) hA hz

/-- `R(z) y` is the domain element `resD hA hz y`. -/
theorem resolvent_apply (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    resolvent hA z y = (resD hA hz y : E) := by
  have h := (isResolvent_resolvent hA hz).apply_sub (resD hA hz y)
  rwa [shiftOp_resD] at h

/-- `‖R(z)‖ ≤ 1/|z|` (Hille–Yosida resolvent bound for skew-adjoint `A`). -/
theorem norm_resolvent_apply_le (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    ‖resolvent hA z y‖ ≤ |z|⁻¹ * ‖y‖ :=
  Operator.norm_resolvent_apply_le (𝕜 := ℝ) hA hz y

/-- `A R(z) y = z R(z) y - y`. -/
theorem apply_resD (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    A (resD hA hz y) = z • resolvent hA z y - y := by
  rw [resolvent_apply hA hz]
  have h := shiftOp_resD hA hz y
  set u := resD hA hz y
  rw [← h, sub_sub_cancel]

/-- `R(z) (A x) = z R(z) x - x` on `D(A)`; i.e. `R(z)` commutes with `A`. -/
theorem resolvent_apply_domain (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (x : A.domain) :
    resolvent hA z (A x) = z • resolvent hA z x - x :=
  (isResolvent_resolvent hA hz).apply_domain x

/-- `⟪R(z) x, y⟫ = -⟪x, R(-z) y⟫`: the adjoint of `R(z)` is `-R(-z) = (z + A)⁻¹`. -/
theorem inner_resolvent_left (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (x y : E) :
    ⟪resolvent hA z x, y⟫ = -⟪x, resolvent hA (-z) y⟫ :=
  Stone.inner_res_left (𝕜 := ℝ) hA hz x y

/-- The resolvent identity `R(z) - R(w) = (w - z) R(z) R(w)`. -/
theorem resolvent_sub (hA : IsSkewAdjoint A) {z w : ℝ} (hz : z ≠ 0) (hw : w ≠ 0) (y : E) :
    resolvent hA z y - resolvent hA w y = (w - z) • resolvent hA z (resolvent hA w y) := by
  have h := (isResolvent_resolvent hA hz).sub_eq (isResolvent_resolvent hA hw)
  exact congrArg (fun T : E →L[ℝ] E => T y) h

/-- Resolvents commute. -/
theorem resolvent_commute (hA : IsSkewAdjoint A) {z w : ℝ} (hz : z ≠ 0) (hw : w ≠ 0) :
    Commute (resolvent hA z) (resolvent hA w) :=
  (isResolvent_resolvent hA hz).commute (isResolvent_resolvent hA hw)

/-! ### Bounded skew approximants (`Feec.Stone`) -/

/-- The scale `c_n = n + 1` (`Feec.Stone.scale`). -/
def scale (n : ℕ) : ℝ := Stone.scale n

/-- `c_n > 0`. -/
theorem scale_pos (n : ℕ) : 0 < scale n := Stone.scale_pos n

/-- `c_n ≠ 0`. -/
theorem scale_ne_zero (n : ℕ) : scale n ≠ 0 := Stone.scale_ne_zero n

/-- `-c_n ≠ 0`. -/
theorem neg_scale_ne_zero (n : ℕ) : -scale n ≠ 0 := Stone.neg_scale_ne_zero n

/-- `J_n = (c/2) (R(c) - R(-c))` (`Feec.Stone.approxJ`). -/
def approxJ (_hA : IsSkewAdjoint A) (n : ℕ) : E →L[ℝ] E := Stone.approxJ A n

/-- `B_n = (c²/2) (R(c) + R(-c))` (`Feec.Stone.approxB`). -/
def approxB (_hA : IsSkewAdjoint A) (n : ℕ) : E →L[ℝ] E := Stone.approxB A n

/-- `B_n` is skew: `⟪B_n x, y⟫ = -⟪x, B_n y⟫`. -/
theorem approxB_skew (hA : IsSkewAdjoint A) (n : ℕ) (x y : E) :
    ⟪approxB hA n x, y⟫ = -⟪x, approxB hA n y⟫ :=
  Stone.approxB_skew (𝕜 := ℝ) hA n x y

/-- `B_n x = J_n (A x)` on `D(A)`. -/
theorem approxB_apply_domain (hA : IsSkewAdjoint A) (n : ℕ) (x : A.domain) :
    approxB hA n x = approxJ hA n (A x) :=
  Stone.approxB_apply_domain (𝕜 := ℝ) hA n x

/-- `‖J_n‖ ≤ 1`. -/
theorem norm_approxJ_apply_le (hA : IsSkewAdjoint A) (n : ℕ) (y : E) :
    ‖approxJ hA n y‖ ≤ ‖y‖ :=
  Stone.norm_approxJ_apply_le (𝕜 := ℝ) hA n y

/-- `‖B_n x‖ ≤ ‖A x‖` on `D(A)`. -/
theorem norm_approxB_apply_domain_le (hA : IsSkewAdjoint A) (n : ℕ) (x : A.domain) :
    ‖approxB hA n x‖ ≤ ‖A x‖ :=
  Stone.norm_approxB_apply_domain_le (𝕜 := ℝ) hA n x

/-- `‖J_n y - y‖ ≤ ‖A y‖ / c_n` on `D(A)`. -/
theorem norm_approxJ_sub_le (hA : IsSkewAdjoint A) (n : ℕ) (y : A.domain) :
    ‖approxJ hA n y - y‖ ≤ ‖A y‖ / scale n :=
  Stone.norm_approxJ_sub_le (𝕜 := ℝ) hA n y

/-- `c_n → ∞`. -/
theorem tendsto_scale_atTop : Tendsto scale atTop atTop := Stone.tendsto_scale_atTop

omit [CompleteSpace E] in
/-- Strong convergence on a dense set plus a uniform bound `‖T n x‖ ≤ ‖x‖` gives strong
convergence everywhere. -/
theorem tendsto_apply_of_dense {T : ℕ → E →L[ℝ] E} (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) {D : Set E}
    (hD : Dense D) (h : ∀ x ∈ D, Tendsto (fun n => T n x) atTop (𝓝 x)) (x : E) :
    Tendsto (fun n => T n x) atTop (𝓝 x) :=
  Stone.tendsto_apply_of_dense hT hD h x

/-- `J_n y → y` for every `y`. -/
theorem tendsto_approxJ (hA : IsSkewAdjoint A) (y : E) :
    Tendsto (fun n => approxJ hA n y) atTop (𝓝 y) :=
  Stone.tendsto_approxJ (𝕜 := ℝ) hA y

/-- `B_n x → A x` on `D(A)`. -/
theorem tendsto_approxB (hA : IsSkewAdjoint A) (x : A.domain) :
    Tendsto (fun n => approxB hA n x) atTop (𝓝 (A x)) :=
  Stone.tendsto_approxB (𝕜 := ℝ) hA x

/-- The approximants commute (resolvents commute). -/
theorem approxB_commute (hA : IsSkewAdjoint A) (n m : ℕ) :
    Commute (approxB hA n) (approxB hA m) :=
  Stone.approxB_commute (𝕜 := ℝ) hA n m

omit [CompleteSpace E] in
/-- Strong Cauchy-ness on a dense set plus a uniform bound `‖T n x‖ ≤ ‖x‖` gives strong
Cauchy-ness everywhere. -/
theorem cauchySeq_apply_of_dense {T : ℕ → E →L[ℝ] E} (hT : ∀ n x, ‖T n x‖ ≤ ‖x‖) {D : Set E}
    (hD : Dense D) (h : ∀ x ∈ D, CauchySeq fun n => T n x) (x : E) :
    CauchySeq fun n => T n x :=
  Stone.cauchySeq_apply_of_dense hT hD h x

/-! ### The approximating groups `exp(t B_n)` and their strong limit -/

/-- `ℚ`-algebra structure on operators, needed by `NormedSpace.exp_add_of_commute`. -/
local instance instNormedAlgebraRatOpStone : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- The approximating orthogonal groups `U_n(t) = exp(t B_n)` (`Feec.Stone.approxU`). -/
def approxU (_hA : IsSkewAdjoint A) (n : ℕ) (t : ℝ) : E →L[ℝ] E := Stone.approxU A n t

/-- `exp(t B_n)` is an isometry. -/
theorem norm_approxU_apply (hA : IsSkewAdjoint A) (n : ℕ) (t : ℝ) (x : E) :
    ‖approxU hA n t x‖ = ‖x‖ :=
  Stone.norm_approxU_apply (𝕜 := ℝ) hA n t x

/-- Group law for `exp(t B_n)`. -/
theorem approxU_add (hA : IsSkewAdjoint A) (n : ℕ) (s t : ℝ) :
    approxU hA n (s + t) = approxU hA n s * approxU hA n t :=
  Stone.approxU_add (𝕜 := ℝ) n s t

/-- `‖e^{tB_n} x - e^{tB_m} x‖ ≤ |t| ‖B_n x - B_m x‖` (the approximants commute). -/
theorem norm_approxU_sub_le (hA : IsSkewAdjoint A) (n m : ℕ) (t : ℝ) (x : E) :
    ‖approxU hA n t x - approxU hA m t x‖ ≤ |t| * ‖approxB hA n x - approxB hA m x‖ :=
  Stone.norm_approxU_sub_le (𝕜 := ℝ) hA n m t x

/-- `(exp(t B_n) x)_n` is Cauchy. -/
theorem cauchySeq_approxU (hA : IsSkewAdjoint A) (t : ℝ) (x : E) :
    CauchySeq fun n => approxU hA n t x :=
  Stone.cauchySeq_approxU (𝕜 := ℝ) hA t x

/-- **The Stone group** `S(t) x = lim_n exp(t B_n) x` (`Feec.Stone.stoneS`). -/
def stoneS (hA : IsSkewAdjoint A) (t : ℝ) : E →L[ℝ] E := Stone.stoneS (𝕜 := ℝ) hA t

/-- `exp(t B_n) x → S(t) x`. -/
theorem tendsto_approxU (hA : IsSkewAdjoint A) (t : ℝ) (x : E) :
    Tendsto (fun n => approxU hA n t x) atTop (𝓝 (stoneS hA t x)) :=
  Stone.tendsto_approxU (𝕜 := ℝ) hA t x

/-- `exp(t B_n) y_n → S(t) y` whenever `y_n → y` (the `exp(t B_n)` are isometries). -/
theorem tendsto_approxU_of_tendsto (hA : IsSkewAdjoint A) (t : ℝ) {y : ℕ → E} {y₀ : E}
    (hy : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n => approxU hA n t (y n)) atTop (𝓝 (stoneS hA t y₀)) :=
  Stone.tendsto_approxU_of_tendsto (𝕜 := ℝ) hA t hy

/-- `S(t)` is an isometry. -/
theorem norm_stoneS_apply (hA : IsSkewAdjoint A) (t : ℝ) (x : E) : ‖stoneS hA t x‖ = ‖x‖ :=
  Stone.norm_stoneS_apply (𝕜 := ℝ) hA t x

/-- `S(0) = 1`. -/
theorem stoneS_zero (hA : IsSkewAdjoint A) : stoneS hA 0 = 1 := Stone.stoneS_zero (𝕜 := ℝ) hA

/-- `S(s + t) = S(s) S(t)`. -/
theorem stoneS_add (hA : IsSkewAdjoint A) (s t : ℝ) :
    stoneS hA (s + t) = stoneS hA s * stoneS hA t :=
  Stone.stoneS_add (𝕜 := ℝ) hA s t

/-- `‖S(t) x - S(s) x‖ ≤ |t - s| ‖A x‖` on `D(A)`. -/
theorem norm_stoneS_sub_le (hA : IsSkewAdjoint A) (x : A.domain) (t s : ℝ) :
    ‖stoneS hA t x - stoneS hA s x‖ ≤ |t - s| * ‖A x‖ :=
  Stone.norm_stoneS_sub_le (𝕜 := ℝ) hA x t s

/-- Strong continuity: `t ↦ S(t) x` is continuous. -/
theorem continuous_stoneS_apply (hA : IsSkewAdjoint A) (x : E) :
    Continuous fun t => stoneS hA t x :=
  Stone.continuous_stoneS_apply (𝕜 := ℝ) hA x

/-- `S(t) x - x = ∫₀ᵗ S(s) (A x) ds` on `D(A)`. -/
theorem stoneS_sub_eq_integral (hA : IsSkewAdjoint A) (x : A.domain) (t : ℝ) :
    stoneS hA t x - x = ∫ s in (0 : ℝ)..t, stoneS hA s (A x) :=
  Stone.stoneS_sub_eq_integral (𝕜 := ℝ) hA x t

/-- The generator of `S` extends `A`: `(d/dt) S(t) x |_{t=0} = A x` on `D(A)`. -/
theorem hasDerivAt_stoneS_zero (hA : IsSkewAdjoint A) (x : A.domain) :
    HasDerivAt (fun t => stoneS hA t x) (A x) 0 :=
  Stone.hasDerivAt_stoneS_zero (𝕜 := ℝ) hA x

/-- `⟪S(h) x, z⟫ = ⟪x, S(-h) z⟫`: `S(h)` is orthogonal with inverse `S(-h)`. -/
theorem inner_stoneS_left (hA : IsSkewAdjoint A) (h : ℝ) (x z : E) :
    ⟪stoneS hA h x, z⟫ = ⟪x, stoneS hA (-h) z⟫ :=
  (Stone.isIsometric_group (𝕜 := ℝ) hA).inner_S_left h x z

/-! ### Stone's theorem -/

/-- **Stone's theorem (existence half), real Hilbert space.** Every skew-adjoint operator
`A` generates a strongly continuous orthogonal group, with generator domain exactly `D(A)`:
the Stone group `LinearPMap.IsSkewAdjoint.group hA` of `Feec.Semigroup.Stone`.

Thesis gap: the existence input of [QuennevilleBelair2015, Thm 4.3], cited there from
[CazenaveHaraux1998]; proved here. Cf. [Pazy1983, §1.10], [Brezis2011, Ch. 7]. -/
def stoneGroup (hA : IsSkewAdjoint A) : UnitaryGroupGenerator A :=
  (LinearPMap.IsSkewAdjoint.group hA).toUnitaryGroupGenerator
    (LinearPMap.IsSkewAdjoint.isIsometric_group hA) (LinearPMap.IsSkewAdjoint.generator_group hA)

/-- The generator of `S` is exactly `A`, domain included
(`LinearPMap.IsSkewAdjoint.generator_group`). -/
theorem mem_domain_iff_differentiableAt_stoneS (hA : IsSkewAdjoint A) (x : E) :
    x ∈ A.domain ↔ DifferentiableAt ℝ (fun t => stoneS hA t x) 0 :=
  (stoneGroup hA).mem_domain_iff x

/-! ### The converse half of Stone's theorem, and uniqueness of the group -/

namespace UnitaryGroupGenerator

variable {L : E →ₗ.[ℝ] E}

omit [CompleteSpace E] in
/-- `⟪S(t) a, b⟫ = ⟪a, S(-t) b⟫`. -/
theorem inner_S_left (G : UnitaryGroupGenerator L) (t : ℝ) (a b : E) :
    ⟪G.S t a, b⟫ = ⟪a, G.S (-t) b⟫ :=
  G.isIsometric_toC0Group.inner_S_left t a b

/-- The generator of a strongly continuous orthogonal group is densely defined
(`C0Group.dense_domain_generator`). -/
theorem dense_domain (G : UnitaryGroupGenerator L) : Dense (L.domain : Set E) := by
  have h := G.toC0Group.dense_domain_generator
  rwa [G.generator_toC0Group] at h

/-- **Stone's theorem, converse half**: the generator of a strongly continuous orthogonal
group is skew-adjoint (`C0Group.IsIsometric.isSkewAdjoint_generator`). -/
theorem isSkewAdjoint (G : UnitaryGroupGenerator L) : IsSkewAdjoint L := by
  have h := G.isIsometric_toC0Group.isSkewAdjoint_generator
  rwa [G.generator_toC0Group] at h

/-- **Uniqueness**: a strongly continuous orthogonal group is determined by its generator
(`C0Group.IsIsometric.ext_of_generator_eq`). -/
theorem S_eq (G G' : UnitaryGroupGenerator L) : G.S = G'.S :=
  congrArg C0Group.S (G.isIsometric_toC0Group.ext_of_generator_eq
    (G.generator_toC0Group.trans G'.generator_toC0Group.symm))

end UnitaryGroupGenerator

/-- **Stone's theorem** (real Hilbert space form): `A` is skew-adjoint iff it generates a
strongly continuous orthogonal group (`LinearPMap.isSkewAdjoint_iff_existsUnique_isometricGroup`
for the general form). -/
theorem isSkewAdjoint_iff_nonempty_unitaryGroupGenerator :
    IsSkewAdjoint A ↔ Nonempty (UnitaryGroupGenerator A) :=
  ⟨fun hA => ⟨stoneGroup hA⟩, fun ⟨G⟩ => G.isSkewAdjoint⟩

/-- Every orthogonal group generated by a skew-adjoint `A` is the Stone group `stoneS`, the
strong limit of `exp(t B_n)`. -/
theorem UnitaryGroupGenerator.S_eq_stoneS (hA : IsSkewAdjoint A) (G : UnitaryGroupGenerator A) :
    G.S = stoneS hA :=
  G.S_eq (stoneGroup hA)

end Feec
