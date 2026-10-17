module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Feec.Legacy.Existence
public import Feec.Semigroup.Stone

/-!
# Stone's theorem for skew-adjoint operators on a real Hilbert space (old interface)

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use.
Most of the original module was re-derived in the general layers (see
`docs/migration/map.tsv`); what remains is listed below.

## Contents

* `shiftEquiv`: `z - A` as a linear equivalence `D(A) ≃ E` (skew-adjoint `A`, `z ≠ 0`).
* `resD`: `(z - A)⁻¹ y ∈ D(A)`, as an element of the domain.
* `shiftOp_resD`: `(z - A) R(z) y = y`.
* `resolvent`: The resolvent `R(z) = (z - A)⁻¹ : E →L[ℝ] E` of a skew-adjoint operator, for real `z ≠ 0` (`Feec.Operator.resolvent`), with `‖R(z)‖ ≤ 1/|z|`.
* `isResolvent_resolvent`
* `resolvent_apply`: `R(z) y` is the domain element `resD hA hz y`.
* `norm_resolvent_apply_le`: `‖R(z)‖ ≤ 1/|z|` (Hille–Yosida resolvent bound for skew-adjoint `A`).
* `apply_resD`: `A R(z) y = z R(z) y - y`.
* `resolvent_apply_domain`: `R(z) (A x) = z R(z) x - x` on `D(A)`; i.e.
* `stoneS`: **The Stone group** `S(t) x = lim_n exp(t B_n) x` (`Feec.Stone.stoneS`).
* `stoneGroup`: **Stone's theorem (existence half), real Hilbert space.** Every skew-adjoint operator `A` generates a strongly continuous orthogonal group, with generator domain exactly `D(A)`: the Stone group `LinearPMap.IsSkewAdjoint.group hA` of `Feec.Semigroup.Stone`.
* `UnitaryGroupGenerator.inner_S_left`: `⟪S(t) a, b⟫ = ⟪a, S(-t) b⟫`.
* `UnitaryGroupGenerator.dense_domain`: The generator of a strongly continuous orthogonal group is densely defined (`C0Group.dense_domain_generator`).

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3), §4.4 (Thm 4.6)
* [Pazy1983], §1.10 (Stone's theorem)
* [Kato1995] (resolvents and the resolvent identity for closed operators)
-/

open scoped RealInnerProductSpace Topology
open Set Filter NormedSpace LinearPMap

@[expose] public noncomputable section

namespace Feec.Legacy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E}

/-! ### The shifted operator `z - A` and the resolvent -/

/-- `z - A` as a linear equivalence `D(A) ≃ E` (skew-adjoint `A`, `z ≠ 0`). -/
def shiftEquiv (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) : A.domain ≃ₗ[ℝ] E :=
  Operator.shiftEquiv (𝕜 := ℝ) hA hz

/-- `(z - A)⁻¹ y ∈ D(A)`, as an element of the domain. -/
def resD (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) : A.domain := (shiftEquiv hA hz).symm y

/-- `(z - A) R(z) y = y`. -/
theorem shiftOp_resD (hA : IsSkewAdjoint A) {z : ℝ} (hz : z ≠ 0) (y : E) :
    z • (resD hA hz y : E) - A (resD hA hz y) = y :=
  (shiftEquiv hA hz).apply_symm_apply y

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

/-! ### The approximating groups `exp(t B_n)` and their strong limit -/

/-- **The Stone group** `S(t) x = lim_n exp(t B_n) x` (`Feec.Stone.stoneS`). -/
def stoneS (hA : IsSkewAdjoint A) (t : ℝ) : E →L[ℝ] E := Stone.stoneS (𝕜 := ℝ) hA t

/-! ### Stone's theorem -/

/-- **Stone's theorem (existence half), real Hilbert space.** Every skew-adjoint operator
`A` generates a strongly continuous orthogonal group, with generator domain exactly `D(A)`:
the Stone group `LinearPMap.IsSkewAdjoint.group hA` of `Feec.Semigroup.Stone`.

Thesis gap: the existence input of [QuennevilleBelair2015, Thm 4.3], cited there from
[CazenaveHaraux1998]; proved here. Cf. [Pazy1983, §1.10], [Brezis2011, Ch. 7]. -/
def stoneGroup (hA : IsSkewAdjoint A) : UnitaryGroupGenerator A :=
  (LinearPMap.IsSkewAdjoint.group hA).toUnitaryGroupGenerator
    (LinearPMap.IsSkewAdjoint.isIsometric_group hA) (LinearPMap.IsSkewAdjoint.generator_group hA)

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

end UnitaryGroupGenerator

end Feec.Legacy
