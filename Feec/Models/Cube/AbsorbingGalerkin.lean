module

public import Feec.Models.Cube.AbsorbingTSD
public import Feec.HilbertComplex.Approximation.DissipGalerkin
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Semi-discrete Galerkin schemes for the absorbing problem on the cube

Galerkin schemes on dense-sequence spaces for the absorbing generator, as a dissipative FEEC
discretization with constraint `tsdPair`.

## Main results

* `absorbingGalerkin_verdict`: the core is dense and the `dissipFEEC` verdict holds.
* `absorbingGalerkin_residual_not_invariant`: for some TSD datum, the TSD residuals tend to a
  positive limit.
-/

open scoped InnerProductSpace
open Set MeasureTheory Filter Topology Metric TopologicalSpace Feec.HilbertComplex

@[expose] public noncomputable section

namespace Feec.Models.Cube.Absorbing

open Geometry

/-! ### Separability -/

private theorem fact_two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

attribute [local instance] fact_two_ne_top

/-- `L²(Q; ℝ^{3×3})` is separable. -/
instance separableSpace_MQ : SeparableSpace MQ := inferInstance

/-- **The energy space is separable** (a subspace of a finite product of `L²` spaces). -/
instance separableSpace_energySpace : SeparableSpace EnergySpace := by
  have : SecondCountableTopology (WithLp 2 (MQ × Bdry)) := WithLp.secondCountableTopology 2 MQ Bdry
  have : SecondCountableTopology Amb :=
    WithLp.secondCountableTopology 2 MQ (WithLp 2 (MQ × Bdry))
  infer_instance

/-! ### The scheme -/

/-- **Approximating Galerkin data** for the absorbing problem: dense-sequence spaces. -/
def galerkinData : ImpedanceTriple.GalerkinData impedanceTriple ℕ :=
  ImpedanceTriple.GalerkinData.ofDenseSeq impedanceTriple

theorem approximates_galerkinData : galerkinData.Approximates :=
  ImpedanceTriple.GalerkinData.approximates_ofDenseSeq

/-- **The semi-discrete Galerkin scheme** for the absorbing problem, with constraint `tsdPair`. -/
def absorbingGalerkin : DissipFEEC absorbing ℕ :=
  galerkinData.galerkin tsdPair isClosed_tsdPair

/-- Its Trotter–Kato core `R(1) D(A)`. -/
def absorbingGalerkinCore : absorbingGalerkin.Core :=
  galerkinData.galerkinCore tsdPair isClosed_tsdPair approximates_galerkinData

/-- **The absorbing scheme's verdict**: the core is dense and the `dissipFEEC` verdict holds. -/
theorem absorbingGalerkin_verdict :
    absorbingGalerkinCore.Data.topologicalClosure = ⊤ ∧
      absorbingGalerkin.Verdict absorbingGalerkinCore :=
  galerkinData.galerkin_verdict tsdPair isClosed_tsdPair approximates_galerkinData

/-- **Convergence for every datum**: for every `x` and every family of discrete initial values
with `ιₙ vₙ → x`, the semi-discrete solutions converge to `S(t) x` uniformly on `[0, T]`. -/
theorem absorbingGalerkin_converges (T : ℝ) (x : State) {v : ∀ n, absorbingGalerkin.X n}
    (hv : Tendsto (fun n => absorbingGalerkin.incl n (v n)) atTop (𝓝 x)) :
    TendstoUniformlyOn (fun n t => absorbingGalerkin.sol n (v n) t)
      (fun t => absorbingSemigroup.S t x) atTop (Icc 0 T) := by
  have hx : x ∈ absorbingGalerkinCore.Data.topologicalClosure := by
    rw [absorbingGalerkin_verdict.1]; trivial
  exact absorbingGalerkin_verdict.2.converges hx hv T

/-- **The TSD residual has a positive limit**: some TSD datum `x` leaves `tsdPair` at some `t ≤ T`,
and the residuals of every convergent family tend to `dist(S(t) x, tsdPair) > 0`. -/
theorem absorbingGalerkin_residual_not_invariant {T : ℝ} (hT : 0 < T) :
    ∃ x ∈ tsdPair, ∃ t ∈ Icc 0 T, absorbingSemigroup.S t x ∉ tsdPair ∧
      0 < infDist (absorbingSemigroup.S t x) (tsdPair : Set State) ∧
      Tendsto (fun n => absorbingGalerkin.incl n (absorbingGalerkin.proj n x)) atTop (𝓝 x) ∧
      ∀ v : ∀ n, absorbingGalerkin.X n,
        Tendsto (fun n => absorbingGalerkin.incl n (v n)) atTop (𝓝 x) →
        Tendsto (fun n => infDist (absorbingGalerkin.sol n (v n) t) (tsdPair : Set State)) atTop
          (𝓝 (infDist (absorbingSemigroup.S t x) (tsdPair : Set State))) := by
  obtain ⟨hcl, hV⟩ := absorbingGalerkin_verdict
  obtain ⟨x, hxK, t, ht, hout⟩ := hV.leaves not_invariant_tsdPair hT
  have hx : x ∈ absorbingGalerkinCore.Data.topologicalClosure := by rw [hcl]; trivial
  exact ⟨x, hxK, t, ht, hout,
    (isClosed_tsdPair.notMem_iff_infDist_pos ⟨0, tsdPair.zero_mem⟩).1 hout,
    hV.tendsto_incl_proj hx, fun v hv => hV.tendsto_infDist _ hx hv ht.1⟩

/-- **The discrete energy identity**: the energy decreases by twice the discrete outgoing flux. -/
theorem absorbingGalerkin_energy (n : ℕ) (x : absorbingGalerkin.X n) {t : ℝ} (ht : 0 ≤ t) :
    ‖absorbingGalerkin.sol n x t‖ ^ 2 = ‖absorbingGalerkin.incl n x‖ ^ 2 -
      2 * ∫ s in (0 : ℝ)..t,
        ‖galerkinData.Γh n ((C0Group.ofBounded (galerkinData.Lh n)).S s x).fst‖ ^ 2 :=
  galerkinData.norm_sq_galerkin_sol n x ht

end Feec.Models.Cube.Absorbing
