module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closed operators and the Bochner integral

* `LinearPMap.mem_graph_iff_exists`: membership in the graph, in domain form.
* `LinearPMap.integral_mem_graph_of_isClosed` (**Hille**): a closed operator commutes with the
  Bochner integral over `(a,b]`.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.2
* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §II.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Set MeasureTheory

@[expose] public section

namespace LinearPMap

/-- Membership in the graph, in domain form. -/
theorem mem_graph_iff_exists {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] {A : E →ₗ.[R] F} {x : E} {v : F} :
    (x, v) ∈ A.graph ↔ ∃ h : x ∈ A.domain, A ⟨x, h⟩ = v :=
  ⟨fun h => ⟨LinearPMap.mem_domain_of_mem_graph h,
    ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph h)).2 h).symm⟩,
   fun ⟨h, e⟩ => e ▸ A.mem_graph ⟨x, h⟩⟩

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

/-- **Hille's theorem for closed operators**: if `A` is closed, `f` and `H` are integrable on
`(a,b]` and `(f s, H s)` lies in the graph of `A` for a.e. `s`, then
`(∫ₐᵇ f, ∫ₐᵇ H)` lies in the graph of `A`. -/
theorem integral_mem_graph_of_isClosed {A : E →ₗ.[𝕜] E} (hA : A.IsClosed) {f H : ℝ → E}
    {a b : ℝ} (hab : a ≤ b) (hf : IntegrableOn f (Ioc a b)) (hH : IntegrableOn H (Ioc a b))
    (hfH : ∀ᵐ s ∂(volume.restrict (Ioc a b)), (f s, H s) ∈ A.graph) :
    (∫ s in a..b, f s, ∫ s in a..b, H s) ∈ A.graph := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← integral_pair hf hH]
  set K : Submodule ℝ (E × E) := A.graph.restrictScalars ℝ
  have hK : _root_.IsClosed (K : Set (E × E)) := hA
  rcases hab.lt_or_eq with hab | rfl
  · have h0 : volume (Ioc a b) ≠ 0 := by simp [hab]
    have hfin : volume (Ioc a b) ≠ ⊤ := by simp
    have havg := K.convex.set_average_mem hK h0 hfin hfH (hf.prodMk hH)
    rw [setAverage_eq] at havg
    have := K.smul_mem (volume.real (Ioc a b)) havg
    rwa [smul_inv_smul₀ (by rw [Real.volume_real_Ioc_of_le hab.le]; linarith)] at this
  · simp only [Ioc_self, Measure.restrict_empty, integral_zero_measure]
    exact A.graph.zero_mem

end LinearPMap
