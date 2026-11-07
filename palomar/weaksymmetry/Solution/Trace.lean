module

public import Solution.Defs
public import Feec.FiniteElement.PolyComplex

/-!
# Tangential traces

The challenge's `TraceEq` is `Feec.FiniteElement.TangentialTraceEq` (`traceEq_iff`: the value of a
`k`-covector on `k` vectors is the pullback along their matrix, a sum of minors,
`ExteriorFibre.wedgeProd_apply_eq_det_submatrix`). The degrees of freedom of an admissible
sequence on a face of any dimension and its subfaces determine the tangential trace on the face
(`Feec.FiniteElement.PolySeq.tangentialTraceEq_of_dof_eq_face`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3, §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset

@[expose] public noncomputable section

namespace FEEC

open Feec.FiniteElement Feec.ExteriorFibre Feec.Mesh

variable {n : ℕ}

theorem univ_orderEmbOfFin_apply {k : ℕ} (h : (Finset.univ : Finset (Fin k)).card = k)
    (j : Fin k) : Finset.univ.orderEmbOfFin h j = j := by
  have := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin k))) h
    (f := id) (fun x => Finset.mem_univ x) strictMono_id
  exact (congrFun this j).symm

/-- **The value of a covector on vectors is the pullback along their matrix.** -/
theorem covEval_eq {k : ℕ} (α : Finset (Fin n) → ℝ) (v : Fin k → Fin n → ℝ) :
    covEval α v = pullback (fun i l => v l i) α univ := by
  rw [pullback_apply, covEval]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hu : (univ : Finset (Fin k)).card = k := by simp
  split_ifs with hs
  · rw [wedgeProd_apply_eq_det_submatrix _ hs hu]
    congr 2
    ext i l
    simp [univ_orderEmbOfFin_apply hu]
  · rw [isDeg_wedgeProd _ s univ (by rw [hu]; exact Ne.symm hs), mul_zero]

/-- **`TraceEq` is `Feec`'s `TangentialTraceEq`.** -/
theorem traceEq_iff (g : Finset (Fin n → ℝ)) (k : ℕ) (α β : Finset (Fin n) → ℝ) :
    TraceEq g k α β ↔ TangentialTraceEq g k α β := by
  constructor
  · intro h V hV
    have := h (fun l i => V i l) hV
    rwa [covEval_eq, covEval_eq] at this
  · intro h v hv
    rw [covEval_eq, covEval_eq]
    exact h (fun i l => v l i) hv

end FEEC
