module

public import Solution.Bounded
public import Feec.Models.Cube.MirrorWeakSymmetryTSD

/-!
# The mirror data of the challenge are those of `Feec`

`dPart J k` is `Feec`'s `d_J` (`dPart_eq`: the challenge's span is the graph of `d_max` on the
forms vanishing near the `J`-faces, whose closure is the graph of `d_J`), so `mirrorData` is the
forms model `Feec.Models.Cube.MirrorWeakSymmetry.mirrorBGGSegment` of the mirror data:
top row `d_∅ = d_max`, bottom row `∏ₐ d_{a}`, `S = wsL2` (`mirrorData_eq`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain
open Feec.Models.Cube.FEM (cubeDomain isOpen_cubeDomain)

variable {n : ℕ}

/-- **`dPart` is `Feec`'s `d_J`.** -/
theorem dPart_eq (J : Finset (Fin n)) (k : ℤ) :
    dPart J k = Feec.Models.Cube.DeRhamIdent.dPart (cubeDomain n) J k := by
  have hS : Submodule.span ℝ {p : L2Form (cube n) k × L2Form (cube n) (k + 1) |
      ∃ h : p.1 ∈ (dMax (cube n) k).domain, dMax (cube n) k ⟨p.1, h⟩ = p.2 ∧
        ∃ δ > 0, ∀ s, ∀ᵐ y ∂volume.restrict (cube n),
          (∃ j ∈ J, y j < δ ∨ 1 / 2 - δ < y j) → p.1 s y = 0} =
      (Feec.Models.Cube.DeRhamIdent.dCore (cubeDomain n) J k).graph := by
    rw [← Submodule.span_eq (Feec.Models.Cube.DeRhamIdent.dCore (cubeDomain n) J k).graph]
    congr 1
    ext ⟨x, y⟩
    have hd := dMax_eq (cube n) k
    refine ⟨fun ⟨h, e, δ, hδ, hv⟩ => ?_, fun hm => ?_⟩
    · refine Feec.Models.Cube.DeRhamIdent.mem_graph_dCore.2 ⟨hd ▸ h, ⟨δ, hδ, hv⟩, ?_⟩
      exact (LinearPMap.apply_of_eq' hd ⟨x, h⟩).symm.trans e
    · obtain ⟨h, ⟨δ, hδ, hv⟩, e⟩ := Feec.Models.Cube.DeRhamIdent.mem_graph_dCore.1 hm
      refine ⟨hd ▸ h, ?_, δ, hδ, hv⟩
      exact (LinearPMap.apply_of_eq' hd.symm ⟨x, h⟩).symm.trans e
  unfold FEEC.dPart
  rw [hS]
  erw [← Feec.Models.Cube.DeRhamIdent.dPart_graph (isOpen_cubeDomain n)]
  refine LinearPMap.eq_of_eq_graph (Submodule.toLinearPMap_graph_eq _ fun x hx h0 => ?_)
  exact LinearPMap.graph_fst_eq_zero_snd _ (x := x.1) (x' := x.2) hx h0

end FEEC
