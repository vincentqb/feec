module

public import Solution.Defs
public import Feec.FiniteElement.PolyComplex

/-!
# Tangential traces

The challenge's `TraceEq` is `Feec.FiniteElement.TangentialTraceEq` (`traceEq_iff`: the value of a
`k`-covector on `k` vectors is the pullback along their matrix, a sum of minors,
`ExteriorFibre.wedgeProd_apply_eq_det_submatrix`). The degrees of freedom of an admissible
sequence on a face of any dimension and its subfaces determine the tangential trace on the face
(`PolySeq.tangentialTraceEq_of_dof_eq_face`; `Feec` states the facet case,
`Feec.FiniteElement.PolySeq.tangentialTraceEq_of_dof_eq`).

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

/-- Tangential traces through a parametrization of a face of any dimension: if the pullbacks
along the edge matrix `B_q` of `q : Fin (j + 1) → ℝⁿ` agree, the tangential traces on the face
`range q` agree. -/
theorem tangentialTraceEq_of_pullback_eq' {j : ℕ} {F : Finset (Fin n → ℝ)} {k : ℕ}
    (q : Fin (j + 1) → Fin n → ℝ) (hq : Set.range q = F) {α β : Finset (Fin n) → ℝ}
    (h : pullback (simplexMatrix q) α = pullback (simplexMatrix q) β) :
    TangentialTraceEq F k α β := by
  intro V hV
  have hV' : ∀ l, ∃ c : Fin j → ℝ, ∀ i, V i l = ∑ m, simplexMatrix q i m * c m := by
    intro l
    have h1 := hV l
    rw [← hq, vectorSpan_range_eq_span_range_vsub_right ℝ q 0,
      Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨fun m => c m.succ, fun i => ?_⟩
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, vsub_eq_sub, Pi.sub_apply, smul_eq_mul,
      Fin.sum_univ_succ, sub_self, mul_zero, zero_add] at this
    rw [← this]
    exact Finset.sum_congr rfl fun m _ => by simp [simplexMatrix, mul_comm]
  choose C hC using hV'
  have hVC : V = fun i l => ∑ m, simplexMatrix q i m * C l m := by
    funext i l; exact hC l i
  rw [hVC, ← pullback_pullback (simplexMatrix q) (fun m l => C l m), h, pullback_pullback]

namespace PolySeq

variable (S : Feec.FiniteElement.PolySeq)

/-- **Trace determination on faces of every dimension**: on a face `F` of `T`, two forms of the
local space with the same degrees of freedom on the faces of `F` have the same tangential trace
on `F`. -/
theorem tangentialTraceEq_of_dof_eq_face [NeZero n] {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {F : Finset (Fin n → ℝ)} {k j : ℕ} (hT : F ⊆ Feec.Mesh.vertexSet T) (hc : #F = j + 1)
    {w η : FormField n} (hw : w ∈ S.space n k) (hη : η ∈ S.space n k)
    (hdof : ∀ g ⊆ F, ∀ i : S.DofIdx g k, S.dof g k i ⟨w, S.space_le_contForms n k hw⟩ =
      S.dof g k i ⟨η, S.space_le_contForms n k hη⟩) :
    ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TangentialTraceEq F k (w x) (η x) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  set p' := lexEnum (Feec.Mesh.vertexSet T) (m + 1)
  have hp' := isUnit_det_edgeMatrix_lexEnum T
  have hmono := strictMono_lexEnum (card_vertexSet T)
  obtain ⟨eF, heF⟩ := exists_orderEmb_comp_eq_lexEnum hmono hc fun x hx =>
    exists_lexEnum_eq_of_mem_vertexSet T (hT hx)
  set q := lexEnum F j
  have hq : Set.range q = F := range_lexEnum hc
  have htr := PolyKind.faceTrace_eq (S.kind k) hp' (S.one_le_deg k) (Face.ofEmb eF) hw hη
    fun g hg ζ hζ => by
      obtain ⟨hcard, hG⟩ := lexEnum_image_comp hmono g.emb.strictMono
      have hGF : Finset.univ.image (p' ∘ g.emb) ⊆ F := fun x hx => by
        obtain ⟨i, -, rfl⟩ := mem_image.1 hx
        have hi := hg (orderEmbOfFin_mem g.2.1 g.2.2 i)
        obtain ⟨a, -, ha⟩ := mem_map.1 hi
        change p' (g.2.1.orderEmbOfFin g.2.2 i) ∈ F
        rw [← ha]
        change (p' ∘ eF) a ∈ F
        rw [heF]
        exact lexEnum_mem hc a
      have h := S.degMoment_eq_of_dof_eq hcard (fun i => hdof _ hGF i) hζ
      rw [hG, degField_eq_self (PolyKind.isDeg_of_mem_space hw),
        degField_eq_self (PolyKind.isDeg_of_mem_space hη)] at h
      exact h
  rw [Face.emb_ofEmb, faceTrace_apply, faceTrace_apply] at htr
  rw [heF, show lexEnum (Feec.Mesh.vertexSet T) (m + 1) (eF 0) = q 0 from congrFun heF 0] at htr
  intro x hx
  rw [← hq] at hx
  obtain ⟨y, -, rfl⟩ := exists_simplexMap_eq_of_mem_convexHull q hx
  refine tangentialTraceEq_of_pullback_eq' q hq ?_
  have := congrFun htr y
  simpa [affinePullback_apply, simplexMap] using this

end PolySeq

end FEEC
