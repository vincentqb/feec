module

public import Feec.Models.Cube.TangentialRate
public import Feec.Models.Cube.WeakSymmetryWave

/-!
# Thm 5.5 and the rate of (6.5) on the cube for solutions with vanishing tangential traces

The rates of `Feec.Models.Cube.WeakSymmetryFEM` (`cubeFEM_rate_C2`, `cubeFEM_rate_isSaddle`, thesis
Thm 5.5 with the elements of Table 5.1) and of `Feec.Models.Cube.WeakSymmetryWave`
(`cubeWave_rate`, the semi-discrete scheme (6.5) of Table 6.1) are stated for `FEM.IsCsFormMin`,
`C²` fields on `ℝ³` vanishing outside `Q` (flat at `∂Q`). This module restates them on the natural
class `FEM.IsCsFormTr 0` (`Feec.Models.Cube.TangentialRate`): `C²` fields **up to the boundary**
(restrictions to `Q` of `C²` fields on `ℝ³`; this matches "`C²` on `cl Q`" through an extension
theorem for the cube, which is not formalized) whose tangential components vanish on `∂Q`, with no
condition on the normal components.

* **The class of `S¹u` is derived** from that of `u` (`exists_isCsFormTr_segS1`: the tangential
  trace of `dxₐ ∧ uₐ` vanishes with that of `uₐ`), so `cubeFEM_rate_tr`, `cubeFEM_rate_isSaddle_tr`
  and `IsSmoothStateTr` put no hypothesis on `S¹u`.
* The `L²` bound of a field is now its sup bound (`IsCsFormTr.norm_le`), and the bound
  `|⟪x, d w⟫| ≤ c L ‖w‖` for `w ∈ H̊Λ¹(Q)` is **Green's formula** `⟪x, d w⟫ = ⟪δx, w⟫` on `D(d_min)`
  (`IsCsForm.abs_inner_D1_le`: no boundary condition on `x` at all).
* The interpolation errors (`cubeFEM_err_P0_tr`, …, `cubeFEM_err_Pt2_tr`) come from
  `IsCsFormTr.exists_mem_polyMin_le` (the canonical interpolant of a field with vanishing
  tangential traces has vanishing boundary DOFs).
* **`cubeFEM_rate_tr`** (Thm 5.5), `cubeFEM_rate_tr_of_bounds`, `cubeFEM_rate_isSaddle_tr`;
  **`cubeFEM_ellipticProjection_rate_tr`** (the `O(h)` rate of the elliptic projection (6.4) on the
  cube, the cube form of `Feec.BGG.Discrete.strang_rate_of_regularPotential`);
  `IsSmoothStateTr`, **`cubeWave_rate_tr`** (the `O(h)` rate of (6.5)).
* Every flat form is a form of the new class with the same bound (`FEM.IsCsFormMin.isCsFormTr`).
* **Non-vacuity beyond flat data**: `tangentialManufactured_solution` is a smooth solution of (5.3)
  (`σ = φ = λ = 0`, `u = ((sin 2πy₁ sin 2πy₂) dx₀, 0, 0)`, divergence free with `S¹u = 0`) whose
  normal component does not vanish on `∂Q` (`normalWitness_ne_zero`, the first row being
  `normalWitness`) and which is not flat (`not_isCsFormMin_tangentialU0`); `waveTangential T` is
  a classical solution of (6.2) built on it (`u(t) = ū`, `ρ(t) = t curl ū`, `M = 0`), meeting
  the hypotheses of `cubeWave_rate_tr` (`waveTangential_hyps`). `combinedManufactured_solution` adds the flat
  coupled solution of `Feec.Models.Cube.WeakSymmetryFEM` to it: `σ, φ, λ ≠ 0` and `u` not flat
  (`not_isCsFormMin_coupledu_add_tangentialU`, through `IsCsFormMin.sub`).

**Boundary conditions on `M` and `ρ`.** The discrete fields `Mₕ ∈ P₁⁻Λ̊²` and
`ρₕ ∈ P₁Λ̊² ⊗ ℝ³` have vanishing boundary DOFs (Table 6.1 with the thesis' boundary conditions),
so `‖M − Mₕ‖ ≥ dist_{L²}(M, P₁⁻Λ̊²)`, which is of order `h^{1/2}`, not `h`, for a smooth `M` whose
tangential trace on `∂Q` (the normal flux of the associated vector field) does not vanish (boundary
layer of width `h`; this lower bound is a standard argument and is **not formalized**). The `O(h)`
rate therefore requires `M, ρ` in `IsCsFormTr`; along a solution of (6.2), `M(t) − M(0) = ∫ S¹u` and
`ρ(t) − ρ(0) = ∫ du` have vanishing tangential traces whenever `u` does, so the condition is one on
the initial data `M(0)`, `ρ(0)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Table 5.1, Thm 5.5; §6.2 (6.4), §6.3 (6.5), Table 6.1
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (vanishing tangential
  traces), Ch. 7 (approximation estimates)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace ContDiff
open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM

/-! ### Bounds of smooth fields: sup bounds and Green's formula -/

section SmoothBounds

/-- **`L²` bound from the sup bound**: `‖x‖ ≤ #(formIdx) L` for `IsCsFormTr s j L x` (`|Q| ≤ 1`). -/
theorem _root_.Feec.Models.Cube.FEM.IsCsFormTr.norm_le {s : ℕ} {j : ℤ} {L : ℝ}
    {x : L2F ℝ (cubeDomain 3) (formIdx 3 j)} (hx : IsCsFormTr s j L x) (hL0 : 0 ≤ L) :
    ‖x‖ ≤ Fintype.card (formIdx 3 j) * L := by
  rcases hx with hj | ⟨k, rfl, w, hw, -, -, hL, rfl⟩
  · rw [norm_eq_zero_of_neg hj]; positivity
  refine norm_L2F_le_of_bound _ hL0 fun t => ?_
  filter_upwards [coeFn_formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) k
    ⟨w, hw.continuous⟩ t, ae_restrict_mem (isOpen_cubeDomain 3).measurableSet] with y h1 hy
  rw [h1]
  calc ‖(w y) t.1‖ ≤ ‖w y‖ := norm_le_pi_norm (w y) t.1
    _ ≤ L := by simpa using (hL 0 (Nat.zero_le _) y (subset_closure hy)).1

/-- The Green bound for the class `IsCsFormTr` (which carries no condition used by it). -/
theorem _root_.Feec.Models.Cube.FEM.IsCsFormTr.abs_inner_D1_le {L : ℝ} {x : W2}
    (hx : IsCsFormTr 0 2 L x) (hL0 : 0 ≤ L) (w : U1) :
    |⟪x, D1 w⟫| ≤ (Fintype.card (formIdx 3 1) * (3 * L)) * ‖w‖ :=
  hx.isCsForm.abs_inner_D1_le hL0 w

end SmoothBounds

/-! ### Regularity of `S¹u` from that of `u` -/

section S1Regularity

open Feec.ExteriorFibre

/-- The fibre maps `v ↦ dxₐ ∧ v` of `S` (`S v = Σₐ dxₐ ∧ vₐ`) on `ℝ³`. -/
def coordWedgeCLM (a : Fin 3) : (Finset (Fin 3) → ℝ) →L[ℝ] (Finset (Fin 3) → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((coordWedgeSumₗ : (Fin 3 → Finset (Fin 3) → ℝ) →ₗ[ℝ] _) ∘ₗ
      LinearMap.single ℝ (fun _ : Fin 3 => Finset (Fin 3) → ℝ) a)

/-- `S v = Σₐ dxₐ ∧ vₐ` as a sum of fibre maps. -/
theorem coordWedgeField_eq_sum (v : Fin 3 → FormField 3) :
    coordWedgeField v = ∑ a, (coordWedgeCLM a) ∘ v a := by
  funext x
  rw [coordWedgeField_apply, Finset.sum_apply]
  conv_lhs => rw [← Finset.univ_sum_single (fun i => v i x)]
  rw [coordWedgeSum_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rfl

/-- Derivative bounds for `S v` from those of the `vₐ`. -/
theorem norm_iteratedFDeriv_coordWedgeField_le_sum {v : Fin 3 → FormField 3} {m : ℕ}
    (hv : ∀ a, ContDiff ℝ m (v a)) {L : ℝ} {i : ℕ} (hi : i ≤ m) {y : Fin 3 → ℝ}
    (h : ∀ a, ‖iteratedFDeriv ℝ i (v a) y‖ ≤ L) :
    ‖iteratedFDeriv ℝ i (coordWedgeField v) y‖ ≤ (∑ a, ‖coordWedgeCLM a‖) * L := by
  have hi' : (i : WithTop ℕ∞) ≤ m := by exact_mod_cast hi
  rw [coordWedgeField_eq_sum, iteratedFDeriv_sum_apply fun a _ =>
    ((coordWedgeCLM a).contDiff.comp ((hv a).of_le hi')).contDiffAt, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  exact ((coordWedgeCLM a).norm_iteratedFDeriv_comp_left (hv a).contDiffAt hi').trans
    (mul_le_mul_of_nonneg_left (h a) (norm_nonneg _))

/-- `S` preserves vanishing tangential traces: for `j ∉ t`, `j ∉ t ∖ {l}`. -/
theorem isTangentialZero_coordWedgeField {v : Fin 3 → FormField 3}
    (hv : ∀ a, IsTangentialZero (v a)) : IsTangentialZero (coordWedgeField v) := by
  intro y hy j t hjt hyj
  rw [coordWedgeField_apply, coordWedgeSum_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l hl => ?_
  rw [hv i y hy j (t.erase l) (fun h' => hjt (Finset.mem_of_mem_erase h')) hyj, mul_zero]

/-- **`S¹u` inherits the class of `u`**: if every component `uₐ` is a `C²` `1`-form with vanishing
tangential traces and bound `L` (`IsCsFormTr 0`), then `S¹u = Σₐ dxₐ ∧ uₐ` is a `C²` `2`-form with
vanishing tangential traces and bound `c L`, with `c` universal: the tangential trace of
`dxₐ ∧ uₐ` on a face vanishes with that of `uₐ` (`isTangentialZero_coordWedgeField`),
`d(S¹u) = −Σₐ dxₐ ∧ duₐ` (`extDeriv_coordWedgeField_eq`), and the derivatives are bounded through
the fibre maps (`norm_iteratedFDeriv_coordWedgeField_le_sum`). -/
theorem exists_isCsFormTr_segS1 : ∃ c : ℝ, 1 ≤ c ∧ ∀ (u : Wv U1) {L : ℝ}, 0 ≤ L →
    (∀ a, IsCsFormTr 0 1 L (u a : W1)) → IsCsFormTr 0 2 (c * L) (bggSegment.S1 u) := by
  have hc0 : 0 ≤ ∑ a, ‖coordWedgeCLM a‖ := Finset.sum_nonneg fun a _ => norm_nonneg _
  refine ⟨1 + ∑ a, ‖coordWedgeCLM a‖, by linarith, fun u L hL0 hu => ?_⟩
  have hex : ∀ a, ∃ w : FormField 3, ∃ hw : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) w,
      (∀ y, IsDeg 1 (w y)) ∧ IsTangentialZero w ∧
      (∀ i ≤ 0 + 1, ∀ y ∈ closure (cubeDomain 3),
        ‖iteratedFDeriv ℝ i w y‖ ≤ L ∧ ‖iteratedFDeriv ℝ i (FiniteElement.extDeriv w) y‖ ≤ L) ∧
      (u a : W1) = formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 1
        ⟨w, hw.continuous⟩ := by
    intro a
    rcases hu a with h | ⟨k, hk, w, hw, hdeg, htan, hL, he⟩
    · exact absurd h (by norm_num)
    · obtain rfl : k = 1 := by exact_mod_cast hk
      exact ⟨w, hw, hdeg, htan, hL, he⟩
  choose w hw hdeg htan hL he using hex
  have hw2 : ∀ a, ContDiff ℝ 2 (w a) := fun a => by simpa using hw a
  have hw1 : ∀ a, ContDiff ℝ 1 (w a) := fun a => (hw2 a).of_le (by norm_num)
  have hdw : ∀ a, ContDiff ℝ 1 (FiniteElement.extDeriv (w a)) := fun a =>
    contDiff_extDeriv (by simpa [one_add_one_eq_two] using hw2 a)
  have hW : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) (coordWedgeField w) :=
    contDiff_coordWedgeField hw
  have hcL : (∑ a, ‖coordWedgeCLM a‖) * L ≤ (1 + ∑ a, ‖coordWedgeCLM a‖) * L := by nlinarith
  refine Or.inr ⟨2, rfl, coordWedgeField w, hW, fun y => isDeg_coordWedgeField hdeg y,
    isTangentialZero_coordWedgeField htan, fun i hi y hy => ⟨?_, ?_⟩, ?_⟩
  · exact (norm_iteratedFDeriv_coordWedgeField_le_sum hw (by omega)
      fun a => (hL a i hi y hy).1).trans hcL
  · rw [extDeriv_coordWedgeField_eq hw1, iteratedFDeriv_neg_apply, norm_neg]
    exact (norm_iteratedFDeriv_coordWedgeField_le_sum (m := 1) (fun a => by exact_mod_cast hdw a)
      (by omega)
      fun a => (hL a i hi y hy).2).trans hcL
  · change wsL2 (Ω := cubeDomain 3) 1 (incl1 u) = _
    refine PiLp.ext fun t => Lp.ext ?_
    rw [wsL2_apply]
    have h1 := Lp.coeFn_finsetSum Finset.univ fun p : Fin 3 × formIdx 3 1 =>
      wsCoeff 1 t p • (incl1 u) p.1 p.2
    have h2 : ∀ p : Fin 3 × formIdx 3 1,
        (((wsCoeff 1 t p • (incl1 u) p.1 p.2 : L2 ℝ (cubeDomain 3))) : (Fin 3 → ℝ) → ℝ) =ᵐ[
          volume.restrict (cubeDomain 3)] fun x => wsCoeff 1 t p * w p.1 x p.2.1 := by
      intro p
      have e : (incl1 u) p.1 = formL2 (isOpen_cubeDomain 3).measurableSet
          (isBounded_cubeDomain 3) 1 ⟨w p.1, (hw p.1).continuous⟩ := he p.1
      rw [e]
      filter_upwards [Lp.coeFn_smul (wsCoeff 1 t p) (formL2 (isOpen_cubeDomain 3).measurableSet
          (isBounded_cubeDomain 3) 1 ⟨w p.1, (hw p.1).continuous⟩ p.2),
        coeFn_formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 1
          ⟨w p.1, (hw p.1).continuous⟩ p.2] with x hx1 hx2
      rw [hx1, Pi.smul_apply, smul_eq_mul, hx2]
    filter_upwards [h1, ae_all_iff.2 h2, coeFn_formL2 (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) 2 ⟨coordWedgeField w, hW.continuous⟩ t] with x hx1 hx2 hx3
    rw [hx1, Finset.sum_apply, hx3]
    simp only [hx2]
    rw [coordWedgeField_apply]
    exact (coordWedgeSum_eq_sum_wsCoeff (k := 1) (fun a => hdeg a x) t).symm

end S1Regularity

/-! ### Projection errors -/

section ProjError

/-- Interpolation of a `C²` scalar field vanishing on `∂Q` (degree `0`), in the graph norm. -/
theorem exists_approx_zero_tr {S : PolySeq} {L : ℝ} (hL0 : 0 ≤ L) (N : ℕ) (σ : U0)
    (hσ : IsCsFormTr 0 0 L (σ : W0)) :
    ∃ v, ∃ hv : v ∈ (polyMin 3 S N).V 0,
      ‖(σ : W0) - v‖ ≤ polyInterpBound 3 S 0 * L * meshSize N ∧
      ‖D0 ⟨(σ : W0) - v, D0.domain.sub_mem σ.2 (mem_D0_of_mem_V hv)⟩‖ ≤
        polyInterpBound 3 S 0 * L * meshSize N := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_polyMin_le ((polyOrder_zero S).polyOrderAt 0) hL0 N
  refine ⟨v, hv, by simpa using h1, ?_⟩
  have h := h2 1 (mem_dom01 σ.2)
  rw [d01_apply] at h
  simpa using h

/-- Interpolation of a `C²` `1`-form with vanishing tangential traces, in the graph norm. -/
theorem exists_approx_one_tr {S : PolySeq} {L : ℝ} (hL0 : 0 ≤ L) (N : ℕ) (u : U1)
    (hu : IsCsFormTr 0 1 L (u : W1)) :
    ∃ v, ∃ hv : v ∈ (polyMin 3 S N).V 1,
      ‖(u : W1) - v‖ ≤ polyInterpBound 3 S 1 * L * meshSize N ∧
      ‖D1 ⟨(u : W1) - v, D1.domain.sub_mem u.2 (mem_D1_of_mem_V hv)⟩‖ ≤
        polyInterpBound 3 S 1 * L * meshSize N := by
  obtain ⟨v, hv, h1, h2⟩ := hu.exists_mem_polyMin_le ((polyOrder_zero S).polyOrderAt 1) hL0 N
  refine ⟨v, hv, by simpa using h1, ?_⟩
  have h := h2 2 (mem_dom12 u.2)
  rw [d12_apply] at h
  simpa using h



end ProjError

section CubeFEM

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

theorem cubeFEM_err_P0_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (σ : U0) (hσ : IsCsFormTr 0 0 L (σ : W0)) :
    Feec.BGG.graphSq bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ) ≤
      2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 0) ^ 2 * (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  obtain ⟨v, hv, hv1, hv2⟩ := exists_approx_zero_tr (S := PolySeq.lowestOrder) hL0 N σ hσ
  refine (graphSq_projU0_sub_le (hT.proj N) (hT.norm_proj_le N 1) (hT.norm_proj_le N 0) σ hv
    hv1 hv2 hA).trans (le_of_eq ?_)
  ring

theorem cubeFEM_err_Pt0_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (φ : Wv U0)
    (hφ : ∀ a, IsCsFormTr 0 0 L (φ a : W0)) :
    Feec.BGG.graphSq bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ) ≤
      3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 0) ^ 2) *
        (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  rw [cubeFEM, bggDiscrete_Pt0, bggSegment_dt0, graphSq_piMap]
  calc ∑ a, Feec.BGG.graphSq segD0 ((piMap (projU0 (hB.proj N)) φ - φ) a) ≤
        ∑ _a : Fin 3, 2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 0) ^ 2 *
          (L * meshSize N) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        obtain ⟨v, hv, hv1, hv2⟩ := exists_approx_zero_tr (S := PolySeq.lagrangeP2) hL0 N (φ a)
          (hφ a)
        refine (graphSq_projU0_sub_le (hB.proj N) (hB.norm_proj_le N 1) (hB.norm_proj_le N 0)
          (φ a) hv hv1 hv2 hA).trans (le_of_eq ?_)
        ring
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem cubeFEM_err_Pt1_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (u : Wv U1)
    (hu : ∀ a, IsCsFormTr 0 1 L (u a : W1)) :
    Feec.BGG.graphSq bggSegment.dt1 ((cubeFEM hT hB N).Pt1 u - u) ≤
      3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2) *
        (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  rw [cubeFEM, bggDiscrete_Pt1, bggSegment_dt1, graphSq_piMap]
  calc ∑ a, Feec.BGG.graphSq segD1 ((piMap (projU1 (hB.proj N)) u - u) a) ≤
        ∑ _a : Fin 3, 2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2 *
          (L * meshSize N) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        obtain ⟨v, hv, hv1, hv2⟩ := exists_approx_one_tr (S := PolySeq.lagrangeP2) hL0 N (u a)
          (hu a)
        refine (graphSq_projU1_sub_le (hB.proj N) (hB.norm_proj_le N 2) (hB.norm_proj_le N 1)
          (u a) hv hv1 hv2 hA).trans (le_of_eq ?_)
        ring
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem cubeFEM_err_gnSq_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (u : Wv U1)
    (hu : ∀ a, IsCsFormTr 0 1 L (u a : W1)) :
    (cubeFEM hT hB N).gnSq ((cubeFEM hT hB N).Pt1 u - u) ≤
      (1 + 8 * C ^ 2) * (3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2)) *
        (L * meshSize N) ^ 2 := by
  have h1 := cubeFEM_gnSq_le hT hB N ((cubeFEM hT hB N).Pt1 u - u)
  have h2 := mul_le_mul_of_nonneg_left (cubeFEM_err_Pt1_tr hT hB N hL0 u hu)
    (by positivity : (0 : ℝ) ≤ 1 + 8 * C ^ 2)
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := by ring

theorem cubeFEM_err_S1_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (u : Wv U1)
    (hSu : IsCsFormTr 0 2 L (bggSegment.S1 u)) :
    ‖bggSegment.S1 u - (cubeFEM hT hB N).S1h u‖ ^ 2 ≤
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  obtain ⟨v, hv, hv1, -⟩ := hSu.exists_mem_polyMin_le (S := PolySeq.lowestOrder)
    ((polyOrder_zero _).polyOrderAt 2) hL0 N
  have h' : ‖bggSegment.S1 u - (cubeFEM hT hB N).S1h u‖ ≤
      (1 + 2 * C) * (polyInterpBound 3 PolySeq.lowestOrder 2 * L * meshSize N) := by
    change ‖segS1 u - (hT.proj N).π 2 (segS1 u)‖ ≤ _
    refine (norm_sub_π_le_of_mem (hT.proj N) (hT.norm_proj_le N 2) hv).trans
      (mul_le_mul_of_nonneg_left ?_ hA)
    have hv1' : ‖bggSegment.S1 u - v‖ ≤ polyInterpBound 3 PolySeq.lowestOrder 2 * L * meshSize N :=
      by simpa using hv1
    exact hv1'
  have := pow_le_pow_left₀ (norm_nonneg _) h' 2
  nlinarith


set_option maxHeartbeats 1000000 in
/-- **Thesis Thm 5.5 on the cube with the elements of Table 5.1, with rate**: under the regularity
hypothesis (`curl H̊(curl) = curl S⁰H̊¹(Q;ℝ³)` with constant `C_R`), for every `N` and every
solution `(σ, φ, u, λ)` of the continuous system (5.3) whose components and `S¹u` are `C²` up to
`∂Q` with vanishing tangential traces (`IsCsFormTr 0`, bound `L`), with `‖λ‖, ‖S¹u‖ ≤ L` and
`|⟪S¹u, d w⟫| ≤ L ‖w‖`
(`S¹u ∈ D(d¹*)`), every discrete solution of the method (5.6), i.e. (5.7) with `S_h = πS` in place
of the canonical `Π¹_h S⁰`, `Π²_h S¹`, satisfies
`‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N)²` with `K` independent of `N`. -/
theorem cubeFEM_rate_tr_of_bounds {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
      {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
        ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
      (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
        ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
      bggSegment.d0 σ = bggSegment.S0 φ →
      IsCsFormTr 0 0 L (σ : W0) → (∀ a, IsCsFormTr 0 0 L (φ a : W0)) →
      (∀ a, IsCsFormTr 0 1 L (u a : W1)) → IsCsFormTr 0 2 L (bggSegment.S1 u) →
      ‖lam‖ ≤ L → ‖bggSegment.S1 u‖ ≤ L →
      (∀ w : U1, |⟪bggSegment.S1 u, bggSegment.d1 w⟫| ≤ L * ‖w‖) →
      ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
      σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
      uh ∈ (cubeFEM hT hB N).Vt1h →
      (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
        ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
          ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
      (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
        ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
        (cubeFEM hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2 := by
  have hK := cubeFEM_rate_of_err hT hB hCR0 hCR
  refine ⟨hK.choose, hK.choose_spec.1, ?_⟩
  intro N σ φ u lam F L hL0 c1 c2 c3 hσ hφ hu hSu
  exact hK.choose_spec.2 N hL0 c1 c2 c3 (cubeFEM_err_P0_tr hT hB N hL0 σ hσ)
    (cubeFEM_err_Pt0_tr hT hB N hL0 φ hφ) (cubeFEM_err_gnSq_tr hT hB N hL0 u hu)
    (cubeFEM_err_S1_tr hT hB N hL0 u hSu)

set_option maxHeartbeats 1000000 in
/-- **Thesis Thm 5.5 on the cube with the elements of Table 5.1, with rate, for `C²` solutions
with vanishing tangential traces** (thesis' boundary conditions, no flatness): the form of
`cubeFEM_rate_tr_of_bounds` where the hypotheses on `σ, φ, u` are `C²` regularity up to
`∂Q`: if `σ`, `φ` and `u` are `C²` forms whose tangential components vanish on `∂Q`, with
values and first derivatives bounded by `L` on `cl Q` (`IsCsFormTr 0`), and the multiplier
`λ ∈ L²` (no boundary condition, no smoothness) has
`‖λ‖ ≤ L`, then `‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N)²`; the class of `S¹u`
(`exists_isCsFormTr_segS1`), its `L²` bound
and the regularity `S¹u ∈ D(d¹*)` are derived (`IsCsFormTr.norm_le`,
`IsCsFormTr.abs_inner_D1_le`). -/
theorem cubeFEM_rate_tr {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
      {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
        ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
      (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
        ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
      bggSegment.d0 σ = bggSegment.S0 φ →
      IsCsFormTr 0 0 L (σ : W0) → (∀ a, IsCsFormTr 0 0 L (φ a : W0)) →
      (∀ a, IsCsFormTr 0 1 L (u a : W1)) → ‖lam‖ ≤ L →
      ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
      σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
      uh ∈ (cubeFEM hT hB N).Vt1h →
      (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
        ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
          ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
      (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
        ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
        (cubeFEM hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2 := by
  have hex := cubeFEM_rate_tr_of_bounds hT hB hCR0 hCR
  obtain ⟨K, hK⟩ := hex
  have hK0 := hK.1
  have hrate := hK.2
  obtain ⟨cS, hcS1, hcS⟩ := exists_isCsFormTr_segS1
  have hcS0 : 0 ≤ cS := by linarith
  have hc1 : (0 : ℝ) ≤ Fintype.card (formIdx 3 1) := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ Fintype.card (formIdx 3 2) := Nat.cast_nonneg _
  refine ⟨K * (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * cS,
    mul_nonneg (by positivity) hcS0,
    fun N σ φ u lam F L hL0 c1 c2 c3 hσ hφ hu hlam σh φh uh lh hσh hφh huh h1 h2 h3 => ?_⟩
  have hSu : IsCsFormTr 0 2 (cS * L) (bggSegment.S1 u) := hcS u hL0 hu
  have hL' : L ≤ cS * L := le_mul_of_one_le_left hL0 hcS1
  have hL'0 : 0 ≤ cS * L := mul_nonneg hcS0 hL0
  have hc1' : (1 : ℝ) ≤ 1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2) := by
    linarith
  have hcL : cS * L ≤ (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) *
      (cS * L) := le_mul_of_one_le_left hL'0 hc1'
  have hcL0 : 0 ≤ (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) *
      (cS * L) := le_trans hL'0 hcL
  have hLc := hL'.trans hcL
  have hn : (Fintype.card (formIdx 3 2) : ℝ) * (cS * L) ≤
      (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * (cS * L) :=
    mul_le_mul_of_nonneg_right (by linarith) hL'0
  have hd : (Fintype.card (formIdx 3 1) : ℝ) * (3 * (cS * L)) ≤
      (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * (cS * L) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) hL'0
  have hb := hrate N hcL0 c1 c2 c3 (hσ.mono hLc) (fun a => (hφ a).mono hLc)
    (fun a => (hu a).mono hLc) (hSu.mono hcL) (hlam.trans hLc) ((hSu.norm_le hL'0).trans hn)
    (fun w => (hSu.abs_inner_D1_le hL'0 w).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)))
    hσh hφh huh h1 h2 h3
  refine hb.trans (le_of_eq ?_)
  ring

/-- **The rate for the solution of Prop 5.2** (`bggHilb.IsSaddle`, `bgg_existsUnique_isSaddle`):
`cubeFEM_rate_tr` applied to the graph-space solution `(x, jW λ)` of (5.3) with right-hand side `f`
and multiplier in `W¹` (`λ ∈ L²Λ¹(Q)`), through `isSaddle_jW_domain_eqs`; the discrete datum is
`F v = ⟪f, v⟫`. -/
theorem cubeFEM_rate_isSaddle_tr {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {f : Wv W1} {x : Feec.BGG.Xsp V0 Vt0 Vt1} {lam : W1} {L : ℝ},
      0 ≤ L → bggHilb.IsSaddle f x (bggHilb.jW lam) →
      IsCsFormTr 0 0 L ((graphDomₗ (Feec.BGG.pσ V0 Vt0 Vt1 x) : U0) : W0) →
      (∀ a, IsCsFormTr 0 0 L ((rp (Feec.BGG.pφ V0 Vt0 Vt1 x) a : U0) : W0)) →
      (∀ a, IsCsFormTr 0 1 L ((rp1 (Feec.BGG.pu V0 Vt0 Vt1 x) a : U1) : W1)) → ‖lam‖ ≤ L →
      ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
      σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
      uh ∈ (cubeFEM hT hB N).Vt1h →
      (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
        ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
          ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
      (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
        ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = ((innerSL ℝ f).toLinearMap ∘ₗ incl1) v) →
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (graphDomₗ (Feec.BGG.pσ V0 Vt0 Vt1 x) - σh) +
        Feec.BGG.graphSq bggSegment.dt0 (rp (Feec.BGG.pφ V0 Vt0 Vt1 x) - φh) +
        (cubeFEM hT hB N).gnSq (rp1 (Feec.BGG.pu V0 Vt0 Vt1 x) - uh) ≤
          (K * L * meshSize N) ^ 2 := by
  have hex := cubeFEM_rate_tr hT hB hCR0 hCR
  obtain ⟨K, hK0, hK⟩ := hex
  refine ⟨K, hK0, fun N f x lam L hL0 hs hσ hφ hu hlam σh φh uh lh hσh hφh huh h1 h2 h3 => ?_⟩
  have e := isSaddle_jW_domain_eqs hs
  exact hK N hL0 e.1 e.2.1 e.2.2 hσ hφ hu hlam hσh hφh huh h1 h2 h3


/-- `L²` error of `π²` on a `C²` `2`-form with vanishing tangential traces. -/
theorem cubeFEM_err_P2_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (z : W2) (hz : IsCsFormTr 0 2 L z) :
    ‖(cubeFEM hT hB N).P2 z - z‖ ^ 2 ≤
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  obtain ⟨v, hv, hv1, -⟩ := hz.exists_mem_polyMin_le (S := PolySeq.lowestOrder)
    ((polyOrder_zero _).polyOrderAt 2) hL0 N
  have h' : ‖(cubeFEM hT hB N).P2 z - z‖ ≤
      (1 + 2 * C) * (polyInterpBound 3 PolySeq.lowestOrder 2 * L * meshSize N) := by
    rw [norm_sub_rev]
    change ‖z - (hT.proj N).π 2 z‖ ≤ _
    refine (norm_sub_π_le_of_mem (hT.proj N) (hT.norm_proj_le N 2) hv).trans
      (mul_le_mul_of_nonneg_left ?_ hA)
    simpa using hv1
  have := pow_le_pow_left₀ (norm_nonneg _) h' 2
  nlinarith

/-- `L²` error of the componentwise `π̃²` on `C²` `2`-forms with vanishing tangential traces. -/
theorem cubeFEM_err_Pt2_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (ρ : Wv W2)
    (hρ : ∀ a, IsCsFormTr 0 2 L (ρ a)) :
    ‖(cubeFEM hT hB N).Pt2 ρ - ρ‖ ^ 2 ≤
      3 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 * (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  have hc : ∀ a, ‖((cubeFEM hT hB N).Pt2 ρ - ρ) a‖ ^ 2 ≤
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 * (L * meshSize N) ^ 2 := by
    intro a
    obtain ⟨v, hv, hv1, -⟩ := (hρ a).exists_mem_polyMin_le (S := PolySeq.lagrangeP2)
      ((polyOrder_zero _).polyOrderAt 2) hL0 N
    have h' : ‖((cubeFEM hT hB N).Pt2 ρ - ρ) a‖ ≤
        (1 + 2 * C) * (polyInterpBound 3 PolySeq.lagrangeP2 2 * L * meshSize N) := by
      rw [PiLp.sub_apply, norm_sub_rev]
      change ‖ρ a - (hB.proj N).π 2 (ρ a)‖ ≤ _
      refine (norm_sub_π_le_of_mem (hB.proj N) (hB.norm_proj_le N 2) hv).trans
        (mul_le_mul_of_nonneg_left ?_ hA)
      simpa using hv1
    have := pow_le_pow_left₀ (norm_nonneg _) h' 2
    nlinarith
  rw [norm_sq_wv]
  calc ∑ a, ‖((cubeFEM hT hB N).Pt2 ρ - ρ) a‖ ^ 2 ≤
      ∑ _a : Fin 3, ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 *
        (L * meshSize N) ^ 2 := Finset.sum_le_sum fun a _ => hc a
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Regularity of an exact state** `(σ, φ, u, M, ρ)` for the `O(h)` rate: all components are
`C²` forms (restrictions to `Q` of `C²` fields on `ℝ³`) whose tangential components vanish on
`∂Q` (no condition on the normal components), with values and first derivatives bounded by `L`
on `cl Q` (`IsCsFormTr 0`). The class of `S¹u` follows (`exists_isCsFormTr_segS1`). The
condition on `M`, `ρ` is needed for the rate: `Mₕ`, `ρₕ` have vanishing boundary DOFs (see the
module docstring). -/
def IsSmoothStateTr (L : ℝ) (σ : U0) (φ : Wv U0) (u : Wv U1) (M : W2) (ρ : Wv W2) : Prop :=
  IsCsFormTr 0 0 L (σ : W0) ∧ (∀ a, IsCsFormTr 0 0 L (φ a : W0)) ∧
    (∀ a, IsCsFormTr 0 1 L (u a : W1)) ∧ IsCsFormTr 0 2 L M ∧ ∀ a, IsCsFormTr 0 2 L (ρ a)

theorem IsSmoothStateTr.isCsFormTr_M {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2}
    {ρ : Wv W2} (h : IsSmoothStateTr L σ φ u M ρ) : IsCsFormTr 0 2 L M := h.2.2.2.1

theorem IsSmoothStateTr.mono {L L' : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2}
    {ρ : Wv W2} (h : IsSmoothStateTr L σ φ u M ρ) (hLL' : L ≤ L') :
    IsSmoothStateTr L' σ φ u M ρ :=
  ⟨h.1.mono hLL', fun a => (h.2.1 a).mono hLL', fun a => (h.2.2.1 a).mono hLL',
    h.2.2.2.1.mono hLL', fun a => (h.2.2.2.2 a).mono hLL'⟩

/-- A state of `IsSmoothStateTr` together with the class of `S¹u` at the same bound: the form
used by the Strang bounds (`cubeFEM_strangData_le_tr`); obtained from `IsSmoothStateTr` with a
universal factor on the bound (`exists_isSmoothStateTrS1`). -/
def IsSmoothStateTrS1 (L : ℝ) (σ : U0) (φ : Wv U0) (u : Wv U1) (M : W2) (ρ : Wv W2) : Prop :=
  IsSmoothStateTr L σ φ u M ρ ∧ IsCsFormTr 0 2 L (bggSegment.S1 u)

/-- **The class of `S¹u` is derived**: `IsSmoothStateTr L` gives `IsSmoothStateTrS1 (c L)` for a
universal `c ≥ 1` (`exists_isCsFormTr_segS1`). -/
theorem exists_isSmoothStateTrS1 : ∃ c : ℝ, 1 ≤ c ∧ ∀ {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1}
    {M : W2} {ρ : Wv W2}, 0 ≤ L → IsSmoothStateTr L σ φ u M ρ →
      IsSmoothStateTrS1 (c * L) σ φ u M ρ := by
  obtain ⟨c, hc1, hc⟩ := exists_isCsFormTr_segS1
  exact ⟨c, hc1, fun hL0 h => ⟨h.mono (le_mul_of_one_le_left hL0 hc1), hc _ hL0 h.2.2.1⟩⟩

set_option maxHeartbeats 2000000 in
/-- **The data of the Strang bound of (6.4) for a smooth exact state**: the interpolation part
is `≤ interpConst C · (L h_N)²`, for every `N`. -/
theorem cubeFEM_strangData_le_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) {σ : U0} {φ : Wv U0} {u : Wv U1}
    {M : W2} {ρ : Wv W2} (hs : IsSmoothStateTrS1 L σ φ u M ρ) (K0 K1 : ℝ) :
    (cubeFEM hT hB N).strangData σ φ u M ρ K0 K1 ≤
      interpConst C * (L * meshSize N) ^ 2 + K0 ^ 2 + K1 ^ 2 := by
  obtain ⟨⟨hσ, hφ, hu, hM, hρ⟩, hSu⟩ := hs
  have h1 := cubeFEM_err_P0_tr hT hB N hL0 σ hσ
  have h2 := cubeFEM_err_Pt0_tr hT hB N hL0 φ hφ
  have h3 := cubeFEM_err_gnSq_tr hT hB N hL0 u hu
  have h4 := cubeFEM_err_P2_tr hT hB N hL0 M hM
  have h5 := cubeFEM_err_Pt2_tr hT hB N hL0 ρ hρ
  have h6 := cubeFEM_err_S1_tr hT hB N hL0 u hSu
  have g1 : ‖(cubeFEM hT hB N).P0 σ - σ‖ ^ 2 ≤
      Feec.BGG.graphSq bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ) := by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ)‖]
  have g2 : ‖bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)‖ ^ 2 ≤
      Feec.BGG.graphSq bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ) := by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖(cubeFEM hT hB N).Pt0 φ - φ‖]
  have e1 : (cubeFEM hT hB N).strangData σ φ u M ρ K0 K1 =
      ‖(cubeFEM hT hB N).P0 σ - σ‖ ^ 2 + ‖bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)‖ ^ 2 +
        (cubeFEM hT hB N).gnSq ((cubeFEM hT hB N).Pt1 u - u) +
        ‖(cubeFEM hT hB N).P2 M - M‖ ^ 2 + ‖(cubeFEM hT hB N).Pt2 ρ - ρ‖ ^ 2 + K0 ^ 2 + K1 ^ 2 +
        ‖bggSegment.S1 u - (cubeFEM hT hB N).S1h u‖ ^ 2 := rfl
  have e2 : interpConst C * (L * meshSize N) ^ 2 =
      2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 0) ^ 2 * (L * meshSize N) ^ 2 +
      3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 0) ^ 2) *
        (L * meshSize N) ^ 2 +
      (1 + 8 * C ^ 2) * (3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2)) *
        (L * meshSize N) ^ 2 +
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * (L * meshSize N) ^ 2 +
      3 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 * (L * meshSize N) ^ 2 +
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * (L * meshSize N) ^ 2 := by
    unfold interpConst; ring
  rw [e1, e2]
  linarith

/-- `S¹u ∈ D(d¹*)`-type bounds of a `C²` `2`-form with vanishing tangential traces (sup bound and
Green's formula): `‖z‖ ≤ c L` and
`|⟪z, curl w⟫| ≤ c L ‖w‖` with `c = 1 + 3·#Λ¹ + #Λ²`. -/
theorem _root_.Feec.Models.Cube.FEM.IsCsFormTr.bounds_two {L : ℝ} (hL0 : 0 ≤ L) {z : W2}
    (hz : IsCsFormTr 0 2 L z) :
    ‖z‖ ≤ (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L ∧
      ∀ w : U1, |⟪z, bggSegment.d1 w⟫| ≤
        ((1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L) * ‖w‖ := by
  have hc1 : (0 : ℝ) ≤ Fintype.card (formIdx 3 1) := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ Fintype.card (formIdx 3 2) := Nat.cast_nonneg _
  refine ⟨(hz.norm_le hL0).trans (by nlinarith), fun w => (hz.abs_inner_D1_le hL0 w).trans
    (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _))⟩


set_option maxHeartbeats 4000000 in
/-- **The `O(h)` rate of the elliptic projection (6.4) on the cube** (the cube form of
`Feec.BGG.Discrete.strang_rate_of_regularPotential`, whose hypothesis `M ∈ D(d¹*)` with
representer in `V¹` is replaced by the functional bound of Green's formula), under the regularity
hypothesis (constant `C_R`): there is `K`, independent of `N` and of the state, such that for every
exact state `(σ, φ, u, M, ρ)` with `dσ = S₀φ` in the class `IsSmoothStateTr L` (`C²` up to `∂Q`,
vanishing tangential traces) and every multiplier functional with `|ℓ μ| ≤ L ‖μ‖`, every solution
`x`
of (6.4) for the discretization of Table 6.1 satisfies
`(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2} ≤ K L h_N`
(the Strang bound `strang_of_isEllipticProjection` with the consistency bounds of
`consistency_S0_of_approx`, `weakConsistency_of_regularPotential_of_bound` and the interpolation
errors `cubeFEM_strangData_le_tr`). See [QuennevilleBelair2015], §6.2, (6.4), Prop 5.9. -/
theorem cubeFEM_ellipticProjection_rate_trS1 {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
      (ℓ : U1 →ₗ[ℝ] ℝ) {L : ℝ}, 0 ≤ L → bggSegment.d0 σ = bggSegment.S0 φ →
      (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → IsSmoothStateTrS1 L σ φ u M ρ →
      ∀ {x : (((cubeFEM hT hB N).V0h × (cubeFEM hT hB N).Vt1h × (cubeFEM hT hB N).W2h ×
          (cubeFEM hT hB N).Wt2h) × (cubeFEM hT hB N).Vt0h) × (cubeFEM hT hB N).V1h},
      Feec.BGG.IsEllipticProjection (cubeFEM hT hB N).toSegmentH
        ((cubeFEM hT hB N).ellipticDataH σ φ u M ρ ℓ) 0 x →
      √(‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 +
        ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤ K * L * meshSize N := by
  have hh0 := cubeFEM_happ0 hT hB
  obtain ⟨C0, hh1⟩ := hh0
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hC := hT.two_mul_nonneg
  have hreg := regConst_nonneg hT
  have Capp_ex : ∃ x : ℝ, x = C0 + regConst C := ⟨_, rfl⟩
  obtain ⟨Capp, hCapp_def⟩ := Capp_ex
  have hCapp0 : 0 ≤ Capp := by rw [hCapp_def]; linarith
  have Cp_ex : ∃ x : ℝ, x = (2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ := Cp_ex
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have wa_ex : ∃ x : ℝ, x = √(1 + Cp ^ 2) * (1 + 2 * C * (1 + 1 * CR)) := ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ := wa_ex
  have wb_ex : ∃ x : ℝ, x = (1 + (1 + 2 * C) * Real.sqrt 2) * CR := ⟨_, rfl⟩
  obtain ⟨wb, hwb⟩ := wb_ex
  have hwa0 : 0 ≤ wa := by rw [hwa]; positivity
  have hwb0 : 0 ≤ wb := by rw [hwb]; positivity
  have cM_ex : ∃ x : ℝ,
      x = 1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2) := ⟨_, rfl⟩
  obtain ⟨cM, hcM⟩ := cM_ex
  have hcM0 : 0 ≤ cM := by rw [hcM]; positivity
  have Kd_ex : ∃ x : ℝ,
      x = interpConst C + Capp ^ 2 + (Capp * ((wa + wb) * cM)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ := Kd_ex
  have hKd0 : 0 ≤ Kd := by rw [hKd]; have := interpConst_nonneg C; positivity
  have Ks_ex : ∃ x : ℝ, x = √(2 * (Feec.BGG.Discrete.strangConst Cp + 1)) := ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ := Ks_ex
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  refine ⟨Ks * √Kd, by positivity, fun N σ φ u M ρ ℓ L hL0 c3 hℓ hs x hx => ?_⟩
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have H : Feec.BGG.Stability bggSegment Cp CR (Real.sqrt 2) := by
    rw [hCp]; exact bggStability_of hCR0 hCR
  have Bd := cubeFEM_bounded hT hB N
  have h54 := cubeFEM_compatible hT hB N
  have happ : ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      ‖bggSegment.S0 ψ - (cubeFEM hT hB N).S0h ψ‖ ^ 2 ≤
        (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq bggSegment.dt0 ψ := fun ψ hψ => by
    refine (hhapp N ψ hψ).trans (mul_le_mul_of_nonneg_right ?_ (Feec.BGG.graphSq_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (by rw [hCapp_def]; linarith) hh) 2
  have Rg := cubeFEMReg hT hB N hCR0 hCR (by rw [hCapp_def]; linarith : regConst C ≤ Capp)
  have hK0 : ∀ ℓ : U1 →ₗ[ℝ] ℝ, (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      |ℓ ((bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ)| ≤
        (L * Capp * meshSize N) * √(Feec.BGG.graphSq bggSegment.dt0 ψ) := fun ℓ hℓ =>
    Feec.BGG.Discrete.consistency_S0_of_approx hh hCapp0 hL0 ℓ hℓ happ
  have hK1 : ∀ z : W2, IsCsFormTr 0 2 L z → ∀ v ∈ (cubeFEM hT hB N).Vt1h,
      |⟪z, (bggSegment.S1 - (cubeFEM hT hB N).S1h) v⟫| ≤
        (Capp * meshSize N * ((wa + wb) * (cM * L))) * √((cubeFEM hT hB N).gnSq v) := by
    intro z hz v hv
    obtain ⟨hzn, hzd⟩ := hz.bounds_two hL0
    rw [← hcM] at hzn hzd
    have hw := Feec.BGG.Discrete.weakConsistency_of_regularPotential_of_bound H Bd hh hCapp0 Rg
      happ (by positivity) hzd v hv
    have hwc : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
        (cM * L) ≤ (wa + wb) * (cM * L) := by
      have e : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
          (cM * L) = (cM * L) * wa + ‖z‖ * wb := by
        rw [hwa, hwb]; unfold Feec.BGG.Discrete.weakConsistencyConst; ring
      rw [e]; nlinarith
    have hwc0 : 0 ≤ Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
        (cM * L) := Feec.BGG.Discrete.weakConsistencyConst_nonneg hCp0 (Real.sqrt_nonneg _) hC
          zero_le_one hCR0 (norm_nonneg _) (by positivity)
    refine hw.trans ?_
    have hg := Feec.BGG.Discrete.sqrt_graphSq_le_sqrt_gnSq (Q := cubeFEM hT hB N) v
    have hm : 0 ≤ Capp * meshSize N := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwc hm)
      (Real.sqrt_nonneg (Feec.BGG.graphSq bggSegment.dt1 v))
    have h2 := mul_le_mul_of_nonneg_left hg
      (by positivity : 0 ≤ Capp * meshSize N * ((wa + wb) * (cM * L)))
    exact h1.trans h2
  have hdata : (cubeFEM hT hB N).strangData σ φ u M ρ (L * Capp * meshSize N)
        (Capp * meshSize N * ((wa + wb) * (cM * L))) ≤ (√Kd * L * meshSize N) ^ 2 := by
    refine (cubeFEM_strangData_le_tr hT hB N hL0 hs _ _).trans (le_of_eq ?_)
    rw [show (√Kd * L * meshSize N) ^ 2 = √Kd ^ 2 * (L * meshSize N) ^ 2 by ring,
      Real.sq_sqrt hKd0, hKd]
    ring
  have hS := (Feec.BGG.Discrete.strang_of_isEllipticProjection H h54 c3 ℓ (hK0 ℓ hℓ)
    (hK1 M hs.1.isCsFormTr_M) hx).2
  have hC2 : 0 ≤ 2 * (Feec.BGG.Discrete.strangConst Cp + 1) := by
    unfold Feec.BGG.Discrete.strangConst; positivity
  calc √(‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 +
        ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤
        √(2 * (Feec.BGG.Discrete.strangConst Cp + 1) * (√Kd * L * meshSize N) ^ 2) :=
        Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_left hdata hC2))
    _ = Ks * √Kd * L * meshSize N := by
        rw [Real.sqrt_mul hC2, Real.sqrt_sq (by positivity), ← hKs]; ring

set_option maxHeartbeats 1000000 in
/-- **The `O(h)` rate of the elliptic projection (6.4) on the cube** (the cube form of
`Feec.BGG.Discrete.strang_rate_of_regularPotential`, under the regularity hypothesis `C_R`): for
every exact state in `IsSmoothStateTr L` (`σ, φ, u, M, ρ` `C²` with vanishing tangential traces;
the class of `S¹u` is derived, `exists_isSmoothStateTrS1`) with `dσ = S₀φ` and every multiplier
functional with `|ℓ μ| ≤ L ‖μ‖`, every solution of (6.4) for Table 6.1 satisfies
`(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2} ≤ K L h_N`, `K` independent of `N` and of
the state (`cubeFEM_ellipticProjection_rate_trS1`). See [QuennevilleBelair2015], §6.2, (6.4). -/
theorem cubeFEM_ellipticProjection_rate_tr {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
      (ℓ : U1 →ₗ[ℝ] ℝ) {L : ℝ}, 0 ≤ L → bggSegment.d0 σ = bggSegment.S0 φ →
      (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → IsSmoothStateTr L σ φ u M ρ →
      ∀ {x : (((cubeFEM hT hB N).V0h × (cubeFEM hT hB N).Vt1h × (cubeFEM hT hB N).W2h ×
          (cubeFEM hT hB N).Wt2h) × (cubeFEM hT hB N).Vt0h) × (cubeFEM hT hB N).V1h},
      Feec.BGG.IsEllipticProjection (cubeFEM hT hB N).toSegmentH
        ((cubeFEM hT hB N).ellipticDataH σ φ u M ρ ℓ) 0 x →
      √(‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 +
        ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤ K * L * meshSize N := by
  have hex := cubeFEM_ellipticProjection_rate_trS1 hT hB hCR0 hCR
  obtain ⟨K, hK⟩ := hex
  have hK0 := hK.1
  replace hK := hK.2
  obtain ⟨c, hc1, hc⟩ := exists_isSmoothStateTrS1
  refine ⟨K * c, mul_nonneg hK0 (by linarith), fun N σ φ u M ρ ℓ L hL0 c3 hℓ hs x hx => ?_⟩
  have hcL : L ≤ c * L := le_mul_of_one_le_left hL0 hc1
  refine (hK N ℓ (L := c * L) (mul_nonneg (by linarith) hL0) c3
    (fun μ => (hℓ μ).trans (mul_le_mul_of_nonneg_right hcL (norm_nonneg _))) (hc hL0 hs)
    hx).trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **`O(h)` convergence of the semi-discrete scheme (6.5) on the cube** (Table 6.1; new: the
thesis states no convergence result for (6.5)), under the regularity hypothesis (`C_R`). There is
`K`, independent of `N`, `T`, the data and the solution, such that for every `N`, every `T > 0`,
every `L²` source `f` continuous on `[0,T]` and every classical solution `s` of (6.2) (`ExactWave`)
whose states `(σ, φ, u, M, ρ)(t)` and time derivatives `(σ', φ', u', M', ρ')(t)` are `C²` forms
up to `∂Q` with vanishing tangential traces, values and first derivatives bounded by `L`
(`IsSmoothStateTr L`; no flatness), and whose
multiplier functional and its derivative are `L²`-bounded by `L` (`|ℓ(t) μ| ≤ L ‖μ‖`, i.e.
`λ(t) ∈ L²`, `‖λ(t)‖ ≤ L`): the scheme (6.5) with source `P_{Ṽₕ¹} f` (`cubeSource`) has a
solution starting
from the dynamic part of the elliptic projection (6.4) of the exact initial state (admissible by
the (C2) lemma `projected_compatible_u_L2`), and for `t ∈ [0,T]`
`(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2}(t) ≤ K L (1 + t) h_N`.
All hypotheses of `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate` are discharged:
`Stability` (`bggStability_of`), (5.4) (`cubeFEM_compatible`), `S₀,ₕ` onto
(`cubeWave_S0_surjective`), `K₀` from Prop 5.9(1) (`cubeFEM_happ0`,
`consistency_S0_of_approx`), `K₁` from the weak-consistency lemma with regular potentials
(`cubeFEMReg`, `weakConsistency_of_regularPotential_of_bound`), the interpolation errors from
the `H¹`/`C²` approximation of the smoothed projections (`cubeFEM_strangData_le_tr`).
See [QuennevilleBelair2015], §6.3, (6.5), Table 6.1, and §6.2, (6.4), Prop 6.2. -/
theorem cubeWave_rate_tr {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
      0 ≤ L →
      (∀ t ∈ Icc 0 T, IsSmoothStateTr L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
        IsSmoothStateTr L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
      (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
              (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N := by
  have hc := exists_isSmoothStateTrS1
  have hK := cubeWave_rate_of_bounds hT hB hCR0 hCR
  have hcS0 : 0 ≤ hc.choose := by linarith [hc.choose_spec.1]
  refine ⟨hK.choose * hc.choose, mul_nonneg hK.choose_spec.1 hcS0,
    fun N T hT0 f hf s L hL0 hsm hmult => ?_⟩
  have hL0' : 0 ≤ hc.choose * L := mul_nonneg hcS0 hL0
  have hLL : L ≤ hc.choose * L := le_mul_of_one_le_left hL0 hc.choose_spec.1
  have hs := fun t (ht : t ∈ Icc 0 T) =>
    And.intro (hc.choose_spec.2 hL0 (hsm t ht).1) (hc.choose_spec.2 hL0 (hsm t ht).2)
  have H := hK.choose_spec.2 N hT0 hf s hL0'
    (fun t ht K0 K1 => ⟨cubeFEM_strangData_le_tr hT hB N hL0' (hs t ht).1 K0 K1,
      cubeFEM_strangData_le_tr hT hB N hL0' (hs t ht).2 K0 K1⟩)
    (fun t ht => ⟨(hs t ht).1.1.isCsFormTr_M.bounds_two hL0',
      (hs t ht).2.1.isCsFormTr_M.bounds_two hL0'⟩)
    (fun t ht μ => ⟨(hmult t ht μ).1.trans (mul_le_mul_of_nonneg_right hLL (norm_nonneg _)),
      (hmult t ht μ).2.trans (mul_le_mul_of_nonneg_right hLL (norm_nonneg _))⟩)
  exact ⟨H.choose, H.choose_spec.1, fun t ht =>
    (H.choose_spec.2 t ht).trans (le_of_eq (by ring))⟩

end CubeFEM

/-! ### A smooth solution of (5.3) with nonzero normal component on `∂Q` -/

section TangentialManufactured

/-- A derivative along `eᵢ` of a function independent of `yᵢ` vanishes. -/
theorem fderiv_coordDir_eq_zero_of_indep {g : (Fin 3 → ℝ) → ℝ} (hg : Differentiable ℝ g)
    {i : Fin 3} (hind : ∀ (y : Fin 3 → ℝ) (t : ℝ), g (y + t • coordDir i) = g y)
    (y : Fin 3 → ℝ) : fderiv ℝ g y (coordDir i) = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => g (y + t • coordDir i)) (fderiv ℝ g y (coordDir i)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => y + t • (coordDir i : Fin 3 → ℝ)) (coordDir i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordDir i : Fin 3 → ℝ)).const_add y
    have h2 : HasFDerivAt g (fderiv ℝ g y) (y + (0 : ℝ) • (coordDir i : Fin 3 → ℝ)) := by
      simpa using (hg y).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => g (y + t • coordDir i)) 0 0 := by
    simp_rw [hind]; exact hasDerivAt_const _ _
  exact h1.unique h2

/-- The components of the witness `w = (sin 2πy₁ sin 2πy₂) dx₀`. -/
abbrev tangentialψ : formIdx 3 1 → (Fin 3 → ℝ) → ℝ := formComp (normalWitness (n := 3))

theorem contDiff_tangentialψ (r : formIdx 3 1) : ContDiff ℝ ∞ (tangentialψ r) :=
  contDiff_pi.1 contDiff_normalWitness r.1

/-- **`w` is divergence free**: `dᵗw = -∂₀ w₀ = 0` (`w₀` does not depend on `y₀`). -/
theorem formalAdj_tangentialψ : (extDerivOp ℝ 3 0).formalAdj.apply tangentialψ = 0 := by
  funext r y
  rw [formalAdj_extDerivOp_apply, extDAdj, Pi.zero_apply, Pi.zero_apply, neg_eq_zero]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j ∉ r.1 := Finset.mem_compl.1 hj
  rw [formExt_of_card tangentialψ (card_insert_of_formIdx r hj')]
  have hr : r.1 = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast r.2)
  have hins : insert j r.1 = {j} := by rw [hr]; rfl
  by_cases hj0 : j = 0
  · subst hj0
    have hd : Differentiable ℝ (tangentialψ ⟨insert 0 r.1, card_insert_of_formIdx r hj'⟩) :=
      (contDiff_tangentialψ _).differentiable (by simp)
    rw [fderiv_coordDir_eq_zero_of_indep hd (fun z t => ?_) y, mul_zero]
    simp only [tangentialψ, formComp, normalWitness, hins, ↓reduceIte]
    refine Finset.prod_congr rfl fun l hl => ?_
    have hl0 : l ≠ 0 := Finset.ne_of_mem_erase hl
    simp [coordDir, hl0]
  · have h0 : tangentialψ ⟨insert j r.1, card_insert_of_formIdx r hj'⟩ = fun _ => 0 := by
      funext z
      simp only [tangentialψ, formComp, normalWitness, hins]
      rw [ite_eq_right_iff]; intro h; exact absurd (Finset.singleton_inj.1 h) hj0
    rw [h0]; simp

/-- The class of `w` in `L²Λ¹(Q)`. -/
def tangentialX : W1 :=
  formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 1
    ⟨normalWitness, contDiff_normalWitness.continuous⟩

theorem exists_isCsFormTr_tangentialX : ∃ L, 0 ≤ L ∧ IsCsFormTr 0 1 L tangentialX :=
  isCsFormTr_normalWitness 0

/-- **`w ∈ H̊Λ¹(Q)`** with `d_min w = (dw)|_Q`. -/
theorem tangentialX_mem : ∃ h : tangentialX ∈ D1.domain, D1 ⟨_, h⟩ =
    formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 2
      ⟨FiniteElement.extDeriv normalWitness,
        continuous_extDeriv ((contDiff_normalWitness (n := 3)).of_le (by simp))⟩ := by
  obtain ⟨L, -, hL⟩ := exists_bound_iteratedFDeriv_le (n := 3) (m := 1)
    ((contDiff_normalWitness (n := 3)).of_le (by simp))
  obtain ⟨L', -, hL'⟩ := exists_bound_iteratedFDeriv_le (n := 3) (m := 0)
    (contDiff_extDeriv (m := 0) ((contDiff_normalWitness (n := 3)).of_le (by simp)))
  exact mem_minimal_of_isTangentialZero (L := max L L')
    ((contDiff_normalWitness (n := 3)).of_le (by simp)) isDeg_normalWitness
    isTangentialZero_normalWitness
    (fun y hy => by simpa using (hL 0 (Nat.zero_le _) y hy).trans (le_max_left _ _))
    (fun y hy => by
      simpa [norm_iteratedFDeriv_one] using (hL 1 le_rfl y hy).trans (le_max_left _ _))
    (fun y hy => by simpa using (hL' 0 le_rfl y hy).trans (le_max_right _ _))

/-- The witness as a point of `H̊Λ¹(Q)`. -/
def tangentialU0 : U1 := ⟨tangentialX, tangentialX_mem.1⟩

/-- **The manufactured `u`** with nonzero normal component on `∂Q`: first row
`(sin 2πy₁ sin 2πy₂) dx₀`, other rows zero. -/
def tangentialU : Wv U1 := WithLp.toLp 2 (Pi.single 0 tangentialU0)

theorem tangentialU_apply_of_ne {a : Fin 3} (ha : a ≠ 0) : tangentialU a = 0 := by
  change (Pi.single (0 : Fin 3) tangentialU0 : Fin 3 → U1) a = 0
  exact Pi.single_eq_of_ne ha _

theorem tangentialU_apply_zero : tangentialU 0 = tangentialU0 := by
  change (Pi.single (0 : Fin 3) tangentialU0 : Fin 3 → U1) 0 = _
  exact Pi.single_eq_same _ _

/-- `⟪w, d ψ⟫ = 0` for `ψ ∈ H̊Λ⁰(Q)` (`dᵗw = 0`, Green's formula on `D(d_min)`). -/
theorem inner_tangentialX_D0 (x : U0) : ⟪tangentialX, D0 x⟫ = 0 := by
  have hψs : ∀ r, ContDiff ℝ 1 (tangentialψ r) := fun r =>
    (contDiff_tangentialψ r).of_le (by simp)
  have hψ : ∀ r, MemLp (tangentialψ r) 2 (volume.restrict (cubeDomain 3)) := fun r =>
    memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
      (hψs r).continuous
  have hAψ : ∀ r, MemLp ((extDerivOp ℝ 3 0).formalAdj.apply tangentialψ r) 2
      (volume.restrict (cubeDomain 3)) := fun r => by
    rw [formalAdj_tangentialψ]; exact MemLp.zero
  have key := (extDerivOp ℝ 3 0).minimal_green (isOpen_cubeDomain 3) (extDerivOp_isOrderLE 0) x
    hψs hψ hAψ
  have h0 : toL2F hAψ = 0 := by
    refine PiLp.ext fun r => ?_
    rw [PiLp.zero_apply]
    refine Lp.ext ?_
    filter_upwards [(hAψ r).coeFn_toLp, Lp.coeFn_zero ℝ 2 (volume.restrict (cubeDomain 3))]
      with y h1 h2
    change ((hAψ r).toLp _ : L2 ℝ (cubeDomain 3)) y = _
    rw [h1, h2, formalAdj_tangentialψ]
    rfl
  change ⟪toL2F hψ, D0 x⟫ = 0
  rw [real_inner_comm, key, h0, inner_zero_right]

theorem inner_tangentialU_dt0 (ψ : Wv U0) : ⟪tangentialU, bggSegment.dt0 ψ⟫ = 0 := by
  rw [inner_Vt, Fin.sum_univ_three, tangentialU_apply_of_ne (by decide : (1 : Fin 3) ≠ 0),
    tangentialU_apply_of_ne (by decide : (2 : Fin 3) ≠ 0), inner_zero_left, inner_zero_left,
    add_zero, add_zero, tangentialU_apply_zero]
  exact inner_tangentialX_D0 (ψ 0)

/-- **`S¹u = 0`** (`S¹u = Σₐ dxₐ ∧ uₐ = dx₀ ∧ w₀ dx₀ = 0`). -/
theorem segS1_tangentialU : bggSegment.S1 tangentialU = 0 := by
  change wsL2 (Ω := cubeDomain 3) 1 (incl1 tangentialU) = 0
  refine PiLp.ext fun t => ?_
  rw [wsL2_apply, PiLp.zero_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [wsCoeff_eq]
  split_ifs with h
  · by_cases ha : p.1 = 0
    · have hp : (incl1 tangentialU) p.1 p.2 = 0 := by
        change (((tangentialU p.1 : U1) : W1) p.2) = 0
        rw [ha, tangentialU_apply_zero]
        refine formL2_apply_eq_zero fun y => ?_
        change normalWitness y p.2.1 = 0
        simp only [normalWitness]
        rw [ite_eq_right_iff]
        intro h'
        exfalso
        have : (0 : Fin 3) ∈ t.1.erase p.1 := by rw [h.2, h']; exact Finset.mem_singleton_self _
        rw [ha] at this
        simp at this
      rw [hp, smul_zero]
    · have hp : (incl1 tangentialU) p.1 = 0 := by
        change ((tangentialU p.1 : U1) : W1) = 0
        rw [tangentialU_apply_of_ne ha]; rfl
      rw [hp, PiLp.zero_apply, smul_zero]
  · rw [zero_smul]

/-- The datum of the solution, `F v = ⟪S¹u, S¹v⟫ + ⟪d u, d v⟫`. -/
def tangentialDatum : Wv U1 →ₗ[ℝ] ℝ :=
  (innerₛₗ ℝ (bggSegment.S1 tangentialU)) ∘ₗ bggSegment.S1 +
    (innerₛₗ ℝ (bggSegment.dt1 tangentialU)) ∘ₗ bggSegment.dt1

/-- The zero field is in the flat class (with every bound `L ≥ 0`). -/
theorem isCsFormMin_zero_field {n : ℕ} (s k : ℕ) {L : ℝ} (hL0 : 0 ≤ L) :
    IsCsFormMin s (k : ℤ) L (0 : L2F ℝ (cubeDomain n) (formIdx n k)) := by
  have e : FiniteElement.extDeriv (0 : FormField n) = 0 := extDeriv_const (0 : Finset (Fin n) → ℝ)
  refine Or.inr ⟨k, rfl, 0, contDiff_const, fun y t _ => rfl, fun y _ => rfl, fun y _ => ?_,
    fun y _ => ?_, (map_zero _).symm⟩
  · simpa using hL0
  · rw [e]; simpa using hL0

/-- **The manufactured `u` is not flat**: its first row has a nonzero normal component at the
boundary point `(0, ⅛, ⅛)` (`normalWitness_ne_zero`) and is in no class `IsCsFormMin`. -/
theorem not_isCsFormMin_tangentialU0 (s : ℕ) (L : ℝ) :
    ¬ IsCsFormMin s 1 L ((tangentialU 0 : U1) : W1) := by
  rw [tangentialU_apply_zero]
  exact not_isCsFormMin_normalWitness s L

theorem tangentialU_ne_zero : tangentialU ≠ 0 := by
  intro h
  have h0 : tangentialX = 0 := by
    have := congrArg (fun z : Wv U1 => ((z 0 : U1) : W1)) h
    simpa [tangentialU_apply_zero, tangentialU0] using this
  exact not_isCsFormMin_normalWitness (n := 3) 0 0
    (by change IsCsFormMin 0 1 0 tangentialX; rw [h0]; exact isCsFormMin_zero_field 0 1 le_rfl)

/-- **A smooth solution of (5.3) that is not flat at `∂Q`** (non-vacuity of `cubeFEM_rate_tr`
beyond the flat class): `σ = 0`, `φ = 0`, `λ = 0`, `u = tangentialU ≠ 0` (first row
`(sin 2πy₁ sin 2πy₂) dx₀`, divergence free, `S¹u = 0`, normal component nonzero on `{y₀ = 0}`),
datum `F = tangentialDatum`: the equations hold and `u` is `IsCsFormTr 0`. -/
theorem tangentialManufactured_solution :
    (∀ τ ψ, ⟪(0 : U0), τ⟫ - ⟪tangentialU, bggSegment.dt0 ψ⟫ -
      ⟪(0 : W1), ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) ∧
    (∀ v, ⟪bggSegment.dt0 (0 : Wv U0), v⟫ + ⟪bggSegment.S1 tangentialU, bggSegment.S1 v⟫ +
      ⟪bggSegment.dt1 tangentialU, bggSegment.dt1 v⟫ = tangentialDatum v) ∧
    bggSegment.d0 (0 : U0) = bggSegment.S0 (0 : Wv U0) ∧
    ∃ L, 0 ≤ L ∧ IsCsFormTr 0 0 L ((0 : U0) : W0) ∧
      (∀ a, IsCsFormTr 0 0 L (((0 : Wv U0) a : U0) : W0)) ∧
      (∀ a, IsCsFormTr 0 1 L ((tangentialU a : U1) : W1)) ∧ ‖(0 : W1)‖ ≤ L := by
  refine ⟨fun τ ψ => ?_, fun v => ?_, by rw [map_zero, map_zero], ?_⟩
  · rw [inner_tangentialU_dt0, inner_zero_left, inner_zero_left, sub_zero, sub_zero]
  · have hz : bggSegment.dt0 (0 : Wv U0) = 0 := map_zero _
    rw [hz, inner_zero_left, zero_add]
    rfl
  obtain ⟨L, hL0, hL⟩ := exists_isCsFormTr_tangentialX
  refine ⟨L, hL0, isCsFormTr_zero 0 0 hL0, fun a => isCsFormTr_zero 0 0 hL0, fun a => ?_,
    by simpa using hL0⟩
  by_cases ha : a = 0
  · subst ha; rw [tangentialU_apply_zero]; exact hL
  · rw [tangentialU_apply_of_ne ha]; exact isCsFormTr_zero 0 1 hL0

/-- **The combined `u` is not flat**: `(coupledu + tangentialU) 0 − coupledu 0 = tangentialU 0`
and the flat class is closed under differences (`IsCsFormMin.sub`). -/
theorem not_isCsFormMin_coupledu_add_tangentialU (L : ℝ) :
    ¬ IsCsFormMin 0 1 L ((((coupledu + tangentialU : Wv U1)) 0 : U1) : W1) := by
  intro h
  obtain ⟨Lc, -, -, -, -, -, -, -, -, -, -, hu, -⟩ := exists_coupled_manufactured_solution
  have h' := h.sub (hu 0)
  have e : ((((coupledu + tangentialU : Wv U1)) 0 : U1) : W1) - ((coupledu 0 : U1) : W1) =
      ((tangentialU 0 : U1) : W1) := by
    rw [PiLp.add_apply, Submodule.coe_add, add_sub_cancel_left]
  rw [e] at h'
  exact not_isCsFormMin_tangentialU0 0 _ h'

set_option maxHeartbeats 2000000 in
/-- **A smooth solution of (5.3) with `σ, φ, λ ≠ 0` that is not flat at `∂Q`** (non-vacuity of
`cubeFEM_rate_tr` with every unknown nonzero): the sum of the flat coupled solution
`exists_coupled_manufactured_solution` (`σ = dᵗd g`, `φ = ∇σ`, `uₐ = −g dxₐ`, `λ = d g`) and of
`tangentialManufactured_solution` (`σ = φ = λ = 0`, `u = tangentialU`), with datum
`coupledDatum + tangentialDatum`; `u = coupledu + tangentialU` has a nonzero normal component on
`∂Q`. (`S¹u = 0` for both summands, so this witness does not exercise `S¹u ≠ 0`.) -/
theorem combinedManufactured_solution :
    coupledσ ≠ 0 ∧ coupledφ ≠ 0 ∧ coupledMult ≠ 0 ∧
    (∀ L, ¬ IsCsFormMin 0 1 L ((((coupledu + tangentialU : Wv U1)) 0 : U1) : W1)) ∧
    (∀ τ ψ, ⟪coupledσ, τ⟫ - ⟪coupledu + tangentialU, bggSegment.dt0 ψ⟫ -
      ⟪coupledMult, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) ∧
    (∀ v, ⟪bggSegment.dt0 coupledφ, v⟫ +
      ⟪bggSegment.S1 (coupledu + tangentialU), bggSegment.S1 v⟫ +
      ⟪bggSegment.dt1 (coupledu + tangentialU), bggSegment.dt1 v⟫ =
        (coupledDatum + tangentialDatum) v) ∧
    bggSegment.d0 coupledσ = bggSegment.S0 coupledφ ∧
    ∃ L, 0 ≤ L ∧ IsCsFormTr 0 0 L (coupledσ : W0) ∧
      (∀ a, IsCsFormTr 0 0 L ((coupledφ a : U0) : W0)) ∧
      (∀ a, IsCsFormTr 0 1 L ((((coupledu + tangentialU : Wv U1)) a : U1) : W1)) ∧
      ‖coupledMult‖ ≤ L := by
  obtain ⟨Lc, hLc0, hσ0, hφ0, -, hM0, c1, c2, c3, hσ, hφ, hu, hM, -⟩ :=
    exists_coupled_manufactured_solution
  obtain ⟨-, -, -, L2, hL20, -, -, hu2, -⟩ := tangentialManufactured_solution
  refine ⟨hσ0, hφ0, hM0, not_isCsFormMin_coupledu_add_tangentialU, fun τ ψ => ?_, fun v => ?_,
    c3, Lc + L2, add_nonneg hLc0 hL20, hσ.isCsFormTr.mono (le_add_of_nonneg_right hL20),
    fun a => (hφ a).isCsFormTr.mono (le_add_of_nonneg_right hL20), fun a => ?_,
    hM.trans (le_add_of_nonneg_right hL20)⟩
  · have e := inner_add_left (𝕜 := ℝ) coupledu tangentialU (bggSegment.dt0 ψ)
    have h0 := inner_tangentialU_dt0 ψ
    have h1 := c1 τ ψ
    linarith
  · have eS := map_add bggSegment.S1 coupledu tangentialU
    have ed := map_add bggSegment.dt1 coupledu tangentialU
    have eS' := (congrArg (fun z : W2 => ⟪z, bggSegment.S1 v⟫) eS).trans
      (inner_add_left (𝕜 := ℝ) (bggSegment.S1 coupledu) (bggSegment.S1 tangentialU)
        (bggSegment.S1 v))
    have ed' := (congrArg (fun z : Wv W2 => ⟪z, bggSegment.dt1 v⟫) ed).trans
      (inner_add_left (𝕜 := ℝ) (bggSegment.dt1 coupledu) (bggSegment.dt1 tangentialU)
        (bggSegment.dt1 v))
    have eD := LinearMap.add_apply coupledDatum tangentialDatum v
    have eT : tangentialDatum v = ⟪bggSegment.S1 tangentialU, bggSegment.S1 v⟫ +
        ⟪bggSegment.dt1 tangentialU, bggSegment.dt1 v⟫ := rfl
    have h2 := c2 v
    linarith
  · rw [PiLp.add_apply, Submodule.coe_add]
    exact (hu a).isCsFormTr.add (hu2 a)

end TangentialManufactured

/-! ### A classical solution of (6.2) with nonzero normal component on `∂Q` -/

section WaveTangential

/-- The components of `dw` (`w` the witness). -/
abbrev tangentialDψ : formIdx 3 2 → (Fin 3 → ℝ) → ℝ :=
  formComp (FiniteElement.extDeriv (normalWitness (n := 3)))

theorem contDiff_tangentialDψ (r : formIdx 3 2) : ContDiff ℝ 1 (tangentialDψ r) :=
  contDiff_pi.1 (contDiff_extDeriv (m := 1) ((contDiff_normalWitness (n := 3)).of_le (by simp)))
    r.1

theorem memLp_tangentialDψ (r : formIdx 3 2) :
    MemLp (tangentialDψ r) 2 (volume.restrict (cubeDomain 3)) :=
  memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
    (contDiff_tangentialDψ r).continuous

theorem memLp_formalAdj_tangentialDψ (r : formIdx 3 1) :
    MemLp ((extDerivOp ℝ 3 1).formalAdj.apply tangentialDψ r) 2
      (volume.restrict (cubeDomain 3)) :=
  memLp_of_continuous (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3)
    (ConstCoeffOp.continuous_apply _ (formalAdj_extDerivOp_isOrderLE 1) contDiff_tangentialDψ r)

/-- The source `f̄ = (curl* curl w, 0, 0) ∈ (L²Λ¹)³` (`dᵗ dw`, an `L²` field: `w` is smooth up to
the boundary). -/
def waveTangentialSrc : Wv W1 :=
  WithLp.toLp 2 (Pi.single 0 (toL2F memLp_formalAdj_tangentialDψ))

theorem waveTangentialSrc_apply_of_ne {a : Fin 3} (ha : a ≠ 0) : waveTangentialSrc a = 0 := by
  simp [waveTangentialSrc, ha]

theorem waveTangentialSrc_apply_zero :
    waveTangentialSrc 0 = toL2F memLp_formalAdj_tangentialDψ := by
  simp [waveTangentialSrc]

theorem D1_tangentialU0 : D1 tangentialU0 = toL2F memLp_tangentialDψ :=
  tangentialX_mem.2

/-- `⟪curl u, curl v⟫ = ⟪f̄, v⟫` (Green's formula on `D(d_min)`; no condition on `dw` at `∂Q`). -/
theorem inner_dt1_tangentialU (v : Wv U1) :
    ⟪bggSegment.dt1 tangentialU, bggSegment.dt1 v⟫ = ⟪waveTangentialSrc, incl1 v⟫ := by
  rw [inner_Vt, inner_Vt, Fin.sum_univ_three, Fin.sum_univ_three]
  have h1 : ∀ a : Fin 3, a ≠ 0 → (bggSegment.dt1 tangentialU) a = 0 := fun a ha => by
    change D1 (tangentialU a) = 0
    rw [tangentialU_apply_of_ne ha, LinearPMap.map_zero]
  have h2 : ∀ a : Fin 3, a ≠ 0 → waveTangentialSrc a = 0 := fun a ha =>
    waveTangentialSrc_apply_of_ne ha
  have n1 : (1 : Fin 3) ≠ 0 := by simp
  have n2 : (2 : Fin 3) ≠ 0 := by simp
  have z1 : ⟪(bggSegment.dt1 tangentialU) 1, (bggSegment.dt1 v) 1⟫ = 0 := by
    rw [h1 1 n1]; exact inner_zero_left _
  have z2 : ⟪(bggSegment.dt1 tangentialU) 2, (bggSegment.dt1 v) 2⟫ = 0 := by
    rw [h1 2 n2]; exact inner_zero_left _
  have z3 : ⟪waveTangentialSrc 1, (incl1 v) 1⟫ = 0 := by
    rw [h2 1 n1]; exact inner_zero_left _
  have z4 : ⟪waveTangentialSrc 2, (incl1 v) 2⟫ = 0 := by
    rw [h2 2 n2]; exact inner_zero_left _
  simp only [z1, z2, z3, z4, add_zero]
  have e0 : (bggSegment.dt1 tangentialU) 0 = toL2F memLp_tangentialDψ := by
    change D1 (tangentialU 0) = _
    rw [tangentialU_apply_zero, D1_tangentialU0]
  have e1 : waveTangentialSrc 0 = toL2F memLp_formalAdj_tangentialDψ :=
    waveTangentialSrc_apply_zero
  simp only [e0, e1]
  have key := (extDerivOp ℝ 3 1).minimal_green (isOpen_cubeDomain 3) (extDerivOp_isOrderLE 1)
    (v 0) contDiff_tangentialDψ memLp_tangentialDψ memLp_formalAdj_tangentialDψ
  have e2 : (bggSegment.dt1 v) 0 = D1 (v 0) := rfl
  have e3 : (incl1 v) 0 = ((v 0 : U1) : W1) := rfl
  simp only [e2, e3]
  rw [real_inner_comm, key, real_inner_comm]

/-- **A classical solution of (6.2) on the cube whose fields are not flat at `∂Q`**: `σ = φ = 0`,
`u(t) = ū = tangentialU` (normal component nonzero on `{y₀ = 0}`), `M ≡ 0` (`S¹ū = 0`),
`ρ(t) = t curl ū`, `ℓ = 0`, source `f(t) = t f̄`, `f̄ = (curl* curl w, 0, 0)`. -/
def waveTangential (T : ℝ) :
    Feec.BGG.ExactWave bggSegment T (srcFun fun t => t • waveTangentialSrc) where
  σ _ := 0
  φ _ := 0
  u _ := tangentialU
  M _ := 0
  ρ t := t • bggSegment.dt1 tangentialU
  ℓ _ := 0
  σ' _ := 0
  φ' _ := 0
  u' _ := 0
  M' _ := 0
  ρ' _ := bggSegment.dt1 tangentialU
  ℓ' _ := 0
  cσ := continuousOn_const
  cu := continuousOn_const
  cM := continuousOn_const
  cρ := (continuous_id.smul continuous_const).continuousOn
  cdφ := continuousOn_const
  cSu := continuousOn_const
  cdu := continuousOn_const
  cℓ _ := continuousOn_const
  cσ' := continuousOn_const
  cu' := continuousOn_const
  cM' := continuousOn_const
  cρ' := continuousOn_const
  cdφ' := continuousOn_const
  cSu' := continuousOn_const
  cdu' := continuousOn_const
  cℓ' _ := continuousOn_const
  dσ t _ := hasDerivWithinAt_const _ _ _
  du t _ := hasDerivWithinAt_const _ _ _
  dM t _ := hasDerivWithinAt_const _ _ _
  dρ t _ := by
    simpa using ((hasDerivAt_id t).smul_const (bggSegment.dt1 tangentialU)).hasDerivWithinAt
  ddφ t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.dt0 (0 : Wv U0))
  dSu t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.S1 tangentialU)
  ddu t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.dt1 tangentialU)
  dℓ t _ μ := by simpa using hasDerivWithinAt_const t (Ici t) (0 : ℝ)
  ea _ _ τ ψ := by
    simp only [inner_zero_left, LinearMap.zero_apply, zero_sub, sub_zero, neg_eq_zero]
    exact inner_tangentialU_dt0 ψ
  eb t _ v := by
    rw [srcFun_apply]
    simp only [map_zero, inner_zero_left, zero_add, inner_smul_left, RCLike.conj_to_real,
      inner_dt1_tangentialU]
  ec _ _ N := by simp [segS1_tangentialU]
  ed _ _ μ := by simp
  ee _ _ := by rw [map_zero, map_zero]
  ee' _ _ := by rw [map_zero, map_zero]

/-- **Non-vacuity of `cubeWave_rate_tr` beyond the flat class**: `waveTangential T` meets the
hypotheses of `cubeWave_rate_tr` with one bound `L` on `[0,T]`, has `u(t) ≠ 0`, and its `u(t)` is
not flat (`not_isCsFormMin_tangentialU0`). -/
theorem waveTangential_hyps {T : ℝ} (hT : 0 < T) : ∃ L, 0 ≤ L ∧
    (∀ t ∈ Icc 0 T, IsSmoothStateTr L ((waveTangential T).σ t) ((waveTangential T).φ t)
        ((waveTangential T).u t) ((waveTangential T).M t) ((waveTangential T).ρ t) ∧
      IsSmoothStateTr L ((waveTangential T).σ' t) ((waveTangential T).φ' t)
        ((waveTangential T).u' t) ((waveTangential T).M' t) ((waveTangential T).ρ' t)) ∧
    (∀ t ∈ Icc 0 T, ∀ μ : U1, |(waveTangential T).ℓ t μ| ≤ L * ‖μ‖ ∧
      |(waveTangential T).ℓ' t μ| ≤ L * ‖μ‖) ∧
    (∀ t, (waveTangential T).u t ≠ 0) := by
  obtain ⟨Lu, hLu0, hLu⟩ := exists_isCsFormTr_tangentialX
  obtain ⟨Ld, hLd0, hLd⟩ := exists_isCsFormTr (n := 3) 0 (k := 2)
    (contDiff_extDeriv (m := 2) ((contDiff_normalWitness (n := 3)).of_le (by simp)))
    (IsDeg.extDeriv isDeg_normalWitness)
    (isTangentialZero_normalWitness.extDeriv
      ((contDiff_normalWitness (n := 3)).differentiable (by simp)))
  have hd0 : IsCsFormTr 0 2 Ld ((bggSegment.dt1 tangentialU) 0) := by
    have e : (bggSegment.dt1 tangentialU) 0 = toL2F memLp_tangentialDψ := by
      change D1 (tangentialU 0) = _
      rw [tangentialU_apply_zero, D1_tangentialU0]
    rw [e]; exact hLd
  have hdne : ∀ a : Fin 3, a ≠ 0 → (bggSegment.dt1 tangentialU) a = 0 := fun a ha => by
    change D1 (tangentialU a) = 0
    rw [tangentialU_apply_of_ne ha, LinearPMap.map_zero]
  set L1 := Lu + Ld
  have hL10 : 0 ≤ L1 := add_nonneg hLu0 hLd0
  refine ⟨(1 + T) * L1, by positivity, fun t ht => ?_, fun t _ μ => ?_,
    fun _ => tangentialU_ne_zero⟩
  · have hta : |t| ≤ 1 + T := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
    have hLL : ∀ {L' : ℝ}, L' ≤ L1 → L' ≤ (1 + T) * L1 := fun h =>
      h.trans (le_mul_of_one_le_left hL10 (by linarith))
    have hz : ∀ k : ℕ, IsCsFormTr 0 (k : ℤ) ((1 + T) * L1)
        (0 : L2F ℝ (cubeDomain 3) (formIdx 3 k)) := fun k => isCsFormTr_zero 0 k (by positivity)
    have hρ : ∀ a, IsCsFormTr 0 2 ((1 + T) * L1) ((bggSegment.dt1 tangentialU) a) := fun a => by
      by_cases ha : a = 0
      · subst ha; exact hd0.mono (hLL (le_add_of_nonneg_left hLu0))
      · rw [hdne a ha]; exact hz 2
    have hρt : ∀ a, IsCsFormTr 0 2 ((1 + T) * L1)
        ((t • bggSegment.dt1 tangentialU : Wv W2) a) := fun a => by
      rw [PiLp.smul_apply]
      by_cases ha : a = 0
      · subst ha
        exact (hd0.smul t).mono (mul_le_mul hta (le_add_of_nonneg_left hLu0) hLd0 (by linarith))
      · rw [hdne a ha, smul_zero]; exact hz 2
    have hu : ∀ a, IsCsFormTr 0 1 ((1 + T) * L1) ((tangentialU a : U1) : W1) := fun a => by
      by_cases ha : a = 0
      · subst ha; rw [tangentialU_apply_zero]; exact hLu.mono (hLL (le_add_of_nonneg_right hLd0))
      · rw [tangentialU_apply_of_ne ha]; exact hz 1
    exact ⟨⟨hz 0, fun a => hz 0, hu, hz 2, hρt⟩, ⟨hz 0, fun a => hz 0, fun a => hz 1, hz 2, hρ⟩⟩
  · simp only [waveTangential, LinearMap.zero_apply, abs_zero]
    exact ⟨by positivity, by positivity⟩

end WaveTangential

end Feec.Models.Cube.WeakSymmetry
