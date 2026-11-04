module

public import Feec.Models.Cube.CubicalSmoothingEstimates
public import Feec.Models.Cube.PolyRate

/-!
# The cubical finite element methods on the cube as conforming families

For every degree vector `b` (`b_j ≥ 1`; `b = fun _ => r` is `Q_r⁻Λ`, the Nédélec elements on
hexahedra of the first kind for `r ≥ 1` in degree `1`) and the cubical meshes of `Q = (0, ½)ⁿ` with
`N + 1` cells per direction, the cubical complexes `FEM.qMinus n b N ⊆ HΛ(Q)`
(`Feec.Models.Cube.CubicalSmoothingEstimates`) are a conforming family of `HΛ(Q)`, with no
hypothesis:

* **Interpolation error of order `h^{s+1}`** for `s + 1 ≤ b_j` ([ArnoldBoffiBonizzoni2015], §4):
  the cellwise estimate of the global canonical interpolant
  (`exists_norm_sub_cubeFieldGlobalInterp_le`, Bramble–Hilbert on the reference cube) in `L²`
  and, as `Π_h` commutes with `d`, in the graph norm (`FEM.exists_mem_qMinus_le`); its form on
  the regularity classes `FEM.IsCsForm` (`FEM.IsCsForm.exists_mem_qMinus_le`).
* **Density** of the cubical spaces in `HΛ(Q)` and in `L²` (`FEM.eventually_exists_qMinus_graph`,
  `FEM.tendsto_infDist_qMinus`), from the density of smooth forms.
* **The conforming family** (`FEM.QMinusSmoothingEstimates.family`, `FEM.qMinusFamily`): the
  smoothed projections `π_N = J_N⁻¹ Q_N` of `FEM.qMinusSmoothingEstimates_pMax`
  (`Feec.HilbertComplex.ConformingFamily.ofSmoothing`), and **its Jackson estimate**
  (`FEM.qMinusJackson`): `IsCsForm s` forms at the order `h^{s+1}`, `s + 1 ≤ min b`, so the
  rated FEEC theorem (`Feec.HilbertComplex.ConformingFamily.feec_rated`) applies at every order.

## References

* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §5 (the spaces `Q_r⁻Λᵏ(𝒯_h)`), §4 (approximation)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (conforming families: bounded cochain projections, approximation), §5.5 (smoothed
  projections)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.FiniteElement.Cube Feec.HilbertComplex
  ExteriorFibre

variable {n : ℕ} {b : Fin n → ℕ}

/-! ### The global `L²` interpolation error -/

/-- **A pointwise bound on the simplex interiors bounds the `L²` distance** between a continuous
form and a glued cubical field. -/
theorem norm_formL2_sub_cubeGlue_le_of_forall {L : ℝ} [Fact (0 < L)] {N : ℕ} [NeZero N] (k : ℕ)
    (w : contForms n) (u : CubeCell (fun _ : Fin n => N) → Koszul.PolyForm ℝ (Fin n)) {B : ℝ}
    (hB : 0 ≤ B)
    (hpt : ∀ T ∈ (cubeRefinement n L N).simplices, ∀ x ∈ interior T.closedInterior,
      ∀ s : Finset (Fin n), #s = k →
        |(w : FormField n) x s - cellField L u (simplexCell L T) x s| ≤ B) :
    ‖formL2 (isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)).measurableSet
        (cubeRefinement n L N).isBounded_domain k w - cubeGlue n L N k u‖ ≤
      Fintype.card (formIdx n k) *
        (volume.real (cubeRefinement n L N).domain ^ (1 / 2 : ℝ) * B) := by
  set M := cubeRefinement n L N
  have hΩ := (isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)).measurableSet
  have : IsFiniteMeasure (volume.restrict M.domain) :=
    isFiniteMeasure_restrict.2 M.isBounded_domain.measure_lt_top.ne
  change ‖formL2 hΩ M.isBounded_domain k w - pieceL2 M M.domain
    (fun T => formComp (k := (k : ℤ)) (cellField L u (simplexCell L T)))
    (fun _ _ s => continuous_formComp (contDiff_cellField u _ (r := 0)).continuous s)‖ ≤ _
  refine L2F.norm_le_card_mul _ (by positivity) fun s => ?_
  refine (Lp.norm_le_of_ae_bound hB ?_).trans (le_of_eq ?_)
  · have hcont : ∀ T ∈ M.simplices, ∀ s : formIdx n k,
        Continuous (formComp (k := (k : ℤ)) (cellField L u (simplexCell L T)) s) :=
      fun T _ s => continuous_formComp (contDiff_cellField u _ (r := 0)).continuous s
    filter_upwards [Lp.coeFn_sub (formL2 hΩ M.isBounded_domain k w s)
      (pieceL2 M M.domain (fun T => formComp (k := (k : ℤ)) (cellField L u (simplexCell L T)))
        hcont s), coeFn_formL2 hΩ M.isBounded_domain k w s,
      coeFn_pieceL2 (𝕜 := ℝ) M M.domain _ hcont s, Feec.FiniteElement.ae_mem_interior M hΩ]
      with x h1 h2 h3 hx
    obtain ⟨T, hT, hxT⟩ := hx
    rw [PiLp.sub_apply, h1, Pi.sub_apply, h2, h3, pieceFun_of_mem_interior M _ hT hxT,
      Real.norm_eq_abs]
    have hs : #s.1 = k := by exact_mod_cast s.2
    exact hpt T hT x hxT s.1 hs
  · rw [measureUnivNNReal, Measure.restrict_apply_univ, ENNReal.toReal_ofNat, one_div]
    rfl

variable (n) in
/-- The constant of the `L²` interpolation error of `Q_b⁻Λᵏ` at the order `h^{s+1}`
(`exists_norm_sub_cubeFieldGlobalInterp_le`, `0` unless `s + 1 ≤ b_j` for all `j`). -/
def qMinusInterpConst (b : Fin n → ℕ) (s k : ℕ) : ℝ :=
  if h : ∀ j, s + 1 ≤ b j then
    Fintype.card (formIdx n k) * volume.real (cubeDomain n) ^ (1 / 2 : ℝ) *
      max (exists_norm_sub_cubeFieldGlobalInterp_le (k := k) (Nat.succ_pos s) h).choose 0
  else 0

theorem qMinusInterpConst_nonneg (b : Fin n → ℕ) (s k : ℕ) : 0 ≤ qMinusInterpConst n b s k := by
  unfold qMinusInterpConst
  split_ifs
  · positivity
  · exact le_rfl

/-- **The pointwise interpolation error on the cube** at the order `h_N^{s+1}`. -/
theorem abs_sub_cubeFieldGlobalInterp_le {s k : ℕ} (hs : ∀ j, s + 1 ≤ b j) {N : ℕ}
    {w : FormField n} (hw : ContDiff ℝ (s + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M)
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) (hT : T ∈ (mesh n N).simplices) {x : Fin n → ℝ}
    (hx : x ∈ T.closedInterior) (t : Finset (Fin n)) :
    |w x t - cellField (1 / 2) (cubeFieldGlobalInterp (N := N + 1) (1 / 2) k
      (fun j => (Nat.succ_pos s).trans_le (hs j)) w) (simplexCell (1 / 2) T) x t| ≤
      max (exists_norm_sub_cubeFieldGlobalInterp_le (k := k) (Nat.succ_pos s) hs).choose 0 *
        (meshSize N ^ (s + 1) * M) := by
  obtain hC := (exists_norm_sub_cubeFieldGlobalInterp_le (k := k) (Nat.succ_pos s) hs).choose_spec
  have hxm := simplexCell_closedInterior_subset (L := 1 / 2) (N := N + 1) hT hx
  have h := hC (1 / 2) (N + 1) w Set.univ isOpen_univ (subset_univ _) hw.contDiffOn hdeg M
    (fun y hy => hM y (by rw [closure_cubeDomain]; exact hy)) _ x hxm
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (subset_closure (center_mem_cubeDomain n)))
  refine ((norm_le_pi_norm _ t).trans h).trans ?_
  rw [show (1 / 2 : ℝ) / ((N + 1 : ℕ) : ℝ) = meshSize N from (hN_eq_meshSize N), mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (mul_nonneg (pow_nonneg (meshSize_pos N).le _) hM0)

variable [NeZero n]

/-- **The `L²` and graph-norm interpolation error of the cubical spaces on the cube** at the order
`h^{s+1}` ([ArnoldBoffiBonizzoni2015], §4): for a `C^{s+2}` degree-`k` form `w` with
`‖D^{s+1} w‖ ≤ L` and `‖D^{s+1} dw‖ ≤ L'` on `cl Q` and `s + 1 ≤ b_j`, the canonical
interpolant `v = Π_N w ∈ Vₕᵏ` satisfies `‖w - v‖ ≤ A_k h_N^{s+1} L` and
`‖dw - dv‖ ≤ A_{k+1} h_N^{s+1} L'` (`d Π_h = Π_h d`). -/
theorem exists_mem_qMinus_le {s : ℕ} (hs : ∀ j, s + 1 ≤ b j) (N k : ℕ) {w : FormField n}
    (hw : ContDiff ℝ (s + 2) w) (hdeg : ∀ x, IsDeg k (w x)) {L L' : ℝ}
    (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L)
    (hL' : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (qMinus n b N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ qMinusInterpConst n b s k * (meshSize N ^ (s + 1) * L) ∧
      ∃ hv : v ∈ ((complex n).d k (k + 1)).domain,
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by
              exact_mod_cast Nat.le_add_left 1 (s + 1)))⟩ -
          (complex n).d k (k + 1) ⟨v, hv⟩‖ ≤
            qMinusInterpConst n b s (k + 1) * (meshSize N ^ (s + 1) * L') := by
  have hb : ∀ j, 1 ≤ b j := fun j => (Nat.succ_pos s).trans_le (hs j)
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))
  have hws : ContDiff ℝ (s + 1) w := hw.of_le (by exact_mod_cast Nat.le_succ (s + 1))
  have hdw : ContDiff ℝ (s + 1) (extDeriv w) := contDiff_extDeriv (m := s + 1) (by
    exact_mod_cast hw)
  have hdeg' : ∀ x, IsDeg (k + 1) (extDeriv w x) := fun x => IsDeg.extDeriv hdeg x
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL _ (subset_closure (center_mem_cubeDomain n)))
  have hL'0 : 0 ≤ L' := (norm_nonneg _).trans (hL' _ (subset_closure (center_mem_cubeDomain n)))
  refine (deRham ℝ n).maximalSubcomplexOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (cubeSubcomplex n (1 / 2) (N + 1) b)
    (fun Θ hΘ S' => ∀ hbd : Bornology.IsBounded Θ,
      ∀ hvol : volume.real Θ = volume.real (cubeDomain n),
      ∃ v ∈ S'.V k,
        ‖formL2 hΘ.measurableSet hbd k ⟨w, hw.continuous⟩ - asForm n v‖ ≤
          qMinusInterpConst n b s k * (meshSize N ^ (s + 1) * L) ∧
        ∃ hv : v ∈ (((deRham ℝ n).maximalComplex hΘ).d k (k + 1)).domain,
          ‖formL2 hΘ.measurableSet hbd ((k : ℤ) + 1)
              ⟨extDeriv w, continuous_extDeriv hw1⟩ -
            asForm n (((deRham ℝ n).maximalComplex hΘ).d k (k + 1) ⟨v, hv⟩)‖ ≤
            qMinusInterpConst n b s (k + 1) * (meshSize N ^ (s + 1) * L')) ?_
    (isBounded_cubeDomain n) rfl
  intro hbd hvol
  have hΩo := isOpen_cubeRefinement_domain (n := n) (L := 1 / 2) (N := N + 1)
  obtain ⟨hmem, hval⟩ := cubeGlue_cubeFieldGlobalInterp_extDeriv (L := 1 / 2) (N := N + 1)
    (k := k) hb isOpen_univ (subset_univ _) hw1.contDiffOn
  have hB1 : ∀ k', 0 ≤ max (exists_norm_sub_cubeFieldGlobalInterp_le (k := k') (Nat.succ_pos s)
      hs).choose 0 * (meshSize N ^ (s + 1) * L) := fun k' => by
    have := (meshSize_pos N).le; positivity
  have hB2 : ∀ k', 0 ≤ max (exists_norm_sub_cubeFieldGlobalInterp_le (k := k') (Nat.succ_pos s)
      hs).choose 0 * (meshSize N ^ (s + 1) * L') := fun k' => by
    have := (meshSize_pos N).le; positivity
  have hconst : ∀ k', qMinusInterpConst n b s k' = Fintype.card (formIdx n k') *
      volume.real (cubeDomain n) ^ (1 / 2 : ℝ) *
        max (exists_norm_sub_cubeFieldGlobalInterp_le (k := k') (Nat.succ_pos s) hs).choose 0 :=
    fun k' => dite_eq_left hs
  refine ⟨cubeGlue n (1 / 2) (N + 1) k (cubeFieldGlobalInterp (1 / 2) k hb w),
    ⟨⟨_, cubeFieldGlobalInterp_mem hb w⟩, rfl⟩, ?_, ?_⟩
  · have h := norm_formL2_sub_cubeGlue_le_of_forall (L := 1 / 2) (N := N + 1) k
      ⟨w, hw.continuous⟩ _ (hB1 k) fun T hT x hx t _ =>
        abs_sub_cubeFieldGlobalInterp_le hs hws hdeg hL T hT (interior_subset hx) t
    refine h.trans (le_of_eq ?_)
    rw [show volume.real (cubeRefinement n (1 / 2) (N + 1)).domain = volume.real (cubeDomain n)
      from hvol, hconst]; ring
  · refine ⟨by rw [deRham_maximalComplex_d]; exact hmem, ?_⟩
    rw [LinearPMap.apply_eq_of_eq' (deRham_maximalComplex_d (isOpen_mesh_domain n N) (k : ℤ))]
    have h := norm_formL2_sub_cubeGlue_le_of_forall (L := 1 / 2) (N := N + 1) (k + 1)
      ⟨extDeriv w, hdw.continuous⟩ (cubeFieldGlobalInterp (1 / 2) (k + 1) hb (extDeriv w))
      (hB2 (k + 1)) fun T hT x hx t _ =>
        abs_sub_cubeFieldGlobalInterp_le hs hdw hdeg' hL' T hT (interior_subset hx) t
    erw [hval]
    refine h.trans (le_of_eq ?_)
    rw [show volume.real (cubeRefinement n (1 / 2) (N + 1)).domain = volume.real (cubeDomain n)
      from hvol, hconst]; push_cast; ring

/-! ### Density of the cubical spaces -/

/-- **Graph-norm density of the cubical spaces in `HΛᵏ(Q)`**: every `x ∈ D(d)` is the limit, in
the graph norm, of points of the spaces `Vₕᵏ` of `Q_b⁻Λ` (`b_j ≥ 1`). -/
theorem eventually_exists_qMinus_graph (hb : ∀ j, 1 ≤ b j) (k : ℤ)
    (x : L2F ℝ (cubeDomain n) (formIdx n k)) (hx : x ∈ ((complex n).d k (k + 1)).domain) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (qMinus n b N).V k, ‖x - v‖ < ε ∧
      ‖(complex n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((qMinus n b N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth (isOpen_cubeDomain n) (isBounded_cubeDomain n)
    (by norm_num : (0 : ℝ) < 1 / 4) (starBall n) (fun N => qMinus n b N)
    (fun k w hw hdeg => ?_) k x hx hε
  have hw2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := exists_bound_iteratedFDeriv
    (hw.of_le (WithTop.coe_le_coe.2 le_top) : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) w)
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_iteratedFDeriv (m := 1)
    (contDiff_extDeriv (m := 1) (hw.of_le (WithTop.coe_le_coe.2 le_top)))
  have hs : ∀ j, 0 + 1 ≤ b j := hb
  refine ⟨fun N => qMinusInterpConst n b 0 k * (meshSize N ^ (0 + 1) * L) +
    qMinusInterpConst n b 0 (k + 1) * (meshSize N ^ (0 + 1) * L'), by
      simpa using (((tendsto_meshSize.pow 1).mul_const L).const_mul
        (qMinusInterpConst n b 0 k)).add
        (((tendsto_meshSize.pow 1).mul_const L').const_mul (qMinusInterpConst n b 0 (k + 1))),
    fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := exists_mem_qMinus_le hs N k hw2 hdeg hL hL'
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right (mul_nonneg (qMinusInterpConst_nonneg _ _ _)
    (mul_nonneg (pow_nonneg (meshSize_pos N).le _) hL'0))), hdv, hv2.trans (le_add_of_nonneg_left
      (mul_nonneg (qMinusInterpConst_nonneg _ _ _) (mul_nonneg (pow_nonneg (meshSize_pos N).le _)
        hL0)))⟩

/-- `dist(q, Vₕʲ) → 0` for every `q ∈ L²(Q; Λʲ)` (cubical spaces). -/
theorem tendsto_infDist_qMinus (hb : ∀ j, 1 ≤ b j) (j : ℤ)
    (q : L2F ℝ (cubeDomain n) (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((qMinus n b N).V j :
      Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => qMinus n b N) q fun _ ha =>
    Subcomplex.eventually_exists_lt_of_graph
      (fun k x hx _ hε => eventually_exists_qMinus_graph hb k x hx hε) j q ha

/-! ### The cubical complexes as a conforming family -/

/-- **The conforming family of the smoothing estimates `hE`** ([AFW2010], §5.5): the cubical
complexes with the smoothed projections `π_N = J_N⁻¹ Q_N` (`ConformingFamily.ofSmoothing`). -/
def QMinusSmoothingEstimates.family {hb : ∀ j, 1 ≤ b j} {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C : ℝ} (hE : QMinusSmoothingEstimates b hb p C) : ConformingFamily (complex n) ℕ :=
  .ofSmoothing atTop (qMinus n b) (fun N => qMinusSmoothed hb N (p N) (hE.isMaximal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound (tendsto_infDist_qMinus hb)

theorem qMinusSmoothingEstimates_exists (hb : ∀ j, 1 ≤ b j) :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ), QMinusSmoothingEstimates b hb p C := by
  obtain ⟨γ₀, hγ₀, hγ₀1, h⟩ := qMinusSmoothingEstimates_pMax hb
  obtain ⟨C, hC⟩ := h γ₀ hγ₀ hγ₀1 le_rfl
  exact ⟨_, C, hC⟩

variable (n) in
/-- **The cubical finite element complexes `Q_b⁻Λ` of the cube** (`b_j ≥ 1`; `Q_r⁻Λ` for
`b = fun _ => r`) with the smoothed projections (`qMinusSmoothingEstimates_exists`), a conforming
family of `HΛ(Q)`. -/
def qMinusFamily (hb : ∀ j, 1 ≤ b j) : ConformingFamily (complex n) ℕ :=
  (qMinusSmoothingEstimates_exists (n := n) hb).choose_spec.choose_spec.family

@[simp] theorem qMinusFamily_V (hb : ∀ j, 1 ≤ b j) : (qMinusFamily n hb).V = qMinus n b := rfl

/-! ### The Jackson estimate -/

variable (n) in
/-- The constant `B_{s,j} = A_{s,j} + A_{s,j+1}` of the graph-norm interpolation error. -/
def qMinusInterpBound (b : Fin n → ℕ) (s : ℕ) (j : ℤ) : ℝ :=
  qMinusInterpConst n b s j.toNat + qMinusInterpConst n b s (j.toNat + 1)

/-- **Degreewise interpolation error of order `s + 1`** on the regularity classes: for `x` with
`IsCsForm s j L x` and `s + 1 ≤ b_i`, some `v ∈ Vₕʲ` has `‖x - v‖, ‖d (x - v)‖ ≤ B L h^{s+1}`. -/
theorem IsCsForm.exists_mem_qMinus_le {s : ℕ} (hs : ∀ i, s + 1 ≤ b i) {j : ℤ} {L : ℝ}
    {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsCsForm s j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (qMinus n b N).V j,
      ‖x - v‖ ≤ qMinusInterpBound n b s j * (L * meshSize N ^ (s + 1)) ∧
      ∀ j' (hxj : x ∈ ((complex n).d j j').domain),
        ‖(complex n).d j j' ⟨x - v, Submodule.sub_mem _ hxj ((qMinus n b N).le_domain j j' hv)⟩‖ ≤
          qMinusInterpBound n b s j * (L * meshSize N ^ (s + 1)) := by
  have hh := pow_nonneg (meshSize_pos N).le (s + 1)
  have hB0 : 0 ≤ qMinusInterpBound n b s j * (L * meshSize N ^ (s + 1)) :=
    mul_nonneg (add_nonneg (qMinusInterpConst_nonneg _ _ _) (qMinusInterpConst_nonneg _ _ _))
      (mul_nonneg hL0 hh)
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩
  · have := LocalElement.subsingleton_L2F_of_neg (cubeDomain n) (n := n) hj
    exact (qMinus n b N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := FEM.exists_mem_qMinus_le hs N k hw hdeg hL hL'
  obtain ⟨hdom, hval⟩ := formL2_mem_domain k
    (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))) hdeg
  have hA0 := mul_nonneg (qMinusInterpConst_nonneg (n := n) b s k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (qMinusInterpConst_nonneg (n := n) b s (k + 1)) (mul_nonneg hh hL0)
  have e : qMinusInterpBound n b s k * (L * meshSize N ^ (s + 1)) =
      qMinusInterpConst n b s k * (meshSize N ^ (s + 1) * L) +
        qMinusInterpConst n b s (k + 1) * (meshSize N ^ (s + 1) * L) := by
    simp only [qMinusInterpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [hval, e]
  linarith

variable (n) in
/-- **The Jackson estimate of the cubical complexes**: forms of class `IsCsForm s` are
approximated at the order `h_N^{s+1}` for every `s + 1 ≤ min_j b_j`
(`IsCsForm.exists_mem_qMinus_le`; for `Q_r⁻Λ`, every order up to `h^r`). -/
def qMinusJackson (hb : ∀ j, 1 ≤ b j) : (qMinusFamily n hb).Jackson ℕ where
  meshSize := meshSize
  meshSize_nonneg N := (meshSize_pos N).le
  tendsto_meshSize := tendsto_meshSize
  Reg s j L x := (∀ i, s + 1 ≤ b i) ∧ IsCsForm s j L x
  ord s := ((s + 1 : ℕ) : ℝ)
  B s := qMinusInterpBound n b s
  B_nonneg _ _ := add_nonneg (qMinusInterpConst_nonneg _ _ _) (qMinusInterpConst_nonneg _ _ _)
  jackson s N _ _ _ hL hx := by
    rw [Real.rpow_natCast]; exact hx.2.exists_mem_qMinus_le hx.1 hL N

end Feec.Models.Cube.FEM
