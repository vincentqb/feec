module

public import Feec.FiniteElement.CubeInterpolation
public import Feec.Models.Cube.SmoothingEstimates

/-!
# Smoothed projections for the cubical spaces `Q_b⁻Λᵏ` on the cube

**The smoothed canonical interpolant of `Q_b⁻Λ(𝒯_h)`.** On the uniform cubical mesh of the cube
`(0, L)ⁿ` (`Feec.FiniteElement.CubeConformity`), with any smoothing parameters `p` of the maximal
family for a domain star-shaped with respect to a ball, `Q = Π_h R` (the global canonical
interpolant `Π_h` of `Feec.FiniteElement.CubeInterpolation` of the smoothed form `R u`,
`Feec.FiniteElement.smoothForm`) is a commuting map into the cubical subcomplex
(`Feec.FiniteElement.Cube.cubeSmoothedCommutingMap`): `Π_h` commutes with `d` on `C¹` fields
and only sees `[0, L]ⁿ`, where the smoother commutes with `d_max`.

**The estimates on `Q = (0, ½)ⁿ`.** With `N + 1` cells per direction (`h_N = 1 / (2 (N + 1))`,
whose Freudenthal refinement is the mesh `FEM.mesh n N` of the simplicial families), `Q_b⁻Λ`
is the subcomplex `FEM.qMinus n b N ⊆ HΛ(Q)`, and for the admissible parameters
(`FEM.IsAdm`, `FEM.pMax γ`) of `Feec.Models.Cube.SmoothingEstimates`:

* **uniform `L²` bound** (`FEM.QMinus.exists_norm_smoothedInterp_le`): the cell degrees of
  freedom are bounded in `C⁰` (`exists_norm_cubeFieldInterp_le`), the smoothed field on a closed
  cell by the local mass of any of its simplices (`FEM.IsAdm.abs_smoothForm_le_locMass_of_near`),
  and the local masses have bounded overlap (`FEM.sum_locMass_le`);
* **closeness on `Vₕ`** (`FEM.QMinus.exists_closeConst`): `‖v - Q v‖² ≤ K γ² ‖v‖²`. The
  cell interpolant is stable in its degrees of freedom (`exists_norm_cubeFieldInterp_le_sum_dof`),
  a degree of freedom is the integral of its tangential coefficients over the face
  (`fieldMoment_eq_integral`), and the error integrand of a degree of freedom is the pointwise
  estimate `sqrt_mul_abs_sum_sub_smoothForm_le` of the simplicial families: at points of a
  face whose free coordinates are `γ/2`-interior, every cell sampled by the smoother contains the
  point, and the tangential components of the cell fields agree there
  (`cellField_apply_eq_of_free`); the cell fields are polynomials of degree `≤ Σⱼ b_j`
  (`Q_b⁻Λᵏ ⊆ P_{Σ b}Λᵏ`, `cubeFormMinus_le_polyForm`), with the inverse estimates of the cells
  (`exists_cell_inverse_bound`); near the boundary of the face only the inverse estimates are
  used, on a layer of measure `≤ nγ`.

Hence for every `γ ∈ (0, γ₀]` the maximal-family parameters `pMax γ` give the smoothing
estimates (`FEM.QMinusSmoothingEstimates`, `FEM.qMinusSmoothingEstimates_pMax`): uniformly
`L²`-bounded `Q_N` with `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ`, the hypotheses of the smoothed projections
`π_N = J_N⁻¹ Q_N` ([AFW2010], §5.5; `Feec.HilbertComplex.Subcomplex.CommutingMap`).

## Main definitions

* `Feec.FiniteElement.Cube.cubeSmoothedInterp`, `cubeSmoothedCommutingMap`;
* `Feec.Models.Cube.FEM.qMinus n b N`, `FEM.qMinusSmoothed`, `FEM.QMinusSmoothingEstimates`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothed projections)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §4–§5 (the spaces `Q_r⁻Λᵏ(𝒯_h)`, their degrees of freedom and canonical interpolants)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter

namespace Feec.FiniteElement.Cube

open Feec.Domain Feec.Mesh Feec.HilbertComplex Koszul ExteriorFibre

variable {n : ℕ} {L : ℝ} [Fact (0 < L)] {N : ℕ} [NeZero N] {b : Fin n → ℕ}

/-! ### The smoothed canonical interpolant of `Q_b⁻Λ(𝒯_h)` -/

variable (n L N) in
/-- **The smoothed canonical interpolant** `Q = Π_h R : L²((0, L)ⁿ; Λᵏ) → Q_b⁻Λᵏ(𝒯_h)`: the global
canonical interpolant of the smoothed form ([AFW2010], §5.5); zero in negative degrees. -/
def cubeSmoothedInterp (hb : ∀ j, 1 ≤ b j) (p : SmoothingParam (Fin n → ℝ)) :
    ∀ k : ℤ, L2F ℝ (cubeRefinement n L N).domain (formIdx n k) →ₗ[ℝ]
      L2F ℝ (cubeRefinement n L N).domain (formIdx n k)
  | Int.ofNat k =>
    { toFun := fun x => cubeGlue n L N k (cubeFieldGlobalInterp L k hb
        (smoothForm p (isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)).measurableSet
          k x))
      map_add' := fun x y => by
        rw [map_add, Submodule.coe_add, cubeFieldGlobalInterp_add hb
          (c1Forms_le_contForms (Submodule.coe_mem _))
          (c1Forms_le_contForms (Submodule.coe_mem _)), map_add]
      map_smul' := fun c x => by
        rw [map_smul, Submodule.coe_smul, cubeFieldGlobalInterp_smul, map_smul, RingHom.id_apply] }
  | Int.negSucc _ => 0

theorem cubeSmoothedInterp_natCast (hb : ∀ j, 1 ≤ b j) (p : SmoothingParam (Fin n → ℝ)) (k : ℕ)
    (x : L2F ℝ (cubeRefinement n L N).domain (formIdx n k)) :
    cubeSmoothedInterp n L N hb p k x = cubeGlue n L N k (cubeFieldGlobalInterp L k hb
      (smoothForm p (isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)).measurableSet
        k x)) := rfl

theorem cubeSmoothedInterp_mem (hb : ∀ j, 1 ≤ b j) (p : SmoothingParam (Fin n → ℝ)) (k : ℤ)
    (x : L2F ℝ (cubeRefinement n L N).domain (formIdx n k)) :
    cubeSmoothedInterp n L N hb p k x ∈ cubeV n L N b k := by
  rcases k with k | k
  · exact ⟨⟨_, cubeFieldGlobalInterp_mem hb _⟩, rfl⟩
  · exact Submodule.zero_mem _

/-- **`d_max Q u = Q d_max u`** (maximal family): `Π_h` commutes with `d` on `C¹` fields
(`cubeGlue_cubeFieldGlobalInterp_extDeriv`), sees only `[0, L]ⁿ` (`cubeFieldGlobalInterp_congr`),
and the smoother commutes with `d_max` there (`extDeriv_smoothForm_of_maximal`). -/
theorem maximal_cubeSmoothedInterp [NeZero n] (hb : ∀ j, 1 ≤ b j)
    {p : SmoothingParam (Fin n → ℝ)} {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ (cubeRefinement n L N).domain, ∀ z ∈ Metric.ball x₀ s₀,
      segment ℝ z y ⊆ (cubeRefinement n L N).domain)
    (hp : p.IsMaximal x₀ s₀) (k : ℕ)
    (u : ((extDerivOp ℝ n k).maximal (cubeRefinement n L N).domain).domain) :
    ∃ h : cubeSmoothedInterp n L N hb p k u ∈
        ((extDerivOp ℝ n k).maximal (cubeRefinement n L N).domain).domain,
      (extDerivOp ℝ n k).maximal (cubeRefinement n L N).domain ⟨_, h⟩ =
        cubeSmoothedInterp n L N hb p ((k : ℤ) + 1)
          ((extDerivOp ℝ n k).maximal (cubeRefinement n L N).domain u) := by
  have hΩo := isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)
  set w := smoothForm p hΩo.measurableSet k (u : L2F ℝ _ (formIdx n k))
  obtain ⟨h, hval⟩ := cubeGlue_cubeFieldGlobalInterp_extDeriv (L := L) (N := N) (k := k) hb
    isOpen_univ (subset_univ _) (mem_c1Forms.1 w.2).contDiffOn
  refine ⟨h, hval.trans ?_⟩
  rw [cubeFieldGlobalInterp_congr hb fun x hx =>
    extDeriv_smoothForm_of_maximal p hΩo.measurableSet hΩo hstar hp k u
      (by rwa [closure_cubeRefinement_domain])]
  rfl

variable (n L N) in
/-- **The smoothed canonical interpolant as a commuting map** into the cubical subcomplex
`Q_b⁻Λ(𝒯_h) ⊆ HΛ((0, L)ⁿ)` (maximal family, the cube star-shaped with respect to `B(x₀, s₀)`):
`Q = Π_h R` with `d Q = Q d` in every degree. -/
def cubeSmoothedCommutingMap [NeZero n] (hb : ∀ j, 1 ≤ b j) (p : SmoothingParam (Fin n → ℝ))
    {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ (cubeRefinement n L N).domain, ∀ z ∈ Metric.ball x₀ s₀,
      segment ℝ z y ⊆ (cubeRefinement n L N).domain)
    (hp : p.IsMaximal x₀ s₀) : (cubeSubcomplex n L N b).CommutingMap where
  Q := cubeSmoothedInterp n L N hb p
  mem i x := cubeSmoothedInterp_mem hb p i x
  comm i j x := by
    have hΩo := isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)
    by_cases hij : i + 1 = j
    · subst hij
      have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) hΩo i
      rcases i with k | k
      · rw [LinearPMap.apply_eq_of_eq' hd, LinearPMap.apply_eq_of_eq' hd x]
        obtain ⟨h, hv⟩ := maximal_cubeSmoothedInterp hb hstar hp k ⟨x.1, hd ▸ x.2⟩
        exact hv
      · have h0 : ∀ y : (((deRham ℝ n).maximalComplex hΩo).d (Int.negSucc k)
            (Int.negSucc k + 1)).domain, ((deRham ℝ n).maximalComplex hΩo).d _ _ y = 0 := by
          intro y
          have : y = 0 := Subtype.ext ((LocalElement.subsingleton_L2F_negSucc _ k).elim _ _)
          rw [this, LinearPMap.map_zero]
        rw [h0, h0]
        exact (cubeSmoothedInterp n L N hb p _).map_zero.symm
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij),
        HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact (cubeSmoothedInterp n L N hb p j).map_zero.symm

/-! ### Glued fields -/

/-- **The squared norm of a glued cubical field** is at most the sum of the local squared norms
of the cell fields on the simplices of the refinement. -/
theorem norm_sq_cubeGlue_le {k : ℕ} (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (f : Affine.Simplex ℝ (Fin n → ℝ) n → ℝ)
    (hf : ∀ T ∈ (cubeRefinement n L N).simplices, ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (cellField L ω (simplexCell L T) y s.1) ^ 2 ≤ f T) :
    ‖cubeGlue n L N k ω‖ ^ 2 ≤ ∑ T ∈ (cubeRefinement n L N).simplices, f T :=
  (norm_sq_pieceL2_le _ _ _
    (fun _ _ s => continuous_formComp (contDiff_cellField ω _ (r := 0)).continuous s)).trans
    (Finset.sum_le_sum fun T hT => hf T hT)

/-- **A glued cubical field almost everywhere**: a.e. point of `(0, L)ⁿ` lies in the interior of a
simplex `T'` of the refinement, where the zero extension of the field is the field of the cell
of `T'`. -/
theorem ae_extField_cubeGlue_eq {k : ℕ} {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hk : ∀ m, IsDeg k (ω m)) :
    ∀ᵐ t ∂volume, t ∈ (cubeRefinement n L N).domain → ∃ T' ∈ (cubeRefinement n L N).simplices,
      t ∈ interior T'.closedInterior ∧ ∀ s,
        FiniteElement.extField (cubeGlue n L N k ω) t s =
          cellField L ω (simplexCell L T') t s := by
  set M := cubeRefinement n L N
  have hΩ := (isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)).measurableSet
  have h1 : ∀ᵐ t ∂volume.restrict M.domain, ∀ s : formIdx n k,
      ((cubeGlue n L N k ω s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t =
        pieceFun M (fun T => formComp (k := (k : ℤ)) (cellField L ω (simplexCell L T)) s) t := by
    rw [ae_all_iff]
    exact fun s => coeFn_pieceL2 M M.domain _
      (fun _ _ s => continuous_formComp (contDiff_cellField ω _ (r := 0)).continuous s) s
  rw [← ae_restrict_iff' hΩ]
  filter_upwards [h1, ae_mem_interior M hΩ, ae_restrict_mem hΩ] with t ht1 ⟨T', hT', htT'⟩ htΩ
  refine ⟨T', hT', htT', fun s => ?_⟩
  by_cases hs : (#s : ℤ) = (k : ℤ)
  · rw [FiniteElement.extField, formExt_of_card _ hs, Set.indicator_of_mem htΩ,
      ht1 ⟨s, hs⟩, pieceFun_of_mem_interior M _ hT' htT']
    rfl
  · have : FiniteElement.extField (cubeGlue n L N k ω) t s = 0 := by
      simp [FiniteElement.extField, formExt, hs]
    rw [this, isDeg_cellField (hk _) t s (fun h => hs (by rw [h]))]

/-- A point of the interior of a simplex of the refinement and of the open cell `m` lies in
the cell of the simplex: the cell is `m`. -/
theorem simplexCell_eq_of_mem {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (cubeRefinement n L N).simplices) {m : CubeCell fun _ : Fin n => N}
    {t : Fin n → ℝ} (htT : t ∈ T.closedInterior)
    (ht : ∀ j, ((m j : ℕ) : ℝ) < N / L * t j ∧ N / L * t j < (m j : ℕ) + 1) :
    simplexCell (N := N) L T = m := by
  have h := simplexCell_closedInterior_subset hT htT
  funext j
  have h1 := h j
  have h2 := ht j
  have e1 : ((simplexCell (N := N) L T j : ℕ) : ℝ) < (m j : ℕ) + 1 := by linarith [h1.1, h2.2]
  have e2 : ((m j : ℕ) : ℝ) < (simplexCell (N := N) L T j : ℕ) + 1 := by linarith [h1.2, h2.1]
  have e1' : (simplexCell (N := N) L T j : ℕ) < (m j : ℕ) + 1 := by exact_mod_cast e1
  have e2' : (m j : ℕ) < (simplexCell (N := N) L T j : ℕ) + 1 := by exact_mod_cast e2
  exact Fin.ext (by omega)

/-- **The local `L²` norm of a cell field** is controlled by the glued field on any measurable
set containing the closed cell. -/
theorem formL2Sq_cellField_le {k : ℕ} {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hk : ∀ m, IsDeg k (ω m)) (m : CubeCell fun _ : Fin n => N) {K : Set (Fin n → ℝ)}
    (hmK : closedCell L m ⊆ K) :
    formL2Sq (closedCell L m) (cellField L ω m) ≤ ∑ s : formIdx n k, ∫ t in K,
      ((cubeRefinement n L N).domain.indicator
        ((cubeGlue n L N k ω s : L2 ℝ (cubeRefinement n L N).domain) : (Fin n → ℝ) → ℝ) t) ^ 2 := by
  set M := cubeRefinement n L N
  have hL : 0 < L := Fact.out
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  set U : Set (Fin n → ℝ) := Set.univ.pi fun j =>
    Set.Ioo (L / N * ((m j : ℕ) : ℝ)) (L / N * (((m j : ℕ) : ℝ) + 1))
  have hU : closedCell L m =ᵐ[volume] U := by
    rw [closedCell_eq_pi, Set.pi_univ_Icc]
    exact (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))).symm
  have hUmem : ∀ t ∈ U, ∀ j, ((m j : ℕ) : ℝ) < N / L * t j ∧ N / L * t j < (m j : ℕ) + 1 :=
    fun t ht j => by
    have := ht j (Set.mem_univ j)
    have hNL : (0 : ℝ) < N / L := div_pos hN' hL
    have e : N / L * (L / N) = (1 : ℝ) := by field_simp
    constructor
    · have := mul_lt_mul_of_pos_left this.1 hNL
      rwa [← mul_assoc, e, one_mul] at this
    · have := mul_lt_mul_of_pos_left this.2 hNL
      rwa [← mul_assoc, e, one_mul] at this
  have hUΩ : U ⊆ M.domain := fun t ht => by
    rw [cubeRefinement_domain]
    intro j _
    have h1 := hUmem t ht j
    have hm := (m j).isLt
    have hm' : ((m j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hm
    have hNL : (0 : ℝ) < N / L := div_pos hN' hL
    constructor
    · have : 0 < N / L * t j := (Nat.cast_nonneg _).trans_lt h1.1
      exact pos_of_mul_pos_right this hNL.le
    · have : N / L * t j < N / L * L := by
        rw [div_mul_cancel₀ _ hL.ne']; linarith [h1.2]
      exact lt_of_mul_lt_mul_left this hNL.le
  have hae := ae_extField_cubeGlue_eq (L := L) (N := N) hk
  have hUK : U ⊆ K := fun t ht => hmK (by
    rw [closedCell_eq_pi]
    exact fun j _ => Ioo_subset_Icc_self (ht j (Set.mem_univ j)))
  rw [formL2Sq, Domain.sum_eq_sum_formIdx
    (f := fun s => ∫ x in closedCell L m, (cellField L ω m x s) ^ 2) fun s hs => by
      simp only [isDeg_cellField (hk m) _ s hs]; simp]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [setIntegral_congr_set hU]
  calc ∫ t in U, (cellField L ω m t s.1) ^ 2
      = ∫ t in U, (M.domain.indicator ((cubeGlue n L N k ω s : L2 ℝ M.domain) :
          (Fin n → ℝ) → ℝ) t) ^ 2 := by
        refine setIntegral_congr_ae (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) ?_
        filter_upwards [hae] with t ht htU
        obtain ⟨T', hT', htT', hval⟩ := ht (hUΩ htU)
        have hcell := simplexCell_eq_of_mem hT' (interior_subset htT') (hUmem t htU)
        have := hval s.1
        rw [FiniteElement.extField, formExt_of_card _ s.2, hcell] at this
        rw [← this]
    _ ≤ _ := setIntegral_mono_set
        ((memLp_indicator (isOpen_cubeRefinement_domain (n := n) (L := L)
          (N := N)).measurableSet _).integrable_sq.integrableOn)
        (Eventually.of_forall fun _ => sq_nonneg _) (ae_of_all _ hUK)


/-! ### The geometry of nearby cells -/

/-- **Cells near a cell are in its `2h`-neighbourhood**: if `t ∈ m'` is within `h` of a point of
`m`, then `m'` lies within `2h` of every point `z₀` of `m`. -/
theorem closedCell_subset_cthickening {m m' : CubeCell fun _ : Fin n => N} {x t z₀ : Fin n → ℝ}
    (hx : x ∈ closedCell L m) (ht : t ∈ closedCell L m') (hxt : dist x t < L / N)
    (hz₀ : z₀ ∈ closedCell L m) {S : Set (Fin n → ℝ)} (hz₀S : z₀ ∈ S) :
    closedCell L m' ⊆ Metric.cthickening (2 * (L / N)) S := by
  have hL : 0 < L := Fact.out
  intro z hz
  refine Metric.mem_cthickening_of_dist_le z z₀ _ _ hz₀S ?_
  rw [closedCell_eq_pi] at hx ht hz hz₀
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hh : 0 < L / N := div_pos hL hN'
  refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
  have h1 := hx j (Set.mem_univ j)
  have h2 := ht j (Set.mem_univ j)
  have h3 := hz j (Set.mem_univ j)
  have h4 := hz₀ j (Set.mem_univ j)
  have hxt' : |x j - t j| < L / N := (dist_le_pi_dist x t j).trans_lt hxt
  rw [abs_lt] at hxt'
  -- the cells are neighbours: `|m'_j - m_j| ≤ 1`
  have e1 : ((m' j : ℕ) : ℝ) < (m j : ℕ) + 2 := by
    by_contra hc; push Not at hc; nlinarith [h1.2, h2.1]
  have e2 : ((m j : ℕ) : ℝ) < (m' j : ℕ) + 2 := by
    by_contra hc; push Not at hc; nlinarith [h1.1, h2.2]
  have e1' : (m' j : ℕ) ≤ (m j : ℕ) + 1 := by
    have : (m' j : ℕ) < (m j : ℕ) + 2 := by exact_mod_cast e1
    omega
  have e2' : (m j : ℕ) ≤ (m' j : ℕ) + 1 := by
    have : (m j : ℕ) < (m' j : ℕ) + 2 := by exact_mod_cast e2
    omega
  have f1 : ((m' j : ℕ) : ℝ) ≤ (m j : ℕ) + 1 := by exact_mod_cast e1'
  have f2 : ((m j : ℕ) : ℝ) ≤ (m' j : ℕ) + 1 := by exact_mod_cast e2'
  rw [Real.dist_eq, abs_le]
  constructor <;> nlinarith [h3.1, h3.2, h4.1, h4.2]

/-- **Cells sampled near an interior point of a face**: a point `x = h (m + y_g)` of a face `g` of
the cell `m` (fixed coordinates `0` or `1`) whose coordinates `y` are `θ`-interior to `[0, 1]`,
and a point `t` of a closed cell `m'` with `‖x - t‖ < θ h`, `θ ≤ ½`: then `x ∈ m'`, and `m'`
agrees with `m` in the free directions of `g`. -/
theorem mem_closedCell_of_near_face {m m' : CubeCell fun _ : Fin n => N} {g : Fin n → Option ℝ}
    (hg : ∀ j c, g j = some c → c = 0 ∨ c = 1) {θ : ℝ} (hθ : θ ≤ 1 / 2) {y : Fin n → ℝ}
    (hy : ∀ j, θ ≤ y j ∧ y j ≤ 1 - θ) {t : Fin n → ℝ} (ht : t ∈ closedCell L m')
    (hxt : dist ((fun i => L / N * ((m i : ℕ) : ℝ)) + (L / N) • planePoint g y) t <
      θ * (L / N)) :
    (fun i => L / N * ((m i : ℕ) : ℝ)) + (L / N) • planePoint g y ∈ closedCell L m' ∧
      ∀ j, g j = none → m' j = m j := by
  have hL : 0 < L := Fact.out
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hh : 0 < L / N := div_pos hL hN'
  set x := (fun i => L / N * ((m i : ℕ) : ℝ)) + (L / N) • planePoint g y
  have hcoord : ∀ j, |x j - t j| < θ * (L / N) := fun j =>
    (Real.dist_eq _ _ ▸ dist_le_pi_dist x t j).trans_lt hxt
  rw [closedCell_eq_pi] at ht ⊢
  have key : ∀ j, (g j = none → m' j = m j) ∧ x j ∈ Set.Icc (L / N * ((m' j : ℕ) : ℝ))
      (L / N * (((m' j : ℕ) : ℝ) + 1)) := fun j => by
    have h2 := ht j (Set.mem_univ j)
    have h3 := hcoord j
    rw [abs_lt] at h3
    have hxj : x j = L / N * (((m j : ℕ) : ℝ) + planePoint g y j) := by
      simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    cases hgj : g j with
    | none =>
      have hpp : planePoint g y j = y j := by simp [planePoint, hgj]
      rw [hpp] at hxj
      obtain ⟨hy1, hy2⟩ := hy j
      have e1 : ((m' j : ℕ) : ℝ) < (m j : ℕ) + 1 := by
        by_contra hc; push Not at hc; nlinarith [h2.1]
      have e2 : ((m j : ℕ) : ℝ) < (m' j : ℕ) + 1 := by
        by_contra hc; push Not at hc; nlinarith [h2.2]
      have e1' : (m' j : ℕ) < (m j : ℕ) + 1 := by exact_mod_cast e1
      have e2' : (m j : ℕ) < (m' j : ℕ) + 1 := by exact_mod_cast e2
      have heq : m' j = m j := Fin.ext (by omega)
      refine ⟨fun _ => heq, ?_⟩
      rw [hxj, heq]
      constructor <;> nlinarith
    | some c =>
      have hpp : planePoint g y j = c := by simp [planePoint, hgj]
      rw [hpp] at hxj
      refine ⟨fun h => absurd h (by simp), ?_⟩
      rcases hg j c hgj with rfl | rfl
      · -- `x_j = h m_j` is a grid point
        have e1 : ((m' j : ℕ) : ℝ) < (m j : ℕ) + 1 := by
          by_contra hc; push Not at hc; nlinarith [h2.1]
        have e2 : ((m j : ℕ) : ℝ) < (m' j : ℕ) + 2 := by
          by_contra hc; push Not at hc; nlinarith [h2.2]
        have e1' : (m' j : ℕ) < (m j : ℕ) + 1 := by exact_mod_cast e1
        have e2' : (m j : ℕ) < (m' j : ℕ) + 2 := by exact_mod_cast e2
        have f : (m j : ℕ) = (m' j : ℕ) ∨ (m j : ℕ) = (m' j : ℕ) + 1 := by omega
        rw [hxj]
        rcases f with f | f
        · rw [f]; constructor <;> nlinarith
        · rw [f]; push_cast; constructor <;> nlinarith
      · have e1 : ((m' j : ℕ) : ℝ) < (m j : ℕ) + 2 := by
          by_contra hc; push Not at hc; nlinarith [h2.1]
        have e2 : ((m j : ℕ) : ℝ) < (m' j : ℕ) + 1 := by
          by_contra hc; push Not at hc; nlinarith [h2.2]
        have e1' : (m' j : ℕ) < (m j : ℕ) + 2 := by exact_mod_cast e1
        have e2' : (m j : ℕ) < (m' j : ℕ) + 1 := by exact_mod_cast e2
        have f : (m' j : ℕ) = (m j : ℕ) ∨ (m' j : ℕ) = (m j : ℕ) + 1 := by omega
        rw [hxj]
        rcases f with f | f
        · rw [f]; constructor <;> nlinarith
        · rw [f]; push_cast; constructor <;> nlinarith
  exact ⟨fun j _ => (key j).2, fun j => (key j).1⟩

omit [NeZero N] in
/-- Free directions of a face along which two cells agree are free directions of their common
face. -/
theorem commonFace_eq_none {m m' : CubeCell fun _ : Fin n => N} {j : Fin n} (h : m' j = m j) :
    commonFace _ m m' j = none := by
  simp [commonFace, h]

/-! ### Boundary layers of the unit cube -/

/-- The points of `ℝⁿ` with a coordinate `θ`-close to `{0, 1}`. -/
def cubeLayer (θ : ℝ) : Set (Fin n → ℝ) := {y | ∃ j, y j < θ ∨ 1 - θ < y j}

omit [Fact (0 < L)] [NeZero N] in
theorem measurableSet_cubeLayer (θ : ℝ) : MeasurableSet (cubeLayer (n := n) θ) := by
  have : cubeLayer (n := n) θ = ⋃ j, ((fun y => y j) ⁻¹' Set.Iio θ ∪
      (fun y => y j) ⁻¹' Set.Ioi (1 - θ)) := by
    ext y; simp [cubeLayer]
  rw [this]
  exact MeasurableSet.iUnion fun j => ((measurable_pi_apply j) measurableSet_Iio).union
    ((measurable_pi_apply j) measurableSet_Ioi)

omit [Fact (0 < L)] [NeZero N] in
/-- **The boundary layer of the unit cube is small**: `|[0, 1]ⁿ ∩ layer_θ| ≤ 2 n θ`. -/
theorem volume_real_cubeLayer_le {θ : ℝ} (hθ : 0 ≤ θ) :
    volume.real (closedCube n ∩ cubeLayer θ) ≤ 2 * n * θ := by
  classical
  have hsub : closedCube n ∩ cubeLayer θ ⊆ ⋃ j, (Set.Icc (0 : Fin n → ℝ) (Function.update 1 j θ) ∪
      Set.Icc (Function.update 0 j (1 - θ)) 1) := by
    rintro y ⟨hy, j, hj⟩
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rcases hj with hj | hj
    · refine Or.inl ⟨fun i => (hy i (Set.mem_univ i)).1, fun i => ?_⟩
      by_cases hij : i = j
      · subst hij; simp only [Function.update_self]; exact hj.le
      · simp only [Function.update_of_ne hij, Pi.one_apply]; exact (hy i (Set.mem_univ i)).2
    · refine Or.inr ⟨fun i => ?_, fun i => (hy i (Set.mem_univ i)).2⟩
      by_cases hij : i = j
      · subst hij; simp only [Function.update_self]; exact hj.le
      · simp only [Function.update_of_ne hij, Pi.zero_apply]; exact (hy i (Set.mem_univ i)).1
  have hvol : ∀ j, volume (Set.Icc (0 : Fin n → ℝ) (Function.update 1 j θ) ∪
      Set.Icc (Function.update 0 j (1 - θ)) 1) ≤ ENNReal.ofReal (2 * θ) := fun j => by
    refine (measure_union_le _ _).trans ?_
    rw [Real.volume_Icc_pi, Real.volume_Icc_pi, Finset.prod_eq_single j (fun i _ hij => by
        simp [Function.update_of_ne hij]) (by simp),
      Finset.prod_eq_single j (fun i _ hij => by simp [Function.update_of_ne hij]) (by simp)]
    simp only [Function.update_self, Pi.zero_apply, Pi.one_apply, sub_zero, sub_sub_cancel]
    rw [← ENNReal.ofReal_add hθ hθ]
    exact le_of_eq (by ring_nf)
  have h : volume (closedCube n ∩ cubeLayer θ) ≤ ENNReal.ofReal (2 * n * θ) := by
    refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
    rw [tsum_fintype]
    refine (Finset.sum_le_sum fun j _ => hvol j).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_nsmul,
      nsmul_eq_mul]
    ring_nf
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

omit [Fact (0 < L)] [NeZero N] in
open Classical in
/-- **Integration of a moment-integrand bound** over the unit cube: if `H |F(y)| ≤ c` on the
boundary layer `layer_θ` and `≤ c ε` elsewhere, then `H |∫_{[0,1]ⁿ} F| ≤ c (ε + 2 n θ)`. -/
theorem mul_abs_integral_closedCube_le {F : (Fin n → ℝ) → ℝ}
    (hF : ContinuousOn F (closedCube n)) {H c ε θ : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hθ0 : 0 ≤ θ)
    (hpt : ∀ y ∈ closedCube n, H * |F y| ≤ c * (if y ∈ cubeLayer θ then 1 else ε)) :
    H * |∫ y in closedCube n, F y| ≤ c * (ε + 2 * n * θ) := by
  have hS : MeasurableSet (closedCube n) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hcpt : IsCompact (closedCube n) := isCompact_univ_pi fun _ => isCompact_Icc
  have hfin : volume (closedCube n) ≠ ⊤ := hcpt.measure_lt_top.ne
  have hB := measurableSet_cubeLayer (n := n) θ
  set β : (Fin n → ℝ) → ℝ := fun y => c * ε + c * (cubeLayer θ).indicator 1 y
  have hpt' : ∀ y ∈ closedCube n, H * |F y| ≤ β y := fun y hy => by
    refine (hpt y hy).trans ?_
    by_cases hb : y ∈ cubeLayer θ
    · simp only [hb, ite_true, β, Set.indicator_of_mem hb, Pi.one_apply]
      nlinarith [mul_nonneg hc hε]
    · simp [hb, β]
  have hind : IntegrableOn (fun y => (cubeLayer θ).indicator (1 : (Fin n → ℝ) → ℝ) y)
      (closedCube n) := (integrableOn_const hfin).indicator hB
  have hvol : volume.real (closedCube n) = 1 := by
    rw [Measure.real, show closedCube n = Set.Icc (0 : Fin n → ℝ) 1 from Set.pi_univ_Icc 0 1,
      Real.volume_Icc_pi]
    simp
  have hint : ∫ y in closedCube n, β y =
      c * ε * volume.real (closedCube n) + c * volume.real (closedCube n ∩ cubeLayer θ) := by
    rw [integral_add (integrableOn_const hfin) (hind.const_mul _), setIntegral_const, smul_eq_mul,
      integral_const_mul, integral_indicator_one hB, Measure.real, Measure.real,
      Measure.restrict_apply hB, Set.inter_comm]
    simp only [Measure.real]
    ring
  have hbad := volume_real_cubeLayer_le (n := n) hθ0
  calc H * |∫ y in closedCube n, F y|
      ≤ H * ∫ y in closedCube n, |F y| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hH
    _ = ∫ y in closedCube n, H * |F y| := (integral_const_mul _ _).symm
    _ ≤ ∫ y in closedCube n, β y :=
        setIntegral_mono_on ((hF.abs.integrableOn_compact hcpt).const_mul _)
          ((integrableOn_const hfin).add (hind.const_mul _)) hS hpt'
    _ ≤ c * (ε + 2 * n * θ) := by
        rw [hint, hvol]
        have h2 := mul_le_mul_of_nonneg_left hbad hc
        nlinarith

omit [Fact (0 < L)] [NeZero N] in
/-- The fixed coordinates of the faces of the degrees of freedom are `0` or `1`. -/
theorem dofFace_eq_some {s : Finset (Fin n)} {α : Fin n →₀ ℕ} {j : Fin n} {c : ℝ}
    (h : dofFace (fun _ => none) s α j = some c) : c = 0 ∨ c = 1 := by
  simp only [dofFace, Option.none_or] at h
  split_ifs at h with h1
  cases h
  push Not at h1
  rcases Nat.lt_succ_iff.1 h1.2 |>.eq_or_lt with h2 | h2
  · right; rw [h2]; norm_num
  · left; rw [Nat.lt_one_iff.1 h2]; norm_num


/-- **The cell error of an interpolated field**: on the cell `m`, the field of `ω ∈ Q_b⁻Λᵏ` minus
the cell interpolant of `w` is the cell interpolant of `ω_m - w`. -/
theorem cellField_sub_cellInterp {k : ℕ} (hb : ∀ j, 1 ≤ b j)
    {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)} {m : CubeCell fun _ : Fin n => N}
    (hωm : ω m ∈ cubeFormMinus ℝ b k) {w : FormField n} (hw : Continuous w) :
    cellField L ω m - cellInterp L k hb m w = affinePullback (scalarMat n (N / L)) (cellOffset m)
      (cubeFieldInterp k hb (cellPullback L m (cellField L ω m - w))) := by
  have hc : Continuous (cellPullback L m (cellField L ω m)) :=
    continuous_affinePullback _ _ (contDiff_cellField ω m (r := 0)).continuous
  rw [cellPullback, affinePullback_sub, ← cellPullback, ← cellPullback,
    cubeFieldInterp_sub hb hc.continuousOn
      (show Continuous (cellPullback L m w) from continuous_affinePullback _ _ hw).continuousOn,
    cellPullback_cellField, cubeFieldInterp_evalForm hb hωm, affinePullback_sub]
  rfl

/-! ### Stability of the cell interpolants -/

variable (b) in
/-- **Stability of the cell interpolants in `C⁰`**, uniformly in the side `L`, the number of cells
`N` and the cell: `sup_m ‖Π_m w‖ ≤ C sup_m ‖w‖` for `k`-form fields. -/
theorem exists_norm_cellInterp_le (k : ℕ) (hb : ∀ j, 1 ≤ b j) :
    ∃ C, 0 ≤ C ∧ ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) [NeZero N] (m : CubeCell fun _ : Fin n => N)
      (w : FormField n), (∀ x, IsDeg k (w x)) → ∀ B : ℝ, (∀ z ∈ closedCell L m, ‖w z‖ ≤ B) →
      ∀ y ∈ closedCell L m, ‖cellInterp L k hb m w y‖ ≤ C * B := by
  obtain ⟨C, hC⟩ := exists_norm_cubeFieldInterp_le (k := k) hb
  refine ⟨max C 0, le_max_right _ _, fun L _ N _ m w hk B hB y hy => ?_⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hh : 0 < L / N := div_pos Fact.out hN0
  have hNL : 0 < (N : ℝ) / L := div_pos hN0 Fact.out
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y hy)
  have hloc : ∀ z ∈ closedCube n, ‖cellPullback L m w z‖ ≤ (L / N) ^ k * B := fun z hz => by
    rw [cellPullback, affinePullback_scalarMat _ _ hk, norm_smul,
      Real.norm_of_nonneg (pow_pos hh k).le]
    refine mul_le_mul_of_nonneg_left (hB _ ?_) (pow_pos hh k).le
    have := cellMap_mem_closedCell (L := L) m hz
    rwa [affine_scalarMat] at this
  have hval := hC _ _ hloc _ (affine_cellOffset_mem_closedCube hy)
  rw [cellInterp, affinePullback_apply, pullback_scalarMat _ (isDeg_cubeFieldInterp hb _ _),
    norm_smul, Real.norm_of_nonneg (pow_pos hNL k).le]
  have e : ((N : ℝ) / L) ^ k * (L / N) ^ k = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm (N : ℝ) L, div_self (mul_pos (Fact.out : 0 < L)
      (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N)))).ne', one_pow]
  calc ((N : ℝ) / L) ^ k * ‖cubeFieldInterp k hb (cellPullback L m w)
        (affine (scalarMat n (N / L)) (cellOffset m) y)‖
      ≤ ((N : ℝ) / L) ^ k * (C * ((L / N) ^ k * B)) :=
        mul_le_mul_of_nonneg_left hval (pow_pos hNL k).le
    _ ≤ ((N : ℝ) / L) ^ k * (max C 0 * ((L / N) ^ k * B)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (mul_nonneg (pow_pos hh k).le hB0)) (pow_pos hNL k).le
    _ = max C 0 * B := by
        rw [show ((N : ℝ) / L) ^ k * (max C 0 * ((L / N) ^ k * B)) =
          (((N : ℝ) / L) ^ k * (L / N) ^ k) * (max C 0 * B) by ring, e, one_mul]

end Feec.FiniteElement.Cube

/-! ### The cubical complexes of the cube `(0, ½)ⁿ` -/

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.FiniteElement.Cube Feec.HilbertComplex
  ExteriorFibre Koszul

variable {n : ℕ}

instance fact_half_pos : Fact (0 < (1 / 2 : ℝ)) := ⟨by norm_num⟩

/-- The Freudenthal refinement of the cubical mesh of `(0, ½)ⁿ` with `N + 1` cells per direction
is the mesh of the simplicial families. -/
theorem cubeRefinement_eq_mesh (N : ℕ) : cubeRefinement n (1 / 2) (N + 1) = mesh n N := rfl

theorem closedCell_subset_closure (N : ℕ) (m : CubeCell fun _ : Fin n => N + 1) :
    closedCell (1 / 2) m ⊆ closure (cubeDomain n) := by
  rw [closure_cubeDomain]
  exact closedCell_subset_closedBox m

variable [NeZero n] {b : Fin n → ℕ}

variable (n) in
/-- **The cubical complex `Q_b⁻Λ`** on the cubical mesh of `Q = (0, ½)ⁿ` with `N + 1` cells per
direction (`Q_r⁻Λᵏ` for `b = fun _ => r`), as a subcomplex of `HΛ(Q)`. -/
def qMinus (b : Fin n → ℕ) (N : ℕ) : (complex n).Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (cubeSubcomplex n (1 / 2) (N + 1) b)

instance (b : Fin n → ℕ) (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((qMinus n b N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq (mesh_domain n N) _ _
    (cubeSubcomplex n (1 / 2) (N + 1) b) (hS := fun k =>
      inferInstanceAs (FiniteDimensional ℝ (cubeV n (1 / 2) (N + 1) b k))) k

/-- **The smoothed canonical interpolant** `Q_N = Π_h R` of the cubical complex, for
maximal-family smoothing parameters centred at the centre of the cube. -/
def qMinusSmoothed (hb : ∀ j, 1 ≤ b j) (N : ℕ) (p : SmoothingParam (Fin n → ℝ))
    (hp : p.IsMaximal (center n) (1 / 4)) : (qMinus n b N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEq (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    (cubeSmoothedCommutingMap n (1 / 2) (N + 1) hb p (starBall_mesh n N) hp)

variable (b) in
/-- **The estimates of the smoothed interpolants of the cubical complex** ([AFW2010], §5.5): for
maximal-family parameters `p N`, uniform `L²` bounds of `Q_N` and `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ`,
normalized by `½ ≤ C` (the analogue of `FEM.SmoothingEstimates`). -/
structure QMinusSmoothingEstimates (hb : ∀ j, 1 ≤ b j) (p : ℕ → SmoothingParam (Fin n → ℝ))
    (C : ℝ) : Prop where
  isMaximal : ∀ N, (p N).IsMaximal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(qMinusSmoothed hb N (p N) (isMaximal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (qMinus n b N).V i,
    ‖v - (qMinusSmoothed hb N (p N) (isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

namespace QMinus

/-! ### The uniform `L²` bound -/

variable {γ : ℝ}

omit [NeZero n] in
/-- **The local `L²` bound of `Q_N = Π_h R`** on a simplex of the refinement:
`‖Q_N x‖²_{L²(T)} ≤ 2ⁿ (C 2ᵏ)² (32/γ)ⁿ m_T(x)`. -/
theorem sum_integral_sq_smoothedInterp_le (hb : ∀ j, 1 ≤ b j) {k : ℕ} {C : ℝ}
    (hC : ∀ (N : ℕ) (m : CubeCell fun _ : Fin n => N + 1) (w : FormField n),
      (∀ x, IsDeg k (w x)) → ∀ B : ℝ, (∀ z ∈ closedCell (1 / 2) m, ‖w z‖ ≤ B) →
      ∀ y ∈ closedCell (1 / 2) m, ‖cellInterp (1 / 2) k hb m w y‖ ≤ C * B)
    {N : ℕ} {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p) (hγ1 : γ ≤ 1)
    (x : L2F ℝ (mesh n N).domain (formIdx n k)) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (cellField (1 / 2) (cubeFieldGlobalInterp (1 / 2) k hb
        (smoothForm p (isOpen_mesh_domain n N).measurableSet k x))
          (simplexCell (N := N + 1) (1 / 2) T) y s.1) ^ 2 ≤
      2 ^ n * (C * 2 ^ k) ^ 2 * (32 / γ) ^ n * locMass x T := by
  have hh := hN_pos N
  have hγ0 : 0 < γ := hp.gamma_pos
  have hL := locMass_nonneg x T
  set m := simplexCell (N := N + 1) (1 / 2) T
  have hTm : T.closedInterior ⊆ closedCell (1 / 2) m :=
    simplexCell_closedInterior_subset (L := 1 / 2) (N := N + 1) hT
  set B := 2 ^ k * √((32 / (γ * hN N)) ^ n * locMass x T)
  have hB : ∀ z ∈ closedCell (1 / 2) m,
      ‖(smoothForm p (isOpen_mesh_domain n N).measurableSet k x : FormField n) z‖ ≤ B :=
    fun z hz => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => by
      rw [Real.norm_eq_abs]
      exact hp.abs_smoothForm_le_locMass_of_near hγ1 x T (closedCell_subset_closure N m hz)
        (vertexSet_subset_closedInterior T (points_mem_vertexSet T 0))
        (dist_le_of_mem_closedCell hz
          (hTm (vertexSet_subset_closedInterior T (points_mem_vertexSet T 0)))) s
  have hzb : ∀ y ∈ T.closedInterior, ∀ s, |cellField (1 / 2) (cubeFieldGlobalInterp (1 / 2) k hb
      (smoothForm p (isOpen_mesh_domain n N).measurableSet k x)) m y s| ≤ C * B := fun y hy s => by
    rw [cellField_cubeFieldGlobalInterp]
    refine (norm_le_pi_norm (cellInterp (1 / 2) k hb m _ y) s).trans ?_
    exact hC N m _ (fun z => isDeg_smoothForm _ _ k x z) B hB y (hTm hy)
  refine (sum_integral_sq_le_of_abs_le hT (contDiff_cellField _ _ (r := 0)).continuous hzb).trans
    (le_of_eq ?_)
  have hr2 : √((32 / (γ * hN N)) ^ n * locMass x T) ^ 2 = (32 / (γ * hN N)) ^ n * locMass x T :=
    Real.sq_sqrt (by positivity)
  rw [show (32 / γ) ^ n = hN N ^ n * (32 / (γ * hN N)) ^ n by rw [← mul_pow]; congr 1; field_simp]
  simp only [B]
  linear_combination (2 ^ n * hN N ^ n * (C * 2 ^ k) ^ 2) * hr2

omit [NeZero n] in
/-- **The uniform `L²` bound of the smoothed interpolants** `Q_N = Π_h R_N` of the cubical
complexes, for any admissible parameters (`IsAdm`): `‖Q_N x‖ ≤ C ‖x‖` for all `N`, all degrees and
all `x`, with `C` depending only on `n`, `b` and `γ`. -/
theorem exists_norm_smoothedInterp_le (hb : ∀ j, 1 ≤ b j) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ (N k : ℕ) (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
      ∀ x : L2F ℝ (mesh n N).domain (formIdx n k),
        ‖cubeSmoothedInterp n (1 / 2) (N + 1) hb p k x‖ ≤ C * ‖x‖ := by
  choose C hC0 hC using fun k : ℕ => exists_norm_cellInterp_le b k hb
  have hK : ∀ k, 0 ≤ 2 ^ n * (C k * 2 ^ k) ^ 2 * (32 / γ) ^ n *
      ((6 ^ n * n.factorial : ℕ) : ℝ) := fun k => by positivity
  refine ⟨_, Real.sqrt_nonneg _, fun N k p hp x => norm_le_sqrt_sum_of_sq_le hK fun _ => ?_⟩
  rw [show cubeSmoothedInterp n (1 / 2) (N + 1) hb p k x = _ from
    cubeSmoothedInterp_natCast hb p k x]
  refine (norm_sq_cubeGlue_le _ (fun T => 2 ^ n * (C k * 2 ^ k) ^ 2 * (32 / γ) ^ n *
    locMass x T) fun T hT => sum_integral_sq_smoothedInterp_le hb
      (fun N m w hw B hB y hy => hC k (1 / 2) (N + 1) m w hw B hB y hy) hp hγ1 x hT).trans ?_
  rw [← Finset.mul_sum]
  calc 2 ^ n * (C k * 2 ^ k) ^ 2 * (32 / γ) ^ n * ∑ T ∈ (mesh n N).simplices, locMass x T
      ≤ 2 ^ n * (C k * 2 ^ k) ^ 2 * (32 / γ) ^ n * ((6 ^ n * n.factorial : ℕ) * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_locMass_le N x) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

/-! ### The closeness estimate on `Vₕ` -/

/-- The inverse estimates of the cells of the mesh of `Q` with `N + 1` cells per direction, with
the constant `A` (`exists_cell_inverse_bound`). -/
def CellInvBound (b : Fin n → ℕ) (k : ℕ) (A : ℝ) : Prop :=
  ∀ (N : ℕ) (ω : CubeCell (fun _ : Fin n => N + 1) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N + 1), ω m ∈ cubeFormMinus ℝ b k →
    (∀ x ∈ closedCell (1 / 2) m, √(hN N) ^ n * ‖cellField (1 / 2) ω m x‖ ≤
      A * √(formL2Sq (closedCell (1 / 2) m) (cellField (1 / 2) ω m))) ∧
    (∀ x ∈ closedCell (1 / 2) m, ∀ x' ∈ closedCell (1 / 2) m,
      √(hN N) ^ n * hN N * ‖cellField (1 / 2) ω m x - cellField (1 / 2) ω m x'‖ ≤
        A * ‖x - x'‖ * √(formL2Sq (closedCell (1 / 2) m) (cellField (1 / 2) ω m)))

omit [NeZero n] in
theorem exists_cellInvBound (b : Fin n → ℕ) (k : ℕ) : ∃ A, 0 ≤ A ∧ CellInvBound b k A := by
  obtain ⟨A, hA0, hA⟩ := exists_cell_inverse_bound (n := n) b k
  exact ⟨A, hA0, fun N ω m hω => hA (1 / 2) (N + 1) ω m hω⟩

/-- The test form of the degree of freedom `i` of `Q_b⁻Λᵏ`. -/
abbrev dofTestForm {k : ℕ} (i : CubeDofIdx b k) : PolyForm ℝ (Fin n) :=
  Pi.single (freeSet (dofFace (fun _ => none) i.1.1 i.2.1) \ i.1.1)
    (MvPolynomial.monomial (dofTest i.1.1 i.2.1) 1)

omit [NeZero n] in
theorem exists_momentCoeff_bound (b : Fin n → ℕ) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (i : CubeDofIdx b k), ∀ y ∈ closedCube n,
      ∑ s, |momentCoeff (dofFace (fun _ => none) i.1.1 i.2.1) (dofTestForm i) y s| ≤ C := by
  choose C hC0 hC using fun i : CubeDofIdx b k =>
    exists_sum_abs_momentCoeff_le (dofFace (fun _ => none) i.1.1 i.2.1) (dofTestForm i)
  exact ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun i y hy => (hC i y hy).trans
    (Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_univ i))⟩

omit [NeZero n] in
theorem continuous_momentCoeff (g : Fin n → Option ℝ) (η : PolyForm ℝ (Fin n))
    (s : Finset (Fin n)) : Continuous fun y => momentCoeff g η y s := by
  unfold momentCoeff
  split_ifs
  · exact continuous_const.mul ((continuous_apply _).comp (contDiff_evalForm η (r := 0)).continuous)
  · exact continuous_const

omit [NeZero n] in
open Classical in
/-- **The degrees of freedom of `v - Q_N v`** (`v ∈ Vₕ`, maximal family): on the cell `m` of a
simplex `T`, `h^{n/2} |ℓᵢ(F_m^*(v_m - R v))| ≤ hᵏ C A m_T(v)^{1/2} 2^{k+1} ((k + 1) γ + n γ)`.
On a face, the moment is the integral of `Σₛ (v_m - R v)(x)ₛ cₛ` over the unit cube
(`fieldMoment_eq_integral`), whose integrand is `O(γ)` at points with `γ/2`-interior coordinates
(every sampled cell contains the point and has the same tangential components there,
`mem_closedCell_of_near_face`, `cellField_apply_eq_of_free`) and `O(1)` on the boundary layer,
of measure `≤ n γ` (`mul_abs_integral_closedCube_le`), by the pointwise estimate
`sqrt_mul_abs_sum_sub_smoothForm_le` of the simplicial families. -/
theorem sqrt_mul_abs_fieldDof_sub_le {k : ℕ} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : CellInvBound b k A) {Cc : ℝ}
    (hCc : ∀ (i : CubeDofIdx b k), ∀ y ∈ closedCube n,
      ∑ s, |momentCoeff (dofFace (fun _ => none) i.1.1 i.2.1) (dofTestForm i) y s| ≤ Cc)
    {γ : ℝ} {N : ℕ} {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p) (hγ1 : γ ≤ 1)
    (hin : ∀ x ∈ closure (cubeDomain n), ∀ t,
      dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut → t ∈ (mesh n N).domain)
    {ω : CubeCell (fun _ : Fin n => N + 1) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeGlobalSpace (fun _ : Fin n => N + 1) b k)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) (i : CubeDofIdx b k) :
    √(hN N) ^ n * |fieldDof i (cellPullback (1 / 2) (simplexCell (N := N + 1) (1 / 2) T)
      (cellField (1 / 2) ω (simplexCell (1 / 2) T) -
        (smoothForm p (isOpen_mesh_domain n N).measurableSet k
          (cubeGlue n (1 / 2) (N + 1) k ω) : FormField n)))| ≤
      hN N ^ k * (Cc * A * √(locMass (cubeGlue n (1 / 2) (N + 1) k ω) T) * 2 ^ (k + 1) *
        ((k + 1) * γ + 2 * n * (γ / 2))) := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hγ0 : 0 < γ := hp.gamma_pos
  set m := simplexCell (N := N + 1) (1 / 2) T
  set v := cubeGlue n (1 / 2) (N + 1) k ω
  set R : FormField n := (smoothForm p (isOpen_mesh_domain n N).measurableSet k v : FormField n)
  set u := cellField (1 / 2) ω m
  set g := dofFace (fun _ => none) i.1.1 i.2.1
  set η := dofTestForm i
  set t₀ : Fin n → ℝ := fun j => 1 / 2 / ((N + 1 : ℕ) : ℝ) * ((m j : ℕ) : ℝ)
  set X : (Fin n → ℝ) → Fin n → ℝ := fun y => h • planePoint g y + t₀
  set Lm := locMass v T
  have hω' := mem_cubeGlobalSpace.1 hω
  have hk : ∀ m, IsDeg k (ω m) := fun m => (hω'.2 m).1
  have hTm : T.closedInterior ⊆ closedCell (1 / 2) m :=
    simplexCell_closedInterior_subset (L := 1 / 2) (N := N + 1) hT
  set z₀ := T.points 0
  have hz₀T : z₀ ∈ T.closedInterior := vertexSet_subset_closedInterior T (points_mem_vertexSet T 0)
  have hz₀m : z₀ ∈ closedCell (1 / 2) m := hTm hz₀T
  have hmass : ∀ m', closedCell (1 / 2) m' ⊆ Metric.cthickening (2 * h) T.closedInterior →
      formL2Sq (closedCell (1 / 2) m') (cellField (1 / 2) ω m') ≤ Lm :=
    fun m' hsub => formL2Sq_cellField_le hk m' hsub
  have hLm : 0 ≤ Lm := locMass_nonneg v T
  have hH : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  -- the degree of freedom as an integral over the unit cube
  set F : (Fin n → ℝ) → ℝ := fun y => ∑ s, (u (X y) s - R (X y) s) * momentCoeff g η y s
  have hdegu : ∀ x, IsDeg k ((u - R) x) := fun x s hs => by
    change u x s - R x s = 0
    rw [show u x s = 0 from isDeg_cellField (hk m) x s hs,
      show R x s = 0 from isDeg_smoothForm _ _ k v x s hs, sub_zero]
  have hdof : fieldDof i (cellPullback (1 / 2) m (u - R)) = h ^ k * ∫ y in closedCube n, F y := by
    rw [fieldDof, fieldDofAt, fieldMoment_eq_integral, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [cellPullback, affinePullback_scalarMat _ _ hdegu, F, X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mul_assoc]
    rfl
  have hFc : Continuous F := continuous_finsetSum _ fun s _ =>
    (((continuous_apply s).comp ((contDiff_cellField ω m (r := 0)).continuous.comp
      (((continuous_planePoint g).const_smul h).add continuous_const))).sub
      ((continuous_apply s).comp ((mem_c1Forms.1 (smoothForm p _ k v).2).continuous.comp
      (((continuous_planePoint g).const_smul h).add continuous_const)))).mul
      (continuous_momentCoeff g η s)
  -- the pointwise estimate
  have hpt : ∀ y ∈ closedCube n, √h ^ n * |F y| ≤
      (Cc * A * √Lm * 2 ^ (k + 1)) * (if y ∈ cubeLayer (γ / 2) then 1 else (k + 1) * γ) := by
    intro y hy
    set x := X y
    have hpp := planePoint_mem_closedCube (dofFace_mem_Icc i.1.1 i.2.1) hy
    have hxm : x ∈ closedCell (1 / 2) m := by
      have := cellMap_mem_closedCell (L := 1 / 2) m hpp
      rwa [affine_scalarMat] at this
    have hxc : x ∈ closure (cubeDomain n) := closedCell_subset_closure N m hxm
    obtain ⟨hA1, hA2⟩ := hA N ω m (hω'.2 m)
    have hmm : formL2Sq (closedCell (1 / 2) m) u ≤ Lm :=
      hmass m (closedCell_subset_cthickening hxm hxm (by rw [dist_self]; exact hh) hz₀m hz₀T)
    have hdef : |1 - p.factor ^ k| ≤ k * 2 ^ k * γ :=
      (hp.abs_one_sub_pow_le hγ1 k).trans (mul_le_mul_of_nonneg_left
        (by nlinarith [hN_le N]) (by positivity))
    have hmain := sqrt_mul_abs_sum_sub_smoothForm_le (isOpen_mesh_domain n N).measurableSet p v x
      (u x) (momentCoeff g η y) (A := A) (L := Lm) (ε := γ) (y ∈ cubeLayer (γ / 2)) hH hA0
      hγ0.le (hp.pow_factor_le hγ1 k) hdef
      (fun s => (mul_le_mul_of_nonneg_left (norm_le_pi_norm (u x) s) hH.le).trans
        ((hA1 x hxm).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmm) hA0)))
      (by
        filter_upwards [ae_extField_cubeGlue_eq (L := 1 / 2) (N := N + 1) hk] with t ht hdist htΩ
        obtain ⟨T', hT', htT', hval⟩ := ht htΩ
        set m' := simplexCell (N := N + 1) (1 / 2) T'
        have htm' : t ∈ closedCell (1 / 2) m' :=
          simplexCell_closedInterior_subset (L := 1 / 2) (N := N + 1) hT' (interior_subset htT')
        have hxt : ‖x - t‖ < γ * h / 2 := hp.norm_sub_lt hxc hdist
        have hxt' : dist x t < h := by rw [dist_eq_norm]; nlinarith
        have hm' := hmass m' (closedCell_subset_cthickening hxm htm' hxt' hz₀m hz₀T)
        obtain ⟨hB1, hB2⟩ := hA N ω m' (hω'.2 m')
        refine ⟨cellField (1 / 2) ω m', hval, fun s =>
          (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ s) hH.le).trans ((hB1 t htm').trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm') hA0)), fun hgood => ?_⟩
        have hy' : ∀ j, γ / 2 ≤ y j ∧ y j ≤ 1 - γ / 2 := fun j => by
          simp only [cubeLayer, Set.mem_ofPred_eq, not_exists, not_or, not_lt] at hgood
          exact ⟨hgood j |>.1, hgood j |>.2⟩
        obtain ⟨hxm', hfree⟩ := mem_closedCell_of_near_face (L := 1 / 2)
          (fun j c hc => dofFace_eq_some hc) (by linarith) hy' htm'
          (by rw [add_comm]; change dist x t < γ / 2 * h; rw [dist_eq_norm]; linarith)
        replace hxm' : x ∈ closedCell (1 / 2) m' := by
          convert hxm' using 1; exact add_comm _ _
        refine ⟨Finset.sum_congr rfl fun s _ => ?_,
          fun s => (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ s) hH.le).trans
            ((hB1 x hxm').trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm') hA0)),
          fun s => ?_⟩
        · by_cases hs : s ⊆ freeSet g
          · exact congrArg (· * momentCoeff g η y s) (cellField_apply_eq_of_free hω'.1 hxm hxm'
              fun j hj => commonFace_eq_none
                (hfree j (Option.isNone_iff_eq_none.1 (mem_freeSet.1 (hs hj)))))
          · rw [momentCoeff_eq_zero η y hs, mul_zero, mul_zero]
        · have hlip := hB2 x hxm' t htm'
          have hd : |cellField (1 / 2) ω m' x s - cellField (1 / 2) ω m' t s| ≤
              ‖cellField (1 / 2) ω m' x - cellField (1 / 2) ω m' t‖ :=
            norm_le_pi_norm (cellField (1 / 2) ω m' x - cellField (1 / 2) ω m' t) s
          have hF0 := Real.sqrt_le_sqrt hm'
          have hF1 := Real.sqrt_nonneg (formL2Sq (closedCell (1 / 2) m') (cellField (1 / 2) ω m'))
          have hnx := norm_nonneg (x - t)
          have key : √h ^ n * h * |cellField (1 / 2) ω m' x s - cellField (1 / 2) ω m' t s| ≤
              h * (γ * (A * √Lm)) := by
            calc _ ≤ √h ^ n * h * ‖cellField (1 / 2) ω m' x - cellField (1 / 2) ω m' t‖ :=
                  mul_le_mul_of_nonneg_left hd (by positivity)
              _ ≤ A * ‖x - t‖ * √(formL2Sq (closedCell (1 / 2) m') (cellField (1 / 2) ω m')) :=
                  hlip
              _ ≤ A * (γ * h / 2) * √Lm := by gcongr
              _ ≤ h * (γ * (A * √Lm)) := by
                  have := mul_nonneg (mul_nonneg (mul_nonneg hA0 hγ0.le) hh.le)
                    (Real.sqrt_nonneg Lm)
                  nlinarith
          have : √h ^ n * h * |cellField (1 / 2) ω m' x s - cellField (1 / 2) ω m' t s| =
              h * (√h ^ n * |cellField (1 / 2) ω m' x s - cellField (1 / 2) ω m' t s|) := by ring
          rw [this] at key
          exact le_of_mul_le_mul_left key hh)
      (fun _ t hdist htΩ => absurd (hin x hxc t hdist) htΩ)
    refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> positivity))
    have := hCc i y hy
    have h2 : (0 : ℝ) ≤ 2 ^ (k + 1) := by positivity
    have h3 := Real.sqrt_nonneg Lm
    gcongr
  have hCc0 : 0 ≤ Cc := (Finset.sum_nonneg fun s _ => abs_nonneg _).trans
    (hCc i 0 fun _ _ => ⟨le_rfl, zero_le_one⟩)
  have hint := mul_abs_integral_closedCube_le hFc.continuousOn hH.le
    (by have := Real.sqrt_nonneg Lm; positivity) (by positivity) (by positivity) hpt
  rw [hdof, abs_mul, abs_of_nonneg (pow_nonneg hh.le k)]
  calc √h ^ n * (h ^ k * |∫ y in closedCube n, F y|)
        = h ^ k * (√h ^ n * |∫ y in closedCube n, F y|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (pow_nonneg hh.le k)

omit [NeZero n] in
/-- **The local closeness estimate** on a simplex `T` of the refinement:
`‖v - Q_N v‖²_{L²(T)} ≤ 2ⁿ (A_Π #DOF K_T)²` with `K_T` the DOF bound of
`sqrt_mul_abs_fieldDof_sub_le`. -/
theorem sum_integral_sq_sub_smoothedInterp_le (hb : ∀ j, 1 ≤ b j) {k : ℕ} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : CellInvBound b k A) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ (i : CubeDofIdx b k), ∀ y ∈ closedCube n,
      ∑ s, |momentCoeff (dofFace (fun _ => none) i.1.1 i.2.1) (dofTestForm i) y s| ≤ Cc)
    {AI : ℝ} (hAI0 : 0 ≤ AI) (hAI : ∀ (w : FormField n), ∀ x ∈ closedCube n,
      ‖cubeFieldInterp k hb w x‖ ≤ AI * ∑ i : CubeDofIdx b k, |fieldDof i w|)
    {γ : ℝ} {N : ℕ} {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p) (hγ1 : γ ≤ 1)
    (hin : ∀ x ∈ closure (cubeDomain n), ∀ t,
      dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut → t ∈ (mesh n N).domain)
    {ω : CubeCell (fun _ : Fin n => N + 1) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeGlobalSpace (fun _ : Fin n => N + 1) b k)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (cellField (1 / 2) (ω - cubeFieldGlobalInterp (1 / 2) k hb
        (smoothForm p (isOpen_mesh_domain n N).measurableSet k
          (cubeGlue n (1 / 2) (N + 1) k ω))) (simplexCell (N := N + 1) (1 / 2) T) y s.1) ^ 2 ≤
      2 ^ n * (AI * Fintype.card (CubeDofIdx b k) * (Cc * A * 2 ^ (k + 1) * ((k + 1) + n))) ^ 2 *
        γ ^ 2 * locMass (cubeGlue n (1 / 2) (N + 1) k ω) T := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hγ0 : 0 < γ := hp.gamma_pos
  set m := simplexCell (N := N + 1) (1 / 2) T
  set v := cubeGlue n (1 / 2) (N + 1) k ω
  set R : FormField n := (smoothForm p (isOpen_mesh_domain n N).measurableSet k v : FormField n)
  set Lm := locMass v T
  have hLm : 0 ≤ Lm := locMass_nonneg v T
  have hω' := mem_cubeGlobalSpace.1 hω
  have hTm : T.closedInterior ⊆ closedCell (1 / 2) m :=
    simplexCell_closedInterior_subset (L := 1 / 2) (N := N + 1) hT
  have hH : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  set K := Cc * A * √Lm * 2 ^ (k + 1) * ((k + 1) * γ + 2 * n * (γ / 2))
  have hK : 0 ≤ K := by have := Real.sqrt_nonneg Lm; positivity
  have hdof := fun i => sqrt_mul_abs_fieldDof_sub_le hA0 hA hCc hp hγ1 hin hω hT i
  have hzb : ∀ y ∈ T.closedInterior, ∀ s,
      |cellField (1 / 2) (ω - cubeFieldGlobalInterp (1 / 2) k hb R) m y s| ≤
        AI * Fintype.card (CubeDofIdx b k) * K / √h ^ n := fun y hy s => by
    have e := cellField_sub_cellInterp (L := 1 / 2) (N := N + 1) (k := k) (m := m) hb (hω'.2 m)
      (w := R)
      (mem_c1Forms.1 (smoothForm p _ k v).2).continuous
    rw [cellField_sub, cellField_cubeFieldGlobalInterp, e]
    refine (norm_le_pi_norm (affinePullback (scalarMat n _) (cellOffset m)
      (cubeFieldInterp k hb (cellPullback (1 / 2) m (cellField (1 / 2) ω m - R))) y) s).trans ?_
    rw [affinePullback_apply, pullback_scalarMat _ (isDeg_cubeFieldInterp hb _ _), norm_smul,
      Real.norm_of_nonneg (by positivity)]
    have hy' := affine_cellOffset_mem_closedCube (hTm hy)
    refine (mul_le_mul_of_nonneg_left (hAI _ _ hy') (by positivity)).trans ?_
    have hsum : ∑ i : CubeDofIdx b k,
        |fieldDof i (cellPullback (1 / 2) m (cellField (1 / 2) ω m - R))| ≤
        Fintype.card (CubeDofIdx b k) * (h ^ k * K / √h ^ n) := by
      refine (Finset.sum_le_sum fun i _ => ?_).trans (le_of_eq (by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))
      rw [le_div_iff₀ hH, mul_comm]
      exact hdof i
    have e : ((((N + 1 : ℕ) : ℝ) / (1 / 2)) * h) = 1 := by
      simp only [h, hN]; field_simp
    calc (((N + 1 : ℕ) : ℝ) / (1 / 2)) ^ k * (AI * ∑ i : CubeDofIdx b k,
          |fieldDof i (cellPullback (1 / 2) m (cellField (1 / 2) ω m - R))|)
        ≤ (((N + 1 : ℕ) : ℝ) / (1 / 2)) ^ k * (AI * (Fintype.card (CubeDofIdx b k) *
          (h ^ k * K / √h ^ n))) := by gcongr
      _ = ((((N + 1 : ℕ) : ℝ) / (1 / 2)) * h) ^ k * (AI * Fintype.card (CubeDofIdx b k) * K /
          √h ^ n) := by ring
      _ = _ := by rw [e, one_pow, one_mul]
  refine (sum_integral_sq_le_of_abs_le hT (contDiff_cellField _ _ (r := 0)).continuous hzb).trans
    (le_of_eq ?_)
  have hsq : (√h ^ n) ^ 2 = h ^ n := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  have hK' : K = Cc * A * 2 ^ (k + 1) * ((k + 1) + n) * γ * √Lm := by simp only [K]; ring
  have e : h ^ n * (AI * Fintype.card (CubeDofIdx b k) * K / √h ^ n) ^ 2 =
      (AI * Fintype.card (CubeDofIdx b k) * K) ^ 2 := by
    rw [div_pow, hsq]; field_simp
  rw [show hN N = h from rfl, e, hK', show (AI * (Fintype.card (CubeDofIdx b k) : ℝ) *
      (Cc * A * 2 ^ (k + 1) * ((k + 1) + n) * γ * √Lm)) ^ 2 =
      (AI * Fintype.card (CubeDofIdx b k) * (Cc * A * 2 ^ (k + 1) * ((k + 1) + n))) ^ 2 *
        γ ^ 2 * √Lm ^ 2 by ring, Real.sq_sqrt hLm]
  ring

omit [NeZero n] in
variable (b) in
/-- The constant of the closeness estimate in degree `k`: `‖v - Q_N v‖² ≤ K_k γ² ‖v‖²` on
`Vₕᵏ` for all `N` and all admissible parameters of the maximal family (the local estimates
`sum_integral_sq_sub_smoothedInterp_le` summed with the bounded overlap `sum_locMass_le`). -/
theorem exists_closeConst (k : ℕ) (hb : ∀ j, 1 ≤ b j) :
    ∃ K, 0 ≤ K ∧ ∀ {γ : ℝ} {N : ℕ} {p : SmoothingParam (Fin n → ℝ)}, IsAdm γ N p → γ ≤ 1 →
      (∀ x ∈ closure (cubeDomain n), ∀ t,
        dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut → t ∈ (mesh n N).domain) →
      ∀ v ∈ cubeV n (1 / 2) (N + 1) b k,
        ‖v - cubeSmoothedInterp n (1 / 2) (N + 1) hb p k v‖ ^ 2 ≤ K * γ ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := exists_cellInvBound (n := n) b k
  obtain ⟨Cc, hCc0, hCc⟩ := exists_momentCoeff_bound (n := n) b k
  obtain ⟨AI, hAI0, hAI⟩ := exists_norm_cubeFieldInterp_le_sum_dof (n := n) (k := k) hb
  set K₀ := 2 ^ n *
    (AI * Fintype.card (CubeDofIdx b k) * (Cc * A * 2 ^ (k + 1) * ((k + 1) + n))) ^ 2
  refine ⟨K₀ * (6 ^ n * n.factorial : ℕ), by positivity, fun {γ N p} hp hγ1 hin v hv => ?_⟩
  obtain ⟨⟨ω, hω⟩, rfl⟩ := hv
  change ‖cubeGlue n (1 / 2) (N + 1) k ω - cubeGlue n (1 / 2) (N + 1) k
    (cubeFieldGlobalInterp (1 / 2) k hb (smoothForm p (isOpen_mesh_domain n N).measurableSet k
      (cubeGlue n (1 / 2) (N + 1) k ω)))‖ ^ 2 ≤ _
  rw [← map_sub]
  refine (norm_sq_cubeGlue_le _ (fun T => K₀ * γ ^ 2 * locMass (cubeGlue n (1 / 2) (N + 1) k ω) T)
    fun T hT => sum_integral_sq_sub_smoothedInterp_le hb hA0 hA hCc0 hCc hAI0 hAI hp hγ1 hin hω
      hT).trans ?_
  rw [← Finset.mul_sum]
  calc K₀ * γ ^ 2 * ∑ T ∈ (mesh n N).simplices, locMass (cubeGlue n (1 / 2) (N + 1) k ω) T
      ≤ K₀ * γ ^ 2 * ((6 ^ n * n.factorial : ℕ) * ‖cubeGlue n (1 / 2) (N + 1) k ω‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_locMass_le N _) (by positivity)
    _ = _ := by simp only [LinearMap.comp_apply, Submodule.subtype_apply]; ring

end QMinus

open QMinus in
/-- **The smoothed-projection estimates for the cubical complexes** ([AFW2010], §5.5;
[ChristiansenWinther2008]): there is `γ₀ > 0` such that for every `γ ∈ (0, γ₀]` the
maximal-family parameters `pMax γ` give uniformly `L²`-bounded smoothed interpolants with
`‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ`, for all `N`. -/
theorem qMinusSmoothingEstimates_pMax (hb : ∀ j, 1 ≤ b j) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      ∃ C, QMinusSmoothingEstimates b hb (pMax γ hγ hγ1) C := by
  choose K hK0 hK using fun k : ℕ => exists_closeConst b k hb
  set S := ∑ k ∈ Finset.range (n + 1), K k
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hK0 k
  refine ⟨1 / (2 * (√S + 1)), by positivity, ?_, fun γ hγ hγ1 hγγ₀ => ?_⟩
  · rw [div_le_one (by positivity)]; nlinarith [Real.sqrt_nonneg S]
  obtain ⟨C, hC0, hbound⟩ := QMinus.exists_norm_smoothedInterp_le hb hγ hγ1
  have hγS : γ * √S ≤ 1 / 2 := by
    have h1 : γ * (2 * (√S + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hγγ₀; linarith
    nlinarith [Real.sqrt_nonneg S]
  refine ⟨max C (1 / 2), ?_⟩
  have h0 : ∀ (N k : ℕ) (y : L2F ℝ (mesh n N).domain (formIdx n (Int.negSucc k))), ‖y‖ = 0 :=
    fun N k y => by
      have := LocalElement.subsingleton_L2F_negSucc (mesh n N).domain (n := n) k
      rw [Subsingleton.elim y 0, norm_zero]
  have hest : ∀ N, (∀ i x, ‖(qMinusSmoothed hb N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (qMinus n b N).V i,
        ‖v - (qMinusSmoothed hb N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i v‖ ≤
          1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEq_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rcases i with k | k
      · exact (hbound N k _ (pMax_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (h0 N k _).le.trans (by positivity)
    · rcases i with k | k
      · set w : L2F ℝ (cubeRefinement n (1 / 2) (N + 1)).domain (formIdx n k) := v
        have h := norm_le_sqrt_sum_of_sq_le (K := fun k => K k * γ ^ 2)
          (fun k => mul_nonneg (hK0 k) (sq_nonneg γ)) (k := k) (x := w)
          (y := w - cubeSmoothedInterp n (1 / 2) (N + 1) hb (pMax γ hγ hγ1 N) k w) fun _ =>
            (hK k (pMax_isAdm N) hγ1 (fun x hx => pMax_samples_mem N x (by rwa [mesh_domain]))
              w hv).trans (le_of_eq (by ring))
        refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        rw [← Finset.sum_mul, Real.sqrt_mul hS, Real.sqrt_sq hγ.le, mul_comm]
        exact hγS
      · exact (h0 N k _).le.trans (by positivity)
  exact ⟨fun N => pMax_isMaximal N, le_max_right _ _, fun N => (hest N).1, fun N => (hest N).2⟩

end Feec.Models.Cube.FEM
