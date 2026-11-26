module

public import Feec.Models.Cube.PolySmoothingEstimates
public import Feec.Models.Cube.FiniteElementConvergence
public import Feec.HilbertComplex.Approximation.DiscreteCohomology
public import Feec.FiniteElement.PolyOrder

/-!
# The higher-order finite element methods on the cube as conforming families

For every admissible sequence `S` on the Freudenthal meshes of `Q = (0, ½)ⁿ`: interpolation errors,
graph-norm density ([Arnold2018], Ch. 7) and the conforming families `FEM.polyFamily`,
`FEM.polyFamilyMin` ([AFW2010], §5.5).

## Main results

* `FEM.exists_mem_poly_le`: the interpolation error of order `h^{s+1}` in `L²` and for `d`.
* `FEM.eventually_exists_poly_graph`, `FEM.eventually_exists_polyMin_graph`: graph-norm density.
* `FEM.exists_tendstoUniformlyOn_window_poly`: the semi-discrete Hodge wave equation converges.
* `FEM.tableRows_common_smoother`: one smoother for [QuennevilleBelair2015], Tables 5.1 and 6.1.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

namespace Poly

variable (S : PolySeq)

/-! ### The local interpolation error of the higher-order families -/

theorem exists_polySpace_near {N k s : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {w : FormField n} (hw : ContDiff ℝ (s + 1) w)
    (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M) :
    ∃ P ∈ polySpace n s k, ∀ x ∈ T.closedInterior, ‖w x - P x‖ ≤ hN N ^ (s + 1) * M := by
  set x₀ := T.points 0
  have hx₀ : x₀ ∈ T.closedInterior := vertexSet_subset_closedInterior T (points_mem_vertexSet T 0)
  refine ⟨degPartField k (taylorPoly w x₀ (s + 1)), degPartField_taylorPoly_mem w x₀, ?_⟩
  intro x hx
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  have htay := norm_iteratedFDeriv_sub_taylorPoly_le (k := s + 1) (f := w) (U := Set.univ)
    (K := (cubeSimplex N m σ).closedInterior) (x₀ := x₀) (d := hN N) (M := M) isOpen_univ
    (Set.subset_univ _) (convex_closedInterior _) hx₀ (hw.contDiffOn)
    (fun y hy => norm_sub_le_of_mem_cubeSimplex hy hx₀) hM hx (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero, Nat.sub_zero] at htay
  have e : w x - degPartField k (taylorPoly w x₀ (s + 1)) x =
      degPart k (w x - taylorPoly w x₀ (s + 1) x) := by
    have h2 := congrFun (degPartField_sub k w (taylorPoly w x₀ (s + 1))) x
    rw [degPartField_of_isDeg hdeg] at h2
    exact h2.symm
  rw [e]
  exact (norm_degPart_le k _).trans htay

theorem abs_sub_globalInterp_le {N k s : ℕ} (hs : polySpace n s k ≤ S.space n k) {B D : ℝ}
    (hB : DofBound S n k B) (hB0 : 0 ≤ B) (hD : CoeffBound S n k D)
    (T : (mesh n N).simplices) {w : FormField n} (hw : ContDiff ℝ (s + 1) w)
    (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior)
    (t : Finset (Fin n)) :
    |w x t - ((((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
      (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
        FormField n) x t| ≤
      (1 + B * Module.finrank ℝ (S.space n k) * D) * (hN N ^ (s + 1) * M) := by
  obtain ⟨P, hP, hwP⟩ := exists_polySpace_near T.2 hw hdeg hM
  have hPS : P ∈ S.space n k := hs hP
  set e := hN N ^ (s + 1) * M
  have he : 0 ≤ e := (norm_nonneg _).trans (hwP x hx)
  set Iw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    ⟨w, hw.continuous⟩ : (polyElement n S).Piecewise (mesh n N) k) T)
  have hIw : (Iw : FormField n) ∈ S.space n k := Iw.2
  set z : FormField n := (Iw : FormField n) - P
  have hz : z ∈ S.space n k := Submodule.sub_mem _ hIw hPS
  have hwPc : Continuous (w - P) := hw.continuous.sub (PolyKind.contDiff_of_mem_space hPS).continuous
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ hN N ^ k * (D * e) := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ =
        S.dof g k i ⟨w, hw.continuous⟩ :=
      (polyElement n S).localDof_globalInterp (mesh n N) k ⟨w, hw.continuous⟩ T g hgT i
    have e2 : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ = S.dof g k i ⟨w - P, hwPc⟩ := by
      have : (⟨z, S.space_le_contForms n k hz⟩ : contForms n) =
          ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ -
            ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      have : (⟨w - P, hwPc⟩ : contForms n) = ⟨w, hw.continuous⟩ -
          ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      rw [‹(⟨z, _⟩ : contForms n) = _›, this, map_sub, map_sub, e1]
    rw [e2]
    refine (abs_dof_le S hD T.2 hgT i _ he fun y hy t => ?_).trans (le_of_eq (by ring))
    have := norm_le_pi_norm ((w - P) y) t
    rw [Real.norm_eq_abs] at this
    exact this.trans (hwP y hy)
  have hzb := abs_le_of_abs_dof_le S hB hB0 T.2 hz hdof hx t
  have h1 : |w x t - P x t| ≤ e := by
    have := norm_le_pi_norm (w x - P x) t
    rw [Real.norm_eq_abs, Pi.sub_apply] at this
    exact this.trans (hwP x hx)
  calc |w x t - (Iw : FormField n) x t| = |(w x t - P x t) - z x t| := by
        simp only [z, Pi.sub_apply]; ring_nf
    _ ≤ |w x t - P x t| + |z x t| := abs_sub _ _
    _ ≤ e + B * Module.finrank ℝ (S.space n k) * (D * e) := add_le_add h1 hzb
    _ = (1 + B * Module.finrank ℝ (S.space n k) * D) * e := by ring

end Poly

/-! ### Interpolation of smooth forms on the cube meshes -/

variable (n) in
/-- The constant `B_k` of `Poly.DofBound` for `S`. -/
def dofConst (S : PolySeq) (k : ℕ) : ℝ := (Poly.exists_dofBound (n := n) S k).choose

variable (n) in
/-- The constant `D_k` of `Poly.CoeffBound` for `S`. -/
def coeffConst (S : PolySeq) (k : ℕ) : ℝ := (Poly.exists_coeffBound (n := n) S k).choose

theorem dofConst_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ dofConst n S k :=
  (Poly.exists_dofBound (n := n) S k).choose_spec.1

theorem dofBound_dofConst (S : PolySeq) (k : ℕ) : Poly.DofBound S n k (dofConst n S k) :=
  (Poly.exists_dofBound (n := n) S k).choose_spec.2

theorem coeffConst_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ coeffConst n S k :=
  (Poly.exists_coeffBound (n := n) S k).choose_spec.1

theorem coeffBound_coeffConst (S : PolySeq) (k : ℕ) : Poly.CoeffBound S n k (coeffConst n S k) :=
  (Poly.exists_coeffBound (n := n) S k).choose_spec.2

variable (n) in
/-- The constant `#Λᵏ |Q|^{1/2} (1 + B_k dim(P(T)ᵏ) D_k)` of the `L²` interpolation error. -/
def polyInterpConst (S : PolySeq) (k : ℕ) : ℝ :=
  Fintype.card (formIdx n k) * (volume.real (cubeDomain n) ^ (1 / 2 : ℝ) *
    (1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k))

theorem polyInterpConst_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ polyInterpConst n S k := by
  unfold polyInterpConst
  have := dofConst_nonneg (n := n) S k
  have := coeffConst_nonneg (n := n) S k
  positivity

theorem abs_sub_globalInterp_le_cube (S : PolySeq) {N k s : ℕ}
    (hs : polySpace n s k ≤ S.space n k) {w : FormField n} (hw : ContDiff ℝ (s + 1) w)
    (hdeg : ∀ x, IsDeg k (w x)) {L : ℝ}
    (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L)
    (T : (mesh n N).simplices) {x : Fin n → ℝ}
    (hx : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior) (t : Finset (Fin n)) :
    |w x t - ((((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
      (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
        FormField n) x t| ≤
      (1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k) *
        (meshSize N ^ (s + 1) * L) := by
  rw [← hN_eq_meshSize]
  refine Poly.abs_sub_globalInterp_le S hs (dofBound_dofConst S k) (dofConst_nonneg S k)
    (coeffBound_coeffConst S k) T hw hdeg (fun y hy => hL y ?_) hx t
  rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure T.2 hy

variable [NeZero n]

/-- **Interpolation error of order `h^{s+1}`** ([Arnold2018], Ch. 7; [Ciarlet2002], Thm 3.1.4). -/
theorem exists_mem_poly_le (S : PolySeq) (N k s : ℕ) (hs : polySpace n s k ≤ S.space n k)
    (hs' : polySpace n s (k + 1) ≤ S.space n (k + 1)) {w : FormField n}
    (hw : ContDiff ℝ (s + 2) w) (hdeg : ∀ x, IsDeg k (w x)) {L L' : ℝ}
    (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L)
    (hL' : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (poly n S N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ polyInterpConst n S k * (meshSize N ^ (s + 1) * L) ∧
      ∃ hv : v ∈ ((complex n).d k (k + 1)).domain,
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by
              exact_mod_cast Nat.le_add_left 1 (s + 1)))⟩ -
          (complex n).d k (k + 1) ⟨v, hv⟩‖ ≤
            polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))
  have hws : ContDiff ℝ (s + 1) w := hw.of_le (by exact_mod_cast Nat.le_succ (s + 1))
  have hdw : ContDiff ℝ (s + 1) (extDeriv w) := contDiff_extDeriv (m := s + 1) (by
    exact_mod_cast hw)
  have hdeg' : ∀ x, IsDeg (k + 1) (extDeriv w x) := fun x => IsDeg.extDeriv hdeg x
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL _ (subset_closure (center_mem_cubeDomain n)))
  have hL'0 : 0 ≤ L' := (norm_nonneg _).trans (hL' _ (subset_closure (center_mem_cubeDomain n)))
  have hB1 : 0 ≤ (1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k) *
      (meshSize N ^ (s + 1) * L) := by
    have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k
    have := (meshSize_pos N).le; positivity
  have hB2 : 0 ≤ (1 + dofConst n S (k + 1) * Module.finrank ℝ (S.space n (k + 1)) *
      coeffConst n S (k + 1)) * (meshSize N ^ (s + 1) * L') := by
    have := dofConst_nonneg (n := n) S (k + 1); have := coeffConst_nonneg (n := n) S (k + 1)
    have := (meshSize_pos N).le; positivity
  have hΩ := (isOpen_mesh_domain n N).measurableSet
  refine (polyElement n S).exists_mem_maximalSubcomplexOfEq_le (mesh n N) (mesh_domain n N)
    (isOpen_mesh_domain n N) (isOpen_cubeDomain n) (isBounded_cubeDomain n) k hw1
    (A := polyInterpConst n S k * (meshSize N ^ (s + 1) * L))
    (A' := polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L'))
    ((norm_formL2_sub_glue_le_of_forall _ _ hΩ k ⟨w, hw.continuous⟩
      ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
        (polyElement n S).Piecewise (mesh n N) k) hB1
      fun T x hx t _ => abs_sub_globalInterp_le_cube S hs hws hdeg hL T (interior_subset hx) t
      ).trans_eq ?_)
    ((norm_formL2_sub_glue_le_of_forall _ _ hΩ (k + 1) ⟨extDeriv w, hdw.continuous⟩
      ((polyElement n S).globalInterp (mesh n N) (k + 1) ⟨extDeriv w, hdw.continuous⟩ :
        (polyElement n S).Piecewise (mesh n N) (k + 1)) hB2
      fun T x hx t _ => abs_sub_globalInterp_le_cube S hs' hdw hdeg' hL' T (interior_subset hx) t
      ).trans_eq ?_) <;>
  · rw [mesh_domain, polyInterpConst]; push_cast; ring

/-! ### Density of the higher-order complexes -/

omit [NeZero n] in
theorem exists_bound_iteratedFDeriv {m : ℕ} {w : FormField n} (hw : ContDiff ℝ m w) :
    ∃ L, 0 ≤ L ∧ ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ m w y‖ ≤ L := by
  obtain ⟨L, hL⟩ := (isCompact_closure_cubeDomain n).exists_bound_of_continuousOn
    (hw.continuous_iteratedFDeriv le_rfl).continuousOn
  exact ⟨max L 0, le_max_right _ _, fun y hy => (hL y hy).trans (le_max_left _ _)⟩

/-- **Graph-norm density in `HΛᵏ(Q)`** of the spaces `Vₕᵏ` of `S`. -/
theorem eventually_exists_poly_graph (S : PolySeq) (k : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n k))
    (hx : x ∈ ((complex n).d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (poly n S N).V k, ‖x - v‖ < ε ∧
      ‖(complex n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((poly n S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth (isOpen_cubeDomain n) (isBounded_cubeDomain n)
    (by norm_num : (0 : ℝ) < 1 / 4) (starBall n) (fun N => poly n S N)
    (fun k w hw hdeg => ?_) k x hx hε
  have hw2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := exists_bound_iteratedFDeriv
    (hw.of_le (WithTop.coe_le_coe.2 le_top) : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) w)
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_iteratedFDeriv (m := 1)
    (contDiff_extDeriv (m := 1) (hw.of_le (WithTop.coe_le_coe.2 le_top)))
  refine ⟨fun N => polyInterpConst n S k * (meshSize N ^ (0 + 1) * L) +
    polyInterpConst n S (k + 1) * (meshSize N ^ (0 + 1) * L'), by
      simpa using (((tendsto_meshSize.pow 1).mul_const L).const_mul (polyInterpConst n S k)).add
        (((tendsto_meshSize.pow 1).mul_const L').const_mul (polyInterpConst n S (k + 1))),
    fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := exists_mem_poly_le S N k 0 (S.polySpace_zero_le_space k)
    (S.polySpace_zero_le_space (k + 1)) hw2 hdeg hL hL'
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right (mul_nonneg (polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (pow_nonneg (meshSize_pos N).le _) hL'0))), hdv, hv2.trans (le_add_of_nonneg_left
      (mul_nonneg (polyInterpConst_nonneg S k) (mul_nonneg (pow_nonneg (meshSize_pos N).le _)
        hL0)))⟩

theorem eventually_exists_poly_lt (S : PolySeq) (k : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n k))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (poly n S N).V k, ‖x - v‖ < ε :=
  Subcomplex.eventually_exists_lt_of_graph
    (fun k x hx _ hε => eventually_exists_poly_graph S k x hx hε) k x hε

theorem eventually_exists_poly_near (S : PolySeq) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (poly n S N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ ((complex n).d i j).domain),
        ‖(complex n).d i j ⟨x - v, Submodule.sub_mem _ hx ((poly n S N).le_domain i j hv)⟩‖ <
          ε :=
  Subcomplex.eventually_exists_near_of_graph
    (fun k x hx _ hε => eventually_exists_poly_graph S k x hx hε) i x hε

theorem tendsto_infDist_poly (S : PolySeq) (j : ℤ) (q : L2F ℝ (cubeDomain n) (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((poly n S N).V j :
      Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => poly n S N) q fun _ ha =>
    eventually_exists_poly_lt S j q ha

instance (S : PolySeq) (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((poly n S N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((poly n S N).V (a + i)))

instance (S : PolySeq) (N : ℕ) (a : ℤ) (m : ℕ) :
    FiniteDimensional ℝ ((poly n S N).window a m).graphSub :=
  inferInstance

theorem dense_window_poly (S : PolySeq) (a : ℤ) (m : ℕ) :
    ∀ ζ : ((complex n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((poly n S N).window a m).graphSub, ‖ζ - w‖ < δ := fun ζ _ hδ =>
  Subcomplex.eventually_exists_graphSub_lt (fun N => (poly n S N).window a m)
    (fun i x _ hε => (eventually_exists_poly_near S (a + i) x hε).mono fun _ hN => by
      obtain ⟨v, hv, h1, h2⟩ := hN
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩) ζ hδ

/-- **Convergence of the semi-discrete Hodge wave equation** ([QuennevilleBelair2015], Thm 4.14). -/
theorem exists_tendstoUniformlyOn_window_poly (S : PolySeq) (a : ℤ) (m : ℕ) (t₀ t₁ : ℝ)
    (x : ((complex n).window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((poly n S N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((poly n S N).window a m).graphSub)
        (((complex n).window a m).totalD.toGraphSpace
          ⟨x, (((complex n).window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complex n).window a m).totalD.graphFst (ξh N t))
        (fun t => ((complex n).window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  HilbertComplex.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection _
    (Subcomplex.isApproximating (dense_window_poly S a m)) t₀ t₁ x

/-! ### Density with vanishing boundary DOFs -/

/-- **Graph-norm density in `H̊Λᵏ(Q)`** of the spaces of `S` with vanishing boundary DOFs. -/
theorem eventually_exists_polyMin_graph (S : PolySeq) (k : ℤ)
    (x : L2F ℝ (cubeDomain n) (formIdx n k))
    (hx : x ∈ ((complexMin n).d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (polyMin n S N).V k, ‖x - v‖ < ε ∧
      ‖(complexMin n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((polyMin n S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth_min (isOpen_cubeDomain n) (isBounded_cubeDomain n)
    (by norm_num : (0 : ℝ) < 1 / 4) (starBall n) (fun N => polyMin n S N)
    (fun k w hw hdeg hsupp => ?_) k x hx hε
  have hw1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  have hdw : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (extDeriv w) :=
    contDiff_extDeriv (m := 1) (hw.of_le (WithTop.coe_le_coe.2 le_top))
  obtain ⟨L, hL0, hL⟩ := exists_bound_iteratedFDeriv hw1
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_iteratedFDeriv hdw
  refine ⟨fun N => polyInterpConst n S k * (meshSize N ^ (0 + 1) * L) +
    polyInterpConst n S (k + 1) * (meshSize N ^ (0 + 1) * L'), by
      simpa using (((tendsto_meshSize.pow 1).mul_const L).const_mul (polyInterpConst n S k)).add
        (((tendsto_meshSize.pow 1).mul_const L').const_mul (polyInterpConst n S (k + 1))),
    fun N => ?_⟩
  -- the canonical interpolant, with the interpolation error of order `h` (`s = 0`)
  have hB : ∀ (j : ℕ) {M : ℝ}, 0 ≤ M → 0 ≤ (1 + dofConst n S j *
      Module.finrank ℝ (S.space n j) * coeffConst n S j) * (meshSize N ^ (0 + 1) * M) :=
    fun j _ hM => by
      have := dofConst_nonneg (n := n) S j; have := coeffConst_nonneg (n := n) S j
      have := (meshSize_pos N).le; positivity
  have hΩ := (isOpen_mesh_domain n N).measurableSet
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := (polyElement n S).exists_mem_minimalSubcomplexOfEq_le
    (mesh n N) (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    (isBounded_cubeDomain n) (center n) (strictStar_mesh n N) k hw1 hsupp
    (A := polyInterpConst n S k * (meshSize N ^ (0 + 1) * L))
    (A' := polyInterpConst n S (k + 1) * (meshSize N ^ (0 + 1) * L'))
    ((norm_formL2_sub_glue_le_of_forall _ _ hΩ k ⟨w, hw1.continuous⟩
      ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw1.continuous⟩ :
        (polyElement n S).Piecewise (mesh n N) k) (hB k hL0)
      fun T x hx t _ => abs_sub_globalInterp_le_cube S (S.polySpace_zero_le_space k) hw1 hdeg hL
        T (interior_subset hx) t).trans_eq (by
          rw [mesh_domain, polyInterpConst]; push_cast; ring))
    ((norm_formL2_sub_glue_le_of_forall _ _ hΩ (k + 1) ⟨extDeriv w, hdw.continuous⟩
      ((polyElement n S).globalInterp (mesh n N) (k + 1) ⟨extDeriv w, hdw.continuous⟩ :
        (polyElement n S).Piecewise (mesh n N) (k + 1)) (hB (k + 1) hL'0)
      fun T x hx t _ => abs_sub_globalInterp_le_cube S (S.polySpace_zero_le_space (k + 1)) hdw
        (fun x => IsDeg.extDeriv hdeg x) hL' T (interior_subset hx) t).trans_eq (by
          rw [mesh_domain, polyInterpConst]; push_cast; ring))
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right (mul_nonneg (polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (pow_nonneg (meshSize_pos N).le _) hL'0))), hdv, hv2.trans (le_add_of_nonneg_left
      (mul_nonneg (polyInterpConst_nonneg S k) (mul_nonneg (pow_nonneg (meshSize_pos N).le _)
        hL0)))⟩

theorem eventually_exists_polyMin_lt (S : PolySeq) (k : ℤ)
    (x : L2F ℝ (cubeDomain n) (formIdx n k)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v ∈ (polyMin n S N).V k, ‖x - v‖ < ε :=
  Subcomplex.eventually_exists_lt_of_graph
    (fun k x hx _ hε => eventually_exists_polyMin_graph S k x hx hε) k x hε

theorem tendsto_infDist_polyMin (S : PolySeq) (j : ℤ) (q : L2F ℝ (cubeDomain n) (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((polyMin n S N).V j :
      Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => polyMin n S N) q fun _ ha =>
    eventually_exists_polyMin_lt S j q ha

instance (S : PolySeq) (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((polyMin n S N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((polyMin n S N).V (a + i)))

instance (S : PolySeq) (N : ℕ) (a : ℤ) (m : ℕ) :
    FiniteDimensional ℝ ((polyMin n S N).window a m).graphSub :=
  inferInstance

/-! ### The finite element method of the higher-order families under the smoothing estimates -/

namespace PolySmoothingEstimates

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- The smoothed projection `π_N = J_N⁻¹ Q_N` onto the complex of `S` on the cube. -/
def proj (hE : PolySmoothingEstimates n S p C) (N : ℕ) : (poly n S N).CochainProjection :=
  (polySmoothed n S N (p N) (hE.isMaximal N)).toCochainProjection (θ := 1 / 2) (by norm_num)
    (hE.close N)

theorem two_mul_nonneg (hE : PolySmoothingEstimates n S p C) : 0 ≤ 2 * C := by
  linarith [hE.half_le]

variable (hE : PolySmoothingEstimates n S p C)
include hE

theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ :=
  (polySmoothed n S N (p N) (hE.isMaximal N)).norm_toCochainProjection_le_two_mul (hE.close N)
    (hE.bound N i) x

end PolySmoothingEstimates

namespace PolySmoothingEstimatesMin

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- The smoothed projection `π̊_N = J_N⁻¹ Q̊_N` with vanishing boundary DOFs. -/
def proj (hE : PolySmoothingEstimatesMin n S p C) (N : ℕ) : (polyMin n S N).CochainProjection :=
  (polySmoothedMin n S N (p N) (hE.isMinimal N)).toCochainProjection (θ := 1 / 2) (by norm_num)
    (hE.close N)

theorem two_mul_nonneg (hE : PolySmoothingEstimatesMin n S p C) : 0 ≤ 2 * C := by
  linarith [hE.half_le]

variable (hE : PolySmoothingEstimatesMin n S p C)
include hE

theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ :=
  (polySmoothedMin n S N (p N) (hE.isMinimal N)).norm_toCochainProjection_le_two_mul
    (hE.close N) (hE.bound N i) x

end PolySmoothingEstimatesMin

/-! ### The higher-order finite element methods on the cube, with no hypotheses -/

theorem polySmoothingEstimates_exists (S : PolySeq) :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ), PolySmoothingEstimates n S p C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := polySmoothingEstimates_pMax (n := n) S
  obtain ⟨C, hC⟩ := h γ₀ hγ₀ (by linarith) le_rfl
  exact ⟨_, C, hC⟩

theorem polySmoothingEstimatesMin_exists (S : PolySeq) :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ), PolySmoothingEstimatesMin n S p C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := polySmoothingEstimatesMin_pMin (n := n) S
  obtain ⟨C, hC⟩ := h γ₀ hγ₀ le_rfl
  exact ⟨_, C, hC⟩

/-! ### The higher-order families as conforming families -/

section Family

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- The conforming family of `HΛ(Q)` of the smoothing estimates `hE` ([AFW2010], §5.5). -/
def PolySmoothingEstimates.family (hE : PolySmoothingEstimates n S p C) :
    ConformingFamily (complex n) ℕ :=
  .ofSmoothing atTop (poly n S) (fun N => polySmoothed n S N (p N) (hE.isMaximal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound (tendsto_infDist_poly S)

/-- The conforming family of `H̊Λ(Q)` of the smoothing estimates `hE`. -/
def PolySmoothingEstimatesMin.family (hE : PolySmoothingEstimatesMin n S p C) :
    ConformingFamily (complexMin n) ℕ :=
  .ofSmoothing atTop (polyMin n S) (fun N => polySmoothedMin n S N (p N) (hE.isMinimal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound (tendsto_infDist_polyMin S)

variable (n)

/-- The finite element complexes of `S`, a conforming family of `HΛ(Q)`. -/
def polyFamily (S : PolySeq) : ConformingFamily (complex n) ℕ :=
  (polySmoothingEstimates_exists (n := n) S).choose_spec.choose_spec.family

/-- The complexes of `S` with vanishing boundary DOFs, a conforming family of `H̊Λ(Q)`. -/
def polyFamilyMin (S : PolySeq) : ConformingFamily (complexMin n) ℕ :=
  (polySmoothingEstimatesMin_exists (n := n) S).choose_spec.choose_spec.family

variable {n}

@[simp] theorem polyFamily_V (S : PolySeq) : (polyFamily n S).V = poly n S := rfl

@[simp] theorem polyFamilyMin_V (S : PolySeq) : (polyFamilyMin n S).V = polyMin n S := rfl

end Family

/-! ### The rows of Tables 5.1 and 6.1 with one smoother -/

theorem PolySmoothingEstimatesMin.mono {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C C' : ℝ} (hE : PolySmoothingEstimatesMin n S p C) (hC : C ≤ C') :
    PolySmoothingEstimatesMin n S p C' where
  isMinimal := hE.isMinimal
  half_le := hE.half_le.trans hC
  bound N i x := (hE.bound N i x).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  close := hE.close

theorem PolySmoothingEstimates.mono {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)}
    {C C' : ℝ} (hE : PolySmoothingEstimates n S p C) (hC : C ≤ C') :
    PolySmoothingEstimates n S p C' where
  isMaximal := hE.isMaximal
  half_le := hE.half_le.trans hC
  bound N i x := (hE.bound N i x).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  close := hE.close

/-- **The two rows of [QuennevilleBelair2015], Tables 5.1 and 6.1, share one smoother.** -/
theorem tableRows_common_smoother :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ γ₀ →
      (∃ C, SmoothingEstimatesMin 3 (pMin γ hγ) C) ∧
      (∃ C, PolySmoothingEstimatesMin 3 PolySeq.lowestOrder (pMin γ hγ) C) ∧
      (∃ C, PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 (pMin γ hγ) C) := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := exists_common_gamma (n := 3)
    (fun b : Bool => if b then PolySeq.lagrangeP2 else PolySeq.lowestOrder)
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγγ₀ => ?_⟩
  obtain ⟨-, hW, hS⟩ := h γ hγ (by linarith) hγγ₀
  exact ⟨hW, (hS false).2, (hS true).2⟩

theorem tableRows_uniform_cochainProjection :
    ∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
      (∀ N i x, ‖(hT.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧
      (∀ N i j, (hT.proj N).IsGraphBounded i j (2 * C)) ∧
      (∀ N i x, ‖(hB.proj N).π i x‖ ≤ 2 * C * ‖x‖) ∧
      (∀ N i j, (hB.proj N).IsGraphBounded i j (2 * C)) ∧
      (∀ j, Tendsto (fun N => (hT.proj N).harmonicGap j) atTop (𝓝 0)) ∧
      ∀ j, Tendsto (fun N => (hB.proj N).harmonicGap j) atTop (𝓝 0) := by
  obtain ⟨γ₀, hγ₀, -, h⟩ := tableRows_common_smoother
  obtain ⟨-, ⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩ := h γ₀ hγ₀ le_rfl
  have hT := h₁.mono (le_max_left C₁ C₂)
  have hB := h₂.mono (le_max_right C₁ C₂)
  exact ⟨_, max C₁ C₂, hT, hB, hT.norm_proj_le,
    fun N i j => (hT.proj N).isGraphBounded_of_norm_le (hT.norm_proj_le N i) (hT.norm_proj_le N j),
    hB.norm_proj_le,
    fun N i j => (hB.proj N).isGraphBounded_of_norm_le (hB.norm_proj_le N i) (hB.norm_proj_le N j),
    fun _ => hT.family.tendsto_harmonicGap, fun _ => hB.family.tendsto_harmonicGap⟩

end Feec.Models.Cube.FEM
