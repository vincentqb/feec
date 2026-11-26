module

public import Feec.Models.StarShaped.PolySmoothing
public import Feec.Models.StarShaped.FiniteElement
public import Feec.FiniteElement.PolyOrder

/-!
# The higher-order finite element method on star-shaped domains

On a bounded domain star-shaped with respect to a ball with a shape-regular, quasi-uniform mesh
family, the complexes of every admissible sequence (`MeshFamily.poly`) are conforming families with
Jackson estimates of order `h_N^{s+1}` for `C^{s+2}` forms.

## Main results

* `MeshFamily.exists_uniform_polyProj`: uniformly bounded smoothed cochain projections.
* `MeshFamily.exists_mem_poly_le`: the interpolation error of order `h_N^{s+1}`.
* `MeshFamily.mixed_rate_poly`: the rate `h^{s+1}` of the mixed method, given a Poincaré bound.
* `MeshFamily.exists_tendstoUniformlyOn_window_poly`: convergence of the semi-discrete scheme.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

namespace Feec.Models.StarShaped

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

/-! ### The interpolation error on shape-regular simplices -/

section Interp

variable (S : PolySeq)

theorem exists_polySpace_near_diam {k s : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {w : FormField n} (hw : ContDiff ℝ (s + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M) :
    ∃ P ∈ polySpace n s k, ∀ x ∈ T.closedInterior, ‖w x - P x‖ ≤ diam T ^ (s + 1) * M := by
  set x₀ := T.points 0
  have hx₀ : x₀ ∈ T.closedInterior := T.point_mem_closedInterior 0
  refine ⟨degPartField k (taylorPoly w x₀ (s + 1)), degPartField_taylorPoly_mem w x₀,
    fun x hx => ?_⟩
  have htay := norm_iteratedFDeriv_sub_taylorPoly_le (k := s + 1) (f := w) (U := Set.univ)
    (K := T.closedInterior) (x₀ := x₀) (d := diam T) (M := M) isOpen_univ
    (Set.subset_univ _) (convex_closedInterior _) hx₀ (hw.contDiffOn)
    (fun y hy => by
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded hy hx₀) hM hx
    (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero, Nat.sub_zero] at htay
  have e : w x - degPartField k (taylorPoly w x₀ (s + 1)) x =
      degPart k (w x - taylorPoly w x₀ (s + 1) x) := by
    have h2 := congrFun (degPartField_sub k w (taylorPoly w x₀ (s + 1))) x
    rw [degPartField_of_isDeg hdeg] at h2
    exact h2.symm
  rw [e]
  exact (norm_degPart_le k _).trans htay

theorem norm_sub_polyLocalInterp_le {k s : ℕ} (hs : polySpace n s k ≤ S.space n k)
    {C c B D : ℝ} (hB : PolyDofBound S n k C c B) (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D)
    {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} (hS : IsShapeRegular Sset C c)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ Sset) (hh : 0 < diam T) {w : FormField n}
    (hw : ContDiff ℝ (s + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    ‖w x - (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
      (polyElement n S).space T k) : FormField n) x‖ ≤ (1 + B * D) * (diam T ^ (s + 1) * M) := by
  obtain ⟨P, hP, hwP⟩ := exists_polySpace_near_diam hw hdeg hM
  have hPS : P ∈ S.space n k := hs hP
  set e := diam T ^ (s + 1) * M
  have he : 0 ≤ e := (norm_nonneg _).trans (hwP x hx)
  set Iw : (polyElement n S).space T k := (polyElement n S).localInterp T k ⟨w, hw.continuous⟩
  have hIw : (Iw : FormField n) ∈ S.space n k := Iw.2
  set z : FormField n := (Iw : FormField n) - P
  have hz : z ∈ S.space n k := Submodule.sub_mem _ hIw hPS
  have hwPc : Continuous (w - P) :=
    hw.continuous.sub (PolyKind.contDiff_of_mem_space hPS).continuous
  have hdof : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ D * diam T ^ k * e := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ =
        S.dof g k i ⟨w, hw.continuous⟩ :=
      (polyElement n S).localDof_localInterp T k ⟨w, hw.continuous⟩ g hgT i
    have e2 : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ = S.dof g k i ⟨w - P, hwPc⟩ := by
      have h1 : (⟨z, S.space_le_contForms n k hz⟩ : contForms n) =
          ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ -
            ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      have h2 : (⟨w - P, hwPc⟩ : contForms n) = ⟨w, hw.continuous⟩ -
          ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      rw [h1, h2, map_sub, map_sub, e1]
    rw [e2]
    refine abs_polyDof_le S hD hgT i _ he fun y hy t => ?_
    have := norm_le_pi_norm ((w - P) y) t
    rw [Real.norm_eq_abs] at this
    exact this.trans (hwP y hy)
  have hzb := hB hS T hT hh hz (by positivity) hdof x hx
  have hzx : ‖z x‖ ≤ B * D * e := by
    have hk : 0 < diam T ^ k := pow_pos hh k
    refine le_of_mul_le_mul_left (hzb.trans (le_of_eq ?_)) hk
    ring
  have h1 := hwP x hx
  calc ‖w x - (Iw : FormField n) x‖ = ‖(w x - P x) - z x‖ := by
        congr 1; simp only [z, Pi.sub_apply]; abel
    _ ≤ ‖w x - P x‖ + ‖z x‖ := norm_sub_le _ _
    _ ≤ e + B * D * e := add_le_add h1 hzx
    _ = (1 + B * D) * e := by ring

end Interp

/-! ### The complexes of an admissible sequence on a mesh family -/

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D) [NeZero n] (S : PolySeq)

/-- The complex `Vₕ(S, M_N)` of the admissible sequence `S`, a subcomplex of `HΛ(Ω)`. -/
def poly (N : ℕ) : D.complex.Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (F.domain_eq N) (F.isOpen_domain N) D.isOpen
    (S.subcomplex (F.mesh N) (F.isOpen_domain N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((F.poly S N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

/-- The complex `V̊ₕ(S, M_N)` of `S` with vanishing boundary DOFs, a subcomplex of `H̊Λ(Ω)`. -/
def polyMin (N : ℕ) : D.complexMin.Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (F.domain_eq N) (F.isOpen_domain N) D.isOpen
    (S.subcomplexMin (F.mesh N) (F.isOpen_domain N) D.x₀ (F.strict_mesh N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((F.polyMin S N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

/-- Uniformly bounded smoothed cochain projections onto the complexes of `S` on the family, in `L²`
and in every graph norm. [AFW2010], §5.5; [ChristiansenWinther2008] -/
theorem exists_uniform_polyProj : ∃ K : ℝ, 1 ≤ K ∧ ∀ N,
    ∃ π : (F.poly S N).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨K, hK1, hK⟩ := exists_uniform_polyCochainProjection S (x₀ := D.x₀) F.C_nonneg F.c_pos
    F.q_pos D.s₀_pos D.R_pos
  refine ⟨K, hK1, fun N => ?_⟩
  obtain ⟨π, h1, h2⟩ := hK (F.mesh N) (F.data N) (F.isOpen_domain N) (F.starBall_mesh N)
    (F.norm_sub_le_mesh N)
  exact (deRham ℝ n).maximalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (S.subcomplex (F.mesh N) (F.isOpen_domain N))
    (fun Θ hΘ S' => ∃ π : S'.CochainProjection, (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧
      ∀ i j, π.IsGraphBounded i j K) ⟨π, h1, h2⟩

theorem exists_uniform_polyProjMin : ∃ K : ℝ, 1 ≤ K ∧ ∀ N,
    ∃ π : (F.polyMin S N).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨K, hK1, hK⟩ := exists_uniform_polyCochainProjectionMin S (x₀ := D.x₀) F.C_nonneg
    F.c_pos F.q_pos D.s₀_pos D.R_pos
  refine ⟨K, hK1, fun N => ?_⟩
  obtain ⟨π, h1, h2⟩ := hK (F.mesh N) (F.data N) (F.isOpen_domain N) (F.starBall_mesh N)
    (F.norm_sub_le_mesh N)
  exact (deRham ℝ n).minimalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (S.subcomplexMin (F.mesh N) (F.isOpen_domain N) D.x₀ (F.strict_mesh N))
    (fun Θ hΘ S' => ∃ π : S'.CochainProjection, (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧
      ∀ i j, π.IsGraphBounded i j K) ⟨π, h1, h2⟩

end MeshFamily

/-! ### Smooth forms of order `s` on a star-shaped domain -/

namespace StarDomain

variable (D : StarDomain n)

theorem exists_bound_iteratedFDeriv {m : ℕ} {w : FormField n} (hw : ContDiff ℝ m w) :
    ∃ L, 0 ≤ L ∧ ∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ m w y‖ ≤ L := by
  obtain ⟨L, hL⟩ := D.isCompact_closure.exists_bound_of_continuousOn
    (hw.continuous_iteratedFDeriv le_rfl).continuousOn
  exact ⟨max L 0, le_max_right _ _, fun y hy => (hL y hy).trans (le_max_left _ _)⟩

/-- `x` is a `C^{s+2}` form of degree `j` with `(s+1)`-st derivative bounds `L` on `cl Ω`. -/
def IsCsForm (s : ℕ) (j : ℤ) (L : ℝ) (x : L2F ℝ D.Ω (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n,
    ∃ hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    x = formL2 D.isOpen.measurableSet D.isBounded j ⟨w, hw.continuous⟩

/-- `IsCsForm` with, in addition, `w = 0` outside `Ω` (the regularity class of `H̊Λ(Ω)`). -/
def IsCsFormMin (s : ℕ) (j : ℤ) (L : ℝ) (x : L2F ℝ D.Ω (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n,
    ∃ hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∉ D.Ω, w y = 0) ∧
    (∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) ∧
    (∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L) ∧
    x = formL2 D.isOpen.measurableSet D.isBounded j ⟨w, hw.continuous⟩

theorem IsCsFormMin.isCsForm {D : StarDomain n} {s : ℕ} {j : ℤ} {L : ℝ}
    {x : L2F ℝ D.Ω (formIdx n j)} (hx : D.IsCsFormMin s j L x) : D.IsCsForm s j L x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, -, hL, hL', he⟩
  · exact Or.inl hj
  · exact Or.inr ⟨k, hk, w, hw, hdeg, hL, hL', he⟩

end StarDomain

/-! ### Interpolation of smooth forms on the meshes of the family -/

variable (n) in
/-- The coefficient constant `D_k` of the degrees of freedom of `S` (`PolyCoeffBound`). -/
def polyCoeffConst (S : PolySeq) (k : ℕ) : ℝ := (exists_polyCoeffBound (n := n) S k).choose

theorem polyCoeffConst_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ polyCoeffConst n S k :=
  (exists_polyCoeffBound (n := n) S k).choose_spec.1

theorem polyCoeffBound_polyCoeffConst (S : PolySeq) (k : ℕ) :
    PolyCoeffBound S n k (polyCoeffConst n S k) :=
  (exists_polyCoeffBound (n := n) S k).choose_spec.2

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D) (S : PolySeq)

/-- The DOF constant `B_k` of `S` for the shape-regularity constants of the family. -/
def polyDofConst (k : ℕ) : ℝ := (exists_polyDofBound (n := n) S k F.C F.c).choose

theorem polyDofConst_nonneg (k : ℕ) : 0 ≤ F.polyDofConst S k :=
  (exists_polyDofBound (n := n) S k F.C F.c).choose_spec.1

theorem polyDofBound_polyDofConst (k : ℕ) : PolyDofBound S n k F.C F.c (F.polyDofConst S k) :=
  (exists_polyDofBound (n := n) S k F.C F.c).choose_spec.2

/-- The constant `#Λᵏ |Ω|^{1/2} (1 + B_k D_k)` of the `L²` interpolation estimate of `S`. -/
def polyInterpConst (k : ℕ) : ℝ :=
  Fintype.card (formIdx n k) * (volume.real D.Ω ^ (1 / 2 : ℝ) *
    (1 + F.polyDofConst S k * polyCoeffConst n S k))

theorem polyInterpConst_nonneg (k : ℕ) : 0 ≤ F.polyInterpConst S k := by
  unfold polyInterpConst
  have := F.polyDofConst_nonneg S k
  have := polyCoeffConst_nonneg (n := n) S k
  positivity

/-- The constant `B_j = A_j + A_{j+1}` of the graph-norm interpolation error of `S`. -/
def polyInterpBound (j : ℤ) : ℝ := F.polyInterpConst S j.toNat + F.polyInterpConst S (j.toNat + 1)

theorem polyInterpBound_nonneg (j : ℤ) : 0 ≤ F.polyInterpBound S j :=
  add_nonneg (F.polyInterpConst_nonneg _ _) (F.polyInterpConst_nonneg _ _)

theorem globalInterp_apply_eq_localInterp (E : LocalElement n) (M : SimplicialMesh n) (k : ℕ)
    (w : contForms n) (T : M.simplices) :
    ((E.globalInterp M k w : E.Piecewise M k) T) = E.localInterp T k w :=
  E.localSpace_ext T k fun g hg i => by
    rw [LocalElement.localDof_globalInterp _ _ _ _ _ _ hg,
      LocalElement.localDof_localInterp _ _ _ _ _ hg]

theorem abs_sub_globalInterp_le [NeZero n] {N k s : ℕ} (hs : polySpace n s k ≤ S.space n k)
    {w : FormField n} (hw : ContDiff ℝ (s + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {L : ℝ}
    (hL : ∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L)
    (T : (F.mesh N).simplices) {x : Fin n → ℝ}
    (hx : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior) (t : Finset (Fin n)) :
    |w x t - ((((polyElement n S).globalInterp (F.mesh N) k ⟨w, hw.continuous⟩ :
      (polyElement n S).Piecewise (F.mesh N) k) T : (polyElement n S).space T k) :
        FormField n) x t| ≤
      (1 + F.polyDofConst S k * polyCoeffConst n S k) * ((F.mesh N).meshSize ^ (s + 1) * L) := by
  rw [globalInterp_apply_eq_localInterp]
  have hT0 := diam_pos (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hM : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L := fun y hy => hL y (by
    rw [← F.domain_eq N]; exact (F.mesh N).closedInterior_subset_closure T.2 hy)
  have h := norm_sub_polyLocalInterp_le S hs (F.polyDofBound_polyDofConst S k)
    (polyCoeffConst_nonneg S k) (polyCoeffBound_polyCoeffConst S k) (F.data N).shape T.2 hT0
    hw hdeg hM hx
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hM x hx)
  have hts : |w x t - (((polyElement n S).localInterp (T : Affine.Simplex ℝ (Fin n → ℝ) n) k
      ⟨w, hw.continuous⟩ : (polyElement n S).space T k) : FormField n) x t| ≤
      ‖w x - (((polyElement n S).localInterp (T : Affine.Simplex ℝ (Fin n → ℝ) n) k
        ⟨w, hw.continuous⟩ : (polyElement n S).space T k) : FormField n) x‖ := by
    have := norm_le_pi_norm (w x - (((polyElement n S).localInterp
      (T : Affine.Simplex ℝ (Fin n → ℝ) n) k ⟨w, hw.continuous⟩ :
        (polyElement n S).space T k) : FormField n) x) t
    rwa [Real.norm_eq_abs, Pi.sub_apply] at this
  refine hts.trans (h.trans ?_)
  have h1 : 0 ≤ 1 + F.polyDofConst S k * polyCoeffConst n S k := by
    have := F.polyDofConst_nonneg S k; have := polyCoeffConst_nonneg (n := n) S k; positivity
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hL0) h1
  exact pow_le_pow_left₀ (diam_nonneg _) ((F.mesh N).diam_le_meshSize T.2) _

variable [NeZero n]

/-- The `L²` interpolation error of order `h_N^{s+1}` of an admissible sequence for `C^{s+2}` forms.
[Arnold2018], Ch. 7; [Ciarlet2002], Thm 3.1.4 -/
theorem exists_mem_poly_le (N k s : ℕ) (hs : polySpace n s k ≤ S.space n k)
    (hs' : polySpace n s (k + 1) ≤ S.space n (k + 1)) {w : FormField n}
    (hw : ContDiff ℝ (s + 2) w) (hdeg : ∀ x, IsDeg k (w x)) {L L' : ℝ} (hL0 : 0 ≤ L)
    (hL'0 : 0 ≤ L')
    (hL : ∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L)
    (hL' : ∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (F.poly S N).V k,
      ‖formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ - v‖ ≤
        F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L) ∧
      ∃ hv : v ∈ (D.complex.d k (k + 1)).domain,
        ‖formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by
              exact_mod_cast Nat.le_add_left 1 (s + 1)))⟩ -
          D.complex.d k (k + 1) ⟨v, hv⟩‖ ≤
            F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))
  have hws : ContDiff ℝ (s + 1) w := hw.of_le (by exact_mod_cast Nat.le_succ (s + 1))
  have hdw : ContDiff ℝ (s + 1) (extDeriv w) := contDiff_extDeriv (m := s + 1) (by
    exact_mod_cast hw)
  have hdeg' : ∀ x, IsDeg (k + 1) (extDeriv w x) := fun x => IsDeg.extDeriv hdeg x
  have hh := (F.meshSize_pos N).le
  have hB1 : 0 ≤ (1 + F.polyDofConst S k * polyCoeffConst n S k) *
      ((F.mesh N).meshSize ^ (s + 1) * L) := by
    have := F.polyDofConst_nonneg S k; have := polyCoeffConst_nonneg (n := n) S k; positivity
  have hB2 : 0 ≤ (1 + F.polyDofConst S (k + 1) * polyCoeffConst n S (k + 1)) *
      ((F.mesh N).meshSize ^ (s + 1) * L') := by
    have := F.polyDofConst_nonneg S (k + 1); have := polyCoeffConst_nonneg (n := n) S (k + 1)
    positivity
  have hΩ := (F.isOpen_domain N).measurableSet
  refine (polyElement n S).exists_mem_maximalSubcomplexOfEq_le (F.mesh N) (F.domain_eq N)
    (F.isOpen_domain N) D.isOpen D.isBounded k hw1
    (A := F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L))
    (A' := F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L'))
    ((norm_formL2_sub_glue_le_of_forall _ _ hΩ k ⟨w, hw.continuous⟩
      ((polyElement n S).globalInterp (F.mesh N) k ⟨w, hw.continuous⟩ :
        (polyElement n S).Piecewise (F.mesh N) k) hB1
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs hws hdeg hL T (interior_subset hx) t
      ).trans_eq ?_)
    ((norm_formL2_sub_glue_le_of_forall _ _ hΩ (k + 1) ⟨extDeriv w, hdw.continuous⟩
      ((polyElement n S).globalInterp (F.mesh N) (k + 1) ⟨extDeriv w, hdw.continuous⟩ :
        (polyElement n S).Piecewise (F.mesh N) (k + 1)) hB2
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs' hdw hdeg' hL' T (interior_subset hx) t
      ).trans_eq ?_) <;>
  · rw [F.domain_eq N, polyInterpConst]; push_cast; ring

theorem exists_mem_polyMin_le (N k s : ℕ) (hs : polySpace n s k ≤ S.space n k)
    (hs' : polySpace n s (k + 1) ≤ S.space n (k + 1)) {w : FormField n}
    (hw : ContDiff ℝ (s + 2) w) (hdeg : ∀ x, IsDeg k (w x)) (hsupp : ∀ x ∉ D.Ω, w x = 0)
    {L L' : ℝ} (hL0 : 0 ≤ L) (hL'0 : 0 ≤ L')
    (hL : ∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L)
    (hL' : ∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (F.polyMin S N).V k,
      ‖formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ - v‖ ≤
        F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L) ∧
      ∃ hv : v ∈ (D.complexMin.d k (k + 1)).domain,
        ‖formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by
              exact_mod_cast Nat.le_add_left 1 (s + 1)))⟩ -
          D.complexMin.d k (k + 1) ⟨v, hv⟩‖ ≤
            F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))
  have hws : ContDiff ℝ (s + 1) w := hw.of_le (by exact_mod_cast Nat.le_succ (s + 1))
  have hdw : ContDiff ℝ (s + 1) (extDeriv w) := contDiff_extDeriv (m := s + 1) (by
    exact_mod_cast hw)
  have hdeg' : ∀ x, IsDeg (k + 1) (extDeriv w x) := fun x => IsDeg.extDeriv hdeg x
  have hh := (F.meshSize_pos N).le
  have hB1 : 0 ≤ (1 + F.polyDofConst S k * polyCoeffConst n S k) *
      ((F.mesh N).meshSize ^ (s + 1) * L) := by
    have := F.polyDofConst_nonneg S k; have := polyCoeffConst_nonneg (n := n) S k; positivity
  have hB2 : 0 ≤ (1 + F.polyDofConst S (k + 1) * polyCoeffConst n S (k + 1)) *
      ((F.mesh N).meshSize ^ (s + 1) * L') := by
    have := F.polyDofConst_nonneg S (k + 1); have := polyCoeffConst_nonneg (n := n) S (k + 1)
    positivity
  have hΩ := (F.isOpen_domain N).measurableSet
  refine (polyElement n S).exists_mem_minimalSubcomplexOfEq_le (F.mesh N) (F.domain_eq N)
    (F.isOpen_domain N) D.isOpen D.isBounded D.x₀ (F.strict_mesh N) k hw1 hsupp
    (A := F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L))
    (A' := F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L'))
    ((norm_formL2_sub_glue_le_of_forall _ _ hΩ k ⟨w, hw.continuous⟩
      ((polyElement n S).globalInterp (F.mesh N) k ⟨w, hw.continuous⟩ :
        (polyElement n S).Piecewise (F.mesh N) k) hB1
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs hws hdeg hL T (interior_subset hx) t
      ).trans_eq ?_)
    ((norm_formL2_sub_glue_le_of_forall _ _ hΩ (k + 1) ⟨extDeriv w, hdw.continuous⟩
      ((polyElement n S).globalInterp (F.mesh N) (k + 1) ⟨extDeriv w, hdw.continuous⟩ :
        (polyElement n S).Piecewise (F.mesh N) (k + 1)) hB2
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs' hdw hdeg' hL' T (interior_subset hx) t
      ).trans_eq ?_) <;>
  · rw [F.domain_eq N, polyInterpConst]; push_cast; ring

/-! ### Degreewise rates -/

theorem exists_mem_poly_le_of_isCsForm {s : ℕ} {j : ℤ} (hS : PolyOrderAt n S s j) {L : ℝ}
    {x : L2F ℝ D.Ω (formIdx n j)} (hx : D.IsCsForm s j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (F.poly S N).V j,
      ‖x - v‖ ≤ F.polyInterpBound S j * L * (F.mesh N).meshSize ^ (s + 1) ∧
      ∀ j' (hxj : x ∈ (D.complex.d j j').domain),
        ‖D.complex.d j j' ⟨x - v, Submodule.sub_mem _ hxj ((F.poly S N).le_domain j j' hv)⟩‖ ≤
          F.polyInterpBound S j * L * (F.mesh N).meshSize ^ (s + 1) := by
  have hh := pow_nonneg (F.meshSize_pos N).le (s + 1)
  have hB0 := mul_nonneg (mul_nonneg (F.polyInterpBound_nonneg S j) hL0) hh
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩
  · have := LocalElement.subsingleton_L2F_of_neg D.Ω (n := n) hj
    exact (F.poly S N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ :=
    F.exists_mem_poly_le S N k s (hS k rfl).1 (hS k rfl).2 hw hdeg hL0 hL0 hL hL'
  obtain ⟨hdom, hval⟩ := F.formL2_mem_domain k
    (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))) hdeg
  have hA0 := mul_nonneg (F.polyInterpConst_nonneg S k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1)) (mul_nonneg hh hL0)
  have e : F.polyInterpBound S k * L * (F.mesh N).meshSize ^ (s + 1) =
      F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L) +
        F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L) := by
    simp only [polyInterpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [hval, e]
  linarith

theorem exists_mem_polyMin_le_of_isCsFormMin {s : ℕ} {j : ℤ} (hS : PolyOrderAt n S s j)
    {L : ℝ} {x : L2F ℝ D.Ω (formIdx n j)} (hx : D.IsCsFormMin s j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (F.polyMin S N).V j,
      ‖x - v‖ ≤ F.polyInterpBound S j * L * (F.mesh N).meshSize ^ (s + 1) ∧
      ∀ j' (hxj : x ∈ (D.complexMin.d j j').domain),
        ‖D.complexMin.d j j'
            ⟨x - v, Submodule.sub_mem _ hxj ((F.polyMin S N).le_domain j j' hv)⟩‖ ≤
          F.polyInterpBound S j * L * (F.mesh N).meshSize ^ (s + 1) := by
  have hh := pow_nonneg (F.meshSize_pos N).le (s + 1)
  have hB0 := mul_nonneg (mul_nonneg (F.polyInterpBound_nonneg S j) hL0) hh
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hsupp, hL, hL', rfl⟩
  · have := LocalElement.subsingleton_L2F_of_neg D.Ω (n := n) hj
    exact (F.polyMin S N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ :=
    F.exists_mem_polyMin_le S N k s (hS k rfl).1 (hS k rfl).2 hw hdeg hsupp hL0 hL0 hL hL'
  have hA0 := mul_nonneg (F.polyInterpConst_nonneg S k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1)) (mul_nonneg hh hL0)
  have e : F.polyInterpBound S k * L * (F.mesh N).meshSize ^ (s + 1) =
      F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L) +
        F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L) := by
    simp only [polyInterpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [F.complexMin_d_formL2 k (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1)))
    hdeg ⟨_, hxj⟩ rfl, e]
  linarith

/-! ### Density of the higher-order complexes -/

theorem eventually_exists_poly_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complex.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.poly S N).V k, ‖x - v‖ < ε ∧
      ‖D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.poly S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth D.isOpen D.isBounded D.s₀_pos D.starBall
    (fun N => F.poly S N) (fun k w hw hdeg => ?_) k x hx hε
  have hw2 : ContDiff ℝ (0 + 2) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_iteratedFDeriv (m := 0 + 1)
    (contDiff_infty.1 hw _)
  have hdw : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) :=
    contDiff_extDeriv (contDiff_infty.1 hw _)
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_iteratedFDeriv (m := 0 + 1) hdw
  refine ⟨fun N => F.polyInterpConst S k * ((F.mesh N).meshSize * L) +
      F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize * L'), by
    have := ((F.tendsto_meshSize.mul_const L).const_mul (F.polyInterpConst S k)).add
      ((F.tendsto_meshSize.mul_const L').const_mul (F.polyInterpConst S (k + 1)))
    simpa using this, fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_poly_le S N k 0 (S.polySpace_zero_le_space k)
    (S.polySpace_zero_le_space (k + 1)) hw2 hdeg hL0 hL'0 hL hL'
  rw [zero_add, pow_one] at hv1 hv2
  have hb1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.polyInterpConst_nonneg S k)
    (mul_nonneg (F.meshSize_pos N).le hL0)
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right hb1), hdv,
    hv2.trans (le_add_of_nonneg_left hb0)⟩

theorem eventually_exists_poly_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.poly S N).V k, ‖x - v‖ < ε :=
  Subcomplex.eventually_exists_lt_of_graph
    (fun k x hx _ hε => F.eventually_exists_poly_graph S k x hx hε) k x hε

theorem eventually_exists_poly_near (i : ℤ) (x : L2F ℝ D.Ω (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.poly S N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (D.complex.d i j).domain),
        ‖D.complex.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.poly S N).le_domain i j hv)⟩‖ <
          ε :=
  Subcomplex.eventually_exists_near_of_graph
    (fun k x hx _ hε => F.eventually_exists_poly_graph S k x hx hε) i x hε

theorem tendsto_infDist_poly (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.poly S N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => F.poly S N) q fun _ ha =>
    F.eventually_exists_poly_lt S j q ha

theorem eventually_exists_polyMin_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complexMin.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.polyMin S N).V k, ‖x - v‖ < ε ∧
      ‖D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.polyMin S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth_min D.isOpen D.isBounded D.s₀_pos D.starBall
    (fun N => F.polyMin S N) (fun k w hw hdeg hsupp => ?_) k x hx hε
  have hw2 : ContDiff ℝ (0 + 2) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_iteratedFDeriv (m := 0 + 1)
    (contDiff_infty.1 hw _)
  have hdw : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) :=
    contDiff_extDeriv (contDiff_infty.1 hw _)
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_iteratedFDeriv (m := 0 + 1) hdw
  refine ⟨fun N => F.polyInterpConst S k * ((F.mesh N).meshSize * L) +
      F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize * L'), by
    have := ((F.tendsto_meshSize.mul_const L).const_mul (F.polyInterpConst S k)).add
      ((F.tendsto_meshSize.mul_const L').const_mul (F.polyInterpConst S (k + 1)))
    simpa using this, fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_polyMin_le S N k 0 (S.polySpace_zero_le_space k)
    (S.polySpace_zero_le_space (k + 1)) hw2 hdeg hsupp hL0 hL'0 hL hL'
  rw [zero_add, pow_one] at hv1 hv2
  have hb1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.polyInterpConst_nonneg S k)
    (mul_nonneg (F.meshSize_pos N).le hL0)
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right hb1), hdv,
    hv2.trans (le_add_of_nonneg_left hb0)⟩

theorem eventually_exists_polyMin_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.polyMin S N).V k, ‖x - v‖ < ε :=
  Subcomplex.eventually_exists_lt_of_graph
    (fun k x hx _ hε => F.eventually_exists_polyMin_graph S k x hx hε) k x hε

theorem tendsto_infDist_polyMin (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.polyMin S N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => F.polyMin S N) q fun _ ha =>
    F.eventually_exists_polyMin_lt S j q ha

end MeshFamily

/-! ### The finite element theorems on `Ω` for the higher-order families -/

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D) [NeZero n] (S : PolySeq)

instance (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((F.poly S N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((F.poly S N).V (a + i)))

instance (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((F.polyMin S N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((F.polyMin S N).V (a + i)))

/-- The complexes of `S` on the mesh family, a conforming family of `HΛ(Ω)`. -/
def polyFamily : ConformingFamily D.complex ℕ :=
  .ofExists atTop (F.poly S)
    (by
      obtain ⟨K, -, hK⟩ := F.exists_uniform_polyProj S
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    (F.tendsto_infDist_poly S)

/-- The complexes of `S` with vanishing boundary DOFs, a conforming family of `H̊Λ(Ω)`. -/
def polyFamilyMin : ConformingFamily D.complexMin ℕ :=
  .ofExists atTop (F.polyMin S)
    (by
      obtain ⟨K, -, hK⟩ := F.exists_uniform_polyProjMin S
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    (F.tendsto_infDist_polyMin S)

@[simp] theorem polyFamily_V : (F.polyFamily S).V = F.poly S := rfl

@[simp] theorem polyFamilyMin_V : (F.polyFamilyMin S).V = F.polyMin S := rfl

/-- The Jackson estimate of order `h_N^{s+1}` of the complexes of `S`. -/
def polyJackson : (F.polyFamily S).Jackson ℕ where
  meshSize N := (F.mesh N).meshSize
  meshSize_nonneg N := (F.meshSize_pos N).le
  tendsto_meshSize := F.tendsto_meshSize
  Reg s j L x := PolyOrderAt n S s j ∧ D.IsCsForm s j L x
  ord s := ((s + 1 : ℕ) : ℝ)
  B _ := F.polyInterpBound S
  B_nonneg _ := F.polyInterpBound_nonneg S
  jackson s N _ _ _ hL hx := by
    rw [Real.rpow_natCast, ← mul_assoc]; exact F.exists_mem_poly_le_of_isCsForm S hx.1 hx.2 hL N

/-- The Jackson estimate of order `h_N^{s+1}` of the complexes of `S` with vanishing DOFs. -/
def polyJacksonMin : (F.polyFamilyMin S).Jackson ℕ where
  meshSize N := (F.mesh N).meshSize
  meshSize_nonneg N := (F.meshSize_pos N).le
  tendsto_meshSize := F.tendsto_meshSize
  Reg s j L x := PolyOrderAt n S s j ∧ D.IsCsFormMin s j L x
  ord s := ((s + 1 : ℕ) : ℝ)
  B _ := F.polyInterpBound S
  B_nonneg _ := F.polyInterpBound_nonneg S
  jackson s N _ _ _ hL hx := by
    rw [Real.rpow_natCast, ← mul_assoc]
    exact F.exists_mem_polyMin_le_of_isCsFormMin S hx.1 hx.2 hL N

theorem mixed_rate_poly_of_polyOrderAt {cP : ℝ} (hP : HasPoincare D.complex cP) {s : ℕ}
    {i j k : ℤ} (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complex.domainSpace i}
    {u : D.complex.domainSpace j} {q : D.complex.harmonic j},
    D.complex.IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    D.IsCsForm s i L (D.complex.domainIncl i σ) →
    D.IsCsForm s j L (D.complex.domainIncl j u) →
    D.IsCsForm s j L (D.complex.domainIncl j
      (D.complex.boundaryPart j (D.complex.domainIncl j u))) →
    D.IsCsForm s j L (q : L2F ℝ D.Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
      ‖u - (F.poly S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
        (F.poly S N) hij hjk f).snd.snd : (F.poly S N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) := by
  obtain ⟨K, hK⟩ := (F.polyFamily S).rate (F.polyJackson S) s hij hjk
    ((D.complex.closedRangeAt_iff_poincare_of_rel hij).2 ⟨cP, hP i j hij⟩)
    ((D.complex.closedRangeAt_iff_poincare_of_rel hjk).2 ⟨cP, hP j k hjk⟩)
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL ⟨hSi, hσ⟩ ⟨hSj, hu⟩ ⟨hSj, hb⟩ ⟨hSj, hq⟩ N
  simp only [polyFamily_V] at h
  rw [← Real.rpow_natCast]
  exact h

/-- Under the Poincaré inequality, the higher-order mixed method converges at the order `h^{s+1}`
for `C^{s+2}` solutions. [AFW2010], Thm 3.9; [Arnold2018], Ch. 7 -/
theorem mixed_rate_poly {cP : ℝ} (hP : HasPoincare D.complex cP) {s : ℕ}
    (hS : PolyOrder n S s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complex.domainSpace i}
    {u : D.complex.domainSpace j} {q : D.complex.harmonic j},
    D.complex.IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    D.IsCsForm s i L (D.complex.domainIncl i σ) →
    D.IsCsForm s j L (D.complex.domainIncl j u) →
    D.IsCsForm s j L (D.complex.domainIncl j
      (D.complex.boundaryPart j (D.complex.domainIncl j u))) →
    D.IsCsForm s j L (q : L2F ℝ D.Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
      ‖u - (F.poly S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
        (F.poly S N) hij hjk f).snd.snd : (F.poly S N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) :=
  F.mixed_rate_poly_of_polyOrderAt S hP (hS.polyOrderAt i) (hS.polyOrderAt j) hij hjk

/-- Convergence of the semi-discrete Hodge wave equation on every window of `HΛ(Ω)` for the
complexes of `S`. [QuennevilleBelair2015], Thm 4.14 -/
theorem exists_tendstoUniformlyOn_window_poly (a : ℤ) (m : ℕ) (t₀ t₁ : ℝ)
    (x : (D.complex.window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → (D.complex.window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((F.poly S N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((F.poly S N).window a m).graphSub)
        ((D.complex.window a m).totalD.toGraphSpace
          ⟨x, ((D.complex.window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => (D.complex.window a m).totalD.graphFst (ξh N t))
        (fun t => (D.complex.window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  Subcomplex.exists_tendstoUniformlyOn_window_of
    (fun i x _ hε => F.eventually_exists_poly_near S i x hε) a m t₀ t₁ x

theorem exists_mem_window_poly_le {s : ℕ} {a : ℤ} {m : ℕ}
    (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i))
    (ζ : (D.complex.window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m, D.IsCsForm s (a + i) L ((D.complex.window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((F.poly S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, F.polyInterpBound S (a + i)) * L *
        (F.mesh N).meshSize ^ (s + 1) :=
  ((F.poly S N).exists_mem_window_graphSub_le ζ (fun i => F.polyInterpBound S (a + i))
    (fun _ => F.polyInterpBound_nonneg _ _) (mul_nonneg hL0 (pow_nonneg (F.meshSize_pos N).le _))
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_poly_le_of_isCsForm S (hS i) (hζ i) hL0 N
      exact ⟨v, hv, h1.trans_eq (mul_assoc _ _ _),
        fun j hx => (h2 j hx).trans_eq (mul_assoc _ _ _)⟩).imp
    fun _ h => ⟨h.1, h.2.trans_eq (mul_assoc _ _ _).symm⟩

theorem norm_sub_le_window_poly_smooth_of_polyOrderAt {s : ℕ} {a : ℤ}
    {m : ℕ} (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i)) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → (D.complex.window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → (D.complex.window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((F.poly S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((F.poly S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      D.IsCsForm s (a + i) L ((D.complex.window a m).totalD.graphFst (ξ τ) i) ∧
        D.IsCsForm s (a + i) L ((D.complex.window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖(D.complex.window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm (D.complex.window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, F.polyInterpBound S (a + i)) * L *
            (F.mesh N).meshSize ^ (s + 1)) :=
  ((F.poly S N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨F.exists_mem_window_poly_le S hS (ξ τ) hL0 (fun i => (hreg τ hτ i).1) N,
      F.exists_mem_window_poly_le S hS (ξ' τ) hL0 (fun i => (hreg τ hτ i).2) N⟩) ht

theorem norm_sub_le_window_poly_smooth {s : ℕ} (hS : PolyOrder n S s) (a : ℤ)
    (m : ℕ) {t₀ t₁ : ℝ} {ξ ξ' : ℝ → (D.complex.window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → (D.complex.window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((F.poly S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((F.poly S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      D.IsCsForm s (a + i) L ((D.complex.window a m).totalD.graphFst (ξ τ) i) ∧
        D.IsCsForm s (a + i) L ((D.complex.window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖(D.complex.window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm (D.complex.window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, F.polyInterpBound S (a + i)) * L *
            (F.mesh N).meshSize ^ (s + 1)) :=
  F.norm_sub_le_window_poly_smooth_of_polyOrderAt S (fun _ => hS.polyOrderAt _) hξ hξh h0 hL0
    hreg N ht

theorem mixed_rate_polyMin_of_polyOrderAt {cP : ℝ} (hP : HasPoincare D.complexMin cP) {s : ℕ}
    {i j k : ℤ} (hSi : PolyOrderAt n S s i) (hSj : PolyOrderAt n S s j)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complexMin.domainSpace i}
    {u : D.complexMin.domainSpace j} {q : D.complexMin.harmonic j},
    D.complexMin.IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    D.IsCsFormMin s i L (D.complexMin.domainIncl i σ) →
    D.IsCsFormMin s j L (D.complexMin.domainIncl j u) →
    D.IsCsFormMin s j L (D.complexMin.domainIncl j
      (D.complexMin.boundaryPart j (D.complexMin.domainIncl j u))) →
    D.IsCsFormMin s j L (q : L2F ℝ D.Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.polyMin S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk f).fst‖ +
      ‖u - (F.polyMin S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
        (F.polyMin S N) hij hjk f).snd.snd : (F.polyMin S N).V j) :
          L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) := by
  obtain ⟨K, hK⟩ := (F.polyFamilyMin S).rate (F.polyJacksonMin S) s hij hjk
    ((D.complexMin.closedRangeAt_iff_poincare_of_rel hij).2 ⟨cP, hP i j hij⟩)
    ((D.complexMin.closedRangeAt_iff_poincare_of_rel hjk).2 ⟨cP, hP j k hjk⟩)
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL ⟨hSi, hσ⟩ ⟨hSj, hu⟩ ⟨hSj, hb⟩ ⟨hSj, hq⟩ N
  simp only [polyFamilyMin_V] at h
  rw [← Real.rpow_natCast]
  exact h

theorem mixed_rate_polyMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) {s : ℕ}
    (hS : PolyOrder n S s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complexMin.domainSpace i}
    {u : D.complexMin.domainSpace j} {q : D.complexMin.harmonic j},
    D.complexMin.IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    D.IsCsFormMin s i L (D.complexMin.domainIncl i σ) →
    D.IsCsFormMin s j L (D.complexMin.domainIncl j u) →
    D.IsCsFormMin s j L (D.complexMin.domainIncl j
      (D.complexMin.boundaryPart j (D.complexMin.domainIncl j u))) →
    D.IsCsFormMin s j L (q : L2F ℝ D.Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.polyMin S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk f).fst‖ +
      ‖u - (F.polyMin S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
        (F.polyMin S N) hij hjk f).snd.snd : (F.polyMin S N).V j) :
          L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) :=
  F.mixed_rate_polyMin_of_polyOrderAt S hP (hS.polyOrderAt i) (hS.polyOrderAt j) hij hjk

theorem exists_mem_windowMin_poly_le {s : ℕ} {a : ℤ} {m : ℕ}
    (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i))
    (ζ : (D.complexMin.window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m,
      D.IsCsFormMin s (a + i) L ((D.complexMin.window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((F.polyMin S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, F.polyInterpBound S (a + i)) * L *
        (F.mesh N).meshSize ^ (s + 1) :=
  ((F.polyMin S N).exists_mem_window_graphSub_le ζ (fun i => F.polyInterpBound S (a + i))
    (fun _ => F.polyInterpBound_nonneg _ _) (mul_nonneg hL0 (pow_nonneg (F.meshSize_pos N).le _))
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_polyMin_le_of_isCsFormMin S (hS i) (hζ i) hL0 N
      exact ⟨v, hv, h1.trans_eq (mul_assoc _ _ _),
        fun j hx => (h2 j hx).trans_eq (mul_assoc _ _ _)⟩).imp
    fun _ h => ⟨h.1, h.2.trans_eq (mul_assoc _ _ _).symm⟩

theorem norm_sub_le_windowMin_poly_smooth_of_polyOrderAt {s : ℕ} {a : ℤ}
    {m : ℕ} (hS : ∀ i : Fin m, PolyOrderAt n S s (a + i)) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → (D.complexMin.window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → (D.complexMin.window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((F.polyMin S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((F.polyMin S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      D.IsCsFormMin s (a + i) L ((D.complexMin.window a m).totalD.graphFst (ξ τ) i) ∧
        D.IsCsFormMin s (a + i) L ((D.complexMin.window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖(D.complexMin.window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm (D.complexMin.window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, F.polyInterpBound S (a + i)) * L *
            (F.mesh N).meshSize ^ (s + 1)) :=
  ((F.polyMin S N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨F.exists_mem_windowMin_poly_le S hS (ξ τ) hL0 (fun i => (hreg τ hτ i).1) N,
      F.exists_mem_windowMin_poly_le S hS (ξ' τ) hL0 (fun i => (hreg τ hτ i).2) N⟩) ht

end MeshFamily

end Feec.Models.StarShaped
