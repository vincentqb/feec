module

public import Feec.Models.Cube.PolySmoothingEstimates
public import Feec.Models.Cube.FiniteElementConvergence
public import Feec.HilbertComplex.Approximation.DiscreteCohomology

/-!
# The higher-order finite element methods on the cube as conforming families

For every admissible sequence `S` of `P_rΛᵏ` / `P_r⁻Λᵏ` families (`Feec.FiniteElement.PolySeq`) on
the level-`(N + 1)` Freudenthal meshes of `Q = (0, ½)ⁿ`, with the complexes `FEM.poly n S N ⊆ HΛ(Q)`
and `FEM.polyMin n S N ⊆ H̊Λ(Q)` (vanishing boundary DOFs), this module proves the analogues of
`Feec.Models.Cube.FiniteElementMethod`, `Feec.Models.Cube.WhitneyApprox` and
`Feec.Models.Cube.FiniteElementConvergence`, with no hypothesis beyond the data:

* **Interpolation error of order `h^{s+1}`** ([Arnold2018], Ch. 7; [Ciarlet2002], Thm 3.1.4):
  pointwise on each simplex by the Bramble–Hilbert argument with the DOF bound and the DOF
  stability of `Feec.Models.Cube.PolySmoothingEstimates` (`Poly.abs_sub_globalInterp_le`: the
  degree-`k` part of a Taylor polynomial lies in `P_sΛᵏ ⊆ P(T)ᵏ`, `Poly.exists_polySpace_near`), and
  in `L²` and in the graph norm on the cube (`exists_mem_poly_le`, `exists_mem_polyMin_le`, with
  `d Π_h = Π_h d`).
* **Density** of the higher-order spaces in `HΛ(Q)`, `H̊Λ(Q)` and in the graph spaces of every
  window (`eventually_exists_poly_graph`, `dense_window_poly`, and `Min` versions), so the
  semi-discrete Hodge wave equation converges on every window for `D(L)` data
  (`exists_tendstoUniformlyOn_window_poly`; [QuennevilleBelair2015], Thm 4.14).
* Under the smoothing estimates (proved for all small `γ` in
  `Feec.Models.Cube.PolySmoothingEstimates`): **uniformly bounded cochain projections**
  `π_N = J_N⁻¹ Q_N` with `‖π_N‖ ≤ 2C` in `L²` (`PolySmoothingEstimates.proj`,
  `PolySmoothingEstimates.norm_proj_le`), so the complexes of `S` are **conforming families**
  (`PolySmoothingEstimates.family`, `ConformingFamily.ofSmoothing`; with the estimates of
  `polySmoothingEstimates_exists`, `polyFamily`, `polyFamilyMin`). With the closed range of
  `HΛ(Q)`, `H̊Λ(Q)` (`Feec.Models.Cube.DeRhamIdentFEM`) the static FEEC theorem
  (`Feec.HilbertComplex.ConformingFamily.staticFEEC`) gives, unconditionally, the uniform discrete
  Poincaré inequality ([AFW2010], Thm 3.6), uniform well-posedness and stability of the discrete
  mixed Hodge Laplacian (Thm 3.8), the vanishing harmonic gap, the discrete cohomology,
  quasi-optimality (Thm 3.9) and convergence; the rates are in `Feec.Models.Cube.PolyRate`.
* **The rows of Tables 5.1 and 6.1** of [QuennevilleBelair2015] (§5.3, §6.3) on `(0, ½)³` with
  vanishing boundary DOFs, the top row `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²` (`PolySeq.lowestOrder`, and the
  Whitney complex) and the bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` (`PolySeq.lagrangeP2`), **share
  one smoother** (`tableRows_common_smoother`) and carry uniformly bounded cochain projections built
  from the same smoothed fields (`tableRows_uniform_cochainProjection`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (discrete Poincaré inequality, Thm 3.6; cohomology, Thm 3.4), Thm 3.8 (stability),
  Thm 3.9 (quasi-optimality), §5.5 (smoothed projections), §5.6 (cohomology of the finite element
  de Rham complexes)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates, density)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.4
  (interpolation error)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation); §5.3, Table 5.1; §6.3,
  Table 6.1

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

/-- `P_sΛᵏ ⊆ P_{r_k}Λᵏ` and `⊆ P_{r_k}⁻Λᵏ` for `s + 1 ≤ r_k`. -/
theorem polySpace_le_space {k s : ℕ} (hs : s + 1 ≤ S.deg k) :
    polySpace n s k ≤ S.space n k := by
  change polySpace n s k ≤ (S.kind k).space n (S.deg k) k
  cases S.kind k
  · exact polySpace_mono (by omega)
  · exact (polySpace_mono (by omega)).trans (polySpace_le_polyMinusSpace (S.deg k) k)

/-- `P_sΛᵏ ⊆ P_{r_k}Λᵏ` for `s ≤ r_k` when the sequence uses the full family in degree `k`. -/
theorem polySpace_le_space_of_full {k s : ℕ} (hk : S.kind k = .full) (hs : s ≤ S.deg k) :
    polySpace n s k ≤ S.space n k := by
  change polySpace n s k ≤ (S.kind k).space n (S.deg k) k
  rw [hk]
  exact polySpace_mono hs

theorem degPartField_taylorPoly_mem {k s : ℕ} (w : FormField n) (x₀ : Fin n → ℝ) :
    degPartField k (taylorPoly w x₀ (s + 1)) ∈ polySpace n s k :=
  degPartField_mem_polySpace (taylorPoly_mem_polyFunctions w x₀ s) k

/-- **Taylor approximation on a mesh simplex**: for a `C^{s+1}` degree-`k` field `w` with
`‖D^{s+1} w‖ ≤ M` on `T`, the degree-`k` part `P` of its Taylor polynomial of order `s` at a
vertex is a polynomial form of degree `s` with `‖w - P‖ ≤ h_N^{s+1} M` on `T`. -/
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

/-- **The local interpolation error of the higher-order families**, pointwise: for a mesh
simplex `T`, a degree `s` with `P_sΛᵏ ⊆ P(T)ᵏ` and a `C^{s+1}` degree-`k` field `w` with
`‖D^{s+1} w‖ ≤ M` on `T`, `|w - Π_T w| ≤ (1 + B dim D) h_N^{s+1} M` on `T` (Bramble–Hilbert
through the DOF bound `DofBound` and the DOF stability `abs_dof_le`). -/
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

/-! ### The global `L²` interpolation error -/

/-- **A pointwise bound on the simplex interiors bounds the `L²` distance** between a continuous
form and a glued piecewise field (any element family). -/
theorem norm_formL2_sub_glue_le_of_forall (E : LocalElement n) (M : SimplicialMesh n)
    (hΩ : MeasurableSet M.domain) (k : ℕ) (w : contForms n) (u : E.Piecewise M k) {B : ℝ}
    (hB : 0 ≤ B)
    (hpt : ∀ (T : M.simplices), ∀ x ∈ interior (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ∀ s : Finset (Fin n), #s = k →
        |(w : FormField n) x s - ((u T : E.space T k) : FormField n) x s| ≤ B) :
    ‖formL2 hΩ M.isBounded_domain k w - E.glue M k u‖ ≤
      Fintype.card (formIdx n k) * (volume.real M.domain ^ (1 / 2 : ℝ) * B) := by
  have : IsFiniteMeasure (volume.restrict M.domain) :=
    isFiniteMeasure_restrict.2 M.isBounded_domain.measure_lt_top.ne
  rw [LocalElement.glue_apply]
  refine L2F.norm_le_card_mul _ (by positivity) fun s => ?_
  refine (Lp.norm_le_of_ae_bound hB ?_).trans (le_of_eq ?_)
  · have hcont : ∀ T ∈ M.simplices, ∀ s : formIdx n k,
        Continuous (formComp (k := (k : ℤ)) (E.extendPW M u T) s) :=
      fun T hT s => continuous_formComp (E.contDiff_extendPW M u hT).continuous s
    filter_upwards [Lp.coeFn_sub (formL2 hΩ M.isBounded_domain k w s)
      (pieceL2 M M.domain (fun T => formComp (k := (k : ℤ)) (E.extendPW M u T))
        hcont s), coeFn_formL2 hΩ M.isBounded_domain k w s,
      coeFn_pieceL2 (𝕜 := ℝ) M M.domain _ hcont s, Feec.FiniteElement.ae_mem_interior M hΩ]
      with x h1 h2 h3 hx
    obtain ⟨T, hT, hxT⟩ := hx
    rw [PiLp.sub_apply, h1, Pi.sub_apply, h2, h3, pieceFun_of_mem_interior M _ hT hxT]
    change ‖(w : FormField n) x s.1 - E.extendPW M _ T x s.1‖ ≤ B
    rw [LocalElement.extendPW_of_mem _ _ _ hT, Real.norm_eq_abs]
    have hs : #s.1 = k := by exact_mod_cast s.2
    exact hpt ⟨T, hT⟩ x hxT s.1 hs
  · rw [measureUnivNNReal, Measure.restrict_apply_univ, ENNReal.toReal_ofNat, one_div]
    rfl

/-- **`Π_h` commutes with `d` in `L²`** (any element family): for a `C¹` form `w`,
`Π_h w ∈ D(d_max)` and `d_max Π_h w = Π_h dw` (glued). -/
theorem glue_globalInterp_mem_maximal_of [NeZero n] (E : LocalElement n) (M : SimplicialMesh n)
    (hΩo : IsOpen M.domain) (k : ℕ) (w : c1Forms n) :
    ∃ h : E.glue M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) :
        E.Piecewise M k) ∈ ((extDerivOp ℝ n k).maximal M.domain).domain,
      (extDerivOp ℝ n k).maximal M.domain ⟨_, h⟩ =
        E.glue M ((k : ℤ) + 1) (E.globalInterp M (k + 1) (extDerivC1 w) : E.Piecewise M (k + 1)) := by
  obtain ⟨h, hval⟩ := E.glue_mem_maximal M hΩo k
    (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w))
  refine ⟨h, hval.trans ?_⟩
  have h1 : E.dPiecewise M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) :
      E.Piecewise M k) = (E.dGlobal M k (E.globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms w)) : E.Piecewise M (k + 1)) := rfl
  rw [h1, ← LocalElement.globalInterp_extDeriv]

/-! ### Interpolation of smooth forms on the cube meshes -/

variable (n) in
/-- The DOF constant `B_k` of the sequence `S` (`Poly.DofBound`). -/
def dofConst (S : PolySeq) (k : ℕ) : ℝ := (Poly.exists_dofBound (n := n) S k).choose

variable (n) in
/-- The constant `D_k` of the coefficient fields of the degrees of freedom of `S`
(`Poly.CoeffBound`). -/
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
/-- The constant of the `L²` interpolation estimate of degree `k` of the sequence `S` on the cube
meshes: `#Λᵏ |Q|^{1/2} (1 + B_k dim(P_{r_k}Λᵏ) D_k)`, independent of the mesh and of the order. -/
def polyInterpConst (S : PolySeq) (k : ℕ) : ℝ :=
  Fintype.card (formIdx n k) * (volume.real (cubeDomain n) ^ (1 / 2 : ℝ) *
    (1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k))

theorem polyInterpConst_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ polyInterpConst n S k := by
  unfold polyInterpConst
  have := dofConst_nonneg (n := n) S k
  have := coeffConst_nonneg (n := n) S k
  positivity

/-- **The pointwise interpolation error on the cube meshes**: for `w ∈ C^{s+1}` of degree `k`
with `‖D^{s+1} w‖ ≤ L` on `cl Q` and `P_sΛᵏ ⊆ P(T)ᵏ`, on every closed simplex,
`|w - Π_h w| ≤ (1 + B dim D) h_N^{s+1} L`. -/
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

/-- **The `L²` interpolation error of the higher-order families on the cube meshes** at order
`s + 1` ([Arnold2018], Ch. 7; [Ciarlet2002], Thm 3.1.4): for a `C^{s+2}` degree-`k` form `w`
with `‖D^{s+1} w‖ ≤ L` and `‖D^{s+1} dw‖ ≤ L'` on `cl Q`, and `P_sΛᵏ ⊆ P(T)ᵏ`,
`P_sΛᵏ⁺¹ ⊆ P(T)ᵏ⁺¹` (e.g. `s + 1 ≤ r_k, r_{k+1}`), the canonical interpolant `v = Π_N w` of the
complex of `S` satisfies `‖w - v‖ ≤ A_k h_N^{s+1} L` and `‖dw - dv‖ ≤ A_{k+1} h_N^{s+1} L'`. -/
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
  refine (deRham ℝ n).maximalSubcomplexOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (S.subcomplex (mesh n N) (isOpen_mesh_domain n N))
    (fun Θ hΘ S' => ∀ hb : Bornology.IsBounded Θ,
      ∀ hvol : volume.real Θ = volume.real (cubeDomain n),
      ∃ v ∈ S'.V k,
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - asForm n v‖ ≤
          polyInterpConst n S k * (meshSize N ^ (s + 1) * L) ∧
        ∃ hv : v ∈ (((deRham ℝ n).maximalComplex hΘ).d k (k + 1)).domain,
          ‖formL2 hΘ.measurableSet hb ((k : ℤ) + 1)
              ⟨extDeriv w, continuous_extDeriv hw1⟩ -
            asForm n (((deRham ℝ n).maximalComplex hΘ).d k (k + 1) ⟨v, hv⟩)‖ ≤
            polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L')) ?_
    (isBounded_cubeDomain n) rfl
  intro hb hvol
  set M := mesh n N
  have hΩo := isOpen_mesh_domain n N
  set u := (polyElement n S).globalInterp M k (Submodule.inclusion c1Forms_le_contForms
    (⟨w, hw1⟩ : c1Forms n))
  obtain ⟨hmem, hval⟩ := glue_globalInterp_mem_maximal_of (polyElement n S) M hΩo k ⟨w, hw1⟩
  have hB1 : 0 ≤ (1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k) *
      (meshSize N ^ (s + 1) * L) := by
    have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k
    have := (meshSize_pos N).le; positivity
  have hB2 : 0 ≤ (1 + dofConst n S (k + 1) * Module.finrank ℝ (S.space n (k + 1)) *
      coeffConst n S (k + 1)) * (meshSize N ^ (s + 1) * L') := by
    have := dofConst_nonneg (n := n) S (k + 1); have := coeffConst_nonneg (n := n) S (k + 1)
    have := (meshSize_pos N).le; positivity
  refine ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k), ⟨u, rfl⟩, ?_, ?_⟩
  · have h := norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet k
      ⟨w, hw.continuous⟩ (u : (polyElement n S).Piecewise M k) hB1
      fun T x hx t _ => abs_sub_globalInterp_le_cube S hs hws hdeg hL T (interior_subset hx) t
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; ring
  · refine ⟨by rw [deRham_maximalComplex_d]; exact hmem, ?_⟩
    rw [LinearPMap.apply_eq_of_eq' (deRham_maximalComplex_d hΩo (k : ℤ))]
    have h := norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet (k + 1)
      ⟨extDeriv w, hdw.continuous⟩ ((polyElement n S).globalInterp M (k + 1)
        ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) hB2
      fun T x hx t _ => abs_sub_globalInterp_le_cube S hs' hdw hdeg' hL' T (interior_subset hx) t
    have e : (extDerivOp ℝ n k).maximal M.domain
        ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k), hmem⟩ =
        (polyElement n S).glue M ((k + 1 : ℕ) : ℤ) ((polyElement n S).globalInterp M (k + 1)
          ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) := hval
    erw [e]
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; push_cast; ring

/-- **Interpolation error with vanishing boundary DOFs**: for a `C^{s+2}` form `w` vanishing
outside `Q`, the canonical interpolant lies in `V̊ₕᵏ ⊆ H̊Λᵏ(Q)` with the estimates of
`exists_mem_poly_le`. -/
theorem exists_mem_polyMin_le (S : PolySeq) (N k s : ℕ) (hs : polySpace n s k ≤ S.space n k)
    (hs' : polySpace n s (k + 1) ≤ S.space n (k + 1)) {w : FormField n}
    (hw : ContDiff ℝ (s + 2) w) (hdeg : ∀ x, IsDeg k (w x))
    (hsupp : ∀ x ∉ cubeDomain n, w x = 0) {L L' : ℝ}
    (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L)
    (hL' : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (polyMin n S N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ polyInterpConst n S k * (meshSize N ^ (s + 1) * L) ∧
      ∃ hv : v ∈ ((complexMin n).d k (k + 1)).domain,
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by
              exact_mod_cast Nat.le_add_left 1 (s + 1)))⟩ -
          (complexMin n).d k (k + 1) ⟨v, hv⟩‖ ≤
            polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))
  have hws : ContDiff ℝ (s + 1) w := hw.of_le (by exact_mod_cast Nat.le_succ (s + 1))
  have hdw : ContDiff ℝ (s + 1) (extDeriv w) := contDiff_extDeriv (m := s + 1) (by
    exact_mod_cast hw)
  have hdw1 : ContDiff ℝ 1 (extDeriv w) := hdw.of_le (by exact_mod_cast Nat.le_add_left 1 s)
  have hdeg' : ∀ x, IsDeg (k + 1) (extDeriv w x) := fun x => IsDeg.extDeriv hdeg x
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL _ (subset_closure (center_mem_cubeDomain n)))
  have hL'0 : 0 ≤ L' := (norm_nonneg _).trans (hL' _ (subset_closure (center_mem_cubeDomain n)))
  refine (deRham ℝ n).minimalSubcomplexOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (S.subcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))
    (fun Θ hΘ S' => ∀ hb : Bornology.IsBounded Θ,
      ∀ hvol : volume.real Θ = volume.real (cubeDomain n),
      ∃ v ∈ S'.V k,
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - asForm n v‖ ≤
          polyInterpConst n S k * (meshSize N ^ (s + 1) * L) ∧
        ∃ hv : v ∈ (((deRham ℝ n).minimalComplex hΘ).d k (k + 1)).domain,
          ‖formL2 hΘ.measurableSet hb ((k : ℤ) + 1)
              ⟨extDeriv w, continuous_extDeriv hw1⟩ -
            asForm n (((deRham ℝ n).minimalComplex hΘ).d k (k + 1) ⟨v, hv⟩)‖ ≤
            polyInterpConst n S (k + 1) * (meshSize N ^ (s + 1) * L')) ?_
    (isBounded_cubeDomain n) rfl
  intro hb hvol
  set M := mesh n N
  have hΩo := isOpen_mesh_domain n N
  set w' : c1Forms n := ⟨w, hw1⟩
  set u := (polyElement n S).globalInterp M k (Submodule.inclusion c1Forms_le_contForms w')
  have hu₀ : (u : (polyElement n S).Piecewise M k) ∈ (polyElement n S).globalSpace₀ M k :=
    LocalElement.globalInterp_mem_globalSpace₀ _ M k fun x hx => hsupp x (by
      rw [← mesh_domain n N]; exact M.notMem_domain_of_mem_frontier hΩo hx)
  obtain ⟨hmem, hval⟩ := (polyElement n S).glue_mem_minimal M hΩo (center n)
    (strictStar_mesh n N) k ⟨_, hu₀⟩
  have hB1 : 0 ≤ (1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k) *
      (meshSize N ^ (s + 1) * L) := by
    have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k
    have := (meshSize_pos N).le; positivity
  have hB2 : 0 ≤ (1 + dofConst n S (k + 1) * Module.finrank ℝ (S.space n (k + 1)) *
      coeffConst n S (k + 1)) * (meshSize N ^ (s + 1) * L') := by
    have := dofConst_nonneg (n := n) S (k + 1); have := coeffConst_nonneg (n := n) S (k + 1)
    have := (meshSize_pos N).le; positivity
  refine ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k),
    ⟨⟨_, hu₀⟩, rfl⟩, ?_, ?_⟩
  · have h := norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet k
      ⟨w, hw.continuous⟩ (u : (polyElement n S).Piecewise M k) hB1
      fun T x hx t _ => abs_sub_globalInterp_le_cube S hs hws hdeg hL T (interior_subset hx) t
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; ring
  · refine ⟨by rw [deRham_minimalComplex_d]; exact hmem, ?_⟩
    rw [LinearPMap.apply_eq_of_eq' (deRham_minimalComplex_d hΩo (k : ℤ))]
    have h := norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet (k + 1)
      ⟨extDeriv w, hdw.continuous⟩ ((polyElement n S).globalInterp M (k + 1)
        ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) hB2
      fun T x hx t _ => abs_sub_globalInterp_le_cube S hs' hdw hdeg' hL' T (interior_subset hx) t
    have h1 : (polyElement n S).dPiecewise M k (u : (polyElement n S).Piecewise M k) =
        ((polyElement n S).dGlobal M k u : (polyElement n S).Piecewise M (k + 1)) := rfl
    have e : (extDerivOp ℝ n k).minimal M.domain
        ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k), hmem⟩ =
        (polyElement n S).glue M ((k + 1 : ℕ) : ℤ) ((polyElement n S).globalInterp M (k + 1)
          ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) := by
      rw [hval]
      change (polyElement n S).glue M ((k : ℤ) + 1)
        ((polyElement n S).dPiecewise M k (u : (polyElement n S).Piecewise M k)) = _
      rw [h1, ← LocalElement.globalInterp_extDeriv]
      rfl
    erw [e]
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; push_cast; ring

/-! ### Density of the higher-order complexes -/

omit [NeZero n] in
/-- A `C^m` form has a bounded `m`-th derivative on the compact `cl Q`. -/
theorem exists_bound_iteratedFDeriv {m : ℕ} {w : FormField n} (hw : ContDiff ℝ m w) :
    ∃ L, 0 ≤ L ∧ ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ m w y‖ ≤ L := by
  obtain ⟨L, hL⟩ := (isCompact_closure_cubeDomain n).exists_bound_of_continuousOn
    (hw.continuous_iteratedFDeriv le_rfl).continuousOn
  exact ⟨max L 0, le_max_right _ _, fun y hy => (hL y hy).trans (le_max_left _ _)⟩

omit [NeZero n] in
theorem polySpace_zero_le_space (S : PolySeq) (k : ℕ) : polySpace n 0 k ≤ S.space n k :=
  Poly.polySpace_le_space S (by have := S.one_le_deg k; omega)

/-- **Graph-norm density of the higher-order spaces in `HΛᵏ(Q)`**: every `x ∈ D(d)` is the limit,
in the graph norm, of points of the spaces `Vₕᵏ` of `S` on the Freudenthal meshes. -/
theorem eventually_exists_poly_graph (S : PolySeq) (k : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n k))
    (hx : x ∈ ((complex n).d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (poly n S N).V k, ‖x - v‖ < ε ∧
      ‖(complex n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((poly n S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  rcases k with k | k
  swap
  · have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine Eventually.of_forall fun N => ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε
  change ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (poly n S N).V (k : ℤ), ‖x - v‖ < ε ∧
      ‖(complex n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((poly n S N).le_domain k (k + 1) hv)⟩‖ < ε
  refine eventually_exists_graph_of_near (fun N => poly n S N) hx (fun ε hε => ?_) hε
  obtain ⟨w, hw, hdeg, h1, h2⟩ := exists_smooth_near k ⟨x, hx⟩ hε
  have hw2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := exists_bound_iteratedFDeriv
    (hw.of_le (WithTop.coe_le_coe.2 le_top) : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) w)
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_iteratedFDeriv (m := 1)
    (contDiff_extDeriv (m := 1) (hw.of_le (WithTop.coe_le_coe.2 le_top)))
  refine ⟨_, _, fun N => polyInterpConst n S k * (meshSize N ^ (0 + 1) * L) +
    polyInterpConst n S (k + 1) * (meshSize N ^ (0 + 1) * L'), h1, h2, by
      simpa using (((tendsto_meshSize.pow 1).mul_const L).const_mul (polyInterpConst n S k)).add
        (((tendsto_meshSize.pow 1).mul_const L').const_mul (polyInterpConst n S (k + 1))),
    fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := exists_mem_poly_le S N k 0 (polySpace_zero_le_space S k)
    (polySpace_zero_le_space S (k + 1)) hw2 hdeg hL hL'
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right (mul_nonneg (polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (pow_nonneg (meshSize_pos N).le _) hL'0))), hv2.trans (le_add_of_nonneg_left
      (mul_nonneg (polyInterpConst_nonneg S k) (mul_nonneg (pow_nonneg (meshSize_pos N).le _)
        hL0)))⟩

/-- **`L²` density of the higher-order spaces** `Vₕᵏ` in `L²(Q; Λᵏ)`. -/
theorem eventually_exists_poly_lt (S : PolySeq) (k : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n k))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (poly n S N).V k, ‖x - v‖ < ε :=
  eventually_exists_lt_of_graph
    (fun k x hx _ hε => eventually_exists_poly_graph S k x hx hε) k x hε

/-- Degreewise approximation in every graph norm of `HΛ(Q)` by the higher-order spaces. -/
theorem eventually_exists_poly_near (S : PolySeq) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (poly n S N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ ((complex n).d i j).domain),
        ‖(complex n).d i j ⟨x - v, Submodule.sub_mem _ hx ((poly n S N).le_domain i j hv)⟩‖ <
          ε :=
  eventually_exists_near_of_graph
    (fun k x hx _ hε => eventually_exists_poly_graph S k x hx hε) i x hε

/-- `dist(q, Vₕʲ) → 0` for every `q ∈ L²(Q; Λʲ)` (higher-order spaces). -/
theorem tendsto_infDist_poly (S : PolySeq) (j : ℤ) (q : L2F ℝ (cubeDomain n) (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((poly n S N).V j :
      Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0) :=
  tendsto_infDist_of_lt (S := fun N => poly n S N) q fun _ ha =>
    eventually_exists_poly_lt S j q ha

instance (S : PolySeq) (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((poly n S N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((poly n S N).V (a + i)))

instance (S : PolySeq) (N : ℕ) (a : ℤ) (m : ℕ) :
    FiniteDimensional ℝ ((poly n S N).window a m).graphSub :=
  inferInstance

/-- **The windows of the higher-order complexes approximate every point of the graph space** of
the total differential of every window of `HΛ(Q)`. -/
theorem dense_window_poly (S : PolySeq) (a : ℤ) (m : ℕ) :
    ∀ ζ : ((complex n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((poly n S N).window a m).graphSub, ‖ζ - w‖ < δ := fun ζ _ hδ =>
  Subcomplex.eventually_exists_graphSub_lt (fun N => (poly n S N).window a m)
    (fun i x _ hε => (eventually_exists_poly_near S (a + i) x hε).mono fun _ hN => by
      obtain ⟨v, hv, h1, h2⟩ := hN
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩) ζ hδ

/-- **Convergence of the semi-discrete Hodge wave equation for the higher-order complexes**, on
every window of `HΛ(Q)` and for `D(L)` data, unconditionally ([QuennevilleBelair2015],
Thm 4.14). -/
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

omit [NeZero n] in
/-- `formL2` of degree `j` only sees the degree-`j` part. -/
theorem formL2_degField {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (j : ℕ) {j' : ℤ} (hj : (j : ℤ) = j') {w : FormField n} (hw : Continuous w) :
    formL2 hΩ hb j' ⟨degField j w, continuous_degField j hw⟩ = formL2 hΩ hb j' ⟨w, hw⟩ := by
  refine PiLp.ext fun s => Lp.ext ?_
  filter_upwards [coeFn_formL2 hΩ hb j' ⟨degField j w, continuous_degField j hw⟩ s,
    coeFn_formL2 hΩ hb j' ⟨w, hw⟩ s] with x h1 h2
  rw [h1, h2]
  have hs : #s.1 = j := by have := s.2; omega
  simp [degField, hs]

omit [NeZero n] in
/-- `exists_smooth_near_min` with a smooth form of degree `k`. -/
theorem exists_smooth_near_min_deg (k : ℕ) (u : ((complexMin n).d k (k + 1)).domain) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ w : FormField n, ∃ hw : ContDiff ℝ ∞ w, (∀ x, IsDeg k (w x)) ∧
      (∀ x ∉ cubeDomain n, w x = 0) ∧
      ‖(u : L2F ℝ (cubeDomain n) (formIdx n k)) -
          formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
            ⟨w, hw.continuous⟩‖ < ε ∧
      ‖(complexMin n).d k (k + 1) u -
          formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩‖ < ε := by
  obtain ⟨w, hw, hsupp, h1, h2⟩ := exists_smooth_near_min k u hε
  have hw' : ContDiff ℝ ∞ (degField k w) := contDiff_degField k hw
  refine ⟨degField k w, hw', isDeg_degField k w, fun x hx => ?_, ?_, ?_⟩
  · funext s; simp [degField, hsupp x hx]
  · rw [formL2_degField _ _ k rfl hw.continuous]; exact h1
  · have e : formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
        ⟨extDeriv (degField k w), continuous_extDeriv (hw'.of_le (by exact_mod_cast le_top))⟩ =
        formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ := by
      rw [← formL2_degField _ _ (k + 1) (by push_cast; rfl)
        (continuous_extDeriv (hw.of_le (by exact_mod_cast le_top)))]
      exact formL2_congr _ _ _ fun x _ => congrFun (extDeriv_degField k w) x
    rw [e]; exact h2

/-- **Graph-norm density of the higher-order spaces with vanishing boundary DOFs in
`H̊Λᵏ(Q)`**. -/
theorem eventually_exists_polyMin_graph (S : PolySeq) (k : ℤ)
    (x : L2F ℝ (cubeDomain n) (formIdx n k))
    (hx : x ∈ ((complexMin n).d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (polyMin n S N).V k, ‖x - v‖ < ε ∧
      ‖(complexMin n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((polyMin n S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  rcases k with k | k
  swap
  · have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine Eventually.of_forall fun N => ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε
  change ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (polyMin n S N).V (k : ℤ), ‖x - v‖ < ε ∧
      ‖(complexMin n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((polyMin n S N).le_domain k (k + 1) hv)⟩‖ < ε
  refine eventually_exists_graph_of_near (fun N => polyMin n S N) hx (fun ε hε => ?_) hε
  obtain ⟨w, hw, hdeg, hsupp, h1, h2⟩ := exists_smooth_near_min_deg k ⟨x, hx⟩ hε
  have hw2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := exists_bound_iteratedFDeriv
    (hw.of_le (WithTop.coe_le_coe.2 le_top) : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) w)
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_iteratedFDeriv (m := 1)
    (contDiff_extDeriv (m := 1) (hw.of_le (WithTop.coe_le_coe.2 le_top)))
  refine ⟨_, _, fun N => polyInterpConst n S k * (meshSize N ^ (0 + 1) * L) +
    polyInterpConst n S (k + 1) * (meshSize N ^ (0 + 1) * L'), h1, h2, by
      simpa using (((tendsto_meshSize.pow 1).mul_const L).const_mul (polyInterpConst n S k)).add
        (((tendsto_meshSize.pow 1).mul_const L').const_mul (polyInterpConst n S (k + 1))),
    fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := exists_mem_polyMin_le S N k 0 (polySpace_zero_le_space S k)
    (polySpace_zero_le_space S (k + 1)) hw2 hdeg hsupp hL hL'
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right (mul_nonneg (polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (pow_nonneg (meshSize_pos N).le _) hL'0))), hv2.trans (le_add_of_nonneg_left
      (mul_nonneg (polyInterpConst_nonneg S k) (mul_nonneg (pow_nonneg (meshSize_pos N).le _)
        hL0)))⟩

/-- **`L²` density of the higher-order spaces with vanishing boundary DOFs**. -/
theorem eventually_exists_polyMin_lt (S : PolySeq) (k : ℤ)
    (x : L2F ℝ (cubeDomain n) (formIdx n k)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v ∈ (polyMin n S N).V k, ‖x - v‖ < ε :=
  eventually_exists_lt_of_graph
    (fun k x hx _ hε => eventually_exists_polyMin_graph S k x hx hε) k x hε

/-- `dist(q, V̊ₕʲ) → 0` for every `q ∈ L²(Q; Λʲ)` (higher-order spaces). -/
theorem tendsto_infDist_polyMin (S : PolySeq) (j : ℤ) (q : L2F ℝ (cubeDomain n) (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((polyMin n S N).V j :
      Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0) :=
  tendsto_infDist_of_lt (S := fun N => polyMin n S N) q fun _ ha =>
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

/-- **The smoothed projection** `π_N = J_N⁻¹ Q_N` onto the complex of `S` on the cube. -/
def proj (hE : PolySmoothingEstimates n S p C) (N : ℕ) : (poly n S N).CochainProjection :=
  (polySmoothed n S N (p N) (hE.isMaximal N)).toCochainProjection (θ := 1 / 2) (by norm_num)
    (hE.close N)

theorem two_mul_nonneg (hE : PolySmoothingEstimates n S p C) : 0 ≤ 2 * C := by
  linarith [hE.half_le]

variable (hE : PolySmoothingEstimates n S p C)
include hE

/-- **Uniform `L²` bound**: `‖π_N x‖ ≤ 2 C ‖x‖` for every `N`. -/
theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ := by
  have h := (polySmoothed n S N (p N) (hE.isMaximal N)).norm_toCochainProjection_le
    (θ := 1 / 2) (by norm_num) (hE.close N) (hE.bound N i) x
  have e : (1 - 1 / 2 : ℝ)⁻¹ * C = 2 * C := by norm_num
  rwa [e] at h

end PolySmoothingEstimates

namespace PolySmoothingEstimatesMin

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- **The smoothed projection** `π̊_N = J_N⁻¹ Q̊_N` onto the complex of `S` with vanishing
boundary DOFs. -/
def proj (hE : PolySmoothingEstimatesMin n S p C) (N : ℕ) : (polyMin n S N).CochainProjection :=
  (polySmoothedMin n S N (p N) (hE.isMinimal N)).toCochainProjection (θ := 1 / 2) (by norm_num)
    (hE.close N)

theorem two_mul_nonneg (hE : PolySmoothingEstimatesMin n S p C) : 0 ≤ 2 * C := by
  linarith [hE.half_le]

variable (hE : PolySmoothingEstimatesMin n S p C)
include hE

/-- **Uniform `L²` bound** `‖π̊_N x‖ ≤ 2 C ‖x‖`. -/
theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ := by
  have h := (polySmoothedMin n S N (p N) (hE.isMinimal N)).norm_toCochainProjection_le
    (θ := 1 / 2) (by norm_num) (hE.close N) (hE.bound N i) x
  have e : (1 - 1 / 2 : ℝ)⁻¹ * C = 2 * C := by norm_num
  rwa [e] at h

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

/-- **The conforming family of the smoothing estimates `hE`** ([AFW2010], §5.5): the complexes of
`S` on the Freudenthal meshes with the smoothed projections `π_N = J_N⁻¹ Q_N`
(`PolySmoothingEstimates.proj`), a conforming family of `HΛ(Q)`
(`ConformingFamily.ofSmoothing`). -/
def PolySmoothingEstimates.family (hE : PolySmoothingEstimates n S p C) :
    ConformingFamily (complex n) ℕ :=
  .ofSmoothing atTop (poly n S) (fun N => polySmoothed n S N (p N) (hE.isMaximal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound (tendsto_infDist_poly S)

/-- **The conforming family of the smoothing estimates `hE` with vanishing boundary DOFs**, a
conforming family of `H̊Λ(Q)`. -/
def PolySmoothingEstimatesMin.family (hE : PolySmoothingEstimatesMin n S p C) :
    ConformingFamily (complexMin n) ℕ :=
  .ofSmoothing atTop (polyMin n S) (fun N => polySmoothedMin n S N (p N) (hE.isMinimal N))
    (by norm_num : (1 / 2 : ℝ) < 1) hE.close hE.bound (tendsto_infDist_polyMin S)

variable (n)

/-- **The finite element complexes of an admissible sequence `S` on the Freudenthal meshes of the
cube** (every `P_rΛ`, `P_r⁻Λ` and mixed sequence) with the smoothed projections
(`polySmoothingEstimates_exists`), a conforming family of `HΛ(Q)`. -/
def polyFamily (S : PolySeq) : ConformingFamily (complex n) ℕ :=
  (polySmoothingEstimates_exists (n := n) S).choose_spec.choose_spec.family

/-- **The finite element complexes of `S` with vanishing boundary DOFs**, a conforming family of
`H̊Λ(Q)`. -/
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

/-- **The two rows of Tables 5.1 and 6.1 of [QuennevilleBelair2015] (§5.3, §6.3), with vanishing
boundary DOFs on the cube `(0, ½)³`, share one smoother**: there is `γ₀ > 0` such that for
every `γ ∈ (0, γ₀]` the same minimal-family parameters `pMin γ` satisfy the smoothing estimates of
the Whitney complex (the top row `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²`), of the lowest-order sequence
`PolySeq.lowestOrder` (the same row) and of the bottom row `PolySeq.lagrangeP2`
(`P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³`). -/
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

/-- **Uniformly bounded smoothed cochain projections for both rows of Tables 5.1/6.1 from one
smoother** (vanishing boundary DOFs, `(0, ½)³`): there are minimal-family parameters `p` and a
constant `C` such that the projections `π̊_N` of the top row (`PolySeq.lowestOrder`) and of the
bottom row (`PolySeq.lagrangeP2`), both built from the same smoothed fields `R_N u`, are bounded
by `2C` in `L²` and in every graph norm, uniformly in `N`, with vanishing harmonic gaps. -/
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
    fun N i j => (hT.proj N).isGraphBounded_of_norm_le (hT.norm_proj_le N i) (hT.norm_proj_le N j), hB.norm_proj_le,
    fun N i j => (hB.proj N).isGraphBounded_of_norm_le (hB.norm_proj_le N i) (hB.norm_proj_le N j),
    fun _ => hT.family.tendsto_harmonicGap, fun _ => hB.family.tendsto_harmonicGap⟩

end Feec.Models.Cube.FEM
