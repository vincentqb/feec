module

public import Feec.Models.Cube.FiniteElementMethod
public import Feec.FiniteElement.WhitneyInterpolation
public import Feec.FiniteElement.SmoothDensity

/-!
# Approximation by the Whitney complexes of the Freudenthal meshes of the cube

On the Freudenthal meshes of `Q = (0, ½)ⁿ`: the `O(h)` interpolation error ([Arnold2018], Ch. 7),
density of smooth forms ([AFW2010], §5.5) and of the Whitney spaces, and convergence of the
semi-discrete Hodge wave equation ([QuennevilleBelair2015], Thm 4.14).

## Main results

* `FEM.exists_mem_whitney_le`, `FEM.exists_mem_whitneyMin_le`: the `O(h)` interpolation error.
* `FEM.eventually_exists_whitney_graph`, `FEM.eventually_exists_whitneyMin_graph`: density.
* `FEM.exists_tendstoUniformlyOn_window_whitney`: the semi-discrete Hodge wave equation converges.
* `FEM.maxwell_exists_tendstoUniformlyOn_whitney`: the same for Maxwell's equations, `n = 3`.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre

variable (n : ℕ)

/-- A point of the `j`-th space of the de Rham complex as an `L²` field of `j`-forms. -/
abbrev asForm {Θ : Set (Fin n → ℝ)} {j : ℤ} (x : L2F ℝ Θ ((deRham ℝ n).ι j)) :
    L2F ℝ Θ (formIdx n j) := x

/-! ## The Freudenthal meshes of the cube are uniformly shape regular -/

theorem mesh_shape [NeZero n] (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    diam T * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ 2 ∧
      diam T = meshSize N := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  have hh : (0 : ℝ) < 1 / 2 / ((N + 1 : ℕ) : ℝ) := by positivity
  have h2 := norm_linearEquiv_symm_le_freudenthal (0 : Fin n → ℝ) hh (finLattice m) σ
  have hd := diam_freudenthalMesh_simplex (0 : Fin n → ℝ) hh (finLattice m) σ
  have hms : meshSize N = 1 / 2 / ((N + 1 : ℕ) : ℝ) := by
    rw [meshSize]; push_cast; ring
  refine ⟨?_, hd.trans hms.symm⟩
  rw [hd]
  calc 1 / 2 / ((N + 1 : ℕ) : ℝ) * _ ≤ 1 / 2 / ((N + 1 : ℕ) : ℝ) *
        (2 / (1 / 2 / ((N + 1 : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h2 hh.le
    _ = 2 := by field_simp

/-! ## Interpolation of smooth forms on the cube meshes -/

/-- The constant `#Λᵏ |Q|^{1/2} C_{n,k} 2^k` of the `L²` interpolation error of degree `k`. -/
def interpConst (k : ℕ) : ℝ :=
  Fintype.card (formIdx n k) * (volume.real (cubeDomain n) ^ (1 / 2 : ℝ) *
    (whitneyConst n k * 2 ^ k))

theorem interpConst_nonneg (k : ℕ) : 0 ≤ interpConst n k := by
  unfold interpConst; have := whitneyConst_nonneg n k; positivity

theorem isBounded_closure_cubeDomain : Bornology.IsBounded (closure (cubeDomain n)) :=
  (isBounded_cubeDomain n).closure

theorem isCompact_closure_cubeDomain : IsCompact (closure (cubeDomain n)) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure (isBounded_closure_cubeDomain n)

variable {n}

/-- **Interpolation error on the cube meshes** ([Arnold2018], Ch. 7), of order `h_N`. -/
theorem exists_mem_whitney_le [NeZero n] (N k : ℕ) {w : FormField n} (hw : ContDiff ℝ 2 w)
    {L L' : ℝ} (hL0 : 0 ≤ L) (hL'0 : 0 ≤ L')
    (hL : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L)
    (hL' : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (whitney n N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ interpConst n k * (meshSize N * L) ∧
      ∃ hv : v ∈ ((complex n).d k (k + 1)).domain,
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by norm_num))⟩ -
          (complex n).d k (k + 1) ⟨v, hv⟩‖ ≤ interpConst n (k + 1) * (meshSize N * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hcl : closure (mesh n N).domain = closure (cubeDomain n) := by rw [mesh_domain]
  have hshape := fun T hT => mesh_shape n N (T := T) hT
  have hΩ := (isOpen_mesh_domain n N).measurableSet
  refine (whitneyElement n).exists_mem_maximalSubcomplexOfEq_le (mesh n N) (mesh_domain n N)
    (isOpen_mesh_domain n N) (isOpen_cubeDomain n) (isBounded_cubeDomain n) k hw1
    (A := interpConst n k * (meshSize N * L)) (A' := interpConst n (k + 1) * (meshSize N * L'))
    ((norm_formL2_sub_glue_le _ hΩ k hw1 (C₀ := 2) (by norm_num) (meshSize_pos N).le hL0
      (fun y hy => hL y (hcl ▸ hy)) (fun T hT => (hshape T hT).1)
      (fun T hT => (hshape T hT).2.le)).trans_eq ?_)
    ((norm_formL2_sub_glue_le _ hΩ (k + 1) (contDiff_extDeriv (m := 1) hw) (C₀ := 2)
      (by norm_num) (meshSize_pos N).le hL'0 (fun y hy => hL' y (hcl ▸ hy))
      (fun T hT => (hshape T hT).1) (fun T hT => (hshape T hT).2.le)).trans_eq ?_) <;>
  · rw [mesh_domain, interpConst]; push_cast; ring

/-! ## Smooth forms are dense in the graph norm -/

theorem exists_smooth_near (k : ℕ) (u : ((complex n).d k (k + 1)).domain) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ w : FormField n, ∃ hw : ContDiff ℝ ∞ w, (∀ x, IsDeg k (w x)) ∧
      ‖(u : L2F ℝ (cubeDomain n) (formIdx n k)) -
          formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
            ⟨w, hw.continuous⟩‖ < ε ∧
      ‖(complex n).d k (k + 1) u -
          formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩‖ < ε := by
  have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)
  obtain ⟨w, hw, h0, h1, h2⟩ := exists_smooth_near_of_starBall
    (isOpen_cubeDomain n) (isBounded_cubeDomain n) (by norm_num : (0 : ℝ) < 1 / 4) (starBall n) k
    ⟨u, hd ▸ u.2⟩ hε
  have hu : (complex n).d k (k + 1) u =
      (extDerivOp ℝ n k).maximal (cubeDomain n) ⟨u, hd ▸ u.2⟩ :=
    LinearPMap.apply_eq_of_eq' hd u
  exact ⟨w, hw, h0, h1, hu ▸ h2⟩

/-! ## Density of the Whitney complexes in `HΛ(Q)` -/

theorem exists_bound_fderiv {w : FormField n} (hw : ContDiff ℝ 1 w) :
    ∃ L, 0 ≤ L ∧ ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L := by
  obtain ⟨L, hL⟩ := (isCompact_closure_cubeDomain n).exists_bound_of_continuousOn
    (hw.continuous_fderiv one_ne_zero).continuousOn
  exact ⟨max L 0, le_max_right _ _, fun y hy => (hL y hy).trans (le_max_left _ _)⟩

variable [NeZero n]

/-- **Graph-norm density of the Whitney spaces in `HΛᵏ(Q)`.** -/
theorem eventually_exists_whitney_graph (k : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n k))
    (hx : x ∈ ((complex n).d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (whitney n N).V k, ‖x - v‖ < ε ∧
      ‖(complex n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((whitney n N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth (isOpen_cubeDomain n) (isBounded_cubeDomain n)
    (by norm_num : (0 : ℝ) < 1 / 4) (starBall n) (fun N => whitney n N)
    (fun k w hw _ => ?_) k x hx hε
  have hw2 : ContDiff ℝ 2 w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := exists_bound_fderiv (hw.of_le (by exact_mod_cast le_top))
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_fderiv (contDiff_extDeriv (m := 1) hw2)
  refine ⟨fun N => interpConst n k * (meshSize N * L) +
    interpConst n (k + 1) * (meshSize N * L'), by
      simpa using ((tendsto_meshSize.mul_const L).const_mul (interpConst n k)).add
        ((tendsto_meshSize.mul_const L').const_mul (interpConst n (k + 1))), fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := exists_mem_whitney_le N k hw2 hL0 hL'0 hL hL'
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right (mul_nonneg (interpConst_nonneg n (k + 1))
    (mul_nonneg (meshSize_pos N).le hL'0))), hdv, hv2.trans (le_add_of_nonneg_left
      (mul_nonneg (interpConst_nonneg n k) (mul_nonneg (meshSize_pos N).le hL0)))⟩

theorem eventually_exists_whitney_lt (k : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (whitney n N).V k, ‖x - v‖ < ε :=
  Subcomplex.eventually_exists_lt_of_graph
    (fun k x hx _ hε => eventually_exists_whitney_graph k x hx hε) k x hε

theorem eventually_exists_whitney_near (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (whitney n N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ ((complex n).d i j).domain),
        ‖(complex n).d i j ⟨x - v, Submodule.sub_mem _ hx ((whitney n N).le_domain i j hv)⟩‖ <
          ε :=
  Subcomplex.eventually_exists_near_of_graph
    (fun k x hx _ hε => eventually_exists_whitney_graph k x hx hε) i x hε

theorem formL2_mem_domain (k : ℕ) {w : FormField n} (hw : ContDiff ℝ 1 w)
    (hdeg : ∀ x, IsDeg k (w x)) :
    ∃ h : formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
        ⟨w, hw.continuous⟩ ∈ ((complex n).d k (k + 1)).domain,
      (complex n).d k (k + 1) ⟨_, h⟩ =
        formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv hw⟩ := by
  have key : ∀ (Θ : Set (Fin n → ℝ)) (e : Θ = cubeDomain n) (hΘ : MeasurableSet Θ)
      (hb : Bornology.IsBounded Θ),
      (∃ h : formL2 hΘ hb k ⟨w, hw.continuous⟩ ∈ ((extDerivOp ℝ n k).maximal Θ).domain,
        (extDerivOp ℝ n k).maximal Θ ⟨_, h⟩ =
          formL2 hΘ hb ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩) →
      ∃ h : formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ ∈ ((extDerivOp ℝ n k).maximal (cubeDomain n)).domain,
        (extDerivOp ℝ n k).maximal (cubeDomain n) ⟨_, h⟩ =
          formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv hw⟩ := by
    rintro Θ rfl _ _ h; exact h
  obtain ⟨h, hval⟩ := key _ (mesh_domain n 0) _ _
    (formL2_mem_maximal (mesh n 0) (isOpen_mesh_domain n 0) k hw hdeg)
  have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)
  exact ⟨hd ▸ h, (LinearPMap.apply_eq_of_eq' hd _).trans hval⟩

theorem infDist_domainSub_whitney_le (N k : ℕ) {w : FormField n} (hw : ContDiff ℝ 2 w)
    (hdeg : ∀ x, IsDeg k (w x)) {L L' : ℝ} (hL0 : 0 ≤ L) (hL'0 : 0 ≤ L')
    (hL : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L)
    (hL' : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L')
    (σ : (complex n).domainSpace k)
    (hσ : (complex n).domainIncl k σ =
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩) :
    Metric.infDist σ ((whitney n N).domainSub k) ≤
      (interpConst n k * L + interpConst n (k + 1) * L') * meshSize N := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := exists_mem_whitney_le N k hw hL0 hL'0 hL hL'
  obtain ⟨hdom, hval⟩ := formL2_mem_domain k hw1 hdeg
  have hrel : (ComplexShape.up ℤ).Rel (k : ℤ) ((k : ℤ) + 1) := rfl
  refine ((whitney n N).infDist_domainSub_le hrel σ hv).trans ?_
  have hc : (complex n).domainCoord k (k + 1) σ = ⟨_, hdom⟩ := Subtype.ext hσ
  rw [hc, hval, hσ]
  calc _ ≤ interpConst n k * (meshSize N * L) + interpConst n (k + 1) * (meshSize N * L') :=
        add_le_add hv1 hv2
    _ = _ := by ring

theorem tendsto_infDist_whitney (j : ℤ) (q : L2F ℝ (cubeDomain n) (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((whitney n N).V j :
      Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => whitney n N) q fun _ ha =>
    eventually_exists_whitney_lt j q ha

theorem dense_window (a : ℤ) (m : ℕ) :
    ∀ ζ : ((complex n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((whitney n N).window a m).graphSub, ‖ζ - w‖ < δ := fun ζ _ hδ =>
  Subcomplex.eventually_exists_graphSub_lt (fun N => (whitney n N).window a m)
    (fun i x _ hε => (eventually_exists_whitney_near (a + i) x hε).mono fun _ hN => by
      obtain ⟨v, hv, h1, h2⟩ := hN
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩) ζ hδ

/-- **Convergence of the semi-discrete Hodge wave equation** ([QuennevilleBelair2015], Thm 4.14). -/
theorem exists_tendstoUniformlyOn_window_whitney (a : ℤ) (m : ℕ) (t₀ t₁ : ℝ)
    (x : ((complex n).window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitney n N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney n N).window a m).graphSub)
        (((complex n).window a m).totalD.toGraphSpace
          ⟨x, (((complex n).window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complex n).window a m).totalD.graphFst (ξh N t))
        (fun t => ((complex n).window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  exists_tendstoUniformlyOn_window n a m (dense_window a m) t₀ t₁ x

/-! ## Density of the Whitney complexes with vanishing traces in `H̊Λ(Q)` -/

/-- **Interpolation error with vanishing boundary DOFs**, for `C²` forms vanishing outside `Q`. -/
theorem exists_mem_whitneyMin_le (N k : ℕ) {w : FormField n} (hw : ContDiff ℝ 2 w)
    (hsupp : ∀ x ∉ cubeDomain n, w x = 0) {L L' : ℝ} (hL0 : 0 ≤ L) (hL'0 : 0 ≤ L')
    (hL : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L)
    (hL' : ∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (whitneyMin n N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ interpConst n k * (meshSize N * L) ∧
      ∃ hv : v ∈ ((complexMin n).d k (k + 1)).domain,
        ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by norm_num))⟩ -
          (complexMin n).d k (k + 1) ⟨v, hv⟩‖ ≤ interpConst n (k + 1) * (meshSize N * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hcl : closure (mesh n N).domain = closure (cubeDomain n) := by rw [mesh_domain]
  have hshape := fun T hT => mesh_shape n N (T := T) hT
  have hΩ := (isOpen_mesh_domain n N).measurableSet
  refine (whitneyElement n).exists_mem_minimalSubcomplexOfEq_le (mesh n N) (mesh_domain n N)
    (isOpen_mesh_domain n N) (isOpen_cubeDomain n) (isBounded_cubeDomain n) (center n)
    (strictStar_mesh n N) k hw1 hsupp
    (A := interpConst n k * (meshSize N * L)) (A' := interpConst n (k + 1) * (meshSize N * L'))
    ((norm_formL2_sub_glue_le _ hΩ k hw1 (C₀ := 2) (by norm_num) (meshSize_pos N).le hL0
      (fun y hy => hL y (hcl ▸ hy)) (fun T hT => (hshape T hT).1)
      (fun T hT => (hshape T hT).2.le)).trans_eq ?_)
    ((norm_formL2_sub_glue_le _ hΩ (k + 1) (contDiff_extDeriv (m := 1) hw) (C₀ := 2)
      (by norm_num) (meshSize_pos N).le hL'0 (fun y hy => hL' y (hcl ▸ hy))
      (fun T hT => (hshape T hT).1) (fun T hT => (hshape T hT).2.le)).trans_eq ?_) <;>
  · rw [mesh_domain, interpConst]; push_cast; ring

omit [NeZero n] in
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
  have hd := deRham_minimalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)
  obtain ⟨w, hw, hdeg, h0, h1, h2⟩ := exists_smooth_near_min_of_starBall
    (isOpen_cubeDomain n) (isBounded_cubeDomain n) (by norm_num : (0 : ℝ) < 1 / 4) (starBall n) k
    ⟨u, hd ▸ u.2⟩ hε
  have hu : (complexMin n).d k (k + 1) u =
      (extDerivOp ℝ n k).minimal (cubeDomain n) ⟨u, hd ▸ u.2⟩ :=
    LinearPMap.apply_eq_of_eq' hd u
  exact ⟨w, hw, hdeg, h0, h1, hu ▸ h2⟩

/-- **Graph-norm density of the Whitney spaces with vanishing boundary DOFs in `H̊Λᵏ(Q)`**. -/
theorem eventually_exists_whitneyMin_graph (k : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n k))
    (hx : x ∈ ((complexMin n).d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (whitneyMin n N).V k, ‖x - v‖ < ε ∧
      ‖(complexMin n).d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((whitneyMin n N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth_min (isOpen_cubeDomain n) (isBounded_cubeDomain n)
    (by norm_num : (0 : ℝ) < 1 / 4) (starBall n) (fun N => whitneyMin n N)
    (fun k w hw _ hsupp => ?_) k x hx hε
  have hw2 : ContDiff ℝ 2 w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := exists_bound_fderiv (hw.of_le (by exact_mod_cast le_top))
  obtain ⟨L', hL'0, hL'⟩ := exists_bound_fderiv (contDiff_extDeriv (m := 1) hw2)
  refine ⟨fun N => interpConst n k * (meshSize N * L) +
    interpConst n (k + 1) * (meshSize N * L'), by
      simpa using ((tendsto_meshSize.mul_const L).const_mul (interpConst n k)).add
        ((tendsto_meshSize.mul_const L').const_mul (interpConst n (k + 1))), fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := exists_mem_whitneyMin_le N k hw2 hsupp hL0 hL'0 hL hL'
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right (mul_nonneg (interpConst_nonneg n (k + 1))
    (mul_nonneg (meshSize_pos N).le hL'0))), hdv, hv2.trans (le_add_of_nonneg_left
      (mul_nonneg (interpConst_nonneg n k) (mul_nonneg (meshSize_pos N).le hL0)))⟩

theorem eventually_exists_whitneyMin_lt (k : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n k))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (whitneyMin n N).V k, ‖x - v‖ < ε :=
  Subcomplex.eventually_exists_lt_of_graph
    (fun k x hx _ hε => eventually_exists_whitneyMin_graph k x hx hε) k x hε

theorem eventually_exists_whitneyMin_near (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (whitneyMin n N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ ((complexMin n).d i j).domain),
        ‖(complexMin n).d i j
          ⟨x - v, Submodule.sub_mem _ hx ((whitneyMin n N).le_domain i j hv)⟩‖ < ε :=
  Subcomplex.eventually_exists_near_of_graph
    (fun k x hx _ hε => eventually_exists_whitneyMin_graph k x hx hε) i x hε

theorem tendsto_infDist_whitneyMin (j : ℤ) (q : L2F ℝ (cubeDomain n) (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((whitneyMin n N).V j :
      Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => whitneyMin n N) q fun _ ha =>
    eventually_exists_whitneyMin_lt j q ha

theorem dense_windowMin (a : ℤ) (m : ℕ) :
    ∀ ζ : ((complexMin n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((whitneyMin n N).window a m).graphSub, ‖ζ - w‖ < δ := fun ζ _ hδ =>
  Subcomplex.eventually_exists_graphSub_lt (fun N => (whitneyMin n N).window a m)
    (fun i x _ hε => (eventually_exists_whitneyMin_near (a + i) x hε).mono fun _ hN => by
      obtain ⟨v, hv, h1, h2⟩ := hN
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩) ζ hδ

end Feec.Models.Cube.FEM

namespace Feec.Models.Cube.FEM

open Feec.HilbertComplex

/-- **Maxwell's equations on the cube meshes**: the semi-discrete solutions converge, `n = 3`. -/
theorem maxwell_exists_tendstoUniformlyOn_whitney (t₀ t₁ : ℝ)
    (x : ((complex 3).window 0 3).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complex 3).window 0 3).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitney 3 N).window 0 3).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney 3 N).window 0 3).graphSub)
        (((complex 3).window 0 3).totalD.toGraphSpace
          ⟨x, (((complex 3).window 0 3).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complex 3).window 0 3).totalD.graphFst (ξh N t))
        (fun t => ((complex 3).window 0 3).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  exists_tendstoUniformlyOn_window 3 0 3 (dense_window 0 3) t₀ t₁ x

end Feec.Models.Cube.FEM
