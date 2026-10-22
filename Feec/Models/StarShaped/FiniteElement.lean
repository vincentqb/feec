module

public import Feec.FiniteElement.ShapeRegularSmoothing
public import Feec.Models.Cube.SmoothingEstimates
public import Feec.Models.Parallelepiped.FiniteElement

/-!
# The finite element method on domains star-shaped with respect to a ball

Let `Ω ⊆ ℝⁿ` be a bounded open domain star-shaped with respect to every point of a ball
`B(x₀, s₀)`, with `cl Ω ⊆ B̄(x₀, R)` (`StarDomain`), and let `M_N` be conforming simplicial meshes
of `Ω` that are uniformly **shape regular** (`‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T`,
`c h_Tⁿ ≤ |det B_T|`) and **quasi-uniform** (`q h_N ≤ h_T`), with `h_N → 0` (`MeshFamily`). The
finite element theory of the Freudenthal meshes of the cube (`Feec.Models.Cube.SmoothingEstimates`,
`Feec.Models.Cube.FiniteElementConvergence`) holds for the lowest-order Whitney complexes of
`M_N`, with both boundary conditions.

**The smoothed-projection estimates, unconditionally** ([AFW2010], §5.4;
[ChristiansenWinther2008]). For the parameters `pMax` (dilation factor `1 - γ h / R` about `x₀`)
and `pMin` (factor `1 + γ h / R`), bump radii `γ h σ / 2 < γ h σ`, `σ = min 1 (s₀ / (16 R))`
(`sigmaOf`), and `γ` depending only on `n, C, c, q` (`exists_gamma`):
* the smoothed interpolants `Q = Π_h R` are bounded in `L²` uniformly in the mesh
  (`exists_norm_smoothedInterp_le`): the local DOF estimate on shape-regular simplices
  (`Feec.FiniteElement.exists_dof_bound_p1MinusForms`), Jensen's inequality for the mollifier
  (`FEM.abs_smoothForm_le`) and bounded overlap by volume (`sum_locMass_le`);
* `‖v - Q v‖ ≤ ½ ‖v‖` on `Vₕ` and on `V̊ₕ`: at points of a face `g` with barycentric weights
  `≥ θ = K₀ γ` every simplex sampled by the smoother contains `g` (`GeomOK`, from the geometric
  lemma `StarGeom.subset_vertexSet_of_segments` along the paths of `path_of_isMaximal`,
  `path_of_isMinimal`), the traces agree there, and the error is the dilation defect and the
  displacement `O(γ h)` against the shape-regular inverse estimates (`InvBoundM`,
  `sqrt_mul_abs_integrand_le`, `sqrt_mul_abs_dof_err_le`, `norm_sq_sub_smoothedInterp_le`).
  Samples outside `Ω` (`SampleOK`) do not occur for `pMax` (`sampleOK_of_isMaximal`); for `pMin`
  they force the face into a boundary facet (`sampleOK_of_isMinimal`, from the pseudo-manifold
  property `StarGeom.exists_isBoundaryFacet_of_mem_frontier`), where the DOFs of `V̊ₕ` vanish;
* hence **uniformly bounded cochain projections** onto `Vₕ ⊆ HΛ(Ω)` and `V̊ₕ ⊆ H̊Λ(Ω)`, in `L²`
  and every graph norm (`exists_uniform_cochainProjection`, `exists_uniform_cochainProjectionMin`;
  for the family, `MeshFamily.exists_uniform_proj`, `MeshFamily.exists_uniform_projMin`).

**Approximation, unconditionally.** The Whitney interpolation error on shape-regular meshes
(`Feec.FiniteElement.norm_formL2_sub_glue_le_of_isShapeRegular`) gives the rate `h_N` for `C²`
forms (`MeshFamily.exists_mem_whitney_le`, `MeshFamily.exists_mem_whitney_le_of_isC2Form`, and
the `Min` versions for forms vanishing outside `Ω`), and with the density of smooth forms
(`StarDomain.exists_smooth_near`, `StarDomain.exists_smooth_near_min`) graph-norm density of the
Whitney spaces (`MeshFamily.eventually_exists_whitney_near`, `..._whitneyMin_near`).

**The finite element theorems** (`MeshFamily`, both families, `Min` for `H̊Λ(Ω)`):
* `discretePoincare`: uniform discrete Poincaré inequality ([AFW2010], Thm 3.6);
* `mixed_wellPosed`: uniform well-posedness and stability of the discrete mixed Hodge Laplacian
  ([AFW2010], Thm 3.8);
* `mixed_rate_smooth`: `O(h)` convergence for `C²` solutions (`StarDomain.IsC2Form`), error
  `≤ K L h_N` ([AFW2010], Thm 3.9; [Arnold2018], Ch. 7);
* `mixed_quasiOptimal`, `smoothedProjection_uniform`: quasi-optimality with weights `μ_j(N) → 0`
  and the vanishing of the harmonic gap;
* `exists_tendstoUniformlyOn_window`: convergence of the semi-discrete Hodge wave equation on every
  window ([QuennevilleBelair2015], Thm 4.14), with no hypothesis.

**Remaining hypotheses.** The cochain projections, the approximation results and the wave
convergence are proved with no hypothesis. The Poincaré inequality of `HΛ(Ω)`, resp. `H̊Λ(Ω)`
(`HasPoincare`, equivalently closed range), is a hypothesis of `discretePoincare`,
`mixed_wellPosed`, `mixed_rate_smooth` and `mixed_quasiOptimal`; it holds on every bounded
Lipschitz domain (regularized Poincaré and Bogovskiĭ operators, [CostabelMcIntosh2010]), a
theory absent from Mathlib, and is a theorem on the cube with
`c_P = (2π)⁻¹` (`CubeWitness.hasPoincare`, `CubeWitness.hasPoincareMin`) and on every
parallelepiped (`Feec.Models.Parallelepiped.poincare`). The finite-dimensionality of the harmonic
forms is used only for the harmonic gap (`smoothedProjection_uniform`, `mixed_quasiOptimal`).
**Non-vacuity**: the cube with its Freudenthal meshes is a `StarDomain` with a `MeshFamily`
satisfying all these hypotheses (`CubeWitness.starDomain`, `CubeWitness.meshFamily`,
`CubeWitness.hasPoincare`, `CubeWitness.hasPoincareMin`), and so is every parallelepiped `A · Q + b` (every box) with its image
Freudenthal meshes (`ParallelepipedWitness.starDomain`, `ParallelepipedWitness.meshFamily`,
with `Feec.Models.Parallelepiped.poincare`; via the affine images
`StarDomain.map`, `MeshFamily.map`: shape regularity, quasi-uniformity and star-shapedness with
respect to a ball are preserved by affine equivalences, `isShapeRegular_image`,
`MeshData.map`). The higher-order families `P_rΛᵏ`, `P_r⁻Λᵏ` on star-shaped domains
(whose inverse and DOF estimates on shape-regular simplices are
`Feec.FiniteElement.exists_inverse_bound_polySpace` and
`Feec.FiniteElement.exists_dof_bound_of_le_polySpace`) are not treated here.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (Thm 3.6), Thm 3.8, Thm 3.9, §5.4 (smoothed projections)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
  (shape-regular and quasi-uniform families)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (rates for smooth
  solutions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)
* [M. Costabel, A. McIntosh, *On Bogovskiĭ and Regularized Poincaré Integral Operators for de Rham Complexes on Lipschitz Domains*][CostabelMcIntosh2010]
  (the Poincaré inequality on bounded Lipschitz domains)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

namespace Feec.Models.StarShaped

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre Feec.Models.Cube

variable {n : ℕ}

/-! ### Domains star-shaped with respect to a ball -/

section Geometry

variable {Ω : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {s₀ : ℝ}

/-- `Ω` is star-shaped with respect to every point of the ball `B(x₀, s₀)`. -/
def StarBall (Ω : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) (s₀ : ℝ) : Prop :=
  ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω

theorem StarBall.dil_mem (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) {x : Fin n → ℝ}
    (hx : x ∈ closure Ω) {c : ℝ} (hc2 : 1 / 2 ≤ c) (hc1 : c < 1) : x₀ + c • (x - x₀) ∈ Ω :=
  closedBall_dil_subset_of_starBall hstar hc2 hc1 (r := 0) (by nlinarith) hx
    (Metric.mem_closedBall_self le_rfl)

/-- Strict star-shapedness with respect to `x₀`: `x₀ + t (x - x₀) ∈ Ω` for `x ∈ cl Ω`,
`0 ≤ t < 1`. -/
theorem StarBall.strict (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) {x : Fin n → ℝ}
    (hx : x ∈ closure Ω) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : x₀ + t • (x - x₀) ∈ Ω := by
  rcases le_or_gt (1 / 2) t with h | h
  · exact hstar.dil_mem hs₀ hx h ht1
  · have hy := hstar.dil_mem hs₀ hx (le_refl (1 / 2)) (by norm_num)
    have hseg := hstar _ hy x₀ (Metric.mem_ball_self hs₀)
    refine hseg ⟨1 - 2 * t, 2 * t, by linarith, by linarith, by ring, ?_⟩
    simp only [smul_add, smul_smul]
    rw [show (2 : ℝ) * t * (1 / 2) = t by ring]
    module

/-- The dilation segment `[x, x₀ + c (x - x₀)]`, `½ ≤ c ≤ 1`, lies in `cl Ω`. -/
theorem StarBall.segment_dil_subset (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀)
    {x : Fin n → ℝ} (hx : x ∈ closure Ω) {c : ℝ} (hc2 : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    segment ℝ x (x₀ + c • (x - x₀)) ⊆ closure Ω := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  have e : a • x + b • (x₀ + c • (x - x₀)) = x₀ + (a + b * c) • (x - x₀) := by
    have ha' : a = 1 - b := by linarith
    subst ha'; module
  rw [e]
  rcases (show a + b * c ≤ 1 by nlinarith).lt_or_eq with hlt | heq
  · exact subset_closure (hstar.dil_mem hs₀ hx (by nlinarith) hlt)
  · rw [heq, one_smul, add_sub_cancel]; exact hx

/-- **`Ω = int cl Ω`** for `Ω` open and star-shaped with respect to a ball. -/
theorem StarBall.interior_closure_subset (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) :
    interior (closure Ω) ⊆ Ω := by
  intro p hp
  have hc : Tendsto (fun ε : ℝ => x₀ + (1 + ε) • (p - x₀)) (𝓝 0) (𝓝 p) := by
    have : Continuous fun ε : ℝ => x₀ + (1 + ε) • (p - x₀) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), x₀ + (1 + ε) • (p - x₀) ∈ interior (closure Ω) ∧
      ε ∈ Set.Ioo (0 : ℝ) 1 :=
    ((hc.eventually (isOpen_interior.mem_nhds hp)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨ε, hε, hε01⟩ := hev.exists
  have hpos : (0 : ℝ) < 1 + ε := by linarith [hε01.1]
  have hmem := hstar.dil_mem hs₀ (interior_subset hε) (c := (1 + ε)⁻¹)
    (by rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) hpos]; linarith [hε01.2])
    (inv_lt_one_of_one_lt₀ (by linarith [hε01.1]))
  have e : x₀ + (1 + ε)⁻¹ • (x₀ + (1 + ε) • (p - x₀) - x₀) = p := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  rwa [e] at hmem

end Geometry

/-! ### The smoothing parameters -/

section Params

/-- **Admissible smoothing parameters** at scale `γ h`: centre `x₀`, `|c - 1| = γ h / R`, bump
radii `γ h σ / 2 < γ h σ`. -/
structure IsAdm (x₀ : Fin n → ℝ) (R σ γ h : ℝ) (p : SmoothingParam (Fin n → ℝ)) : Prop where
  center_eq : p.center = x₀
  abs_factor_sub_one : |p.factor - 1| = γ * h / R
  rIn_eq : p.bump.rIn = γ * h * σ / 2
  rOut_eq : p.bump.rOut = γ * h * σ

/-- The parameters of the **maximal family**: dilation factor `1 - γ h / R` about `x₀`. -/
def pMax (x₀ : Fin n → ℝ) (R σ γ h : ℝ) (hpos : 0 < γ * h * σ) (hhalf : γ * h / R ≤ 1 / 2) :
    SmoothingParam (Fin n → ℝ) where
  center := x₀
  factor := 1 - γ * h / R
  half_le_factor := by linarith
  bump := ⟨γ * h * σ / 2, γ * h * σ, by positivity, by linarith⟩

/-- The parameters of the **minimal family**: dilation factor `1 + γ h / R` towards `x₀`. -/
def pMin (x₀ : Fin n → ℝ) (R σ γ h : ℝ) (hpos : 0 < γ * h * σ) (hnn : 0 ≤ γ * h / R) :
    SmoothingParam (Fin n → ℝ) where
  center := x₀
  factor := 1 + γ * h / R
  half_le_factor := by linarith
  bump := ⟨γ * h * σ / 2, γ * h * σ, by positivity, by linarith⟩

variable {x₀ : Fin n → ℝ} {R σ γ h s₀ : ℝ}

theorem pMax_isAdm (hpos : 0 < γ * h * σ) (hhalf : γ * h / R ≤ 1 / 2) (hnn : 0 ≤ γ * h / R) :
    IsAdm x₀ R σ γ h (pMax x₀ R σ γ h hpos hhalf) where
  center_eq := rfl
  abs_factor_sub_one := by
    change |1 - γ * h / R - 1| = _
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hnn]
  rIn_eq := rfl
  rOut_eq := rfl

theorem pMin_isAdm (hpos : 0 < γ * h * σ) (hnn : 0 ≤ γ * h / R) :
    IsAdm x₀ R σ γ h (pMin x₀ R σ γ h hpos hnn) where
  center_eq := rfl
  abs_factor_sub_one := by
    change |1 + γ * h / R - 1| = _
    rw [add_sub_cancel_left, abs_of_nonneg hnn]
  rIn_eq := rfl
  rOut_eq := rfl

theorem pMax_isMaximal (hR : 0 < R) (hpos : 0 < γ * h * σ) (hhalf : γ * h / R ≤ 1 / 2)
    (hgh : 0 < γ * h) (hσ : σ < s₀ / (4 * R)) :
    (pMax x₀ R σ γ h hpos hhalf).IsMaximal x₀ s₀ where
  center_eq := rfl
  factor_lt_one := by
    change 1 - γ * h / R < 1
    have : 0 < γ * h / R := div_pos hgh hR
    linarith
  rOut_lt := by
    change γ * h * σ < s₀ * (1 - (1 - γ * h / R)) / 4
    rw [sub_sub_cancel]
    have h1 : γ * h * σ < γ * h * (s₀ / (4 * R)) := mul_lt_mul_of_pos_left hσ hgh
    have h2 : γ * h * (s₀ / (4 * R)) = s₀ * (γ * h / R) / 4 := by field_simp
    linarith

theorem pMin_isMinimal (hR : 0 < R) (hpos : 0 < γ * h * σ) (hnn : 0 ≤ γ * h / R)
    (hgh : 0 < γ * h) (hσ : σ < s₀ / (4 * R)) :
    (pMin x₀ R σ γ h hpos hnn).IsMinimal x₀ s₀ where
  center_eq := rfl
  one_lt_factor := by
    change 1 < 1 + γ * h / R
    have : 0 < γ * h / R := div_pos hgh hR
    linarith
  rOut_lt := by
    change γ * h * σ < s₀ * (1 + γ * h / R - 1) / 2
    rw [add_sub_cancel_left]
    have h1 : γ * h * σ < γ * h * (s₀ / (4 * R)) := mul_lt_mul_of_pos_left hσ hgh
    have h2 : γ * h * (s₀ / (4 * R)) = s₀ * (γ * h / R) / 4 := by field_simp
    have h3 : 0 < s₀ * (γ * h / R) := by
      have : 0 < s₀ / (4 * R) := lt_of_le_of_lt (by nlinarith [hpos]) hσ
      have hs : 0 < s₀ := by
        have := mul_pos this (by positivity : (0 : ℝ) < 4 * R)
        rwa [div_mul_cancel₀ _ (by positivity)] at this
      positivity
    linarith

namespace IsAdm

variable {p : SmoothingParam (Fin n → ℝ)}

theorem gh_nonneg (hp : IsAdm x₀ R σ γ h p) (hR : 0 < R) : 0 ≤ γ * h := by
  have := hp.abs_factor_sub_one ▸ abs_nonneg _
  exact (div_nonneg_iff.1 this).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_le.2 hR)

theorem factor_le_two (hp : IsAdm x₀ R σ γ h p) (hγh : γ * h / R ≤ 1) : p.factor ≤ 2 := by
  have h1 := hp.abs_factor_sub_one
  have := le_abs_self (p.factor - 1)
  linarith

theorem pow_factor_le (hp : IsAdm x₀ R σ γ h p) (hγh : γ * h / R ≤ 1) (k : ℕ) :
    p.factor ^ k ≤ 2 ^ k :=
  pow_le_pow_left₀ p.factor_pos.le (hp.factor_le_two hγh) k

/-- `|1 - cᵏ| ≤ k 2ᵏ γ h / R`. -/
theorem abs_one_sub_pow_le (hp : IsAdm x₀ R σ γ h p) (hR : 0 < R) (hγh : γ * h / R ≤ 1)
    (k : ℕ) : |1 - p.factor ^ k| ≤ k * 2 ^ k * (γ * h / R) := by
  have hg : p.factor ^ k - 1 = (∑ i ∈ Finset.range k, p.factor ^ i) * (p.factor - 1) :=
    (geom_sum_mul p.factor k).symm
  rw [abs_sub_comm, hg, abs_mul, hp.abs_factor_sub_one]
  refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (hp.gh_nonneg hR) hR.le)
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg p.factor_pos.le i)]
  calc ∑ i ∈ Finset.range k, p.factor ^ i ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) ^ k :=
        Finset.sum_le_sum fun i hi => (hp.pow_factor_le hγh i).trans
          (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hi).le)
    _ = k * 2 ^ k := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The dilated point is within `γ h` of `x` for `‖x - x₀‖ ≤ R`. -/
theorem norm_dil_sub_le (hp : IsAdm x₀ R σ γ h p) (hR : 0 < R) {x : Fin n → ℝ}
    (hx : ‖x - x₀‖ ≤ R) :
    ‖(p.center + p.factor • (x - p.center)) - x‖ ≤ γ * h := by
  rw [hp.center_eq]
  have e : x₀ + p.factor • (x - x₀) - x = (p.factor - 1) • (x - x₀) := by
    rw [sub_smul, one_smul]; abel
  rw [e, norm_smul, Real.norm_eq_abs, hp.abs_factor_sub_one]
  calc γ * h / R * ‖x - x₀‖ ≤ γ * h / R * R :=
        mul_le_mul_of_nonneg_left hx (div_nonneg (hp.gh_nonneg hR) hR.le)
    _ = γ * h := by field_simp

/-- Samples of the smoother at `x` are within `2 γ h` of `x` (for `σ ≤ 1`). -/
theorem norm_sub_le_of_dist_le (hp : IsAdm x₀ R σ γ h p) (hR : 0 < R) (hσ1 : σ ≤ 1)
    {x : Fin n → ℝ} (hx : ‖x - x₀‖ ≤ R) {t : Fin n → ℝ}
    (ht : dist t (p.center + p.factor • (x - p.center)) ≤ p.bump.rOut) :
    ‖t - x‖ ≤ 2 * (γ * h) := by
  have h1 := hp.norm_dil_sub_le hR hx
  have h2 : dist t (p.center + p.factor • (x - p.center)) ≤ γ * h := by
    rw [hp.rOut_eq] at ht
    have := hp.gh_nonneg hR
    nlinarith
  rw [← dist_eq_norm]
  calc dist t x ≤ dist t (p.center + p.factor • (x - p.center)) +
        dist (p.center + p.factor • (x - p.center)) x := dist_triangle _ _ _
    _ ≤ γ * h + γ * h := add_le_add h2 (by rw [dist_eq_norm]; exact h1)
    _ = 2 * (γ * h) := by ring

end IsAdm

/-- A simplex of `M` through a point within `2 γ h ≤ h` of `x ∈ T` lies in the
`2h`-neighbourhood of `T`. -/
theorem closedInterior_subset_cthickening {M : SimplicialMesh n} {γ : ℝ}
    (hh : 0 < M.meshSize) (hγ2 : γ ≤ 1 / 2) {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} {x t : Fin n → ℝ}
    (hxT : x ∈ T.closedInterior) (htT' : t ∈ T'.closedInterior) (hT' : T' ∈ M.simplices)
    (hxt : ‖t - x‖ ≤ 2 * (γ * M.meshSize)) :
    T'.closedInterior ⊆ Metric.cthickening (2 * M.meshSize) T.closedInterior := by
  intro y hy
  have hdy : ‖y - t‖ ≤ M.meshSize := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem T'.isCompact_closedInterior.isBounded hy htT').trans
      (M.diam_le_meshSize hT')
  refine Metric.mem_cthickening_of_dist_le y x _ _ hxT ?_
  rw [dist_eq_norm]
  calc ‖y - x‖ = ‖(y - t) + (t - x)‖ := by congr 1; abel
    _ ≤ ‖y - t‖ + ‖t - x‖ := norm_add_le _ _
    _ ≤ M.meshSize + 2 * (γ * M.meshSize) := add_le_add hdy hxt
    _ ≤ 2 * M.meshSize := by nlinarith

end Params

/-! ### Paths from face points to the samples of the smoother -/

section Paths

variable {Ω : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {s₀ R σ γ h : ℝ}
  {p : SmoothingParam (Fin n → ℝ)}

/-- **Maximal family**: a sample `t` of the smoother at `x ∈ cl Ω` is joined to `x` in `cl Ω` by
the segments `[x, x̂]`, `[x̂, t]`, `x̂ = x₀ + c (x - x₀)`. -/
theorem path_of_isMaximal (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) (hp : p.IsMaximal x₀ s₀)
    {x : Fin n → ℝ} (hx : x ∈ closure Ω) {t : Fin n → ℝ}
    (ht : dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut) :
    segment ℝ x (p.center + p.factor • (x - p.center)) ⊆ closure Ω ∧
      segment ℝ (p.center + p.factor • (x - p.center)) t ⊆ closure Ω := by
  rw [hp.center_eq] at ht ⊢
  refine ⟨hstar.segment_dil_subset hs₀ hx p.half_le_factor hp.factor_lt_one.le, ?_⟩
  have hball := closedBall_dil_subset_of_starBall hstar p.half_le_factor hp.factor_lt_one
    hp.rOut_lt hx
  refine ((convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self
    p.bump.rOut_pos.le) (Metric.mem_closedBall.2 ht.le)).trans (hball.trans subset_closure)

/-- **Minimal family**: a sample `t ∈ Ω` of the smoother at `x ∈ cl Ω` is joined to `x` in `cl Ω`
by the segments `[x, tt]`, `[tt, t]`, `tt = x₀ + c⁻¹ (t - x₀)`, with `‖tt - x‖ ≤ rOut`. -/
theorem path_of_isMinimal (hstar : StarBall Ω x₀ s₀) (hs₀ : 0 < s₀) (hR : 0 < R)
    (hp : p.IsMinimal x₀ s₀) (hpA : IsAdm x₀ R σ γ h p) (hγh : γ * h / R ≤ 1)
    (hσ : σ ≤ s₀ / (16 * R)) {x : Fin n → ℝ} {t : Fin n → ℝ} (htΩ : t ∈ Ω)
    (ht : dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut) :
    segment ℝ x (x₀ + p.factor⁻¹ • (t - x₀)) ⊆ closure Ω ∧
      segment ℝ (x₀ + p.factor⁻¹ • (t - x₀)) t ⊆ closure Ω ∧
      ‖x₀ + p.factor⁻¹ • (t - x₀) - x‖ ≤ p.bump.rOut := by
  rw [hp.center_eq] at ht
  have hc1 := hp.one_lt_factor
  have hc0 : 0 < p.factor := p.factor_pos
  have hc2 := hpA.factor_le_two hγh
  set tt := x₀ + p.factor⁻¹ • (t - x₀)
  have he : tt - x = p.factor⁻¹ • (t - (x₀ + p.factor • (x - x₀))) := by
    simp only [tt, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
    abel
  have hnorm : ‖tt - x‖ ≤ p.bump.rOut := by
    rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc0.le), ← dist_eq_norm]
    calc p.factor⁻¹ * dist t (x₀ + p.factor • (x - x₀)) ≤ 1 * p.bump.rOut :=
          mul_le_mul (inv_le_one_of_one_le₀ hc1.le) ht.le dist_nonneg zero_le_one
      _ = p.bump.rOut := one_mul _
  -- the ball around `tt` of radius `rOut` lies in `Ω`
  have hci2 : 1 / 2 ≤ p.factor⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) hc0]; linarith
  have hci1 : p.factor⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc1
  have hr : p.bump.rOut < s₀ * (1 - p.factor⁻¹) / 4 := by
    rw [hpA.rOut_eq]
    have hgh := hpA.abs_factor_sub_one
    rw [abs_of_pos (by linarith)] at hgh
    have h1 : 1 - p.factor⁻¹ = (p.factor - 1) / p.factor := by field_simp
    rw [h1, hgh]
    have hgh0 : 0 < γ * h := by
      have : 0 < γ * h / R := by rw [← hgh]; linarith
      exact (div_pos_iff.1 this).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_lt.2 hR.le)
    have : γ * h * σ ≤ γ * h * (s₀ / (16 * R)) := mul_le_mul_of_nonneg_left hσ hgh0.le
    have h2 : s₀ * (γ * h / R / p.factor) / 4 ≥ s₀ * (γ * h / R) / 8 := by
      have : γ * h / R / p.factor ≥ γ * h / R / 2 :=
        div_le_div_of_nonneg_left (by positivity) hc0 hc2
      nlinarith
    have h3 : γ * h * (s₀ / (16 * R)) = s₀ * (γ * h / R) / 16 := by field_simp
    have h4 : 0 < s₀ * (γ * h / R) := by positivity
    linarith
  have hball := closedBall_dil_subset_of_starBall hstar hci2 hci1 hr (subset_closure htΩ)
  refine ⟨?_, ?_, hnorm⟩
  · refine ((convex_closedBall _ _).segment_subset ?_ (Metric.mem_closedBall_self
      p.bump.rOut_pos.le)).trans (hball.trans subset_closure)
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]; exact hnorm
  · have hseg := hstar t htΩ x₀ (Metric.mem_ball_self hs₀)
    have htt : tt ∈ segment ℝ x₀ t := by
      rw [segment_eq_image_lineMap]
      exact ⟨p.factor⁻¹, ⟨inv_nonneg.2 hc0.le, hci1.le⟩, by
        simp [tt, AffineMap.lineMap_apply_module']; abel⟩
    exact ((convex_segment x₀ t).segment_subset htt (right_mem_segment ℝ x₀ t)).trans
      (hseg.trans subset_closure)

/-- Points of a segment between two points of a closed ball lie in the ball. -/
theorem norm_sub_le_of_mem_segment {x a b q : Fin n → ℝ} {r : ℝ} (ha : ‖a - x‖ ≤ r)
    (hb : ‖b - x‖ ≤ r) (hq : q ∈ segment ℝ a b) : ‖q - x‖ ≤ r := by
  have := (convex_closedBall x r).segment_subset (by rwa [Metric.mem_closedBall, dist_eq_norm])
    (by rwa [Metric.mem_closedBall, dist_eq_norm]) hq
  rwa [Metric.mem_closedBall, dist_eq_norm] at this

end Paths

/-! ### The uniform `L²` bound of the smoothed interpolants -/

section Bound

/-- Shape regularity and quasi-uniformity of a mesh, with a positive mesh size. -/
structure MeshData (M : SimplicialMesh n) (C c q : ℝ) : Prop where
  shape : IsShapeRegular (M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) C c
  quasi : IsQuasiUniform M q
  meshSize_pos : 0 < M.meshSize

/-- The `L²` mass of `x` on the `r`-neighbourhood of `T`. -/
def locMass {Ω : Set (Fin n → ℝ)} {k : ℤ} (r : ℝ) (x : L2F ℝ Ω (formIdx n k))
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) : ℝ :=
  ∑ s : formIdx n k, ∫ t in Metric.cthickening r T.closedInterior,
    (Ω.indicator ((x s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t) ^ 2

theorem locMass_nonneg {Ω : Set (Fin n → ℝ)} {k : ℤ} (r : ℝ) (x : L2F ℝ Ω (formIdx n k))
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) : 0 ≤ locMass r x T :=
  Finset.sum_nonneg fun _ _ => setIntegral_nonneg Metric.isClosed_cthickening.measurableSet
    fun _ _ => sq_nonneg _

theorem integrable_sq_indicator {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (f : L2 ℝ Ω) :
    Integrable fun t => (Ω.indicator (f : (Fin n → ℝ) → ℝ) t) ^ 2 :=
  (memLp_indicator hΩ f).integrable_sq

theorem integral_sq_indicator {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (f : L2 ℝ Ω) :
    ∫ t, (Ω.indicator (f : (Fin n → ℝ) → ℝ) t) ^ 2 = ‖f‖ ^ 2 := by
  rw [norm_sq_eq_integral_sq]
  have e : (fun t => (Ω.indicator (f : (Fin n → ℝ) → ℝ) t) ^ 2) =
      Ω.indicator fun t => ((f : (Fin n → ℝ) → ℝ) t) ^ 2 := by
    funext t; by_cases ht : t ∈ Ω <;> simp [ht]
  rw [e, integral_indicator hΩ]

/-- The overlap constant `6ⁿ n! / (c qⁿ)`. -/
def covConst (n : ℕ) (c q : ℝ) : ℝ := 6 ^ n * n.factorial / (c * q ^ n)

open Classical in
/-- **Bounded overlap of the local masses**: `Σ_T m_T(x) ≤ 6ⁿ n! / (c qⁿ) ‖x‖²`. -/
theorem sum_locMass_le {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) (hc : 0 < c)
    (hq : 0 < q) (hΩ : MeasurableSet M.domain) {k : ℤ} (x : L2F ℝ M.domain (formIdx n k)) :
    ∑ T ∈ M.simplices, locMass (2 * M.meshSize) x T ≤ covConst n c q * ‖x‖ ^ 2 := by
  set h := M.meshSize
  have hh := hM.meshSize_pos
  set F : (Fin n → ℝ) → ℝ := fun t => ∑ s : formIdx n k,
    (M.domain.indicator ((x s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t) ^ 2
  have hF : Integrable F := integrable_finsetSum _ fun s _ => integrable_sq_indicator hΩ _
  have hF0 : ∀ t, 0 ≤ F t := fun t => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∀ T : Affine.Simplex ℝ (Fin n → ℝ) n, locMass (2 * h) x T =
      ∫ t in Metric.cthickening (2 * h) T.closedInterior, F t := fun T => by
    rw [locMass, integral_finsetSum _ fun s _ => (integrable_sq_indicator hΩ _).integrableOn]
  simp_rw [h1]
  have hK : ∀ t, ((M.simplices.filter fun T : Affine.Simplex ℝ (Fin n → ℝ) n =>
      t ∈ Metric.cthickening (2 * h) T.closedInterior).card : ℝ) ≤ covConst n c q := by
    intro t
    refine (card_filter_mem_cthickening_le M hM.shape hc hq hM.quasi hh (by positivity) t).trans
      (le_of_eq ?_)
    rw [covConst, show 2 * (2 * h + h) = 6 * h by ring, mul_pow, mul_pow]
    field_simp
    rfl
  refine (sum_integral_le_of_card_le M.simplices _ (fun T => Metric.isClosed_cthickening.measurableSet)
    hK hF hF0).trans (le_of_eq ?_)
  rw [integral_finsetSum _ fun s _ => integrable_sq_indicator hΩ _, PiLp.norm_sq_eq_of_L2]
  simp_rw [integral_sq_indicator hΩ]

variable {x₀ : Fin n → ℝ} {R σ γ : ℝ}

/-- **The smoothed field on a simplex is bounded by the local mass**:
`|R x (y)ₛ| ≤ 2ᵏ ((γ h σ)⁻ⁿ m_T(x))^{1/2}` on `T`. -/
theorem IsAdm.abs_smoothForm_le_locMass {M : SimplicialMesh n} {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hh : 0 < M.meshSize) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hγh : γ * M.meshSize / R ≤ 1) (hΩ : MeasurableSet M.domain) {k : ℕ}
    (x : L2F ℝ M.domain (formIdx n k)) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) :
    ∀ y ∈ T.closedInterior, ∀ s, |(smoothForm p hΩ k x : FormField n) y s| ≤
      2 ^ k * √((1 / (γ * M.meshSize * σ)) ^ n * locMass (2 * M.meshSize) x T) := by
  intro y hy s
  have hMρ : 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn) =
      (1 / (γ * M.meshSize * σ)) ^ n := by
    rw [hp.rIn_eq, FEM.volume_real_closedBall_zero (by positivity), one_div_pow]
    congr 2; ring
  refine (FEM.abs_smoothForm_le hΩ p k x y s).trans (mul_le_mul (hp.pow_factor_le hγh k)
    ?_ (Real.sqrt_nonneg _) (by positivity))
  rw [hMρ]
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s' _ => ?_)
    (by positivity))
  refine setIntegral_mono_set (integrable_sq_indicator hΩ _).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun t ht => ?_)
  have hyc : y ∈ closure M.domain := M.closedInterior_subset_closure hT hy
  have h1 := hp.norm_sub_le_of_dist_le hR hσ1 (hRx y hyc) (Metric.mem_closedBall.1 ht)
  refine Metric.mem_cthickening_of_dist_le t y _ _ hy ?_
  rw [dist_eq_norm]
  nlinarith

/-- `Σₛ ‖zₛ‖²_{L²(T)} ≤ 2ⁿ (2h)ⁿ K²` on a simplex of `M` when `|z| ≤ K` there. -/
theorem sum_integral_sq_le_of_abs_le {M : SimplicialMesh n} {k : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) {z : FormField n}
    (hzc : Continuous z) {K : ℝ} (hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ K) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2 ≤
      2 ^ n * ((2 * M.meshSize) ^ n * K ^ 2) := by
  have hTh : diam T ≤ M.meshSize := M.diam_le_meshSize hT
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, (2 * M.meshSize) ^ n * K ^ 2 := Finset.sum_le_sum fun s _ =>
        (integral_closedInterior_le (f := fun y => (z y s.1) ^ 2) (A := K ^ 2)
          (((continuous_apply s.1).comp hzc).pow 2)
          (fun y hy => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hzb y hy s.1) 2)
          (fun y => sq_nonneg _)).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
            (by linarith [diam_nonneg T]) (by linarith) n) (sq_nonneg _))
    _ = Fintype.card (formIdx n k) * ((2 * M.meshSize) ^ n * K ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * ((2 * M.meshSize) ^ n * K ^ 2) :=
        mul_le_mul_of_nonneg_right (FEM.card_formIdx_le _)
          (mul_nonneg (pow_nonneg (by linarith [diam_nonneg T]) n) (sq_nonneg _))

/-- **The `L²` norm of a glued field by local masses** (any element family on a quasi-uniform
shape-regular mesh): `‖glue u‖² ≤ K covConst ‖x‖²` when `Σₛ ‖(u_T)ₛ‖²_{L²(T)} ≤ K m_T(x)`. -/
theorem norm_sq_glue_le_locMass (E : LocalElement n) {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hc : 0 < c) (hq : 0 < q) (hΩ : MeasurableSet M.domain) {k : ℕ}
    (x : L2F ℝ M.domain (formIdx n k)) (u : E.Piecewise M k) {K : ℝ} (hK : 0 ≤ K)
    (hloc : ∀ T (hT : T ∈ M.simplices), ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((u ⟨T, hT⟩ : E.space T k) : FormField n) y s.1) ^ 2 ≤ K * locMass (2 * M.meshSize) x T) :
    ‖E.glue M k u‖ ^ 2 ≤ K * (covConst n c q * ‖x‖ ^ 2) := by
  refine (FEM.norm_sq_glue_le E M u _ hloc).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_locMass_le hM hc hq hΩ x) hK

/-- **The local `L²` bound of `Q = Π_h R`** on a simplex of a quasi-uniform shape-regular mesh:
`‖Q x‖²_{L²(T)} ≲ (2 / (γ σ))ⁿ m_T(x)`. -/
theorem sum_integral_sq_interp_le {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    [NeZero n] {k : ℕ} {B : ℝ}
    (hB : ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ {z : FormField n}, z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
        (∀ g ⊆ vertexSet T, g.card = k + 1 →
          |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
        ∀ x ∈ T.closedInterior, ∀ s, diam T ^ k * |z x s| ≤ B * D)
    (hR : 0 < R) (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm x₀ R σ γ M.meshSize p) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hγh : γ * M.meshSize / R ≤ 1)
    (hΩ : MeasurableSet M.domain) (x : L2F ℝ M.domain (formIdx n k))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((whitneyElement n).globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) :
          (whitneyElement n).Piecewise M k) ⟨T, hT⟩ : (whitneyElement n).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (2 / (γ * σ)) ^ n * locMass (2 * M.meshSize) x T := by
  set h := M.meshSize
  have hh : 0 < h := hM.meshSize_pos
  have hT0 : 0 < diam T := diam_pos T
  set z : FormField n := ((((whitneyElement n).globalInterp M k
    (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) :
      (whitneyElement n).Piecewise M k) ⟨T, hT⟩ : (whitneyElement n).space T k) : FormField n)
  have hz : z ∈ p1MinusForms n k := FEM.mem_p1MinusForms_of_space _
  set L := locMass (2 * h) x T
  have hL := locMass_nonneg (2 * h) x T
  set A := 2 ^ k * √((1 / (γ * h * σ)) ^ n * L)
  have hA0 : 0 ≤ A := by positivity
  -- the face integrals of `z` are `O(h_Tᵏ A)`, hence `|z| ≤ B 2ⁿ A` on `T`
  have hdof : ∀ g ⊆ vertexSet T, g.card = k + 1 →
      |simplexIntegral (faceEnum g (k + 1)) z| ≤ 2 ^ n * diam T ^ k * A := by
    intro g hgT hg
    rw [FEM.simplexIntegral_globalInterp k _ ⟨T, hT⟩ hgT hg]
    exact abs_simplexIntegral_face_le' hgT hg hA0
      (hp.abs_smoothForm_le_locMass hh hR hRx hγ hγ1 hσ hσ1 hγh hΩ x hT)
  have hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ B * 2 ^ n * A := fun y hy s =>
    le_of_mul_le_mul_left ((hB hM.shape T hT hT0 hz (by positivity) hdof y hy s).trans
      (le_of_eq (by ring))) (pow_pos hT0 k)
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ 2 ^ n * ((2 * h) ^ n * (B * 2 ^ n * A) ^ 2) :=
        sum_integral_sq_le_of_abs_le hT (isAffineField_of_mem_p1MinusForms hz).continuous hzb
    _ = 2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (2 * h * (1 / (γ * h * σ))) ^ n * L := by
        rw [mul_pow (B * 2 ^ n) A, mul_pow (2 ^ k), Real.sq_sqrt (by positivity), mul_pow (2 * h)]
        ring
    _ = 2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (2 / (γ * σ)) ^ n * L := by
        rw [show 2 * h * (1 / (γ * h * σ)) = 2 / (γ * σ) by field_simp]

/-- **The uniform `L²` bound of the smoothed interpolants** `Q = Π_h R` on quasi-uniform
shape-regular meshes of a domain star-shaped with respect to a ball, for every admissible
parameter at scale `γ h` (either family): `‖Q x‖ ≤ K ‖x‖`, with `K` depending only on
`n, C, c, q, γ, σ`. -/
theorem exists_norm_smoothedInterp_le [NeZero n] {C c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ K, 0 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩ : MeasurableSet M.domain),
      0 < R → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) → γ * M.meshSize / R ≤ 1 →
      ∀ (p : SmoothingParam (Fin n → ℝ)), IsAdm x₀ R σ γ M.meshSize p →
      ∀ (k : ℕ) (x : L2F ℝ M.domain (formIdx n k)),
        ‖(whitneyElement n).smoothedInterp M p hΩ k x‖ ≤ K * ‖x‖ := by
  choose B hB0 hB using fun k : ℕ => exists_dof_bound_p1MinusForms (n := n) k (C := C) (c := c)
  have hG : ∀ k, 0 ≤ 2 ^ n * (B k * 2 ^ n * 2 ^ k) ^ 2 * (2 / (γ * σ)) ^ n * covConst n c q :=
    fun k => by have := hB0 k; simp only [covConst]; positivity
  refine ⟨_, Real.sqrt_nonneg _, fun M hM hΩ hR hRx hγh p hp k x =>
    FEM.norm_le_sqrt_sum_of_sq_le hG fun _ => ?_⟩
  rw [(whitneyElement n).smoothedInterp_natCast, mul_assoc]
  exact norm_sq_glue_le_locMass _ hM hc hq hΩ x _ (by have := hB0 k; positivity)
    fun T hT => sum_integral_sq_interp_le hM (hB k) hR hRx hp hγ hγ1 hσ hσ1 hγh hΩ x hT

end Bound

/-! ### Closeness of the smoothed interpolants to the identity on `Vₕ` -/

section Close

/-- The local inverse estimates on all simplices of `M`, in terms of the mesh size. -/
def InvBoundM (M : SimplicialMesh n) (k : ℕ) (A : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∀ z ∈ p1MinusForms n k,
    (∀ x ∈ T.closedInterior, ∀ s, √M.meshSize ^ n * |z x s| ≤
      A * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2)) ∧
    (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
      √M.meshSize ^ n * M.meshSize * |z x s - z x' s| ≤
        A * ‖x - x'‖ * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2))

theorem MeshData.q_le_one {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) :
    q ≤ 1 := by
  have hh := hM.meshSize_pos
  obtain ⟨T, hT⟩ : M.simplices.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : M.meshSize ≤ 0 := M.meshSize_le le_rfl fun T hT => by simp [hne] at hT
    linarith
  have h1 := hM.quasi T hT
  have h2 := M.diam_le_meshSize hT
  by_contra h
  push Not at h
  nlinarith

theorem MeshData.diam_pos {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    0 < diam T :=
  lt_of_lt_of_le (mul_pos hq hM.meshSize_pos) (hM.quasi T hT)

/-- **Inverse estimates on the mesh in terms of the mesh size**, from the shape-regular local
inverse estimates and quasi-uniformity: `A' = A q^{-n/2} q⁻¹`. -/
theorem invBoundM_of {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) (hq : 0 < q)
    {k : ℕ} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ u ∈ p1MinusForms n k,
        (∀ x ∈ T.closedInterior, ∀ s, √(diam T) ^ n * |u x s| ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
          √(diam T) ^ n * diam T * |u x s - u x' s| ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u))) :
    InvBoundM M k (A / √q ^ n / q) := by
  intro T hT z hz
  have hh := hM.meshSize_pos
  have hq1 := hM.q_le_one
  have hTd := hM.diam_pos hq hT
  obtain ⟨h1, h2⟩ := hA hM.shape T hT hTd z hz
  simp only [formL2Sq] at h1 h2
  set F := ∑ s, ∫ x in T.closedInterior, (z x s) ^ 2
  have hqh : q * M.meshSize ≤ diam T := hM.quasi T hT
  have hsq : √M.meshSize ^ n * √q ^ n ≤ √(diam T) ^ n := by
    rw [← mul_pow, ← Real.sqrt_mul hh.le]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) n
  have hsqq : 0 < √q ^ n := pow_pos (Real.sqrt_pos.2 hq) n
  have hF : 0 ≤ √F := Real.sqrt_nonneg _
  constructor
  · intro x hx s
    have := h1 x hx s
    have hk : √M.meshSize ^ n * |z x s| ≤ A / √q ^ n * √F := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsqq]
      calc √M.meshSize ^ n * |z x s| * √q ^ n = (√M.meshSize ^ n * √q ^ n) * |z x s| := by ring
        _ ≤ √(diam T) ^ n * |z x s| := mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
        _ ≤ _ := this
    refine hk.trans (mul_le_mul_of_nonneg_right ?_ hF)
    exact le_div_self (by positivity) hq hq1
  · intro x hx x' hx' s
    have := h2 x hx x' hx' s
    rw [div_div]
    rw [show A / (√q ^ n * q) * ‖x - x'‖ * √F =
      ‖x - x'‖ * A * √F / (√q ^ n * q) by ring]
    rw [le_div_iff₀ (by positivity)]
    calc √M.meshSize ^ n * M.meshSize * |z x s - z x' s| * (√q ^ n * q)
        = (√M.meshSize ^ n * √q ^ n) * (q * M.meshSize) * |z x s - z x' s| := by ring
      _ ≤ √(diam T) ^ n * diam T * |z x s - z x' s| := by
          gcongr
      _ ≤ A * ‖x - x'‖ * √F := this
      _ = ‖x - x'‖ * A * √F := by ring

variable {x₀ : Fin n → ℝ} {R σ γ : ℝ}

/-- The geometric condition of the smoother: at points of a `k`-face `g` with barycentric
weights `≥ θ`, every simplex whose interior contains a sample contains `g`. -/
def GeomOK (M : SimplicialMesh n) (p : SmoothingParam (Fin n → ℝ)) (θ : ℝ) (k : ℕ) : Prop :=
  ∀ (T : M.simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → g.card = k + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex k, ξ ∉ FEM.nearBdry k θ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (faceEnum g (k + 1)) ξ - p.center)) <
        p.bump.rOut → ∀ T' : M.simplices,
        t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
        g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)

/-- The sampling condition: a sample outside `Ω` at points of a `k`-face `g` with weights `≥ θ`
forces the face integral to vanish (vacuous for the maximal family; for the minimal family it is
the vanishing of the boundary DOFs of `V̊ₕ`). -/
def SampleOK {M : SimplicialMesh n} {k : ℕ} (p : SmoothingParam (Fin n → ℝ)) (θ : ℝ)
    (u : (whitneyElement n).Piecewise M k) : Prop :=
  ∀ (T : M.simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → g.card = k + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex k, ξ ∉ FEM.nearBdry k θ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (faceEnum g (k + 1)) ξ - p.center)) <
        p.bump.rOut → t ∉ M.domain →
        simplexIntegral (faceEnum g (k + 1)) ((u T : (whitneyElement n).space T k) : FormField n) = 0

open Classical in
/-- **The pointwise estimate of the face integrand of `v - Q v`** (`v ∈ Vₕ`) on a quasi-uniform
shape-regular mesh: at `x = F_g(ξ)`,
`h^{n/2} |Σₛ (v_T - R v)(x)ₛ minorₛ| ≤ (Σₛ |minorₛ|) A m_T(v)^{1/2} 2^{k+1} · (1 or 2 (k + 1) γ)`,
with the factor `2 (k + 1) γ` when all barycentric coordinates of `ξ` are `≥ θ`. -/
theorem sqrt_mul_abs_integrand_le {M : SimplicialMesh n} (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundM M k A) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ}
    (hgeom : GeomOK M p θ k) {u : (whitneyElement n).Piecewise M k}
    (hu : u ∈ (whitneyElement n).globalSpace M k) (hs : SampleOK p θ u) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hg : g.card = k + 1) {ξ : Fin k → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex k) :
    √M.meshSize ^ n * |∑ s, (((u T : (whitneyElement n).space T k) : FormField n)
        (simplexMap (faceEnum g (k + 1)) ξ) s -
      (smoothForm p hΩ k ((whitneyElement n).glue M k u) : FormField n)
        (simplexMap (faceEnum g (k + 1)) ξ) s) *
          wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ| ≤
      (∑ s, |wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ|) * A *
        √(locMass (2 * M.meshSize) ((whitneyElement n).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        2 ^ (k + 1) * (if ξ ∈ FEM.nearBdry k θ then 1 else (k + 1) * (2 * γ)) := by
  set h := M.meshSize
  have hγ1 : γ ≤ 1 := by linarith
  have hγh : γ * h / R ≤ 1 := by
    rw [div_le_one hR]; nlinarith
  set q := faceEnum g (k + 1)
  set x := simplexMap q ξ
  set uT : FormField n := ((u T : (whitneyElement n).space T k) : FormField n)
  set L := locMass (2 * h) ((whitneyElement n).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    FEM.simplexMap_faceEnum_mem hgT hg hξ
  have hxc : x ∈ closure M.domain := M.closedInterior_subset_closure T.2 hxT
  -- the local fields near `x` obey the inverse estimates against the local mass of `T`
  have hinv : ∀ T' : M.simplices, (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
      (∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * |((u T' : (whitneyElement n).space T' k) : FormField n) y s| ≤ A * √L) ∧
      ∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        ∀ y' ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * h * |((u T' : (whitneyElement n).space T' k) : FormField n) y s -
          ((u T' : (whitneyElement n).space T' k) : FormField n) y' s| ≤ A * ‖y - y'‖ * √L := by
    intro T' hsub
    have hL' := Real.sqrt_le_sqrt (FEM.sum_integral_sq_le_of_subset (whitneyElement n) hΩ hint u T'
      hsub)
    obtain ⟨h1, h2⟩ := hA T' T'.2 _ (FEM.mem_p1MinusForms_of_space (u T'))
    exact ⟨fun y hy s => (h1 y hy s).trans (mul_le_mul_of_nonneg_left hL' hA0),
      fun y hy y' hy' s => (h2 y hy y' hy' s).trans
        (mul_le_mul_of_nonneg_left hL' (by positivity))⟩
  refine FEM.sqrt_mul_abs_sum_sub_smoothForm_le hΩ p _ x (uT x) _ (ξ ∈ FEM.nearBdry k θ)
    (pow_pos (Real.sqrt_pos.2 hh) n) hA0 (by positivity) (hp.pow_factor_le hγh k)
    ((hp.abs_one_sub_pow_le hR hγh k).trans (mul_le_mul_of_nonneg_left
      (by rw [div_le_iff₀ hR]; nlinarith) (by positivity)))
    (fun s => (hinv T (FEM.self_subset_cthickening _ (by positivity))).1 x hxT s) ?_ ?_
  · filter_upwards [FEM.ae_extField_glue_eq (whitneyElement n) u hΩ] with t ht hdist htΩ
    obtain ⟨T', htT', hext⟩ := ht htΩ
    set u' : FormField n := ((u T' : (whitneyElement n).space T' k) : FormField n)
    have htT'c : t ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset htT'
    have hxt' : ‖t - x‖ ≤ 2 * (γ * h) := hp.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) hdist.le
    obtain ⟨hb1, hb2⟩ := hinv T' (closedInterior_subset_cthickening hh hγ2 hxT htT'c T'.2 hxt')
    refine ⟨u', hext, fun s => hb1 t htT'c s, fun hbad => ?_⟩
    have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
      hgeom T g hgT hg ξ hξ hbad t hdist T' htT'
    have hxT' := FEM.simplexMap_faceEnum_mem hgT' hg hξ
    refine ⟨?_, fun s => hb1 x hxT' s, fun s => ?_⟩
    · rw [FEM.sum_mul_minor_eq (FEM.mem_p1MinusForms_of_space (u T)) q ξ,
        FEM.sum_mul_minor_eq (FEM.mem_p1MinusForms_of_space (u T')) q ξ,
        FEM.simplexIntegral_eq_of_mem_globalSpace hu T T' hgT hgT' hg]
    · refine le_of_mul_le_mul_right ?_ hh
      calc √h ^ n * |u' x s - u' t s| * h = √h ^ n * h * |u' x s - u' t s| := by ring
        _ ≤ A * ‖x - t‖ * √L := hb2 x hxT' t htT'c s
        _ ≤ A * (2 * (γ * h)) * √L := by rw [norm_sub_rev]; gcongr
        _ = 2 * γ * (A * √L) * h := by ring
  · intro hbad t hdist htΩ
    rw [FEM.sum_mul_minor_eq (FEM.mem_p1MinusForms_of_space (u T)) q ξ]
    change ↑k.factorial * simplexIntegral q uT = 0
    rw [hs T g hgT hg ξ hξ hbad t hdist htΩ, mul_zero]

/-- **The DOF error of `Q` on `Vₕ`**: for a `k`-face `g` of `T`,
`h^{n/2} |∫_g (v_T - R v)| ≤ 2 (k + 1) 2ⁿ k! 2^{k+1} A (γ + θ) hᵏ m_T(v)^{1/2}`. -/
theorem sqrt_mul_abs_dof_err_le {M : SimplicialMesh n} (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundM M k A) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : GeomOK M p θ k) {u : (whitneyElement n).Piecewise M k}
    (hu : u ∈ (whitneyElement n).globalSpace M k) (hs : SampleOK p θ u) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hg : g.card = k + 1) :
    √M.meshSize ^ n * |simplexIntegral (faceEnum g (k + 1))
        ((u T : (whitneyElement n).space T k) : FormField n) -
      simplexIntegral (faceEnum g (k + 1))
        (smoothForm p hΩ k ((whitneyElement n).glue M k u) : FormField n)| ≤
      2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A * (γ + θ) * M.meshSize ^ k *
        √(locMass (2 * M.meshSize) ((whitneyElement n).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  classical
  set h := M.meshSize
  set q := faceEnum g (k + 1)
  set uT : FormField n := ((u T : (whitneyElement n).space T k) : FormField n)
  set w : FormField n := (smoothForm p hΩ k ((whitneyElement n).glue M k u) : FormField n)
  set m : Finset (Fin n) → ℝ := fun s => wedgeProd (simplexMatrix q) s univ
  set L := locMass (2 * h) ((whitneyElement n).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hMm : ∑ s, |m s| ≤ 2 ^ n * (k.factorial * h ^ k) :=
    (sum_abs_minor_face_le' hgT hg).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (diam_nonneg _) (M.diam_le_meshSize T.2) k) (by positivity))
      (by positivity))
  have huc : Continuous uT :=
    (isAffineField_of_mem_p1MinusForms (FEM.mem_p1MinusForms_of_space _)).continuous
  have hwc : Continuous w := (mem_c1Forms.1 (smoothForm p hΩ k
    ((whitneyElement n).glue M k u)).2).continuous
  set F : (Fin k → ℝ) → ℝ := fun ξ => ∑ s, (uT (simplexMap q ξ) s - w (simplexMap q ξ) s) * m s
  have hFc : Continuous F := continuous_finsetSum _ fun s _ =>
    ((((continuous_apply s).comp (huc.comp (continuous_simplexMap q))).sub
      ((continuous_apply s).comp (hwc.comp (continuous_simplexMap q)))).mul continuous_const)
  have herr : simplexIntegral q uT - simplexIntegral q w =
      ∫ ξ in FiniteElement.refSimplex k, F ξ := by
    rw [← simplexIntegral_sub huc.continuousOn hwc.continuousOn, simplexIntegral_def]
    rfl
  set c := 2 ^ n * (k.factorial * h ^ k) * A * √L * 2 ^ (k + 1)
  have hc0 : 0 ≤ c := by positivity
  rw [herr]
  refine (FEM.mul_abs_integral_refSimplex_le hFc (pow_nonneg (Real.sqrt_nonneg _) n) hc0
    (by positivity) hθ0 hθ1 fun ξ hξ =>
      (sqrt_mul_abs_integrand_le hΩ hint hA0 hA hp hR hRx hhR hh hγ hγ2 hσ1 hgeom hu hs T
        hgT hg hξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMm hA0) (Real.sqrt_nonneg _)) (by positivity))
        (by split_ifs <;> positivity))).trans ?_
  have : 0 ≤ c * ((k + 1) * θ) := by positivity
  calc c * ((k + 1) * (2 * γ) + (k + 1) * θ) ≤ c * ((k + 1) * (2 * γ)) + 2 * (c * ((k + 1) * θ)) := by
        linarith
    _ = _ := by simp only [c]; ring

/-- **The local `L²` error of `Q` on `Vₕ`**: `‖v - Q v‖²_{L²(T)} ≲ (γ + θ)² m_T(v)`. -/
theorem sum_integral_sq_sub_interp_le {M : SimplicialMesh n} [NeZero n] {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A B : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundM M k A)
    (hB : ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ {z : FormField n}, z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
        (∀ g ⊆ vertexSet T, g.card = k + 1 →
          |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
        ∀ x ∈ T.closedInterior, ∀ s, diam T ^ k * |z x s| ≤ B * D)
    {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : GeomOK M p θ k) {u : (whitneyElement n).Piecewise M k}
    (hu : u ∈ (whitneyElement n).globalSpace M k) (hs : SampleOK p θ u) (T : M.simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (whitneyElement n).space T k) : FormField n) -
        ((((whitneyElement n).globalInterp M k
          (Submodule.inclusion c1Forms_le_contForms
            (smoothForm p hΩ k ((whitneyElement n).glue M k u))) :
            (whitneyElement n).Piecewise M k) T : (whitneyElement n).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      4 ^ n * (B * (2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2 *
        locMass (2 * M.meshSize) ((whitneyElement n).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := M.meshSize
  have hh : 0 < h := hM.meshSize_pos
  set w := smoothForm p hΩ k ((whitneyElement n).glue M k u)
  set z : FormField n := ((u T : (whitneyElement n).space T k) : FormField n) -
    ((((whitneyElement n).globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) :
      (whitneyElement n).Piecewise M k) T : (whitneyElement n).space T k) : FormField n)
  have hz : z ∈ p1MinusForms n k := Submodule.sub_mem _ (FEM.mem_p1MinusForms_of_space _)
    (FEM.mem_p1MinusForms_of_space _)
  set L := locMass (2 * h) ((whitneyElement n).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _ _
  set C₁ := 2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A
  have hC₁ : 0 ≤ C₁ := by positivity
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hγθ : 0 ≤ γ + θ := by linarith
  set D := C₁ * (γ + θ) * h ^ k * √L / √h ^ n
  have hD0 : 0 ≤ D := by positivity
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), g.card = k + 1 →
      |simplexIntegral (faceEnum g (k + 1)) z| ≤ D := by
    intro g hgT hg
    have hc1 : Continuous ((u T : (whitneyElement n).space T k) : FormField n) :=
      (isAffineField_of_mem_p1MinusForms (FEM.mem_p1MinusForms_of_space _)).continuous
    have hc2 : Continuous ((((whitneyElement n).globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms w) : (whitneyElement n).Piecewise M k) T :
          (whitneyElement n).space T k) : FormField n) :=
      (isAffineField_of_mem_p1MinusForms (FEM.mem_p1MinusForms_of_space _)).continuous
    rw [simplexIntegral_sub hc1.continuousOn hc2.continuousOn,
      FEM.simplexIntegral_globalInterp k _ T hgT hg, le_div_iff₀ hsq, mul_comm]
    exact sqrt_mul_abs_dof_err_le hΩ hint hA0 hA hp hR hRx hhR hh hγ hγ2 hσ1 hθ0 hθ1 hgeom hu hs
      T hgT hg
  have hTd := hM.diam_pos hq T.2
  have hqh : q * h ≤ diam (T : Affine.Simplex ℝ (Fin n → ℝ) n) := hM.quasi T T.2
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * (C₁ * (γ + θ) / q ^ k) * √L / √h ^ n := by
    intro y hy s
    have h1 := hB hM.shape T T.2 hTd hz hD0 hdof y hy s
    have hqk : 0 < (q * h) ^ k := pow_pos (mul_pos hq hh) k
    have h2 : (q * h) ^ k * |z y s| ≤ B * D :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hqh k) (abs_nonneg _)).trans h1
    refine le_of_mul_le_mul_left (h2.trans (le_of_eq ?_)) hqk
    simp only [D]; field_simp; ring
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (z y s.1) ^ 2
      ≤ 2 ^ n * ((2 * h) ^ n * (B * (C₁ * (γ + θ) / q ^ k) * √L / √h ^ n) ^ 2) :=
        sum_integral_sq_le_of_abs_le T.2 (isAffineField_of_mem_p1MinusForms hz).continuous hzb
    _ = 4 ^ n * (B * C₁ * (γ + θ) / q ^ k) ^ 2 * (√L) ^ 2 := by
        rw [mul_pow 2 h, hhn, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by
          rw [← mul_pow]; norm_num]
        field_simp
    _ = 4 ^ n * (B * C₁ * (γ + θ) / q ^ k) ^ 2 * L := by rw [Real.sq_sqrt hL0]

/-- **`Q` is close to the identity on `Vₕ`**:
`‖v - Q v‖² ≤ 4ⁿ (B C₁ (γ + θ) / qᵏ)² 6ⁿ n! / (c qⁿ) ‖v‖²`. -/
theorem norm_sq_sub_smoothedInterp_le {M : SimplicialMesh n} [NeZero n] {C c q : ℝ}
    (hM : MeshData M C c q) (hc : 0 < c) (hq : 0 < q) (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A B : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundM M k A)
    (hB : ∀ {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular S C c →
      ∀ T ∈ S, 0 < diam T → ∀ {z : FormField n}, z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
        (∀ g ⊆ vertexSet T, g.card = k + 1 →
          |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
        ∀ x ∈ T.closedInterior, ∀ s, diam T ^ k * |z x s| ≤ B * D)
    {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : GeomOK M p θ k) {u : (whitneyElement n).Piecewise M k}
    (hu : u ∈ (whitneyElement n).globalSpace M k) (hs : SampleOK p θ u) :
    ‖(whitneyElement n).glue M k u - (whitneyElement n).smoothedInterp M p hΩ k
        ((whitneyElement n).glue M k u)‖ ^ 2 ≤
      4 ^ n * (B * (2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2 *
        (covConst n c q * ‖(whitneyElement n).glue M k u‖ ^ 2) := by
  set v := (whitneyElement n).glue M k u
  have hQ := (whitneyElement n).smoothedInterp_natCast M p hΩ k v
  set Pw := (whitneyElement n).globalInterp M k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p hΩ k v))
  set d : (whitneyElement n).Piecewise M k := u - (Pw : (whitneyElement n).Piecewise M k)
  have hsub : v - (whitneyElement n).smoothedInterp M p hΩ k v = (whitneyElement n).glue M k d := by
    rw [hQ, map_sub]
  rw [hsub]
  exact norm_sq_glue_le_locMass _ hM hc hq hΩ v d (by positivity) fun T hT =>
    sum_integral_sq_sub_interp_le hM hq hΩ hint hA0 hA hB hp hR hRx hhR hγ hγ2 hσ1 hθ0 hθ1
      hgeom hu hs ⟨T, hT⟩

end Close

/-! ### The geometric and sampling conditions for both families -/

section Families

variable {x₀ : Fin n → ℝ} {s₀ R σ γ : ℝ}

/-- The barycentric coordinates of a quasi-uniform shape-regular mesh are Lipschitz with constant
`n (n + 1) C / (q h)`. -/
theorem coordLip_of {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) (hq : 0 < q)
    (hC : 0 ≤ C) : StarGeom.CoordLip M (n * ((n + 1) * (C / (q * M.meshSize)))) := by
  intro T hT i y y'
  refine (abs_coord_sub_le T i y y').trans ?_
  obtain ⟨-, hBs, -⟩ := hM.shape T hT
  have hT0 := hM.diam_pos hq hT
  have h1 : ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ≤ C / (q * M.meshSize) :=
    hBs.trans (div_le_div_of_nonneg_left hC (mul_pos hq hM.meshSize_pos) (hM.quasi T hT))
  gcongr

theorem isFacePoint_of_notMem_nearBdry {M : SimplicialMesh n} {k : ℕ} {g : Finset (Fin n → ℝ)}
    (hg : g.card = k + 1) {θ : ℝ} {ξ : Fin k → ℝ} (hξ : ξ ∉ FEM.nearBdry k θ) :
    StarGeom.IsFacePoint M g θ (simplexMap (faceEnum g (k + 1)) ξ) := by
  rw [simplexMap_eq_sum]
  refine StarGeom.isFacePoint_sum_smul (injective_faceEnum hg) (range_faceEnum hg)
    (fun a => ?_) (sum_refBary ξ)
  by_contra hlt; push Not at hlt; exact hξ ⟨a, hlt⟩

theorem coord_near {M : SimplicialMesh n} {C q : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) {x y : Fin n → ℝ}
    (hy : ‖y - x‖ ≤ 2 * (γ * M.meshSize)) :
    n * ((n + 1) * (C / (q * M.meshSize))) * ‖y - x‖ < θ := by
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy (by positivity)) (lt_of_eq_of_lt ?_ hθ)
  field_simp

/-- **The geometric condition for the maximal family.** -/
theorem geomOK_of_isMaximal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀) (hs₀ : 0 < s₀)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) (k : ℕ) : GeomOK M p θ k := by
  intro T g hgT hg ξ hξ hξb t ht T' htT'
  have hh := hM.meshSize_pos
  set x := simplexMap (faceEnum g (k + 1)) ξ
  have hx := isFacePoint_of_notMem_nearBdry (M := M) hg hξb
  have hxT := FEM.simplexMap_faceEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  obtain ⟨h1, h2⟩ := path_of_isMaximal hstar hs₀ hp hxc ht
  have hgh := hpA.gh_nonneg hR
  have hŷ : ‖(p.center + p.factor • (x - p.center)) - x‖ ≤ 2 * (γ * M.meshSize) :=
    (hpA.norm_dil_sub_le hR (hRx x hxc)).trans (by linarith)
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have hxx : ‖x - x‖ ≤ 2 * (γ * M.meshSize) := by rw [sub_self, norm_zero]; positivity
  exact StarGeom.subset_vertexSet_of_segments (coordLip_of hM hq hC) hx
    (StarGeom.mem_starSet.2 ⟨T, T.2, hgT, hxT⟩) h1
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hxx hŷ hy)) h2
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hŷ ht' hy)) T'.2 htT'

/-- **The geometric condition for the minimal family.** -/
theorem geomOK_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀) (hs₀ : 0 < s₀)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMinimal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hσ : σ ≤ s₀ / (16 * R))
    (hγ : 0 < γ) (hγh : γ * M.meshSize / R ≤ 1) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) (k : ℕ) : GeomOK M p θ k := by
  intro T g hgT hg ξ hξ hξb t ht T' htT'
  have hh := hM.meshSize_pos
  set x := simplexMap (faceEnum g (k + 1)) ξ
  have hx := isFacePoint_of_notMem_nearBdry (M := M) hg hξb
  have hxT := FEM.simplexMap_faceEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have htΩ := hint T' T'.2 htT'
  obtain ⟨h1, h2, h3⟩ := path_of_isMinimal hstar hs₀ hR hp hpA hγh hσ htΩ ht
  have hgh := hpA.gh_nonneg hR
  have htt : ‖x₀ + p.factor⁻¹ • (t - x₀) - x‖ ≤ 2 * (γ * M.meshSize) := by
    refine h3.trans ?_
    rw [hpA.rOut_eq]; nlinarith
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have hxx : ‖x - x‖ ≤ 2 * (γ * M.meshSize) := by rw [sub_self, norm_zero]; positivity
  exact StarGeom.subset_vertexSet_of_segments (coordLip_of hM hq hC) hx
    (StarGeom.mem_starSet.2 ⟨T, T.2, hgT, hxT⟩) h1
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hxx htt hy)) h2
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment htt ht' hy)) T'.2 htT'

/-- **The maximal family samples only inside `Ω`**, so the sampling condition holds for every
field. -/
theorem sampleOK_of_isMaximal {M : SimplicialMesh n} (hstar : StarBall M.domain x₀ s₀)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀) {θ : ℝ} {k : ℕ}
    (u : (whitneyElement n).Piecewise M k) : SampleOK p θ u := by
  intro T g hgT hg ξ hξ _ t ht htΩ
  exfalso
  have hxT := FEM.simplexMap_faceEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have := closedBall_dil_subset_of_starBall hstar p.half_le_factor hp.factor_lt_one hp.rOut_lt hxc
  rw [← hp.center_eq] at this
  exact htΩ (this (Metric.mem_closedBall.2 ht.le))

/-- **The minimal family satisfies the sampling condition on `V̊ₕ`**: a sample outside `Ω` near a
point of a face with weights `≥ θ` forces the face into a boundary facet
(`StarGeom.exists_isBoundaryFacet_of_near`), where the DOFs of `V̊ₕ` vanish. -/
theorem sampleOK_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) {p : SmoothingParam (Fin n → ℝ)}
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) {k : ℕ}
    {u : (whitneyElement n).Piecewise M k} (hu : u ∈ (whitneyElement n).globalSpace₀ M k) :
    SampleOK p θ u := by
  classical
  intro T g hgT hg ξ hξ hξb t ht htΩ
  have hh := hM.meshSize_pos
  set x := simplexMap (faceEnum g (k + 1)) ξ
  have hx := isFacePoint_of_notMem_nearBdry (M := M) hg hξb
  have hxT := FEM.simplexMap_faceEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have htc : t ∉ interior (closure M.domain) := fun h' =>
    htΩ (hstar.interior_closure_subset hs₀ h')
  obtain ⟨F, hF, hgF⟩ := StarGeom.exists_isBoundaryFacet_of_near (by positivity)
    (coordLip_of hM hq hC) hx T.2 hgT hxT htc (coord_near hq hC hh hγ hθ ht')
  obtain ⟨-, T'', hT'', hFT''⟩ := hF.1
  have h0 := hu.2 ⟨T'', hT''⟩ F hF hFT'' g hgF (⟨(), hg⟩ : WhitneyDofIdx g k)
  rw [FEM.simplexIntegral_localDof ⟨T'', hT''⟩ hg] at h0
  rw [FEM.simplexIntegral_eq_of_mem_globalSpace hu.1 T ⟨T'', hT''⟩ hgT (hgF.trans hFT'') hg]
  exact h0

end Families

/-! ### The smoothing scale and the smoothed-projection estimates -/

section Estimates

variable {x₀ : Fin n → ℝ}

variable (n) in
/-- **The smoothing scale** `γ` and the threshold `θ`, depending only on `n, C, c, q`: for every
admissible parameter at scale `γ h` (either family) satisfying the geometric and sampling
conditions at threshold `θ`, `‖v - Q v‖ ≤ ½ ‖v‖` on `Vₕ`. -/
theorem exists_gamma [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hq : 0 < q) :
    ∃ γ θ : ℝ, 0 < γ ∧ γ ≤ 1 / 4 ∧ 0 ≤ θ ∧ θ ≤ 1 ∧ 2 * (n * ((n + 1) * C)) / q * γ < θ ∧
      ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩ : MeasurableSet M.domain),
      (∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) →
      ∀ {R σ : ℝ}, 0 < R → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) → M.meshSize ≤ 2 * R →
      σ ≤ 1 → ∀ (p : SmoothingParam (Fin n → ℝ)), IsAdm x₀ R σ γ M.meshSize p →
      ∀ (k : ℕ), GeomOK M p θ k → ∀ u ∈ (whitneyElement n).globalSpace M k, SampleOK p θ u →
        ‖(whitneyElement n).glue M k u - (whitneyElement n).smoothedInterp M p hΩ k
          ((whitneyElement n).glue M k u)‖ ≤ 1 / 2 * ‖(whitneyElement n).glue M k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_inverse_bound_p1MinusForms (n := n) k hC hc
  choose B hB0 hB using fun k : ℕ => exists_dof_bound_p1MinusForms (n := n) k (C := C) (c := c)
  set K₀ : ℝ := 2 * (n * ((n + 1) * C)) / q + 1
  have hK₀ : 1 ≤ K₀ := by simp only [K₀]; have : 0 ≤ 2 * (n * ((n + 1) * C)) / q := by positivity
                          linarith
  set A' : ℕ → ℝ := fun k => A k / √q ^ n / q
  have hA'0 : ∀ k, 0 ≤ A' k := fun k => by have := hA0 k; simp only [A']; positivity
  set x : ℕ → ℝ := fun k =>
    B k * (2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A' k) * (1 + K₀) / q ^ k
  have hx0 : ∀ k, 0 ≤ x k := fun k => by
    have := hB0 k; have := hA'0 k; simp only [x]; positivity
  set S := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hx0 k
  set Kc : ℝ := max 1 (4 ^ n * covConst n c q)
  have hKc : 1 ≤ Kc := le_max_left _ _
  set γ₀ := 1 / (2 * (1 + S * Kc))
  have hpos : 0 < 1 + S * Kc := by nlinarith
  have hγ₀ : 0 < γ₀ := by positivity
  set γ := min (min (1 / 4) (1 / K₀)) γ₀
  have hγ : 0 < γ := lt_min (lt_min (by norm_num) (by positivity)) hγ₀
  have hγ4 : γ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hγK : γ ≤ 1 / K₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hγγ₀ : γ ≤ γ₀ := min_le_right _ _
  refine ⟨γ, K₀ * γ, hγ, hγ4, by positivity, ?_, ?_, ?_⟩
  · calc K₀ * γ ≤ K₀ * (1 / K₀) := mul_le_mul_of_nonneg_left hγK (by linarith)
      _ = 1 := by field_simp
  · have : 2 * (n * ((n + 1) * C)) / q * γ < (2 * (n * ((n + 1) * C)) / q + 1) * γ := by
      nlinarith
    exact this
  intro M hM hΩ hint R σ hR hRx hhR hσ1 p hp k hgeom u hu hs
  by_cases hk : n < k
  · have := FEM.subsingleton_L2F_of_lt (Ω := M.domain) hk
    rw [Subsingleton.elim ((whitneyElement n).glue M k u) 0]; simp
  push Not at hk
  have hInv := invBoundM_of hM hq (hA0 k) (hA k)
  have hθ0 : 0 ≤ K₀ * γ := by positivity
  have hθ1 : K₀ * γ ≤ 1 := by
    calc K₀ * γ ≤ K₀ * (1 / K₀) := mul_le_mul_of_nonneg_left hγK (by linarith)
      _ = 1 := by field_simp
  have h := norm_sq_sub_smoothedInterp_le hM hc hq hΩ hint (hA'0 k) hInv (hB k) hp hR hRx hhR hγ
    (by linarith) hσ1 hθ0 hθ1 hgeom hu hs
  have hxk : x k ≤ S := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  have he : B k * (2 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A' k) * (γ + K₀ * γ) /
      q ^ k = x k * γ := by simp only [x]; ring
  rw [he] at h
  have hq1 : 4 ^ n * (x k * γ) ^ 2 * covConst n c q ≤ 1 / 4 := by
    have h1 : 4 ^ n * (x k * γ) ^ 2 * covConst n c q ≤ Kc * (x k * γ₀) ^ 2 := by
      have hcov : 0 ≤ covConst n c q := by unfold covConst; positivity
      calc 4 ^ n * (x k * γ) ^ 2 * covConst n c q = (4 ^ n * covConst n c q) * (x k * γ) ^ 2 := by
            ring
        _ ≤ Kc * (x k * γ₀) ^ 2 := mul_le_mul (le_max_right _ _)
            (pow_le_pow_left₀ (by have := hx0 k; positivity)
              (mul_le_mul_of_nonneg_left hγγ₀ (hx0 k)) 2) (sq_nonneg _) (by linarith)
    exact h1.trans (FEM.sq_le_quarter hS hKc (hx0 k) hxk)
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 4 ^ n * (x k * γ) ^ 2 * (covConst n c q * ‖(whitneyElement n).glue M k u‖ ^ 2)
      = (4 ^ n * (x k * γ) ^ 2 * covConst n c q) * ‖(whitneyElement n).glue M k u‖ ^ 2 := by ring
    _ ≤ 1 / 4 * ‖(whitneyElement n).glue M k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq1 (sq_nonneg _)
    _ = (1 / 2 * ‖(whitneyElement n).glue M k u‖) ^ 2 := by ring

theorem meshSize_le_two_mul {M : SimplicialMesh n} {R : ℝ} (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) : M.meshSize ≤ 2 * R := by
  refine M.meshSize_le (by positivity) fun T hT => ?_
  have hsub : T.closedInterior ⊆ Metric.closedBall x₀ R := fun y hy => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hRx y (M.closedInterior_subset_closure hT hy)
  exact (Metric.diam_mono hsub Metric.isBounded_closedBall).trans (Metric.diam_closedBall hR.le)

theorem interior_subset_domain {M : SimplicialMesh n} {s₀ : ℝ} (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain := fun _T hT =>
  (interior_mono (M.closedInterior_subset_closure hT)).trans (hstar.interior_closure_subset hs₀)

theorem isBounded_domain_of {M : SimplicialMesh n} {R : ℝ}
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) : Bornology.IsBounded M.domain :=
  (Metric.isBounded_closedBall (x := x₀) (r := R)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hRx y (subset_closure hy)

/-- The bump-radius ratio `σ = min 1 (s₀ / (16 R))`. -/
def sigmaOf (s₀ R : ℝ) : ℝ := min 1 (s₀ / (16 * R))

theorem sigmaOf_pos {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) : 0 < sigmaOf s₀ R :=
  lt_min one_pos (by positivity)

theorem sigmaOf_le_one (s₀ R : ℝ) : sigmaOf s₀ R ≤ 1 := min_le_left _ _

theorem sigmaOf_le (s₀ R : ℝ) : sigmaOf s₀ R ≤ s₀ / (16 * R) := min_le_right _ _

theorem sigmaOf_lt {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) : sigmaOf s₀ R < s₀ / (4 * R) :=
  (sigmaOf_le s₀ R).trans_lt (div_lt_div_of_pos_left hs₀ (by positivity) (by linarith))

/-- **Uniformly bounded smoothed cochain projections onto the Whitney complexes of
quasi-uniform shape-regular meshes of a domain star-shaped with respect to a ball**
([AFW2010], §5.4; [ChristiansenWinther2008]): there is `K`, depending only on `n`, the
shape-regularity and quasi-uniformity constants and the ratio `s₀ / R`, such that every such
mesh `M` of `Ω` (star-shaped with respect to `B(x₀, s₀)`, `cl Ω ⊆ B̄(x₀, R)`) carries a cochain
projection onto its Whitney complex `Vₕ ⊆ HΛ(Ω)` bounded by `K` in `L²` and in every graph norm. -/
theorem exists_uniform_cochainProjection [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hq : 0 < q) {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩo : IsOpen M.domain),
      StarBall M.domain x₀ s₀ → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) →
      ∃ π : ((whitneyElement n).subcomplex M hΩo).CochainProjection,
        (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨γ, θ, hγ, hγ4, hθ0, hθ1, hθ, hclose⟩ := exists_gamma n (x₀ := x₀) hC hc hq
  set σ := sigmaOf s₀ R
  obtain ⟨K', hK'0, hbound⟩ := exists_norm_smoothedInterp_le (x₀ := x₀) (R := R) hc hq hγ
    (by linarith) (sigmaOf_pos hs₀ hR) (sigmaOf_le_one s₀ R)
  refine ⟨max 1 (2 * K'), le_max_left _ _, fun M hM hΩo hstar hRx => ?_⟩
  set h := M.meshSize
  have hh := hM.meshSize_pos
  have hhR := meshSize_le_two_mul hR hRx
  have hγh2 : γ * h / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hR]; nlinarith
  have hpos : 0 < γ * h * σ := by have := sigmaOf_pos hs₀ hR; positivity
  have hnn : 0 ≤ γ * h / R := by positivity
  set p := pMax x₀ R σ γ h hpos hγh2
  have hp : p.IsMaximal x₀ s₀ := pMax_isMaximal hR hpos hγh2 (by positivity) (sigmaOf_lt hs₀ hR)
  have hpA : IsAdm x₀ R σ γ h p := pMax_isAdm hpos hγh2 hnn
  have hint := interior_subset_domain hstar hs₀
  set Q := (whitneyElement n).smoothedCommutingMap M p hΩo hstar hp
  have hQ : ∀ i, Q.Q i = (whitneyElement n).smoothedInterp M p hΩo.measurableSet i := fun i => rfl
  have hQb : ∀ i x, ‖Q.Q i x‖ ≤ K' * ‖x‖ := by
    intro i x
    rw [hQ]
    rcases i with k | k
    · exact hbound M hM hΩo.measurableSet hR hRx (by linarith) p hpA k x
    · have h0 : ∀ y : L2F ℝ M.domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
        have := LocalElement.subsingleton_L2F_negSucc M.domain (n := n) k
        rw [Subsingleton.elim y 0, norm_zero]
      exact (h0 _).le.trans (by positivity)
  have hQc : ∀ i, ∀ v ∈ ((whitneyElement n).subcomplex M hΩo).V i,
      ‖v - Q.Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro i v hv
    rw [hQ]
    rcases i with k | k
    · obtain ⟨u, rfl⟩ := hv
      exact hclose M hM hΩo.measurableSet hint hR hRx hhR (sigmaOf_le_one s₀ R) p hpA k
        (geomOK_of_isMaximal hM hq hC hstar hs₀ hp hpA hR hRx (sigmaOf_le_one s₀ R) hγ hθ k)
        u.1 u.2 (sampleOK_of_isMaximal hstar hp u.1)
    · have h0 : ∀ y : L2F ℝ M.domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
        have := LocalElement.subsingleton_L2F_negSucc M.domain (n := n) k
        rw [Subsingleton.elim y 0, norm_zero]
      exact (h0 _).le.trans (by positivity)
  refine ⟨Q.toCochainProjection (θ := 1 / 2) (by norm_num) hQc, fun i x => ?_, fun i j => ?_⟩
  · have h1 := Q.norm_toCochainProjection_le (θ := 1 / 2) (by norm_num) hQc (hQb i) x
    have e : (1 - 1 / 2 : ℝ)⁻¹ * K' = 2 * K' := by norm_num
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · have h1 := Q.isGraphBounded_toCochainProjection_of_norm_le (θ := 1 / 2) (by norm_num) hQc
      (hQb i) (hQb j)
    have e : (1 - 1 / 2 : ℝ)⁻¹ * K' = 2 * K' := by norm_num
    rw [e] at h1
    exact h1.mono' (by positivity) (le_max_right _ _)

/-- **Uniformly bounded smoothed cochain projections onto the Whitney complexes with vanishing
boundary DOFs** `V̊ₕ ⊆ H̊Λ(Ω)` of quasi-uniform shape-regular meshes of a domain star-shaped
with respect to a ball. The samples of the minimal-family smoother outside `Ω` only meet faces
lying in boundary facets (`StarGeom.exists_isBoundaryFacet_of_near`, from the pseudo-manifold
property `StarGeom.exists_isBoundaryFacet_of_mem_frontier`). -/
theorem exists_uniform_cochainProjectionMin [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hq : 0 < q) {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩo : IsOpen M.domain),
      ∀ (hstar : StarBall M.domain x₀ s₀), (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) →
      ∃ π : ((whitneyElement n).subcomplexMin M hΩo x₀
          (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)).CochainProjection,
        (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨γ, θ, hγ, hγ4, hθ0, hθ1, hθ, hclose⟩ := exists_gamma n (x₀ := x₀) hC hc hq
  set σ := sigmaOf s₀ R
  obtain ⟨K', hK'0, hbound⟩ := exists_norm_smoothedInterp_le (x₀ := x₀) (R := R) hc hq hγ
    (by linarith) (sigmaOf_pos hs₀ hR) (sigmaOf_le_one s₀ R)
  refine ⟨max 1 (2 * K'), le_max_left _ _, fun M hM hΩo hstar hRx => ?_⟩
  set h := M.meshSize
  have hh := hM.meshSize_pos
  have hhR := meshSize_le_two_mul hR hRx
  have hγh1 : γ * h / R ≤ 1 := by
    rw [div_le_iff₀ hR]; nlinarith
  have hpos : 0 < γ * h * σ := by have := sigmaOf_pos hs₀ hR; positivity
  have hnn : 0 ≤ γ * h / R := by positivity
  set p := pMin x₀ R σ γ h hpos hnn
  have hp : p.IsMinimal x₀ s₀ := pMin_isMinimal hR hpos hnn (by positivity) (sigmaOf_lt hs₀ hR)
  have hpA : IsAdm x₀ R σ γ h p := pMin_isAdm hpos hnn
  have hint := interior_subset_domain hstar hs₀
  have hb := isBounded_domain_of hRx
  set Q := (whitneyElement n).smoothedCommutingMapMin M p hΩo hb hstar hp x₀
    (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)
  have hQ : ∀ i, Q.Q i = (whitneyElement n).smoothedInterp M p hΩo.measurableSet i := fun i => rfl
  have hQb : ∀ i x, ‖Q.Q i x‖ ≤ K' * ‖x‖ := by
    intro i x
    rw [hQ]
    rcases i with k | k
    · exact hbound M hM hΩo.measurableSet hR hRx hγh1 p hpA k x
    · have h0 : ∀ y : L2F ℝ M.domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
        have := LocalElement.subsingleton_L2F_negSucc M.domain (n := n) k
        rw [Subsingleton.elim y 0, norm_zero]
      exact (h0 _).le.trans (by positivity)
  have hQc : ∀ i, ∀ v ∈ ((whitneyElement n).subcomplexMin M hΩo x₀
      (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)).V i,
      ‖v - Q.Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro i v hv
    rw [hQ]
    rcases i with k | k
    · obtain ⟨u, rfl⟩ := hv
      exact hclose M hM hΩo.measurableSet hint hR hRx hhR (sigmaOf_le_one s₀ R) p hpA k
        (geomOK_of_isMinimal hM hq hC hstar hs₀ hint hp hpA hR hRx (sigmaOf_le_one s₀ R)
          (sigmaOf_le s₀ R) hγ hγh1 hθ k)
        u.1 ((whitneyElement n).globalSpace₀_le M k u.2)
        (sampleOK_of_isMinimal hM hq hC hstar hs₀ hpA hR hRx (sigmaOf_le_one s₀ R) hγ hθ u.2)
    · have h0 : ∀ y : L2F ℝ M.domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
        have := LocalElement.subsingleton_L2F_negSucc M.domain (n := n) k
        rw [Subsingleton.elim y 0, norm_zero]
      exact (h0 _).le.trans (by positivity)
  refine ⟨Q.toCochainProjection (θ := 1 / 2) (by norm_num) hQc, fun i x => ?_, fun i j => ?_⟩
  · have h1 := Q.norm_toCochainProjection_le (θ := 1 / 2) (by norm_num) hQc (hQb i) x
    have e : (1 - 1 / 2 : ℝ)⁻¹ * K' = 2 * K' := by norm_num
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · have h1 := Q.isGraphBounded_toCochainProjection_of_norm_le (θ := 1 / 2) (by norm_num) hQc
      (hQb i) (hQb j)
    have e : (1 - 1 / 2 : ℝ)⁻¹ * K' = 2 * K' := by norm_num
    rw [e] at h1
    exact h1.mono' (by positivity) (le_max_right _ _)

end Estimates

/-! ## The finite element method on a domain star-shaped with respect to a ball -/

/-- **A bounded open domain `Ω ⊆ ℝⁿ` star-shaped with respect to the ball `B(x₀, s₀)`**, with
`cl Ω ⊆ B̄(x₀, R)`. -/
structure StarDomain (n : ℕ) where
  /-- the domain -/
  Ω : Set (Fin n → ℝ)
  isOpen : IsOpen Ω
  /-- the centre of the ball of star-shapedness -/
  x₀ : Fin n → ℝ
  /-- the radius of the ball of star-shapedness -/
  s₀ : ℝ
  /-- a bound of `‖x - x₀‖` on `cl Ω` -/
  R : ℝ
  s₀_pos : 0 < s₀
  R_pos : 0 < R
  starBall : StarBall Ω x₀ s₀
  norm_sub_le : ∀ y ∈ closure Ω, ‖y - x₀‖ ≤ R

namespace StarDomain

variable (D : StarDomain n)

theorem isBounded : Bornology.IsBounded D.Ω :=
  (Metric.isBounded_closedBall (x := D.x₀) (r := D.R)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact D.norm_sub_le y (subset_closure hy)

theorem strict : ∀ x ∈ closure D.Ω, ∀ t : ℝ, 0 ≤ t → t < 1 → D.x₀ + t • (x - D.x₀) ∈ D.Ω :=
  fun _ hx _ ht0 ht1 => D.starBall.strict D.s₀_pos hx ht0 ht1

/-- `HΛ(Ω)`, the maximal `L²` de Rham complex. -/
abbrev complex : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ D.Ω (formIdx n k) :=
  (deRham ℝ n).maximalComplex D.isOpen

/-- `H̊Λ(Ω)`, the minimal `L²` de Rham complex. -/
abbrev complexMin : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ D.Ω (formIdx n k) :=
  (deRham ℝ n).minimalComplex D.isOpen

end StarDomain

/-- **A family of conforming simplicial meshes of `Ω`**, uniformly shape regular (constants
`C, c`) and quasi-uniform (`q h ≤ h_T`), with mesh sizes tending to `0`. -/
structure MeshFamily (D : StarDomain n) where
  /-- the meshes -/
  mesh : ℕ → SimplicialMesh n
  /-- the shape-regularity constant `‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T` -/
  C : ℝ
  /-- the volume constant `c h_Tⁿ ≤ |det B_T|` -/
  c : ℝ
  /-- the quasi-uniformity constant -/
  q : ℝ
  C_nonneg : 0 ≤ C
  c_pos : 0 < c
  q_pos : 0 < q
  domain_eq : ∀ N, (mesh N).domain = D.Ω
  data : ∀ N, MeshData (mesh N) C c q
  tendsto_meshSize : Tendsto (fun N => (mesh N).meshSize) atTop (𝓝 0)

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D)

theorem isOpen_domain (N : ℕ) : IsOpen (F.mesh N).domain := (F.domain_eq N) ▸ D.isOpen

theorem starBall_mesh (N : ℕ) : StarBall (F.mesh N).domain D.x₀ D.s₀ :=
  (F.domain_eq N) ▸ D.starBall

theorem norm_sub_le_mesh (N : ℕ) : ∀ y ∈ closure (F.mesh N).domain, ‖y - D.x₀‖ ≤ D.R :=
  (F.domain_eq N) ▸ D.norm_sub_le

theorem strict_mesh (N : ℕ) : ∀ x ∈ closure (F.mesh N).domain, ∀ t : ℝ, 0 ≤ t → t < 1 →
    D.x₀ + t • (x - D.x₀) ∈ (F.mesh N).domain :=
  fun _ hx _ ht0 ht1 => (F.starBall_mesh N).strict D.s₀_pos hx ht0 ht1

variable [NeZero n]

/-- **The Whitney complex of `M_N`** as a subcomplex of `HΛ(Ω)`. -/
def whitney (N : ℕ) : D.complex.Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (F.domain_eq N) (F.isOpen_domain N) D.isOpen
    (whitneySubcomplex (F.mesh N) (F.isOpen_domain N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((F.whitney N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

/-- **The Whitney complex of `M_N` with vanishing boundary DOFs** as a subcomplex of `H̊Λ(Ω)`. -/
def whitneyMin (N : ℕ) : D.complexMin.Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (F.domain_eq N) (F.isOpen_domain N) D.isOpen
    (whitneySubcomplexMin (F.mesh N) (F.isOpen_domain N) D.x₀ (F.strict_mesh N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((F.whitneyMin N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

/-- **Uniformly bounded smoothed cochain projections onto the Whitney complexes of the family**
in `L²` and in every graph norm of `HΛ(Ω)` ([AFW2010], §5.4; [ChristiansenWinther2008]), with no
hypothesis beyond shape regularity and quasi-uniformity. -/
theorem exists_uniform_proj : ∃ K : ℝ, 1 ≤ K ∧ ∀ N, ∃ π : (F.whitney N).CochainProjection,
    (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨K, hK1, hK⟩ := exists_uniform_cochainProjection (x₀ := D.x₀) F.C_nonneg F.c_pos
    F.q_pos D.s₀_pos D.R_pos
  refine ⟨K, hK1, fun N => ?_⟩
  obtain ⟨π, h1, h2⟩ := hK (F.mesh N) (F.data N) (F.isOpen_domain N) (F.starBall_mesh N)
    (F.norm_sub_le_mesh N)
  exact (deRham ℝ n).maximalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (whitneySubcomplex (F.mesh N) (F.isOpen_domain N))
    (fun Θ hΘ S => ∃ π : S.CochainProjection, (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧
      ∀ i j, π.IsGraphBounded i j K) ⟨π, h1, h2⟩

/-- **Uniformly bounded smoothed cochain projections onto the Whitney complexes with vanishing
boundary DOFs** in `L²` and in every graph norm of `H̊Λ(Ω)`. -/
theorem exists_uniform_projMin : ∃ K : ℝ, 1 ≤ K ∧ ∀ N, ∃ π : (F.whitneyMin N).CochainProjection,
    (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨K, hK1, hK⟩ := exists_uniform_cochainProjectionMin (x₀ := D.x₀) F.C_nonneg F.c_pos
    F.q_pos D.s₀_pos D.R_pos
  refine ⟨K, hK1, fun N => ?_⟩
  obtain ⟨π, h1, h2⟩ := hK (F.mesh N) (F.data N) (F.isOpen_domain N) (F.starBall_mesh N)
    (F.norm_sub_le_mesh N)
  exact (deRham ℝ n).minimalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (whitneySubcomplexMin (F.mesh N) (F.isOpen_domain N) D.x₀ (F.strict_mesh N))
    (fun Θ hΘ S => ∃ π : S.CochainProjection, (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧
      ∀ i j, π.IsGraphBounded i j K) ⟨π, h1, h2⟩

/-! ### Interpolation of smooth forms and density of the Whitney complexes -/

/-- The constant of the `L²` interpolation estimate of degree `k`:
`#Λᵏ |Ω|^{1/2} C_{n,k} Cᵏ`. -/
def interpConst (k : ℕ) : ℝ :=
  Fintype.card (formIdx n k) * (volume.real D.Ω ^ (1 / 2 : ℝ) * (whitneyConst n k * F.C ^ k))

omit [NeZero n] in
theorem interpConst_nonneg (k : ℕ) : 0 ≤ F.interpConst k := by
  unfold interpConst; have := whitneyConst_nonneg n k; have := F.C_nonneg; positivity

omit [NeZero n] in
theorem meshSize_pos (N : ℕ) : 0 < (F.mesh N).meshSize := (F.data N).meshSize_pos

omit [NeZero n] in
theorem diam_le (N : ℕ) : ∀ T ∈ (F.mesh N).simplices, diam T ≤ (F.mesh N).meshSize :=
  fun _ hT => (F.mesh N).diam_le_meshSize hT

/-- **Interpolation error on the meshes of the family** ([Arnold2018], Ch. 7, classical form):
for a `C²` form `w` with `‖Dw‖ ≤ L` and `‖D(dw)‖ ≤ L'` on `cl Ω`, the canonical interpolant
`v = Π_N w ∈ Vₕᵏ` satisfies `‖w - v‖ ≤ A_k h_N L` and `‖dw - dv‖ ≤ A_{k+1} h_N L'`. -/
theorem exists_mem_whitney_le (N k : ℕ) {w : FormField n} (hw : ContDiff ℝ 2 w)
    {L L' : ℝ} (hL0 : 0 ≤ L) (hL'0 : 0 ≤ L')
    (hL : ∀ y ∈ closure D.Ω, ‖fderiv ℝ w y‖ ≤ L)
    (hL' : ∀ y ∈ closure D.Ω, ‖fderiv ℝ (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (F.whitney N).V k,
      ‖formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ - v‖ ≤
        F.interpConst k * ((F.mesh N).meshSize * L) ∧
      ∃ hv : v ∈ (D.complex.d k (k + 1)).domain,
        ‖formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by norm_num))⟩ -
          D.complex.d k (k + 1) ⟨v, hv⟩‖ ≤
          F.interpConst (k + 1) * ((F.mesh N).meshSize * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hdw : ContDiff ℝ 1 (extDeriv w) := contDiff_extDeriv (m := 1) hw
  refine (deRham ℝ n).maximalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (whitneySubcomplex (F.mesh N) (F.isOpen_domain N))
    (fun Θ hΘ S => ∀ hb : Bornology.IsBounded Θ, ∀ hvol : volume.real Θ = volume.real D.Ω,
      ∃ v ∈ S.V k,
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - FEM.asForm n v‖ ≤
          F.interpConst k * ((F.mesh N).meshSize * L) ∧
        ∃ hv : v ∈ (((deRham ℝ n).maximalComplex hΘ).d k (k + 1)).domain,
          ‖formL2 hΘ.measurableSet hb ((k : ℤ) + 1)
              ⟨extDeriv w, continuous_extDeriv (hw.of_le (by norm_num))⟩ -
            FEM.asForm n (((deRham ℝ n).maximalComplex hΘ).d k (k + 1) ⟨v, hv⟩)‖ ≤
            F.interpConst (k + 1) * ((F.mesh N).meshSize * L')) ?_ D.isBounded rfl
  intro hb hvol
  set M := F.mesh N
  have hΩo := F.isOpen_domain N
  have hcl : closure M.domain = closure D.Ω := by rw [F.domain_eq N]
  set u := (whitneyElement n).globalInterp M k (Submodule.inclusion c1Forms_le_contForms
    (⟨w, hw1⟩ : c1Forms n))
  obtain ⟨hmem, hval⟩ := glue_globalInterp_mem_maximal M hΩo k ⟨w, hw1⟩
  refine ⟨(whitneyElement n).glue M k (u : (whitneyElement n).Piecewise M k), ⟨u, rfl⟩, ?_, ?_⟩
  · have h := norm_formL2_sub_glue_le_of_isShapeRegular M hΩo.measurableSet k hw1 F.C_nonneg
      (F.meshSize_pos N).le hL0 (fun y hy => hL y (hcl ▸ hy)) (F.data N).shape (F.diam_le N)
    refine h.trans (le_of_eq ?_)
    rw [hvol, interpConst]; ring
  · refine ⟨by rw [deRham_maximalComplex_d]; exact hmem, ?_⟩
    rw [LinearPMap.apply_eq_of_eq' (deRham_maximalComplex_d hΩo (k : ℤ))]
    have h := norm_formL2_sub_glue_le_of_isShapeRegular M hΩo.measurableSet (k + 1) hdw
      F.C_nonneg (F.meshSize_pos N).le hL'0 (fun y hy => hL' y (hcl ▸ hy)) (F.data N).shape
      (F.diam_le N)
    have e : (extDerivOp ℝ n k).maximal M.domain
        ⟨(whitneyElement n).glue M k (u : (whitneyElement n).Piecewise M k), hmem⟩ =
        (whitneyElement n).glue M ((k + 1 : ℕ) : ℤ) ((whitneyElement n).globalInterp M (k + 1)
          ⟨extDeriv w, hdw.continuous⟩ : (whitneyElement n).Piecewise M (k + 1)) := hval
    erw [e]
    refine h.trans (le_of_eq ?_)
    rw [hvol, interpConst]; push_cast; ring

/-- **Interpolation error with vanishing boundary DOFs**: for a `C²` form `w` vanishing outside
`Ω`, the canonical interpolant lies in `V̊ₕᵏ ⊆ H̊Λᵏ(Ω)`, with the estimates of
`exists_mem_whitney_le`. -/
theorem exists_mem_whitneyMin_le (N k : ℕ) {w : FormField n} (hw : ContDiff ℝ 2 w)
    (hsupp : ∀ x ∉ D.Ω, w x = 0) {L L' : ℝ} (hL0 : 0 ≤ L) (hL'0 : 0 ≤ L')
    (hL : ∀ y ∈ closure D.Ω, ‖fderiv ℝ w y‖ ≤ L)
    (hL' : ∀ y ∈ closure D.Ω, ‖fderiv ℝ (extDeriv w) y‖ ≤ L') :
    ∃ v ∈ (F.whitneyMin N).V k,
      ‖formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ - v‖ ≤
        F.interpConst k * ((F.mesh N).meshSize * L) ∧
      ∃ hv : v ∈ (D.complexMin.d k (k + 1)).domain,
        ‖formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by norm_num))⟩ -
          D.complexMin.d k (k + 1) ⟨v, hv⟩‖ ≤
          F.interpConst (k + 1) * ((F.mesh N).meshSize * L') := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hdw : ContDiff ℝ 1 (extDeriv w) := contDiff_extDeriv (m := 1) hw
  refine (deRham ℝ n).minimalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (whitneySubcomplexMin (F.mesh N) (F.isOpen_domain N) D.x₀ (F.strict_mesh N))
    (fun Θ hΘ S => ∀ hb : Bornology.IsBounded Θ, ∀ hvol : volume.real Θ = volume.real D.Ω,
      ∃ v ∈ S.V k,
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - FEM.asForm n v‖ ≤
          F.interpConst k * ((F.mesh N).meshSize * L) ∧
        ∃ hv : v ∈ (((deRham ℝ n).minimalComplex hΘ).d k (k + 1)).domain,
          ‖formL2 hΘ.measurableSet hb ((k : ℤ) + 1)
              ⟨extDeriv w, continuous_extDeriv (hw.of_le (by norm_num))⟩ -
            FEM.asForm n (((deRham ℝ n).minimalComplex hΘ).d k (k + 1) ⟨v, hv⟩)‖ ≤
            F.interpConst (k + 1) * ((F.mesh N).meshSize * L')) ?_ D.isBounded rfl
  intro hb hvol
  set M := F.mesh N
  have hΩo := F.isOpen_domain N
  have hcl : closure M.domain = closure D.Ω := by rw [F.domain_eq N]
  set w' : c1Forms n := ⟨w, hw1⟩
  set u := (whitneyElement n).globalInterp M k (Submodule.inclusion c1Forms_le_contForms w')
  have hu₀ : (u : (whitneyElement n).Piecewise M k) ∈ (whitneyElement n).globalSpace₀ M k :=
    LocalElement.globalInterp_mem_globalSpace₀ _ M k fun x hx => hsupp x (by
      rw [← F.domain_eq N]; exact M.notMem_domain_of_mem_frontier hΩo hx)
  obtain ⟨hmem, hval⟩ := (whitneyElement n).glue_mem_minimal M hΩo D.x₀ (F.strict_mesh N) k
    ⟨_, hu₀⟩
  refine ⟨(whitneyElement n).glue M k (u : (whitneyElement n).Piecewise M k),
    ⟨⟨_, hu₀⟩, rfl⟩, ?_, ?_⟩
  · have h := norm_formL2_sub_glue_le_of_isShapeRegular M hΩo.measurableSet k hw1 F.C_nonneg
      (F.meshSize_pos N).le hL0 (fun y hy => hL y (hcl ▸ hy)) (F.data N).shape (F.diam_le N)
    refine h.trans (le_of_eq ?_)
    rw [hvol, interpConst]; ring
  · refine ⟨by rw [deRham_minimalComplex_d]; exact hmem, ?_⟩
    rw [LinearPMap.apply_eq_of_eq' (deRham_minimalComplex_d hΩo (k : ℤ))]
    have h := norm_formL2_sub_glue_le_of_isShapeRegular M hΩo.measurableSet (k + 1) hdw
      F.C_nonneg (F.meshSize_pos N).le hL'0 (fun y hy => hL' y (hcl ▸ hy)) (F.data N).shape
      (F.diam_le N)
    have h1 : (whitneyElement n).dPiecewise M k (u : (whitneyElement n).Piecewise M k) =
        ((whitneyElement n).dGlobal M k u : (whitneyElement n).Piecewise M (k + 1)) := rfl
    have e : (extDerivOp ℝ n k).minimal M.domain
        ⟨(whitneyElement n).glue M k (u : (whitneyElement n).Piecewise M k), hmem⟩ =
        (whitneyElement n).glue M ((k + 1 : ℕ) : ℤ) ((whitneyElement n).globalInterp M (k + 1)
          ⟨extDeriv w, hdw.continuous⟩ : (whitneyElement n).Piecewise M (k + 1)) := by
      rw [hval]
      change (whitneyElement n).glue M ((k : ℤ) + 1)
        ((whitneyElement n).dPiecewise M k (u : (whitneyElement n).Piecewise M k)) = _
      rw [h1, ← LocalElement.globalInterp_extDeriv]
      rfl
    erw [e]
    refine h.trans (le_of_eq ?_)
    rw [hvol, interpConst]; push_cast; ring

end MeshFamily

namespace StarDomain

variable (D : StarDomain n)

theorem isCompact_closure : IsCompact (closure D.Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure D.isBounded.closure

/-- A `C¹` form has a bounded derivative on the compact `cl Ω`. -/
theorem exists_bound_fderiv {w : FormField n} (hw : ContDiff ℝ 1 w) :
    ∃ L, 0 ≤ L ∧ ∀ y ∈ closure D.Ω, ‖fderiv ℝ w y‖ ≤ L := by
  obtain ⟨L, hL⟩ := D.isCompact_closure.exists_bound_of_continuousOn
    (hw.continuous_fderiv one_ne_zero).continuousOn
  exact ⟨max L 0, le_max_right _ _, fun y hy => (hL y hy).trans (le_max_left _ _)⟩

/-- **Smooth forms are dense in `HΛᵏ(Ω)`** ([AFW2010], §5.4: the smoother with dilation factor
`c → 1` and bump radius `→ 0`). -/
theorem exists_smooth_near (k : ℕ) (u : (D.complex.d k (k + 1)).domain) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ w : FormField n, ∃ hw : ContDiff ℝ ∞ w, (∀ x, IsDeg k (w x)) ∧
      ‖(u : L2F ℝ D.Ω (formIdx n k)) -
          formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩‖ < ε ∧
      ‖D.complex.d k (k + 1) u -
          formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩‖ < ε := by
  set Ω := D.Ω
  have hΩ := D.isOpen
  have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) hΩ (k : ℤ)
  set u' : ((extDerivOp ℝ n k).maximal Ω).domain := ⟨u, hd ▸ u.2⟩
  have hu' : D.complex.d k (k + 1) u = (extDerivOp ℝ n k).maximal Ω u' :=
    LinearPMap.apply_eq_of_eq' hd u
  obtain ⟨η₁, hη₁, hP₁⟩ := exists_norm_smoothField_sub_lt hΩ.measurableSet D.x₀
    (u : L2F ℝ Ω (formIdx n k)) hε
  obtain ⟨η₂, hη₂, hP₂⟩ := exists_norm_smoothField_sub_lt hΩ.measurableSet D.x₀
    ((extDerivOp ℝ n k).maximal Ω u') hε
  obtain ⟨δ₁, hδ₁, hc₁⟩ := FEM.exists_abs_pow_sub_one_lt k hη₁
  obtain ⟨δ₂, hδ₂, hc₂⟩ := FEM.exists_abs_pow_sub_one_lt (k + 1) hη₂
  obtain ⟨p, hp, hc, hr⟩ := SmoothingParam.exists_isMaximal D.x₀ D.s₀_pos
    (η := min (min η₁ η₂) (min δ₁ δ₂)) (by positivity)
  have hcη₁ : |p.factor - 1| < η₁ := hc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hcη₂ : |p.factor - 1| < η₂ := hc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hcδ₁ : |p.factor - 1| < δ₁ := hc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcδ₂ : |p.factor - 1| < δ₂ := hc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrη₁ : p.bump.rOut < η₁ := hr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hrη₂ : p.bump.rOut < η₂ := hr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  set w : FormField n := (smoothForm p hΩ.measurableSet k (u : L2F ℝ Ω (formIdx n k)) :
    FormField n)
  have hw : ContDiff ℝ ∞ w := FEM.contDiff_smoothForm p hΩ.measurableSet k _
  refine ⟨w, hw, isDeg_smoothForm p hΩ.measurableSet k _, ?_, ?_⟩
  · have e := FEM.formL2_smoothForm hΩ.measurableSet D.isBounded p (k : ℤ)
      (u : L2F ℝ Ω (formIdx n k))
    change ‖(u : L2F ℝ Ω (formIdx n k)) - formL2 hΩ.measurableSet D.isBounded k
      (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ.measurableSet k
        (u : L2F ℝ Ω (formIdx n k))))‖ < ε
    rw [e, norm_sub_rev]
    refine hP₁ p hp.center_eq hcη₁ hrη₁ _ ?_
    rw [zpow_natCast]; exact hc₁ _ hcδ₁
  · have e1 : formL2 hΩ.measurableSet D.isBounded ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ =
        formL2 hΩ.measurableSet D.isBounded ((k : ℤ) + 1)
          (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ.measurableSet ((k : ℤ) + 1)
            ((extDerivOp ℝ n k).maximal Ω u'))) :=
      formL2_congr _ _ _ fun x hx =>
        extDeriv_smoothForm_of_maximal p hΩ.measurableSet hΩ D.starBall hp k u'
          (subset_closure hx)
    rw [e1, FEM.formL2_smoothForm, hu', norm_sub_rev]
    refine hP₂ p hp.center_eq hcη₂ hrη₂ _ ?_
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact hc₂ _ hcδ₂

/-- **Smooth forms with compact support in `Ω` are dense in `H̊Λᵏ(Ω)`** (the smoother with
dilation towards the centre, `c > 1`). -/
theorem exists_smooth_near_min (k : ℕ) (u : (D.complexMin.d k (k + 1)).domain) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ w : FormField n, ∃ hw : ContDiff ℝ ∞ w, (∀ x ∉ D.Ω, w x = 0) ∧
      ‖(u : L2F ℝ D.Ω (formIdx n k)) -
          formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩‖ < ε ∧
      ‖D.complexMin.d k (k + 1) u -
          formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩‖ < ε := by
  set Ω := D.Ω
  have hΩ := D.isOpen
  have hd := deRham_minimalComplex_d (𝕜 := ℝ) (n := n) hΩ (k : ℤ)
  set u' : ((extDerivOp ℝ n k).minimal Ω).domain := ⟨u, hd ▸ u.2⟩
  have hu' : D.complexMin.d k (k + 1) u = (extDerivOp ℝ n k).minimal Ω u' :=
    LinearPMap.apply_eq_of_eq' hd u
  obtain ⟨η₁, hη₁, hP₁⟩ := exists_norm_smoothField_sub_lt hΩ.measurableSet D.x₀
    (u : L2F ℝ Ω (formIdx n k)) hε
  obtain ⟨η₂, hη₂, hP₂⟩ := exists_norm_smoothField_sub_lt hΩ.measurableSet D.x₀
    ((extDerivOp ℝ n k).minimal Ω u') hε
  obtain ⟨δ₁, hδ₁, hc₁⟩ := FEM.exists_abs_pow_sub_one_lt k hη₁
  obtain ⟨δ₂, hδ₂, hc₂⟩ := FEM.exists_abs_pow_sub_one_lt (k + 1) hη₂
  obtain ⟨p, hp, hc, hr⟩ := SmoothingParam.exists_isMinimal D.x₀ D.s₀_pos
    (η := min (min η₁ η₂) (min δ₁ δ₂)) (by positivity)
  have hcη₁ : |p.factor - 1| < η₁ := hc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hcη₂ : |p.factor - 1| < η₂ := hc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hcδ₁ : |p.factor - 1| < δ₁ := hc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcδ₂ : |p.factor - 1| < δ₂ := hc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrη₁ : p.bump.rOut < η₁ := hr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hrη₂ : p.bump.rOut < η₂ := hr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  set w : FormField n := (smoothForm p hΩ.measurableSet k (u : L2F ℝ Ω (formIdx n k)) :
    FormField n)
  have hw : ContDiff ℝ ∞ w := FEM.contDiff_smoothForm p hΩ.measurableSet k _
  refine ⟨w, hw, fun x hx => smoothForm_eq_zero_of_minimal p hΩ D.isBounded
    D.starBall hp k _ hx, ?_, ?_⟩
  · have e := FEM.formL2_smoothForm hΩ.measurableSet D.isBounded p (k : ℤ)
      (u : L2F ℝ Ω (formIdx n k))
    change ‖(u : L2F ℝ Ω (formIdx n k)) - formL2 hΩ.measurableSet D.isBounded k
      (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ.measurableSet k
        (u : L2F ℝ Ω (formIdx n k))))‖ < ε
    rw [e, norm_sub_rev]
    refine hP₁ p hp.center_eq hcη₁ hrη₁ _ ?_
    rw [zpow_natCast]; exact hc₁ _ hcδ₁
  · have e1 : formL2 hΩ.measurableSet D.isBounded ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ =
        formL2 hΩ.measurableSet D.isBounded ((k : ℤ) + 1)
          (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ.measurableSet ((k : ℤ) + 1)
            ((extDerivOp ℝ n k).minimal Ω u'))) :=
      formL2_congr _ _ _ fun x _ =>
        extDeriv_smoothForm_of_minimal p hΩ.measurableSet hΩ k u' x
    rw [e1, FEM.formL2_smoothForm, hu', norm_sub_rev]
    refine hP₂ p hp.center_eq hcη₂ hrη₂ _ ?_
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact hc₂ _ hcδ₂

end StarDomain

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D) [NeZero n]

/-- **Graph-norm density of the Whitney spaces in `HΛᵏ(Ω)`**: smooth forms are dense
(`StarDomain.exists_smooth_near`) and their canonical interpolants converge at rate `h_N`
(`exists_mem_whitney_le`). -/
theorem eventually_exists_whitney_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complex.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitney N).V k, ‖x - v‖ < ε ∧
      ‖D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.whitney N).le_domain k (k + 1) hv)⟩‖ < ε := by
  rcases k with k | k
  swap
  · have := LocalElement.subsingleton_L2F_negSucc D.Ω (n := n) k
    refine Eventually.of_forall fun N => ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε
  change ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitney N).V (k : ℤ), ‖x - v‖ < ε ∧
      ‖D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.whitney N).le_domain k (k + 1) hv)⟩‖ < ε
  obtain ⟨w, hw, -, h1, h2⟩ := D.exists_smooth_near k ⟨x, hx⟩ (half_pos hε)
  have hw2 : ContDiff ℝ 2 w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_fderiv (hw.of_le (by exact_mod_cast le_top))
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_fderiv (contDiff_extDeriv (m := 1) hw2)
  have ht : Tendsto (fun N => F.interpConst k * ((F.mesh N).meshSize * L) +
      F.interpConst (k + 1) * ((F.mesh N).meshSize * L')) atTop (𝓝 0) := by
    have := ((F.tendsto_meshSize.mul_const L).const_mul (F.interpConst k)).add
      ((F.tendsto_meshSize.mul_const L').const_mul (F.interpConst (k + 1)))
    simpa using this
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with N hN
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_whitney_le N k hw2 hL0 hL'0 hL hL'
  have hb1 := mul_nonneg (F.interpConst_nonneg (k + 1)) (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.interpConst_nonneg k) (mul_nonneg (F.meshSize_pos N).le hL0)
  refine ⟨v, hv, ?_, ?_⟩
  · calc ‖x - v‖ ≤ ‖x - formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩‖ +
          ‖formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ - v‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 (hv1.trans (by linarith))
      _ = ε := add_halves ε
  · have e : D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.whitney N).le_domain k (k + 1) hv)⟩ =
        D.complex.d k (k + 1) ⟨x, hx⟩ - D.complex.d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e]
    calc ‖D.complex.d k (k + 1) ⟨x, hx⟩ - D.complex.d k (k + 1) ⟨v, hdv⟩‖
        ≤ ‖D.complex.d k (k + 1) ⟨x, hx⟩ - formL2 D.isOpen.measurableSet D.isBounded
            ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv
              (hw.of_le (by exact_mod_cast le_top))⟩‖ +
          ‖formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ -
            D.complex.d k (k + 1) ⟨v, hdv⟩‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h2 (hv2.trans (by linarith))
      _ = ε := add_halves ε

/-- **`L²` density of the Whitney spaces** `Vₕᵏ` in `L²(Ω; Λᵏ)`. -/
theorem eventually_exists_whitney_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.whitney N).V k, ‖x - v‖ < ε := by
  obtain ⟨y, hy, hxy⟩ := (D.complex.dense k (k + 1)).exists_dist_lt x (half_pos hε)
  filter_upwards [F.eventually_exists_whitney_graph k y hy (half_pos hε)] with N hN
  obtain ⟨v, hv, h1, -⟩ := hN
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm] at hxy
  calc ‖x - v‖ ≤ ‖x - y‖ + ‖y - v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy h1
    _ = ε := add_halves ε

/-- **Degreewise approximation in every graph norm of `HΛ(Ω)`**. -/
theorem eventually_exists_whitney_near (i : ℤ) (x : L2F ℝ D.Ω (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitney N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (D.complex.d i j).domain),
        ‖D.complex.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.whitney N).le_domain i j hv)⟩‖ <
          ε := by
  by_cases hx : x ∈ (D.complex.d i (i + 1)).domain
  · filter_upwards [F.eventually_exists_whitney_graph i x hx hε] with N hN
    obtain ⟨v, hv, h1, h2⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact h2
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε
  · filter_upwards [F.eventually_exists_whitney_lt i x hε] with N hN
    obtain ⟨v, hv, h1⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact absurd hxj hx
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε

/-- `dist(q, Vₕʲ) → 0` for every `q ∈ L²(Ω; Λʲ)`. -/
theorem tendsto_infDist_whitney (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.whitney N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N =>
    ha.trans_le Metric.infDist_nonneg, fun a ha => ?_⟩
  filter_upwards [F.eventually_exists_whitney_lt j q ha] with N hN
  obtain ⟨v, hv, h⟩ := hN
  exact (Metric.infDist_le_dist_of_mem hv).trans_lt (by rwa [dist_eq_norm])

/-- **Graph-norm density of the Whitney spaces in `H̊Λᵏ(Ω)`**: smooth forms are dense
(`StarDomain.exists_smooth_near`) and their canonical interpolants converge at rate `h_N`
(`exists_mem_whitney_le`). -/
theorem eventually_exists_whitneyMin_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complexMin.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitneyMin N).V k, ‖x - v‖ < ε ∧
      ‖D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.whitneyMin N).le_domain k (k + 1) hv)⟩‖ < ε := by
  rcases k with k | k
  swap
  · have := LocalElement.subsingleton_L2F_negSucc D.Ω (n := n) k
    refine Eventually.of_forall fun N => ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε
  change ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitneyMin N).V (k : ℤ), ‖x - v‖ < ε ∧
      ‖D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.whitneyMin N).le_domain k (k + 1) hv)⟩‖ < ε
  obtain ⟨w, hw, hsupp, h1, h2⟩ := D.exists_smooth_near_min k ⟨x, hx⟩ (half_pos hε)
  have hw2 : ContDiff ℝ 2 w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_fderiv (hw.of_le (by exact_mod_cast le_top))
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_fderiv (contDiff_extDeriv (m := 1) hw2)
  have ht : Tendsto (fun N => F.interpConst k * ((F.mesh N).meshSize * L) +
      F.interpConst (k + 1) * ((F.mesh N).meshSize * L')) atTop (𝓝 0) := by
    have := ((F.tendsto_meshSize.mul_const L).const_mul (F.interpConst k)).add
      ((F.tendsto_meshSize.mul_const L').const_mul (F.interpConst (k + 1)))
    simpa using this
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with N hN
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_whitneyMin_le N k hw2 hsupp hL0 hL'0 hL hL'
  have hb1 := mul_nonneg (F.interpConst_nonneg (k + 1)) (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.interpConst_nonneg k) (mul_nonneg (F.meshSize_pos N).le hL0)
  refine ⟨v, hv, ?_, ?_⟩
  · calc ‖x - v‖ ≤ ‖x - formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩‖ +
          ‖formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ - v‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 (hv1.trans (by linarith))
      _ = ε := add_halves ε
  · have e : D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.whitneyMin N).le_domain k (k + 1) hv)⟩ =
        D.complexMin.d k (k + 1) ⟨x, hx⟩ - D.complexMin.d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e]
    calc ‖D.complexMin.d k (k + 1) ⟨x, hx⟩ - D.complexMin.d k (k + 1) ⟨v, hdv⟩‖
        ≤ ‖D.complexMin.d k (k + 1) ⟨x, hx⟩ - formL2 D.isOpen.measurableSet D.isBounded
            ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv
              (hw.of_le (by exact_mod_cast le_top))⟩‖ +
          ‖formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (hw.of_le (by exact_mod_cast le_top))⟩ -
            D.complexMin.d k (k + 1) ⟨v, hdv⟩‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h2 (hv2.trans (by linarith))
      _ = ε := add_halves ε

/-- **`L²` density of the Whitney spaces with vanishing boundary DOFs** `V̊ₕᵏ` in `L²(Ω; Λᵏ)`. -/
theorem eventually_exists_whitneyMin_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.whitneyMin N).V k, ‖x - v‖ < ε := by
  obtain ⟨y, hy, hxy⟩ := (D.complexMin.dense k (k + 1)).exists_dist_lt x (half_pos hε)
  filter_upwards [F.eventually_exists_whitneyMin_graph k y hy (half_pos hε)] with N hN
  obtain ⟨v, hv, h1, -⟩ := hN
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm] at hxy
  calc ‖x - v‖ ≤ ‖x - y‖ + ‖y - v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy h1
    _ = ε := add_halves ε

/-- **Degreewise approximation in every graph norm of `H̊Λ(Ω)`**. -/
theorem eventually_exists_whitneyMin_near (i : ℤ) (x : L2F ℝ D.Ω (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitneyMin N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (D.complexMin.d i j).domain),
        ‖D.complexMin.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.whitneyMin N).le_domain i j hv)⟩‖ <
          ε := by
  by_cases hx : x ∈ (D.complexMin.d i (i + 1)).domain
  · filter_upwards [F.eventually_exists_whitneyMin_graph i x hx hε] with N hN
    obtain ⟨v, hv, h1, h2⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact h2
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε
  · filter_upwards [F.eventually_exists_whitneyMin_lt i x hε] with N hN
    obtain ⟨v, hv, h1⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact absurd hxj hx
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε

/-- `dist(q, V̊ₕʲ) → 0` for every `q ∈ L²(Ω; Λʲ)`. -/
theorem tendsto_infDist_whitneyMin (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.whitneyMin N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N =>
    ha.trans_le Metric.infDist_nonneg, fun a ha => ?_⟩
  filter_upwards [F.eventually_exists_whitneyMin_lt j q ha] with N hN
  obtain ⟨v, hv, h⟩ := hN
  exact (Metric.infDist_le_dist_of_mem hv).trans_lt (by rwa [dist_eq_norm])

include F in
/-- **Smooth `k`-forms lie in `HΛᵏ(Ω)`**, with `d (w|_Ω) = (dw)|_Ω`. -/
theorem formL2_mem_domain (k : ℕ) {w : FormField n} (hw : ContDiff ℝ 1 w)
    (hdeg : ∀ x, IsDeg k (w x)) :
    ∃ h : formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ ∈
        (D.complex.d k (k + 1)).domain,
      D.complex.d k (k + 1) ⟨_, h⟩ =
        formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv hw⟩ := by
  have key : ∀ (Θ : Set (Fin n → ℝ)) (e : Θ = D.Ω) (hΘ : MeasurableSet Θ)
      (hb : Bornology.IsBounded Θ),
      (∃ h : formL2 hΘ hb k ⟨w, hw.continuous⟩ ∈ ((extDerivOp ℝ n k).maximal Θ).domain,
        (extDerivOp ℝ n k).maximal Θ ⟨_, h⟩ =
          formL2 hΘ hb ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩) →
      ∃ h : formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ ∈
          ((extDerivOp ℝ n k).maximal D.Ω).domain,
        (extDerivOp ℝ n k).maximal D.Ω ⟨_, h⟩ =
          formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv hw⟩ := by
    rintro Θ rfl _ _ h; exact h
  obtain ⟨h, hval⟩ := key _ (F.domain_eq 0) _ _
    (formL2_mem_maximal (F.mesh 0) (F.isOpen_domain 0) k hw hdeg)
  have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) D.isOpen (k : ℤ)
  exact ⟨hd ▸ h, (LinearPMap.apply_eq_of_eq' hd _).trans hval⟩

include F in
/-- **`d_min` of a smooth form**: if `x ∈ H̊Λᵏ(Ω)` is the class of a `C¹` form `w`, then
`d x = (dw)|_Ω`. -/
theorem complexMin_d_formL2 (k : ℕ) {w : FormField n} (hw : ContDiff ℝ 1 w)
    (hdeg : ∀ y, IsDeg k (w y)) (x : (D.complexMin.d k (k + 1)).domain)
    (hx : (x : L2F ℝ D.Ω (formIdx n k)) =
      formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩) :
    D.complexMin.d k (k + 1) x =
      formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
        ⟨extDeriv w, continuous_extDeriv hw⟩ := by
  have hd := deRham_minimalComplex_d (𝕜 := ℝ) (n := n) D.isOpen (k : ℤ)
  have hD := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) D.isOpen (k : ℤ)
  obtain ⟨h, hval⟩ := F.formL2_mem_domain k hw hdeg
  refine (LinearPMap.apply_eq_of_eq' hd x).trans
    (((extDerivOp_minimal_le_maximal (𝕜 := ℝ) (n := n) D.isOpen (k : ℤ)).2
      (y := ⟨_, hD ▸ h⟩) hx).trans ?_)
  rw [← hval]
  exact (LinearPMap.apply_eq_of_eq' hD ⟨_, h⟩).symm

end MeshFamily

/-! ### Smooth forms and the approximation rate -/

namespace StarDomain

variable (D : StarDomain n)

/-- `x ∈ L²(Ω; Λʲ)` is a `C²` form of degree `j` whose derivative and the derivative of its
exterior derivative are bounded by `L` on `cl Ω` (trivially true in negative degrees). -/
def IsC2Form (j : ℤ) (L : ℝ) (x : L2F ℝ D.Ω (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n, ∃ hw : ContDiff ℝ 2 w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∈ closure D.Ω, ‖fderiv ℝ w y‖ ≤ L) ∧
    (∀ y ∈ closure D.Ω, ‖fderiv ℝ (extDeriv w) y‖ ≤ L) ∧
    x = formL2 D.isOpen.measurableSet D.isBounded j ⟨w, hw.continuous⟩

/-- `IsC2Form` with, in addition, `w = 0` outside `Ω` (the regularity class of `H̊Λ(Ω)`). -/
def IsC2FormMin (j : ℤ) (L : ℝ) (x : L2F ℝ D.Ω (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n, ∃ hw : ContDiff ℝ 2 w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∉ D.Ω, w y = 0) ∧
    (∀ y ∈ closure D.Ω, ‖fderiv ℝ w y‖ ≤ L) ∧
    (∀ y ∈ closure D.Ω, ‖fderiv ℝ (extDeriv w) y‖ ≤ L) ∧
    x = formL2 D.isOpen.measurableSet D.isBounded j ⟨w, hw.continuous⟩

end StarDomain

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D)

/-- The constant `B_j = A_j + A_{j+1}` of the graph-norm interpolation error in degree `j`. -/
def interpBound (j : ℤ) : ℝ := F.interpConst j.toNat + F.interpConst (j.toNat + 1)

theorem interpBound_nonneg (j : ℤ) : 0 ≤ F.interpBound j :=
  add_nonneg (F.interpConst_nonneg _) (F.interpConst_nonneg _)

variable [NeZero n]

/-- **Degreewise interpolation error for `C²` forms**: `‖x - v‖, ‖d (x - v)‖ ≤ B_j L h_N` for the
Whitney interpolant `v ∈ Vₕʲ`. -/
theorem exists_mem_whitney_le_of_isC2Form {j : ℤ} {L : ℝ} {x : L2F ℝ D.Ω (formIdx n j)}
    (hx : D.IsC2Form j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (F.whitney N).V j, ‖x - v‖ ≤ F.interpBound j * L * (F.mesh N).meshSize ∧
      ∀ j' (hxj : x ∈ (D.complex.d j j').domain),
        ‖D.complex.d j j' ⟨x - v, Submodule.sub_mem _ hxj ((F.whitney N).le_domain j j' hv)⟩‖ ≤
          F.interpBound j * L * (F.mesh N).meshSize := by
  have hB0 := mul_nonneg (mul_nonneg (F.interpBound_nonneg j) hL0) (F.meshSize_pos N).le
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc D.Ω (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_whitney_le N k hw hL0 hL0 hL hL'
  obtain ⟨hdom, hval⟩ := F.formL2_mem_domain k (hw.of_le (by norm_num)) hdeg
  have hh := (F.meshSize_pos N).le
  have hA0 := mul_nonneg (F.interpConst_nonneg k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (F.interpConst_nonneg (k + 1)) (mul_nonneg hh hL0)
  have e : F.interpBound k * L * (F.mesh N).meshSize =
      F.interpConst k * ((F.mesh N).meshSize * L) +
        F.interpConst (k + 1) * ((F.mesh N).meshSize * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : D.complex.d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((F.whitney N).le_domain k (k + 1) hv)⟩ =
        D.complex.d k (k + 1) ⟨_, hdom⟩ - D.complex.d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', hval, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact mul_nonneg (mul_nonneg (F.interpBound_nonneg _) hL0) hh

/-- **Degreewise interpolation error for `C²` forms vanishing outside `Ω`**, in `H̊Λ(Ω)`. -/
theorem exists_mem_whitneyMin_le_of_isC2FormMin {j : ℤ} {L : ℝ} {x : L2F ℝ D.Ω (formIdx n j)}
    (hx : D.IsC2FormMin j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (F.whitneyMin N).V j,
      ‖x - v‖ ≤ F.interpBound j * L * (F.mesh N).meshSize ∧
      ∀ j' (hxj : x ∈ (D.complexMin.d j j').domain),
        ‖D.complexMin.d j j'
            ⟨x - v, Submodule.sub_mem _ hxj ((F.whitneyMin N).le_domain j j' hv)⟩‖ ≤
          F.interpBound j * L * (F.mesh N).meshSize := by
  have hB0 := mul_nonneg (mul_nonneg (F.interpBound_nonneg j) hL0) (F.meshSize_pos N).le
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hsupp, hL, hL', rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc D.Ω (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_whitneyMin_le N k hw hsupp hL0 hL0 hL hL'
  have hh := (F.meshSize_pos N).le
  have hA0 := mul_nonneg (F.interpConst_nonneg k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (F.interpConst_nonneg (k + 1)) (mul_nonneg hh hL0)
  have e : F.interpBound k * L * (F.mesh N).meshSize =
      F.interpConst k * ((F.mesh N).meshSize * L) +
        F.interpConst (k + 1) * ((F.mesh N).meshSize * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : D.complexMin.d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((F.whitneyMin N).le_domain k (k + 1) hv)⟩ =
        D.complexMin.d k (k + 1) ⟨_, hxj⟩ - D.complexMin.d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', F.complexMin_d_formL2 k (hw.of_le (by norm_num)) hdeg ⟨_, hxj⟩ rfl, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact mul_nonneg (mul_nonneg (F.interpBound_nonneg _) hL0) hh

end MeshFamily

/-! ### The finite element theorems on `Ω` -/

/-- **The Poincaré inequality of a Hilbert complex** with constant `c_P`:
`‖z‖ ≤ c_P ‖d z‖` on `D(d) ∩ 𝔷⊥`, in every degree (equivalently, closed range). -/
def HasPoincare {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)]
    [∀ i, CompleteSpace (W i)] (H : HilbertComplex ℝ (ComplexShape.up ℤ) W) (cP : ℝ) : Prop :=
  ∀ i j, (ComplexShape.up ℤ).Rel i j → ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ →
    ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖

/-- A larger constant also works. -/
theorem HasPoincare.mono {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
    {H : HilbertComplex ℝ (ComplexShape.up ℤ) W} {cP cP' : ℝ} (h : HasPoincare H cP)
    (hle : cP ≤ cP') : HasPoincare H cP' := fun i j hij z hz =>
  (h i j hij z hz).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D) [NeZero n]

instance (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((F.whitney N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((F.whitney N).V (a + i)))

instance (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((F.whitneyMin N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((F.whitneyMin N).V (a + i)))

/-- **Uniformly bounded smoothed cochain projections with vanishing harmonic gap** onto the
Whitney complexes, when the harmonic forms of `HΛ(Ω)` are finite-dimensional. -/
theorem smoothedProjection_uniform [∀ j, FiniteDimensional ℝ (D.complex.harmonic j)] :
    Parallelepiped.HasUniformProj D.complex F.whitney := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_proj
  choose π hb hg using hK
  exact ⟨K, π, hK1, hb, hg, fun j => Subcomplex.CochainProjection.tendsto_harmonicGap π
    (zero_le_one.trans hK1) (fun N x => hb N j x) fun q _ => F.tendsto_infDist_whitney j q⟩

/-- **Uniform discrete Poincaré inequality** on the Whitney complexes of the family
([AFW2010], Thm 3.6), under the Poincaré inequality of `HΛ(Ω)`. -/
theorem discretePoincare {cP : ℝ} (hP : HasPoincare D.complex cP) :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ D.Ω (formIdx n i)} (hx : x ∈ (F.whitney N).V i),
      (∀ y ∈ (F.whitney N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖D.complex.d i j ⟨x, (F.whitney N).le_domain i j hx⟩‖ := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_proj
  refine ⟨K * cP, fun {i j} hij N x hx hxo => ?_⟩
  obtain ⟨π, hb, -⟩ := hK N
  exact π.norm_le_of_forall_inner_eq_zero hij (hP i j hij) (zero_le_one.trans hK1) (hb i) hx hxo

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian**
([AFW2010], Thm 3.8), under the Poincaré inequality of `HΛ(Ω)`. -/
theorem mixed_wellPosed {cP : ℝ} (hP : HasPoincare D.complex cP) :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.whitney N).V j),
      (∃! x, (F.whitney N).toHilbertComplex.mixedForm i j k x =
        (F.whitney N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.whitney N).toHilbertComplex.MixedSpace i j,
        (F.whitney N).toHilbertComplex.mixedForm i j k x =
          (F.whitney N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine F.exists_uniform_proj.elim fun K hK => ?_
  have hcP : 1 ≤ max 1 cP := le_max_left _ _
  have hP' := hP.mono (le_max_right 1 cP)
  refine ⟨16 * (K * max 1 cP) ^ 2, fun {i j k} hij hjk N f =>
    (hK.2 N).elim fun π hπ => ⟨?_, fun x hx => ?_⟩⟩
  · exact π.existsUnique_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) f
  · exact π.norm_le_of_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) hx

/-- **Quasi-optimality of the mixed method** ([AFW2010], Thm 3.9) with weights `μ_j(N) → 0`,
under the Poincaré inequality and the finite-dimensionality of the harmonic forms of `HΛ(Ω)`. -/
theorem mixed_quasiOptimal {cP : ℝ} (hP : HasPoincare D.complex cP)
    [∀ j, FiniteDimensional ℝ (D.complex.harmonic j)] :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complex.domainSpace i} {u : D.complex.domainSpace j}
    {q : D.complex.harmonic j},
    D.complex.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (F.whitney N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.whitney N) hij hjk f).fst‖ +
        ‖u - (F.whitney N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitney N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.whitney N) hij hjk f).snd.snd : (F.whitney N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.whitney N).domainSub i) +
        Metric.infDist u ((F.whitney N).domainSub j) +
        Metric.infDist (q : L2F ℝ D.Ω (formIdx n j)) ((F.whitney N).harmonicW j) +
        μ j N * Metric.infDist (D.complex.boundaryPart j (D.complex.domainIncl j u))
          ((F.whitney N).domainSub j)) :=
  Parallelepiped.mixed_quasiOptimal_of hP F.smoothedProjection_uniform

/-- **`O(h)` convergence of the mixed method for `C²` solutions** ([AFW2010], Thm 3.9;
[Arnold2018], Ch. 7), under the Poincaré inequality of `HΛ(Ω)`: if `σ`, `u`, `P_𝔅 u` and the
harmonic part `q` are `C²` forms with bound `L`, the error of the discrete Whitney solutions is
`≤ K L h_N` with `K` independent of `N`. No finite-dimensionality of `ℌ` is needed. -/
theorem mixed_rate_smooth {cP : ℝ} (hP : HasPoincare D.complex cP) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complex.domainSpace i} {u : D.complex.domainSpace j}
    {q : D.complex.harmonic j} (hs : D.complex.IsMixedSolution i j k f σ u q) {L : ℝ}
    (hL0 : 0 ≤ L) (hσ : D.IsC2Form i L (D.complex.domainIncl i σ))
    (hu : D.IsC2Form j L (D.complex.domainIncl j u))
    (hb : D.IsC2Form j L (D.complex.domainIncl j
      (D.complex.boundaryPart j (D.complex.domainIncl j u))))
    (hq : D.IsC2Form j L (q : L2F ℝ D.Ω (formIdx n j))) :
    ∃ K : ℝ, ∀ N : ℕ,
      ‖σ - (F.whitney N).embD i
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitney N) hij hjk f).fst‖ +
        ‖u - (F.whitney N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitney N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.whitney N) hij hjk f).snd.snd : (F.whitney N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_proj
  choose π hπb hπg using hK
  refine ⟨(1 + 144 * (K * √(1 + cP ^ 2)) ^ 2) * (1 + K) *
    (2 * (F.interpBound i + F.interpBound j) * (3 + 2 * K)), fun N => ?_⟩
  have h := Parallelepiped.mixed_rate_of hP π hK1 hπg (Reg := fun l x => D.IsC2Form l L x)
    (B := fun l => F.interpBound l * L)
    (fun l => mul_nonneg (F.interpBound_nonneg l) hL0) (r := fun N => (F.mesh N).meshSize)
    (fun N => (F.meshSize_pos N).le)
    (fun N l x hx => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_whitney_le_of_isC2Form hx hL0 N
      exact ⟨v, hv, h1, h2⟩) hij hjk hs hσ hu hb hq N
  refine h.trans (le_of_eq ?_)
  ring

/-- **Convergence of the semi-discrete Hodge wave equation** on every window of `HΛ(Ω)`
([QuennevilleBelair2015], Thm 4.14), with no hypothesis: the Whitney windows approximate every
point of the graph space (`eventually_exists_whitney_near`). -/
theorem exists_tendstoUniformlyOn_window (a : ℤ) (m : ℕ) (t₀ t₁ : ℝ)
    (x : (D.complex.window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → (D.complex.window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((F.whitney N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((F.whitney N).window a m).graphSub)
        ((D.complex.window a m).totalD.toGraphSpace
          ⟨x, ((D.complex.window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => (D.complex.window a m).totalD.graphFst (ξh N t))
        (fun t => (D.complex.window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  Parallelepiped.exists_tendstoUniformlyOn_window_of
    (fun i x _ hε => F.eventually_exists_whitney_near i x hε) a m t₀ t₁ x

/-- **Uniformly bounded smoothed cochain projections with vanishing harmonic gap** onto the
Whitney complexes, when the harmonic forms of `H̊Λ(Ω)` are finite-dimensional. -/
theorem smoothedProjection_uniformMin [∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)] :
    Parallelepiped.HasUniformProj D.complexMin F.whitneyMin := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_projMin
  choose π hb hg using hK
  exact ⟨K, π, hK1, hb, hg, fun j => Subcomplex.CochainProjection.tendsto_harmonicGap π
    (zero_le_one.trans hK1) (fun N x => hb N j x) fun q _ => F.tendsto_infDist_whitneyMin j q⟩

/-- **Uniform discrete Poincaré inequality** on the Whitney complexes of the family
([AFW2010], Thm 3.6), under the Poincaré inequality of `H̊Λ(Ω)`. -/
theorem discretePoincareMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ D.Ω (formIdx n i)} (hx : x ∈ (F.whitneyMin N).V i),
      (∀ y ∈ (F.whitneyMin N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖D.complexMin.d i j ⟨x, (F.whitneyMin N).le_domain i j hx⟩‖ := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_projMin
  refine ⟨K * cP, fun {i j} hij N x hx hxo => ?_⟩
  obtain ⟨π, hb, -⟩ := hK N
  exact π.norm_le_of_forall_inner_eq_zero hij (hP i j hij) (zero_le_one.trans hK1) (hb i) hx hxo

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian**
([AFW2010], Thm 3.8), under the Poincaré inequality of `H̊Λ(Ω)`. -/
theorem mixed_wellPosedMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.whitneyMin N).V j),
      (∃! x, (F.whitneyMin N).toHilbertComplex.mixedForm i j k x =
        (F.whitneyMin N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.whitneyMin N).toHilbertComplex.MixedSpace i j,
        (F.whitneyMin N).toHilbertComplex.mixedForm i j k x =
          (F.whitneyMin N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine F.exists_uniform_projMin.elim fun K hK => ?_
  have hcP : 1 ≤ max 1 cP := le_max_left _ _
  have hP' := hP.mono (le_max_right 1 cP)
  refine ⟨16 * (K * max 1 cP) ^ 2, fun {i j k} hij hjk N f =>
    (hK.2 N).elim fun π hπ => ⟨?_, fun x hx => ?_⟩⟩
  · exact π.existsUnique_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) f
  · exact π.norm_le_of_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) hx

/-- **Quasi-optimality of the mixed method** ([AFW2010], Thm 3.9) with weights `μ_j(N) → 0`,
under the Poincaré inequality and the finite-dimensionality of the harmonic forms of `H̊Λ(Ω)`. -/
theorem mixed_quasiOptimalMin {cP : ℝ} (hP : HasPoincare D.complexMin cP)
    [∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)] :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complexMin.domainSpace i} {u : D.complexMin.domainSpace j}
    {q : D.complexMin.harmonic j},
    D.complexMin.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (F.whitneyMin N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.whitneyMin N) hij hjk f).fst‖ +
        ‖u - (F.whitneyMin N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitneyMin N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.whitneyMin N) hij hjk f).snd.snd : (F.whitneyMin N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.whitneyMin N).domainSub i) +
        Metric.infDist u ((F.whitneyMin N).domainSub j) +
        Metric.infDist (q : L2F ℝ D.Ω (formIdx n j)) ((F.whitneyMin N).harmonicW j) +
        μ j N * Metric.infDist (D.complexMin.boundaryPart j (D.complexMin.domainIncl j u))
          ((F.whitneyMin N).domainSub j)) :=
  Parallelepiped.mixed_quasiOptimal_of hP F.smoothedProjection_uniformMin

/-- **`O(h)` convergence of the mixed method for `C²` solutions** ([AFW2010], Thm 3.9;
[Arnold2018], Ch. 7), under the Poincaré inequality of `H̊Λ(Ω)`: if `σ`, `u`, `P_𝔅 u` and the
harmonic part `q` are `C²` forms with bound `L`, the error of the discrete Whitney solutions is
`≤ K L h_N` with `K` independent of `N`. No finite-dimensionality of `ℌ` is needed. -/
theorem mixed_rate_smoothMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complexMin.domainSpace i} {u : D.complexMin.domainSpace j}
    {q : D.complexMin.harmonic j} (hs : D.complexMin.IsMixedSolution i j k f σ u q) {L : ℝ}
    (hL0 : 0 ≤ L) (hσ : D.IsC2FormMin i L (D.complexMin.domainIncl i σ))
    (hu : D.IsC2FormMin j L (D.complexMin.domainIncl j u))
    (hb : D.IsC2FormMin j L (D.complexMin.domainIncl j
      (D.complexMin.boundaryPart j (D.complexMin.domainIncl j u))))
    (hq : D.IsC2FormMin j L (q : L2F ℝ D.Ω (formIdx n j))) :
    ∃ K : ℝ, ∀ N : ℕ,
      ‖σ - (F.whitneyMin N).embD i
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitneyMin N) hij hjk f).fst‖ +
        ‖u - (F.whitneyMin N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.whitneyMin N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.whitneyMin N) hij hjk f).snd.snd : (F.whitneyMin N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_projMin
  choose π hπb hπg using hK
  refine ⟨(1 + 144 * (K * √(1 + cP ^ 2)) ^ 2) * (1 + K) *
    (2 * (F.interpBound i + F.interpBound j) * (3 + 2 * K)), fun N => ?_⟩
  have h := Parallelepiped.mixed_rate_of hP π hK1 hπg (Reg := fun l x => D.IsC2FormMin l L x)
    (B := fun l => F.interpBound l * L)
    (fun l => mul_nonneg (F.interpBound_nonneg l) hL0) (r := fun N => (F.mesh N).meshSize)
    (fun N => (F.meshSize_pos N).le)
    (fun N l x hx => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_whitneyMin_le_of_isC2FormMin hx hL0 N
      exact ⟨v, hv, h1, h2⟩) hij hjk hs hσ hu hb hq N
  refine h.trans (le_of_eq ?_)
  ring

/-- **Convergence of the semi-discrete Hodge wave equation** on every window of `H̊Λ(Ω)`
([QuennevilleBelair2015], Thm 4.14), with no hypothesis: the Whitney windows approximate every
point of the graph space (`eventually_exists_whitney_near`). -/
theorem exists_tendstoUniformlyOn_windowMin (a : ℤ) (m : ℕ) (t₀ t₁ : ℝ)
    (x : (D.complexMin.window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → (D.complexMin.window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((F.whitneyMin N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((F.whitneyMin N).window a m).graphSub)
        ((D.complexMin.window a m).totalD.toGraphSpace
          ⟨x, ((D.complexMin.window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => (D.complexMin.window a m).totalD.graphFst (ξh N t))
        (fun t => (D.complexMin.window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  Parallelepiped.exists_tendstoUniformlyOn_window_of
    (fun i x _ hε => F.eventually_exists_whitneyMin_near i x hε) a m t₀ t₁ x

end MeshFamily

/-! ### Non-vacuity: the cube and its Freudenthal meshes -/

namespace CubeWitness

variable (n)

/-- The cube `Q = (0, ½)ⁿ` as a domain star-shaped with respect to `B((¼, …, ¼), ¼)`, with
`cl Q ⊆ B̄((¼, …, ¼), ¼)`. -/
def starDomain : StarDomain n where
  Ω := FEM.cubeDomain n
  isOpen := FEM.isOpen_cubeDomain n
  x₀ := FEM.center n
  s₀ := 1 / 4
  R := 1 / 4
  s₀_pos := by norm_num
  R_pos := by norm_num
  starBall := FEM.starBall n
  norm_sub_le := fun _ hy => FEM.norm_sub_center_le hy

variable [NeZero n]

theorem meshSize_mesh (N : ℕ) : (FEM.mesh n N).meshSize = FEM.meshSize N := by
  have hne : (FEM.mesh n N).simplices.Nonempty :=
    ⟨_, mem_freudenthalMesh_simplices.2 ⟨0, 1, rfl⟩⟩
  exact (FEM.mesh n N).meshSize_eq hne fun T hT => (FEM.mesh_shape n N hT).2

/-- **The Freudenthal meshes of the cube** are uniformly shape regular (constants `max n 2`,
`1`) and quasi-uniform (`q = 1`), with mesh size `h_N = 1 / (2 (N + 1)) → 0`. -/
def meshFamily : MeshFamily (starDomain n) where
  mesh := FEM.mesh n
  C := ((max n 2 : ℕ) : ℝ)
  c := 1
  q := 1
  C_nonneg := Nat.cast_nonneg _
  c_pos := one_pos
  q_pos := one_pos
  domain_eq := FEM.mesh_domain n
  data N := by
    refine ⟨fun T hT => ?_, fun T hT => ?_, ?_⟩
    · have := isShapeRegular_freudenthalMesh (0 : Fin n → ℝ) (1 / 2) (by norm_num) T ⟨N, hT⟩
      exact_mod_cast this
    · rw [one_mul, meshSize_mesh, (FEM.mesh_shape n N hT).2]
    · rw [meshSize_mesh]; exact FEM.meshSize_pos N
  tendsto_meshSize := by
    simp only [meshSize_mesh]; exact FEM.tendsto_meshSize

omit [NeZero n] in
/-- The Poincaré inequality of `HΛ(Q)`, `c_P = (2π)⁻¹` (`FEM.norm_le_of_mem_orthogonal_cycles`). -/
theorem hasPoincare : HasPoincare (starDomain n).complex (2 * Real.pi)⁻¹ :=
  fun _ _ hij z hz => FEM.norm_le_of_mem_orthogonal_cycles hij z hz

omit [NeZero n] in
/-- The Poincaré inequality of `H̊Λ(Q)`, `c_P = (2π)⁻¹`. -/
theorem hasPoincareMin : HasPoincare (starDomain n).complexMin (2 * Real.pi)⁻¹ :=
  fun _ _ hij z hz => FEM.norm_le_of_mem_orthogonal_cycles_min hij z hz

instance (j : ℤ) : FiniteDimensional ℝ ((starDomain n).complex.harmonic j) :=
  FEM.finiteDimensional_harmonic j

instance (j : ℤ) : FiniteDimensional ℝ ((starDomain n).complexMin.harmonic j) :=
  FEM.finiteDimensional_harmonic_min j

end CubeWitness

/-! ### Images under affine equivalences; non-vacuity on parallelepipeds -/

section AffineImage

variable (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))

/-- The linear part of the affine equivalence `e`, as a continuous linear equivalence. -/
def linCLE : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := e.linear.toContinuousLinearEquiv

/-- A Lipschitz constant `‖e⃗‖ + 1 > 0` of `e`. -/
def lipConst : ℝ := ‖(linCLE e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ + 1

/-- A Lipschitz constant `‖e⃗⁻¹‖ + 1 > 0` of `e⁻¹`. -/
def lipConstInv : ℝ := ‖((linCLE e).symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ + 1

/-- The Jacobian `|det e⃗|` of `e`. -/
def jacAbs : ℝ := |LinearMap.det (e.linear : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))|

theorem lipConst_pos : 0 < lipConst e := by unfold lipConst; positivity

theorem lipConstInv_pos : 0 < lipConstInv e := by unfold lipConstInv; positivity

theorem jacAbs_pos : 0 < jacAbs e :=
  abs_pos.2 (LinearEquiv.isUnit_det' e.linear).ne_zero

theorem linCLE_apply (x : Fin n → ℝ) : linCLE e x = e.linear x := rfl

theorem sub_eq_linCLE (x y : Fin n → ℝ) : e x - e y = linCLE e (x - y) := by
  rw [linCLE_apply, ← vsub_eq_sub, ← vsub_eq_sub]
  exact (e.toAffineMap.linear_apply_vsub x y).symm

theorem symm_sub_eq_linCLE_symm (x y : Fin n → ℝ) :
    e.symm x - e.symm y = (linCLE e).symm (x - y) := by
  apply (linCLE e).injective
  rw [← sub_eq_linCLE, ContinuousLinearEquiv.apply_symm_apply, e.apply_symm_apply,
    e.apply_symm_apply]

theorem norm_linCLE_le : ‖(linCLE e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ lipConst e := by
  unfold lipConst; linarith

theorem norm_linCLE_symm_le :
    ‖((linCLE e).symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ lipConstInv e := by
  unfold lipConstInv; linarith

theorem dist_apply_le (x y : Fin n → ℝ) : dist (e x) (e y) ≤ lipConst e * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, sub_eq_linCLE]
  exact ((linCLE e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (norm_linCLE_le e) (norm_nonneg _))

theorem dist_symm_apply_le (x y : Fin n → ℝ) :
    dist (e.symm x) (e.symm y) ≤ lipConstInv e * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, symm_sub_eq_linCLE_symm]
  exact (((linCLE e).symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (norm_linCLE_symm_le e) (norm_nonneg _))

/-- `h_{e(K)} ≤ (‖e⃗‖ + 1) h_K`. -/
theorem diam_mapEquiv_le (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    diam (mapEquiv e K) ≤ lipConst e * diam K := by
  rw [diam, closedInterior_mapEquiv]
  refine Metric.diam_le_of_forall_dist_le (mul_nonneg (lipConst_pos e).le (diam_nonneg K)) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (dist_apply_le e x y).trans (mul_le_mul_of_nonneg_left
    (Metric.dist_le_diam_of_mem K.isCompact_closedInterior.isBounded hx hy) (lipConst_pos e).le)

/-- `h_K ≤ (‖e⃗⁻¹‖ + 1) h_{e(K)}`. -/
theorem diam_le_diam_mapEquiv (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    diam K ≤ lipConstInv e * diam (mapEquiv e K) := by
  refine Metric.diam_le_of_forall_dist_le
    (mul_nonneg (lipConstInv_pos e).le (diam_nonneg _)) fun x hx y hy => ?_
  have hb := (mapEquiv e K).isCompact_closedInterior.isBounded
  have hx' : e x ∈ (mapEquiv e K).closedInterior := by
    rw [closedInterior_mapEquiv]; exact ⟨x, hx, rfl⟩
  have hy' : e y ∈ (mapEquiv e K).closedInterior := by
    rw [closedInterior_mapEquiv]; exact ⟨y, hy, rfl⟩
  have h := dist_symm_apply_le e (e x) (e y)
  rw [e.symm_apply_apply, e.symm_apply_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem hb hx' hy')
    (lipConstInv_pos e).le)

theorem linearPart_mapEquiv_apply (K : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    (mapEquiv e K).linearPart x = linCLE e (K.linearPart x) := by
  simp only [Affine.Simplex.linearPart_apply, mapEquiv_points, map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [sub_eq_linCLE]

/-- `B_{e(K)} = e⃗ B_K`. -/
theorem linearPart_mapEquiv (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    (mapEquiv e K).linearPart = (e.linear : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ K.linearPart :=
  LinearMap.ext fun x => linearPart_mapEquiv_apply e K x

theorem norm_linearEquiv_mapEquiv_le (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ‖((mapEquiv e K).linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤
      lipConst e * ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (lipConst_pos e).le (norm_nonneg _)) fun x => ?_
  rw [ContinuousLinearEquiv.coe_coe, Affine.Simplex.linearEquiv_apply,
    linearPart_mapEquiv_apply, mul_assoc]
  refine ((linCLE e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm _).trans
    (mul_le_mul (norm_linCLE_le e) ?_ (norm_nonneg _) (lipConst_pos e).le)
  exact (K.linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm x

theorem norm_linearEquiv_symm_mapEquiv_le (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ‖((mapEquiv e K).linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤
      ‖(K.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ * lipConstInv e := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _) (lipConstInv_pos e).le) fun x => ?_
  have hx : (mapEquiv e K).linearEquiv.symm x = K.linearEquiv.symm ((linCLE e).symm x) := by
    apply (mapEquiv e K).linearEquiv.injective
    rw [ContinuousLinearEquiv.apply_symm_apply, Affine.Simplex.linearEquiv_apply,
      linearPart_mapEquiv_apply, ← Affine.Simplex.linearEquiv_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearEquiv.coe_coe, hx, mul_assoc]
  refine ((K.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact (((linCLE e).symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_linCLE_symm_le e) (norm_nonneg _))

theorem abs_det_linearPart_mapEquiv (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    |LinearMap.det (mapEquiv e K).linearPart| = jacAbs e * |LinearMap.det K.linearPart| := by
  rw [linearPart_mapEquiv, LinearMap.det_comp, abs_mul, jacAbs]

/-- **Shape regularity is preserved by affine equivalences**: the images of a shape-regular set
of simplices with constants `C, c` are shape regular with constants `L L' C` and
`|det e⃗| c / Lⁿ`, `L = ‖e⃗‖ + 1`, `L' = ‖e⃗⁻¹‖ + 1` ([Ciarlet2002], §3.1). -/
theorem isShapeRegular_image {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hS : IsShapeRegular S C c) :
    IsShapeRegular (mapEquiv e '' S) (lipConst e * lipConstInv e * C)
      (jacAbs e * c / lipConst e ^ n) := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨h1, h2, h3⟩ := hS K hK
  have hL := lipConst_pos e
  have hL' := lipConstInv_pos e
  have hdT := diam_mapEquiv_le e K
  have hdK := diam_le_diam_mapEquiv e K
  have hK0 := diam_nonneg K
  have hT0 := diam_nonneg (mapEquiv e K)
  refine ⟨?_, ?_, ?_⟩
  · refine (norm_linearEquiv_mapEquiv_le e K).trans ?_
    calc lipConst e * ‖(K.linearEquiv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖
        ≤ lipConst e * (C * (lipConstInv e * diam (mapEquiv e K))) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hdK hC)) hL.le
      _ = _ := by ring
  · refine (norm_linearEquiv_symm_mapEquiv_le e K).trans ?_
    rcases hT0.eq_or_lt with h0 | h0
    · have hK' : diam K = 0 := le_antisymm (by rw [← h0, mul_zero] at hdK; exact hdK) hK0
      rw [hK', div_zero] at h2
      rw [← h0, div_zero]
      exact (mul_le_mul_of_nonneg_right h2 hL'.le).trans (by rw [zero_mul])
    · have hKpos : 0 < diam K := by
        by_contra hne
        have : diam K = 0 := le_antisymm (not_lt.1 hne) hK0
        rw [this, mul_zero] at hdT
        linarith
      calc ‖(K.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ * lipConstInv e
          ≤ C / diam K * lipConstInv e := mul_le_mul_of_nonneg_right h2 hL'.le
        _ ≤ lipConst e * lipConstInv e * C / diam (mapEquiv e K) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hKpos h0]
          have := mul_le_mul_of_nonneg_left hdT (mul_nonneg hC hL'.le)
          nlinarith
  · rw [abs_det_linearPart_mapEquiv]
    have hpow : (diam (mapEquiv e K) / lipConst e) ^ n ≤ diam K ^ n :=
      pow_le_pow_left₀ (div_nonneg hT0 hL.le) ((div_le_iff₀ hL).2 (by linarith)) n
    calc jacAbs e * c / lipConst e ^ n * diam (mapEquiv e K) ^ n
        = jacAbs e * (c * (diam (mapEquiv e K) / lipConst e) ^ n) := by
          rw [div_pow]; field_simp
      _ ≤ jacAbs e * (c * diam K ^ n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hc) (jacAbs_pos e).le
      _ ≤ jacAbs e * |LinearMap.det K.linearPart| :=
          mul_le_mul_of_nonneg_left h3 (jacAbs_pos e).le

theorem meshSize_nonneg' (M : SimplicialMesh n) : 0 ≤ M.meshSize :=
  Real.iSup_nonneg fun _ => diam_nonneg _

theorem meshSize_map_le (M : SimplicialMesh n) :
    (M.map e).meshSize ≤ lipConst e * M.meshSize := by
  refine SimplicialMesh.meshSize_le _ (mul_nonneg (lipConst_pos e).le (meshSize_nonneg' M))
    fun T hT => ?_
  obtain ⟨K, hK, rfl⟩ := M.mem_map_simplices.1 hT
  exact (diam_mapEquiv_le e K).trans
    (mul_le_mul_of_nonneg_left (M.diam_le_meshSize hK) (lipConst_pos e).le)

theorem meshSize_le_meshSize_map (M : SimplicialMesh n) :
    M.meshSize ≤ lipConstInv e * (M.map e).meshSize := by
  refine SimplicialMesh.meshSize_le _
    (mul_nonneg (lipConstInv_pos e).le (meshSize_nonneg' _)) fun K hK => ?_
  exact (diam_le_diam_mapEquiv e K).trans (mul_le_mul_of_nonneg_left
    ((M.map e).diam_le_meshSize (M.mem_map_simplices.2 ⟨K, hK, rfl⟩)) (lipConstInv_pos e).le)

theorem simplices_map_eq (M : SimplicialMesh n) :
    ((M.map e).simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) =
      mapEquiv e '' (M.simplices : Set (Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  ext T
  simp only [Finset.mem_coe, M.mem_map_simplices, Set.mem_image]

/-- **Mesh data are preserved by affine equivalences**, with constants depending only on
`C, c, q` and `‖e⃗‖, ‖e⃗⁻¹‖, |det e⃗|`. -/
theorem MeshData.map {M : SimplicialMesh n} {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hq : 0 < q)
    (h : MeshData M C c q) :
    MeshData (M.map e) (lipConst e * lipConstInv e * C) (jacAbs e * c / lipConst e ^ n)
      (q / (lipConst e * lipConstInv e)) := by
  have hL := lipConst_pos e
  have hL' := lipConstInv_pos e
  refine ⟨?_, fun T hT => ?_, ?_⟩
  · rw [simplices_map_eq]; exact isShapeRegular_image e hC hc h.shape
  · obtain ⟨K, hK, rfl⟩ := M.mem_map_simplices.1 hT
    have hq1 := h.quasi K hK
    have hm := meshSize_map_le e M
    have hd := diam_le_diam_mapEquiv e K
    calc q / (lipConst e * lipConstInv e) * (M.map e).meshSize
        ≤ q / (lipConst e * lipConstInv e) * (lipConst e * M.meshSize) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = q * M.meshSize / lipConstInv e := by field_simp
      _ ≤ diam K / lipConstInv e := div_le_div_of_nonneg_right hq1 hL'.le
      _ ≤ diam (mapEquiv e K) := (div_le_iff₀ hL').2 (by linarith)
  · have := meshSize_le_meshSize_map e M
    have h0 := h.meshSize_pos
    by_contra hne
    have : (M.map e).meshSize ≤ 0 := not_lt.1 hne
    nlinarith

end AffineImage

namespace StarDomain

variable (D : StarDomain n) (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))

/-- **The image of a star-shaped domain under an affine equivalence** `e`, given as any set
`Ω' = e(Ω)`: it is star-shaped with respect to `B(e x₀, s₀ / (‖e⃗⁻¹‖ + 1))`, with
`cl Ω' ⊆ B̄(e x₀, (‖e⃗‖ + 1) R)`. -/
def map (Ω' : Set (Fin n → ℝ)) (hΩ' : Ω' = e '' D.Ω) : StarDomain n where
  Ω := Ω'
  isOpen := hΩ' ▸ (AffineEquiv.toContinuousAffineEquiv e).toHomeomorph.isOpenMap _ D.isOpen
  x₀ := e D.x₀
  s₀ := D.s₀ / lipConstInv e
  R := lipConst e * D.R
  s₀_pos := div_pos D.s₀_pos (lipConstInv_pos e)
  R_pos := mul_pos (lipConst_pos e) D.R_pos
  starBall := by
    subst hΩ'
    rintro _ ⟨y, hy, rfl⟩ z hz
    have hz' : e.symm z ∈ Metric.ball D.x₀ D.s₀ := by
      rw [Metric.mem_ball] at hz ⊢
      have h := dist_symm_apply_le e z (e D.x₀)
      rw [e.symm_apply_apply] at h
      have hL' := lipConstInv_pos e
      calc dist (e.symm z) D.x₀ ≤ lipConstInv e * dist z (e D.x₀) := h
        _ < lipConstInv e * (D.s₀ / lipConstInv e) := mul_lt_mul_of_pos_left hz hL'
        _ = D.s₀ := by field_simp
    have hseg := image_segment ℝ e.toAffineMap (e.symm z) y
    rw [AffineEquiv.coe_toAffineMap, e.apply_symm_apply] at hseg
    rw [← hseg]
    exact Set.image_mono (D.starBall y hy _ hz')
  norm_sub_le := by
    subst hΩ'
    have hcl : closure (e '' D.Ω) = e '' closure D.Ω :=
      ((AffineEquiv.toContinuousAffineEquiv e).toHomeomorph.image_closure D.Ω).symm
    rw [hcl]
    rintro _ ⟨y, hy, rfl⟩
    rw [← dist_eq_norm]
    exact (dist_apply_le e y D.x₀).trans
      (mul_le_mul_of_nonneg_left (by rw [dist_eq_norm]; exact D.norm_sub_le y hy)
        (lipConst_pos e).le)

end StarDomain

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D) (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))

/-- **The image of a mesh family under an affine equivalence** `e`: the meshes `e(M_N)` of
`e(Ω)` are again uniformly shape regular and quasi-uniform with `h_N → 0`. -/
def map (Ω' : Set (Fin n → ℝ)) (hΩ' : Ω' = e '' D.Ω) : MeshFamily (D.map e Ω' hΩ') where
  mesh N := (F.mesh N).map e
  C := lipConst e * lipConstInv e * F.C
  c := jacAbs e * F.c / lipConst e ^ n
  q := F.q / (lipConst e * lipConstInv e)
  C_nonneg := mul_nonneg (mul_pos (lipConst_pos e) (lipConstInv_pos e)).le F.C_nonneg
  c_pos := div_pos (mul_pos (jacAbs_pos e) F.c_pos) (pow_pos (lipConst_pos e) n)
  q_pos := div_pos F.q_pos (mul_pos (lipConst_pos e) (lipConstInv_pos e))
  domain_eq N := by
    change e '' (F.mesh N).domain = Ω'
    rw [F.domain_eq N, hΩ']
  data N := (F.data N).map e F.C_nonneg F.c_pos.le F.q_pos
  tendsto_meshSize := by
    have h := F.tendsto_meshSize.const_mul (lipConst e)
    rw [mul_zero] at h
    exact squeeze_zero (fun N => meshSize_nonneg' _) (fun N => meshSize_map_le e (F.mesh N)) h

end MeshFamily

namespace ParallelepipedWitness

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- The parallelepiped `Ω = A · (0, ½)ⁿ + b` as a star-shaped domain: the image of the cube
(`CubeWitness.starDomain`) under `T x = A x + b`. -/
def starDomain : StarDomain n :=
  (CubeWitness.starDomain n).map (Parallelepiped.affEquiv A hA b) (Parallelepiped.domain A b)
    (Parallelepiped.domain_eq_image A hA b)

variable [NeZero n]

/-- The image Freudenthal meshes `T(M_N)` of the parallelepiped as a mesh family. -/
def meshFamily : MeshFamily (starDomain A hA b) :=
  (CubeWitness.meshFamily n).map (Parallelepiped.affEquiv A hA b) _ _

end ParallelepipedWitness

end Feec.Models.StarShaped
