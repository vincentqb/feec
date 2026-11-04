module

public import Feec.Models.StarShaped.Smoothing
public import Feec.FiniteElement.SmoothDensity
public import Feec.HilbertComplex.Approximation.StaticFEEC

/-!
# The finite element method on domains star-shaped with respect to a ball

Let `Ω ⊆ ℝⁿ` be a bounded open domain star-shaped with respect to every point of a ball
`B(x₀, s₀)`, with `cl Ω ⊆ B̄(x₀, R)` (`StarDomain`), and let `M_N` be conforming simplicial meshes
of `Ω` that are uniformly **shape regular** (`‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T`,
`c h_Tⁿ ≤ |det B_T|`) and **quasi-uniform** (`q h_N ≤ h_T`), with `h_N → 0` (`MeshFamily`). The
finite element theory of the Freudenthal meshes of the cube (`Feec.Models.Cube.SmoothingEstimates`,
`Feec.Models.Cube.FiniteElementConvergence`) holds for the lowest-order Whitney complexes of
`M_N`, with both boundary conditions.

**The smoothed-projection estimates, unconditionally** ([AFW2010], §5.5;
[ChristiansenWinther2008]; `Feec.Models.StarShaped.Smoothing`): uniformly bounded smoothed
cochain projections onto `Vₕ ⊆ HΛ(Ω)` and `V̊ₕ ⊆ H̊Λ(Ω)`, in `L²` and every graph norm
(`exists_uniform_cochainProjection`, `exists_uniform_cochainProjectionMin`; for the family,
`MeshFamily.exists_uniform_proj`, `MeshFamily.exists_uniform_projMin`).

**Approximation, unconditionally.** The Whitney interpolation error on shape-regular meshes
(`Feec.FiniteElement.norm_formL2_sub_glue_le_of_isShapeRegular`) gives the rate `h_N` for `C²`
forms (`MeshFamily.exists_mem_whitney_le`, `MeshFamily.exists_mem_whitney_le_of_isC2Form`, and
the `Min` versions for forms vanishing outside `Ω`), and with the density of smooth forms
(`Feec.FiniteElement.exists_smooth_near_of_starBall`, `_min_of_starBall`) graph-norm
density of the Whitney spaces (`MeshFamily.eventually_exists_whitney_near`, `..._whitneyMin_near`).

**The finite element families** (`MeshFamily`, both families, `Min` for `H̊Λ(Ω)`): the Whitney
complexes with the smoothed projections are **conforming families** (`MeshFamily.whitneyFamily`,
`MeshFamily.whitneyFamilyMin`) with the **Jackson estimates** of order `h_N` for `C²` forms
(`MeshFamily.whitneyJackson`, `MeshFamily.whitneyJacksonMin`; `StarDomain.IsC2Form`), so the
static FEEC theorem (`Feec.HilbertComplex.ConformingFamily.staticFEEC`: uniform discrete
Poincaré inequality, well-posedness and stability, harmonic gap, cohomology, quasi-optimality,
convergence) and its rates hold for them; the semi-discrete Hodge wave equation converges on
every window with no hypothesis (`exists_tendstoUniformlyOn_window`; [QuennevilleBelair2015],
Thm 4.14).

**Remaining hypotheses.** The cochain projections, the approximation results and the wave
convergence are proved with no hypothesis. The Poincaré inequality of `HΛ(Ω)`, resp. `H̊Λ(Ω)`
(`HasPoincare`, equivalently closed range), is the hypothesis of the static theorems
(`ConformingFamily.quasiOptimal` and `ConformingFamily.rate` need it only in the degrees of the
problem); it holds on every bounded Lipschitz domain (regularized Poincaré and Bogovskiĭ
operators, [CostabelMcIntosh2010]), a theory absent from Mathlib, and is a theorem on the cube
and on every parallelepiped (`Feec.Models.Parallelepiped.StarShaped`). The finite-dimensionality
of the harmonic forms is used only for the harmonic gap and the cohomology.
**Affine images**: shape regularity, quasi-uniformity and star-shapedness with respect to a ball
are preserved by affine equivalences (`StarDomain.map`, `MeshFamily.map`; `isShapeRegular_image`,
`MeshData.map`). **Non-vacuity**: the cube with its Freudenthal meshes and every parallelepiped
`A · Q + b` (every box) with its image Freudenthal meshes are `StarDomain`s with a `MeshFamily`
satisfying all these hypotheses (`Feec.Models.Parallelepiped.StarShaped`:
`CubeWitness.meshFamily`, `CubeWitness.hasPoincare`, `ParallelepipedWitness.meshFamily`). The
higher-order families `P_rΛᵏ`, `P_r⁻Λᵏ` (whose inverse and DOF estimates on shape-regular simplices
are
`Feec.FiniteElement.exists_inverse_bound_polySpace` and
`Feec.FiniteElement.exists_dof_bound_of_le_polySpace`) are in
`Feec.Models.StarShaped.PolyFiniteElement`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (Thm 3.6), Thm 3.8, Thm 3.9, §5.5 (smoothed projections)
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

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

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
in `L²` and in every graph norm of `HΛ(Ω)` ([AFW2010], §5.5; [ChristiansenWinther2008]), with no
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
  have hcl : closure (F.mesh N).domain = closure D.Ω := by rw [F.domain_eq N]
  have hΩ := (F.isOpen_domain N).measurableSet
  refine (whitneyElement n).exists_mem_maximalSubcomplexOfEq_le (F.mesh N) (F.domain_eq N)
    (F.isOpen_domain N) D.isOpen D.isBounded k hw1
    (A := F.interpConst k * ((F.mesh N).meshSize * L))
    (A' := F.interpConst (k + 1) * ((F.mesh N).meshSize * L'))
    ((norm_formL2_sub_glue_le_of_isShapeRegular _ hΩ k hw1 F.C_nonneg (F.meshSize_pos N).le hL0
      (fun y hy => hL y (hcl ▸ hy)) (F.data N).shape (F.diam_le N)).trans_eq ?_)
    ((norm_formL2_sub_glue_le_of_isShapeRegular _ hΩ (k + 1) (contDiff_extDeriv (m := 1) hw)
      F.C_nonneg (F.meshSize_pos N).le hL'0 (fun y hy => hL' y (hcl ▸ hy)) (F.data N).shape
      (F.diam_le N)).trans_eq ?_) <;>
  · rw [F.domain_eq N, interpConst]; push_cast; ring

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
  have hcl : closure (F.mesh N).domain = closure D.Ω := by rw [F.domain_eq N]
  have hΩ := (F.isOpen_domain N).measurableSet
  refine (whitneyElement n).exists_mem_minimalSubcomplexOfEq_le (F.mesh N) (F.domain_eq N)
    (F.isOpen_domain N) D.isOpen D.isBounded D.x₀ (F.strict_mesh N) k hw1 hsupp
    (A := F.interpConst k * ((F.mesh N).meshSize * L))
    (A' := F.interpConst (k + 1) * ((F.mesh N).meshSize * L'))
    ((norm_formL2_sub_glue_le_of_isShapeRegular _ hΩ k hw1 F.C_nonneg (F.meshSize_pos N).le hL0
      (fun y hy => hL y (hcl ▸ hy)) (F.data N).shape (F.diam_le N)).trans_eq ?_)
    ((norm_formL2_sub_glue_le_of_isShapeRegular _ hΩ (k + 1) (contDiff_extDeriv (m := 1) hw)
      F.C_nonneg (F.meshSize_pos N).le hL'0 (fun y hy => hL' y (hcl ▸ hy)) (F.data N).shape
      (F.diam_le N)).trans_eq ?_) <;>
  · rw [F.domain_eq N, interpConst]; push_cast; ring

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

end StarDomain

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D) [NeZero n]

/-- **Graph-norm density of the Whitney spaces in `HΛᵏ(Ω)`**: the canonical interpolants of
smooth forms converge at rate `h_N` (`exists_mem_whitney_le`,
`eventually_exists_graph_of_smooth`). -/
theorem eventually_exists_whitney_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complex.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitney N).V k, ‖x - v‖ < ε ∧
      ‖D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.whitney N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth D.isOpen D.isBounded D.s₀_pos D.starBall
    (fun N => F.whitney N) (fun k w hw _ => ?_) k x hx hε
  have hw2 : ContDiff ℝ 2 w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_fderiv (hw.of_le (by exact_mod_cast le_top))
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_fderiv (contDiff_extDeriv (m := 1) hw2)
  refine ⟨fun N => F.interpConst k * ((F.mesh N).meshSize * L) +
      F.interpConst (k + 1) * ((F.mesh N).meshSize * L'), by
    have := ((F.tendsto_meshSize.mul_const L).const_mul (F.interpConst k)).add
      ((F.tendsto_meshSize.mul_const L').const_mul (F.interpConst (k + 1)))
    simpa using this, fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_whitney_le N k hw2 hL0 hL'0 hL hL'
  have hb1 := mul_nonneg (F.interpConst_nonneg (k + 1)) (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.interpConst_nonneg k) (mul_nonneg (F.meshSize_pos N).le hL0)
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right hb1), hdv,
    hv2.trans (le_add_of_nonneg_left hb0)⟩

/-- **`L²` density of the Whitney spaces** `Vₕᵏ` in `L²(Ω; Λᵏ)`. -/
theorem eventually_exists_whitney_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.whitney N).V k, ‖x - v‖ < ε :=
  Subcomplex.eventually_exists_lt_of_graph
    (fun k x hx _ hε => F.eventually_exists_whitney_graph k x hx hε) k x hε

/-- **Degreewise approximation in every graph norm of `HΛ(Ω)`**. -/
theorem eventually_exists_whitney_near (i : ℤ) (x : L2F ℝ D.Ω (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitney N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (D.complex.d i j).domain),
        ‖D.complex.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.whitney N).le_domain i j hv)⟩‖ <
          ε :=
  Subcomplex.eventually_exists_near_of_graph
    (fun k x hx _ hε => F.eventually_exists_whitney_graph k x hx hε) i x hε

/-- `dist(q, Vₕʲ) → 0` for every `q ∈ L²(Ω; Λʲ)`. -/
theorem tendsto_infDist_whitney (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.whitney N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => F.whitney N) q fun _ ha =>
    F.eventually_exists_whitney_lt j q ha

/-- **Graph-norm density of the Whitney spaces in `H̊Λᵏ(Ω)`**: the canonical interpolants of
smooth forms vanishing outside `Ω` converge at rate `h_N` (`exists_mem_whitneyMin_le`,
`eventually_exists_graph_of_smooth_min`). -/
theorem eventually_exists_whitneyMin_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complexMin.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitneyMin N).V k, ‖x - v‖ < ε ∧
      ‖D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.whitneyMin N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine eventually_exists_graph_of_smooth_min D.isOpen D.isBounded D.s₀_pos D.starBall
    (fun N => F.whitneyMin N) (fun k w hw _ hsupp => ?_) k x hx hε
  have hw2 : ContDiff ℝ 2 w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_fderiv (hw.of_le (by exact_mod_cast le_top))
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_fderiv (contDiff_extDeriv (m := 1) hw2)
  refine ⟨fun N => F.interpConst k * ((F.mesh N).meshSize * L) +
      F.interpConst (k + 1) * ((F.mesh N).meshSize * L'), by
    have := ((F.tendsto_meshSize.mul_const L).const_mul (F.interpConst k)).add
      ((F.tendsto_meshSize.mul_const L').const_mul (F.interpConst (k + 1)))
    simpa using this, fun N => ?_⟩
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_whitneyMin_le N k hw2 hsupp hL0 hL'0 hL hL'
  have hb1 := mul_nonneg (F.interpConst_nonneg (k + 1)) (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.interpConst_nonneg k) (mul_nonneg (F.meshSize_pos N).le hL0)
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right hb1), hdv,
    hv2.trans (le_add_of_nonneg_left hb0)⟩

/-- **`L²` density of the Whitney spaces with vanishing boundary DOFs** `V̊ₕᵏ` in `L²(Ω; Λᵏ)`. -/
theorem eventually_exists_whitneyMin_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.whitneyMin N).V k, ‖x - v‖ < ε :=
  Subcomplex.eventually_exists_lt_of_graph
    (fun k x hx _ hε => F.eventually_exists_whitneyMin_graph k x hx hε) k x hε

/-- **Degreewise approximation in every graph norm of `H̊Λ(Ω)`**. -/
theorem eventually_exists_whitneyMin_near (i : ℤ) (x : L2F ℝ D.Ω (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.whitneyMin N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (D.complexMin.d i j).domain),
        ‖D.complexMin.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.whitneyMin N).le_domain i j hv)⟩‖ <
          ε :=
  Subcomplex.eventually_exists_near_of_graph
    (fun k x hx _ hε => F.eventually_exists_whitneyMin_graph k x hx hε) i x hε

/-- `dist(q, V̊ₕʲ) → 0` for every `q ∈ L²(Ω; Λʲ)`. -/
theorem tendsto_infDist_whitneyMin (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.whitneyMin N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) :=
  Subcomplex.tendsto_infDist_of_lt (S := fun N => F.whitneyMin N) q fun _ ha =>
    F.eventually_exists_whitneyMin_lt j q ha

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
  · have := LocalElement.subsingleton_L2F_of_neg D.Ω (n := n) hj
    exact (F.whitney N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_whitney_le N k hw hL0 hL0 hL hL'
  obtain ⟨hdom, hval⟩ := F.formL2_mem_domain k (hw.of_le (by norm_num)) hdeg
  have hh := (F.meshSize_pos N).le
  have hA0 := mul_nonneg (F.interpConst_nonneg k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (F.interpConst_nonneg (k + 1)) (mul_nonneg hh hL0)
  have e : F.interpBound k * L * (F.mesh N).meshSize =
      F.interpConst k * ((F.mesh N).meshSize * L) +
        F.interpConst (k + 1) * ((F.mesh N).meshSize * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [hval, e]
  linarith

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
  · have := LocalElement.subsingleton_L2F_of_neg D.Ω (n := n) hj
    exact (F.whitneyMin N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_whitneyMin_le N k hw hsupp hL0 hL0 hL hL'
  have hh := (F.meshSize_pos N).le
  have hA0 := mul_nonneg (F.interpConst_nonneg k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (F.interpConst_nonneg (k + 1)) (mul_nonneg hh hL0)
  have e : F.interpBound k * L * (F.mesh N).meshSize =
      F.interpConst k * ((F.mesh N).meshSize * L) +
        F.interpConst (k + 1) * ((F.mesh N).meshSize * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [F.complexMin_d_formL2 k (hw.of_le (by norm_num)) hdeg ⟨_, hxj⟩ rfl, e]
  linarith

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

/-- **The Whitney forms of a shape-regular, quasi-uniform mesh family** of a domain star-shaped
with respect to a ball, with the smoothed projections (`exists_uniform_proj`), a conforming
family of `HΛ(Ω)`. -/
def whitneyFamily : ConformingFamily D.complex ℕ :=
  .ofExists atTop F.whitney
    (by
      obtain ⟨K, -, hK⟩ := F.exists_uniform_proj
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    F.tendsto_infDist_whitney

/-- **The Whitney forms with vanishing boundary DOFs of the mesh family**, a conforming family of
`H̊Λ(Ω)`. -/
def whitneyFamilyMin : ConformingFamily D.complexMin ℕ :=
  .ofExists atTop F.whitneyMin
    (by
      obtain ⟨K, -, hK⟩ := F.exists_uniform_projMin
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    F.tendsto_infDist_whitneyMin

@[simp] theorem whitneyFamily_V : F.whitneyFamily.V = F.whitney := rfl

@[simp] theorem whitneyFamilyMin_V : F.whitneyFamilyMin.V = F.whitneyMin := rfl

/-- **The Jackson estimate of the Whitney forms of the mesh family**: `C²` forms on `cl Ω`
(`StarDomain.IsC2Form`) at the order `h_N` with the constants `interpBound`
(`exists_mem_whitney_le_of_isC2Form`). -/
def whitneyJackson : F.whitneyFamily.Jackson Unit where
  meshSize N := (F.mesh N).meshSize
  meshSize_nonneg N := (F.meshSize_pos N).le
  tendsto_meshSize := F.tendsto_meshSize
  Reg _ := D.IsC2Form
  ord _ := 1
  B _ := F.interpBound
  B_nonneg _ := F.interpBound_nonneg
  jackson _ N _ _ _ hL hx := by
    rw [Real.rpow_one, ← mul_assoc]; exact F.exists_mem_whitney_le_of_isC2Form hx hL N

/-- **The Jackson estimate of the Whitney forms with vanishing boundary DOFs**: `C²` forms
vanishing outside `Ω` (`StarDomain.IsC2FormMin`) at the order `h_N`. -/
def whitneyJacksonMin : F.whitneyFamilyMin.Jackson Unit where
  meshSize N := (F.mesh N).meshSize
  meshSize_nonneg N := (F.meshSize_pos N).le
  tendsto_meshSize := F.tendsto_meshSize
  Reg _ := D.IsC2FormMin
  ord _ := 1
  B _ := F.interpBound
  B_nonneg _ := F.interpBound_nonneg
  jackson _ N _ _ _ hL hx := by
    rw [Real.rpow_one, ← mul_assoc]; exact F.exists_mem_whitneyMin_le_of_isC2FormMin hx hL N

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
  Subcomplex.exists_tendstoUniformlyOn_window_of
    (fun i x _ hε => F.eventually_exists_whitney_near i x hε) a m t₀ t₁ x

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
  Subcomplex.exists_tendstoUniformlyOn_window_of
    (fun i x _ hε => F.eventually_exists_whitneyMin_near i x hε) a m t₀ t₁ x

end MeshFamily

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

end Feec.Models.StarShaped
