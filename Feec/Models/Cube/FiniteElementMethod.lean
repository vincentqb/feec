module

public import Feec.FiniteElement.SmoothedInterp
public import Feec.FiniteElement.WhitneyComplex
public import Feec.HilbertComplex.Approximation.Convergence
public import Feec.HilbertComplex.Approximation.ConformingFamily

/-!
# Smoothed projections and the finite element method on cube meshes

The smoothed canonical interpolant `Q = Π_h R` of an element family and its commuting maps
(`Feec.FiniteElement.LocalElement.smoothedCommutingMap`,
`Feec.FiniteElement.LocalElement.smoothedCommutingMapMin`) are in
`Feec.FiniteElement.SmoothedInterp`.

**The cube.** On `Q = (0, ½)ⁿ` (`FEM.cubeDomain`, star-shaped with respect to `B((¼, …, ¼), ¼)`,
`FEM.starBall`) with the level-`(N + 1)` Freudenthal meshes (`FEM.mesh`, mesh size
`h_N = 1 / (2 (N + 1))`, `FEM.meshSize`), the Whitney complexes `FEM.whitney N` (Lagrange `P₁`,
Nédélec, Raviart–Thomas, piecewise constants; transported to one Hilbert complex
`FEM.complex = HΛ(Q)`) carry the concrete smoothed interpolants `FEM.smoothed N p`. Under the
**estimates of [AFW2010], §5.5 and [ChristiansenWinther2008]** for these maps (uniform `L²`
bound `C` and `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ`; the structure `FEM.SmoothingEstimates`, taken as a
hypothesis here and proved for explicit parameters in `Feec.Models.Cube.SmoothingEstimates`):

* uniformly bounded cochain projections `π_N` with `‖π_N‖ ≤ 2C` in `L²`
  (`SmoothingEstimates.proj`, `SmoothingEstimates.norm_proj_le`), hence in every graph norm
  (`Subcomplex.CochainProjection.isGraphBounded_of_norm_le`); with the density of the Whitney
  spaces they make the Whitney complexes a conforming family (`SmoothingEstimates.family` in
  `Feec.Models.Cube.FiniteElementConvergence`), to which the static FEEC theorem
  (`Feec.HilbertComplex.ConformingFamily.staticFEEC`: discrete Poincaré inequality,
  well-posedness, quasi-optimality, harmonic gap, cohomology, convergence) applies;
* for the Hodge wave equation of any window, the Whitney windows are approximating as soon as they
  are dense (`FEM.isApproximating_window`), hence convergence of the semi-discrete solutions
  (`FEM.exists_tendstoUniformlyOn_window`), and the rate `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + t - t₀)² K h_N`
  when the solution and its time derivative are approximable at rate `h`
  (`FEM.norm_sub_le_meshSize_window`, from `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, which needs
  no smoothed projection); **Maxwell's equations** (perfect
  magnetic conductor, `n = 3`, window `HΛ⁰ → HΛ¹ → L²Λ²`) are the instance `a = 0`, `m = 3`.

**Remaining hypotheses.** None for the cube: the three hypotheses of this module are theorems
elsewhere, and `Feec.Models.Cube.FiniteElementConvergence` states the results without them.
(1) `FEM.SmoothingEstimates` and `FEM.SmoothingEstimatesMin` hold for explicit parameters
(`FEM.smoothingEstimates_pMax`, `FEM.smoothingEstimatesMin_pMin` in
`Feec.Models.Cube.SmoothingEstimates`, from the inverse estimates of
`Feec.FiniteElement.InverseEstimate`); (2) the Poincaré inequalities of `HΛ(Q)` and `H̊Λ(Q)` hold
with `c_P = (2π)⁻¹` (`FEM.norm_le_of_mem_orthogonal_cycles`, `_min` in
`Feec.Models.Cube.DeRhamIdentFEM`, from the identification of `HΛ(Q)`, `H̊Λ(Q)` with the parity
classes of the torus complex, `Feec.Models.Cube.DeRhamIdent`); (3) the Whitney spaces approximate
at rate `h` for `C²` forms and are dense (`Feec.Models.Cube.WhitneyApprox`,
`Feec.Models.Cube.WhitneyRate`, from `Feec.FiniteElement.WhitneyInterpolation`). The statements of
this module keep (1) as a hypothesis so that they apply to any parameters and constants. For the
Einstein–Bianchi (BGG) system, `Feec.BGG.Discrete` needs subcomplexes of
both rows with cochain projections satisfying `Π S = S_h Π'`; vector-valued Whitney forms and such
a pair of projections are not constructed, so that structure remains an explicit hypothesis of
`Feec.HilbertComplex.BGG.Discrete`.

**The vanishing-trace family.** For minimal-family parameters (`c > 1`), the commuting maps
into `V̊ₕ` give on the cube `FEM.whitneyMin`, `FEM.smoothedMin` and, under the analogous explicit
estimates `FEM.SmoothingEstimatesMin`, uniformly bounded cochain projections onto `V̊ₕ`
(`SmoothingEstimatesMin.proj`, `SmoothingEstimatesMin.norm_proj_le`; the conforming family
`SmoothingEstimatesMin.family`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothed projections), Thm 3.6, Thm 3.8, Thm 3.9
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (canonical interpolants, Whitney forms)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (bounded commuting
  projections, approximation)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

/-! ## Freudenthal meshes of the cube `(0, ½)ⁿ` -/

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex

variable (n : ℕ)

/-- The cube `Q = (0, ½)ⁿ`. -/
def cubeDomain : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Ioo 0 (1 / 2)

theorem isOpen_cubeDomain : IsOpen (cubeDomain n) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem convex_cubeDomain : Convex ℝ (cubeDomain n) :=
  convex_pi fun _ _ => convex_Ioo _ _

/-- The maximal de Rham complex `HΛ(Q)` of the cube. -/
abbrev complex : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (cubeDomain n) (formIdx n k) :=
  (deRham ℝ n).maximalComplex (isOpen_cubeDomain n)

/-- The centre `(¼, …, ¼)` of the cube. -/
def center : Fin n → ℝ := fun _ => 1 / 4

/-- **The cube is star-shaped with respect to the ball `B(centre, ¼)`** (in the sup norm of
`ℝⁿ` this ball is the cube itself; the cube is convex). -/
theorem starBall : ∀ y ∈ cubeDomain n, ∀ z ∈ Metric.ball (center n) (1 / 4),
    segment ℝ z y ⊆ cubeDomain n := by
  intro y hy z hz
  have hzQ : z ∈ cubeDomain n := by
    rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num)] at hz
    intro i _
    have := hz i
    rw [Real.dist_eq, center, abs_lt] at this
    constructor <;> linarith
  exact (convex_cubeDomain n).segment_subset hzQ hy

/-- The level-`(N + 1)` Freudenthal mesh of the cube, mesh size `h = 1 / (2 (N + 1))`. -/
def mesh (N : ℕ) : SimplicialMesh n := freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)

/-- The mesh size `h_N = 1 / (2 (N + 1))` (the edge of the cubes of the Freudenthal mesh). -/
def meshSize (N : ℕ) : ℝ := 1 / 2 / (N + 1)

theorem meshSize_pos (N : ℕ) : 0 < meshSize N := by unfold meshSize; positivity

theorem tendsto_meshSize : Tendsto meshSize atTop (𝓝 0) := by
  unfold meshSize
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem mesh_domain (N : ℕ) : (mesh n N).domain = cubeDomain n := by
  rw [mesh, freudenthalMesh_domain]
  simp [cubeDomain]

theorem isOpen_mesh_domain (N : ℕ) : IsOpen (mesh n N).domain :=
  isOpen_freudenthalMesh_domain _ _ _ _

theorem starBall_mesh (N : ℕ) : ∀ y ∈ (mesh n N).domain, ∀ z ∈ Metric.ball (center n) (1 / 4),
    segment ℝ z y ⊆ (mesh n N).domain := by
  rw [mesh_domain]; exact starBall n

variable [NeZero n]

/-- **The Whitney complex of the level-`(N + 1)` Freudenthal mesh** (Lagrange `P₁`, and in `ℝ³`
Nédélec edge and Raviart–Thomas face elements, piecewise constants) as a subcomplex of `HΛ(Q)`. -/
def whitney (N : ℕ) : (complex n).Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (whitneySubcomplex (mesh n N) (isOpen_mesh_domain n N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitney n N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

/-- **The smoothed canonical interpolant** `Q_N = Π_h R` on the Freudenthal Whitney complex of
the cube, for maximal-family smoothing parameters centred at the centre of the cube. -/
def smoothed (N : ℕ) (p : SmoothingParam (Fin n → ℝ)) (hp : p.IsMaximal (center n) (1 / 4)) :
    (whitney n N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEq (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    ((whitneyElement n).smoothedCommutingMap (mesh n N) p (isOpen_mesh_domain n N)
      (starBall_mesh n N) hp)

/-! ## The finite element method on the cube under the smoothed-projection estimates -/

variable (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ)

/-- **The estimates of the smoothed canonical interpolants** ([AFW2010], §5.5;
[ChristiansenWinther2008]): for maximal-family smoothing parameters `p N` (any
`IsMaximal` parameters; the structure imposes no scaling), the smoothed interpolants
`Q_N = Π_h R` of the Whitney complexes are bounded in `L²` uniformly in `N`, and close to the
identity on `Vₕ`: `‖v - Q_N v‖ ≤ ½ ‖v‖`. In the references these are obtained with the scaling
factor `1 - δ h_N`, bump radius `≈ δ h_N` and `δ` small, from elementwise inverse estimates for
polynomials and the interpolation error of `Π_h` on smoothed fields. They are the hypotheses of
this section, so that its results apply to any parameters; for the parameters `FEM.pMax γ` they
are proved in `Feec.Models.Cube.SmoothingEstimates` (`FEM.smoothingEstimates_pMax`,
`FEM.smoothingEstimates_exists`). The maps `Q_N` themselves are the
concrete smoothed interpolants `smoothed n N (p N)`, and their commutation with `d` is proved
(`Feec.FiniteElement.LocalElement.smoothedCommutingMap`). The constant is normalized by
`½ ≤ C` (any bound can be enlarged). -/
structure SmoothingEstimates : Prop where
  isMaximal : ∀ N, (p N).IsMaximal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(smoothed n N (p N) (isMaximal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (whitney n N).V i,
    ‖v - (smoothed n N (p N) (isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

namespace SmoothingEstimates

variable {n p C}

/-- **The smoothed projection** `π_N = J_N⁻¹ Q_N` onto the Whitney complex of the cube. -/
def proj (hE : SmoothingEstimates n p C) (N : ℕ) : (whitney n N).CochainProjection :=
  (smoothed n N (p N) (hE.isMaximal N)).toCochainProjection (θ := 1 / 2) (by norm_num)
    (hE.close N)

theorem two_mul_nonneg (hE : SmoothingEstimates n p C) : 0 ≤ 2 * C := by linarith [hE.half_le]

variable (hE : SmoothingEstimates n p C)
include hE

/-- **Uniform `L²` bound**: `‖π_N x‖ ≤ 2 C ‖x‖` for every `N`. -/
theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ :=
  (smoothed n N (p N) (hE.isMaximal N)).norm_toCochainProjection_le_two_mul (hE.close N)
    (hE.bound N i) x

end SmoothingEstimates

/-! ## The vanishing-trace family `H̊Λ(Q)` -/

/-- The minimal `L²` de Rham complex `H̊Λ(Q)` of the cube (vanishing tangential traces). -/
abbrev complexMin : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (cubeDomain n) (formIdx n k) :=
  (deRham ℝ n).minimalComplex (isOpen_cubeDomain n)

omit [NeZero n] in
theorem isBounded_cubeDomain : Bornology.IsBounded (cubeDomain n) :=
  Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _

omit [NeZero n] in
theorem center_mem_cubeDomain : center n ∈ cubeDomain n := fun i _ => by
  simp only [center, Set.mem_Ioo]; norm_num

omit [NeZero n] in
theorem strictStar_mesh (N : ℕ) : ∀ x ∈ closure (mesh n N).domain, ∀ t : ℝ, 0 ≤ t → t < 1 →
    center n + t • (x - center n) ∈ (mesh n N).domain := by
  rw [mesh_domain]
  exact add_smul_sub_mem_of_convex (isOpen_cubeDomain n) (convex_cubeDomain n)
    (center_mem_cubeDomain n)

/-- **The Whitney complex with vanishing boundary DOFs** of the level-`(N + 1)` Freudenthal mesh,
as a subcomplex of `H̊Λ(Q)`. -/
def whitneyMin (N : ℕ) : (complexMin n).Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (whitneySubcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitneyMin n N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

/-- **The smoothed canonical interpolant with vanishing boundary DOFs** `Q̊_N = Π_h R` on the
Freudenthal Whitney complex of `H̊Λ(Q)`, for minimal-family smoothing parameters (dilation
towards the centre, `c > 1`): `R u` is a test form on `Q`, so `Q̊_N u ∈ V̊ₕ`, and `d Q̊_N = Q̊_N d`. -/
def smoothedMin (N : ℕ) (p : SmoothingParam (Fin n → ℝ)) (hp : p.IsMinimal (center n) (1 / 4)) :
    (whitneyMin n N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEqMin (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    ((whitneyElement n).smoothedCommutingMapMin (mesh n N) p (isOpen_mesh_domain n N)
      (mesh_domain n N ▸ isBounded_cubeDomain n) (starBall_mesh n N) hp (center n)
      (strictStar_mesh n N))

/-- **The estimates of the smoothed interpolants with vanishing boundary DOFs** ([AFW2010],
§5.5, [ChristiansenWinther2008]; a hypothesis of the results below, as `SmoothingEstimates`,
proved for the parameters `FEM.pMin γ` in `Feec.Models.Cube.SmoothingEstimates`,
`FEM.smoothingEstimatesMin_pMin`): for minimal-family parameters `p N`, uniform `L²` bounds of
`Q̊_N` and `‖v - Q̊_N v‖ ≤ ½ ‖v‖` on `V̊ₕ`; normalized by `½ ≤ C`. -/
structure SmoothingEstimatesMin (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) : Prop where
  isMinimal : ∀ N, (p N).IsMinimal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(smoothedMin n N (p N) (isMinimal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (whitneyMin n N).V i,
    ‖v - (smoothedMin n N (p N) (isMinimal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

namespace SmoothingEstimatesMin

variable {n} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- **The smoothed projection** `π̊_N = J_N⁻¹ Q̊_N` onto the Whitney complex of `H̊Λ(Q)`. -/
def proj (hE : SmoothingEstimatesMin n p C) (N : ℕ) : (whitneyMin n N).CochainProjection :=
  (smoothedMin n N (p N) (hE.isMinimal N)).toCochainProjection (θ := 1 / 2) (by norm_num)
    (hE.close N)

theorem two_mul_nonneg (hE : SmoothingEstimatesMin n p C) : 0 ≤ 2 * C := by
  linarith [hE.half_le]

variable (hE : SmoothingEstimatesMin n p C)
include hE

/-- **Uniform `L²` bound** `‖π̊_N x‖ ≤ 2 C ‖x‖`. -/
theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ :=
  (smoothedMin n N (p N) (hE.isMinimal N)).norm_toCochainProjection_le_two_mul (hE.close N)
    (hE.bound N i) x

end SmoothingEstimatesMin

/-! ## The Hodge wave equation and Maxwell's equations on the cube meshes -/

instance (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((whitney n N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((whitney n N).V (a + i)))

instance (N : ℕ) (a : ℤ) (m : ℕ) : FiniteDimensional ℝ ((whitney n N).window a m).graphSub :=
  inferInstance

/-- **The Whitney windows are approximating** (for the semi-discrete Hodge wave equation of the
window `HΛᵃ(Q) → ⋯ → HΛ^{a+m-1}(Q)`) as soon as they approximate every point of the graph space
of the total differential; the uniform bound of the elliptic projections holds for every
subcomplex (`Feec.HilbertComplex.Subcomplex.norm_ellipticProjection_le`). -/
theorem isApproximating_window (a : ℤ) (m : ℕ)
    (hd : ∀ ζ : ((complex n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((whitney n N).window a m).graphSub, ‖ζ - w‖ < δ) :
    HodgeWave.IsApproximating atTop fun N => ((whitney n N).window a m).graphSub :=
  Subcomplex.isApproximating hd

/-- **Convergence of the semi-discrete Hodge wave equation on the cube meshes** for `D(L)` data
(`L` the Hodge wave operator of the window): the semi-discrete Whitney solutions with
`ξₕ(t₀) = Pₕ x` converge to `e^{(t - t₀) L} x` uniformly on `[t₀, t₁]`. See
[QuennevilleBelair2015], Thm 4.14; the error bound for each `N` is
`Feec.HodgeWave.norm_sub_le_of_semidiscrete`. -/
theorem exists_tendstoUniformlyOn_window (a : ℤ) (m : ℕ)
    (hd : ∀ ζ : ((complex n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((whitney n N).window a m).graphSub, ‖ζ - w‖ < δ)
    (t₀ t₁ : ℝ) (x : ((complex n).window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitney n N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney n N).window a m).graphSub)
        (((complex n).window a m).totalD.toGraphSpace
          ⟨x, (((complex n).window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complex n).window a m).totalD.graphFst (ξh N t))
        (fun t => ((complex n).window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  HilbertComplex.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection _
    (isApproximating_window n a m hd) t₀ t₁ x

/-- **`O(h)` error of the semi-discrete Hodge wave equation on the cube meshes**
([QuennevilleBelair2015], Thm 4.14; rate as in [Arnold2018], Ch. 7): for a weak solution `ξ` in
`C¹([t₀, t₁]; Γ(𝐝))` of the Hodge wave equation of the window and the semi-discrete Whitney
solutions `ξₕ` started at `Pₕ ξ(t₀)`, if `ξ(s)` and `ξ'(s)` are approximated in the graph norm by
the Whitney window to order `K h_N` on `[t₀, t₁]` (for smooth solutions, the interpolation error
of the Whitney interpolant), then `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² K h_N` with `A` independent
of `N` (`Feec.HilbertComplex.Subcomplex.norm_sub_le_of_approx`). -/
theorem norm_sub_le_meshSize_window (a : ℤ) (m : ℕ) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitney n N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney n N).window a m).graphSub) (ξ t₀))
    {K : ℝ}
    (happ : ∀ N, ∀ s ∈ Set.Icc t₀ t₁,
      (∃ w ∈ ((whitney n N).window a m).graphSub, ‖ξ s - w‖ ≤ K * meshSize N) ∧
      (∃ w ∈ ((whitney n N).window a m).graphSub, ‖ξ' s - w‖ ≤ K * meshSize N))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 * (K * meshSize N) :=
  ((whitney n N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (happ N) ht

end Feec.Models.Cube.FEM
