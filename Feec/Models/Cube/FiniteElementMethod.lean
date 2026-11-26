module

public import Feec.FiniteElement.SmoothedInterp
public import Feec.FiniteElement.WhitneyComplex
public import Feec.HilbertComplex.Approximation.Convergence
public import Feec.HilbertComplex.Approximation.ConformingFamily

/-!
# Smoothed projections and the finite element method on cube meshes

The Whitney complexes of `Q = (0, ½)ⁿ` with their smoothed interpolants: bounded cochain
projections under the estimates of [AFW2010], §5.5 and [ChristiansenWinther2008].

## Main results

* `FEM.exists_tendstoUniformlyOn_window`: convergence of the semi-discrete Hodge wave equation when
  the Whitney windows approximate the graph space.
* `FEM.norm_sub_le_meshSize_window`: its `O(h)` error for solutions approximable at rate `h`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

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

/-- **The Whitney complex of the level-`(N + 1)` Freudenthal mesh** as a subcomplex of `HΛ(Q)`. -/
def whitney (N : ℕ) : (complex n).Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (whitneySubcomplex (mesh n N) (isOpen_mesh_domain n N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitney n N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

/-- **The smoothed canonical interpolant** `Q_N = Π_h R` on the Freudenthal Whitney complex. -/
def smoothed (N : ℕ) (p : SmoothingParam (Fin n → ℝ)) (hp : p.IsMaximal (center n) (1 / 4)) :
    (whitney n N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEq (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    ((whitneyElement n).smoothedCommutingMap (mesh n N) p (isOpen_mesh_domain n N)
      (starBall_mesh n N) hp)

/-! ## The finite element method on the cube under the smoothed-projection estimates -/

variable (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ)

/-- **The smoothing estimates** ([AFW2010], §5.5; [ChristiansenWinther2008]). -/
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

/-- **The Whitney complex with vanishing boundary DOFs**, a subcomplex of `H̊Λ(Q)`. -/
def whitneyMin (N : ℕ) : (complexMin n).Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (whitneySubcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitneyMin n N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

/-- **The smoothed canonical interpolant with vanishing boundary DOFs** `Q̊_N = Π_h R`. -/
def smoothedMin (N : ℕ) (p : SmoothingParam (Fin n → ℝ)) (hp : p.IsMinimal (center n) (1 / 4)) :
    (whitneyMin n N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEqMin (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    ((whitneyElement n).smoothedCommutingMapMin (mesh n N) p (isOpen_mesh_domain n N)
      (mesh_domain n N ▸ isBounded_cubeDomain n) (starBall_mesh n N) hp (center n)
      (strictStar_mesh n N))

/-- **The smoothing estimates with vanishing boundary DOFs** ([AFW2010], §5.5). -/
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

theorem isApproximating_window (a : ℤ) (m : ℕ)
    (hd : ∀ ζ : ((complex n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((whitney n N).window a m).graphSub, ‖ζ - w‖ < δ) :
    HodgeWave.IsApproximating atTop fun N => ((whitney n N).window a m).graphSub :=
  Subcomplex.isApproximating hd

/-- **Convergence of the semi-discrete Hodge wave equation on the cube meshes** for `D(L)` data,
uniformly on `[t₀, t₁]`, when the Whitney windows approximate the graph space
([QuennevilleBelair2015], Thm 4.14). -/
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

/-- **`O(h)` error of the semi-discrete Hodge wave equation** ([QuennevilleBelair2015], Thm 4.14):
started at the elliptic projection of `ξ(t₀)`, with `ξ(s)`, `ξ'(s)` within `K h_N` of the Whitney
window, `‖ξ(t) - ξₕ(t)‖_{L²} ≤ A (1 + t - t₀)² K h_N`, with the rate as in [Arnold2018], Ch. 7. -/
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
