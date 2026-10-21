module

public import Feec.Models.StarShaped.PolySmoothing
public import Feec.Models.Cube.PolyRate

/-!
# The higher-order finite element method on star-shaped domains and parallelepipeds

Let `Ω ⊆ ℝⁿ` be a bounded domain star-shaped with respect to a ball (`StarDomain`) with a family
`M_N` of conforming, uniformly shape-regular and quasi-uniform meshes, `h_N → 0` (`MeshFamily`).
For every admissible sequence `S` (`P_{r_k}Λᵏ`, `P_{r_k}⁻Λᵏ` and the mixed rows), both
boundary-condition families (`MeshFamily.poly`, `MeshFamily.polyMin`; `Min` for `H̊Λ(Ω)`), the
finite element theory of the Whitney forms (`Feec.Models.StarShaped.FiniteElement`) holds at every
order, from the uniformly bounded cochain projections of `Feec.Models.StarShaped.PolySmoothing`.

**Approximation, unconditionally.** The interpolation error on shape-regular meshes gives the rate
`h_N^{s+1}` for `C^{s+2}` forms (`MeshFamily.exists_mem_poly_le`,
`MeshFamily.exists_mem_polyMin_le`; degreewise `MeshFamily.exists_mem_poly_le_of_isCsForm` for the
class `StarDomain.IsCsForm s`, `C^{s+2}` on `cl Ω`, and `StarDomain.IsCsFormMin s`, vanishing
outside `Ω`; satisfiable: `StarDomain.exists_isCsForm`), and with the density of smooth forms the
graph-norm density of the spaces (`MeshFamily.eventually_exists_poly_near`,
`MeshFamily.eventually_exists_polyMin_near`, `MeshFamily.tendsto_infDist_poly`).

**The finite element theorems** (`MeshFamily`, every `S`):
* `discretePoincare_poly`: uniform discrete Poincaré inequality ([AFW2010], Thm 3.6);
* `mixed_wellPosed_poly`: uniform well-posedness and stability of the discrete mixed Hodge
  Laplacian ([AFW2010], Thm 3.8);
* `mixed_quasiOptimal_poly`: quasi-optimality with weights `μ_j(N) → 0` ([AFW2010], Thm 3.9);
* **`mixed_rate_poly`**: error `≤ K L h_N^{s+1}` for solutions of class `IsCsForm s` and `S` of
  order `s` (`FEM.PolyOrder`), `K` independent of `N`, of the solution and of `L` ([AFW2010],
  Thm 3.9; [Arnold2018], Ch. 7), and the degreewise form `mixed_rate_poly_of_polyOrderAt`
  (`FEM.PolyOrderAt`: only the degrees of the problem matter, e.g. order `h²` of the bottom row
  `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` on `1`-forms);
* `exists_tendstoUniformlyOn_window_poly`: convergence of the semi-discrete Hodge wave equation on
  every window ([QuennevilleBelair2015], Thm 4.14), and its rate `O(h_N^{s+1})` for smooth
  solutions (`norm_sub_le_window_poly_smooth`, `norm_sub_le_window_poly_smooth_of_polyOrderAt`);
* the same with vanishing boundary DOFs (`..._polyMin`, `..._windowMin_poly...`).

**Remaining hypotheses.** On a general star-shaped domain the only hypothesis is the Poincaré
inequality of `HΛ(Ω)`, resp. `H̊Λ(Ω)` (`HasPoincare`, equivalently closed range), used by
`discretePoincare_poly`, `mixed_wellPosed_poly`, `mixed_quasiOptimal_poly` and
`mixed_rate_poly(_of_polyOrderAt)` (and their `Min` versions); it holds on every bounded Lipschitz
domain through the regularized Poincaré and Bogovskiĭ operators ([CostabelMcIntosh2010]), a
theory absent from Mathlib. `mixed_quasiOptimal_poly` also uses the finite-dimensionality of the
harmonic forms (for the vanishing harmonic gap); the rate theorems do not. The cochain
projections, the approximation results and the wave convergence and rates are proved with no
hypothesis.

**Parallelepipeds, with no hypothesis.** For every parallelepiped `Ω = A · Q + b` (every box) and
**every** quasi-uniform shape-regular mesh family of it (not only the image Freudenthal meshes),
the Poincaré inequalities are theorems (`Parallelepiped.hasPoincare`,
`Parallelepiped.hasPoincareMin`, from `Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles`
and `_min`), and so are the harmonic finite-dimensionality instances; hence
**`Parallelepiped.mixed_rate_poly_general`** and its companions
(`Parallelepiped.discretePoincare_poly_general`, `Parallelepiped.mixed_wellPosed_poly_general`,
`Parallelepiped.mixed_quasiOptimal_poly_general`,
`Parallelepiped.mixed_rate_poly_general_of_polyOrderAt`, the `Min` versions, and the instances
`Parallelepiped.mixed_rate_lagrangeP2_general` (order `h²` of the bottom row on `1`-forms) and
`Parallelepiped.mixed_rate_trimmed₂_general` (order `h²` of `P₂⁻Λ`)) hold unconditionally.

**Non-vacuity.** The cube with its Freudenthal meshes (`CubeWitness.meshFamily`) and every
parallelepiped with its image Freudenthal meshes (`ParallelepipedWitness.meshFamily`) satisfy all
the hypotheses for the bottom row and for `P₂⁻Λ` (`CubeWitness.nonvacuous_poly`,
`ParallelepipedWitness.nonvacuous_poly`), with the instances `CubeWitness.mixed_rate_lagrangeP2`
and `ParallelepipedWitness.mixed_rate_lagrangeP2`. The rate is attained by a non-zero smooth
solution: the harmonic datum `f = 1` on the cube, solved by `σ = 0`, `u = 0`, `p = 1`
(`CubeWitness.exists_mixedSolution_ne_zero`, `CubeWitness.mixed_rate_lagrangeP2_ne_zero`). The
general parallelepiped theorems apply beyond the image Freudenthal meshes: the reflected meshes
`T(reflect(M_N))` (`ParallelepipedWitness.reflectedFamily`) form a mesh family which, for `n ≥ 2`,
has at every level a simplex whose vertex set is that of no image Freudenthal simplex
(`ParallelepipedWitness.exists_reflected_simplex`, `ParallelepipedWitness.reflectedFamily_ne`),
with the instance `ParallelepipedWitness.mixed_rate_lagrangeP2_reflected`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (Thm 3.6), Thm 3.8, Thm 3.9, §5.4 (smoothed projections)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1–3.2
  (shape-regular families, interpolation error)
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

/-! ### Smooth forms of order `s` on a star-shaped domain -/

namespace StarDomain

variable (D : StarDomain n)

/-- A `C^m` form has a bounded `m`-th derivative on the compact `cl Ω`. -/
theorem exists_bound_iteratedFDeriv {m : ℕ} {w : FormField n} (hw : ContDiff ℝ m w) :
    ∃ L, 0 ≤ L ∧ ∀ y ∈ closure D.Ω, ‖iteratedFDeriv ℝ m w y‖ ≤ L := by
  obtain ⟨L, hL⟩ := D.isCompact_closure.exists_bound_of_continuousOn
    (hw.continuous_iteratedFDeriv le_rfl).continuousOn
  exact ⟨max L 0, le_max_right _ _, fun y hy => (hL y hy).trans (le_max_left _ _)⟩

/-- `x ∈ L²(Ω; Λʲ)` is a `C^{s+2}` form of degree `j` whose `(s+1)`-st derivative and that of its
exterior derivative are bounded by `L` on `cl Ω` (trivially true in negative degrees): the
regularity class of the rate `h^{s+1}` (for `s = 0` the class `IsC2Form`, with `‖D¹w‖ = ‖Dw‖`). -/
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

/-- **Every `C^{s+2}` form is `IsCsForm s`** for some bound (non-vacuity of the rate
hypotheses). -/
theorem exists_isCsForm (s : ℕ) {k : ℕ} {w : FormField n}
    (hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w) (hdeg : ∀ y, IsDeg k (w y)) :
    ∃ L, 0 ≤ L ∧ D.IsCsForm s (k : ℤ) L
      (formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩) := by
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_iteratedFDeriv (m := s + 1)
    (hw.of_le (by exact_mod_cast Nat.le_succ (s + 1)))
  have hw' : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hdw : ContDiff ℝ ((s + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) := contDiff_extDeriv hw'
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_iteratedFDeriv (m := s + 1) hdw
  exact ⟨max L L', le_max_of_le_left hL0, Or.inr ⟨k, rfl, w, hw, hdeg,
    fun y hy => (hL y hy).trans (le_max_left _ _),
    fun y hy => (hL' y hy).trans (le_max_right _ _), rfl⟩⟩

/-- **Every `C^{s+2}` form vanishing outside `Ω` is `IsCsFormMin s`** for some bound. -/
theorem exists_isCsFormMin (s : ℕ) {k : ℕ} {w : FormField n}
    (hw : ContDiff ℝ ((s + 2 : ℕ) : WithTop ℕ∞) w) (hdeg : ∀ y, IsDeg k (w y))
    (hsupp : ∀ y ∉ D.Ω, w y = 0) :
    ∃ L, 0 ≤ L ∧ D.IsCsFormMin s (k : ℤ) L
      (formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩) := by
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_iteratedFDeriv (m := s + 1)
    (hw.of_le (by exact_mod_cast Nat.le_succ (s + 1)))
  have hw' : ContDiff ℝ (((s + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
  have hdw : ContDiff ℝ ((s + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) := contDiff_extDeriv hw'
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_iteratedFDeriv (m := s + 1) hdw
  exact ⟨max L L', le_max_of_le_left hL0, Or.inr ⟨k, rfl, w, hw, hdeg, hsupp,
    fun y hy => (hL y hy).trans (le_max_left _ _),
    fun y hy => (hL' y hy).trans (le_max_right _ _), rfl⟩⟩

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

/-- The DOF constant `B_k` of `S` for the shape-regularity constants of the family
(`PolyDofBound`). -/
def polyDofConst (k : ℕ) : ℝ := (exists_polyDofBound (n := n) S k F.C F.c).choose

theorem polyDofConst_nonneg (k : ℕ) : 0 ≤ F.polyDofConst S k :=
  (exists_polyDofBound (n := n) S k F.C F.c).choose_spec.1

theorem polyDofBound_polyDofConst (k : ℕ) : PolyDofBound S n k F.C F.c (F.polyDofConst S k) :=
  (exists_polyDofBound (n := n) S k F.C F.c).choose_spec.2

/-- The constant of the `L²` interpolation estimate of degree `k` of `S` on the family:
`#Λᵏ |Ω|^{1/2} (1 + B_k D_k)`, independent of the mesh and of the order. -/
def polyInterpConst (k : ℕ) : ℝ :=
  Fintype.card (formIdx n k) * (volume.real D.Ω ^ (1 / 2 : ℝ) *
    (1 + F.polyDofConst S k * polyCoeffConst n S k))

theorem polyInterpConst_nonneg (k : ℕ) : 0 ≤ F.polyInterpConst S k := by
  unfold polyInterpConst
  have := F.polyDofConst_nonneg S k
  have := polyCoeffConst_nonneg (n := n) S k
  positivity

/-- The constant `B_j = A_j + A_{j+1}` of the graph-norm interpolation error of `S` in
degree `j`. -/
def polyInterpBound (j : ℤ) : ℝ := F.polyInterpConst S j.toNat + F.polyInterpConst S (j.toNat + 1)

theorem polyInterpBound_nonneg (j : ℤ) : 0 ≤ F.polyInterpBound S j :=
  add_nonneg (F.polyInterpConst_nonneg _ _) (F.polyInterpConst_nonneg _ _)

/-- The global canonical interpolant on a simplex is the local one. -/
theorem globalInterp_apply_eq_localInterp (E : LocalElement n) (M : SimplicialMesh n) (k : ℕ)
    (w : contForms n) (T : M.simplices) :
    ((E.globalInterp M k w : E.Piecewise M k) T) = E.localInterp T k w :=
  E.localSpace_ext T k fun g hg i => by
    rw [LocalElement.localDof_globalInterp _ _ _ _ _ _ hg,
      LocalElement.localDof_localInterp _ _ _ _ _ hg]

/-- **The pointwise interpolation error on the meshes of the family**: for `w ∈ C^{s+1}` of
degree `k` with `‖D^{s+1} w‖ ≤ L` on `cl Ω` and `P_sΛᵏ ⊆ P(T)ᵏ`, on every closed simplex,
`|w - Π_h w| ≤ (1 + B D) h_N^{s+1} L`. -/
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

/-- **The `L²` interpolation error of order `s + 1` of an admissible sequence on the meshes of the
family** ([Arnold2018], Ch. 7; [Ciarlet2002], Thm 3.1.4): for a `C^{s+2}` degree-`k` form `w` with
`‖D^{s+1} w‖ ≤ L` and `‖D^{s+1} dw‖ ≤ L'` on `cl Ω`, and `P_sΛᵏ ⊆ P(T)ᵏ`,
`P_sΛᵏ⁺¹ ⊆ P(T)ᵏ⁺¹`, the canonical interpolant `v = Π_N w ∈ Vₕᵏ` satisfies
`‖w - v‖ ≤ A_k h_N^{s+1} L` and `‖dw - dv‖ ≤ A_{k+1} h_N^{s+1} L'`. -/
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
  refine (deRham ℝ n).maximalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (S.subcomplex (F.mesh N) (F.isOpen_domain N))
    (fun Θ hΘ S' => ∀ hb : Bornology.IsBounded Θ, ∀ hvol : volume.real Θ = volume.real D.Ω,
      ∃ v ∈ S'.V k,
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - FEM.asForm n v‖ ≤
          F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L) ∧
        ∃ hv : v ∈ (((deRham ℝ n).maximalComplex hΘ).d k (k + 1)).domain,
          ‖formL2 hΘ.measurableSet hb ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw1⟩ -
            FEM.asForm n (((deRham ℝ n).maximalComplex hΘ).d k (k + 1) ⟨v, hv⟩)‖ ≤
            F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L')) ?_
    D.isBounded rfl
  intro hb hvol
  set M := F.mesh N
  have hΩo := F.isOpen_domain N
  set u := (polyElement n S).globalInterp M k (Submodule.inclusion c1Forms_le_contForms
    (⟨w, hw1⟩ : c1Forms n))
  obtain ⟨hmem, hval⟩ := FEM.glue_globalInterp_mem_maximal_of (polyElement n S) M hΩo k ⟨w, hw1⟩
  have hh := (F.meshSize_pos N).le
  have hB1 : 0 ≤ (1 + F.polyDofConst S k * polyCoeffConst n S k) *
      ((F.mesh N).meshSize ^ (s + 1) * L) := by
    have := F.polyDofConst_nonneg S k; have := polyCoeffConst_nonneg (n := n) S k; positivity
  have hB2 : 0 ≤ (1 + F.polyDofConst S (k + 1) * polyCoeffConst n S (k + 1)) *
      ((F.mesh N).meshSize ^ (s + 1) * L') := by
    have := F.polyDofConst_nonneg S (k + 1); have := polyCoeffConst_nonneg (n := n) S (k + 1)
    positivity
  refine ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k), ⟨u, rfl⟩, ?_, ?_⟩
  · have h := FEM.norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet k
      ⟨w, hw.continuous⟩ (u : (polyElement n S).Piecewise M k) hB1
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs hws hdeg hL T (interior_subset hx) t
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; ring
  · refine ⟨by rw [deRham_maximalComplex_d]; exact hmem, ?_⟩
    rw [LinearPMap.apply_eq_of_eq' (deRham_maximalComplex_d hΩo (k : ℤ))]
    have h := FEM.norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet (k + 1)
      ⟨extDeriv w, hdw.continuous⟩ ((polyElement n S).globalInterp M (k + 1)
        ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) hB2
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs' hdw hdeg' hL' T (interior_subset hx) t
    have e : (extDerivOp ℝ n k).maximal M.domain
        ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k), hmem⟩ =
        (polyElement n S).glue M ((k + 1 : ℕ) : ℤ) ((polyElement n S).globalInterp M (k + 1)
          ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) := hval
    erw [e]
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; push_cast; ring

/-- **The `L²` interpolation error with vanishing boundary DOFs**: for a `C^{s+2}` form `w`
vanishing outside `Ω`, the canonical interpolant lies in `V̊ₕᵏ ⊆ H̊Λᵏ(Ω)`, with the estimates of
`exists_mem_poly_le`. -/
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
  refine (deRham ℝ n).minimalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (S.subcomplexMin (F.mesh N) (F.isOpen_domain N) D.x₀ (F.strict_mesh N))
    (fun Θ hΘ S' => ∀ hb : Bornology.IsBounded Θ, ∀ hvol : volume.real Θ = volume.real D.Ω,
      ∃ v ∈ S'.V k,
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - FEM.asForm n v‖ ≤
          F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L) ∧
        ∃ hv : v ∈ (((deRham ℝ n).minimalComplex hΘ).d k (k + 1)).domain,
          ‖formL2 hΘ.measurableSet hb ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw1⟩ -
            FEM.asForm n (((deRham ℝ n).minimalComplex hΘ).d k (k + 1) ⟨v, hv⟩)‖ ≤
            F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L')) ?_
    D.isBounded rfl
  intro hb hvol
  set M := F.mesh N
  have hΩo := F.isOpen_domain N
  set w' : c1Forms n := ⟨w, hw1⟩
  set u := (polyElement n S).globalInterp M k (Submodule.inclusion c1Forms_le_contForms w')
  have hu₀ : (u : (polyElement n S).Piecewise M k) ∈ (polyElement n S).globalSpace₀ M k :=
    LocalElement.globalInterp_mem_globalSpace₀ _ M k fun x hx => hsupp x (by
      rw [← F.domain_eq N]; exact M.notMem_domain_of_mem_frontier hΩo hx)
  obtain ⟨hmem, hval⟩ := (polyElement n S).glue_mem_minimal M hΩo D.x₀ (F.strict_mesh N) k
    ⟨_, hu₀⟩
  have hh := (F.meshSize_pos N).le
  have hB1 : 0 ≤ (1 + F.polyDofConst S k * polyCoeffConst n S k) *
      ((F.mesh N).meshSize ^ (s + 1) * L) := by
    have := F.polyDofConst_nonneg S k; have := polyCoeffConst_nonneg (n := n) S k; positivity
  have hB2 : 0 ≤ (1 + F.polyDofConst S (k + 1) * polyCoeffConst n S (k + 1)) *
      ((F.mesh N).meshSize ^ (s + 1) * L') := by
    have := F.polyDofConst_nonneg S (k + 1); have := polyCoeffConst_nonneg (n := n) S (k + 1)
    positivity
  refine ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k),
    ⟨⟨_, hu₀⟩, rfl⟩, ?_, ?_⟩
  · have h := FEM.norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet k
      ⟨w, hw.continuous⟩ (u : (polyElement n S).Piecewise M k) hB1
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs hws hdeg hL T (interior_subset hx) t
    refine h.trans (le_of_eq ?_)
    rw [hvol, polyInterpConst]; ring
  · refine ⟨by rw [deRham_minimalComplex_d]; exact hmem, ?_⟩
    rw [LinearPMap.apply_eq_of_eq' (deRham_minimalComplex_d hΩo (k : ℤ))]
    have h := FEM.norm_formL2_sub_glue_le_of_forall (polyElement n S) M hΩo.measurableSet (k + 1)
      ⟨extDeriv w, hdw.continuous⟩ ((polyElement n S).globalInterp M (k + 1)
        ⟨extDeriv w, hdw.continuous⟩ : (polyElement n S).Piecewise M (k + 1)) hB2
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs' hdw hdeg' hL' T (interior_subset hx) t
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

/-! ### Degreewise rates -/

/-- **Degreewise interpolation error of order `s + 1`**: for `x` with `IsCsForm s j L x` and a
sequence reproducing `P_s` in the degrees `j, j + 1` (`FEM.PolyOrderAt`), some `v ∈ Vₕʲ` has
`‖x - v‖ ≤ B_j L h_N^{s+1}` and `‖d (x - v)‖ ≤ B_j L h_N^{s+1}`. -/
theorem exists_mem_poly_le_of_isCsForm {s : ℕ} {j : ℤ} (hS : FEM.PolyOrderAt n S s j) {L : ℝ}
    {x : L2F ℝ D.Ω (formIdx n j)} (hx : D.IsCsForm s j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (F.poly S N).V j,
      ‖x - v‖ ≤ F.polyInterpBound S j * L * (F.mesh N).meshSize ^ (s + 1) ∧
      ∀ j' (hxj : x ∈ (D.complex.d j j').domain),
        ‖D.complex.d j j' ⟨x - v, Submodule.sub_mem _ hxj ((F.poly S N).le_domain j j' hv)⟩‖ ≤
          F.polyInterpBound S j * L * (F.mesh N).meshSize ^ (s + 1) := by
  have hh := pow_nonneg (F.meshSize_pos N).le (s + 1)
  have hB0 := mul_nonneg (mul_nonneg (F.polyInterpBound_nonneg S j) hL0) hh
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc D.Ω (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
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
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : D.complex.d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((F.poly S N).le_domain k (k + 1) hv)⟩ =
        D.complex.d k (k + 1) ⟨_, hdom⟩ - D.complex.d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', hval, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact hB0

/-- **Degreewise interpolation error of order `s + 1` with vanishing boundary DOFs**, in
`H̊Λ(Ω)`. -/
theorem exists_mem_polyMin_le_of_isCsFormMin {s : ℕ} {j : ℤ} (hS : FEM.PolyOrderAt n S s j)
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
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc D.Ω (n := n) k
    refine ⟨0, Submodule.zero_mem _, ?_, fun j' hxj => ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hB0
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ :=
    F.exists_mem_polyMin_le S N k s (hS k rfl).1 (hS k rfl).2 hw hdeg hsupp hL0 hL0 hL hL'
  have hA0 := mul_nonneg (F.polyInterpConst_nonneg S k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1)) (mul_nonneg hh hL0)
  have e : F.polyInterpBound S k * L * (F.mesh N).meshSize ^ (s + 1) =
      F.polyInterpConst S k * ((F.mesh N).meshSize ^ (s + 1) * L) +
        F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize ^ (s + 1) * L) := by
    simp only [polyInterpBound, Int.toNat_natCast]; ring
  refine ⟨v, hv, ?_, fun j' hxj => ?_⟩
  · rw [e]; linarith
  by_cases hj : (k : ℤ) + 1 = j'
  · subst hj
    have e' : D.complexMin.d k (k + 1)
        ⟨_ - v, Submodule.sub_mem _ hxj ((F.polyMin S N).le_domain k (k + 1) hv)⟩ =
        D.complexMin.d k (k + 1) ⟨_, hxj⟩ - D.complexMin.d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e', F.complexMin_d_formL2 k (hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1)))
      hdeg ⟨_, hxj⟩ rfl, e]
    linarith
  · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]
    exact hB0

/-! ### Density of the higher-order complexes -/

/-- **Graph-norm density of the higher-order spaces in `HΛᵏ(Ω)`**: smooth forms are dense
(`StarDomain.exists_smooth_near`) and their canonical interpolants converge at rate `h_N`
(`exists_mem_poly_le` with `s = 0`). -/
theorem eventually_exists_poly_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complex.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.poly S N).V k, ‖x - v‖ < ε ∧
      ‖D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.poly S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  rcases k with k | k
  swap
  · have := LocalElement.subsingleton_L2F_negSucc D.Ω (n := n) k
    refine Eventually.of_forall fun N => ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε
  change ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.poly S N).V (k : ℤ), ‖x - v‖ < ε ∧
      ‖D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.poly S N).le_domain k (k + 1) hv)⟩‖ < ε
  obtain ⟨w, hw, hdeg, h1, h2⟩ := D.exists_smooth_near k ⟨x, hx⟩ (half_pos hε)
  have hw2 : ContDiff ℝ (0 + 2) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_iteratedFDeriv (m := 0 + 1)
    (contDiff_infty.1 hw _)
  have hdw : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) :=
    contDiff_extDeriv (contDiff_infty.1 hw _)
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_iteratedFDeriv (m := 0 + 1) hdw
  have ht : Tendsto (fun N => F.polyInterpConst S k * ((F.mesh N).meshSize * L) +
      F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize * L')) atTop (𝓝 0) := by
    have := ((F.tendsto_meshSize.mul_const L).const_mul (F.polyInterpConst S k)).add
      ((F.tendsto_meshSize.mul_const L').const_mul (F.polyInterpConst S (k + 1)))
    simpa using this
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with N hN
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_poly_le S N k 0 (FEM.polySpace_zero_le_space S k)
    (FEM.polySpace_zero_le_space S (k + 1)) hw2 hdeg hL0 hL'0 hL hL'
  rw [zero_add, pow_one] at hv1 hv2
  have hb1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.polyInterpConst_nonneg S k)
    (mul_nonneg (F.meshSize_pos N).le hL0)
  refine ⟨v, hv, ?_, ?_⟩
  · calc ‖x - v‖ ≤ ‖x - formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩‖ +
          ‖formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ - v‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 (hv1.trans (by linarith : _ ≤ ε / 2))
      _ = ε := add_halves ε
  · have e : D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.poly S N).le_domain k (k + 1) hv)⟩ =
        D.complex.d k (k + 1) ⟨x, hx⟩ - D.complex.d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e]
    calc ‖D.complex.d k (k + 1) ⟨x, hx⟩ - D.complex.d k (k + 1) ⟨v, hdv⟩‖
        ≤ ‖D.complex.d k (k + 1) ⟨x, hx⟩ - formL2 D.isOpen.measurableSet D.isBounded
            ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv
              (contDiff_infty.1 hw _)⟩‖ +
          ‖formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (contDiff_infty.1 hw _)⟩ -
            D.complex.d k (k + 1) ⟨v, hdv⟩‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h2 (hv2.trans (by linarith : _ ≤ ε / 2))
      _ = ε := add_halves ε

/-- **`L²` density of the higher-order spaces** `Vₕᵏ` in `L²(Ω; Λᵏ)`. -/
theorem eventually_exists_poly_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.poly S N).V k, ‖x - v‖ < ε := by
  obtain ⟨y, hy, hxy⟩ := (D.complex.dense k (k + 1)).exists_dist_lt x (half_pos hε)
  filter_upwards [F.eventually_exists_poly_graph S k y hy (half_pos hε)] with N hN
  obtain ⟨v, hv, h1, -⟩ := hN
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm] at hxy
  calc ‖x - v‖ ≤ ‖x - y‖ + ‖y - v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy h1
    _ = ε := add_halves ε

/-- **Degreewise approximation in every graph norm of `HΛ(Ω)`** by the higher-order spaces. -/
theorem eventually_exists_poly_near (i : ℤ) (x : L2F ℝ D.Ω (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.poly S N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (D.complex.d i j).domain),
        ‖D.complex.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.poly S N).le_domain i j hv)⟩‖ <
          ε := by
  by_cases hx : x ∈ (D.complex.d i (i + 1)).domain
  · filter_upwards [F.eventually_exists_poly_graph S i x hx hε] with N hN
    obtain ⟨v, hv, h1, h2⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact h2
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε
  · filter_upwards [F.eventually_exists_poly_lt S i x hε] with N hN
    obtain ⟨v, hv, h1⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact absurd hxj hx
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε

/-- `dist(q, Vₕʲ) → 0` for every `q ∈ L²(Ω; Λʲ)` (higher-order spaces). -/
theorem tendsto_infDist_poly (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.poly S N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N =>
    ha.trans_le Metric.infDist_nonneg, fun a ha => ?_⟩
  filter_upwards [F.eventually_exists_poly_lt S j q ha] with N hN
  obtain ⟨v, hv, h⟩ := hN
  exact (Metric.infDist_le_dist_of_mem hv).trans_lt (by rwa [dist_eq_norm])

omit [NeZero n] in
/-- The `L²` class of a `k`-form only sees its degree-`k` part. -/
theorem formL2_degField {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (k : ℕ) {w : FormField n} (hw : Continuous w) :
    formL2 hΩ hb k ⟨degField k w, continuous_degField k hw⟩ = formL2 hΩ hb k ⟨w, hw⟩ := by
  refine PiLp.ext fun s => Lp.ext ?_
  filter_upwards [coeFn_formL2 hΩ hb k ⟨degField k w, continuous_degField k hw⟩ s,
    coeFn_formL2 hΩ hb k ⟨w, hw⟩ s] with x h1 h2
  rw [h1, h2]
  have hs : #s.1 = k := by exact_mod_cast s.2
  simp [degField, hs]

/-- **Graph-norm density of the higher-order spaces with vanishing boundary DOFs in
`H̊Λᵏ(Ω)`**: smooth forms with compact support in `Ω` are dense
(`StarDomain.exists_smooth_near_min`, degree-`k` parts) and their canonical interpolants lie in
`V̊ₕᵏ` and converge at rate `h_N`. -/
theorem eventually_exists_polyMin_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complexMin.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.polyMin S N).V k, ‖x - v‖ < ε ∧
      ‖D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.polyMin S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  rcases k with k | k
  swap
  · have := LocalElement.subsingleton_L2F_negSucc D.Ω (n := n) k
    refine Eventually.of_forall fun N => ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [Subsingleton.elim (x - 0) 0, norm_zero]; exact hε
    · rw [LinearPMap.apply_mk_eq_zero _ _ (Subsingleton.elim _ _), norm_zero]; exact hε
  change ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.polyMin S N).V (k : ℤ), ‖x - v‖ < ε ∧
      ‖D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.polyMin S N).le_domain k (k + 1) hv)⟩‖ < ε
  obtain ⟨w₀, hw₀, hsupp₀, h1₀, h2₀⟩ := D.exists_smooth_near_min k ⟨x, hx⟩ (half_pos hε)
  set w := degField k w₀
  have hw : ContDiff ℝ ∞ w := contDiff_degField k hw₀
  have hdeg : ∀ y, IsDeg k (w y) := isDeg_degField k w₀
  have hsupp : ∀ y ∉ D.Ω, w y = 0 := fun y hy => by
    funext s; simp [w, degField, hsupp₀ y hy]
  have hdw : extDeriv w = degField (k + 1) (extDeriv w₀) := extDeriv_degField k w₀
  have h1 : ‖(x : L2F ℝ D.Ω (formIdx n k)) -
      formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩‖ < ε / 2 := by
    rw [formL2_degField D.isOpen.measurableSet D.isBounded k hw₀.continuous]; exact h1₀
  have h2 : ‖D.complexMin.d k (k + 1) ⟨x, hx⟩ -
      formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
        ⟨extDeriv w, continuous_extDeriv (contDiff_infty.1 hw _)⟩‖ < ε / 2 := by
    have e : formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
        ⟨extDeriv w, continuous_extDeriv (contDiff_infty.1 hw _)⟩ =
        formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
          ⟨extDeriv w₀, continuous_extDeriv (contDiff_infty.1 hw₀ _)⟩ := by
      have h := formL2_degField D.isOpen.measurableSet D.isBounded (k + 1)
        (continuous_extDeriv (contDiff_infty.1 hw₀ _))
      push_cast at h
      rw [← h]
      congr 2
    rw [e]; exact h2₀
  have hw2 : ContDiff ℝ (0 + 2) w := hw.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hL0, hL⟩ := D.exists_bound_iteratedFDeriv (m := 0 + 1)
    (contDiff_infty.1 hw _)
  have hdw' : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) :=
    contDiff_extDeriv (contDiff_infty.1 hw _)
  obtain ⟨L', hL'0, hL'⟩ := D.exists_bound_iteratedFDeriv (m := 0 + 1) hdw'
  have ht : Tendsto (fun N => F.polyInterpConst S k * ((F.mesh N).meshSize * L) +
      F.polyInterpConst S (k + 1) * ((F.mesh N).meshSize * L')) atTop (𝓝 0) := by
    have := ((F.tendsto_meshSize.mul_const L).const_mul (F.polyInterpConst S k)).add
      ((F.tendsto_meshSize.mul_const L').const_mul (F.polyInterpConst S (k + 1)))
    simpa using this
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with N hN
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_polyMin_le S N k 0
    (FEM.polySpace_zero_le_space S k) (FEM.polySpace_zero_le_space S (k + 1)) hw2 hdeg hsupp
    hL0 hL'0 hL hL'
  rw [zero_add, pow_one] at hv1 hv2
  have hb1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.polyInterpConst_nonneg S k)
    (mul_nonneg (F.meshSize_pos N).le hL0)
  refine ⟨v, hv, ?_, ?_⟩
  · calc ‖x - v‖ ≤ ‖x - formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩‖ +
          ‖formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩ - v‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 (hv1.trans (by linarith : _ ≤ ε / 2))
      _ = ε := add_halves ε
  · have e : D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.polyMin S N).le_domain k (k + 1) hv)⟩ =
        D.complexMin.d k (k + 1) ⟨x, hx⟩ - D.complexMin.d k (k + 1) ⟨v, hdv⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e]
    calc ‖D.complexMin.d k (k + 1) ⟨x, hx⟩ - D.complexMin.d k (k + 1) ⟨v, hdv⟩‖
        ≤ ‖D.complexMin.d k (k + 1) ⟨x, hx⟩ - formL2 D.isOpen.measurableSet D.isBounded
            ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv
              (contDiff_infty.1 hw _)⟩‖ +
          ‖formL2 D.isOpen.measurableSet D.isBounded ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv (contDiff_infty.1 hw _)⟩ -
            D.complexMin.d k (k + 1) ⟨v, hdv⟩‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h2 (hv2.trans (by linarith : _ ≤ ε / 2))
      _ = ε := add_halves ε

/-- **`L²` density of the higher-order spaces with vanishing boundary DOFs** `V̊ₕᵏ` in
`L²(Ω; Λᵏ)`. -/
theorem eventually_exists_polyMin_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.polyMin S N).V k, ‖x - v‖ < ε := by
  obtain ⟨y, hy, hxy⟩ := (D.complexMin.dense k (k + 1)).exists_dist_lt x (half_pos hε)
  filter_upwards [F.eventually_exists_polyMin_graph S k y hy (half_pos hε)] with N hN
  obtain ⟨v, hv, h1, -⟩ := hN
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm] at hxy
  calc ‖x - v‖ ≤ ‖x - y‖ + ‖y - v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy h1
    _ = ε := add_halves ε

/-- **Degreewise approximation in every graph norm of `H̊Λ(Ω)`** by the higher-order spaces with
vanishing boundary DOFs. -/
theorem eventually_exists_polyMin_near (i : ℤ) (x : L2F ℝ D.Ω (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.polyMin S N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (D.complexMin.d i j).domain),
        ‖D.complexMin.d i j
          ⟨x - v, Submodule.sub_mem _ hx ((F.polyMin S N).le_domain i j hv)⟩‖ < ε := by
  by_cases hx : x ∈ (D.complexMin.d i (i + 1)).domain
  · filter_upwards [F.eventually_exists_polyMin_graph S i x hx hε] with N hN
    obtain ⟨v, hv, h1, h2⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact h2
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε
  · filter_upwards [F.eventually_exists_polyMin_lt S i x hε] with N hN
    obtain ⟨v, hv, h1⟩ := hN
    refine ⟨v, hv, h1, fun j hxj => ?_⟩
    by_cases hj : i + 1 = j
    · subst hj; exact absurd hxj hx
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hj), norm_zero]; exact hε

/-- `dist(q, V̊ₕʲ) → 0` for every `q ∈ L²(Ω; Λʲ)` (higher-order spaces). -/
theorem tendsto_infDist_polyMin (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.polyMin S N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N =>
    ha.trans_le Metric.infDist_nonneg, fun a ha => ?_⟩
  filter_upwards [F.eventually_exists_polyMin_lt S j q ha] with N hN
  obtain ⟨v, hv, h⟩ := hN
  exact (Metric.infDist_le_dist_of_mem hv).trans_lt (by rwa [dist_eq_norm])

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

/-- **Uniformly bounded smoothed cochain projections with vanishing harmonic gap** onto the
complexes of `S`, when the harmonic forms of `HΛ(Ω)` are finite-dimensional. -/
theorem polySmoothedProjection_uniform [∀ j, FiniteDimensional ℝ (D.complex.harmonic j)] :
    Parallelepiped.HasUniformProj D.complex (F.poly S) := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_polyProj S
  choose π hb hg using hK
  exact ⟨K, π, hK1, hb, hg, fun j => Subcomplex.CochainProjection.tendsto_harmonicGap π
    (zero_le_one.trans hK1) (fun N x => hb N j x) fun q _ => F.tendsto_infDist_poly S j q⟩

/-- **Uniform discrete Poincaré inequality** on the complexes of `S` ([AFW2010], Thm 3.6), under
the Poincaré inequality of `HΛ(Ω)`. -/
theorem discretePoincare_poly {cP : ℝ} (hP : HasPoincare D.complex cP) :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ D.Ω (formIdx n i)} (hx : x ∈ (F.poly S N).V i),
      (∀ y ∈ (F.poly S N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖D.complex.d i j ⟨x, (F.poly S N).le_domain i j hx⟩‖ := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_polyProj S
  refine ⟨K * cP, fun {i j} hij N x hx hxo => ?_⟩
  obtain ⟨π, hb, -⟩ := hK N
  exact π.norm_le_of_forall_inner_eq_zero hij (hP i j hij) (zero_le_one.trans hK1) (hb i) hx hxo

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian** on the
complexes of `S` ([AFW2010], Thm 3.8), under the Poincaré inequality of `HΛ(Ω)`. -/
theorem mixed_wellPosed_poly {cP : ℝ} (hP : HasPoincare D.complex cP) :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.poly S N).V j),
      (∃! x, (F.poly S N).toHilbertComplex.mixedForm i j k x =
        (F.poly S N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.poly S N).toHilbertComplex.MixedSpace i j,
        (F.poly S N).toHilbertComplex.mixedForm i j k x =
          (F.poly S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine (F.exists_uniform_polyProj S).elim fun K hK => ?_
  have hcP : 1 ≤ max 1 cP := le_max_left _ _
  have hP' := hP.mono (le_max_right 1 cP)
  refine ⟨16 * (K * max 1 cP) ^ 2, fun {i j k} hij hjk N f =>
    (hK.2 N).elim fun π hπ => ⟨?_, fun x hx => ?_⟩⟩
  · exact π.existsUnique_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) f
  · exact π.norm_le_of_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) hx

/-- **Quasi-optimality of the mixed method** on the complexes of `S` ([AFW2010], Thm 3.9) with
weights `μ_j(N) → 0`, under the Poincaré inequality and the finite-dimensionality of the harmonic
forms of `HΛ(Ω)`. -/
theorem mixed_quasiOptimal_poly {cP : ℝ} (hP : HasPoincare D.complex cP)
    [∀ j, FiniteDimensional ℝ (D.complex.harmonic j)] :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complex.domainSpace i} {u : D.complex.domainSpace j}
    {q : D.complex.harmonic j},
    D.complex.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
        ‖u - (F.poly S N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.poly S N) hij hjk f).snd.snd : (F.poly S N).V j) : L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.poly S N).domainSub i) +
        Metric.infDist u ((F.poly S N).domainSub j) +
        Metric.infDist (q : L2F ℝ D.Ω (formIdx n j)) ((F.poly S N).harmonicW j) +
        μ j N * Metric.infDist (D.complex.boundaryPart j (D.complex.domainIncl j u))
          ((F.poly S N).domainSub j)) :=
  Parallelepiped.mixed_quasiOptimal_of hP (F.polySmoothedProjection_uniform S)

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method for smooth solutions**
([AFW2010], Thm 3.9; [Arnold2018], Ch. 7), degreewise form, under the Poincaré inequality of
`HΛ(Ω)`: if `S` reproduces `P_s` in the degrees `i, i + 1, j, j + 1` (`FEM.PolyOrderAt`) and `σ`,
`u`, `P_𝔅 u` and the harmonic part `q` are `IsCsForm s` with bound `L` (`C^{s+2}` on `cl Ω`), the
error of the discrete solutions is `≤ K L h_N^{s+1}`, with `K` independent of `N`, of the solution
and of `L`. No finite-dimensionality of `ℌ` is needed. -/
theorem mixed_rate_poly_of_polyOrderAt {cP : ℝ} (hP : HasPoincare D.complex cP) {s : ℕ}
    {i j k : ℤ} (hSi : FEM.PolyOrderAt n S s i) (hSj : FEM.PolyOrderAt n S s j)
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
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_polyProj S
  choose π hπb hπg using hK
  refine ⟨(1 + 144 * (K * √(1 + cP ^ 2)) ^ 2) * (1 + K) *
    (2 * (F.polyInterpBound S i + F.polyInterpBound S j) * (3 + 2 * K)),
    fun hs L hL0 hσ hu hb hq N => ?_⟩
  have h := Parallelepiped.mixed_rate_of hP π hK1 hπg
    (Reg := fun l x => D.IsCsForm s l L x ∧ FEM.PolyOrderAt n S s l)
    (B := fun l => F.polyInterpBound S l * L)
    (fun l => mul_nonneg (F.polyInterpBound_nonneg S l) hL0)
    (r := fun N => (F.mesh N).meshSize ^ (s + 1))
    (fun N => pow_nonneg (F.meshSize_pos N).le _)
    (fun N l x hx => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_poly_le_of_isCsForm S hx.2 hx.1 hL0 N
      exact ⟨v, hv, h1, h2⟩) hij hjk hs ⟨hσ, hSi⟩ ⟨hu, hSj⟩ ⟨hb, hSj⟩ ⟨hq, hSj⟩ N
  refine h.trans (le_of_eq ?_)
  ring

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method for smooth solutions**
([AFW2010], Thm 3.9; [Arnold2018], Ch. 7), under the Poincaré inequality of `HΛ(Ω)`, for a
sequence of order `s` in every degree (`FEM.PolyOrder`, e.g. `s + 1 ≤ r_k`): error
`≤ K L h_N^{s+1}` for solutions of class `IsCsForm s`. -/
theorem mixed_rate_poly {cP : ℝ} (hP : HasPoincare D.complex cP) {s : ℕ}
    (hS : FEM.PolyOrder n S s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
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

/-- **Convergence of the semi-discrete Hodge wave equation** on every window of `HΛ(Ω)` for the
complexes of `S` ([QuennevilleBelair2015], Thm 4.14), with no hypothesis: the higher-order windows
approximate every point of the graph space (`eventually_exists_poly_near`). -/
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
  Parallelepiped.exists_tendstoUniformlyOn_window_of
    (fun i x _ hε => F.eventually_exists_poly_near S i x hε) a m t₀ t₁ x

/-- **Graph-norm rate in the total space of a window** for a sequence of order `s`: if every
component of `ζ ∈ Γ(𝐝)` is `IsCsForm s` with bound `L`, some point of the window of `Vₕ` is
within `(m + m²) (Σᵢ B_{a+i}) L h_N^{s+1}` of `ζ`. -/
theorem exists_mem_window_poly_le {s : ℕ} {a : ℤ} {m : ℕ}
    (hS : ∀ i : Fin m, FEM.PolyOrderAt n S s (a + i))
    (ζ : (D.complex.window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m, D.IsCsForm s (a + i) L ((D.complex.window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((F.poly S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, F.polyInterpBound S (a + i)) * L *
        (F.mesh N).meshSize ^ (s + 1) := by
  obtain ⟨x, rfl, -, -⟩ := (D.complex.window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hh := pow_nonneg (F.meshSize_pos N).le (s + 1)
  have hle : ∀ i : Fin m, F.polyInterpBound S (a + i) * L * (F.mesh N).meshSize ^ (s + 1) ≤
      (∑ i : Fin m, F.polyInterpBound S (a + i)) * L * (F.mesh N).meshSize ^ (s + 1) := fun i =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i : Fin m => F.polyInterpBound S (a + i))
        (fun _ _ => F.polyInterpBound_nonneg _ _) (Finset.mem_univ i)) hL0) hh
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((F.poly S N).window a m) x
    (ε := (∑ i : Fin m, F.polyInterpBound S (a + i)) * L * (F.mesh N).meshSize ^ (s + 1))
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_poly_le_of_isCsForm S (hS i) (hζ i) hL0 N
      exact ⟨v, hv, h1.trans (hle i), fun j hx => (h2 (a + j) hx).trans (hle i)⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]; ring

/-- **Convergence of order `h^{s+1}` of the semi-discrete Hodge wave equation** for the
complexes of `S` ([QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7), degreewise form, on
every window of `HΛ(Ω)`, with no hypothesis beyond the regularity of the solution: for a weak
solution `ξ` in `C¹([t₀, t₁]; Γ(𝐝))` whose values and time derivatives have `IsCsForm s`
components with bound `L`, and the semi-discrete solutions `ξₕ` started at the elliptic
projection, `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² (m + m²) (Σᵢ B_{a+i}) L h_N^{s+1}`. -/
theorem norm_sub_le_window_poly_smooth_of_polyOrderAt {s : ℕ} {a : ℤ}
    {m : ℕ} (hS : ∀ i : Fin m, FEM.PolyOrderAt n S s (a + i)) {t₀ t₁ : ℝ}
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

/-- The case of a sequence of order `s` in every degree (`FEM.PolyOrder`) of
`norm_sub_le_window_poly_smooth_of_polyOrderAt`. -/
theorem norm_sub_le_window_poly_smooth {s : ℕ} (hS : FEM.PolyOrder n S s) (a : ℤ)
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

/-! #### Vanishing boundary DOFs -/

/-- **Uniformly bounded smoothed cochain projections with vanishing harmonic gap** onto the
complexes of `S` with vanishing boundary DOFs, when the harmonic forms of `H̊Λ(Ω)` are
finite-dimensional. -/
theorem polySmoothedProjection_uniformMin
    [∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)] :
    Parallelepiped.HasUniformProj D.complexMin (F.polyMin S) := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_polyProjMin S
  choose π hb hg using hK
  exact ⟨K, π, hK1, hb, hg, fun j => Subcomplex.CochainProjection.tendsto_harmonicGap π
    (zero_le_one.trans hK1) (fun N x => hb N j x) fun q _ => F.tendsto_infDist_polyMin S j q⟩

/-- **Uniform discrete Poincaré inequality** on the complexes of `S` with vanishing boundary DOFs
([AFW2010], Thm 3.6), under the Poincaré inequality of `H̊Λ(Ω)`. -/
theorem discretePoincare_polyMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ D.Ω (formIdx n i)} (hx : x ∈ (F.polyMin S N).V i),
      (∀ y ∈ (F.polyMin S N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖D.complexMin.d i j ⟨x, (F.polyMin S N).le_domain i j hx⟩‖ := by
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_polyProjMin S
  refine ⟨K * cP, fun {i j} hij N x hx hxo => ?_⟩
  obtain ⟨π, hb, -⟩ := hK N
  exact π.norm_le_of_forall_inner_eq_zero hij (hP i j hij) (zero_le_one.trans hK1) (hb i) hx hxo

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian** on the
complexes of `S` with vanishing boundary DOFs ([AFW2010], Thm 3.8), under the Poincaré
inequality of `H̊Λ(Ω)`. -/
theorem mixed_wellPosed_polyMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.polyMin S N).V j),
      (∃! x, (F.polyMin S N).toHilbertComplex.mixedForm i j k x =
        (F.polyMin S N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.polyMin S N).toHilbertComplex.MixedSpace i j,
        (F.polyMin S N).toHilbertComplex.mixedForm i j k x =
          (F.polyMin S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine (F.exists_uniform_polyProjMin S).elim fun K hK => ?_
  have hcP : 1 ≤ max 1 cP := le_max_left _ _
  have hP' := hP.mono (le_max_right 1 cP)
  refine ⟨16 * (K * max 1 cP) ^ 2, fun {i j k} hij hjk N f =>
    (hK.2 N).elim fun π hπ => ⟨?_, fun x hx => ?_⟩⟩
  · exact π.existsUnique_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) f
  · exact π.norm_le_of_mixed hij hjk hcP hK.1 (hP' i j hij) (hP' j k hjk) (hπ.1 i) (hπ.1 j) hx

/-- **Quasi-optimality of the mixed method** on the complexes of `S` with vanishing boundary DOFs
([AFW2010], Thm 3.9), under the Poincaré inequality and the finite-dimensionality of the
harmonic forms of `H̊Λ(Ω)`. -/
theorem mixed_quasiOptimal_polyMin {cP : ℝ} (hP : HasPoincare D.complexMin cP)
    [∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)] :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ D.Ω (formIdx n j)} {σ : D.complexMin.domainSpace i}
    {u : D.complexMin.domainSpace j} {q : D.complexMin.harmonic j},
    D.complexMin.IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (F.polyMin S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk f).fst‖ +
        ‖u - (F.polyMin S N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk
            f).snd.fst‖ +
        ‖(q : L2F ℝ D.Ω (formIdx n j)) - (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.polyMin S N) hij hjk f).snd.snd : (F.polyMin S N).V j) :
            L2F ℝ D.Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.polyMin S N).domainSub i) +
        Metric.infDist u ((F.polyMin S N).domainSub j) +
        Metric.infDist (q : L2F ℝ D.Ω (formIdx n j)) ((F.polyMin S N).harmonicW j) +
        μ j N * Metric.infDist (D.complexMin.boundaryPart j (D.complexMin.domainIncl j u))
          ((F.polyMin S N).domainSub j)) :=
  Parallelepiped.mixed_quasiOptimal_of hP (F.polySmoothedProjection_uniformMin S)

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method with vanishing boundary
DOFs for smooth solutions**, degreewise form, under the Poincaré inequality of `H̊Λ(Ω)`, for
solutions of class `IsCsFormMin s` (`C^{s+2}`, vanishing outside `Ω`). -/
theorem mixed_rate_polyMin_of_polyOrderAt {cP : ℝ} (hP : HasPoincare D.complexMin cP) {s : ℕ}
    {i j k : ℤ} (hSi : FEM.PolyOrderAt n S s i) (hSj : FEM.PolyOrderAt n S s j)
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
  obtain ⟨K, hK1, hK⟩ := F.exists_uniform_polyProjMin S
  choose π hπb hπg using hK
  refine ⟨(1 + 144 * (K * √(1 + cP ^ 2)) ^ 2) * (1 + K) *
    (2 * (F.polyInterpBound S i + F.polyInterpBound S j) * (3 + 2 * K)),
    fun hs L hL0 hσ hu hb hq N => ?_⟩
  have h := Parallelepiped.mixed_rate_of hP π hK1 hπg
    (Reg := fun l x => D.IsCsFormMin s l L x ∧ FEM.PolyOrderAt n S s l)
    (B := fun l => F.polyInterpBound S l * L)
    (fun l => mul_nonneg (F.polyInterpBound_nonneg S l) hL0)
    (r := fun N => (F.mesh N).meshSize ^ (s + 1))
    (fun N => pow_nonneg (F.meshSize_pos N).le _)
    (fun N l x hx => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_polyMin_le_of_isCsFormMin S hx.2 hx.1 hL0 N
      exact ⟨v, hv, h1, h2⟩) hij hjk hs ⟨hσ, hSi⟩ ⟨hu, hSj⟩ ⟨hb, hSj⟩ ⟨hq, hSj⟩ N
  refine h.trans (le_of_eq ?_)
  ring

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method with vanishing boundary
DOFs** for a sequence of order `s` in every degree. -/
theorem mixed_rate_polyMin {cP : ℝ} (hP : HasPoincare D.complexMin cP) {s : ℕ}
    (hS : FEM.PolyOrder n S s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
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

/-- **Convergence of the semi-discrete Hodge wave equation** on every window of `H̊Λ(Ω)` for the
complexes of `S` with vanishing boundary DOFs, with no hypothesis. -/
theorem exists_tendstoUniformlyOn_windowMin_poly (a : ℤ) (m : ℕ) (t₀ t₁ : ℝ)
    (x : (D.complexMin.window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → (D.complexMin.window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((F.polyMin S N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((F.polyMin S N).window a m).graphSub)
        ((D.complexMin.window a m).totalD.toGraphSpace
          ⟨x, ((D.complexMin.window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => (D.complexMin.window a m).totalD.graphFst (ξh N t))
        (fun t => (D.complexMin.window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  Parallelepiped.exists_tendstoUniformlyOn_window_of
    (fun i x _ hε => F.eventually_exists_polyMin_near S i x hε) a m t₀ t₁ x

/-- **Graph-norm rate in the total space of a window of `H̊Λ(Ω)`** for a sequence of order
`s`. -/
theorem exists_mem_windowMin_poly_le {s : ℕ} {a : ℤ} {m : ℕ}
    (hS : ∀ i : Fin m, FEM.PolyOrderAt n S s (a + i))
    (ζ : (D.complexMin.window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m,
      D.IsCsFormMin s (a + i) L ((D.complexMin.window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((F.polyMin S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, F.polyInterpBound S (a + i)) * L *
        (F.mesh N).meshSize ^ (s + 1) := by
  obtain ⟨x, rfl, -, -⟩ := (D.complexMin.window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hh := pow_nonneg (F.meshSize_pos N).le (s + 1)
  have hle : ∀ i : Fin m, F.polyInterpBound S (a + i) * L * (F.mesh N).meshSize ^ (s + 1) ≤
      (∑ i : Fin m, F.polyInterpBound S (a + i)) * L * (F.mesh N).meshSize ^ (s + 1) := fun i =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i : Fin m => F.polyInterpBound S (a + i))
        (fun _ _ => F.polyInterpBound_nonneg _ _) (Finset.mem_univ i)) hL0) hh
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((F.polyMin S N).window a m) x
    (ε := (∑ i : Fin m, F.polyInterpBound S (a + i)) * L * (F.mesh N).meshSize ^ (s + 1))
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_polyMin_le_of_isCsFormMin S (hS i) (hζ i) hL0 N
      exact ⟨v, hv, h1.trans (hle i), fun j hx => (h2 (a + j) hx).trans (hle i)⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]; ring

/-- **Convergence of order `h^{s+1}` of the semi-discrete Hodge wave equation with vanishing
boundary DOFs** for the complexes of `S`, degreewise form, on every window of `H̊Λ(Ω)`. -/
theorem norm_sub_le_windowMin_poly_smooth_of_polyOrderAt {s : ℕ} {a : ℤ}
    {m : ℕ} (hS : ∀ i : Fin m, FEM.PolyOrderAt n S s (a + i)) {t₀ t₁ : ℝ}
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

/-! ### Parallelepipeds: every quasi-uniform shape-regular mesh family, with no hypothesis -/

namespace Parallelepiped

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- **The Poincaré inequality of `HΛ(Ω)` on the parallelepiped** `Ω = A · Q + b`, with
`c_P(A) = Feec.Models.Parallelepiped.poincareConst A`
(`Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles`, by affine transport from the
cube). -/
theorem hasPoincare : HasPoincare (ParallelepipedWitness.starDomain A hA b).complex
    (Feec.Models.Parallelepiped.poincareConst A) := fun _ _ hij z hz =>
  (Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles A hA b hij z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- **The Poincaré inequality of `H̊Λ(Ω)` on the parallelepiped**
(`Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles_min`). -/
theorem hasPoincareMin : HasPoincare (ParallelepipedWitness.starDomain A hA b).complexMin
    (Feec.Models.Parallelepiped.poincareConst A) := fun _ _ hij z hz =>
  (Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles_min A hA b hij z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

instance (j : ℤ) :
    FiniteDimensional ℝ ((ParallelepipedWitness.starDomain A hA b).complex.harmonic j) :=
  Feec.Models.Parallelepiped.finiteDimensional_harmonic A hA b j

instance (j : ℤ) :
    FiniteDimensional ℝ ((ParallelepipedWitness.starDomain A hA b).complexMin.harmonic j) :=
  Feec.Models.Parallelepiped.finiteDimensional_harmonic_min A hA b j

variable [NeZero n] (F : MeshFamily (ParallelepipedWitness.starDomain A hA b)) (S : PolySeq)

/-- **Uniform discrete Poincaré inequality on the higher-order complexes of every quasi-uniform
shape-regular mesh family of a parallelepiped** ([AFW2010], Thm 3.6), with no hypothesis. -/
theorem discretePoincare_poly_general :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n i)}
      (hx : x ∈ (F.poly S N).V i),
      (∀ y ∈ (F.poly S N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖(ParallelepipedWitness.starDomain A hA b).complex.d i j
          ⟨x, (F.poly S N).le_domain i j hx⟩‖ :=
  F.discretePoincare_poly S (hasPoincare A hA b)

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian on the
higher-order complexes of every quasi-uniform shape-regular mesh family of a parallelepiped**
([AFW2010], Thm 3.8), with no hypothesis. -/
theorem mixed_wellPosed_poly_general :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.poly S N).V j),
      (∃! x, (F.poly S N).toHilbertComplex.mixedForm i j k x =
        (F.poly S N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.poly S N).toHilbertComplex.MixedSpace i j,
        (F.poly S N).toHilbertComplex.mixedForm i j k x =
          (F.poly S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ :=
  F.mixed_wellPosed_poly S (hasPoincare A hA b)

/-- **Quasi-optimality of the higher-order mixed method on every quasi-uniform shape-regular mesh
family of a parallelepiped** ([AFW2010], Thm 3.9), with no hypothesis. -/
theorem mixed_quasiOptimal_poly_general :
    ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace i}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace j}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic j},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution i j k f σ u q →
    ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
        ‖u - (F.poly S N).embD j
          (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution
            (F.poly S N) hij hjk f).snd.snd : (F.poly S N).V j) :
              L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((F.poly S N).domainSub i) +
        Metric.infDist u ((F.poly S N).domainSub j) +
        Metric.infDist (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))
          ((F.poly S N).harmonicW j) +
        μ j N * Metric.infDist ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart j
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u))
          ((F.poly S N).domainSub j)) :=
  F.mixed_quasiOptimal_poly S (hasPoincare A hA b)

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method on every quasi-uniform
shape-regular mesh family of a parallelepiped** ([AFW2010], Thm 3.9; [Arnold2018], Ch. 7),
degreewise form, with no hypothesis beyond the regularity of the solution (`IsCsForm s`). -/
theorem mixed_rate_poly_general_of_polyOrderAt {s : ℕ} {i j k : ℤ}
    (hSi : FEM.PolyOrderAt n S s i) (hSj : FEM.PolyOrderAt n S s j)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace i}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace j}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic j},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution i j k f σ u q →
    ∀ {L : ℝ}, 0 ≤ L →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s i L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl i σ) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j
        ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart j
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u))) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
      ‖u - (F.poly S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.snd :
          (F.poly S N).V j) : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) :=
  F.mixed_rate_poly_of_polyOrderAt S (hasPoincare A hA b) hSi hSj hij hjk

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method on every quasi-uniform
shape-regular mesh family of every parallelepiped `A · Q + b`** (not only the image Freudenthal
meshes; [AFW2010], Thm 3.9; [Arnold2018], Ch. 7), for a sequence of order `s` and solutions of
class `IsCsForm s`, with **no hypothesis**: the Poincaré inequality of `HΛ(Ω)` is discharged by
`Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles` (`hasPoincare`). -/
theorem mixed_rate_poly_general {s : ℕ} (hS : FEM.PolyOrder n S s) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace i}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace j}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic j},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution i j k f σ u q →
    ∀ {L : ℝ}, 0 ≤ L →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s i L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl i σ) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j
        ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart j
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u))) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm s j L
      (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.poly S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).fst‖ +
      ‖u - (F.poly S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution (F.poly S N) hij hjk f).snd.snd :
          (F.poly S N).V j) : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) :=
  F.mixed_rate_poly S (hasPoincare A hA b) hS hij hjk

/-- **Uniform discrete Poincaré inequality with vanishing boundary DOFs** on every
quasi-uniform shape-regular mesh family of a parallelepiped, with no hypothesis. -/
theorem discretePoincare_polyMin_general :
    ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
      {x : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n i)}
      (hx : x ∈ (F.polyMin S N).V i),
      (∀ y ∈ (F.polyMin S N).cyclesW i, inner ℝ y x = 0) →
        ‖x‖ ≤ c * ‖(ParallelepipedWitness.starDomain A hA b).complexMin.d i j
          ⟨x, (F.polyMin S N).le_domain i j hx⟩‖ :=
  F.discretePoincare_polyMin S (hasPoincareMin A hA b)

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian with vanishing
boundary DOFs** on every quasi-uniform shape-regular mesh family of a parallelepiped. -/
theorem mixed_wellPosed_polyMin_general :
    ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      ∀ (N : ℕ) (f : (F.polyMin S N).V j),
      (∃! x, (F.polyMin S N).toHilbertComplex.mixedForm i j k x =
        (F.polyMin S N).toHilbertComplex.mixedRHS i j f) ∧
      ∀ x : (F.polyMin S N).toHilbertComplex.MixedSpace i j,
        (F.polyMin S N).toHilbertComplex.mixedForm i j k x =
          (F.polyMin S N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ :=
  F.mixed_wellPosed_polyMin S (hasPoincareMin A hA b)

/-- **Convergence of order `h^{s+1}` of the higher-order mixed method with vanishing boundary
DOFs on every quasi-uniform shape-regular mesh family of a parallelepiped**, for a sequence of
order `s` and solutions of class `IsCsFormMin s`, with no hypothesis. -/
theorem mixed_rate_polyMin_general {s : ℕ} (hS : FEM.PolyOrder n S s) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complexMin.domainSpace i}
    {u : (ParallelepipedWitness.starDomain A hA b).complexMin.domainSpace j}
    {q : (ParallelepipedWitness.starDomain A hA b).complexMin.harmonic j},
    (ParallelepipedWitness.starDomain A hA b).complexMin.IsMixedSolution i j k f σ u q →
    ∀ {L : ℝ}, 0 ≤ L →
    (ParallelepipedWitness.starDomain A hA b).IsCsFormMin s i L
      ((ParallelepipedWitness.starDomain A hA b).complexMin.domainIncl i σ) →
    (ParallelepipedWitness.starDomain A hA b).IsCsFormMin s j L
      ((ParallelepipedWitness.starDomain A hA b).complexMin.domainIncl j u) →
    (ParallelepipedWitness.starDomain A hA b).IsCsFormMin s j L
      ((ParallelepipedWitness.starDomain A hA b).complexMin.domainIncl j
        ((ParallelepipedWitness.starDomain A hA b).complexMin.boundaryPart j
          ((ParallelepipedWitness.starDomain A hA b).complexMin.domainIncl j u))) →
    (ParallelepipedWitness.starDomain A hA b).IsCsFormMin s j L
      (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.polyMin S N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk f).fst‖ +
      ‖u - (F.polyMin S N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution (F.polyMin S N) hij hjk
          f).snd.snd : (F.polyMin S N).V j) :
            L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (s + 1) :=
  F.mixed_rate_polyMin S (hasPoincareMin A hA b) hS hij hjk

/-- **Second-order convergence of the bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` of Tables 5.1/6.1
for the Hodge Laplacian on `1`-forms** on every quasi-uniform shape-regular mesh family of a
parallelepiped (the problem in degree `1` only uses `P₂Λ⁰, P₂⁻Λ¹, P₁Λ²`, which contain `P₁`):
error `≤ K L h_N²` for `C³` solutions, with no hypothesis. -/
theorem mixed_rate_lagrangeP2_general :
    ∃ K : ℝ, ∀ {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n 1)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace 0}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace 1}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic 1},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution 0 1 2 f σ u q →
    ∀ {L : ℝ}, 0 ≤ L →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 0 L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl 0 σ) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 1 L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl 1 u) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 1 L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl 1
        ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart 1
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl 1 u))) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 1 L
      (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - (F.poly PolySeq.lagrangeP2 N).embD 0
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly PolySeq.lagrangeP2 N)
          (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
      ‖u - (F.poly PolySeq.lagrangeP2 N).embD 1
        (Subcomplex.CochainProjection.discreteMixedSolution (F.poly PolySeq.lagrangeP2 N)
          (i := 0) (j := 1) (k := 2) rfl rfl f).snd.fst‖ +
      ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n 1)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution (F.poly PolySeq.lagrangeP2 N)
          (i := 0) (j := 1) (k := 2) rfl rfl f).snd.snd : (F.poly PolySeq.lagrangeP2 N).V 1) :
            L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n 1))‖ ≤
      K * L * (F.mesh N).meshSize ^ (1 + 1) :=
  F.mixed_rate_poly_of_polyOrderAt PolySeq.lagrangeP2 (hasPoincare A hA b)
    FEM.lagrangeP2_polyOrderAt_zero FEM.lagrangeP2_polyOrderAt_one rfl rfl

/-- **Convergence of order `h²` of the trimmed sequence `P₂⁻Λ⁰ → ⋯ → P₂⁻Λⁿ`** (order `1`,
`FEM.polyOrder_trimmed`) for the mixed Hodge Laplacian in every degree, on every quasi-uniform
shape-regular mesh family of a parallelepiped, with no hypothesis. -/
theorem mixed_rate_trimmed₂_general {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)}
    {σ : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace i}
    {u : (ParallelepipedWitness.starDomain A hA b).complex.domainSpace j}
    {q : (ParallelepipedWitness.starDomain A hA b).complex.harmonic j},
    (ParallelepipedWitness.starDomain A hA b).complex.IsMixedSolution i j k f σ u q →
    ∀ {L : ℝ}, 0 ≤ L →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 i L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl i σ) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 j L
      ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j
        ((ParallelepipedWitness.starDomain A hA b).complex.boundaryPart j
          ((ParallelepipedWitness.starDomain A hA b).complex.domainIncl j u))) →
    (ParallelepipedWitness.starDomain A hA b).IsCsForm 1 j L
      (q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (F.poly (PolySeq.trimmed 2 (by norm_num)) N).embD i
        (Subcomplex.CochainProjection.discreteMixedSolution
          (F.poly (PolySeq.trimmed 2 (by norm_num)) N) hij hjk f).fst‖ +
      ‖u - (F.poly (PolySeq.trimmed 2 (by norm_num)) N).embD j
        (Subcomplex.CochainProjection.discreteMixedSolution
          (F.poly (PolySeq.trimmed 2 (by norm_num)) N) hij hjk f).snd.fst‖ +
      ‖(q : L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution
          (F.poly (PolySeq.trimmed 2 (by norm_num)) N) hij hjk f).snd.snd :
            (F.poly (PolySeq.trimmed 2 (by norm_num)) N).V j) :
              L2F ℝ (ParallelepipedWitness.starDomain A hA b).Ω (formIdx n j))‖ ≤
      K * L * (F.mesh N).meshSize ^ (1 + 1) :=
  F.mixed_rate_poly (PolySeq.trimmed 2 (by norm_num)) (hasPoincare A hA b)
    (FEM.polyOrder_trimmed (n := n) (r := 2) (by norm_num)) hij hjk

end Parallelepiped

/-! ### Non-vacuity: the cube and the parallelepipeds -/

namespace CubeWitness

variable (n) [NeZero n]

/-- **Second-order convergence of the bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` on the Freudenthal
meshes of the cube, as a mesh family of a star-shaped domain** (`CubeWitness.meshFamily`): the
star-shaped theory instantiated, with the Poincaré inequality `CubeWitness.hasPoincare`. -/
theorem mixed_rate_lagrangeP2 :
    ∃ K : ℝ, ∀ {f : L2F ℝ (starDomain n).Ω (formIdx n 1)}
    {σ : (starDomain n).complex.domainSpace 0} {u : (starDomain n).complex.domainSpace 1}
    {q : (starDomain n).complex.harmonic 1},
    (starDomain n).complex.IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    (starDomain n).IsCsForm 1 0 L ((starDomain n).complex.domainIncl 0 σ) →
    (starDomain n).IsCsForm 1 1 L ((starDomain n).complex.domainIncl 1 u) →
    (starDomain n).IsCsForm 1 1 L ((starDomain n).complex.domainIncl 1
      ((starDomain n).complex.boundaryPart 1 ((starDomain n).complex.domainIncl 1 u))) →
    (starDomain n).IsCsForm 1 1 L (q : L2F ℝ (starDomain n).Ω (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - ((meshFamily n).poly PolySeq.lagrangeP2 N).embD 0
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
      ‖u - ((meshFamily n).poly PolySeq.lagrangeP2 N).embD 1
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.fst‖ +
      ‖(q : L2F ℝ (starDomain n).Ω (formIdx n 1)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.snd : ((meshFamily n).poly PolySeq.lagrangeP2 N).V 1) :
              L2F ℝ (starDomain n).Ω (formIdx n 1))‖ ≤
      K * L * ((meshFamily n).mesh N).meshSize ^ (1 + 1) :=
  (meshFamily n).mixed_rate_poly_of_polyOrderAt PolySeq.lagrangeP2 (hasPoincare n)
    FEM.lagrangeP2_polyOrderAt_zero FEM.lagrangeP2_polyOrderAt_one rfl rfl

/-- **The hypotheses of the higher-order theorems on star-shaped domains are satisfiable**: the
cube with its Freudenthal meshes is a star-shaped domain with a quasi-uniform shape-regular mesh
family whose complexes satisfy the Poincaré inequality, the bottom row reproduces `P₁` in the
degrees `0, 1, 2`, the trimmed sequence `P₂⁻Λ` has order `1`, and every `C³` form is of class
`IsCsForm 1`. -/
theorem nonvacuous_poly : ∃ (D : StarDomain n) (_ : MeshFamily D),
    HasPoincare D.complex 1 ∧ HasPoincare D.complexMin 1 ∧
    (∀ j, FiniteDimensional ℝ (D.complex.harmonic j)) ∧
    (∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)) ∧
    FEM.PolyOrderAt n PolySeq.lagrangeP2 1 0 ∧ FEM.PolyOrderAt n PolySeq.lagrangeP2 1 1 ∧
    FEM.PolyOrder n (PolySeq.trimmed 2 (by norm_num)) 1 ∧
    ∀ {k : ℕ} {w : FormField n} (hw : ContDiff ℝ ((1 + 2 : ℕ) : WithTop ℕ∞) w),
      (∀ y, IsDeg k (w y)) → ∃ L, 0 ≤ L ∧ D.IsCsForm 1 (k : ℤ) L
        (formL2 D.isOpen.measurableSet D.isBounded k ⟨w, hw.continuous⟩) := by
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
  exact ⟨starDomain n, meshFamily n, (hasPoincare n).mono hpi, (hasPoincareMin n).mono hpi,
    fun j => inferInstance, fun j => inferInstance, FEM.lagrangeP2_polyOrderAt_zero,
    FEM.lagrangeP2_polyOrderAt_one, FEM.polyOrder_trimmed (n := n) (r := 2) (by norm_num),
    fun hw hdeg => (starDomain n).exists_isCsForm 1 hw hdeg⟩

end CubeWitness

namespace ParallelepipedWitness

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ) [NeZero n]

/-- **Second-order convergence of the bottom row on the image Freudenthal meshes of a
parallelepiped**, as an instance of `Parallelepiped.mixed_rate_lagrangeP2_general` for the mesh
family `ParallelepipedWitness.meshFamily`. -/
theorem mixed_rate_lagrangeP2 :
    ∃ K : ℝ, ∀ {f : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)}
    {σ : (starDomain A hA b).complex.domainSpace 0}
    {u : (starDomain A hA b).complex.domainSpace 1}
    {q : (starDomain A hA b).complex.harmonic 1},
    (starDomain A hA b).complex.IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    (starDomain A hA b).IsCsForm 1 0 L ((starDomain A hA b).complex.domainIncl 0 σ) →
    (starDomain A hA b).IsCsForm 1 1 L ((starDomain A hA b).complex.domainIncl 1 u) →
    (starDomain A hA b).IsCsForm 1 1 L ((starDomain A hA b).complex.domainIncl 1
      ((starDomain A hA b).complex.boundaryPart 1
        ((starDomain A hA b).complex.domainIncl 1 u))) →
    (starDomain A hA b).IsCsForm 1 1 L
      (q : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - ((meshFamily A hA b).poly PolySeq.lagrangeP2 N).embD 0
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).fst‖ +
      ‖u - ((meshFamily A hA b).poly PolySeq.lagrangeP2 N).embD 1
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.fst‖ +
      ‖(q : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.snd : ((meshFamily A hA b).poly PolySeq.lagrangeP2 N).V 1) :
              L2F ℝ (starDomain A hA b).Ω (formIdx n 1))‖ ≤
      K * L * ((meshFamily A hA b).mesh N).meshSize ^ (1 + 1) :=
  Parallelepiped.mixed_rate_lagrangeP2_general A hA b (meshFamily A hA b)

/-- **Non-vacuity on parallelepipeds**: every parallelepiped `A · Q + b` carries a quasi-uniform
shape-regular mesh family (its image Freudenthal meshes), on which the higher-order theorems hold
with no hypothesis (`Parallelepiped.hasPoincare`, `Parallelepiped.hasPoincareMin`), the bottom row
reproduces `P₁` in the degrees `0, 1, 2` and `P₂⁻Λ` has order `1`. -/
theorem nonvacuous_poly : ∃ (D : StarDomain n) (F : MeshFamily D),
    D.Ω = Feec.Models.Parallelepiped.domain A b ∧
    (∀ N, F.mesh N = Feec.Models.Parallelepiped.mesh A hA b N) ∧
    HasPoincare D.complex (Feec.Models.Parallelepiped.poincareConst A) ∧
    HasPoincare D.complexMin (Feec.Models.Parallelepiped.poincareConst A) ∧
    (∀ j, FiniteDimensional ℝ (D.complex.harmonic j)) ∧
    (∀ j, FiniteDimensional ℝ (D.complexMin.harmonic j)) ∧
    FEM.PolyOrderAt n PolySeq.lagrangeP2 1 0 ∧ FEM.PolyOrderAt n PolySeq.lagrangeP2 1 1 ∧
    FEM.PolyOrder n (PolySeq.trimmed 2 (by norm_num)) 1 :=
  ⟨starDomain A hA b, meshFamily A hA b, rfl, fun _ => rfl, Parallelepiped.hasPoincare A hA b,
    Parallelepiped.hasPoincareMin A hA b, fun j => inferInstance, fun j => inferInstance,
    FEM.lagrangeP2_polyOrderAt_zero, FEM.lagrangeP2_polyOrderAt_one,
    FEM.polyOrder_trimmed (n := n) (r := 2) (by norm_num)⟩

end ParallelepipedWitness

/-! ### Non-vacuity beyond the zero solution and beyond the Freudenthal meshes -/

namespace StarDomain
variable (D : StarDomain n)

theorem IsCsForm.mono {D : StarDomain n} {s : ℕ} {j : ℤ} {L L' : ℝ}
    {x : L2F ℝ D.Ω (formIdx n j)} (hx : D.IsCsForm s j L x) (hLL : L ≤ L') :
    D.IsCsForm s j L' x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, hL, hL', he⟩
  · exact Or.inl hj
  · exact Or.inr ⟨k, hk, w, hw, hdeg, fun y hy => (hL y hy).trans hLL,
      fun y hy => (hL' y hy).trans hLL, he⟩

theorem isCsForm_zero (s : ℕ) (j : ℤ) {L : ℝ} (hL : 0 ≤ L) : D.IsCsForm s j L 0 := by
  rcases lt_or_ge j 0 with hj | hj
  · exact Or.inl hj
  · refine Or.inr ⟨j.toNat, Int.toNat_of_nonneg hj, 0, contDiff_const, fun y s _ => rfl,
      fun y _ => ?_, fun y _ => ?_, ?_⟩
    · simp [iteratedFDeriv_zero, hL]
    · have : extDeriv (0 : FormField n) = 0 := by
        funext y t; simp [extDeriv]
      rw [this]; simp [iteratedFDeriv_zero, hL]
    · exact (map_zero (formL2 D.isOpen.measurableSet D.isBounded j)).symm

/-- A harmonic datum is solved by `σ = 0`, `u = 0`, `p = f`. -/
theorem isMixedSolution_harmonic (i j k : ℤ) (p : D.complex.harmonic j) :
    D.complex.IsMixedSolution i j k (p : L2F ℝ D.Ω (formIdx n j)) 0 0 p :=
  ⟨fun τ => by simp, fun v => by simp, fun q _ => by simp⟩

end StarDomain

namespace CubeWitness
variable (n)

/-- The constant `0`-form `1` on the cube as a harmonic form of `HΛ(Q)`. -/
def oneHarmonic : (starDomain n).complex.harmonic 0 :=
  ⟨FEM.oneForm n, by
    change FEM.oneForm n ∈ (FEM.complex n).harmonic 0
    rw [FEM.harmonic_zero_eq_span]; exact Submodule.mem_span_singleton_self _⟩

theorem oneHarmonic_ne_zero : oneHarmonic n ≠ 0 := fun h =>
  FEM.oneForm_ne_zero (congrArg Subtype.val h)

/-- The constant field `1` of degree `0`. -/
def oneField : FormField n := fun _ => Pi.single ∅ 1

theorem contDiff_oneField {m : WithTop ℕ∞} : ContDiff ℝ m (oneField n) := contDiff_const

theorem isDeg_oneField (y : Fin n → ℝ) : IsDeg 0 (oneField n y) := fun s hs => by
  simp only [oneField, Pi.single_apply]
  exact ite_eq_right_iff.2 fun h => absurd (by rw [h]; rfl) hs

theorem formL2_oneField :
    formL2 (starDomain n).isOpen.measurableSet (starDomain n).isBounded 0
      ⟨oneField n, (contDiff_oneField n (m := 0)).continuous⟩ =
      ((oneHarmonic n : (starDomain n).complex.harmonic 0) :
        L2F ℝ (starDomain n).Ω (formIdx n 0)) := by
  refine PiLp.ext fun s => ?_
  change MemLp.toLp _ (Feec.Domain.memLp_of_continuous (starDomain n).isOpen.measurableSet
      (starDomain n).isBounded (continuous_formComp (k := 0)
        (contDiff_oneField n (m := 0)).continuous s)) =
    MemLp.toLp _ (DeRhamIdent.memLp_constFun (starDomain n).isOpen.measurableSet
      (starDomain n).isBounded _ s)
  apply MemLp.toLp_congr
  refine Eventually.of_forall fun y => ?_
  simp only [formComp, oneField, Pi.single_apply, DeRhamIdent.constFun]
  congr 1
  exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem rel_neg_one_zero : (ComplexShape.up ℤ).Rel (-1) 0 := by simp

theorem lagrangeP2_polyOrderAt_neg_one : FEM.PolyOrderAt n PolySeq.lagrangeP2 1 (-1) :=
  fun k hk => absurd hk (by omega)

/-- **A non-zero smooth mixed solution on the cube**: the datum `f = 1 ∈ ℌ⁰(HΛ(Q))` (the constant
`0`-form) is solved by `σ = 0`, `u = 0`, `p = 1 ≠ 0` (degrees `-1, 0, 1`, the Neumann problem), and
all four fields are of class `IsCsForm s` for one bound `L`. -/
theorem exists_mixedSolution_ne_zero (s : ℕ) : ∃ L, 0 ≤ L ∧
    (starDomain n).complex.IsMixedSolution (-1) 0 1
      ((oneHarmonic n : (starDomain n).complex.harmonic 0) :
        L2F ℝ (starDomain n).Ω (formIdx n 0)) 0 0 (oneHarmonic n) ∧
    oneHarmonic n ≠ 0 ∧
    (starDomain n).IsCsForm s (-1) L ((starDomain n).complex.domainIncl (-1) 0) ∧
    (starDomain n).IsCsForm s 0 L ((starDomain n).complex.domainIncl 0 0) ∧
    (starDomain n).IsCsForm s 0 L ((starDomain n).complex.domainIncl 0
      ((starDomain n).complex.boundaryPart 0 ((starDomain n).complex.domainIncl 0 0))) ∧
    (starDomain n).IsCsForm s 0 L
      ((oneHarmonic n : (starDomain n).complex.harmonic 0) :
        L2F ℝ (starDomain n).Ω (formIdx n 0)) := by
  obtain ⟨L, hL0, hL⟩ := (starDomain n).exists_isCsForm s (k := 0)
    (contDiff_oneField n) (isDeg_oneField n)
  refine ⟨L, hL0, (starDomain n).isMixedSolution_harmonic _ _ _ _, oneHarmonic_ne_zero n,
    Or.inl (by norm_num), ?_, ?_, ?_⟩
  · rw [map_zero]; exact (starDomain n).isCsForm_zero s 0 hL0
  · simp only [map_zero, boundaryPart, domainIncl_cyclesToDomainSpace]
    exact (starDomain n).isCsForm_zero s 0 hL0
  · rw [← formL2_oneField]; exact hL

variable [NeZero n]

/-- **Second-order convergence for a non-zero smooth solution** (non-vacuity of
`MeshFamily.mixed_rate_poly_of_polyOrderAt` beyond the zero solution): for the harmonic datum
`f = 1` on the cube, the discrete solutions of the bottom row `P₂Λ⁰ → …` on the Freudenthal meshes
satisfy `‖σ - σ_h‖ + ‖u - u_h‖ + ‖p - p_h‖ ≤ K L h_N²` with `p = 1 ≠ 0`. -/
theorem mixed_rate_lagrangeP2_ne_zero : ∃ K L : ℝ, 0 ≤ L ∧ oneHarmonic n ≠ 0 ∧ ∀ N : ℕ,
    ‖(0 : (starDomain n).complex.domainSpace (-1)) -
        ((meshFamily n).poly PolySeq.lagrangeP2 N).embD (-1)
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (rel_neg_one_zero) (j := 0) (k := 1) rfl
          ((oneHarmonic n : (starDomain n).complex.harmonic 0) :
            L2F ℝ (starDomain n).Ω (formIdx n 0))).fst‖ +
      ‖(0 : (starDomain n).complex.domainSpace 0) -
        ((meshFamily n).poly PolySeq.lagrangeP2 N).embD 0
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (rel_neg_one_zero) (j := 0) (k := 1) rfl
          ((oneHarmonic n : (starDomain n).complex.harmonic 0) :
            L2F ℝ (starDomain n).Ω (formIdx n 0))).snd.fst‖ +
      ‖((oneHarmonic n : (starDomain n).complex.harmonic 0) :
          L2F ℝ (starDomain n).Ω (formIdx n 0)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution
          ((meshFamily n).poly PolySeq.lagrangeP2 N) (rel_neg_one_zero) (j := 0) (k := 1) rfl
          ((oneHarmonic n : (starDomain n).complex.harmonic 0) :
            L2F ℝ (starDomain n).Ω (formIdx n 0))).snd.snd :
            ((meshFamily n).poly PolySeq.lagrangeP2 N).V 0) :
          L2F ℝ (starDomain n).Ω (formIdx n 0))‖ ≤
      K * L * ((meshFamily n).mesh N).meshSize ^ (1 + 1) := by
  obtain ⟨K, hK⟩ := (meshFamily n).mixed_rate_poly_of_polyOrderAt PolySeq.lagrangeP2
    (hasPoincare n) (lagrangeP2_polyOrderAt_neg_one n) FEM.lagrangeP2_polyOrderAt_zero
    (rel_neg_one_zero) (show (ComplexShape.up ℤ).Rel 0 1 from rfl)
  obtain ⟨L, hL0, hs, hne, h1, h2, h3, h4⟩ := exists_mixedSolution_ne_zero n 1
  exact ⟨K, L, hL0, hne, hK hs hL0 h1 h2 h3 h4⟩

end CubeWitness

namespace MeshFamily

/-- A mesh family of `D` as a mesh family of any `D'` with the same domain. -/
def congrDomain {D : StarDomain n} (F : MeshFamily D) (D' : StarDomain n) (h : D'.Ω = D.Ω) :
    MeshFamily D' where
  mesh := F.mesh
  C := F.C
  c := F.c
  q := F.q
  C_nonneg := F.C_nonneg
  c_pos := F.c_pos
  q_pos := F.q_pos
  domain_eq N := (F.domain_eq N).trans h.symm
  data := F.data
  tendsto_meshSize := F.tendsto_meshSize

end MeshFamily

namespace CubeWitness

variable (n) [NeZero n]

/-- The sign `-1` on the first coordinate, `1` on the others. -/
def reflectUnit (i : Fin n) : ℝˣ := if i = 0 then -1 else 1

/-- The reflection `x₀ ↦ ½ - x₀` of the first coordinate, a symmetry of `Q = (0, ½)ⁿ`. -/
def reflect : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) :=
  (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (reflectUnit n i)).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (Fin n → ℝ) (Pi.single 0 (1 / 2)))

theorem reflect_apply (x : Fin n → ℝ) (i : Fin n) :
    reflect n x i = if i = 0 then 1 / 2 - x i else x i := by
  by_cases h : i = 0
  · subst h
    simp [reflect, reflectUnit, LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv,
      Units.smul_def]; ring
  · simp [reflect, reflectUnit, h, LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv]

theorem reflect_reflect (x : Fin n → ℝ) : reflect n (reflect n x) = x := by
  funext i; rw [reflect_apply, reflect_apply]; split_ifs <;> ring

theorem reflect_mem_cubeDomain {x : Fin n → ℝ} (hx : x ∈ FEM.cubeDomain n) :
    reflect n x ∈ FEM.cubeDomain n := by
  simp only [FEM.cubeDomain, Set.mem_univ_pi, Set.mem_Ioo] at hx ⊢
  intro i; rw [reflect_apply]; have := hx i
  split_ifs <;> constructor <;> linarith [this.1, this.2]

theorem cubeDomain_eq_image_reflect : FEM.cubeDomain n = reflect n '' FEM.cubeDomain n := by
  ext x
  exact ⟨fun hx => ⟨reflect n x, reflect_mem_cubeDomain n hx, reflect_reflect n x⟩,
    fun ⟨y, hy, e⟩ => e ▸ reflect_mem_cubeDomain n hy⟩

/-- **The reflected Freudenthal meshes of the cube**: the images of the Freudenthal meshes under
`x₀ ↦ ½ - x₀`, whose simplices have their long diagonal along `(-1, 1, …, 1)`; a quasi-uniform
shape-regular mesh family of `Q` other than `CubeWitness.meshFamily` (for `n ≥ 2`,
`exists_reflected_simplex`). -/
def reflectedFamily : MeshFamily (starDomain n) :=
  ((meshFamily n).map (reflect n) _ (cubeDomain_eq_image_reflect n)).congrDomain _ rfl

theorem reflectedFamily_mesh (N : ℕ) :
    (reflectedFamily n).mesh N = (FEM.mesh n N).map (reflect n) := rfl

omit [NeZero n] in
/-- Two vertices of a simplex of a Freudenthal mesh are comparable coordinatewise. -/
theorem le_total_of_mem_vertexSet {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (FEM.mesh n N).simplices) {x y : Fin n → ℝ} (hx : x ∈ vertexSet T)
    (hy : y ∈ vertexSet T) : x ≤ y ∨ y ≤ x := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  obtain ⟨i, rfl⟩ := mem_vertexSet.1 hx
  obtain ⟨j, rfl⟩ := mem_vertexSet.1 hy
  have hh : (0 : ℝ) ≤ 1 / 2 / ((N + 1 : ℕ) : ℝ) := by positivity
  have hs := freudenthalScale_ne_zero (by norm_num : (0 : ℝ) < 1 / 2) (N + 1)
  have key : ∀ a b : Fin (n + 1), a ≤ b →
      (mapEquiv (boxMap 0 (1 / 2 / ((N + 1 : ℕ) : ℝ)) hs)
        (freudenthalSimplex (finLattice m) σ)).points a ≤
      (mapEquiv (boxMap 0 (1 / 2 / ((N + 1 : ℕ) : ℝ)) hs)
        (freudenthalSimplex (finLattice m) σ)).points b := by
    intro a b hab k
    simp only [mapEquiv_points, freudenthalSimplex_points, boxMap_apply, zero_add,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply]
    gcongr ?_ * (_ + ?_)
    simp only [kuhnVertex]
    split_ifs with h1 h2 <;> norm_num
    exact h2 (lt_of_lt_of_le h1 (by exact_mod_cast hab))
  rcases le_total i j with h | h
  · exact Or.inl (key _ _ h)
  · exact Or.inr (key _ _ h)

omit [NeZero n] in
/-- Distinct vertex sets stay distinct under an affine equivalence. -/
theorem vertexSet_mapEquiv_ne {M : SimplicialMesh n} {T₀ : Affine.Simplex ℝ (Fin n → ℝ) n}
    (h : ∀ T ∈ M.simplices, vertexSet T ≠ vertexSet T₀) (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) :
    ∀ T ∈ (M.map e).simplices, vertexSet T ≠ vertexSet (mapEquiv e T₀) := by
  intro T hT he
  obtain ⟨T', hT', rfl⟩ := (M.mem_map_simplices).1 hT
  have h' := congrArg (fun s : Finset (Fin n → ℝ) => (s : Set (Fin n → ℝ))) he
  simp only [vertexSet_mapEquiv] at h'
  exact h T' hT' (Finset.coe_injective (e.injective.image_injective h'))

/-- **The reflected meshes are not the Freudenthal meshes** (`n ≥ 2`): at every level, some
simplex of `reflect(M_N)` has a vertex set that is the vertex set of no simplex of `M_N`. Two
vertices of a Freudenthal simplex are comparable coordinatewise
(`le_total_of_mem_vertexSet`), while the reflected images `(½, 0, …)` and `(½ - h, h, …)` of the
endpoints `0`, `h 𝟙` of the long diagonal of `h K_id` are not. -/
theorem exists_reflected_simplex (h2 : 2 ≤ n) (N : ℕ) :
    ∃ T ∈ ((reflectedFamily n).mesh N).simplices,
      ∀ T' ∈ (FEM.mesh n N).simplices, vertexSet T' ≠ vertexSet T := by
  set h : ℝ := 1 / 2 / ((N + 1 : ℕ) : ℝ) with hh
  have hpos : 0 < h := by positivity
  set T₀ := mapEquiv (boxMap 0 h (freudenthalScale_ne_zero (by norm_num : (0 : ℝ) < 1 / 2)
    (N + 1))) (freudenthalSimplex (finLattice (0 : Fin n → Fin (N + 1))) 1) with hT₀
  have hT₀m : T₀ ∈ (FEM.mesh n N).simplices := mem_freudenthalMesh_simplices.2 ⟨0, 1, rfl⟩
  refine ⟨mapEquiv (reflect n) T₀, (SimplicialMesh.mem_map_simplices _).2 ⟨T₀, hT₀m, rfl⟩,
    fun T' hT' he => ?_⟩
  have hv : ∀ j, reflect n (T₀.points j) ∈ vertexSet T' := fun j => by
    rw [he]; exact mem_vertexSet.2 ⟨j, by rw [mapEquiv_points]⟩
  have hp : ∀ j k, T₀.points j k = h * kuhnVertex 1 j k := fun j k => by
    simp [hT₀, freudenthalSimplex_points, finLattice]
  set i₁ : Fin n := ⟨1, h2⟩
  have hi₁ : i₁ ≠ 0 := fun e => by
    have := congrArg Fin.val e; simp [i₁] at this
  rcases le_total_of_mem_vertexSet n hT' (hv 0) (hv (Fin.last n)) with hle | hle
  · have := hle 0
    simp only [reflect_apply, ↓reduceIte, hp, kuhnVertex_zero, kuhnVertex_last] at this
    simp at this; linarith
  · have := hle i₁
    simp only [reflect_apply, hi₁, ↓reduceIte, hp, kuhnVertex_zero, kuhnVertex_last] at this
    simp at this; linarith

end CubeWitness

namespace ParallelepipedWitness

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ) [NeZero n]

/-- **A mesh family of the parallelepiped that is not an image Freudenthal family**: the images
`T(reflect(M_N))` of the reflected Freudenthal meshes under `T x = A x + b`, a mesh family of
`ParallelepipedWitness.starDomain A hA b` to which `Parallelepiped.mixed_rate_poly_general`
applies (`reflectedFamily_ne`). -/
def reflectedFamily : MeshFamily (starDomain A hA b) :=
  ((CubeWitness.reflectedFamily n).map (Feec.Models.Parallelepiped.affEquiv A hA b)
    (Feec.Models.Parallelepiped.domain A b)
    (Feec.Models.Parallelepiped.domain_eq_image A hA b)).congrDomain _ rfl

/-- **`reflectedFamily` differs from the image Freudenthal meshes** (`n ≥ 2`): at every level
some simplex of it has a vertex set that is the vertex set of no simplex of
`Parallelepiped.mesh A hA b N`; in particular the meshes differ. -/
theorem exists_reflected_simplex (h2 : 2 ≤ n) (N : ℕ) :
    ∃ T ∈ ((reflectedFamily A hA b).mesh N).simplices,
      ∀ T' ∈ (Feec.Models.Parallelepiped.mesh A hA b N).simplices,
        vertexSet T' ≠ vertexSet T := by
  obtain ⟨T, hT, hne⟩ := CubeWitness.exists_reflected_simplex n h2 N
  exact ⟨_, (SimplicialMesh.mem_map_simplices _).2 ⟨T, hT, rfl⟩,
    CubeWitness.vertexSet_mapEquiv_ne n hne _⟩

theorem reflectedFamily_ne (h2 : 2 ≤ n) (N : ℕ) :
    (reflectedFamily A hA b).mesh N ≠ Feec.Models.Parallelepiped.mesh A hA b N := fun e => by
  obtain ⟨T, hT, hne⟩ := exists_reflected_simplex A hA b h2 N
  exact hne T (e ▸ hT) rfl

/-- **Second-order convergence of the bottom row on the reflected meshes of a parallelepiped**:
`Parallelepiped.mixed_rate_lagrangeP2_general` for the mesh family `reflectedFamily`, which is not
an image Freudenthal family (`reflectedFamily_ne`). -/
theorem mixed_rate_lagrangeP2_reflected :
    ∃ K : ℝ, ∀ {f : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)}
    {σ : (starDomain A hA b).complex.domainSpace 0}
    {u : (starDomain A hA b).complex.domainSpace 1}
    {q : (starDomain A hA b).complex.harmonic 1},
    (starDomain A hA b).complex.IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    (starDomain A hA b).IsCsForm 1 0 L ((starDomain A hA b).complex.domainIncl 0 σ) →
    (starDomain A hA b).IsCsForm 1 1 L ((starDomain A hA b).complex.domainIncl 1 u) →
    (starDomain A hA b).IsCsForm 1 1 L ((starDomain A hA b).complex.domainIncl 1
      ((starDomain A hA b).complex.boundaryPart 1
        ((starDomain A hA b).complex.domainIncl 1 u))) →
    (starDomain A hA b).IsCsForm 1 1 L
      (q : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - ((reflectedFamily A hA b).poly PolySeq.lagrangeP2 N).embD 0
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((reflectedFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).fst‖ +
      ‖u - ((reflectedFamily A hA b).poly PolySeq.lagrangeP2 N).embD 1
        (Subcomplex.CochainProjection.discreteMixedSolution
          ((reflectedFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.fst‖ +
      ‖(q : L2F ℝ (starDomain A hA b).Ω (formIdx n 1)) -
        (((Subcomplex.CochainProjection.discreteMixedSolution
          ((reflectedFamily A hA b).poly PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl
            f).snd.snd : ((reflectedFamily A hA b).poly PolySeq.lagrangeP2 N).V 1) :
              L2F ℝ (starDomain A hA b).Ω (formIdx n 1))‖ ≤
      K * L * ((reflectedFamily A hA b).mesh N).meshSize ^ (1 + 1) :=
  Parallelepiped.mixed_rate_lagrangeP2_general A hA b (reflectedFamily A hA b)

end ParallelepipedWitness


end Feec.Models.StarShaped
