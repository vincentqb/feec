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
outside `Ω`), and with the density of smooth forms the graph-norm density of the spaces
(`MeshFamily.eventually_exists_poly_near`, `MeshFamily.tendsto_infDist_poly`).

**The finite element theorems** (`MeshFamily`, every `S`):
* the complexes of `S` are **conforming families** (`MeshFamily.polyFamily`,
  `MeshFamily.polyFamilyMin`) with the **Jackson estimates** of order `h_N^{s+1}`
  (`MeshFamily.polyJackson`, `MeshFamily.polyJacksonMin`), so the static FEEC theorem
  (`Feec.HilbertComplex.ConformingFamily.staticFEEC`: uniform discrete Poincaré inequality,
  well-posedness and stability, harmonic gap, cohomology, quasi-optimality, convergence) holds;
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
inequality of `HΛ(Ω)`, resp. `H̊Λ(Ω)` (`HasPoincare`, equivalently closed range), used by the
static theorems and `mixed_rate_poly(_of_polyOrderAt)` (and their `Min` versions); it holds on
every bounded Lipschitz domain through the regularized Poincaré and Bogovskiĭ operators
([CostabelMcIntosh2010]), a theory absent from Mathlib. The harmonic gap and the cohomology also
use the finite-dimensionality of the harmonic forms; the rate theorems do not
(`ConformingFamily.rate`). The cochain
projections, the approximation results and the wave convergence and rates are proved with no
hypothesis.

**Parallelepipeds, with no hypothesis.** For every parallelepiped `Ω = A · Q + b` (every box) and
**every** quasi-uniform shape-regular mesh family of it (not only the image Freudenthal meshes),
the Poincaré inequalities are theorems (`Parallelepiped.hasPoincare`,
`Parallelepiped.hasPoincareMin`, from `Feec.Models.Parallelepiped.norm_le_of_mem_orthogonal_cycles`
and `_min`), and so are the harmonic finite-dimensionality instances; hence the static FEEC
theorem for `MeshFamily.polyFamily` and **`Parallelepiped.mixed_rate_poly_general`**
(`Parallelepiped.mixed_rate_poly_general_of_polyOrderAt`, the instance
`Parallelepiped.mixed_rate_lagrangeP2_general`: order `h²` of the bottom row on `1`-forms) hold
unconditionally; with vanishing boundary DOFs `Parallelepiped.hasPoincareMin` discharges the
hypothesis of the `Min` theorems. The discrete cohomology of these families is in
`Feec.Models.ConformingFamilies`.

**Non-vacuity.** The cube with its Freudenthal meshes (`CubeWitness.meshFamily`) and every
parallelepiped with its image Freudenthal meshes (`ParallelepipedWitness.meshFamily`) satisfy all
the hypotheses for the bottom row: `CubeWitness.mixed_rate_lagrangeP2`,
`ParallelepipedWitness.mixed_rate_lagrangeP2`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (Thm 3.4, 3.6), Thm 3.8, Thm 3.9, §5.5 (smoothed projections)
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
    ((FEM.norm_formL2_sub_glue_le_of_forall _ _ hΩ k ⟨w, hw.continuous⟩
      ((polyElement n S).globalInterp (F.mesh N) k ⟨w, hw.continuous⟩ :
        (polyElement n S).Piecewise (F.mesh N) k) hB1
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs hws hdeg hL T (interior_subset hx) t
      ).trans_eq ?_)
    ((FEM.norm_formL2_sub_glue_le_of_forall _ _ hΩ (k + 1) ⟨extDeriv w, hdw.continuous⟩
      ((polyElement n S).globalInterp (F.mesh N) (k + 1) ⟨extDeriv w, hdw.continuous⟩ :
        (polyElement n S).Piecewise (F.mesh N) (k + 1)) hB2
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs' hdw hdeg' hL' T (interior_subset hx) t
      ).trans_eq ?_) <;>
  · rw [F.domain_eq N, polyInterpConst]; push_cast; ring

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
    ((FEM.norm_formL2_sub_glue_le_of_forall _ _ hΩ k ⟨w, hw.continuous⟩
      ((polyElement n S).globalInterp (F.mesh N) k ⟨w, hw.continuous⟩ :
        (polyElement n S).Piecewise (F.mesh N) k) hB1
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs hws hdeg hL T (interior_subset hx) t
      ).trans_eq ?_)
    ((FEM.norm_formL2_sub_glue_le_of_forall _ _ hΩ (k + 1) ⟨extDeriv w, hdw.continuous⟩
      ((polyElement n S).globalInterp (F.mesh N) (k + 1) ⟨extDeriv w, hdw.continuous⟩ :
        (polyElement n S).Piecewise (F.mesh N) (k + 1)) hB2
      fun T x hx t _ => F.abs_sub_globalInterp_le S hs' hdw hdeg' hL' T (interior_subset hx) t
      ).trans_eq ?_) <;>
  · rw [F.domain_eq N, polyInterpConst]; push_cast; ring

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

/-- **Graph-norm density of the higher-order spaces in `HΛᵏ(Ω)`**: the canonical interpolants of
smooth forms converge at rate `h_N` (`exists_mem_poly_le` with `s = 0`,
`FEM.eventually_exists_graph_of_smooth`). -/
theorem eventually_exists_poly_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complex.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.poly S N).V k, ‖x - v‖ < ε ∧
      ‖D.complex.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.poly S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine FEM.eventually_exists_graph_of_smooth D.isOpen D.isBounded D.s₀_pos D.starBall
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
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_poly_le S N k 0 (FEM.polySpace_zero_le_space S k)
    (FEM.polySpace_zero_le_space S (k + 1)) hw2 hdeg hL0 hL'0 hL hL'
  rw [zero_add, pow_one] at hv1 hv2
  have hb1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.polyInterpConst_nonneg S k)
    (mul_nonneg (F.meshSize_pos N).le hL0)
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right hb1), hdv,
    hv2.trans (le_add_of_nonneg_left hb0)⟩

/-- **`L²` density of the higher-order spaces** `Vₕᵏ` in `L²(Ω; Λᵏ)`. -/
theorem eventually_exists_poly_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.poly S N).V k, ‖x - v‖ < ε :=
  FEM.eventually_exists_lt_of_graph
    (fun k x hx _ hε => F.eventually_exists_poly_graph S k x hx hε) k x hε

/-- **Degreewise approximation in every graph norm of `HΛ(Ω)`** by the higher-order spaces. -/
theorem eventually_exists_poly_near (i : ℤ) (x : L2F ℝ D.Ω (formIdx n i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.poly S N).V i, ‖x - v‖ < ε ∧
      ∀ j (hx : x ∈ (D.complex.d i j).domain),
        ‖D.complex.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.poly S N).le_domain i j hv)⟩‖ <
          ε :=
  FEM.eventually_exists_near_of_graph
    (fun k x hx _ hε => F.eventually_exists_poly_graph S k x hx hε) i x hε

/-- `dist(q, Vₕʲ) → 0` for every `q ∈ L²(Ω; Λʲ)` (higher-order spaces). -/
theorem tendsto_infDist_poly (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.poly S N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) :=
  FEM.tendsto_infDist_of_lt (S := fun N => F.poly S N) q fun _ ha =>
    F.eventually_exists_poly_lt S j q ha

/-- **Graph-norm density of the higher-order spaces with vanishing boundary DOFs in
`H̊Λᵏ(Ω)`**: the canonical interpolants of smooth forms vanishing outside `Ω` lie in `V̊ₕᵏ` and
converge at rate `h_N` (`exists_mem_polyMin_le`, `FEM.eventually_exists_graph_of_smooth_min`). -/
theorem eventually_exists_polyMin_graph (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k))
    (hx : x ∈ (D.complexMin.d k (k + 1)).domain) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v, ∃ hv : v ∈ (F.polyMin S N).V k, ‖x - v‖ < ε ∧
      ‖D.complexMin.d k (k + 1)
        ⟨x - v, Submodule.sub_mem _ hx ((F.polyMin S N).le_domain k (k + 1) hv)⟩‖ < ε := by
  refine FEM.eventually_exists_graph_of_smooth_min D.isOpen D.isBounded D.s₀_pos D.starBall
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
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := F.exists_mem_polyMin_le S N k 0 (FEM.polySpace_zero_le_space S k)
    (FEM.polySpace_zero_le_space S (k + 1)) hw2 hdeg hsupp hL0 hL'0 hL hL'
  rw [zero_add, pow_one] at hv1 hv2
  have hb1 := mul_nonneg (F.polyInterpConst_nonneg S (k + 1))
    (mul_nonneg (F.meshSize_pos N).le hL'0)
  have hb0 := mul_nonneg (F.polyInterpConst_nonneg S k)
    (mul_nonneg (F.meshSize_pos N).le hL0)
  exact ⟨v, hv, hv1.trans (le_add_of_nonneg_right hb1), hdv,
    hv2.trans (le_add_of_nonneg_left hb0)⟩

/-- **`L²` density of the higher-order spaces with vanishing boundary DOFs** `V̊ₕᵏ` in
`L²(Ω; Λᵏ)`. -/
theorem eventually_exists_polyMin_lt (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∃ v ∈ (F.polyMin S N).V k, ‖x - v‖ < ε :=
  FEM.eventually_exists_lt_of_graph
    (fun k x hx _ hε => F.eventually_exists_polyMin_graph S k x hx hε) k x hε

/-- `dist(q, V̊ₕʲ) → 0` for every `q ∈ L²(Ω; Λʲ)` (higher-order spaces). -/
theorem tendsto_infDist_polyMin (j : ℤ) (q : L2F ℝ D.Ω (formIdx n j)) :
    Tendsto (fun N => Metric.infDist q ((F.polyMin S N).V j :
      Set (L2F ℝ D.Ω (formIdx n j)))) atTop (𝓝 0) :=
  FEM.tendsto_infDist_of_lt (S := fun N => F.polyMin S N) q fun _ ha =>
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

/-- **The finite element complexes of an admissible sequence `S` on the mesh family**, with the
smoothed projections (`exists_uniform_polyProj`), a conforming family of `HΛ(Ω)`. -/
def polyFamily : ConformingFamily D.complex ℕ :=
  .ofExists atTop (F.poly S)
    (by
      obtain ⟨K, -, hK⟩ := F.exists_uniform_polyProj S
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    (F.tendsto_infDist_poly S)

/-- **The finite element complexes of `S` with vanishing boundary DOFs on the mesh family**, a
conforming family of `H̊Λ(Ω)`. -/
def polyFamilyMin : ConformingFamily D.complexMin ℕ :=
  .ofExists atTop (F.polyMin S)
    (by
      obtain ⟨K, -, hK⟩ := F.exists_uniform_polyProjMin S
      choose π hb _ using hK
      exact ⟨K, π, hb⟩)
    (F.tendsto_infDist_polyMin S)

@[simp] theorem polyFamily_V : (F.polyFamily S).V = F.poly S := rfl

@[simp] theorem polyFamilyMin_V : (F.polyFamilyMin S).V = F.polyMin S := rfl

/-- **The Jackson estimate of the complexes of `S` on the mesh family**: for `s : ℕ`, the
`C^{s+2}` forms on `cl Ω` (`StarDomain.IsCsForm s`) of the degrees where `S` reproduces `P_s`
(`FEM.PolyOrderAt`) at the order `h_N^{s+1}` (`exists_mem_poly_le_of_isCsForm`). -/
def polyJackson : (F.polyFamily S).Jackson ℕ where
  meshSize N := (F.mesh N).meshSize
  meshSize_nonneg N := (F.meshSize_pos N).le
  tendsto_meshSize := F.tendsto_meshSize
  Reg s j L x := FEM.PolyOrderAt n S s j ∧ D.IsCsForm s j L x
  ord s := ((s + 1 : ℕ) : ℝ)
  B _ := F.polyInterpBound S
  B_nonneg _ := F.polyInterpBound_nonneg S
  jackson s N _ _ _ hL hx := by
    rw [Real.rpow_natCast, ← mul_assoc]; exact F.exists_mem_poly_le_of_isCsForm S hx.1 hx.2 hL N

/-- **The Jackson estimate of the complexes of `S` with vanishing boundary DOFs**: the forms of
class `StarDomain.IsCsFormMin s` at the order `h_N^{s+1}`. -/
def polyJacksonMin : (F.polyFamilyMin S).Jackson ℕ where
  meshSize N := (F.mesh N).meshSize
  meshSize_nonneg N := (F.meshSize_pos N).le
  tendsto_meshSize := F.tendsto_meshSize
  Reg s j L x := FEM.PolyOrderAt n S s j ∧ D.IsCsFormMin s j L x
  ord s := ((s + 1 : ℕ) : ℝ)
  B _ := F.polyInterpBound S
  B_nonneg _ := F.polyInterpBound_nonneg S
  jackson s N _ _ _ hL hx := by
    rw [Real.rpow_natCast, ← mul_assoc]
    exact F.exists_mem_polyMin_le_of_isCsFormMin S hx.1 hx.2 hL N

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
  obtain ⟨K, hK⟩ := (F.polyFamily S).rate (F.polyJackson S) s hij hjk
    ((D.complex.closedRangeAt_iff_poincare_of_rel hij).2 ⟨cP, hP i j hij⟩)
    ((D.complex.closedRangeAt_iff_poincare_of_rel hjk).2 ⟨cP, hP j k hjk⟩)
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL ⟨hSi, hσ⟩ ⟨hSj, hu⟩ ⟨hSj, hb⟩ ⟨hSj, hq⟩ N
  simp only [polyFamily_V] at h
  rw [← Real.rpow_natCast]
  exact h

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
        (F.mesh N).meshSize ^ (s + 1) :=
  ((F.poly S N).exists_mem_window_graphSub_le ζ (fun i => F.polyInterpBound S (a + i))
    (fun _ => F.polyInterpBound_nonneg _ _) (mul_nonneg hL0 (pow_nonneg (F.meshSize_pos N).le _))
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_poly_le_of_isCsForm S (hS i) (hζ i) hL0 N
      exact ⟨v, hv, h1.trans_eq (mul_assoc _ _ _),
        fun j hx => (h2 j hx).trans_eq (mul_assoc _ _ _)⟩).imp
    fun _ h => ⟨h.1, h.2.trans_eq (mul_assoc _ _ _).symm⟩

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
  obtain ⟨K, hK⟩ := (F.polyFamilyMin S).rate (F.polyJacksonMin S) s hij hjk
    ((D.complexMin.closedRangeAt_iff_poincare_of_rel hij).2 ⟨cP, hP i j hij⟩)
    ((D.complexMin.closedRangeAt_iff_poincare_of_rel hjk).2 ⟨cP, hP j k hjk⟩)
  refine ⟨K, fun hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL ⟨hSi, hσ⟩ ⟨hSj, hu⟩ ⟨hSj, hb⟩ ⟨hSj, hq⟩ N
  simp only [polyFamilyMin_V] at h
  rw [← Real.rpow_natCast]
  exact h

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
        (F.mesh N).meshSize ^ (s + 1) :=
  ((F.polyMin S N).exists_mem_window_graphSub_le ζ (fun i => F.polyInterpBound S (a + i))
    (fun _ => F.polyInterpBound_nonneg _ _) (mul_nonneg hL0 (pow_nonneg (F.meshSize_pos N).le _))
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := F.exists_mem_polyMin_le_of_isCsFormMin S (hS i) (hζ i) hL0 N
      exact ⟨v, hv, h1.trans_eq (mul_assoc _ _ _),
        fun j hx => (h2 j hx).trans_eq (mul_assoc _ _ _)⟩).imp
    fun _ h => ⟨h.1, h.2.trans_eq (mul_assoc _ _ _).symm⟩

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

end ParallelepipedWitness

end Feec.Models.StarShaped
